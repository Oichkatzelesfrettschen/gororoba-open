//! paper-fetcher: download papers by arXiv identifier or URL into a directory
//! the user names.
//!
//! Usage:
//!   paper-fetcher 2603.03446 math/0403113v1 https://example.org/paper.pdf
//!   paper-fetcher --dest ~/papers arXiv:2503.14738
//!
//! Without `--dest` the tool asks for the directory on the terminal; it has no
//! default destination.

use anyhow::{Context, Result, bail, ensure};
use clap::Parser;
use std::{
    fs,
    io::{self, BufRead, IsTerminal, Read, Write},
    path::{Path, PathBuf},
    thread::sleep,
    time::Duration,
};

const USER_AGENT: &str =
    "gororoba-fetch/0.2 (research; https://github.com/Oichkatzelesfrettschen/gororoba-open)";
/// arXiv asks automated clients for at most one request every three seconds
/// (arxiv.org/help/api/tou).
const ARXIV_REQUEST_INTERVAL: Duration = Duration::from_secs(3);
const REQUEST_TIMEOUT: Duration = Duration::from_secs(60);
/// A PDF file starts with this header (ISO 32000-2, section 7.5.2); a response
/// without it is an error or captcha page.
const PDF_MAGIC: &[u8] = b"%PDF-";

#[derive(Parser, Debug)]
#[command(
    name = "paper-fetcher",
    about = "Download papers by arXiv identifier or URL"
)]
struct Cli {
    /// Directory that receives the PDFs; asked for on the terminal when omitted
    #[arg(long)]
    dest: Option<PathBuf>,

    /// arXiv identifiers (2603.03446, math/0403113v1, arXiv:2503.14738) or http(s) URLs
    #[arg(required = true)]
    papers: Vec<String>,
}

#[derive(Debug, PartialEq, Eq)]
struct Target {
    url: String,
    file_name: String,
    arxiv: bool,
}

fn all_digits(value: &str) -> bool {
    !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit())
}

/// Accepts the arXiv identifier forms of arxiv.org/help/arxiv_identifier, each
/// with an optional `vN` version suffix: `YYMM.NNNN` through 1412,
/// `YYMM.NNNNN` from 1501, and the legacy `archive/YYMMNNN`.
fn is_arxiv_identifier(value: &str) -> bool {
    let number = match value.rsplit_once('v') {
        Some((number, version)) if all_digits(version) => number,
        _ => value,
    };
    let modern = number.split_once('.').is_some_and(|(yymm, serial)| {
        let serial_digits = if yymm < "1501" { 4 } else { 5 };
        yymm.len() == 4 && all_digits(yymm) && serial.len() == serial_digits && all_digits(serial)
    });
    let legacy = number.split_once('/').is_some_and(|(archive, serial)| {
        !archive.is_empty()
            && archive
                .bytes()
                .all(|byte| byte.is_ascii_lowercase() || byte == b'-' || byte == b'.')
            && serial.len() == 7
            && all_digits(serial)
    });
    modern || legacy
}

fn sanitize(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '.' | '-' | '_') {
                c
            } else {
                '_'
            }
        })
        .collect::<String>()
        .trim_matches(['.', '_'])
        .to_owned()
}

fn classify(argument: &str) -> Result<Target> {
    let trimmed = argument.trim();
    if let Some(rest) = trimmed
        .strip_prefix("https://")
        .or_else(|| trimmed.strip_prefix("http://"))
    {
        let path = rest.split(['?', '#']).next().unwrap_or(rest);
        let file = path
            .split_once('/')
            .map(|(_, file_path)| file_path.rsplit('/').next().unwrap_or_default())
            .unwrap_or_default();
        let stem = sanitize(file.strip_suffix(".pdf").unwrap_or(file));
        ensure!(
            !stem.is_empty(),
            "URL {trimmed} names no file; pass a URL that ends in the document's file name"
        );
        return Ok(Target {
            url: trimmed.to_owned(),
            file_name: format!("{stem}.pdf"),
            arxiv: false,
        });
    }
    let identifier = trimmed
        .strip_prefix("arXiv:")
        .or_else(|| trimmed.strip_prefix("arxiv:"))
        .unwrap_or(trimmed);
    ensure!(
        is_arxiv_identifier(identifier),
        "{argument:?} is neither an arXiv identifier nor an http(s) URL"
    );
    Ok(Target {
        url: format!("https://arxiv.org/pdf/{identifier}"),
        file_name: format!("{}.pdf", identifier.replace('/', "_")),
        arxiv: true,
    })
}

fn expand_home(path: &str) -> PathBuf {
    match (path.strip_prefix("~/"), std::env::var_os("HOME")) {
        (Some(rest), Some(home)) => PathBuf::from(home).join(rest),
        _ => PathBuf::from(path),
    }
}

fn prompt_destination(input: &mut impl BufRead, output: &mut impl Write) -> Result<PathBuf> {
    write!(output, "Download directory: ")?;
    output.flush()?;
    let mut line = String::new();
    input.read_line(&mut line)?;
    let answer = line.trim();
    ensure!(!answer.is_empty(), "no download directory given");
    Ok(expand_home(answer))
}

fn resolve_destination(dest: Option<PathBuf>) -> Result<PathBuf> {
    let dest = match dest {
        Some(dest) => dest,
        None => {
            if !io::stdin().is_terminal() {
                bail!("no --dest given and standard input is not a terminal to ask for one");
            }
            prompt_destination(&mut io::stdin().lock(), &mut io::stderr())?
        }
    };
    fs::create_dir_all(&dest)
        .with_context(|| format!("creating download directory {}", dest.display()))?;
    Ok(dest)
}

fn ensure_pdf(body: &[u8], url: &str) -> Result<()> {
    ensure!(
        body.starts_with(PDF_MAGIC),
        "{url} returned {} bytes that are not a PDF",
        body.len()
    );
    Ok(())
}

enum Outcome {
    Downloaded,
    AlreadyPresent,
}

/// Writes through a sibling `.part` file and renames it, so the destination
/// never holds a truncated PDF.
fn fetch(agent: &ureq::Agent, target: &Target, dest: &Path) -> Result<Outcome> {
    let path = dest.join(&target.file_name);
    if path.exists() {
        return Ok(Outcome::AlreadyPresent);
    }
    let response = agent
        .get(&target.url)
        .call()
        .with_context(|| format!("requesting {}", target.url))?;
    let mut body = Vec::new();
    response
        .into_body()
        .into_reader()
        .read_to_end(&mut body)
        .with_context(|| format!("reading {}", target.url))?;
    ensure_pdf(&body, &target.url)?;
    let partial = path.with_extension("pdf.part");
    fs::write(&partial, &body).with_context(|| format!("writing {}", partial.display()))?;
    fs::rename(&partial, &path).with_context(|| format!("renaming to {}", path.display()))?;
    Ok(Outcome::Downloaded)
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let targets = cli
        .papers
        .iter()
        .map(|paper| classify(paper))
        .collect::<Result<Vec<_>>>()?;
    let dest = resolve_destination(cli.dest)?;
    let agent: ureq::Agent = ureq::Agent::config_builder()
        .user_agent(USER_AGENT)
        .timeout_global(Some(REQUEST_TIMEOUT))
        .build()
        .into();

    let mut failures = 0usize;
    let mut arxiv_requested = false;
    for target in &targets {
        if target.arxiv && arxiv_requested {
            sleep(ARXIV_REQUEST_INTERVAL);
        }
        let path = dest.join(&target.file_name);
        match fetch(&agent, target, &dest) {
            Ok(Outcome::Downloaded) => {
                arxiv_requested |= target.arxiv;
                println!("OK   {}", path.display());
            }
            Ok(Outcome::AlreadyPresent) => println!("SKIP {} (exists)", path.display()),
            Err(error) => {
                arxiv_requested |= target.arxiv;
                failures += 1;
                eprintln!("FAIL {}: {error:#}", target.url);
            }
        }
    }
    ensure!(
        failures == 0,
        "{failures} of {} downloads failed",
        targets.len()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classifies_modern_legacy_and_prefixed_arxiv_identifiers() {
        assert_eq!(
            classify("2603.03446").unwrap(),
            Target {
                url: "https://arxiv.org/pdf/2603.03446".to_owned(),
                file_name: "2603.03446.pdf".to_owned(),
                arxiv: true,
            }
        );
        assert_eq!(
            classify("math/0403113v1").unwrap().file_name,
            "math_0403113v1.pdf"
        );
        assert_eq!(
            classify("arXiv:2503.14738v2").unwrap().url,
            "https://arxiv.org/pdf/2503.14738v2"
        );
        assert!(classify("hep-th/9901001").unwrap().arxiv);
        assert!(classify("1210.1282v1").unwrap().arxiv);
        assert!(classify("1210.12820").is_err());
    }

    #[test]
    fn classifies_urls_by_their_file_name() {
        let target =
            classify("https://cds.cern.ch/record/2951492/files/ilten.pdf?version=1").unwrap();
        assert_eq!(target.file_name, "ilten.pdf");
        assert!(!target.arxiv);
        assert_eq!(
            classify("https://example.org/a b.pdf").unwrap().file_name,
            "a_b.pdf"
        );
    }

    #[test]
    fn rejects_inputs_that_name_no_document() {
        for bad in [
            "sedenion",
            "2603.3446",
            "26030.03446",
            "https://example.org/",
            "https://example.org",
            "",
            "../etc",
        ] {
            assert!(classify(bad).is_err(), "{bad:?} must be rejected");
        }
    }

    #[test]
    fn prompt_reads_the_destination_and_rejects_an_empty_answer() {
        let mut shown = Vec::new();
        let dest = prompt_destination(&mut "/srv/papers\n".as_bytes(), &mut shown).unwrap();
        assert_eq!(dest, PathBuf::from("/srv/papers"));
        assert_eq!(shown, b"Download directory: ");
        assert!(prompt_destination(&mut "\n".as_bytes(), &mut Vec::new()).is_err());
    }

    #[test]
    fn non_pdf_bodies_are_rejected() {
        assert!(ensure_pdf(b"%PDF-1.7\n", "u").is_ok());
        assert!(ensure_pdf(b"<html>captcha</html>", "u").is_err());
        assert!(ensure_pdf(b"", "u").is_err());
    }
}
