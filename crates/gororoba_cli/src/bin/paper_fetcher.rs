//! paper-fetcher: download papers by arXiv identifier or URL into a directory
//! the user names.
//!
//! Usage:
//!   paper-fetcher 2603.03446 math/0403113v1 math.GM/0011260 https://example.org/paper.pdf
//!   paper-fetcher --dest ~/papers arXiv:2503.14738
//!
//! Without `--dest` the tool asks for the directory on the terminal; it has no
//! default destination. Only `https` URLs are fetched. Two inputs that map to
//! one file name abort the run before any download, and a file that already
//! exists in the destination is left untouched and reported as `EXISTS, not
//! overwritten`.

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
/// Hosts that serve arXiv papers and fall under the arXiv request interval.
const ARXIV_HOSTS: &[&str] = &["arxiv.org", "export.arxiv.org"];
const REQUEST_TIMEOUT: Duration = Duration::from_secs(60);
/// Upper bound on one download, so a server that streams without end cannot
/// fill the destination disk.
const MAX_PDF_BYTES: u64 = 256 * 1024 * 1024;
/// A PDF file starts with this header (ISO 32000-2, section 7.5.2); a response
/// without it is an error or captcha page.
const PDF_MAGIC: &[u8] = b"%PDF-";

#[derive(Parser, Debug)]
#[command(
    name = "paper-fetcher",
    about = "Download papers by arXiv identifier or https URL"
)]
struct Cli {
    /// Directory that receives the PDFs; asked for on the terminal when omitted
    #[arg(long)]
    dest: Option<PathBuf>,

    /// arXiv identifiers (2603.03446, math/0403113v1, math.GM/0011260,
    /// arXiv:2503.14738) or https URLs
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

/// True for a four-digit `YYMM` whose month is 01 through 12.
fn is_yymm(value: &str) -> bool {
    value.len() == 4
        && all_digits(value)
        && value[2..]
            .parse::<u8>()
            .is_ok_and(|month| (1..=12).contains(&month))
}

/// Accepts the arXiv identifier forms of arxiv.org/help/arxiv_identifier, each
/// with an optional `vN` version suffix: `YYMM.NNNN` through 1412,
/// `YYMM.NNNNN` from 1501, and the legacy `archive/YYMMNNN` or
/// `archive.SC/YYMMNNN` with an uppercase subject class (`math.GM/0011260`).
/// The archive name starts with a lowercase letter and continues with
/// lowercase letters and hyphens.
fn is_arxiv_identifier(value: &str) -> bool {
    let number = match value.rsplit_once('v') {
        Some((number, version)) if all_digits(version) => number,
        _ => value,
    };
    let modern = number.split_once('.').is_some_and(|(yymm, serial)| {
        let serial_digits = if yymm < "1501" { 4 } else { 5 };
        is_yymm(yymm) && serial.len() == serial_digits && all_digits(serial)
    });
    let legacy = number.split_once('/').is_some_and(|(category, serial)| {
        let (archive, subject_class) = match category.split_once('.') {
            Some((archive, class)) => (archive, Some(class)),
            None => (category, None),
        };
        archive
            .bytes()
            .next()
            .is_some_and(|b| b.is_ascii_lowercase())
            && archive
                .bytes()
                .all(|byte| byte.is_ascii_lowercase() || byte == b'-')
            && subject_class.is_none_or(|class| {
                !class.is_empty() && class.bytes().all(|b| b.is_ascii_uppercase())
            })
            && serial.len() == 7
            && all_digits(serial)
            && is_yymm(&serial[..4])
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

/// Host of a URL given as the text after `https://`: the authority up to the
/// first `/`, `?` or `#`, without userinfo, port or a trailing dot, in lowercase.
fn url_host(after_scheme: &str) -> String {
    let authority = after_scheme
        .split(['/', '?', '#'])
        .next()
        .unwrap_or_default();
    let host_port = authority.rsplit('@').next().unwrap_or(authority);
    host_port
        .split(':')
        .next()
        .unwrap_or_default()
        .trim_end_matches('.')
        .to_ascii_lowercase()
}

fn classify(argument: &str) -> Result<Target> {
    let trimmed = argument.trim();
    ensure!(
        !trimmed.starts_with("http://"),
        "refusing {trimmed}: only https URLs are fetched; use the https form of the address"
    );
    if let Some(rest) = trimmed.strip_prefix("https://") {
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
            arxiv: ARXIV_HOSTS.contains(&url_host(rest).as_str()),
        });
    }
    let identifier = trimmed
        .strip_prefix("arXiv:")
        .or_else(|| trimmed.strip_prefix("arxiv:"))
        .unwrap_or(trimmed);
    ensure!(
        is_arxiv_identifier(identifier),
        "{argument:?} is neither an arXiv identifier nor an https URL"
    );
    Ok(Target {
        url: format!("https://arxiv.org/pdf/{identifier}"),
        file_name: format!("{}.pdf", identifier.replace('/', "_")),
        arxiv: true,
    })
}

/// Fails when two inputs map to the same destination file name, naming both
/// inputs, so the second never reads the first one's file as "already present".
fn reject_collisions(inputs: &[String], targets: &[Target]) -> Result<()> {
    for (later, target) in targets.iter().enumerate() {
        if let Some(earlier) = targets[..later]
            .iter()
            .position(|other| other.file_name == target.file_name)
        {
            bail!(
                "inputs {:?} and {:?} both map to the file name {}; fetch them into separate directories",
                inputs[earlier],
                inputs[later],
                target.file_name
            );
        }
    }
    Ok(())
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

fn ensure_pdf_header(head: &[u8], url: &str) -> Result<()> {
    ensure!(
        head == PDF_MAGIC,
        "{url} returned a body that does not start with the PDF header"
    );
    Ok(())
}

enum Outcome {
    Downloaded,
    Exists,
}

/// Streams `reader` into `partial`: checks the PDF header before the file is
/// created, refuses a body longer than `limit` bytes, and syncs the file to
/// disk so the rename that follows publishes complete data.
fn write_part(reader: impl Read, partial: &Path, url: &str, limit: u64) -> Result<()> {
    let mut limited = reader.take(limit.saturating_add(1));
    let mut head = Vec::with_capacity(PDF_MAGIC.len());
    (&mut limited)
        .take(PDF_MAGIC.len() as u64)
        .read_to_end(&mut head)
        .with_context(|| format!("reading {url}"))?;
    ensure_pdf_header(&head, url)?;
    let mut file =
        fs::File::create(partial).with_context(|| format!("creating {}", partial.display()))?;
    file.write_all(&head)
        .with_context(|| format!("writing {}", partial.display()))?;
    let copied = io::copy(&mut limited, &mut file)
        .with_context(|| format!("streaming {url} to {}", partial.display()))?;
    ensure!(
        head.len() as u64 + copied <= limit,
        "{url} exceeds the download limit of {limit} bytes"
    );
    file.sync_all()
        .with_context(|| format!("syncing {}", partial.display()))?;
    Ok(())
}

/// Writes through the sibling `.part` file and renames it onto `path`, so the
/// destination never holds a truncated PDF; the `.part` file is removed when
/// the write or the rename fails.
fn store_pdf(reader: impl Read, path: &Path, url: &str, limit: u64) -> Result<()> {
    let partial = path.with_extension("pdf.part");
    let stored = write_part(reader, &partial, url, limit).and_then(|()| {
        fs::rename(&partial, path).with_context(|| format!("renaming to {}", path.display()))
    });
    let Err(error) = stored else {
        return Ok(());
    };
    match fs::remove_file(&partial) {
        Ok(()) => Err(error),
        Err(removal) if removal.kind() == io::ErrorKind::NotFound => Err(error),
        Err(removal) => Err(error.context(format!(
            "{} also could not be removed: {removal}",
            partial.display()
        ))),
    }
}

fn fetch(agent: &ureq::Agent, target: &Target, dest: &Path) -> Result<Outcome> {
    let path = dest.join(&target.file_name);
    if fs::symlink_metadata(&path).is_ok() {
        return Ok(Outcome::Exists);
    }
    let response = agent
        .get(&target.url)
        .call()
        .with_context(|| format!("requesting {}", target.url))?;
    store_pdf(
        response.into_body().into_reader(),
        &path,
        &target.url,
        MAX_PDF_BYTES,
    )?;
    Ok(Outcome::Downloaded)
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let targets = cli
        .papers
        .iter()
        .map(|paper| classify(paper))
        .collect::<Result<Vec<_>>>()?;
    reject_collisions(&cli.papers, &targets)?;
    let dest = resolve_destination(cli.dest)?;
    let agent: ureq::Agent = ureq::Agent::config_builder()
        .user_agent(USER_AGENT)
        .timeout_global(Some(REQUEST_TIMEOUT))
        .https_only(true)
        .build()
        .into();

    let (mut downloaded, mut existing, mut failures) = (0usize, 0usize, 0usize);
    let mut arxiv_requested = false;
    for target in &targets {
        if target.arxiv && arxiv_requested {
            sleep(ARXIV_REQUEST_INTERVAL);
        }
        let path = dest.join(&target.file_name);
        match fetch(&agent, target, &dest) {
            Ok(Outcome::Downloaded) => {
                arxiv_requested |= target.arxiv;
                downloaded += 1;
                println!("OK   {}", path.display());
            }
            Ok(Outcome::Exists) => {
                existing += 1;
                println!("EXISTS, not overwritten {}", path.display());
            }
            Err(error) => {
                arxiv_requested |= target.arxiv;
                failures += 1;
                eprintln!("FAIL {}: {error:#}", target.url);
            }
        }
    }
    println!(
        "{downloaded} downloaded, {existing} EXISTS (not overwritten), {failures} failed of {}",
        targets.len()
    );
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
    fn accepts_the_legacy_subject_class_form() {
        let target = classify("math.GM/0011260").unwrap();
        assert_eq!(target.url, "https://arxiv.org/pdf/math.GM/0011260");
        assert_eq!(target.file_name, "math.GM_0011260.pdf");
        assert!(classify("arXiv:math.GM/0011260v2").is_ok());
        assert!(classify("solv-int/9901001").is_ok());
    }

    #[test]
    fn rejects_archive_names_that_are_not_lowercase_words() {
        for bad in [
            "../0403113",
            "./0403113",
            "-/0403113",
            "-math/0403113",
            "Math/0403113",
            "math.gm/0011260",
            "math./0011260",
            "math.G1/0011260",
            "math.GM.AB/0011260",
            "/0403113",
        ] {
            assert!(classify(bad).is_err(), "{bad:?} must be rejected");
        }
    }

    #[test]
    fn rejects_months_outside_01_to_12_in_both_schemes() {
        for bad in [
            "2699.12345",
            "2600.12345",
            "2613.12345",
            "1213.1234",
            "math/0013260",
            "math/0000260",
            "math.GM/0013260",
        ] {
            assert!(classify(bad).is_err(), "{bad:?} must be rejected");
        }
        assert!(classify("2612.12345").is_ok());
        assert!(classify("1201.1234").is_ok());
        assert!(classify("math/0012260").is_ok());
        assert!(classify("math/0001260").is_ok());
    }

    #[test]
    fn serial_width_follows_the_1501_boundary() {
        assert!(classify("1412.1234").is_ok());
        assert!(classify("1412.12345").is_err());
        assert!(classify("1501.12345").is_ok());
        assert!(classify("1501.1234").is_err());
        assert!(classify("math/040311").is_err());
        assert!(classify("math/04031134").is_err());
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
    fn arxiv_hosts_in_urls_get_the_arxiv_interval() {
        for url in [
            "https://arxiv.org/pdf/2603.03446",
            "https://export.arxiv.org/pdf/2603.03446",
            "https://ARXIV.org:443/pdf/2603.03446",
            "https://arxiv.org./pdf/2603.03446",
        ] {
            assert!(classify(url).unwrap().arxiv, "{url} is an arXiv host");
        }
        for url in [
            "https://notarxiv.org/pdf/x.pdf",
            "https://arxiv.org.evil.example/pdf/x.pdf",
            "https://arxiv.org@evil.example/pdf/x.pdf",
            "https://evil.example/arxiv.org/x.pdf",
            "https://evil.example/x.pdf?u=arxiv.org",
        ] {
            assert!(!classify(url).unwrap().arxiv, "{url} is not an arXiv host");
        }
    }

    #[test]
    fn refuses_plain_http_with_a_clear_message() {
        let message = classify("http://example.org/a.pdf")
            .unwrap_err()
            .to_string();
        assert!(message.contains("only https URLs"), "{message}");
        assert!(message.contains("http://example.org/a.pdf"), "{message}");
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
    fn colliding_file_names_name_both_inputs() {
        let inputs = vec![
            "https://a.example/x/download".to_owned(),
            "2603.03446".to_owned(),
            "https://b.example/y/download".to_owned(),
        ];
        let targets: Vec<Target> = inputs.iter().map(|i| classify(i).unwrap()).collect();
        let message = reject_collisions(&inputs, &targets)
            .unwrap_err()
            .to_string();
        assert!(
            message.contains("https://a.example/x/download"),
            "{message}"
        );
        assert!(
            message.contains("https://b.example/y/download"),
            "{message}"
        );
        assert!(message.contains("download.pdf"), "{message}");
        assert!(!message.contains("2603.03446"), "{message}");

        let alias = vec!["2603.03446".to_owned(), "arXiv:2603.03446".to_owned()];
        let targets: Vec<Target> = alias.iter().map(|i| classify(i).unwrap()).collect();
        assert!(reject_collisions(&alias, &targets).is_err());

        let distinct = vec!["2603.03446".to_owned(), "math.GM/0011260".to_owned()];
        let targets: Vec<Target> = distinct.iter().map(|i| classify(i).unwrap()).collect();
        assert!(reject_collisions(&distinct, &targets).is_ok());
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
    fn non_pdf_headers_are_rejected() {
        assert!(ensure_pdf_header(b"%PDF-", "u").is_ok());
        assert!(ensure_pdf_header(b"<html", "u").is_err());
        assert!(ensure_pdf_header(b"", "u").is_err());
    }

    #[test]
    fn write_part_streams_a_pdf_body_to_the_part_file() {
        let tmp = tempfile::tempdir().unwrap();
        let partial = tmp.path().join("a.pdf.part");
        write_part(&b"%PDF-1.7\nbody"[..], &partial, "u", 64).unwrap();
        assert_eq!(fs::read(&partial).unwrap(), b"%PDF-1.7\nbody");
    }

    #[test]
    fn write_part_refuses_a_non_pdf_body_without_creating_the_file() {
        let tmp = tempfile::tempdir().unwrap();
        let partial = tmp.path().join("a.pdf.part");
        assert!(write_part(&b"<html>captcha</html>"[..], &partial, "u", 64).is_err());
        assert!(!partial.exists());
    }

    #[test]
    fn write_part_enforces_the_size_limit_exactly() {
        let tmp = tempfile::tempdir().unwrap();
        let partial = tmp.path().join("a.pdf.part");
        let body = b"%PDF-12345";
        write_part(&body[..], &partial, "u", body.len() as u64).unwrap();
        let error = write_part(&body[..], &partial, "u", body.len() as u64 - 1).unwrap_err();
        assert!(error.to_string().contains("download limit"), "{error}");
    }

    #[test]
    fn write_part_stops_reading_at_the_limit() {
        struct Endless;
        impl Read for Endless {
            fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
                buf.fill(b'%');
                Ok(buf.len())
            }
        }
        let tmp = tempfile::tempdir().unwrap();
        let partial = tmp.path().join("a.pdf.part");
        let reader = (&b"%PDF-"[..]).chain(Endless);
        assert!(write_part(reader, &partial, "u", 1024).is_err());
        assert!(fs::metadata(&partial).unwrap().len() <= 1025);
    }

    #[test]
    fn store_pdf_publishes_the_file_and_leaves_no_part_file() {
        let tmp = tempfile::tempdir().unwrap();
        let path = tmp.path().join("a.pdf");
        store_pdf(&b"%PDF-1.7\nbody"[..], &path, "u", 64).unwrap();
        assert_eq!(fs::read(&path).unwrap(), b"%PDF-1.7\nbody");
        assert!(!tmp.path().join("a.pdf.part").exists());
    }

    #[test]
    fn store_pdf_removes_the_part_file_when_the_body_exceeds_the_limit() {
        let tmp = tempfile::tempdir().unwrap();
        let path = tmp.path().join("a.pdf");
        assert!(store_pdf(&b"%PDF-123456789"[..], &path, "u", 8).is_err());
        assert!(!path.exists());
        assert!(!tmp.path().join("a.pdf.part").exists());
    }

    #[test]
    fn store_pdf_removes_the_part_file_when_the_rename_fails() {
        let tmp = tempfile::tempdir().unwrap();
        let path = tmp.path().join("a.pdf");
        fs::create_dir_all(path.join("occupied")).unwrap();
        assert!(store_pdf(&b"%PDF-1.7\n"[..], &path, "u", 64).is_err());
        assert!(!tmp.path().join("a.pdf.part").exists());
    }
}
