// SPDX-License-Identifier: MIT
//! DOI audit for a BibTeX file.
//!
//! Resolves each `@article` entry against the CrossRef REST API and flags any
//! entry where two or more metadata fields (first-author family name, title
//! prefix, journal, year) disagree with the bib file, or where the DOI
//! returns 404.
//!
//! Usage: `check-refs [--strict] [BIB_FILE]`
//!
//! `--strict` exits 1 when any entry fails. The default bib file is
//! `docs/latex/heliosphere/refs_heliosphere.bib`.

use std::{
    collections::HashMap, path::PathBuf, process::ExitCode, sync::LazyLock, thread::sleep,
    time::Duration,
};

use clap::Parser;
use regex::Regex;
use serde_json::{Value, json};
use unicode_normalization::UnicodeNormalization;

const BIB_DEFAULT: &str = "docs/latex/heliosphere/refs_heliosphere.bib";
const CROSSREF_API: &str = "https://api.crossref.org/works/";
const REQUEST_DELAY: Duration = Duration::from_millis(500);
const REQUEST_TIMEOUT: Duration = Duration::from_secs(10);
const FIELDS: [&str; 7] = [
    "author", "title", "journal", "year", "doi", "volume", "pages",
];

#[derive(Parser)]
#[command(about = "DOI audit for a BibTeX file against the CrossRef REST API")]
struct Args {
    /// BibTeX file to audit.
    bib_file: Option<PathBuf>,
    /// Exit 1 when any entry fails.
    #[arg(long)]
    strict: bool,
}

/// One parsed `@article` entry: its citation key and the extracted fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Entry {
    pub key: String,
    pub fields: HashMap<String, String>,
}

impl Entry {
    fn get(&self, field: &str) -> &str {
        self.fields.get(field).map_or("", String::as_str)
    }
}

static ENTRY_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?s)@article\{([^,]+),(.*?)\n\}").expect("entry regex"));
static FIELD_RES: LazyLock<Vec<(&'static str, Regex)>> = LazyLock::new(|| {
    FIELDS
        .iter()
        .map(|f| {
            let pat = format!(r"(?s)\b{f}\s*=\s*\{{([^{{}}]*(?:\{{[^{{}}]*\}}[^{{}}]*)*)\}}");
            (*f, Regex::new(&pat).expect("field regex"))
        })
        .collect()
});
static WS_RE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"\s+").expect("ws regex"));
static BRACE_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\{([^{}]*)\}").expect("brace regex"));
static CMD_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\\[a-zA-Z]+\s*").expect("command regex"));
static NON_ALNUM_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"[^a-z0-9 ]").expect("non-alnum regex"));

/// Fold to ASCII lowercase for fuzzy comparison: NFKD, drop non-ASCII,
/// collapse apostrophes, and map every other non-alphanumeric to a space.
pub fn normalize(s: &str) -> String {
    let ascii: String = s.nfkd().filter(char::is_ascii).collect();
    let ascii = ascii.replace('\'', "").to_lowercase();
    NON_ALNUM_RE.replace_all(&ascii, " ").into_owned()
}

/// Parse `@article` entries from bib text.
pub fn extract_entries(bib_text: &str) -> Vec<Entry> {
    ENTRY_RE
        .captures_iter(bib_text)
        .map(|m| {
            let body = &m[2];
            let mut fields = HashMap::new();
            for (name, re) in FIELD_RES.iter() {
                if let Some(fm) = re.captures(body) {
                    let val = WS_RE.replace_all(&fm[1], " ");
                    let val = BRACE_RE.replace_all(val.trim(), "$1");
                    let val = CMD_RE.replace_all(&val, "");
                    fields.insert((*name).to_string(), val.trim().to_string());
                }
            }
            Entry {
                key: m[1].trim().to_string(),
                fields,
            }
        })
        .collect()
}

/// Python-style `repr` of a string: single quotes unless the text holds a
/// single quote and no double quote.
fn py_repr(s: &str) -> String {
    let q = if s.contains('\'') && !s.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut out = String::from(q);
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c == q => {
                out.push('\\');
                out.push(c);
            }
            c => out.push(c),
        }
    }
    out.push(q);
    out
}

fn either_contains(a: &str, b: &str) -> bool {
    a.contains(b) || b.contains(a)
}

fn first_str(v: &Value, key: &str) -> Option<String> {
    v.get(key)?
        .as_array()?
        .first()?
        .as_str()
        .map(str::to_string)
}

fn first_words(s: &str) -> Vec<String> {
    s.split_whitespace().take(6).map(str::to_string).collect()
}

/// List the metadata mismatches between a bib entry and a CrossRef record.
pub fn compare_entry(entry: &Entry, cr: &Value) -> Vec<String> {
    let mut mismatches = Vec::new();

    let bib_year = entry.get("year");
    let cr_year = cr
        .pointer("/published/date-parts/0/0")
        .and_then(Value::as_i64)
        .map(|y| y.to_string())
        .unwrap_or_default();
    if !bib_year.is_empty() && !cr_year.is_empty() && bib_year != cr_year {
        mismatches.push(format!(
            "year: bib={} cr={}",
            py_repr(bib_year),
            py_repr(&cr_year)
        ));
    }

    let bib_journal = normalize(entry.get("journal"));
    let cr_journal_raw = first_str(cr, "container-title");
    let cr_journal = cr_journal_raw.as_deref().map(normalize).unwrap_or_default();
    if !bib_journal.is_empty()
        && !cr_journal.is_empty()
        && !either_contains(&bib_journal, &cr_journal)
    {
        mismatches.push(format!(
            "journal: bib={} cr={}",
            py_repr(entry.get("journal")),
            py_repr(&cr_journal_raw.unwrap_or_default())
        ));
    }

    let bib_title = first_words(&normalize(entry.get("title")));
    let cr_title = first_words(&normalize(&first_str(cr, "title").unwrap_or_default()));
    if !bib_title.is_empty() && !cr_title.is_empty() && bib_title != cr_title {
        mismatches.push(format!(
            "title prefix: bib={} cr={}",
            py_repr(&bib_title.join(" ")),
            py_repr(&cr_title.join(" "))
        ));
    }

    let bib_first = entry.get("author").split(" and ").next().unwrap_or("");
    let bib_family = normalize(bib_first.split(',').next().unwrap_or("").trim());
    let cr_family = cr
        .pointer("/author/0/family")
        .and_then(Value::as_str)
        .map(normalize)
        .unwrap_or_default();
    if !bib_family.is_empty() && !cr_family.is_empty() && !either_contains(&bib_family, &cr_family)
    {
        mismatches.push(format!(
            "first-author: bib={} cr={}",
            py_repr(&bib_family),
            py_repr(&cr_family)
        ));
    }

    mismatches
}

/// Outcome of a CrossRef lookup.
enum Lookup {
    Found(Value),
    /// 404, transport failure, timeout, or unparsable body.
    Missing,
    /// Any other HTTP status; the audit aborts.
    Status(u16),
}

fn fetch_crossref(doi: &str) -> Lookup {
    let config = ureq::Agent::config_builder()
        .timeout_global(Some(REQUEST_TIMEOUT))
        .http_status_as_error(false)
        .build();
    let agent: ureq::Agent = config.into();
    let Ok(mut resp) = agent
        .get(format!("{CROSSREF_API}{}", doi.trim()))
        .header("User-Agent", "check_refs/1.0 (gororoba-open CI)")
        .call()
    else {
        return Lookup::Missing;
    };
    match resp.status().as_u16() {
        404 => Lookup::Missing,
        200 => match resp
            .body_mut()
            .read_to_string()
            .ok()
            .and_then(|t| serde_json::from_str::<Value>(&t).ok())
        {
            Some(body) => Lookup::Found(body.get("message").cloned().unwrap_or_else(|| json!({}))),
            None => Lookup::Missing,
        },
        other => Lookup::Status(other),
    }
}

/// Audit result of one entry.
#[derive(Debug, PartialEq, Eq)]
pub enum Verdict {
    Ok,
    Warn(String),
    Fail(String),
}

/// Classify an entry given the comparator output: two or more mismatches
/// fail, one warns.
pub fn classify(key: &str, mismatches: &[String]) -> Verdict {
    match mismatches {
        [] => Verdict::Ok,
        [one] => Verdict::Warn(format!("  WARN  {key}: 1 minor mismatch: {one}")),
        many => Verdict::Fail(format!(
            "  FAIL  {key}: {} field mismatches: {}",
            many.len(),
            many.join("; ")
        )),
    }
}

fn main() -> ExitCode {
    let args = Args::parse();
    let bib_file = args
        .bib_file
        .unwrap_or_else(|| repo_root::path!(BIB_DEFAULT));
    let bib_text = match std::fs::read_to_string(&bib_file) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("check-refs: cannot read {}: {e}", bib_file.display());
            return ExitCode::from(2);
        }
    };
    let entries = extract_entries(&bib_text);
    println!(
        "Auditing {} @article entries in {}\n",
        entries.len(),
        bib_file.display()
    );

    let mut failures: Vec<String> = Vec::new();
    let mut warnings: Vec<String> = Vec::new();

    for entry in &entries {
        let key = &entry.key;
        let doi = entry.get("doi");
        if doi.is_empty() {
            warnings.push(format!("  WARN  {key}: no DOI field -- cannot verify"));
            println!("  WARN  {key}: no DOI");
            continue;
        }
        sleep(REQUEST_DELAY);
        let cr = match fetch_crossref(doi) {
            Lookup::Found(cr) => cr,
            Lookup::Status(code) => {
                eprintln!(
                    "check-refs: CrossRef returned HTTP {code} for {}",
                    py_repr(doi)
                );
                return ExitCode::from(1);
            }
            Lookup::Missing => {
                failures.push(format!(
                    "  FAIL  {key}: DOI {doi:?} returned 404 or network error"
                ));
                println!("  FAIL  {key}: DOI 404 ({doi})");
                continue;
            }
        };
        match classify(key, &compare_entry(entry, &cr)) {
            Verdict::Fail(msg) => {
                println!("{msg}");
                failures.push(msg);
            }
            Verdict::Warn(msg) => {
                println!("{msg}");
                warnings.push(msg);
            }
            Verdict::Ok => println!("  OK    {key} ({doi})"),
        }
    }

    println!("\n--- Summary ---");
    println!(
        "  OK:       {}",
        entries
            .len()
            .saturating_sub(failures.len() + warnings.len())
    );
    println!("  Warnings: {}", warnings.len());
    println!("  Failures: {}", failures.len());
    if !failures.is_empty() {
        println!("\nFailed entries:");
        for f in &failures {
            println!("{f}");
        }
    }
    if args.strict && !failures.is_empty() {
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    const BIB: &str = "@article{smith2020,\n  author = {Smith, J. and {Doe}, A.},\n  title = {The {Sun}'s {magnetopause} and more words here},\n  journal = {J. Geophys. Res.},\n  year = {2020},\n  doi = {10.1/x},\n}\n\n@article{nodoi,\n  title = {T},\n}\n@book{skip,\n  title = {no},\n}\n";

    #[test]
    fn normalize_folds_accents_apostrophes_and_punctuation() {
        assert_eq!(
            normalize("Humanity's Caf\u{e9}-Zo\u{eb}"),
            "humanitys cafe zoe"
        );
        assert_eq!(normalize("A.B"), "a b");
    }

    #[test]
    fn extract_entries_parses_articles_only_and_strips_latex() {
        let es = extract_entries(BIB);
        assert_eq!(es.len(), 2);
        assert_eq!(es[0].key, "smith2020");
        assert_eq!(es[0].get("author"), "Smith, J. and Doe, A.");
        assert_eq!(
            es[0].get("title"),
            "The Sun's magnetopause and more words here"
        );
        assert_eq!(es[0].get("year"), "2020");
        assert_eq!(es[0].get("doi"), "10.1/x");
        assert_eq!(es[1].get("doi"), "");
    }

    fn cr_record() -> Value {
        json!({
            "published": {"date-parts": [[2020, 5]]},
            "container-title": ["Journal of Geophysical Research: Space Physics"],
            "title": ["The Sun's Magnetopause and more words here today"],
            "author": [{"family": "Smith"}]
        })
    }

    #[test]
    fn compare_entry_accepts_matching_record() {
        let e = &extract_entries(BIB)[0];
        let mut e = e.clone();
        e.fields
            .insert("journal".into(), "Journal of Geophysical Research".into());
        assert!(compare_entry(&e, &cr_record()).is_empty());
    }

    #[test]
    fn compare_entry_reports_each_field() {
        let e = extract_entries(BIB)[0].clone();
        let mut cr = cr_record();
        cr["published"]["date-parts"] = json!([[2019]]);
        cr["title"] = json!(["Unrelated heading entirely different"]);
        cr["author"] = json!([{"family": "Jones"}]);
        let m = compare_entry(&e, &cr);
        assert_eq!(m.len(), 4, "{m:?}");
        assert!(m[0].starts_with("year:"));
        assert!(m[1].starts_with("journal:"));
        assert!(m[2].starts_with("title prefix:"));
        assert!(m[3].starts_with("first-author:"));
    }

    #[test]
    fn compare_entry_skips_missing_crossref_fields() {
        let e = extract_entries(BIB)[0].clone();
        assert!(compare_entry(&e, &json!({})).is_empty());
    }

    #[test]
    fn py_repr_matches_python_quoting() {
        assert_eq!(py_repr("10.1/x"), "'10.1/x'");
        assert_eq!(py_repr("it's"), "\"it's\"");
        assert_eq!(py_repr("a'b\"c"), "'a\\'b\"c'");
        let e = extract_entries(BIB)[0].clone();
        let m = compare_entry(&e, &json!({"published": {"date-parts": [[2019]]}}));
        assert_eq!(m, vec!["year: bib='2020' cr='2019'".to_string()]);
    }

    #[test]
    fn two_mismatches_fail_and_one_warns() {
        assert_eq!(classify("k", &[]), Verdict::Ok);
        let w = classify("k", &["year: x".to_string()]);
        assert_eq!(
            w,
            Verdict::Warn("  WARN  k: 1 minor mismatch: year: x".into())
        );
        let f = classify("k", &["a".to_string(), "b".to_string()]);
        assert_eq!(
            f,
            Verdict::Fail("  FAIL  k: 2 field mismatches: a; b".into())
        );
    }
}
