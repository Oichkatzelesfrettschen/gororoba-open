// SPDX-License-Identifier: MIT
//
// The PDFs under `data/papers/` form an ignored local cache. Their bytes live
// in the workspace documents repositories, `gororoba-documents-public` and
// `gororoba-documents-private`, checked out beside this repository; each lists
// every file it holds in `manifest.tsv` with the columns `sha256`, `bytes` and
// `path` first. `data/papers/document_cache.tsv` binds every cache path to the
// sha256 of its bytes, so a cache path is restored by digest from whichever
// repository holds it, and restored bytes enter the cache only when they hash
// to the recorded value.

use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::io::{self, Read};
use std::path::{Component, Path, PathBuf};

/// Repository-relative location of the cache list.
pub const CACHE_LIST_PATH: &str = "data/papers/document_cache.tsv";

/// Every cache path lies under this repository-relative directory.
pub const CACHE_ROOT: &str = "data/papers";

/// Documents checkouts searched when the caller names none, relative to the
/// repository root.
pub const DEFAULT_DOCUMENT_ROOTS: [&str; 2] = [
    "../gororoba-documents-public",
    "../gororoba-documents-private",
];

const CACHE_LIST_HEADER: &str = "\
# sha256<TAB>path of every PDF in the ignored data/papers/ cache. The bytes
# live in the gororoba-documents-public and gororoba-documents-private
# checkouts; `repo-utilities document-cache --restore` relinks them by digest.
";

/// One cache path and the digest its bytes must carry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CacheEntry {
    pub sha256: String,
    pub path: String,
}

/// State of one cache path after a check or a restore.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryState {
    /// The file exists and hashes to the recorded digest.
    Present,
    /// The file was absent and a documents checkout supplied its bytes.
    Restored,
    /// The file is absent and a documents checkout holds its bytes.
    Resolvable,
    /// No documents checkout lists the digest.
    Unresolved,
    /// The file exists with other bytes; the named digest is what it holds.
    Mismatch(String),
}

fn is_digest(text: &str) -> bool {
    text.len() == 64
        && text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// A cache path is relative, lies under `data/papers/` and names no parent
/// directory, so a list entry cannot write outside the cache.
pub fn is_cache_path(path: &str) -> bool {
    let candidate = Path::new(path);
    candidate.starts_with(CACHE_ROOT)
        && candidate
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
}

/// Parses the cache list: `sha256<TAB>path` per line, `#` comments allowed.
pub fn parse_cache_list(text: &str) -> Result<Vec<CacheEntry>, String> {
    let mut entries = Vec::new();
    for (index, line) in text.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let (sha256, path) = line
            .split_once('\t')
            .ok_or_else(|| format!("line {}: expected sha256<TAB>path", index + 1))?;
        if !is_digest(sha256) {
            return Err(format!(
                "line {}: {sha256} is not a lowercase sha256",
                index + 1
            ));
        }
        if !is_cache_path(path) {
            return Err(format!(
                "line {}: {path} lies outside {CACHE_ROOT}/",
                index + 1
            ));
        }
        entries.push(CacheEntry {
            sha256: sha256.to_owned(),
            path: path.to_owned(),
        });
    }
    Ok(entries)
}

/// Renders the cache list sorted by path.
pub fn render_cache_list(entries: &BTreeMap<String, String>) -> String {
    let mut text = String::from(CACHE_LIST_HEADER);
    for (path, sha256) in entries {
        text.push_str(sha256);
        text.push('\t');
        text.push_str(path);
        text.push('\n');
    }
    text
}

/// Maps each digest of a documents `manifest.tsv` to its repository-relative
/// path. The header row names `sha256`, `bytes` and `path` as its first three
/// columns.
pub fn parse_manifest(text: &str) -> Result<HashMap<String, String>, String> {
    let mut lines = text.lines();
    let header = lines.next().unwrap_or_default();
    if !header.starts_with("sha256\tbytes\tpath") {
        return Err("manifest header must start with sha256<TAB>bytes<TAB>path".to_owned());
    }
    let mut paths = HashMap::new();
    for (index, line) in lines.enumerate() {
        let mut fields = line.split('\t');
        let (Some(sha256), Some(_), Some(path)) = (fields.next(), fields.next(), fields.next())
        else {
            return Err(format!(
                "manifest row {}: fewer than three columns",
                index + 2
            ));
        };
        if !is_digest(sha256) {
            return Err(format!(
                "manifest row {}: {sha256} is not a lowercase sha256",
                index + 2
            ));
        }
        paths.insert(sha256.to_owned(), path.to_owned());
    }
    Ok(paths)
}

/// Hex sha256 of a file's bytes.
pub fn sha256_file(path: &Path) -> io::Result<String> {
    let mut file = fs::File::open(path)?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0_u8; 1 << 20];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

/// A documents checkout and the digest index of its manifest.
pub struct DocumentRoot {
    pub root: PathBuf,
    pub paths: HashMap<String, String>,
}

impl DocumentRoot {
    /// Reads `root/manifest.tsv`.
    pub fn open(root: &Path) -> Result<Self, String> {
        let manifest = root.join("manifest.tsv");
        let text = fs::read_to_string(&manifest)
            .map_err(|error| format!("{}: {error}", manifest.display()))?;
        let paths =
            parse_manifest(&text).map_err(|error| format!("{}: {error}", manifest.display()))?;
        Ok(Self {
            root: root.to_path_buf(),
            paths,
        })
    }
}

fn source_for(entry: &CacheEntry, roots: &[DocumentRoot]) -> Option<PathBuf> {
    roots.iter().find_map(|root| {
        root.paths
            .get(&entry.sha256)
            .map(|path| root.root.join(path))
    })
}

/// Checks one entry against the cache and, when `restore` holds, links or
/// copies its bytes from the first documents checkout that lists the digest.
/// Existing bytes that differ are reported and never overwritten.
pub fn settle(
    repo: &Path,
    entry: &CacheEntry,
    roots: &[DocumentRoot],
    restore: bool,
) -> io::Result<EntryState> {
    let target = repo.join(&entry.path);
    if target.is_file() {
        let held = sha256_file(&target)?;
        return Ok(if held == entry.sha256 {
            EntryState::Present
        } else {
            EntryState::Mismatch(held)
        });
    }
    let Some(source) = source_for(entry, roots) else {
        return Ok(EntryState::Unresolved);
    };
    if !restore {
        return Ok(EntryState::Resolvable);
    }
    let held = sha256_file(&source)?;
    if held != entry.sha256 {
        return Err(io::Error::other(format!(
            "{} hashes to {held}, manifest says {}",
            source.display(),
            entry.sha256
        )));
    }
    if let Some(parent) = target.parent() {
        fs::create_dir_all(parent)?;
    }
    if fs::hard_link(&source, &target).is_err() {
        let temporary = target.with_extension("pdf.partial");
        fs::copy(&source, &temporary)?;
        fs::rename(&temporary, &target)?;
    }
    Ok(EntryState::Restored)
}

#[cfg(test)]
mod tests {
    use super::*;

    const DIGEST: &str = "9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08";

    #[test]
    fn cache_list_rejects_paths_outside_the_cache() {
        assert!(parse_cache_list(&format!("{DIGEST}\tdata/papers/a.pdf\n")).is_ok());
        assert!(parse_cache_list(&format!("{DIGEST}\tdata/papers/../../etc/passwd\n")).is_err());
        assert!(parse_cache_list(&format!("{DIGEST}\t/data/papers/a.pdf\n")).is_err());
        assert!(parse_cache_list("ABC\tdata/papers/a.pdf\n").is_err());
    }

    #[test]
    fn rendered_list_parses_back() {
        let entries = BTreeMap::from([("data/papers/b.pdf".to_owned(), DIGEST.to_owned())]);
        let parsed = parse_cache_list(&render_cache_list(&entries)).expect("parse");
        assert_eq!(
            parsed,
            vec![CacheEntry {
                sha256: DIGEST.to_owned(),
                path: "data/papers/b.pdf".to_owned()
            }]
        );
    }

    fn fixture() -> (tempfile::TempDir, PathBuf, Vec<DocumentRoot>) {
        let workspace = tempfile::tempdir().expect("tempdir");
        let repo = workspace.path().join("repo");
        let documents = workspace.path().join("documents");
        fs::create_dir_all(repo.join("data/papers")).expect("repo");
        fs::create_dir_all(documents.join("pdf")).expect("documents");
        fs::write(documents.join("pdf/test.pdf"), b"test").expect("pdf");
        fs::write(
            documents.join("manifest.tsv"),
            format!("sha256\tbytes\tpath\n{DIGEST}\t4\tpdf/test.pdf\n"),
        )
        .expect("manifest");
        let roots = vec![DocumentRoot::open(&documents).expect("open")];
        (workspace, repo, roots)
    }

    #[test]
    fn restore_links_bytes_by_digest() {
        let (_workspace, repo, roots) = fixture();
        let entry = CacheEntry {
            sha256: DIGEST.to_owned(),
            path: "data/papers/sub/x.pdf".to_owned(),
        };
        assert_eq!(
            settle(&repo, &entry, &roots, false).expect("check"),
            EntryState::Resolvable
        );
        assert_eq!(
            settle(&repo, &entry, &roots, true).expect("restore"),
            EntryState::Restored
        );
        assert_eq!(
            fs::read(repo.join("data/papers/sub/x.pdf")).expect("read"),
            b"test"
        );
        assert_eq!(
            settle(&repo, &entry, &roots, false).expect("recheck"),
            EntryState::Present
        );
    }

    #[test]
    fn differing_bytes_are_reported_and_kept() {
        let (_workspace, repo, roots) = fixture();
        fs::write(repo.join("data/papers/x.pdf"), b"other").expect("write");
        let entry = CacheEntry {
            sha256: DIGEST.to_owned(),
            path: "data/papers/x.pdf".to_owned(),
        };
        assert!(matches!(
            settle(&repo, &entry, &roots, true).expect("settle"),
            EntryState::Mismatch(_)
        ));
        assert_eq!(
            fs::read(repo.join("data/papers/x.pdf")).expect("read"),
            b"other"
        );
    }

    #[test]
    fn unlisted_digest_is_unresolved() {
        let (_workspace, repo, roots) = fixture();
        let entry = CacheEntry {
            sha256: "0".repeat(64),
            path: "data/papers/y.pdf".to_owned(),
        };
        assert_eq!(
            settle(&repo, &entry, &roots, true).expect("settle"),
            EntryState::Unresolved
        );
    }
}
