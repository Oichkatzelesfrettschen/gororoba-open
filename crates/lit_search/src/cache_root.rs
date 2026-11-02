// SPDX-License-Identifier: GPL-2.0-or-later
//! The directory the literature search and citation-verification caches live in.

use std::{
    ffi::OsString,
    path::{Path, PathBuf},
    process::Command,
};

/// Environment variable naming the cache directory explicitly.
pub const CACHE_ENV: &str = "GOROROBA_LIT_CACHE";

/// `GOROROBA_LIT_CACHE` when it is set, otherwise `.cache/lit-cache` of the primary checkout of the workspace the
/// tool runs in, which `.gitignore` leaves untracked. Outside a checkout there is no cache directory and the caches
/// stay off.
pub fn lit_cache_root() -> Option<PathBuf> {
    resolve(std::env::var_os(CACHE_ENV), repo_root::discover())
}

fn resolve(explicit: Option<OsString>, workspace: Option<PathBuf>) -> Option<PathBuf> {
    if let Some(path) = explicit.filter(|path| !path.is_empty()) {
        return Some(PathBuf::from(path));
    }
    let root = workspace?;
    let primary = primary_checkout(&root).unwrap_or(root);
    Some(primary.join(".cache").join("lit-cache"))
}

/// The primary checkout behind `root`: the parent of `git rev-parse --path-format=absolute --git-common-dir`, which
/// names the shared `.git` directory from a linked worktree as well (the plain form answers relative to it).
fn primary_checkout(root: &Path) -> Option<PathBuf> {
    let output = Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["rev-parse", "--path-format=absolute", "--git-common-dir"])
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let common = PathBuf::from(String::from_utf8(output.stdout).ok()?.trim());
    common.parent().map(Path::to_path_buf)
}

#[cfg(test)]
mod tests {
    use super::{primary_checkout, resolve};
    use std::{fs, path::PathBuf, process::Command};

    fn git(dir: &std::path::Path, args: &[&str]) {
        let status = Command::new("git")
            .arg("-C")
            .arg(dir)
            .args(args)
            .status()
            .expect("git runs");
        assert!(status.success(), "git {args:?} failed in {}", dir.display());
    }

    fn scratch(name: &str) -> PathBuf {
        let dir =
            std::env::temp_dir().join(format!("lit-cache-root-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("scratch directory");
        dir
    }

    #[test]
    fn the_environment_variable_names_the_directory() {
        let chosen = resolve(Some("/tmp/explicit".into()), Some(PathBuf::from("/repo")));
        assert_eq!(chosen, Some(PathBuf::from("/tmp/explicit")));
        assert_eq!(resolve(Some("".into()), None), None);
    }

    #[test]
    fn outside_a_checkout_the_caches_stay_off() {
        assert_eq!(resolve(None, None), None);
    }

    #[test]
    fn a_linked_worktree_resolves_to_the_primary_checkout() {
        let base = scratch("worktree");
        let primary = base.join("primary");
        fs::create_dir_all(&primary).expect("primary directory");
        git(&primary, &["init", "-q"]);
        git(
            &primary,
            &[
                "-c",
                "user.name=Test",
                "-c",
                "user.email=test@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "commit",
                "-q",
                "--allow-empty",
                "-m",
                "root",
            ],
        );
        let linked = base.join("linked");
        git(
            &primary,
            &[
                "worktree",
                "add",
                "-q",
                "--detach",
                linked.to_str().expect("utf-8 path"),
            ],
        );
        let expected = fs::canonicalize(&primary)
            .expect("primary path")
            .join(".cache")
            .join("lit-cache");
        assert_eq!(resolve(None, Some(primary.clone())), Some(expected.clone()));
        assert_eq!(resolve(None, Some(linked.clone())), Some(expected));
        assert!(primary_checkout(&base.join("absent")).is_none());
        let _ = fs::remove_dir_all(&base);
    }
}
