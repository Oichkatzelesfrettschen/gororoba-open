// SPDX-License-Identifier: GPL-2.0-or-later
//
// Location of the Rocq proof tree.
//
// The proof tree lives in the gororoba-math repository under `rocq/open`.
// Registry rows, receipts and witnesses retained in this repository name its
// files by the locators they were recorded under, `proofs/<path>`, and those
// bytes stay as recorded. `ProofTree` maps such a locator to the file in the
// gororoba-math checkout, and maps every other recorded path to this
// repository, so a reader resolves each path against the repository that
// holds it.

use std::env;
use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::path::{Component, Path, PathBuf};

/// Environment variable naming a gororoba-math checkout. `ci/gororoba_math.pin`
/// names the commit that hosted validation fetches.
pub const MATH_ENV: &str = "GOROROBA_MATH";

/// Directory of the proof tree inside a gororoba-math checkout.
pub const TREE_PATH: &str = "rocq/open";

/// Prefix of the locators that registry rows, receipts and witnesses record
/// for proof-tree files.
pub const RECORDED_PREFIX: &str = "proofs/";

/// File that lists the sources of the proof tree.
pub const PROJECT_FILE: &str = "_RocqProject";

/// The proof tree cannot be located.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofTreeError(String);

impl fmt::Display for ProofTreeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for ProofTreeError {}

/// The part of a recorded locator below `proofs/`, or `None` when the locator
/// names a file of this repository.
pub fn recorded_relative(recorded: &str) -> Option<&str> {
    recorded.strip_prefix(RECORDED_PREFIX)
}

/// Whether `path` is a nonempty relative path of plain names, which names no
/// parent directory, root or absolute location.
pub fn is_plain_relative(path: &str) -> bool {
    let path = Path::new(path);
    !path.as_os_str().is_empty()
        && path
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
}

/// The recorded locator of a file at `relative` inside the proof tree.
pub fn recorded_locator(relative: &str) -> String {
    format!("{RECORDED_PREFIX}{relative}")
}

/// A directory that holds `_RocqProject` and the `theories/`, `verified/` and
/// `evidence/` directories it lists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofTree {
    root: PathBuf,
}

impl ProofTree {
    /// The tree of the gororoba-math checkout that `GOROROBA_MATH` names.
    pub fn from_environment() -> Result<Self, ProofTreeError> {
        Self::from_environment_value(env::var_os(MATH_ENV))
    }

    /// As [`ProofTree::from_environment`] for a value already read, so a
    /// caller or a test supplies the variable without mutating the process.
    pub fn from_environment_value(value: Option<OsString>) -> Result<Self, ProofTreeError> {
        match value {
            Some(checkout) if !checkout.is_empty() => Self::in_checkout(Path::new(&checkout)),
            _ => Err(ProofTreeError(format!(
                "the proof tree is unresolved: {MATH_ENV} is unset; set it to a gororoba-math \
                 checkout at the commit named by ci/gororoba_math.pin (the tree is {TREE_PATH} \
                 there)"
            ))),
        }
    }

    /// The tree `GOROROBA_MATH` names, or `None` when the variable is unset or
    /// empty. A variable that names a checkout without the tree is an error, so
    /// a caller that skips the checks of an absent tree never skips those of a
    /// broken one.
    pub fn from_environment_if_set() -> Result<Option<Self>, ProofTreeError> {
        Self::from_environment_value_if_set(env::var_os(MATH_ENV))
    }

    /// As [`ProofTree::from_environment_if_set`] for a value already read.
    pub fn from_environment_value_if_set(
        value: Option<OsString>,
    ) -> Result<Option<Self>, ProofTreeError> {
        match value {
            Some(checkout) if !checkout.is_empty() => {
                Self::in_checkout(Path::new(&checkout)).map(Some)
            }
            _ => Ok(None),
        }
    }

    /// The tree of the gororoba-math checkout at `checkout`.
    pub fn in_checkout(checkout: &Path) -> Result<Self, ProofTreeError> {
        Self::at_root(checkout.join(TREE_PATH))
    }

    /// The tree rooted at `root`, which holds `_RocqProject` as a regular
    /// file.
    pub fn at_root(root: impl Into<PathBuf>) -> Result<Self, ProofTreeError> {
        let root = root.into();
        let project = root.join(PROJECT_FILE);
        let regular = fs::symlink_metadata(&project)
            .map(|metadata| metadata.file_type().is_file())
            .unwrap_or(false);
        if !regular {
            return Err(ProofTreeError(format!(
                "the proof tree is unresolved: {} is not a regular file; {MATH_ENV} must name a \
                 gororoba-math checkout whose {TREE_PATH} holds {PROJECT_FILE}",
                project.display()
            )));
        }
        Ok(Self { root })
    }

    /// Directory of the tree.
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Path of `_RocqProject`.
    pub fn project_file(&self) -> PathBuf {
        self.root.join(PROJECT_FILE)
    }

    /// The file of this tree that a recorded `proofs/<path>` locator names.
    /// `None` when the locator lacks the prefix or its remainder holds a
    /// component other than a plain name.
    pub fn locate(&self, recorded: &str) -> Option<PathBuf> {
        let relative = recorded_relative(recorded)?;
        let path = Path::new(relative);
        if relative.is_empty()
            || !path
                .components()
                .all(|component| matches!(component, Component::Normal(_)))
        {
            return None;
        }
        Some(self.root.join(path))
    }

    /// The file a recorded path names: in this tree for a `proofs/` locator,
    /// below `repository_root` for every other path.
    ///
    /// The locator must be a nonempty relative path of plain names, which
    /// rules out `..`, a root and an absolute path. Where the file or one of
    /// its parent directories exists, the canonical path must stay under
    /// the tree (proof locator) or under `repository_root` (any other path),
    /// so a symbolic link that leaves its directory is refused. A path that
    /// does not exist is returned unchanged for the caller to report as
    /// missing.
    pub fn resolve(
        &self,
        repository_root: &Path,
        recorded: &str,
    ) -> Result<PathBuf, ProofTreeError> {
        let (base, relative) = match recorded_relative(recorded) {
            Some(inside) => (self.root.as_path(), inside),
            None => (repository_root, recorded),
        };
        if !is_plain_relative(relative) {
            return Err(ProofTreeError(format!(
                "recorded path is not a relative path of plain names: {recorded}"
            )));
        }
        let candidate = base.join(relative);
        contain(base, &candidate, recorded)?;
        Ok(candidate)
    }

    /// Whether the file a recorded path names exists; see [`ProofTree::resolve`]
    /// for the paths it refuses.
    pub fn exists(&self, repository_root: &Path, recorded: &str) -> Result<bool, ProofTreeError> {
        Ok(self.resolve(repository_root, recorded)?.exists())
    }

    /// Whether a recorded path names a regular file; see [`ProofTree::resolve`]
    /// for the paths it refuses.
    pub fn is_file(&self, repository_root: &Path, recorded: &str) -> Result<bool, ProofTreeError> {
        Ok(self.resolve(repository_root, recorded)?.is_file())
    }
}

/// Fails unless the deepest existing part of `candidate` canonicalizes to a
/// path under `base`.
fn contain(base: &Path, candidate: &Path, recorded: &str) -> Result<(), ProofTreeError> {
    let escape = || {
        ProofTreeError(format!(
            "recorded path leaves {}: {recorded}",
            base.display()
        ))
    };
    let canonical_base = base
        .canonicalize()
        .map_err(|error| ProofTreeError(format!("cannot resolve {}: {error}", base.display())))?;
    let mut probe = candidate;
    loop {
        if fs::symlink_metadata(probe).is_ok() {
            let canonical = probe.canonicalize().map_err(|_| escape())?;
            return if canonical.starts_with(&canonical_base) {
                Ok(())
            } else {
                Err(escape())
            };
        }
        match probe.parent() {
            Some(parent) => probe = parent,
            None => return Err(escape()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tree_directory(directory: &Path) -> PathBuf {
        let tree = directory.join(TREE_PATH);
        fs::create_dir_all(&tree).unwrap();
        fs::write(tree.join(PROJECT_FILE), "-R theories OpenGororoba\n").unwrap();
        tree
    }

    #[test]
    fn an_unset_variable_names_itself_and_the_pin() {
        for value in [None, Some(OsString::new())] {
            let message = ProofTree::from_environment_value(value)
                .expect_err("unset variable")
                .to_string();
            assert!(message.contains(MATH_ENV), "{message}");
            assert!(message.contains("ci/gororoba_math.pin"), "{message}");
        }
    }

    #[test]
    fn an_optional_tree_is_absent_only_when_the_variable_is_unset() {
        assert_eq!(ProofTree::from_environment_value_if_set(None), Ok(None));
        assert_eq!(
            ProofTree::from_environment_value_if_set(Some(OsString::new())),
            Ok(None)
        );
        let directory = tempfile::tempdir().unwrap();
        assert!(
            ProofTree::from_environment_value_if_set(Some(directory.path().as_os_str().to_owned()))
                .is_err(),
            "a variable that names a broken checkout is an error"
        );
        tree_directory(directory.path());
        assert!(
            ProofTree::from_environment_value_if_set(Some(directory.path().as_os_str().to_owned()))
                .unwrap()
                .is_some()
        );
    }

    #[test]
    fn a_checkout_without_the_project_file_is_unresolved() {
        let directory = tempfile::tempdir().unwrap();
        let message = ProofTree::in_checkout(directory.path())
            .expect_err("no project file")
            .to_string();
        assert!(message.contains(PROJECT_FILE), "{message}");
    }

    #[test]
    fn a_checkout_resolves_to_its_tree_directory() {
        let directory = tempfile::tempdir().unwrap();
        let tree_root = tree_directory(directory.path());
        let from_value =
            ProofTree::from_environment_value(Some(directory.path().as_os_str().to_owned()))
                .unwrap();
        assert_eq!(from_value.root(), tree_root);
        assert_eq!(from_value.project_file(), tree_root.join(PROJECT_FILE));
    }

    #[test]
    fn a_recorded_locator_resolves_into_the_tree_and_other_paths_into_the_repository() {
        let directory = tempfile::tempdir().unwrap();
        let tree_root = tree_directory(directory.path());
        let tree = ProofTree::at_root(&tree_root).unwrap();
        let repository = directory.path().join("repository");
        fs::create_dir_all(&repository).unwrap();
        assert_eq!(
            tree.resolve(&repository, "proofs/verified/C001_Test.v")
                .unwrap(),
            tree_root.join("verified/C001_Test.v")
        );
        assert_eq!(
            tree.resolve(&repository, "data/output/audit/receipt.toml")
                .unwrap(),
            repository.join("data/output/audit/receipt.toml")
        );
        assert_eq!(recorded_locator("theories/A.v"), "proofs/theories/A.v");
        assert_eq!(recorded_relative("other/proofs/A.v"), None);
    }

    #[test]
    fn a_locator_that_leaves_the_tree_is_not_located() {
        let directory = tempfile::tempdir().unwrap();
        let tree = ProofTree::at_root(tree_directory(directory.path())).unwrap();
        for recorded in [
            "proofs/",
            "proofs/../escape",
            "proofs//absolute",
            "proofs/./x",
        ] {
            assert_eq!(tree.locate(recorded), None, "{recorded}");
        }
    }

    #[test]
    fn traversal_and_absolute_locators_are_refused_for_both_kinds_of_path() {
        let directory = tempfile::tempdir().unwrap();
        let tree = ProofTree::at_root(tree_directory(directory.path())).unwrap();
        let repository = directory.path().join("repository");
        fs::create_dir_all(&repository).unwrap();
        for recorded in [
            "proofs/../../../outside",
            "proofs/../escape",
            "proofs//absolute",
            "proofs/",
            "../outside",
            "data/../../outside",
            "/etc/passwd",
            "",
        ] {
            assert!(
                tree.resolve(&repository, recorded).is_err(),
                "{recorded:?} must be refused"
            );
            assert!(tree.exists(&repository, recorded).is_err(), "{recorded:?}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn a_symbolic_link_that_leaves_its_directory_is_refused() {
        let directory = tempfile::tempdir().unwrap();
        let tree_root = tree_directory(directory.path());
        let tree = ProofTree::at_root(&tree_root).unwrap();
        let repository = directory.path().join("repository");
        let outside = directory.path().join("outside");
        fs::create_dir_all(&repository).unwrap();
        fs::create_dir_all(&outside).unwrap();
        fs::write(outside.join("secret.v"), "").unwrap();
        fs::write(tree_root.join("kept.v"), "").unwrap();
        std::os::unix::fs::symlink(&outside, tree_root.join("theories")).unwrap();
        std::os::unix::fs::symlink(outside.join("secret.v"), tree_root.join("leak.v")).unwrap();
        std::os::unix::fs::symlink(directory.path().join("gone"), tree_root.join("dangling.v"))
            .unwrap();
        std::os::unix::fs::symlink(&outside, repository.join("linked")).unwrap();
        for recorded in [
            "proofs/theories/secret.v",
            "proofs/leak.v",
            "proofs/dangling.v",
            "linked/secret.v",
        ] {
            assert!(
                tree.resolve(&repository, recorded).is_err(),
                "{recorded} must be refused"
            );
        }
        assert!(tree.is_file(&repository, "proofs/kept.v").unwrap());
    }

    #[test]
    fn existing_and_missing_paths_inside_their_directory_resolve() {
        let directory = tempfile::tempdir().unwrap();
        let tree_root = tree_directory(directory.path());
        let tree = ProofTree::at_root(&tree_root).unwrap();
        let repository = directory.path().join("repository");
        fs::create_dir_all(repository.join("data")).unwrap();
        fs::write(repository.join("data/log.txt"), "").unwrap();
        assert!(tree.is_file(&repository, "data/log.txt").unwrap());
        assert!(!tree.exists(&repository, "data/missing.txt").unwrap());
        assert!(
            !tree
                .exists(&repository, "proofs/verified/Missing.v")
                .unwrap()
        );
        assert!(tree.is_file(&repository, "proofs/_RocqProject").unwrap());
    }
}
