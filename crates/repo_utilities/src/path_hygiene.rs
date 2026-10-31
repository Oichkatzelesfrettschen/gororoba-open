// SPDX-License-Identifier: MIT
//
// Tracked text names paths relative to the repository root. An absolute home
// or root-account path (`/home/<user>/...`, `/Users/<user>/...`, or the root
// account's home directory) binds a record to one machine and one checkout
// location, and
// stops resolving once the checkout moves or another host replays it.
//
// The baseline lists the tracked files that held such a path when the rule
// took effect: captured tool logs, receipts and the mirrors generated from
// them, plus literals that name a home prefix on purpose. The baseline only
// shrinks. A file outside it that matches fails the check, and a listed file
// that no longer matches also fails until its entry is removed, so every
// cleanup lands in the baseline in the same change.

use std::collections::BTreeSet;

/// Repository-relative location of the baseline file.
pub const BASELINE_PATH: &str = "crates/repo_utilities/path_hygiene_baseline.txt";

/// Extended regular expression for `git grep -E`. The bracket in `roo[t]`
/// keeps this source line from matching its own pattern.
pub const ABSOLUTE_HOME_PATTERN: &str =
    r"(^|[^A-Za-z0-9_])(/home/[A-Za-z0-9._-]+/|/Users/[A-Za-z0-9._-]+/|/roo[t]/)";

const BASELINE_HEADER: &str = "\
# Tracked files that named an absolute home or root-account path when the
# path-hygiene check took effect. The list only shrinks: remove an entry once
# its file holds repository-relative paths, with
# `repo-utilities path-hygiene --prune-baseline`.
";

/// Outcome of comparing the current offenders with the baseline.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct HygieneReport {
    /// Files that name an absolute home path and are absent from the baseline.
    pub new_offenders: Vec<String>,
    /// Baseline entries whose file no longer names one, or no longer exists.
    pub stale_entries: Vec<String>,
}

impl HygieneReport {
    pub fn is_clean(&self) -> bool {
        self.new_offenders.is_empty() && self.stale_entries.is_empty()
    }
}

/// Reads baseline entries: one repository-relative path per line; blank
/// lines and `#` comments are ignored.
pub fn parse_baseline(text: &str) -> BTreeSet<String> {
    text.lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(str::to_owned)
        .collect()
}

/// Writes the baseline in its canonical sorted form.
pub fn render_baseline(entries: &BTreeSet<String>) -> String {
    let mut out = String::from(BASELINE_HEADER);
    for entry in entries {
        out.push_str(entry);
        out.push('\n');
    }
    out
}

pub fn compare(offenders: &BTreeSet<String>, baseline: &BTreeSet<String>) -> HygieneReport {
    HygieneReport {
        new_offenders: offenders.difference(baseline).cloned().collect(),
        stale_entries: baseline.difference(offenders).cloned().collect(),
    }
}

/// The baseline after removing stale entries; it never gains an entry.
pub fn pruned_baseline(
    offenders: &BTreeSet<String>,
    baseline: &BTreeSet<String>,
) -> BTreeSet<String> {
    baseline.intersection(offenders).cloned().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use regex::Regex;

    fn set(items: &[&str]) -> BTreeSet<String> {
        items.iter().map(|item| (*item).to_owned()).collect()
    }

    fn home(rest: &str) -> String {
        format!("/{}/{}", "home", rest)
    }

    #[test]
    fn pattern_matches_home_paths_and_spares_relative_and_placeholder_forms() {
        let pattern = Regex::new(ABSOLUTE_HOME_PATTERN).expect("pattern compiles");
        assert!(pattern.is_match(&home("alice/repo/file.rs")));
        assert!(pattern.is_match(&format!("cwd = \"{}\"", home("alice/x"))));
        assert!(pattern.is_match(&format!("/{}/{}", "root", ".cargo")));
        assert!(pattern.is_match(&format!("/{}/{}", "Users", "bob/src/")));
        assert!(!pattern.is_match("data/output/audit/receipt.toml"));
        assert!(!pattern.is_match("~/.claude/projects/key/memory"));
        assert!(!pattern.is_match(&format!("/{}/<user>/", "home")));
        assert!(!pattern.is_match(&format!("prefix \"/{}/\"", "home")));
        assert!(!pattern.is_match(&format!("x{}", home("alice/"))));
        assert!(!pattern.is_match(ABSOLUTE_HOME_PATTERN));
    }

    #[test]
    fn parse_skips_comments_and_blank_lines() {
        let parsed = parse_baseline("# header\n\nb.txt\n  a.txt  \n# tail\n");
        assert_eq!(parsed, set(&["a.txt", "b.txt"]));
    }

    #[test]
    fn render_round_trips_through_parse() {
        let entries = set(&["z/y.log", "a/b.toml"]);
        assert_eq!(parse_baseline(&render_baseline(&entries)), entries);
    }

    #[test]
    fn compare_reports_new_offenders_and_stale_entries() {
        let report = compare(&set(&["a", "new"]), &set(&["a", "cleaned"]));
        assert_eq!(
            report,
            HygieneReport {
                new_offenders: vec!["new".to_owned()],
                stale_entries: vec!["cleaned".to_owned()],
            }
        );
        assert!(!report.is_clean());
        assert!(compare(&set(&["a"]), &set(&["a"])).is_clean());
    }

    #[test]
    fn pruning_never_adds_an_entry() {
        let pruned = pruned_baseline(&set(&["a", "new"]), &set(&["a", "cleaned"]));
        assert_eq!(pruned, set(&["a"]));
    }
}
