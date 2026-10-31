// SPDX-License-Identifier: MIT
//
// Cargo cache footprint report. The repo-local cache family and the
// per-checkout temporary gate root are sized with `du` and compared against
// GiB budgets. `make cargo-cache-status` passes the budgets through
// `CARGO_CACHE_REPO_BUDGET_GIB` and `CARGO_CACHE_TMP_BUDGET_GIB`.

use anyhow::{Context, Result, bail};
use sha2::{Digest, Sha256};
use std::path::Path;
use std::process::Command;

pub const DEFAULT_REPO_BUDGET_GIB: u64 = 150;
pub const DEFAULT_TMP_BUDGET_GIB: u64 = 16;

/// Repo-local cache directories, relative to the repository root.
pub const REPO_CACHE_RELATIVE: &[&str] = &[
    ".cache/cargo-default-target",
    ".cache/gate-target",
    ".cache/gate-cbuild",
    ".cache/phase7-target",
    ".cache/sparse-mainline-target",
    ".cache/cargo-home",
    "target",
];

/// First 16 hex digits of the SHA-256 of the repository root path.
pub fn repo_hash(repo_root: &str) -> String {
    let digest = Sha256::digest(repo_root.as_bytes());
    digest.iter().take(8).fold(String::new(), |mut acc, byte| {
        acc.push_str(&format!("{byte:02x}"));
        acc
    })
}

/// Gibibytes with two decimals from a size in kibibytes.
pub fn format_gib(kib: u64) -> String {
    format!("{:.2}", kib as f64 / 1024.0 / 1024.0)
}

pub fn budget_kib(budget_gib: u64) -> u64 {
    budget_gib.saturating_mul(1024 * 1024)
}

/// Budget verdict for one cache family.
#[derive(Debug, PartialEq, Eq)]
pub struct BudgetStatus {
    pub lines: [String; 3],
    pub over_budget: bool,
}

pub fn budget_status(label: &str, kib: u64, budget_gib: u64) -> BudgetStatus {
    let over_budget = kib > budget_kib(budget_gib);
    BudgetStatus {
        lines: [
            format!("{label}_total_gib={}", format_gib(kib)),
            format!("{label}_budget_gib={budget_gib}"),
            format!(
                "status.{label}={}",
                if over_budget { "over-budget" } else { "ok" }
            ),
        ],
        over_budget,
    }
}

/// Budget from the named environment variable; unset or empty selects the default.
pub fn budget_from_env(name: &str, default: u64) -> Result<u64> {
    match std::env::var(name) {
        Ok(value) if !value.is_empty() => value
            .parse::<u64>()
            .with_context(|| format!("{name} must be a non-negative integer, got {value:?}")),
        _ => Ok(default),
    }
}

fn du(flag: &str, path: &Path) -> Result<String> {
    let out = Command::new("du")
        .arg(flag)
        .arg(path)
        .output()
        .context("run du")?;
    if !out.status.success() {
        bail!("du {flag} {} failed", path.display());
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// The `du -sh` line for a path, or `0<TAB>path` when the path is absent.
pub fn show_path(path: &Path) -> Result<String> {
    if path.exists() {
        Ok(du("-sh", path)?.trim_end_matches('\n').to_string())
    } else {
        Ok(format!("0\t{}", path.display()))
    }
}

/// Size in KiB from `du -sk`; absent paths count as zero.
pub fn path_kib(path: &Path) -> Result<u64> {
    if !path.exists() {
        return Ok(0);
    }
    let text = du("-sk", path)?;
    text.split_whitespace()
        .next()
        .and_then(|field| field.parse().ok())
        .with_context(|| format!("parse du -sk output for {}", path.display()))
}

fn sum_kib(paths: &[std::path::PathBuf]) -> Result<u64> {
    paths.iter().try_fold(0u64, |acc, p| Ok(acc + path_kib(p)?))
}

/// Print the report and return the process exit code (1 when over budget).
pub fn run(repo_root: &Path) -> Result<i32> {
    let repo_budget = budget_from_env("CARGO_CACHE_REPO_BUDGET_GIB", DEFAULT_REPO_BUDGET_GIB)?;
    let tmp_budget = budget_from_env("CARGO_CACHE_TMP_BUDGET_GIB", DEFAULT_TMP_BUDGET_GIB)?;
    let root_text = repo_root.display().to_string();
    let hash = repo_hash(&root_text);
    let tmp_base = match std::env::var("TMPDIR") {
        Ok(value) if !value.is_empty() => value,
        _ => "/tmp".to_string(),
    };
    let tmp_root = format!("{tmp_base}/open_gororoba-cargo-build");
    let gate_root = format!("{tmp_root}/gate/{hash}");
    let ambient_root = format!("{tmp_root}/ambient");
    let home = std::env::var("HOME").context("HOME is not set")?;

    println!("cargo-cache-layout");
    println!("repo_root={root_text}");
    println!("repo_hash={hash}");
    println!("tmp_root={tmp_root}");
    println!("ambient_root={ambient_root}");
    println!("gate_root={gate_root}");
    println!();

    let repo_paths: Vec<_> = REPO_CACHE_RELATIVE
        .iter()
        .map(|rel| repo_root.join(rel))
        .collect();
    let tmp_paths = [
        std::path::PathBuf::from(&ambient_root),
        std::path::PathBuf::from(&gate_root),
    ];
    for path in repo_paths.iter().chain(tmp_paths.iter()) {
        println!("{}", show_path(path)?);
    }
    println!("{}", show_path(&Path::new(&home).join(".cargo"))?);
    println!();

    let repo = budget_status("repo_cache", sum_kib(&repo_paths)?, repo_budget);
    let tmp = budget_status("tmp_cache", sum_kib(&tmp_paths)?, tmp_budget);
    for line in repo.lines.iter().chain(tmp.lines.iter()) {
        println!("{line}");
    }
    if repo.over_budget {
        println!("remediation.repo_cache=make cache-sweep-soft");
    }
    if tmp.over_budget {
        println!("remediation.tmp_cache=inspect and remove stale tmp cache under {tmp_root}");
    }
    Ok(i32::from(repo.over_budget || tmp.over_budget))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_is_sixteen_hex_digits_of_sha256() {
        // sha256("abc") = ba7816bf8f01cfea...
        assert_eq!(repo_hash("abc"), "ba7816bf8f01cfea");
    }

    #[test]
    fn gib_formatting_rounds_to_two_decimals() {
        assert_eq!(format_gib(0), "0.00");
        assert_eq!(format_gib(1024 * 1024), "1.00");
        assert_eq!(format_gib(1024 * 1024 * 3 / 2), "1.50");
    }

    #[test]
    fn budget_boundary_is_strictly_greater() {
        assert!(!budget_status("x", 1024 * 1024, 1).over_budget);
        let over = budget_status("x", 1024 * 1024 + 1, 1);
        assert!(over.over_budget);
        assert_eq!(over.lines[2], "status.x=over-budget");
        assert_eq!(over.lines[1], "x_budget_gib=1");
    }

    #[test]
    fn absent_path_reports_zero() {
        let tmp = tempfile::tempdir().unwrap();
        let missing = tmp.path().join("nope");
        assert_eq!(path_kib(&missing).unwrap(), 0);
        assert_eq!(
            show_path(&missing).unwrap(),
            format!("0\t{}", missing.display())
        );
    }

    #[test]
    fn present_path_sizes_through_du() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::write(tmp.path().join("f"), vec![0u8; 8192]).unwrap();
        assert!(path_kib(tmp.path()).unwrap() >= 8);
        assert!(
            show_path(tmp.path())
                .unwrap()
                .ends_with(&tmp.path().display().to_string())
        );
    }
}
