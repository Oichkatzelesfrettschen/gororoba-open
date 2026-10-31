// SPDX-License-Identifier: MIT
//! lambda-sweep: E-027 imbalance-coupling (lambda) scaling sweep.
//!
//! Builds `percolation-experiment` with GPU support, runs it once per lambda
//! value on a 64^3 grid, stores each run's `e027_results.toml` as
//! `e027_lambda_<lambda>_grid64.toml` under `data/e027/lambda_sweep`
//! (relative to the working directory), and prints a PASS/FAIL table keyed on
//! the permutation-test p-value threshold of 0.05.

use std::{
    cmp::Ordering,
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode},
};

const GRID_SIZE: u32 = 64;
const LBM_STEPS: u32 = 2500;
const NU_BASE: &str = "0.333";
const N_PERMUTATIONS: u32 = 1000;
const SEED: u32 = 42;
const OUTPUT_DIR: &str = "data/e027/lambda_sweep";
const LAMBDAS: [&str; 8] = ["0.1", "0.5", "1.0", "2.0", "5.0", "10.0", "20.0", "50.0"];
const P_VALUE_THRESHOLD: f64 = 0.05;
const RULE: &str = "========================================";
const TABLE_RULE: &str = "============================================================";

/// Argument vector of the `cargo build` that prepares the experiment binary.
fn build_args(jobs: usize) -> Vec<String> {
    [
        "build",
        "--release",
        "--features",
        "gpu",
        "--bin",
        "percolation-experiment",
    ]
    .iter()
    .map(|arg| (*arg).to_string())
    .chain([format!("-j{jobs}")])
    .collect()
}

/// Argument vector of the `cargo run` for one lambda value.
fn run_args(lambda: &str) -> Vec<String> {
    let mut args: Vec<String> = [
        "run",
        "--release",
        "--features",
        "gpu",
        "--bin",
        "percolation-experiment",
        "--",
    ]
    .iter()
    .map(|arg| (*arg).to_string())
    .collect();
    for (flag, value) in [
        ("--grid-size", GRID_SIZE.to_string()),
        ("--lbm-steps", LBM_STEPS.to_string()),
        ("--nu-base", NU_BASE.to_string()),
        ("--lambda", lambda.to_string()),
        ("--n-permutations", N_PERMUTATIONS.to_string()),
        ("--seed", SEED.to_string()),
        ("--output-dir", OUTPUT_DIR.to_string()),
    ] {
        args.push(flag.to_string());
        args.push(value);
    }
    args.push("--use-gpu".to_string());
    args.push("--verbose".to_string());
    args
}

fn labeled_result_path(lambda: &str) -> PathBuf {
    Path::new(OUTPUT_DIR).join(format!("e027_lambda_{lambda}_grid{GRID_SIZE}.toml"))
}

/// Run `cargo` with `args`; a non-zero status is returned as `Err(code)`.
fn cargo(args: &[String]) -> Result<(), u8> {
    let status = Command::new("cargo").args(args).status().map_err(|error| {
        eprintln!("failed to spawn cargo: {error}");
        127_u8
    })?;
    if status.success() {
        Ok(())
    } else {
        Err(status
            .code()
            .map_or(1, |code| u8::try_from(code).unwrap_or(1)))
    }
}

/// Order two strings the way `sort -V` does for file names: digit runs
/// compare by numeric value, every other byte compares by value.
fn version_cmp(a: &str, b: &str) -> Ordering {
    let (mut a, mut b) = (a.as_bytes(), b.as_bytes());
    while let (Some(&x), Some(&y)) = (a.first(), b.first()) {
        if x.is_ascii_digit() && y.is_ascii_digit() {
            let run = |s: &[u8]| s.iter().take_while(|c| c.is_ascii_digit()).count();
            let (la, lb) = (run(a), run(b));
            let na = std::str::from_utf8(&a[..la])
                .unwrap_or("0")
                .trim_start_matches('0');
            let nb = std::str::from_utf8(&b[..lb])
                .unwrap_or("0")
                .trim_start_matches('0');
            let ord = na.len().cmp(&nb.len()).then_with(|| na.cmp(nb));
            if ord != Ordering::Equal {
                return ord;
            }
            a = &a[la..];
            b = &b[lb..];
        } else {
            if x != y {
                return x.cmp(&y);
            }
            a = &a[1..];
            b = &b[1..];
        }
    }
    a.len().cmp(&b.len())
}

/// Value of the first line containing `key`: the text between the first and
/// second `=` with quotes dropped and whitespace collapsed.
fn field_after(text: &str, key: &str) -> String {
    text.lines()
        .find(|line| line.contains(key))
        .and_then(|line| line.split('=').nth(1))
        .map(|value| {
            value
                .replace(['"', '\''], "")
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ")
        })
        .unwrap_or_default()
}

struct SummaryRow {
    lambda: String,
    p_value: String,
    channels: String,
    status: &'static str,
}

fn summary_row(text: &str) -> Option<SummaryRow> {
    let lambda = field_after(text, "lambda =");
    let p_value = field_after(text, "p_value =");
    let channels = field_after(text, "n_channels_detected =");
    if lambda.is_empty() || p_value.is_empty() {
        return None;
    }
    let passes = p_value
        .parse::<f64>()
        .is_ok_and(|value| value < P_VALUE_THRESHOLD);
    Some(SummaryRow {
        lambda,
        p_value,
        channels,
        status: if passes { "PASS" } else { "FAIL" },
    })
}

fn result_files() -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = fs::read_dir(OUTPUT_DIR)
        .into_iter()
        .flatten()
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("e027_lambda_") && name.ends_with(".toml"))
        })
        .collect();
    files.sort_by(|a, b| version_cmp(&a.to_string_lossy(), &b.to_string_lossy()));
    files
}

fn print_summary() {
    println!("Generating summary...");
    println!();
    println!("Lambda Sweep Summary:");
    println!("{TABLE_RULE}");
    println!(
        "{:<10} {:<15} {:<10} Status",
        "Lambda", "P-Value", "Channels"
    );
    println!("{}", "-".repeat(60));
    for file in result_files() {
        let text = fs::read_to_string(&file).unwrap_or_default();
        if let Some(row) = summary_row(&text) {
            println!(
                "{:<10} {:<15} {:<10} {}",
                row.lambda, row.p_value, row.channels, row.status
            );
        }
    }
    println!("{TABLE_RULE}");
}

fn sweep() -> Result<(), u8> {
    fs::create_dir_all(OUTPUT_DIR).map_err(|error| {
        eprintln!("cannot create {OUTPUT_DIR}: {error}");
        1_u8
    })?;
    println!("{RULE}");
    println!("Phase 1.4.1: Lambda Scaling Sweep");
    println!("{RULE}");
    println!("Grid: {GRID_SIZE}^3");
    println!("LBM steps: {LBM_STEPS}");
    println!("Lambda values: {}", LAMBDAS.join(" "));
    println!("Total runs: {}", LAMBDAS.len());
    println!();

    println!("Building percolation-experiment binary with GPU support...");
    let jobs = std::thread::available_parallelism().map_or(1, usize::from);
    cargo(&build_args(jobs))?;
    println!();

    for lambda in LAMBDAS {
        println!("{RULE}");
        println!("Running: lambda = {lambda}");
        println!("{RULE}");
        let labeled = labeled_result_path(lambda);
        cargo(&run_args(lambda))?;
        let produced = Path::new(OUTPUT_DIR).join("e027_results.toml");
        if produced.is_file() {
            fs::rename(&produced, &labeled).map_err(|error| {
                eprintln!(
                    "cannot move {} to {}: {error}",
                    produced.display(),
                    labeled.display()
                );
                1_u8
            })?;
            println!("Saved result to: {}", labeled.display());
        } else {
            println!("WARNING: Expected output file not found");
        }
        println!();
    }

    println!("{RULE}");
    println!("Lambda Sweep Complete");
    println!("{RULE}");
    println!("Results in: {OUTPUT_DIR}");
    println!();
    print_summary();
    println!();
    println!("Next steps:");
    println!("1. Review results to identify optimal lambda");
    println!("2. Update Phase 1.4.3 grid sweep with optimal lambda");
    println!("3. Proceed to Phase 1.5 analytical work");
    Ok(())
}

fn main() -> ExitCode {
    match sweep() {
        Ok(()) => ExitCode::SUCCESS,
        Err(code) => ExitCode::from(code),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn run_args_match_experiment_cli() {
        let args = run_args("0.5").join(" ");
        assert_eq!(
            args,
            "run --release --features gpu --bin percolation-experiment -- --grid-size 64 \
             --lbm-steps 2500 --nu-base 0.333 --lambda 0.5 --n-permutations 1000 --seed 42 \
             --output-dir data/e027/lambda_sweep --use-gpu --verbose"
        );
    }

    #[test]
    fn version_sort_orders_numeric_runs() {
        let mut names = vec!["l_10.0_g", "l_2.0_g", "l_0.5_g", "l_1.0_g", "l_20.0_g"];
        names.sort_by(|a, b| version_cmp(a, b));
        assert_eq!(
            names,
            ["l_0.5_g", "l_1.0_g", "l_2.0_g", "l_10.0_g", "l_20.0_g"]
        );
    }

    #[test]
    fn summary_row_classifies_p_value() {
        let pass = summary_row("lambda = 1.0\np_value = 0.01\nn_channels_detected = 3\n").unwrap();
        assert_eq!((pass.status, pass.channels.as_str()), ("PASS", "3"));
        let fail = summary_row("lambda = 2.0\np_value = 0.5\n").unwrap();
        assert_eq!(fail.status, "FAIL");
        assert!(summary_row("lambda = 2.0\n").is_none());
    }
}
