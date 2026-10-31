// SPDX-License-Identifier: MIT
//
// Native BLAS and LAPACK detection report. `pkg-config` answers presence,
// version, and link flags for each candidate library; the report never
// enables a Cargo feature. The fixed prose lines mirror the feature table in
// `crates/gororoba_algebra/Cargo.toml`, where `openblas-system` is the only
// repo-exposed native BLAS feature.

use std::io::ErrorKind;
use std::process::Command;

/// Libraries probed through `pkg-config`, in report order.
pub const PKG_CONFIG_CANDIDATES: &[&str] = &["openblas", "blis", "blas", "lapack", "lapacke"];

/// Probe outcome for one `pkg-config` package.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PkgStatus {
    /// `pkg-config` is not installed.
    Skipped,
    Missing,
    Present {
        version: String,
        libs: String,
    },
}

const HEADER_LINES: &[&str] = &[
    "Native BLAS and LAPACK detection",
    "- Repo-exposed Cargo feature: openblas-system",
    "- Opt-in mechanism: the `Cargo.toml` `[features]` table, enabled with `cargo ... --features <name>`",
    "- Default behavior: no native BLAS feature is enabled unless a build command opts in explicitly",
    "- Probe method: pkg-config for installed native libraries plus platform notes for non-pkg-config backends",
];

const MACOS_NOTE: &str = "- Host note: macOS may provide Accelerate as a system framework, but this repo does not currently expose an `accelerate` feature.";

const FOOTER_LINES: &[&str] = &[
    "- Repo mapping: `openblas-system` expects a system OpenBLAS install and is the only repo-exposed native BLAS feature.",
    "- Upstream Burn also forwards `openblas`, `accelerate`, and `blas-netlib`, but this repo intentionally does not expose them because the source-backed path is not reproducible in offline gates.",
    "- Upstream `blas-src` supports `blis`, `intel-mkl`, and `r`, but Burn does not forward those selectors for this crate, so they are not repo opt-ins today.",
];

/// Collapse every whitespace run to one space and trim both ends.
pub fn collapse_whitespace(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// One report line for a probed package.
pub fn format_pkg_line(pkg: &str, status: &PkgStatus) -> String {
    match status {
        PkgStatus::Skipped => format!("- pkg-config {pkg}: skipped (pkg-config not installed)"),
        PkgStatus::Missing => format!("- pkg-config {pkg}: missing"),
        PkgStatus::Present { version, libs } if libs.is_empty() => {
            format!("- pkg-config {pkg}: present (version {version})")
        }
        PkgStatus::Present { version, libs } => {
            format!("- pkg-config {pkg}: present (version {version}; libs {libs})")
        }
    }
}

/// Render the full report. `os` is `std::env::consts::OS`.
pub fn render_report(statuses: &[(&str, PkgStatus)], os: &str) -> String {
    let mut out = String::new();
    for line in HEADER_LINES {
        out.push_str(line);
        out.push('\n');
    }
    for (pkg, status) in statuses {
        out.push_str(&format_pkg_line(pkg, status));
        out.push('\n');
    }
    if os == "macos" {
        out.push_str(MACOS_NOTE);
        out.push('\n');
    }
    for line in FOOTER_LINES {
        out.push_str(line);
        out.push('\n');
    }
    out
}

fn pkg_config_output(args: &[&str]) -> String {
    Command::new("pkg-config")
        .args(args)
        .output()
        .map(|out| collapse_whitespace(&String::from_utf8_lossy(&out.stdout)))
        .unwrap_or_default()
}

/// Probe one package by invoking `pkg-config`.
pub fn probe_pkg(pkg: &str) -> PkgStatus {
    let exists = match Command::new("pkg-config").args(["--exists", pkg]).output() {
        Ok(out) => out.status.success(),
        Err(err) if err.kind() == ErrorKind::NotFound => return PkgStatus::Skipped,
        Err(_) => false,
    };
    if !exists {
        return PkgStatus::Missing;
    }
    PkgStatus::Present {
        version: pkg_config_output(&["--modversion", pkg]),
        libs: pkg_config_output(&["--libs", pkg]),
    }
}

/// Probe every candidate and render the report for the running host.
pub fn detect() -> String {
    let statuses: Vec<(&str, PkgStatus)> = PKG_CONFIG_CANDIDATES
        .iter()
        .map(|pkg| (*pkg, probe_pkg(pkg)))
        .collect();
    render_report(&statuses, std::env::consts::OS)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn whitespace_runs_collapse_and_ends_trim() {
        assert_eq!(collapse_whitespace(" -L/a \n -lb\t-lc\n"), "-L/a -lb -lc");
        assert_eq!(collapse_whitespace("\n"), "");
    }

    #[test]
    fn pkg_lines_cover_each_status() {
        assert_eq!(
            format_pkg_line("blis", &PkgStatus::Skipped),
            "- pkg-config blis: skipped (pkg-config not installed)"
        );
        assert_eq!(
            format_pkg_line("blis", &PkgStatus::Missing),
            "- pkg-config blis: missing"
        );
        let bare = PkgStatus::Present {
            version: "1.0".into(),
            libs: String::new(),
        };
        assert_eq!(
            format_pkg_line("blas", &bare),
            "- pkg-config blas: present (version 1.0)"
        );
        let full = PkgStatus::Present {
            version: "1.0".into(),
            libs: "-lblas".into(),
        };
        assert_eq!(
            format_pkg_line("blas", &full),
            "- pkg-config blas: present (version 1.0; libs -lblas)"
        );
    }

    #[test]
    fn macos_note_appears_only_on_macos() {
        let statuses = [("openblas", PkgStatus::Missing)];
        assert!(render_report(&statuses, "macos").contains("Accelerate"));
        assert!(!render_report(&statuses, "linux").contains("Accelerate"));
    }

    #[test]
    fn report_starts_with_title_and_ends_with_newline() {
        let report = render_report(&[], "linux");
        assert!(report.starts_with("Native BLAS and LAPACK detection\n"));
        assert!(report.ends_with("not repo opt-ins today.\n"));
    }
}
