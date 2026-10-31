// SPDX-License-Identifier: GPL-2.0-or-later
//! `xtask bootstrap-user-local-xdg`: install the gororoba-open developer
//! configuration into user-local locations.
//!
//! Writes `$HOME/.cargo/config.toml`, `$XDG_CONFIG_HOME/nextest.toml`, the
//! `$XDG_CACHE_HOME/gororoba-lit-cache/` directory and, on request,
//! `$HOME/.gemini/settings.json`. An existing target file receives a
//! `.bak.<timestamp>` copy unless `--force` is set.

use anyhow::{Context, Result, bail};
use chrono::Local;
use clap::Parser;
use std::{
    env, fs,
    path::{Path, PathBuf},
};

const NEXTTEST_CONFIG: &str = "\
# User-local nextest config for gororoba-open.
#
# WHY: The canonical profile definitions (default, ci, smoke, heavy, gpu) live
# in the workspace at .config/nextest.toml. Nextest merges workspace config with
# user config; workspace config takes precedence for any duplicate keys.
#
# This file is for MACHINE-SPECIFIC overrides only, such as local thread counts
# or per-developer timing tweaks. Do not duplicate profile definitions here --
# edit .config/nextest.toml in the workspace root instead.
#
# Example machine-specific override (uncomment and adjust as needed):
# [profile.default]
# test-threads = 4
";

const GEMINI_SETTINGS: &str = "\
{
  \"context\": {
    \"discoveryMaxDirs\": 100
  },
  \"fileReadLineLimit\": 500
}
";

#[derive(Parser, Debug)]
#[command(
    name = "bootstrap-user-local-xdg",
    about = "Install open_gororoba developer config into user-local locations only",
    after_help = "\
Installed locations:
- ~/.cargo/config.toml
- $XDG_CONFIG_HOME/nextest.toml (defaults to ~/.config/nextest.toml)
- $XDG_CACHE_HOME/gororoba-lit-cache/ (defaults to ~/.cache/gororoba-lit-cache/)
- ~/.gemini/settings.json (optional; only with --with-gemini)

Existing files are backed up with a timestamp suffix unless --force is used.

Credential-bearing runtime variables are documented in:
- docs/engineering/runtime_env_inventory.txt
- docs/engineering/lit_search_env_vars.txt"
)]
pub struct BootstrapXdgCli {
    /// Overwrite existing files without writing a timestamped backup.
    #[arg(long)]
    force: bool,
    /// Also write ~/.gemini/settings.json.
    #[arg(long)]
    with_gemini: bool,
}

/// Resolved process environment that determines every written path.
struct Layout {
    root: PathBuf,
    home: PathBuf,
    xdg_config_home: PathBuf,
    xdg_cache_home: PathBuf,
    tmpdir: Option<PathBuf>,
    stamp: String,
}

/// Read a variable the way `${NAME:-default}` does: unset and empty both
/// select the default.
fn env_nonempty(name: &str) -> Option<PathBuf> {
    env::var_os(name)
        .filter(|value| !value.is_empty())
        .map(PathBuf::from)
}

impl Layout {
    fn from_env(root: PathBuf) -> Result<Self> {
        let home = env::var_os("HOME")
            .map(PathBuf::from)
            .context("HOME is not set")?;
        let xdg_config_home =
            env_nonempty("XDG_CONFIG_HOME").unwrap_or_else(|| home.join(".config"));
        let xdg_cache_home = env_nonempty("XDG_CACHE_HOME").unwrap_or_else(|| home.join(".cache"));
        Ok(Self {
            root,
            home,
            xdg_config_home,
            xdg_cache_home,
            tmpdir: env_nonempty("TMPDIR"),
            stamp: Local::now().format("%Y%m%d%H%M%S").to_string(),
        })
    }
}

struct BuildDirChoice {
    dir: PathBuf,
    reason: &'static str,
    fallback_details: Vec<String>,
}

/// Create `dir` and confirm a file can be created inside it.
fn dir_is_writable(dir: &Path) -> bool {
    if fs::create_dir_all(dir).is_err() {
        return false;
    }
    let probe = dir.join(format!(".write-probe-{}", std::process::id()));
    let ok = fs::File::create(&probe).is_ok();
    let _ = fs::remove_file(&probe);
    ok
}

fn select_cargo_build_dir(layout: &Layout) -> Result<BuildDirChoice> {
    let mut candidates: Vec<(PathBuf, &'static str)> = Vec::new();
    let mut fallback_details: Vec<String> = Vec::new();
    match &layout.tmpdir {
        Some(tmpdir) => candidates.push((tmpdir.clone(), "TMPDIR is set and writable")),
        None => fallback_details.push("TMPDIR is unset".to_string()),
    }
    candidates.push((PathBuf::from("/tmp"), "/tmp is writable"));
    candidates.push((layout.xdg_cache_home.clone(), "using XDG cache fallback"));

    for (root, reason) in candidates {
        let dir = root.join("open_gororoba-cargo-build").join("ambient");
        if dir_is_writable(&dir) {
            return Ok(BuildDirChoice {
                dir,
                reason,
                fallback_details,
            });
        }
        fallback_details.push(format!(
            "skipped '{}' (unable to create/write '{}')",
            root.display(),
            dir.display()
        ));
    }
    let mut message = String::from("unable to select a writable Cargo build-dir root.");
    for detail in &fallback_details {
        message.push_str(&format!("\n  - {detail}"));
    }
    bail!(message)
}

fn require_writable_dir(path: &Path) -> Result<()> {
    if !path.is_dir() {
        bail!("expected directory does not exist: {}", path.display());
    }
    if !dir_is_writable(path) {
        bail!("directory is not writable: {}", path.display());
    }
    Ok(())
}

fn backup_if_needed(path: &Path, force: bool, stamp: &str) -> Result<()> {
    if path.exists() && !force {
        let mut backup = path.as_os_str().to_owned();
        backup.push(format!(".bak.{stamp}"));
        fs::copy(path, &backup)
            .with_context(|| format!("back up {} to {:?}", path.display(), backup))?;
    }
    Ok(())
}

fn cargo_config(root: &Path, stamp: &str, build_dir: &Path) -> String {
    format!(
        "\
# gororoba-open user-local Cargo configuration
# Generated by `cargo run -p xtask -- bootstrap-user-local-xdg` in {root} on {stamp}

[build]
target-dir = \"{root}/.cache/cargo-default-target\"
build-dir = \"{build_dir}\"
incremental = false

[env]
CARGO_INCREMENTAL = \"0\"

[cache]
auto-clean-frequency = \"1 day\"

[unstable]
gc = true

[target.'cfg(target_arch = \"x86_64\")']
rustflags = [\"-C\", \"target-cpu=native\", \"-C\", \"link-arg=-fuse-ld=mold\", \"-Dwarnings\"]
linker = \"clang\"

[profile.dev]
split-debuginfo = \"unpacked\"
",
        root = root.display(),
        build_dir = build_dir.display(),
    )
}

fn install(layout: &Layout, cli: &BootstrapXdgCli) -> Result<()> {
    let choice = select_cargo_build_dir(layout)?;
    println!("Selected Cargo build-dir: {}", choice.dir.display());
    println!("  reason: {}", choice.reason);
    if !choice.fallback_details.is_empty() {
        println!("  fallback details:");
        for detail in &choice.fallback_details {
            println!("    - {detail}");
        }
    }

    let cargo_dir = layout.home.join(".cargo");
    let lit_cache = layout.xdg_cache_home.join("gororoba-lit-cache");
    for dir in [&cargo_dir, &layout.xdg_config_home, &lit_cache, &choice.dir] {
        fs::create_dir_all(dir).with_context(|| format!("create {}", dir.display()))?;
    }
    for dir in [&cargo_dir, &layout.xdg_config_home, &lit_cache, &choice.dir] {
        require_writable_dir(dir)?;
    }

    let cargo_config_path = cargo_dir.join("config.toml");
    backup_if_needed(&cargo_config_path, cli.force, &layout.stamp)?;
    fs::write(
        &cargo_config_path,
        cargo_config(&layout.root, &layout.stamp, &choice.dir),
    )
    .with_context(|| format!("write {}", cargo_config_path.display()))?;

    let nextest_path = layout.xdg_config_home.join("nextest.toml");
    backup_if_needed(&nextest_path, cli.force, &layout.stamp)?;
    fs::write(&nextest_path, NEXTTEST_CONFIG)
        .with_context(|| format!("write {}", nextest_path.display()))?;

    if cli.with_gemini {
        let gemini_dir = layout.home.join(".gemini");
        fs::create_dir_all(&gemini_dir)
            .with_context(|| format!("create {}", gemini_dir.display()))?;
        let gemini_path = gemini_dir.join("settings.json");
        backup_if_needed(&gemini_path, cli.force, &layout.stamp)?;
        fs::write(&gemini_path, GEMINI_SETTINGS)
            .with_context(|| format!("write {}", gemini_path.display()))?;
    }

    println!("Installed user-local open_gororoba config:");
    println!("  ~/.cargo/config.toml");
    println!("  {}", nextest_path.display());
    println!("  {}/", lit_cache.display());
    if cli.with_gemini {
        println!("  ~/.gemini/settings.json");
    }
    println!();
    println!("User-local runtime variable guidance:");
    println!(
        "  {}/docs/engineering/runtime_env_inventory.txt",
        layout.root.display()
    );
    println!(
        "  {}/docs/engineering/lit_search_env_vars.txt",
        layout.root.display()
    );
    Ok(())
}

pub fn run(cli: BootstrapXdgCli, root: PathBuf) -> Result<()> {
    let layout = Layout::from_env(root)?;
    install(&layout, &cli)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    fn layout_in(base: &Path) -> Layout {
        Layout {
            root: PathBuf::from("/repo"),
            home: base.join("home"),
            xdg_config_home: base.join("home/.config"),
            xdg_cache_home: base.join("home/.cache"),
            tmpdir: Some(base.join("tmp")),
            stamp: "20260101000000".to_string(),
        }
    }

    #[test]
    fn default_run_writes_cargo_and_nextest_only() {
        let base = tempdir().unwrap();
        let layout = layout_in(base.path());
        let cli = BootstrapXdgCli {
            force: false,
            with_gemini: false,
        };
        install(&layout, &cli).unwrap();
        let cargo = fs::read_to_string(layout.home.join(".cargo/config.toml")).unwrap();
        assert!(cargo.contains("target-dir = \"/repo/.cache/cargo-default-target\""));
        assert!(cargo.contains(&format!(
            "build-dir = \"{}/tmp/open_gororoba-cargo-build/ambient\"",
            base.path().display()
        )));
        assert!(layout.xdg_config_home.join("nextest.toml").is_file());
        assert!(layout.xdg_cache_home.join("gororoba-lit-cache").is_dir());
        assert!(!layout.home.join(".gemini").exists());
    }

    #[test]
    fn rerun_backs_up_unless_forced() {
        let base = tempdir().unwrap();
        let layout = layout_in(base.path());
        let plain = BootstrapXdgCli {
            force: false,
            with_gemini: true,
        };
        install(&layout, &plain).unwrap();
        install(&layout, &plain).unwrap();
        let backup = layout.home.join(".cargo/config.toml.bak.20260101000000");
        assert!(backup.is_file());
        assert!(
            layout
                .home
                .join(".gemini/settings.json.bak.20260101000000")
                .is_file()
        );

        fs::remove_file(&backup).unwrap();
        let forced = BootstrapXdgCli {
            force: true,
            with_gemini: true,
        };
        install(&layout, &forced).unwrap();
        assert!(!backup.exists());
    }
}
