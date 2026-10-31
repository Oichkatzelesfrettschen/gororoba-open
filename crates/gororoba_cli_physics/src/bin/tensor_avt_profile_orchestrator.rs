// SPDX-License-Identifier: MIT
//! tensor-avt-profile-orchestrator: profile the `tensor_avt_profile` example
//! of `gororoba_algebra` on the CPU backend and each GPU mode.
//!
//! Per dimension and backend the orchestrator builds the example in the
//! bench profile, then records `perf stat`, `perf record` with
//! `perf report`, `/usr/bin/time -v`, `heaptrack`, and optionally
//! `cargo flamegraph`, `samply` and `ncu`, and finally writes a Markdown
//! summary. The GPU backend also samples `nvidia-smi` once per second for
//! the duration of the capture. Configuration comes from environment
//! variables; an unset or empty variable selects its default.
//!
//! | Variable | Default |
//! | --- | --- |
//! | `PROFILE_TIMESTAMP` | local `%Y-%m-%d/%H%M%S` |
//! | `TENSOR_AVT_PROFILE_ROOT` | `<repo>/.cache/profiles/tensor_avt/<timestamp>` |
//! | `CARGO_HOME` | `<repo>/.cache/cargo-home` |
//! | `TENSOR_AVT_CPU_TARGET_DIR` | `<repo>/.cache/tensor_avt_profile/cpu-target` |
//! | `TENSOR_AVT_GPU_TARGET_DIR` | `<repo>/.cache/tensor_avt_profile/gpu-target` |
//! | `TENSOR_AVT_PATH` | `single` |
//! | `TENSOR_AVT_DIM` / `TENSOR_AVT_DIMS` | `256` / the value of `TENSOR_AVT_DIM` |
//! | `TENSOR_AVT_BATCH_SIZE` | `16` |
//! | `TENSOR_AVT_ITERS` | `32` |
//! | `TENSOR_AVT_WARMUP` | `4` |
//! | `TENSOR_AVT_SEED` | `7` |
//! | `TENSOR_AVT_GPU_MODES` / `TENSOR_AVT_GPU_MODE` | `host,workspace,resident` |
//! | `TENSOR_AVT_WITH_NCU` | `0` |
//! | `TENSOR_AVT_WITH_FLAMEGRAPH` | `1` |
//! | `TENSOR_AVT_WITH_SAMPLY` | `0` |

use std::{
    env,
    ffi::OsString,
    fs::{self, File, OpenOptions},
    io::Write as _,
    path::{Path, PathBuf},
    process::{Child, Command, ExitCode, Stdio},
};

/// Process exit status that aborts the orchestration.
struct Abort(u8);

type Step<T = ()> = Result<T, Abort>;

fn env_nonempty(name: &str) -> Option<String> {
    env::var(name).ok().filter(|value| !value.is_empty())
}

fn env_or(name: &str, default: &str) -> String {
    env_nonempty(name).unwrap_or_else(|| default.to_string())
}

/// Split a comma- or blank-separated list on its first line.
fn split_list(raw: &str) -> Vec<String> {
    raw.lines()
        .next()
        .unwrap_or("")
        .replace(',', " ")
        .split_whitespace()
        .map(str::to_string)
        .collect()
}

struct Config {
    out_root: String,
    cargo_home: String,
    cpu_target_dir: String,
    gpu_target_dir: String,
    path_kind: String,
    dims: Vec<String>,
    batch_size: String,
    iters: String,
    warmup: String,
    seed: String,
    gpu_modes: Vec<String>,
    with_ncu: bool,
    with_flamegraph: bool,
    with_samply: bool,
}

impl Config {
    fn from_env(root: &Path) -> Step<Self> {
        let root = root.display();
        let stamp = env_nonempty("PROFILE_TIMESTAMP")
            .unwrap_or_else(|| chrono::Local::now().format("%Y-%m-%d/%H%M%S").to_string());
        let dim = env_or("TENSOR_AVT_DIM", "256");
        let dims = split_list(&env_or("TENSOR_AVT_DIMS", &dim));
        if dims.is_empty() {
            eprintln!("TENSOR_AVT_DIMS resolved to an empty dimension list");
            return Err(Abort(2));
        }
        let default_modes = env_or("TENSOR_AVT_GPU_MODE", "host,workspace,resident");
        let gpu_modes = split_list(&env_or("TENSOR_AVT_GPU_MODES", &default_modes));
        if gpu_modes.is_empty() {
            eprintln!("TENSOR_AVT_GPU_MODES resolved to an empty mode list");
            return Err(Abort(2));
        }
        Ok(Self {
            out_root: env_or(
                "TENSOR_AVT_PROFILE_ROOT",
                &format!("{root}/.cache/profiles/tensor_avt/{stamp}"),
            ),
            cargo_home: env_or("CARGO_HOME", &format!("{root}/.cache/cargo-home")),
            cpu_target_dir: env_or(
                "TENSOR_AVT_CPU_TARGET_DIR",
                &format!("{root}/.cache/tensor_avt_profile/cpu-target"),
            ),
            gpu_target_dir: env_or(
                "TENSOR_AVT_GPU_TARGET_DIR",
                &format!("{root}/.cache/tensor_avt_profile/gpu-target"),
            ),
            path_kind: env_or("TENSOR_AVT_PATH", "single"),
            dims,
            batch_size: env_or("TENSOR_AVT_BATCH_SIZE", "16"),
            iters: env_or("TENSOR_AVT_ITERS", "32"),
            warmup: env_or("TENSOR_AVT_WARMUP", "4"),
            seed: env_or("TENSOR_AVT_SEED", "7"),
            gpu_modes,
            with_ncu: env_or("TENSOR_AVT_WITH_NCU", "0") == "1",
            with_flamegraph: env_or("TENSOR_AVT_WITH_FLAMEGRAPH", "1") == "1",
            with_samply: env_or("TENSOR_AVT_WITH_SAMPLY", "0") == "1",
        })
    }

    /// Arguments handed to the profiled example binary.
    fn run_args(&self, backend: &str, gpu_mode: &str, dim: &str) -> Vec<String> {
        let mut args: Vec<String> = [
            "--backend",
            backend,
            "--dim",
            dim,
            "--path",
            &self.path_kind,
            "--batch-size",
            &self.batch_size,
            "--iters",
            &self.iters,
            "--warmup",
            &self.warmup,
            "--seed",
            &self.seed,
        ]
        .iter()
        .map(|arg| (*arg).to_string())
        .collect();
        if backend == "gpu" {
            args.push("--gpu-mode".to_string());
            args.push(gpu_mode.to_string());
        }
        args
    }
}

/// Where a child's output stream goes.
enum Sink<'a> {
    Inherit,
    File(&'a str),
}

fn open_sink(sink: &Sink<'_>) -> Step<Option<File>> {
    match sink {
        Sink::Inherit => Ok(None),
        Sink::File(path) => File::create(path).map(Some).map_err(|error| {
            eprintln!("cannot create {path}: {error}");
            Abort(1)
        }),
    }
}

/// Run `command` with its streams redirected as in a shell. A spawn failure
/// is reported on the redirected stderr and maps to status 127; a non-zero
/// exit returns that status.
fn run(mut command: Command, stdout: Sink<'_>, stderr: Sink<'_>) -> Result<(), u8> {
    let out = open_sink(&stdout).map_err(|abort| abort.0)?;
    let err = open_sink(&stderr).map_err(|abort| abort.0)?;
    let mut err_copy = err.as_ref().and_then(|file| file.try_clone().ok());
    if let Some(file) = out {
        command.stdout(Stdio::from(file));
    }
    if let Some(file) = err {
        command.stderr(Stdio::from(file));
    }
    let program = command.get_program().to_string_lossy().into_owned();
    match command.status() {
        Ok(status) if status.success() => Ok(()),
        Ok(status) => Err(status
            .code()
            .map_or(1, |code| u8::try_from(code).unwrap_or(1))),
        Err(error) => {
            match err_copy.as_mut() {
                Some(file) => {
                    let _ = writeln!(file, "{program}: {error}");
                }
                None => eprintln!("{program}: {error}"),
            }
            Err(127)
        }
    }
}

fn required(result: Result<(), u8>) -> Step {
    result.map_err(Abort)
}

/// Background `nvidia-smi` sampler, stopped when dropped.
struct NvidiaMonitor(Option<Child>);

impl NvidiaMonitor {
    fn start(output: &str) -> Step<Self> {
        let file = File::create(output).map_err(|error| {
            eprintln!("cannot create {output}: {error}");
            Abort(1)
        })?;
        let mut err_file = file.try_clone().map_err(|_| Abort(1))?;
        let child = Command::new("nvidia-smi")
            .args([
                "--query-gpu=name,driver_version,pstate,utilization.gpu,utilization.memory,memory.total,memory.used",
                "--format=csv",
                "-l",
                "1",
            ])
            .stdout(Stdio::from(file))
            .stderr(Stdio::from(err_file.try_clone().map_err(|_| Abort(1))?))
            .spawn();
        match child {
            Ok(child) => Ok(Self(Some(child))),
            Err(error) => {
                let _ = writeln!(err_file, "nvidia-smi: {error}");
                Ok(Self(None))
            }
        }
    }
}

impl Drop for NvidiaMonitor {
    fn drop(&mut self) {
        if let Some(mut child) = self.0.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

fn command_exists(name: &str) -> bool {
    env::var_os("PATH")
        .map(|paths| {
            env::split_paths(&paths).any(|dir| {
                let candidate = dir.join(name);
                candidate.is_file()
            })
        })
        .unwrap_or(false)
}

/// `cargo` invocation with the repo-scoped cargo home and a per-backend
/// target directory.
fn cargo_command(cfg: &Config, target_dir: &str, args: &[&str]) -> Command {
    let mut command = Command::new("cargo");
    command
        .env("CARGO_HOME", &cfg.cargo_home)
        .env("CARGO_TARGET_DIR", target_dir)
        .args(args);
    command
}

fn run_backend(
    cfg: &Config,
    backend: &str,
    gpu_mode: &str,
    target_dir: &str,
    out_dir: &str,
    dim: &str,
    cargo_features: &[&str],
) -> Step {
    let bin = format!("{target_dir}/release/examples/tensor_avt_profile");
    let result_txt = format!("{out_dir}/result.txt");
    let perf_txt = format!("{out_dir}/perf.txt");
    let perf_data = format!("{out_dir}/perf.data");
    let run_args = cfg.run_args(backend, gpu_mode, dim);

    let mut build = vec!["build", "--profile", "bench", "-p", "gororoba_algebra"];
    build.extend_from_slice(cargo_features);
    build.extend(["--example", "tensor_avt_profile"]);
    required(run(
        cargo_command(cfg, target_dir, &build),
        Sink::Inherit,
        Sink::Inherit,
    ))?;

    let _nvidia = if backend == "gpu" {
        Some(NvidiaMonitor::start(&format!("{out_dir}/nvidia-smi.csv"))?)
    } else {
        None
    };

    let mut perf_stat = Command::new("perf");
    perf_stat.args([
        "stat",
        "--all-user",
        "-e",
        "task-clock,cycles,instructions,cache-references,cache-misses,branches,branch-misses",
        &bin,
    ]);
    perf_stat.args(&run_args);
    required(run(
        perf_stat,
        Sink::File(&result_txt),
        Sink::File(&perf_txt),
    ))?;

    let mut perf_record = Command::new("perf");
    perf_record.args([
        "record",
        "--call-graph",
        "dwarf",
        "-F",
        "999",
        "-o",
        &perf_data,
        &bin,
    ]);
    perf_record.args(&run_args);
    required(run(
        perf_record,
        Sink::File(&format!("{out_dir}/perf-record.stdout")),
        Sink::File(&format!("{out_dir}/perf-record.txt")),
    ))?;

    let mut perf_report = Command::new("perf");
    perf_report.args(["report", "--stdio", "-i", &perf_data]);
    required(run(
        perf_report,
        Sink::File(&format!("{out_dir}/perf-report.txt")),
        Sink::Inherit,
    ))?;

    let mut time = Command::new("/usr/bin/time");
    time.args(["-v", &bin]);
    time.args(&run_args);
    required(run(
        time,
        Sink::File(&format!("{out_dir}/time.stdout")),
        Sink::File(&format!("{out_dir}/time.txt")),
    ))?;

    let mut heaptrack = Command::new("heaptrack");
    heaptrack.args(["--record-only", "-o", &format!("{out_dir}/heaptrack"), &bin]);
    heaptrack.args(&run_args);
    required(run(
        heaptrack,
        Sink::File(&format!("{out_dir}/heaptrack.stdout")),
        Sink::File(&format!("{out_dir}/heaptrack.stderr")),
    ))?;

    if cfg.with_flamegraph {
        let mut args = vec!["flamegraph", "--profile", "bench", "-p", "gororoba_algebra"];
        args.extend_from_slice(cargo_features);
        let svg = format!("{out_dir}/flamegraph.svg");
        args.extend(["--example", "tensor_avt_profile", "-o", &svg, "--"]);
        let mut flamegraph = cargo_command(cfg, target_dir, &args);
        flamegraph.args(&run_args);
        required(run(
            flamegraph,
            Sink::File(&format!("{out_dir}/flamegraph.stdout")),
            Sink::File(&format!("{out_dir}/flamegraph.stderr")),
        ))?;
    }

    if cfg.with_samply {
        let mut samply = Command::new("samply");
        samply.args([
            "record",
            "--save-only",
            "-o",
            &format!("{out_dir}/samply.json.gz"),
            &bin,
        ]);
        samply.args(&run_args);
        let outcome = run(
            samply,
            Sink::File(&format!("{out_dir}/samply.stdout")),
            Sink::File(&format!("{out_dir}/samply.stderr")),
        );
        if outcome.is_err() {
            let mut notes = OpenOptions::new()
                .create(true)
                .append(true)
                .open(format!("{out_dir}/notes.txt"))
                .map_err(|_| Abort(1))?;
            writeln!(notes, "samply capture skipped; see {out_dir}/samply.stderr")
                .map_err(|_| Abort(1))?;
        }
    }

    if backend == "gpu" && cfg.with_ncu && command_exists("ncu") {
        let mut ncu = Command::new("ncu");
        ncu.args([
            "--set",
            "full",
            "--target-processes",
            "all",
            "--force-overwrite",
            "--export",
            &format!("{out_dir}/ncu"),
            &bin,
        ]);
        ncu.args(&run_args);
        required(run(
            ncu,
            Sink::File(&format!("{out_dir}/ncu.stdout")),
            Sink::File(&format!("{out_dir}/ncu.stderr")),
        ))?;
    }
    Ok(())
}

/// First line of `file` containing `pattern`, with leading whitespace and
/// the `pattern` prefix removed; empty when the file or the line is absent.
fn metric_or_na(pattern: &str, file: &str) -> String {
    let Ok(bytes) = fs::read(file) else {
        return String::new();
    };
    let text = String::from_utf8_lossy(&bytes);
    text.lines()
        .find(|line| line.contains(pattern))
        .map(|line| {
            let trimmed = line.trim_start();
            trimmed.strip_prefix(pattern).unwrap_or(trimmed).to_string()
        })
        .unwrap_or_default()
}

/// Lexicographically first `heaptrack*.gz`, `heaptrack*.zst` or
/// `heaptrack*.gz.zst` file directly inside `dir`; empty when none exists.
fn heaptrack_artifact(dir: &str) -> String {
    let mut found: Vec<String> = fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .filter(|entry| entry.path().is_file())
        .filter_map(|entry| entry.file_name().into_string().ok())
        .filter(|name| {
            name.starts_with("heaptrack") && (name.ends_with(".gz") || name.ends_with(".zst"))
        })
        .map(|name| format!("{dir}/{name}"))
        .collect();
    found.sort();
    found.into_iter().next().unwrap_or_default()
}

fn has_ncu_output(dir: &str) -> bool {
    fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .any(|entry| entry.file_name().to_string_lossy().starts_with("ncu"))
}

fn write_summary(cfg: &Config) -> Step<String> {
    let mut md = String::new();
    let mut line = |text: String| {
        md.push_str(&text);
        md.push('\n');
    };
    line("# TensorAVT Profile Summary".to_string());
    line(String::new());
    line(format!("- path: {}", cfg.path_kind));
    line(format!("- dims: {}", cfg.dims.join(" ")));
    line(format!("- batch_size: {}", cfg.batch_size));
    line(format!("- iters: {}", cfg.iters));
    line(format!("- warmup: {}", cfg.warmup));
    line(format!("- seed: {}", cfg.seed));
    line(format!("- gpu_modes: {}", cfg.gpu_modes.join(" ")));
    line(String::new());
    let backend_dirs: Vec<String> = std::iter::once("cpu".to_string())
        .chain(cfg.gpu_modes.iter().map(|mode| format!("gpu-{mode}")))
        .collect();
    for dim in &cfg.dims {
        line(format!("## dim {dim}"));
        line(String::new());
        for backend_dir in &backend_dirs {
            let dir = format!("{}/dim{dim}/{backend_dir}", cfg.out_root);
            let result_txt = format!("{dir}/result.txt");
            let perf_txt = format!("{dir}/perf.txt");
            let time_txt = format!("{dir}/time.txt");
            line(format!("### {backend_dir}"));
            line(String::new());
            line(format!(
                "- backend: {}",
                metric_or_na("backend=", &result_txt)
            ));
            line(format!(
                "- gpu_mode: {}",
                metric_or_na("gpu_mode=", &result_txt)
            ));
            line(format!(
                "- seconds: {}",
                metric_or_na("seconds=", &result_txt)
            ));
            line(format!(
                "- ns_per_iter: {}",
                metric_or_na("ns_per_iter=", &result_txt)
            ));
            line(format!(
                "- checksum: {}",
                metric_or_na("checksum=", &result_txt)
            ));
            line(format!(
                "- max_rss_kb: {}",
                metric_or_na("Maximum resident set size (kbytes):", &time_txt)
            ));
            for (label, pattern) in [
                ("task_clock", "task-clock"),
                ("cycles", "cycles"),
                ("instructions", "instructions"),
                ("cache_references", "cache-references"),
                ("cache_misses", "cache-misses"),
                ("branches", "branches"),
                ("branch_misses", "branch-misses"),
            ] {
                line(format!("- {label}: {}", metric_or_na(pattern, &perf_txt)));
            }
            line(format!("- perf: {perf_txt}"));
            line(format!("- perf_record: {dir}/perf-record.txt"));
            line(format!("- perf_report: {dir}/perf-report.txt"));
            line(format!("- time: {time_txt}"));
            line(format!("- heaptrack: {}", heaptrack_artifact(&dir)));
            for (label, file) in [
                ("flamegraph", "flamegraph.svg"),
                ("samply", "samply.json.gz"),
                ("nvidia_smi", "nvidia-smi.csv"),
            ] {
                if Path::new(&format!("{dir}/{file}")).is_file() {
                    line(format!("- {label}: {dir}/{file}"));
                }
            }
            if has_ncu_output(&dir) {
                line(format!("- ncu: {dir}/ncu"));
            }
            if Path::new(&format!("{dir}/notes.txt")).is_file() {
                line(format!("- notes: {dir}/notes.txt"));
            }
            line(String::new());
        }
    }
    let summary = format!("{}/summary.md", cfg.out_root);
    let mut file = File::create(&summary).map_err(|error| {
        eprintln!("cannot create {summary}: {error}");
        Abort(1)
    })?;
    file.write_all(md.as_bytes()).map_err(|_| Abort(1))?;
    Ok(summary)
}

fn orchestrate() -> Step {
    let root: PathBuf = repo_root::resolve!();
    let cfg = Config::from_env(&root)?;
    for dir in [&cfg.out_root, &cfg.cpu_target_dir, &cfg.gpu_target_dir] {
        fs::create_dir_all(dir).map_err(|error| {
            eprintln!("cannot create {dir}: {error}");
            Abort(1)
        })?;
    }
    for dim in &cfg.dims {
        let dim_root = format!("{}/dim{dim}", cfg.out_root);
        let mkdir = |path: &str| {
            fs::create_dir_all(path).map_err(|error| {
                eprintln!("cannot create {path}: {error}");
                Abort(1)
            })
        };
        let cpu_dir = format!("{dim_root}/cpu");
        mkdir(&cpu_dir)?;
        run_backend(&cfg, "cpu", "host", &cfg.cpu_target_dir, &cpu_dir, dim, &[])?;
        for gpu_mode in &cfg.gpu_modes {
            let gpu_dir = format!("{dim_root}/gpu-{gpu_mode}");
            mkdir(&gpu_dir)?;
            run_backend(
                &cfg,
                "gpu",
                gpu_mode,
                &cfg.gpu_target_dir,
                &gpu_dir,
                dim,
                &["--features", "gpu"],
            )?;
        }
    }
    let summary = write_summary(&cfg)?;
    println!("OK: tensor_avt profiles written to {}", cfg.out_root);
    println!("Summary: {summary}");
    Ok(())
}

fn main() -> ExitCode {
    // Arguments are ignored; the environment carries the configuration.
    let _ignored: Vec<OsString> = env::args_os().skip(1).collect();
    match orchestrate() {
        Ok(()) => ExitCode::SUCCESS,
        Err(Abort(code)) => ExitCode::from(code),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_list_accepts_commas_and_blanks() {
        assert_eq!(split_list("64,128 256"), ["64", "128", "256"]);
        assert!(split_list(" , ").is_empty());
    }

    #[test]
    fn metric_strips_leading_blanks_and_prefix() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("result.txt");
        fs::write(&file, "noise\n  seconds=1.5\nseconds=9\n").unwrap();
        let path = file.to_str().unwrap();
        assert_eq!(metric_or_na("seconds=", path), "1.5");
        assert_eq!(metric_or_na("checksum=", path), "");
        assert_eq!(metric_or_na("seconds=", "/nonexistent/file"), "");
    }

    #[test]
    fn heaptrack_artifact_picks_first_sorted_match() {
        let dir = tempfile::tempdir().unwrap();
        for name in [
            "heaptrack.b.gz",
            "heaptrack.a.zst",
            "heaptrack.txt",
            "other.gz",
        ] {
            fs::write(dir.path().join(name), "").unwrap();
        }
        let base = dir.path().to_str().unwrap();
        assert_eq!(heaptrack_artifact(base), format!("{base}/heaptrack.a.zst"));
    }
}
