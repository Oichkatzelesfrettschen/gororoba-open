// SPDX-License-Identifier: MIT
//! What predicts the cells of a D3Q19 BGK run that fails late: a test of the
//! temporal associator norm of claim C-1617 against product-free scores.
//!
//! The flow is a quasi-two-dimensional periodic double shear layer (64 x 64 x
//! 4 cells) with a transverse sine perturbation. Two subcommands:
//!
//! 1. `scan` steps a grid of (tau, U0, delta) configurations until the first
//!    population is negative or the step budget ends, and records the first
//!    violating step and the number of cells holding a negative population.
//!    When no configuration violates inside the kept window, one wider grid
//!    (lower tau, larger U0) runs and the output records it.
//! 2. `score` re-runs at most eight kept configurations, labels each cell
//!    positive when it holds a negative population at the first violating
//!    step F, and ranks the cells at horizons h before F with six scores that
//!    read only states up to step F - h: the associator norm of the cell's
//!    unit 32-vectors at steps F-h-2, F-h-1, F-h (identity slot map), the Gram
//!    volume of the same three unit vectors, the step-difference norm, the
//!    local Mach number, and the smallest population over the density.
//!
//! The Gram volume is the three-dimensional volume spanned by the triple. It
//! is zero for collinear states and one for orthonormal states, and it
//! separates a product-free third-order quantity from the associator.
//!
//! Output: one JSON file, written by `scan` and extended by `score`, and a
//! summary on stderr.

use std::collections::VecDeque;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use cd_kernel::batch_sliding_associator_norms_parallel;
use clap::{Args, Parser, Subcommand};
use lbm_3d::{
    lattice::D3Q19Lattice,
    solver::{LbmSolver3D, aosoa_idx},
};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

/// Lattice extent along x.
const NX: usize = 64;
/// Lattice extent along y (the shear direction).
const NY: usize = 64;
/// Lattice extent along z (periodic, the quasi-two-dimensional direction).
const NZ: usize = 4;
/// Cells of the lattice.
const CELLS: usize = NX * NY * NZ;
/// Populations per cell (D3Q19).
const Q: usize = 19;
/// Embedding dimension: the 19 populations occupy slots 0..19 of 32 (a pathion).
const DIM: usize = 32;
/// Populations below this norm stay unnormalized.
const NORM_FLOOR: f64 = 1e-15;
/// Horizons h, in steps, before the first violating step.
const HORIZONS: [usize; 3] = [1, 10, 50];
/// A horizon is skipped when F - h falls below this many steps.
const MIN_LEAD: usize = 3;
/// States the scoring run keeps: steps F - 52 through F.
const RING: usize = 50 + 2 + 1;
/// Tolerance of prediction P13a on the associator's ROC area.
const AUC_MARGIN: f64 = 0.02;
/// Spearman bound below which prediction P13b holds.
const SPEARMAN_HOLDS: f64 = 0.9;
/// Spearman bound at or above which prediction P13b is falsified.
const SPEARMAN_FALSIFIES: f64 = 0.95;

#[derive(Parser)]
#[command(name = "lbm-late-failure-precursor")]
#[command(
    about = "Scores of the cells that hold a negative population at the first violating step"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Find each configuration's first violating step.
    Scan(ScanArgs),
    /// Rank the cells of the kept configurations before their first violation.
    Score(ScoreArgs),
}

#[derive(Args)]
struct ScanArgs {
    /// Relaxation times of the grid.
    #[arg(long, value_delimiter = ',', default_value = "0.502,0.505,0.51,0.52")]
    taus: Vec<f64>,

    /// Shear amplitudes U0 of the grid.
    #[arg(long, value_delimiter = ',', default_value = "0.05,0.08,0.12,0.16")]
    u0s: Vec<f64>,

    /// Shear-layer widths delta of the grid, in cells.
    #[arg(long, value_delimiter = ',', default_value = "1,2,4")]
    deltas: Vec<f64>,

    /// Relaxation times of the wider grid that runs when none is kept.
    #[arg(long, value_delimiter = ',', default_value = "0.5005,0.501,0.502")]
    wide_taus: Vec<f64>,

    /// Shear amplitudes of the wider grid.
    #[arg(long, value_delimiter = ',', default_value = "0.16,0.2,0.25,0.3")]
    wide_u0s: Vec<f64>,

    /// Skip the wider grid.
    #[arg(long)]
    no_widen: bool,

    /// Transverse perturbation amplitude, in units of U0.
    #[arg(long, default_value_t = 0.05)]
    eps: f64,

    /// Step budget of the search.
    #[arg(long, default_value_t = 6000)]
    max_steps: usize,

    /// Earliest first violating step that a configuration keeps.
    #[arg(long, default_value_t = 200)]
    min_kept_step: usize,

    /// Output JSON path.
    #[arg(
        long,
        default_value = "data/output/lbm/ablations/lbm_late_failure_precursor.json"
    )]
    out_json: PathBuf,
}

#[derive(Args)]
struct ScoreArgs {
    /// JSON written by `scan`; it is rewritten with the scores.
    #[arg(
        long,
        default_value = "data/output/lbm/ablations/lbm_late_failure_precursor.json"
    )]
    json: PathBuf,

    /// Copy of the finished JSON for the retained record.
    #[arg(
        long,
        default_value = "data/output/audit/claim-family-evidence-adjudication/lbm-late-failure-precursor.json"
    )]
    retained_json: PathBuf,

    /// Most configurations scored.
    #[arg(long, default_value_t = 8)]
    max_configs: usize,
}

/// One point of the parameter grid.
#[derive(Clone, Copy)]
struct Config {
    tau: f64,
    u0: f64,
    delta: f64,
}

#[derive(Debug, Serialize, Deserialize)]
struct ScanRow {
    /// `base` or `widened`.
    grid: String,
    tau: f64,
    u0: f64,
    delta: f64,
    #[serde(default)]
    first_violation_step: Option<usize>,
    #[serde(default)]
    violating_cells: Option<usize>,
    #[serde(default)]
    min_population: Option<f64>,
    kept: bool,
}

#[derive(Debug, Serialize, Deserialize)]
struct HorizonScore {
    horizon: usize,
    positive_cells: usize,
    auc_associator: Option<f64>,
    auc_gram_volume: Option<f64>,
    auc_step_difference: Option<f64>,
    auc_mach: Option<f64>,
    auc_min_population_share: Option<f64>,
    spearman_associator_gram_volume: Option<f64>,
    spearman_associator_step_difference: Option<f64>,
    /// Best ROC area among Mach, smallest population share and step difference.
    best_product_free_auc: Option<f64>,
    /// Associator area minus the best product-free area.
    associator_excess: Option<f64>,
    /// The same excess after each score takes the orientation (area or its
    /// complement) that ranks the positives better.
    associator_excess_oriented: Option<f64>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ConfigScore {
    tau: f64,
    u0: f64,
    delta: f64,
    first_violation_step: usize,
    violating_cells: usize,
    skipped_horizons: Vec<usize>,
    horizons: Vec<HorizonScore>,
}

#[derive(Debug, Serialize, Deserialize)]
struct HorizonSummary {
    horizon: usize,
    configs: usize,
    exceed_margin: usize,
    exceed_margin_oriented: usize,
    median_associator_auc: Option<f64>,
    median_best_product_free_auc: Option<f64>,
}

#[derive(Debug, Serialize, Deserialize)]
struct Predictions {
    p13a_by_horizon: Vec<HorizonSummary>,
    /// Pairs (configuration, horizon) scored, and how many of them hold the
    /// associator above the best product-free score by more than the margin.
    p13a_pairs: usize,
    p13a_pairs_exceeding: usize,
    p13a_pairs_h_ge_10: usize,
    p13a_pairs_h_ge_10_exceeding: usize,
    p13b_pairs: usize,
    p13b_spearman_min: Option<f64>,
    p13b_spearman_median: Option<f64>,
    p13b_spearman_max: Option<f64>,
    p13b_pairs_below_0_9: usize,
    p13b_pairs_at_or_above_0_95: usize,
}

#[derive(Debug, Serialize, Deserialize)]
struct Output {
    nx: usize,
    ny: usize,
    nz: usize,
    eps: f64,
    max_steps: usize,
    min_kept_step: usize,
    widened: bool,
    scan: Vec<ScanRow>,
    #[serde(default)]
    scores: Vec<ConfigScore>,
    #[serde(default)]
    predictions: Option<Predictions>,
}

/// u_x of the double shear layer at row `y`.
fn shear_ux(cfg: Config, y: usize) -> f64 {
    let y = y as f64;
    let ny = NY as f64;
    if y < ny / 2.0 {
        cfg.u0 * ((y - ny / 4.0) / cfg.delta).tanh()
    } else {
        cfg.u0 * ((3.0 * ny / 4.0 - y) / cfg.delta).tanh()
    }
}

/// Density and velocity of the shear layer in the solver's cell order
/// (z * NX * NY + y * NX + x).
fn shear_fields(cfg: Config, eps: f64) -> (Vec<f64>, Vec<[f64; 3]>) {
    let mut u = Vec::with_capacity(CELLS);
    for _z in 0..NZ {
        for y in 0..NY {
            for x in 0..NX {
                let uy = eps * cfg.u0 * (2.0 * std::f64::consts::PI * x as f64 / NX as f64).sin();
                u.push([shear_ux(cfg, y), uy, 0.0]);
            }
        }
    }
    (vec![1.0; CELLS], u)
}

fn fresh_solver(cfg: Config, eps: f64) -> LbmSolver3D {
    let mut solver = LbmSolver3D::new(NX, NY, NZ, cfg.tau);
    let (rho, u) = shear_fields(cfg, eps);
    solver.rho.copy_from_slice(&rho);
    solver.u.copy_from_slice(&u);
    solver.reinitialize_from_macroscopic();
    solver
}

/// A population that is negative or not finite.
fn is_bad(f: f64) -> bool {
    f < 0.0 || !f.is_finite()
}

/// Cells holding a bad population, and the smallest population, of the solver.
fn violation_in(solver: &LbmSolver3D) -> Option<(usize, f64)> {
    let mut cells = 0;
    let mut smallest = f64::INFINITY;
    for cell in 0..CELLS {
        let mut bad = false;
        for dir in 0..Q {
            let f = solver.f[aosoa_idx(cell, dir)];
            smallest = smallest.min(f);
            bad |= is_bad(f);
        }
        cells += usize::from(bad);
    }
    (cells > 0).then_some((cells, smallest))
}

struct Violation {
    step: usize,
    cells: usize,
    min_population: f64,
}

/// Step the solver (collision, then streaming) until a population is bad or
/// `max_steps` steps pass.
fn scan_config(cfg: Config, eps: f64, max_steps: usize) -> Option<Violation> {
    let mut solver = fresh_solver(cfg, eps);
    if let Some((cells, min_population)) = violation_in(&solver) {
        return Some(Violation {
            step: 0,
            cells,
            min_population,
        });
    }
    for step in 1..=max_steps {
        let _ = solver.phase1_collision();
        let _ = solver.phase2_streaming();
        if let Some((cells, min_population)) = violation_in(&solver) {
            return Some(Violation {
                step,
                cells,
                min_population,
            });
        }
    }
    None
}

fn scan_grid(
    name: &str,
    taus: &[f64],
    u0s: &[f64],
    deltas: &[f64],
    args: &ScanArgs,
) -> Vec<ScanRow> {
    let mut configs = Vec::new();
    for &tau in taus {
        for &u0 in u0s {
            for &delta in deltas {
                configs.push(Config { tau, u0, delta });
            }
        }
    }
    configs
        .par_iter()
        .map(|&cfg| {
            let found = scan_config(cfg, args.eps, args.max_steps);
            let kept = found.as_ref().is_some_and(|v| v.step >= args.min_kept_step);
            ScanRow {
                grid: name.to_string(),
                tau: cfg.tau,
                u0: cfg.u0,
                delta: cfg.delta,
                first_violation_step: found.as_ref().map(|v| v.step),
                violating_cells: found.as_ref().map(|v| v.cells),
                min_population: found.as_ref().map(|v| v.min_population),
                kept,
            }
        })
        .collect()
}

fn write_json(path: &Path, output: &Output) -> Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent).with_context(|| format!("create {}", parent.display()))?;
    }
    std::fs::write(path, serde_json::to_string_pretty(output)?)
        .with_context(|| format!("write {}", path.display()))
}

fn report_scan(rows: &[ScanRow]) {
    for r in rows {
        eprintln!(
            "{} tau {} U0 {} delta {}: {}{}",
            r.grid,
            r.tau,
            r.u0,
            r.delta,
            r.first_violation_step
                .map_or("no violation".to_string(), |s| format!(
                    "first violation step {s}, {} cells, min population {:.3e}",
                    r.violating_cells.unwrap_or(0),
                    r.min_population.unwrap_or(f64::NAN)
                )),
            if r.kept { " (kept)" } else { "" }
        );
    }
}

fn scan(args: &ScanArgs) -> Result<()> {
    let mut rows = scan_grid("base", &args.taus, &args.u0s, &args.deltas, args);
    let mut widened = false;
    if !rows.iter().any(|r| r.kept) && !args.no_widen {
        eprintln!("no base configuration is kept; running the wider grid");
        widened = true;
        rows.extend(scan_grid(
            "widened",
            &args.wide_taus,
            &args.wide_u0s,
            &args.deltas,
            args,
        ));
    }
    report_scan(&rows);
    eprintln!(
        "kept {} of {} configurations (widened grid: {widened})",
        rows.iter().filter(|r| r.kept).count(),
        rows.len()
    );
    let output = Output {
        nx: NX,
        ny: NY,
        nz: NZ,
        eps: args.eps,
        max_steps: args.max_steps,
        min_kept_step: args.min_kept_step,
        widened,
        scan: rows,
        scores: Vec::new(),
        predictions: None,
    };
    write_json(&args.out_json, &output)?;
    eprintln!("wrote {}", args.out_json.display());
    Ok(())
}

/// The populations of every cell, cell-major (`cell * 19 + direction`), into
/// `state`.
fn snapshot_into(solver: &LbmSolver3D, state: &mut Vec<f64>) {
    state.clear();
    for cell in 0..CELLS {
        for dir in 0..Q {
            state.push(solver.f[aosoa_idx(cell, dir)]);
        }
    }
}

/// The last `RING` states of a run, as (step, state) pairs, ending at the
/// first violating step.
struct Trace {
    first_violation: usize,
    ring: VecDeque<(usize, Vec<f64>)>,
}

impl Trace {
    fn state_at(&self, step: usize) -> &[f64] {
        let first = self.ring.front().map_or(0, |(s, _)| *s);
        &self.ring[step - first].1
    }
}

/// Step until the first bad population, keeping the last `RING` states.
fn trace_to_violation(cfg: Config, eps: f64, max_steps: usize) -> Result<Trace> {
    let mut solver = fresh_solver(cfg, eps);
    let mut ring: VecDeque<(usize, Vec<f64>)> = VecDeque::with_capacity(RING + 1);
    for step in 0..=max_steps {
        if step > 0 {
            let _ = solver.phase1_collision();
            let _ = solver.phase2_streaming();
        }
        let mut buffer = if ring.len() == RING {
            ring.pop_front().map(|(_, b)| b).unwrap_or_default()
        } else {
            Vec::with_capacity(CELLS * Q)
        };
        snapshot_into(&solver, &mut buffer);
        let bad = buffer.iter().any(|&f| is_bad(f));
        ring.push_back((step, buffer));
        if bad {
            return Ok(Trace {
                first_violation: step,
                ring,
            });
        }
    }
    bail!(
        "tau {} U0 {} delta {}: no violation in {max_steps} steps",
        cfg.tau,
        cfg.u0,
        cfg.delta
    )
}

/// The 19 populations of one cell in slots 0..19 of a 32-vector, divided by
/// its Euclidean norm.
fn unit_vector(state: &[f64], cell: usize) -> Vec<f64> {
    let mut v = vec![0.0; DIM];
    v[..Q].copy_from_slice(&state[cell * Q..(cell + 1) * Q]);
    let norm = norm(&v);
    if norm > NORM_FLOOR {
        v.iter_mut().for_each(|x| *x /= norm);
    }
    v
}

fn dot(a: &[f64], b: &[f64]) -> f64 {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

fn norm(a: &[f64]) -> f64 {
    dot(a, a).sqrt()
}

fn distance(a: &[f64], b: &[f64]) -> f64 {
    a.iter()
        .zip(b)
        .map(|(x, y)| (x - y) * (x - y))
        .sum::<f64>()
        .sqrt()
}

/// `v` minus its components along the orthonormal `basis`, in two
/// Gram-Schmidt passes (the second removes the residue of the first).
fn orthogonalize(v: &[f64], basis: &[&[f64]]) -> Vec<f64> {
    let mut out = v.to_vec();
    for _pass in 0..2 {
        for b in basis {
            let c = dot(&out, b);
            for (o, x) in out.iter_mut().zip(*b) {
                *o -= c * x;
            }
        }
    }
    out
}

/// Square root of the Gram determinant of three vectors: |v0| times the part
/// of v1 orthogonal to v0, times the part of v2 orthogonal to both. It is zero
/// when the three vectors are linearly dependent.
fn gram_volume(v0: &[f64], v1: &[f64], v2: &[f64]) -> f64 {
    let n0 = norm(v0);
    if n0 <= 0.0 {
        return 0.0;
    }
    let e0: Vec<f64> = v0.iter().map(|x| x / n0).collect();
    let p1 = orthogonalize(v1, &[&e0]);
    let n1 = norm(&p1);
    if n1 <= 0.0 {
        return 0.0;
    }
    let e1: Vec<f64> = p1.iter().map(|x| x / n1).collect();
    let p2 = orthogonalize(v2, &[&e0, &e1]);
    n0 * n1 * norm(&p2)
}

/// Ranks 1..n with ties sharing their mean rank.
fn mean_ranks(x: &[f64]) -> Vec<f64> {
    let mut order: Vec<usize> = (0..x.len()).collect();
    order.sort_by(|&a, &b| x[a].total_cmp(&x[b]));
    let mut out = vec![0.0; x.len()];
    let mut i = 0;
    while i < order.len() {
        let mut j = i;
        while j + 1 < order.len() && x[order[j + 1]] == x[order[i]] {
            j += 1;
        }
        let shared = 0.5 * (i + j) as f64 + 1.0;
        for &k in &order[i..=j] {
            out[k] = shared;
        }
        i = j + 1;
    }
    out
}

/// Area under the ROC curve of `score` for the positive `label`, by the
/// rank-sum formula. Tied scores share their mean rank, so a tie between a
/// positive and a negative cell counts one half and the area does not depend
/// on cell order; the lattice symmetry gives many cells equal scores.
fn auc(score: &[f64], label: &[bool]) -> f64 {
    let ranks = mean_ranks(score);
    let positives = label.iter().filter(|&&l| l).count() as f64;
    let negatives = label.len() as f64 - positives;
    if positives == 0.0 || negatives == 0.0 {
        return f64::NAN;
    }
    let rank_sum: f64 = ranks
        .iter()
        .zip(label)
        .filter(|(_, l)| **l)
        .map(|(r, _)| r)
        .sum();
    (rank_sum - positives * (positives + 1.0) / 2.0) / (positives * negatives)
}

fn mean(values: &[f64]) -> f64 {
    if values.is_empty() {
        return f64::NAN;
    }
    values.iter().sum::<f64>() / values.len() as f64
}

fn pearson(x: &[f64], y: &[f64]) -> f64 {
    let (mx, my) = (mean(x), mean(y));
    let (mut sxy, mut sxx, mut syy) = (0.0, 0.0, 0.0);
    for (a, b) in x.iter().zip(y) {
        sxy += (a - mx) * (b - my);
        sxx += (a - mx).powi(2);
        syy += (b - my).powi(2);
    }
    sxy / (sxx * syy).sqrt()
}

fn spearman(x: &[f64], y: &[f64]) -> f64 {
    pearson(&mean_ranks(x), &mean_ranks(y))
}

/// Median of the finite entries; `None` when there are none.
fn median(values: &[f64]) -> Option<f64> {
    let mut finite: Vec<f64> = values.iter().copied().filter(|v| v.is_finite()).collect();
    if finite.is_empty() {
        return None;
    }
    finite.sort_by(f64::total_cmp);
    let n = finite.len();
    Some(if n % 2 == 1 {
        finite[n / 2]
    } else {
        0.5 * (finite[n / 2 - 1] + finite[n / 2])
    })
}

fn finite(x: f64) -> Option<f64> {
    x.is_finite().then_some(x)
}

/// The five per-cell scores, each indexed by cell.
struct CellScores {
    associator: Vec<f64>,
    gram_volume: Vec<f64>,
    step_difference: Vec<f64>,
    mach: Vec<f64>,
    min_population_share: Vec<f64>,
}

/// Scores of every cell from three consecutive states `s0`, `s1`, `s2`
/// (steps F-h-2, F-h-1, F-h); the Mach number and population share read `s2`.
fn cell_scores(lattice: &D3Q19Lattice, s0: &[f64], s1: &[f64], s2: &[f64]) -> CellScores {
    let rows: Vec<[f64; 5]> = (0..CELLS)
        .into_par_iter()
        .map(|cell| {
            let triple = [
                unit_vector(s0, cell),
                unit_vector(s1, cell),
                unit_vector(s2, cell),
            ];
            let associator = batch_sliding_associator_norms_parallel(&triple, DIM)[0];
            let volume = gram_volume(&triple[0], &triple[1], &triple[2]);
            let step_difference = distance(&triple[2], &triple[1]);

            let pops = &s2[cell * Q..(cell + 1) * Q];
            let rho: f64 = pops.iter().sum();
            let mut momentum = [0.0_f64; 3];
            for (dir, &f) in pops.iter().enumerate() {
                let c = lattice.velocities[dir];
                for (m, &cd) in momentum.iter_mut().zip(&c) {
                    *m += f64::from(cd) * f;
                }
            }
            let speed = norm(&momentum) / rho;
            let smallest = pops.iter().copied().fold(f64::INFINITY, f64::min);
            [
                associator,
                volume,
                step_difference,
                speed * 3.0_f64.sqrt(),
                -smallest / rho,
            ]
        })
        .collect();
    let column = |k: usize| rows.iter().map(|r| r[k]).collect::<Vec<f64>>();
    CellScores {
        associator: column(0),
        gram_volume: column(1),
        step_difference: column(2),
        mach: column(3),
        min_population_share: column(4),
    }
}

/// The orientation of a ROC area that ranks the positives better.
fn oriented(a: f64) -> f64 {
    a.max(1.0 - a)
}

fn horizon_score(
    lattice: &D3Q19Lattice,
    trace: &Trace,
    labels: &[bool],
    horizon: usize,
) -> HorizonScore {
    let end = trace.first_violation - horizon;
    let s = cell_scores(
        lattice,
        trace.state_at(end - 2),
        trace.state_at(end - 1),
        trace.state_at(end),
    );
    let a_assoc = auc(&s.associator, labels);
    let a_gram = auc(&s.gram_volume, labels);
    let a_step = auc(&s.step_difference, labels);
    let a_mach = auc(&s.mach, labels);
    let a_pop = auc(&s.min_population_share, labels);
    let best = a_step.max(a_mach).max(a_pop);
    let best_oriented = oriented(a_step).max(oriented(a_mach)).max(oriented(a_pop));
    HorizonScore {
        horizon,
        positive_cells: labels.iter().filter(|&&l| l).count(),
        auc_associator: finite(a_assoc),
        auc_gram_volume: finite(a_gram),
        auc_step_difference: finite(a_step),
        auc_mach: finite(a_mach),
        auc_min_population_share: finite(a_pop),
        spearman_associator_gram_volume: finite(spearman(&s.associator, &s.gram_volume)),
        spearman_associator_step_difference: finite(spearman(&s.associator, &s.step_difference)),
        best_product_free_auc: finite(best),
        associator_excess: finite(a_assoc - best),
        associator_excess_oriented: finite(oriented(a_assoc) - best_oriented),
    }
}

fn score_config(row: &ScanRow, out: &Output, lattice: &D3Q19Lattice) -> Result<ConfigScore> {
    let Some(expected) = row.first_violation_step else {
        bail!("configuration without a violation cannot be scored");
    };
    let cfg = Config {
        tau: row.tau,
        u0: row.u0,
        delta: row.delta,
    };
    let trace = trace_to_violation(cfg, out.eps, out.max_steps)?;
    if trace.first_violation != expected {
        bail!(
            "tau {} U0 {} delta {}: the scan found step {expected}, the re-run {}",
            row.tau,
            row.u0,
            row.delta,
            trace.first_violation
        );
    }
    let labels: Vec<bool> = trace
        .state_at(expected)
        .chunks_exact(Q)
        .map(|pops| pops.iter().any(|&f| is_bad(f)))
        .collect();
    let mut horizons = Vec::new();
    let mut skipped = Vec::new();
    for h in HORIZONS {
        if expected < h + MIN_LEAD {
            skipped.push(h);
            continue;
        }
        horizons.push(horizon_score(lattice, &trace, &labels, h));
    }
    Ok(ConfigScore {
        tau: row.tau,
        u0: row.u0,
        delta: row.delta,
        first_violation_step: expected,
        violating_cells: labels.iter().filter(|&&l| l).count(),
        skipped_horizons: skipped,
        horizons,
    })
}

/// At most `max` kept rows, spread over the sorted first violating steps.
fn select_kept(rows: &[ScanRow], max: usize) -> Vec<&ScanRow> {
    let mut kept: Vec<&ScanRow> = rows.iter().filter(|r| r.kept).collect();
    kept.sort_by_key(|r| r.first_violation_step);
    if kept.len() <= max || max == 0 {
        return kept;
    }
    (0..max)
        .map(|i| kept[i * (kept.len() - 1) / (max - 1).max(1)])
        .collect()
}

/// An excess above the prediction margin.
fn exceeds(excess: Option<f64>) -> bool {
    excess.is_some_and(|e| e > AUC_MARGIN)
}

fn predictions(scores: &[ConfigScore]) -> Predictions {
    let mut by_horizon = Vec::new();
    let mut pairs = 0;
    let mut exceeding = 0;
    let mut pairs_late = 0;
    let mut exceeding_late = 0;
    let mut spearmans = Vec::new();
    for h in HORIZONS {
        let at: Vec<&HorizonScore> = scores
            .iter()
            .flat_map(|c| c.horizons.iter())
            .filter(|s| s.horizon == h)
            .collect();
        pairs += at.len();
        exceeding += at.iter().filter(|s| exceeds(s.associator_excess)).count();
        if h >= 10 {
            pairs_late += at.len();
            exceeding_late += at.iter().filter(|s| exceeds(s.associator_excess)).count();
        }
        spearmans.extend(at.iter().filter_map(|s| s.spearman_associator_gram_volume));
        let assoc: Vec<f64> = at.iter().filter_map(|s| s.auc_associator).collect();
        let best: Vec<f64> = at.iter().filter_map(|s| s.best_product_free_auc).collect();
        by_horizon.push(HorizonSummary {
            horizon: h,
            configs: at.len(),
            exceed_margin: at.iter().filter(|s| exceeds(s.associator_excess)).count(),
            exceed_margin_oriented: at
                .iter()
                .filter(|s| exceeds(s.associator_excess_oriented))
                .count(),
            median_associator_auc: median(&assoc),
            median_best_product_free_auc: median(&best),
        });
    }
    let extreme =
        |pick: fn(f64, f64) -> f64, start: f64| spearmans.iter().copied().fold(start, pick);
    Predictions {
        p13a_by_horizon: by_horizon,
        p13a_pairs: pairs,
        p13a_pairs_exceeding: exceeding,
        p13a_pairs_h_ge_10: pairs_late,
        p13a_pairs_h_ge_10_exceeding: exceeding_late,
        p13b_pairs: spearmans.len(),
        p13b_spearman_min: (!spearmans.is_empty()).then(|| extreme(f64::min, f64::INFINITY)),
        p13b_spearman_median: median(&spearmans),
        p13b_spearman_max: (!spearmans.is_empty()).then(|| extreme(f64::max, f64::NEG_INFINITY)),
        p13b_pairs_below_0_9: spearmans.iter().filter(|&&r| r < SPEARMAN_HOLDS).count(),
        p13b_pairs_at_or_above_0_95: spearmans
            .iter()
            .filter(|&&r| r >= SPEARMAN_FALSIFIES)
            .count(),
    }
}

fn fmt(x: Option<f64>) -> String {
    x.map_or("n/a".to_string(), |v| format!("{v:.4}"))
}

fn report_score(c: &ConfigScore) {
    eprintln!(
        "tau {} U0 {} delta {}: F {} ({} cells), skipped horizons {:?}",
        c.tau, c.u0, c.delta, c.first_violation_step, c.violating_cells, c.skipped_horizons
    );
    for h in &c.horizons {
        eprintln!(
            "  h {:>2}: AUC assoc {} gram {} step diff {} Mach {} min pop {}; Spearman assoc-gram {} assoc-step {}",
            h.horizon,
            fmt(h.auc_associator),
            fmt(h.auc_gram_volume),
            fmt(h.auc_step_difference),
            fmt(h.auc_mach),
            fmt(h.auc_min_population_share),
            fmt(h.spearman_associator_gram_volume),
            fmt(h.spearman_associator_step_difference)
        );
    }
}

fn score(args: &ScoreArgs) -> Result<()> {
    let text = std::fs::read_to_string(&args.json)
        .with_context(|| format!("read {}", args.json.display()))?;
    let mut out: Output =
        serde_json::from_str(&text).with_context(|| format!("parse {}", args.json.display()))?;
    if (out.nx, out.ny, out.nz) != (NX, NY, NZ) {
        bail!(
            "scan grid {}x{}x{} differs from this binary",
            out.nx,
            out.ny,
            out.nz
        );
    }
    let lattice = D3Q19Lattice::new();
    let picked = select_kept(&out.scan, args.max_configs);
    if picked.is_empty() {
        bail!("scan holds no kept configuration");
    }
    let mut scores = Vec::new();
    for row in picked {
        let result = score_config(row, &out, &lattice)?;
        report_score(&result);
        scores.push(result);
    }
    let summary = predictions(&scores);
    eprintln!(
        "P13a: associator above the best product-free score by more than {AUC_MARGIN} in {} of {} pairs ({} of {} at h >= 10)",
        summary.p13a_pairs_exceeding,
        summary.p13a_pairs,
        summary.p13a_pairs_h_ge_10_exceeding,
        summary.p13a_pairs_h_ge_10
    );
    eprintln!(
        "P13b: Spearman associator-Gram volume min {} median {} max {} over {} pairs; {} below 0.9, {} at or above 0.95",
        fmt(summary.p13b_spearman_min),
        fmt(summary.p13b_spearman_median),
        fmt(summary.p13b_spearman_max),
        summary.p13b_pairs,
        summary.p13b_pairs_below_0_9,
        summary.p13b_pairs_at_or_above_0_95
    );
    out.scores = scores;
    out.predictions = Some(summary);
    write_json(&args.json, &out)?;
    write_json(&args.retained_json, &out)?;
    eprintln!(
        "wrote {} and {}",
        args.json.display(),
        args.retained_json.display()
    );
    Ok(())
}

fn main() -> Result<()> {
    match Cli::parse().command {
        Command::Scan(args) => scan(&args),
        Command::Score(args) => score(&args),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg() -> Config {
        Config {
            tau: 0.51,
            u0: 0.1,
            delta: 4.0,
        }
    }

    #[test]
    fn shear_layer_is_periodic_and_has_zero_mean_transverse_velocity() {
        let (rho, u) = shear_fields(cfg(), 0.05);
        assert_eq!(rho.len(), CELLS);
        assert!(rho.iter().all(|&r| r == 1.0));
        let at = |x: usize, y: usize, z: usize| u[z * NX * NY + y * NX + x];

        // The step between the last and first row is no larger than the
        // largest interior step, so the profile closes on itself.
        let jump = |y0: usize, y1: usize| (at(0, y0, 0)[0] - at(0, y1, 0)[0]).abs();
        let interior = (0..NY - 1).map(|y| jump(y, y + 1)).fold(0.0, f64::max);
        assert!(jump(NY - 1, 0) <= interior + 1e-12);
        // The same closure along x for the transverse component.
        let xjump = |x0: usize, x1: usize| (at(x0, 0, 0)[1] - at(x1, 0, 0)[1]).abs();
        let xinterior = (0..NX - 1).map(|x| xjump(x, x + 1)).fold(0.0, f64::max);
        assert!(xjump(NX - 1, 0) <= xinterior + 1e-12);

        let mean_uy = u.iter().map(|v| v[1]).sum::<f64>() / CELLS as f64;
        assert!(mean_uy.abs() < 1e-14, "mean u_y {mean_uy}");
        for y in 0..NY {
            let row: f64 = (0..NX).map(|x| at(x, y, 0)[1]).sum();
            assert!(row.abs() < 1e-12, "row {y} sum {row}");
        }
        // The second layer is the first one shifted by NY / 2 with its sign
        // reversed.
        for y in 0..NY / 2 {
            assert!((shear_ux(cfg(), y + NY / 2) + shear_ux(cfg(), y)).abs() < 1e-12);
        }
        assert!(u.iter().all(|v| v[2] == 0.0));
    }

    #[test]
    fn shear_layer_crosses_zero_at_the_layer_centers() {
        let c = cfg();
        assert!(shear_ux(c, NY / 4).abs() < 1e-12);
        assert!((shear_ux(c, NY / 2 - 1) - c.u0 * (15.0_f64 / 4.0).tanh()).abs() < 1e-12);
        assert!(shear_ux(c, 3 * NY / 4).abs() < 1e-12);
        assert!((shear_ux(c, 0) + c.u0 * (16.0_f64 / 4.0).tanh()).abs() < 1e-12);
    }

    #[test]
    fn auc_of_a_separating_score_and_of_its_negation() {
        let score = [0.1, 0.2, 0.3, 0.7, 0.8, 0.9];
        let label = [false, false, false, true, true, true];
        assert!((auc(&score, &label) - 1.0).abs() < 1e-12);
        let negated: Vec<f64> = score.iter().map(|s| -s).collect();
        assert!(auc(&negated, &label).abs() < 1e-12);
    }

    #[test]
    fn auc_of_tied_scores_is_one_half_in_either_label_order() {
        let score = [1.0, 1.0, 1.0, 1.0];
        assert!((auc(&score, &[false, false, true, true]) - 0.5).abs() < 1e-12);
        assert!((auc(&score, &[true, true, false, false]) - 0.5).abs() < 1e-12);
    }

    #[test]
    fn gram_volume_of_an_orthonormal_triple_is_one() {
        let mut e = [vec![0.0; DIM], vec![0.0; DIM], vec![0.0; DIM]];
        e[0][0] = 1.0;
        e[1][5] = 1.0;
        e[2][31] = 1.0;
        assert!((gram_volume(&e[0], &e[1], &e[2]) - 1.0).abs() < 1e-14);
    }

    #[test]
    fn gram_volume_of_a_collinear_triple_is_zero() {
        let mut a = vec![0.0; DIM];
        a[3] = 1.0;
        a[7] = -2.0;
        let scaled = |k: f64| a.iter().map(|x| k * x).collect::<Vec<f64>>();
        assert_eq!(gram_volume(&a, &scaled(2.0), &scaled(-0.5)), 0.0);
    }

    #[test]
    fn gram_volume_equals_the_square_root_of_the_gram_determinant() {
        let v0: Vec<f64> = (0..DIM).map(|i| ((i * 7 + 1) % 11) as f64 - 5.0).collect();
        let v1: Vec<f64> = (0..DIM).map(|i| ((i * 5 + 3) % 13) as f64 - 6.0).collect();
        let v2: Vec<f64> = (0..DIM).map(|i| ((i * 3 + 2) % 17) as f64 - 8.0).collect();
        let g = [
            [dot(&v0, &v0), dot(&v0, &v1), dot(&v0, &v2)],
            [dot(&v1, &v0), dot(&v1, &v1), dot(&v1, &v2)],
            [dot(&v2, &v0), dot(&v2, &v1), dot(&v2, &v2)],
        ];
        let det = g[0][0] * (g[1][1] * g[2][2] - g[1][2] * g[2][1])
            - g[0][1] * (g[1][0] * g[2][2] - g[1][2] * g[2][0])
            + g[0][2] * (g[1][0] * g[2][1] - g[1][1] * g[2][0]);
        let expected = det.sqrt();
        let got = gram_volume(&v0, &v1, &v2);
        assert!((got - expected).abs() < 1e-9 * expected, "{got} {expected}");
        assert!((gram_volume(&v2, &v0, &v1) - expected).abs() < 1e-9 * expected);
    }

    #[test]
    fn selection_spreads_over_the_failure_steps() {
        let rows: Vec<ScanRow> = (0..20)
            .map(|i| ScanRow {
                grid: "base".to_string(),
                tau: 0.5,
                u0: 0.1,
                delta: 1.0,
                first_violation_step: Some(200 + 10 * i),
                violating_cells: Some(1),
                min_population: Some(-1.0),
                kept: true,
            })
            .collect();
        let picked = select_kept(&rows, 8);
        assert_eq!(picked.len(), 8);
        assert_eq!(picked[0].first_violation_step, Some(200));
        assert_eq!(picked[7].first_violation_step, Some(390));
    }
}
