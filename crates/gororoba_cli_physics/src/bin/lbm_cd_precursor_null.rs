// SPDX-License-Identifier: MIT
//! Controls for the LBM associator precursor ratio of claim C-1617.
//!
//! The statistic is the half ratio of the temporal associator norms at the
//! first violation cell of a D3Q19 BGK Gaussian-density run: the mean of the
//! late half of the series over the mean of the early half (`lbm-rca-probe
//! --cd-probe`). The solver is the probe's: a 16^3 periodic lattice, tau 0.7,
//! density 1 + (contrast - 1) exp(-r^2 / (2 sigma^2)) with sigma = 16 / 6 and
//! zero velocity. Per contrast this binary measures:
//!
//! 1. the ratio of the same cell under four cheaper series (the first-difference
//!    and departure norms of the unit vectors, and the associator series without
//!    its last norm) and under six other slot maps of the 19 populations into
//!    the 32 slots (the identity map is the map of C-1617);
//! 2. the ratio at every cell, split by whether the cell holds a negative
//!    population at the violation step;
//! 3. the same ratio and spatial mean on stable runs (low contrast, no negative
//!    population) of the same length;
//! 4. how well five scores computed before the violation rank the cells that
//!    turn negative: the last associator norm, the departure norm, the
//!    first-difference norm, the local Mach number and the smallest population
//!    over the density.
//!
//! Output: one JSON file; a summary on stderr.

use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use cd_kernel::batch_sliding_associator_norms_parallel;
use clap::Parser;
use lbm_3d::{
    lattice::D3Q19Lattice,
    solver::{LbmSolver3D, aosoa_idx},
};
use rayon::prelude::*;
use serde::Serialize;

/// Cubic grid edge of the probe's solver.
const N: usize = 16;
/// BGK relaxation time of the probe's solver.
const TAU: f64 = 0.7;
/// Populations per cell (D3Q19).
const Q: usize = 19;
/// Embedding dimension: the 19 populations occupy 19 of 32 slots (a pathion).
const DIM: usize = 32;
/// Slot-map multipliers: population i sits at slot (m * i + 3) mod 32. Each
/// is odd, so the map is injective on 0..19.
const SLOT_MULTIPLIERS: [usize; 5] = [3, 5, 7, 11, 13];
/// Face-neighbor offsets of the spatial probe: the cell, then +-x, +-y, +-z.
const FACE_OFFSETS: [[i32; 3]; 7] = [
    [0, 0, 0],
    [1, 0, 0],
    [-1, 0, 0],
    [0, 1, 0],
    [0, -1, 0],
    [0, 0, 1],
    [0, 0, -1],
];
/// Populations below this norm stay unnormalized (the probe's guard).
const NORM_FLOOR: f64 = 1e-15;

#[derive(Parser)]
#[command(name = "lbm-cd-precursor-null")]
#[command(about = "LBM associator ratio against stable-run, cell and slot-map controls")]
struct Cli {
    /// Density contrasts whose first positivity violation is analyzed.
    #[arg(long, value_delimiter = ',', default_value = "21,22,23,24,25")]
    contrasts: Vec<f64>,

    /// Contrasts of the stable runs, each stepped as long as the violating run.
    #[arg(long, value_delimiter = ',', default_value = "2,5,10,15")]
    stable_contrasts: Vec<f64>,

    /// Step budget for the search of the first negative population.
    #[arg(long, default_value_t = 400)]
    max_steps: usize,

    /// Output JSON path.
    #[arg(
        long,
        default_value = "data/output/lbm/ablations/lbm_cd_precursor_null.json"
    )]
    out_json: PathBuf,
}

#[derive(Debug, Serialize)]
struct CellXyz {
    x: usize,
    y: usize,
    z: usize,
}

#[derive(Debug, Serialize)]
struct Quantiles {
    min: f64,
    p5: f64,
    p25: f64,
    median: f64,
    p75: f64,
    p95: f64,
    max: f64,
}

#[derive(Debug, Serialize)]
struct SlotMapRatio {
    map: String,
    ratio: f64,
}

#[derive(Debug, Serialize)]
struct StableRun {
    contrast: f64,
    /// Set when a negative population appears inside the run; the run then
    /// carries no ratio.
    #[serde(skip_serializing_if = "Option::is_none")]
    violated_at: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    min_population: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    ratio_at_cell: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    ratio_all_cells_median: Option<f64>,
    spatial_mean_by_step: Vec<f64>,
}

#[derive(Debug, Serialize)]
struct Ranking {
    auc_associator: f64,
    auc_departure: f64,
    auc_first_difference: f64,
    auc_mach: f64,
    auc_min_population_share: f64,
    spearman_associator_departure: f64,
    spearman_associator_mach: f64,
}

#[derive(Debug, Serialize)]
struct ContrastResult {
    contrast: f64,
    violation_step: usize,
    cell: CellXyz,
    violating_cells: usize,
    norms_at_cell: Vec<f64>,
    ratio_at_cell: f64,
    ratio_first_diff_at_cell: f64,
    ratio_departure_at_cell: f64,
    ratio_cut_1: Option<f64>,
    spatial_mean_by_step: Vec<f64>,
    ratio_by_slot_map: Vec<SlotMapRatio>,
    ratio_violating_cells: Quantiles,
    ratio_nonviolating_cells: Quantiles,
    share_nonviolating_above_1_1: f64,
    stable: Vec<StableRun>,
    ranking: Option<Ranking>,
}

#[derive(Debug, Serialize)]
struct Output {
    grid: usize,
    tau: f64,
    max_steps: usize,
    contrasts: Vec<ContrastResult>,
}

/// Gaussian density perturbation centered on the grid, as `lbm-rca-probe`.
fn gaussian_density(contrast: f64) -> Vec<f64> {
    let center = (N / 2) as f64;
    let sigma = (N as f64) / 6.0;
    let mut rho = Vec::with_capacity(N * N * N);
    for ix in 0..N {
        for iy in 0..N {
            for iz in 0..N {
                let dx = ix as f64 - center;
                let dy = iy as f64 - center;
                let dz = iz as f64 - center;
                let r2 = dx * dx + dy * dy + dz * dz;
                rho.push(1.0 + (contrast - 1.0) * (-r2 / (2.0 * sigma * sigma)).exp());
            }
        }
    }
    rho
}

/// BGK solver at rest on the Gaussian density, as `lbm-rca-probe`.
fn fresh_solver(contrast: f64) -> LbmSolver3D {
    let mut solver = LbmSolver3D::new(N, N, N, TAU);
    let rho = gaussian_density(contrast);
    let u_zero = vec![[0.0_f64; 3]; N * N * N];
    solver.rho.copy_from_slice(&rho);
    solver.u.copy_from_slice(&u_zero);
    solver.reinitialize_from_macroscopic();
    solver
}

/// The populations of every cell, cell-major (`cell * 19 + direction`).
fn snapshot(solver: &LbmSolver3D) -> Vec<f64> {
    let mut state = Vec::with_capacity(N * N * N * Q);
    for cell in 0..N * N * N {
        for dir in 0..Q {
            state.push(solver.f[aosoa_idx(cell, dir)]);
        }
    }
    state
}

/// First cell, in linear order z * N * N + y * N + x, that holds a negative
/// population.
fn first_negative_cell(state: &[f64]) -> Option<usize> {
    state
        .chunks_exact(Q)
        .position(|pops| pops.iter().any(|&f| f < 0.0))
}

/// Decode a linear cell index into (x, y, z).
fn decode_cell(cell: usize) -> CellXyz {
    CellXyz {
        x: cell % N,
        y: (cell % (N * N)) / N,
        z: cell / (N * N),
    }
}

fn encode_cell(x: usize, y: usize, z: usize) -> usize {
    z * N * N + y * N + x
}

/// States 0..=t of a run, and the first step that leaves a negative population.
struct Run {
    states: Vec<Vec<f64>>,
    violation: Option<Violation>,
}

struct Violation {
    step: usize,
    cell: usize,
}

/// Step the solver (collision, then streaming) up to `max_steps`, stopping at
/// the first step after which a population is negative. State 0 is the
/// equilibrium initialization.
fn run(contrast: f64, max_steps: usize) -> Run {
    let mut solver = fresh_solver(contrast);
    let mut states = vec![snapshot(&solver)];
    for step in 1..=max_steps {
        let _ = solver.phase1_collision();
        let _ = solver.phase2_streaming();
        let state = snapshot(&solver);
        let negative = first_negative_cell(&state);
        states.push(state);
        if let Some(cell) = negative {
            return Run {
                states,
                violation: Some(Violation { step, cell }),
            };
        }
    }
    Run {
        states,
        violation: None,
    }
}

/// Slot of each population: identity.
fn identity_map() -> [usize; Q] {
    std::array::from_fn(|i| i)
}

/// Slot of population i: (m * i + 3) mod 32.
fn multiplier_map(m: usize) -> [usize; Q] {
    std::array::from_fn(|i| (m * i + 3) % DIM)
}

/// Slot of population i: 18 - i.
fn reversed_map() -> [usize; Q] {
    std::array::from_fn(|i| Q - 1 - i)
}

/// The 19 populations of one cell in a 32-vector at the given slots, divided
/// by its Euclidean norm.
fn cell_vector(state: &[f64], cell: usize, slots: &[usize; Q]) -> Vec<f64> {
    let mut v = vec![0.0; DIM];
    for (dir, &slot) in slots.iter().enumerate() {
        v[slot] = state[cell * Q + dir];
    }
    let norm = v.iter().map(|x| x * x).sum::<f64>().sqrt();
    if norm > NORM_FLOOR {
        v.iter_mut().for_each(|x| *x /= norm);
    }
    v
}

fn distance(a: &[f64], b: &[f64]) -> f64 {
    a.iter()
        .zip(b)
        .map(|(x, y)| (x - y) * (x - y))
        .sum::<f64>()
        .sqrt()
}

fn mean(values: &[f64]) -> f64 {
    if values.is_empty() {
        return f64::NAN;
    }
    values.iter().sum::<f64>() / values.len() as f64
}

/// Mean of the second half over the mean of the first half, with the first half
/// `len / 2` long (the verdict statistic of `lbm-rca-probe`).
fn half_ratio(x: &[f64]) -> f64 {
    let half = x.len() / 2;
    if half == 0 {
        return f64::NAN;
    }
    mean(&x[half..]) / mean(&x[..half]).max(1e-20)
}

/// Percentile with linear interpolation between order statistics; NaN for an
/// empty list.
fn percentile(values: &[f64], pct: f64) -> f64 {
    if values.is_empty() {
        return f64::NAN;
    }
    let mut sorted = values.to_vec();
    sorted.sort_by(f64::total_cmp);
    let pos = pct / 100.0 * (sorted.len() - 1) as f64;
    let lo = pos.floor() as usize;
    let hi = (lo + 1).min(sorted.len() - 1);
    sorted[lo] + (sorted[hi] - sorted[lo]) * (pos - lo as f64)
}

/// Quantiles of the finite entries of `values`.
fn quantiles(values: &[f64]) -> Quantiles {
    let finite: Vec<f64> = values.iter().copied().filter(|v| v.is_finite()).collect();
    Quantiles {
        min: percentile(&finite, 0.0),
        p5: percentile(&finite, 5.0),
        p25: percentile(&finite, 25.0),
        median: percentile(&finite, 50.0),
        p75: percentile(&finite, 75.0),
        p95: percentile(&finite, 95.0),
        max: percentile(&finite, 100.0),
    }
}

/// Associator norms of the cell's unit vectors over consecutive state triples.
fn assoc_series(states: &[Vec<f64>], cell: usize, slots: &[usize; Q]) -> Vec<f64> {
    let vectors: Vec<Vec<f64>> = states.iter().map(|s| cell_vector(s, cell, slots)).collect();
    batch_sliding_associator_norms_parallel(&vectors, DIM)
}

/// First-difference and departure norms of the cell's unit vectors, one per
/// state triple (the triple ending at state t + 2 gives |v[t+2] - v[t+1]| and
/// |v[t+2] - v[0]|).
fn difference_series(states: &[Vec<f64>], cell: usize) -> (Vec<f64>, Vec<f64>) {
    let vectors: Vec<Vec<f64>> = states
        .iter()
        .map(|s| cell_vector(s, cell, &identity_map()))
        .collect();
    let first_diff = vectors.windows(3).map(|w| distance(&w[2], &w[1])).collect();
    let departure = vectors
        .windows(3)
        .map(|w| distance(&w[2], &vectors[0]))
        .collect();
    (first_diff, departure)
}

/// Half ratio of the associator series of every cell.
fn assoc_ratios_all_cells(states: &[Vec<f64>]) -> Vec<f64> {
    let identity = identity_map();
    (0..N * N * N)
        .into_par_iter()
        .map(|cell| half_ratio(&assoc_series(states, cell, &identity)))
        .collect()
}

/// Mean associator norm of the 7 face-neighbor cell vectors of `cell` (center,
/// +-x, +-y, +-z with periodic wrap) at one state: 5 consecutive triples.
fn spatial_mean(state: &[f64], cell: usize) -> f64 {
    let at = decode_cell(cell);
    let identity = identity_map();
    let vectors: Vec<Vec<f64>> = FACE_OFFSETS
        .iter()
        .map(|off| {
            let wrap = |c: usize, d: i32| (c as i32 + d).rem_euclid(N as i32) as usize;
            let neighbor = encode_cell(wrap(at.x, off[0]), wrap(at.y, off[1]), wrap(at.z, off[2]));
            cell_vector(state, neighbor, &identity)
        })
        .collect();
    mean(&batch_sliding_associator_norms_parallel(&vectors, DIM))
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

/// The five pre-violation scores of every cell and their ranking of the cells
/// that are negative at the violation step. `before` holds states
/// 0..=t_v - 1, none with a negative population.
fn ranking(before: &[Vec<f64>], violating: &[bool]) -> Option<Ranking> {
    if before.len() < 3 {
        return None;
    }
    let lattice = D3Q19Lattice::new();
    let identity = identity_map();
    let last = before.len() - 1;
    let cells = N * N * N;
    let mut associator = Vec::with_capacity(cells);
    let mut departure = Vec::with_capacity(cells);
    let mut first_difference = Vec::with_capacity(cells);
    let mut mach = Vec::with_capacity(cells);
    let mut min_share = Vec::with_capacity(cells);
    for cell in 0..cells {
        let triple: Vec<Vec<f64>> = before[last - 2..]
            .iter()
            .map(|s| cell_vector(s, cell, &identity))
            .collect();
        associator.push(batch_sliding_associator_norms_parallel(&triple, DIM)[0]);
        let v0 = cell_vector(&before[0], cell, &identity);
        departure.push(distance(&triple[2], &v0));
        first_difference.push(distance(&triple[2], &triple[1]));

        let pops = &before[last][cell * Q..(cell + 1) * Q];
        let rho: f64 = pops.iter().sum();
        let mut momentum = [0.0_f64; 3];
        for (dir, &f) in pops.iter().enumerate() {
            let c = lattice.velocities[dir];
            for (m, &cd) in momentum.iter_mut().zip(&c) {
                *m += f64::from(cd) * f;
            }
        }
        let speed = momentum.iter().map(|m| m * m).sum::<f64>().sqrt() / rho;
        mach.push(speed * 3.0_f64.sqrt());
        let smallest = pops.iter().copied().fold(f64::INFINITY, f64::min);
        min_share.push(-smallest / rho);
    }
    Some(Ranking {
        auc_associator: auc(&associator, violating),
        auc_departure: auc(&departure, violating),
        auc_first_difference: auc(&first_difference, violating),
        auc_mach: auc(&mach, violating),
        auc_min_population_share: auc(&min_share, violating),
        spearman_associator_departure: spearman(&associator, &departure),
        spearman_associator_mach: spearman(&associator, &mach),
    })
}

/// A stable run of exactly `steps` steps at `contrast`, read at `cell`.
fn stable_run(contrast: f64, steps: usize, cell: usize) -> StableRun {
    let r = run(contrast, steps);
    if let Some(v) = r.violation {
        return StableRun {
            contrast,
            violated_at: Some(v.step),
            min_population: None,
            ratio_at_cell: None,
            ratio_all_cells_median: None,
            spatial_mean_by_step: Vec::new(),
        };
    }
    let identity = identity_map();
    let ratios = assoc_ratios_all_cells(&r.states);
    let finite: Vec<f64> = ratios.iter().copied().filter(|v| v.is_finite()).collect();
    let min_population = r
        .states
        .last()
        .map(|s| s.iter().copied().fold(f64::INFINITY, f64::min));
    StableRun {
        contrast,
        violated_at: None,
        min_population,
        ratio_at_cell: Some(half_ratio(&assoc_series(&r.states, cell, &identity))),
        ratio_all_cells_median: Some(percentile(&finite, 50.0)),
        spatial_mean_by_step: r.states.iter().map(|s| spatial_mean(s, cell)).collect(),
    }
}

fn analyze_contrast(contrast: f64, cli: &Cli) -> Result<ContrastResult> {
    let violating_run = run(contrast, cli.max_steps);
    let Some(violation) = violating_run.violation else {
        bail!(
            "contrast {contrast}: no negative population in {} steps",
            cli.max_steps
        );
    };
    let (t_v, cell) = (violation.step, violation.cell);
    let states = &violating_run.states;
    let identity = identity_map();

    let norms = assoc_series(states, cell, &identity);
    let (first_diff, departure) = difference_series(states, cell);
    let cut_1 = (norms.len() > 3).then(|| half_ratio(&norms[..norms.len() - 1]));

    let mut by_slot_map = Vec::new();
    for m in SLOT_MULTIPLIERS {
        by_slot_map.push(SlotMapRatio {
            map: format!("m{m}"),
            ratio: half_ratio(&assoc_series(states, cell, &multiplier_map(m))),
        });
    }
    by_slot_map.push(SlotMapRatio {
        map: "reversed".to_string(),
        ratio: half_ratio(&assoc_series(states, cell, &reversed_map())),
    });

    let final_state = &states[t_v];
    let violating: Vec<bool> = final_state
        .chunks_exact(Q)
        .map(|pops| pops.iter().any(|&f| f < 0.0))
        .collect();
    let ratios = assoc_ratios_all_cells(states);
    let split = |want: bool| -> Vec<f64> {
        ratios
            .iter()
            .zip(&violating)
            .filter(|(_, v)| **v == want)
            .map(|(r, _)| *r)
            .collect()
    };
    let nonviolating = split(false);
    let above = nonviolating.iter().filter(|&&r| r > 1.1).count();

    Ok(ContrastResult {
        contrast,
        violation_step: t_v,
        cell: decode_cell(cell),
        violating_cells: violating.iter().filter(|&&v| v).count(),
        ratio_at_cell: half_ratio(&norms),
        ratio_first_diff_at_cell: half_ratio(&first_diff),
        ratio_departure_at_cell: half_ratio(&departure),
        ratio_cut_1: cut_1,
        norms_at_cell: norms,
        spatial_mean_by_step: states.iter().map(|s| spatial_mean(s, cell)).collect(),
        ratio_by_slot_map: by_slot_map,
        ratio_violating_cells: quantiles(&split(true)),
        ratio_nonviolating_cells: quantiles(&nonviolating),
        share_nonviolating_above_1_1: above as f64 / nonviolating.len() as f64,
        stable: cli
            .stable_contrasts
            .iter()
            .map(|&c| stable_run(c, t_v, cell))
            .collect(),
        ranking: ranking(&states[..t_v], &violating),
    })
}

fn report(r: &ContrastResult) {
    eprintln!(
        "contrast {}: violation step {} at ({},{},{}), {} violating cells",
        r.contrast, r.violation_step, r.cell.x, r.cell.y, r.cell.z, r.violating_cells
    );
    eprintln!(
        "  ratio at cell {:.4}  first diff {:.4}  departure {:.4}  cut 1 {}",
        r.ratio_at_cell,
        r.ratio_first_diff_at_cell,
        r.ratio_departure_at_cell,
        r.ratio_cut_1
            .map_or("n/a".to_string(), |v| format!("{v:.4}"))
    );
    let maps: Vec<String> = r
        .ratio_by_slot_map
        .iter()
        .map(|m| format!("{} {:.4}", m.map, m.ratio))
        .collect();
    eprintln!("  slot maps: {}", maps.join(", "));
    eprintln!(
        "  violating cells median {:.4} (p5 {:.4}, p95 {:.4}); non-violating median {:.4} (p5 {:.4}, p95 {:.4}); share above 1.1 {:.4}",
        r.ratio_violating_cells.median,
        r.ratio_violating_cells.p5,
        r.ratio_violating_cells.p95,
        r.ratio_nonviolating_cells.median,
        r.ratio_nonviolating_cells.p5,
        r.ratio_nonviolating_cells.p95,
        r.share_nonviolating_above_1_1
    );
    for s in &r.stable {
        match s.violated_at {
            Some(step) => eprintln!("  stable contrast {}: violated at {step}", s.contrast),
            None => eprintln!(
                "  stable contrast {}: ratio at cell {:.4}  all-cell median {:.4}  last spatial mean {:.6e}",
                s.contrast,
                s.ratio_at_cell.unwrap_or(f64::NAN),
                s.ratio_all_cells_median.unwrap_or(f64::NAN),
                s.spatial_mean_by_step.last().copied().unwrap_or(f64::NAN)
            ),
        }
    }
    if let Some(k) = &r.ranking {
        eprintln!(
            "  AUC: associator {:.4} departure {:.4} first diff {:.4} Mach {:.4} min population {:.4}; Spearman associator-departure {:.4}, associator-Mach {:.4}",
            k.auc_associator,
            k.auc_departure,
            k.auc_first_difference,
            k.auc_mach,
            k.auc_min_population_share,
            k.spearman_associator_departure,
            k.spearman_associator_mach
        );
    }
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let mut contrasts = Vec::new();
    for &contrast in &cli.contrasts {
        let result = analyze_contrast(contrast, &cli)?;
        report(&result);
        contrasts.push(result);
    }
    let output = Output {
        grid: N,
        tau: TAU,
        max_steps: cli.max_steps,
        contrasts,
    };
    if let Some(parent) = cli.out_json.parent() {
        std::fs::create_dir_all(parent).with_context(|| format!("create {}", parent.display()))?;
    }
    std::fs::write(&cli.out_json, serde_json::to_string_pretty(&output)?)
        .with_context(|| format!("write {}", cli.out_json.display()))?;
    eprintln!("wrote {}", cli.out_json.display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn half_ratio_of_a_step_and_of_a_constant() {
        assert!((half_ratio(&[1.0, 1.0, 2.0, 2.0]) - 2.0).abs() < 1e-12);
        assert!((half_ratio(&[3.0, 3.0, 3.0, 3.0]) - 1.0).abs() < 1e-12);
    }

    #[test]
    fn slot_maps_are_injective_into_the_32_slots() {
        let mut maps: Vec<[usize; Q]> = SLOT_MULTIPLIERS
            .iter()
            .map(|&m| multiplier_map(m))
            .collect();
        maps.push(reversed_map());
        maps.push(identity_map());
        for map in maps {
            let mut seen = [false; DIM];
            for slot in map {
                assert!(slot < DIM, "slot {slot} outside 0..32");
                assert!(!seen[slot], "slot {slot} used twice");
                seen[slot] = true;
            }
        }
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
    fn contrast_two_run_holds_no_negative_population() {
        let r = run(2.0, 5);
        assert!(r.violation.is_none());
        assert_eq!(r.states.len(), 6);
        for state in &r.states {
            assert!(state.iter().all(|&f| f >= 0.0));
        }
        let cell = encode_cell(7, 6, 2);
        let state_zero = spatial_mean(&r.states[0], cell);
        assert!(state_zero < 1e-12, "state-0 spatial mean {state_zero}");
    }

    #[test]
    fn cell_vector_is_unit_norm_at_its_slots() {
        let state: Vec<f64> = (0..Q).map(|i| 1.0 + i as f64).collect();
        let v = cell_vector(&state, 0, &multiplier_map(5));
        let norm = v.iter().map(|x| x * x).sum::<f64>().sqrt();
        assert!((norm - 1.0).abs() < 1e-12);
        assert_eq!(v.iter().filter(|&&x| x != 0.0).count(), Q);
        assert!(v[3] > 0.0, "population 0 sits at slot 3");
    }

    #[test]
    fn percentile_interpolates_linearly() {
        assert_eq!(percentile(&[1.0, 2.0, 3.0, 4.0], 50.0), 2.5);
        assert_eq!(percentile(&[1.0, 2.0, 3.0, 4.0], 0.0), 1.0);
        assert_eq!(percentile(&[1.0, 2.0, 3.0, 4.0], 100.0), 4.0);
    }
}
