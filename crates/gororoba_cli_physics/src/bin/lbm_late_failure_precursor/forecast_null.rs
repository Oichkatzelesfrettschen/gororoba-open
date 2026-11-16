// SPDX-License-Identifier: MIT
//! Null distributions for the anchored forecast of
//! `lbm-late-failure-precursor`: subcommand `forecast-null`.
//!
//! Each run is re-simulated to its anchor (the same solver, anchor and labels
//! as `forecast`), keeping the 64 states that end at the anchor, and the
//! observed ROC areas are checked against the retained forecast record before
//! any null is read. Every test then asks what a ROC area of the better
//! orientation (the larger of the area and its complement) reaches without
//! the structure it is credited to.
//!
//! Model. The four z layers of a run are bitwise identical, and the shear
//! layer is invariant under two lattice reflections combined with a velocity
//! reflection (each verified on the anchor state to a relative tolerance, see
//! `generators`). Cells in one orbit of the verified group carry equal
//! labels and equal quartiles, so the exchangeable unit of a label permutation
//! is the orbit, not the cell. Scores that ignore the order of the 19
//! populations (the Gram volume, the step difference, the Mach number, the
//! smallest population share, |c - a|) take equal values on an orbit. The
//! associator does not: it places the populations in 32 slots through the
//! identity slot map, a velocity reflection permutes the slots, and the
//! Cayley-Dickson product is not invariant under that permutation, so one
//! orbit holds several associator values (`score_image_deviation` records the
//! spread). Three levels are reported: the cell, the z layer and the orbit.
//! The orbit level draws a tie-free rank-sum law from the orbit counts
//! (`level_null`); the direct orbit null (`direct_null`) relabels whole
//! orbits of equal size and recomputes the cell-level area of the actual
//! scores, which is the law of the statistic that P13d compares. A score
//! field is spatially smooth, so the orbit nulls still understate the
//! dependence between neighboring cells; the torus-shift null keeps it by
//! translating the score field of the z = 0 layer against fixed labels and
//! fixed quartile masks.
//!
//! Tests, each on the six scores unless a family says otherwise (the associator, the Gram volume, the step
//! difference, the Mach number, the smallest population share, and the norm
//! of the two-step difference |c - a| of the unit vectors a, b, c at steps
//! t-2, t-1, t):
//!
//! 1. label permutation at the cell, z-layer and orbit level (Poisson-binomial
//!    law of the count of pairs above the bound, per-pair tail probability),
//!    and the direct relabeling of whole orbits;
//! 2. torus shift of the z = 0 layer (every non-zero shift, and the shifts
//!    along x alone);
//! 3. surrogate increments: the last two increments of each cell replaced
//!    from the cell's own 63 increments with the end state fixed, by a block
//!    permutation (blocks of seven), by a draw of two increments, and by a
//!    common random phase per frequency of the 63-step increment spectrum;
//! 4. algebra substitution on the XOR-graded 32-dimensional basis: sign
//!    cocycles of the Cayley-Dickson doubling with split levels, of the
//!    sedenion, octonion and quaternion algebras (tensored with a
//!    group algebra of Z2), of the Clifford algebras Cl(0,5) and Cl(5,0) and
//!    of the group algebra, random sign cocycles, and dense random bilinear
//!    products; the associative ones are negative controls;
//! 5. the order decomposition of the associator in the increments
//!    b - a and c - a;
//! 6. a logistic likelihood-ratio test of the associator given the
//!    product-free scores at orbit level;
//! 7. Benjamini-Hochberg and Holm adjustments over the per-pair tests. Each
//!    family is stated in the record: the label tests adjust the pairs of one
//!    score (one family per score), the torus tests adjust the per-pair
//!    probabilities of five scores (the associator and the four original
//!    product-free scores) and of all six, and the likelihood-ratio test
//!    adjusts the tested pairs.
//!
//! P13d reads its threshold from the rank-sum law of the orbit counts and
//! records the direct-relabeling quantile beside it; a pair whose associator
//! area, threshold or product-free area is not finite receives no call, stays
//! out of the pair count behind the floor of 8 and is listed under `skipped`.
//!
//! The count statistic of the null is a Poisson-binomial sum over the
//! (run, quartile) pairs, which treats pairs of one run as independent; the
//! torus null keeps their shared shift, and is the reference for the
//! count. Seeds are values of an ANU QRNG draw, one index per use.

use std::collections::{BTreeMap, VecDeque};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use clap::Args;
use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha8Rng;
use rand_distr::{Distribution, StandardNormal};
use rayon::prelude::*;
use rustfft::{FftPlanner, num_complex::Complex};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use statrs::distribution::{ChiSquared, ContinuousCDF, Normal};

use super::{
    CELLS, Config, ConfigKey, D3Q19Lattice, DIM, FORECAST_LEAD, FORECAST_WINDOW, Forecast,
    NORM_FLOOR, NX, NY, NZ, Output, P13C_BOUND, P13C_MIN_POSITIVES, Q, QUARTILES, auc, cell_scores,
    distance, fresh_solver, gram_volume, mark_first_bad, mean_ranks, median, orient,
    population_quartiles, snapshot_into, spearman, unit_vector, violation_in,
};

/// Names of the six scores, in the order of every per-score array.
const SCORE_NAMES: [&str; 6] = [
    "associator",
    "gram_volume",
    "step_difference",
    "mach",
    "min_population_share",
    "two_step_difference",
];
/// Scores that carry no product: every name after the associator.
const PRODUCT_FREE: std::ops::Range<usize> = 1..6;
/// States kept per run: steps anchor-63 through the anchor.
const HISTORY: usize = 64;
/// Increments between consecutive kept states.
const INCREMENTS: usize = HISTORY - 1;
/// Length of a block of the block-permutation surrogate.
const BLOCK: usize = 7;
/// Relative tolerance of a symmetry of the anchor state.
const SYMMETRY_TOLERANCE: f64 = 1e-3;
/// Tolerance at which the orbit count is reported again, for comparison.
const SYMMETRY_STRICT_TOLERANCE: f64 = 1e-9;
/// Quantile of the orbit null that P13d reads as its calibrated threshold.
const P13D_QUANTILE: f64 = 0.95;
/// Margin by which P13d requires the associator to beat the best product-free area.
const P13D_MARGIN: f64 = 0.02;
/// Pairs P13d needs before it reports a verdict.
const P13D_MIN_PAIRS: usize = 8;
/// Pairs of random unit triples behind the algebra property table.
const PROPERTY_TRIPLES: usize = 2000;

/// Indices of the ANU QRNG draw that seed each use (one value per use).
const SEED_LABELS: usize = 1;
const SEED_BLOCK: usize = 2;
const SEED_SHUFFLE: usize = 3;
const SEED_PHASE: usize = 4;
const SEED_SIGNS: usize = 5;
const SEED_DENSE: usize = 6;
const SEED_TRIPLES: usize = 7;
const SEED_ORBIT_DIRECT: usize = 9;
/// Draws per random stream of the direct orbit null.
const DIRECT_CHUNK: usize = 500;

#[derive(Args)]
pub struct NullArgs {
    /// JSON files written by `score`; the configurations they score are the
    /// runs of the null, or with `--heldout` the kept configurations they leave
    /// unscored.
    #[arg(
        long,
        value_delimiter = ',',
        default_values = [
            "data/output/audit/claim-family-evidence-adjudication/lbm-late-failure-precursor.json",
            "data/output/audit/claim-family-evidence-adjudication/lbm-late-failure-precursor-widened.json",
        ]
    )]
    json: Vec<PathBuf>,

    /// Retained forecast record that the re-simulated areas must reproduce.
    #[arg(
        long,
        default_value = "data/output/audit/claim-family-evidence-adjudication/lbm-late-failure-forecast.json"
    )]
    forecast_json: PathBuf,

    /// ANU QRNG draw that holds the seeds.
    #[arg(
        long,
        default_value = "data/output/audit/claim-family-evidence-adjudication/anu_qrng/draw-2026-11-15T230053Z.json"
    )]
    draw_json: PathBuf,

    /// Output JSON path.
    #[arg(
        long,
        default_value = "data/output/audit/claim-family-evidence-adjudication/lbm-late-failure-null.json"
    )]
    out_json: PathBuf,

    /// Surrogate series per cell and kind in the increment nulls.
    #[arg(long, default_value_t = 20)]
    surrogates: usize,

    /// Label permutations per (run, quartile) pair and level.
    #[arg(long, default_value_t = 20000)]
    label_draws: usize,

    /// Run the kept configurations that the score files leave unscored; the
    /// retained forecast record is not read.
    #[arg(long)]
    heldout: bool,
}

// ---------------------------------------------------------------- statistics

/// splitmix64 finalizer, the mixing step of the per-use random streams.
fn mix(x: u64) -> u64 {
    let mut z = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// The stream of seed `seed` addressed by two coordinates, independent of thread order.
fn stream(seed: u64, a: u64, b: u64) -> ChaCha8Rng {
    ChaCha8Rng::seed_from_u64(mix(seed ^ mix(a ^ mix(b))))
}

/// Benjamini-Hochberg adjusted p-values.
fn benjamini_hochberg(p: &[f64]) -> Vec<f64> {
    let n = p.len();
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| p[a].total_cmp(&p[b]));
    let mut adjusted = vec![0.0; n];
    let mut running = 1.0_f64;
    for (rank, &i) in order.iter().enumerate().rev() {
        running = running.min(p[i] * n as f64 / (rank + 1) as f64);
        adjusted[i] = running;
    }
    adjusted
}

/// Holm step-down adjusted p-values.
fn holm(p: &[f64]) -> Vec<f64> {
    let n = p.len();
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| p[a].total_cmp(&p[b]));
    let mut adjusted = vec![0.0; n];
    let mut running = 0.0_f64;
    for (rank, &i) in order.iter().enumerate() {
        running = running.max((p[i] * (n - rank) as f64).min(1.0));
        adjusted[i] = running;
    }
    adjusted
}

fn count_below(p: &[f64], bound: f64) -> usize {
    p.iter().filter(|&&x| x < bound).count()
}

/// Law of the number of successes among independent Bernoulli trials.
fn poisson_binomial(p: &[f64]) -> Vec<f64> {
    let mut law = vec![0.0; p.len() + 1];
    law[0] = 1.0;
    for &x in p {
        for k in (1..law.len()).rev() {
            law[k] = law[k] * (1.0 - x) + law[k - 1] * x;
        }
        law[0] *= 1.0 - x;
    }
    law
}

/// Quantile of sorted values by linear interpolation between order statistics.
fn quantile(sorted: &[f64], q: f64) -> f64 {
    if sorted.is_empty() {
        return f64::NAN;
    }
    let pos = q * (sorted.len() - 1) as f64;
    let lo = pos.floor() as usize;
    let hi = pos.ceil() as usize;
    sorted[lo] + (sorted[hi] - sorted[lo]) * (pos - lo as f64)
}

fn oriented(a: f64) -> f64 {
    if a.is_finite() {
        orient(a).auc
    } else {
        f64::NAN
    }
}

/// Oriented ROC areas of `draws` random labelings with `positives` of `total` units, ties
/// absent (the exchangeable-label law of the rank-sum area).
fn oriented_null(positives: usize, total: usize, draws: usize, rng: &mut ChaCha8Rng) -> Vec<f64> {
    let negatives = total - positives;
    let norm = positives as f64 * negatives as f64;
    let mut ranks: Vec<u32> = (1..=total as u32).collect();
    (0..draws)
        .map(|_| {
            let mut sum = 0.0;
            for k in 0..positives {
                let j = rng.random_range(k..total);
                ranks.swap(k, j);
                sum += f64::from(ranks[k]);
            }
            let a = (sum - positives as f64 * (positives as f64 + 1.0) / 2.0) / norm;
            a.max(1.0 - a)
        })
        .collect()
}

// ------------------------------------------------------------------ algebras

/// A bilinear product on 32-vectors.
enum Algebra {
    /// `(ab)_{p^q} += sign[p][q] a_p b_q` on the XOR-graded basis.
    Xor(Vec<f64>),
    /// A dense structure tensor `t[(i * DIM + j) * DIM + k]`.
    Dense(Vec<f64>),
}

type Vector = [f64; DIM];

impl Algebra {
    fn mul(&self, a: &Vector, b: &Vector) -> Vector {
        let mut out = [0.0; DIM];
        match self {
            Self::Xor(sign) => {
                for (p, &ap) in a.iter().enumerate() {
                    if ap == 0.0 {
                        continue;
                    }
                    for (q, &bq) in b.iter().enumerate() {
                        out[p ^ q] += sign[p * DIM + q] * ap * bq;
                    }
                }
            }
            Self::Dense(t) => {
                for (i, &ai) in a.iter().enumerate() {
                    if ai == 0.0 {
                        continue;
                    }
                    for (j, &bj) in b.iter().enumerate() {
                        if bj == 0.0 {
                            continue;
                        }
                        let w = ai * bj;
                        let row = &t[(i * DIM + j) * DIM..(i * DIM + j + 1) * DIM];
                        for (o, &x) in out.iter_mut().zip(row) {
                            *o += w * x;
                        }
                    }
                }
            }
        }
        out
    }

    /// (ab)c - a(bc).
    fn associator(&self, a: &Vector, b: &Vector, c: &Vector) -> Vector {
        let left = self.mul(&self.mul(a, b), c);
        let right = self.mul(a, &self.mul(b, c));
        let mut out = [0.0; DIM];
        for k in 0..DIM {
            out[k] = left[k] - right[k];
        }
        out
    }
}

fn vnorm(v: &[f64]) -> f64 {
    v.iter().map(|x| x * x).sum::<f64>().sqrt()
}

fn vsub(a: &Vector, b: &Vector) -> Vector {
    let mut out = [0.0; DIM];
    for k in 0..DIM {
        out[k] = a[k] - b[k];
    }
    out
}

/// Product of two vectors of a Cayley-Dickson doubling, `(a,b)(c,d) = (ac + g d* b, da + b c*)` with
/// `g = gammas[level]`; `g = -1` at every level is the Cayley-Dickson algebra and `g = +1` a split level.
fn cd_mul(a: &[f64], b: &[f64], gammas: &[f64]) -> Vec<f64> {
    let n = a.len();
    if n == 1 {
        return vec![a[0] * b[0]];
    }
    let h = n / 2;
    let g = gammas[n.trailing_zeros() as usize - 1];
    let conj = |x: &[f64]| -> Vec<f64> {
        x.iter()
            .enumerate()
            .map(|(i, &v)| if i == 0 { v } else { -v })
            .collect()
    };
    let (al, ar) = a.split_at(h);
    let (cl, cr) = b.split_at(h);
    let left = cd_mul(al, cl, gammas);
    let left2 = cd_mul(&conj(cr), ar, gammas);
    let right = cd_mul(cr, al, gammas);
    let right2 = cd_mul(ar, &conj(cl), gammas);
    left.iter()
        .zip(&left2)
        .map(|(x, y)| x + g * y)
        .chain(right.iter().zip(&right2).map(|(x, y)| x + y))
        .collect()
}

/// Signs of the basis products `e_p e_q = sign[p][q] e_{p^q}` of the doubling of dimension
/// `dim` with the given level signs.
fn cd_sign_table(dim: usize, gammas: &[f64]) -> Result<Vec<f64>> {
    let mut table = vec![0.0; dim * dim];
    for p in 0..dim {
        for q in 0..dim {
            let mut a = vec![0.0; dim];
            let mut b = vec![0.0; dim];
            a[p] = 1.0;
            b[q] = 1.0;
            let v = cd_mul(&a, &b, gammas);
            let k = v
                .iter()
                .position(|&x| x != 0.0)
                .context("a basis product vanishes")?;
            if k != p ^ q {
                bail!("basis product e{p} e{q} lands on e{k}, not on the XOR index");
            }
            table[p * dim + q] = v[k];
        }
    }
    Ok(table)
}

/// A sign table of dimension `DIM` that reads the low bits of both indices through a smaller table.
fn embed_signs(small: &[f64], dim: usize) -> Vec<f64> {
    let mut out = vec![0.0; DIM * DIM];
    for p in 0..DIM {
        for q in 0..DIM {
            out[p * DIM + q] = small[(p & (dim - 1)) * dim + (q & (dim - 1))];
        }
    }
    out
}

/// Signs of the Clifford algebra with generators of square `square` on five generators.
fn clifford_signs(square: f64) -> Vec<f64> {
    let mut out = vec![0.0; DIM * DIM];
    for p in 0..DIM {
        for q in 0..DIM {
            let swaps: u32 = (0..5)
                .filter(|j| q >> j & 1 == 1)
                .map(|j| (p >> (j + 1)).count_ones())
                .sum();
            let sign = if swaps.is_multiple_of(2) { 1.0 } else { -1.0 };
            out[p * DIM + q] = sign * square.powi((p & q).count_ones() as i32);
        }
    }
    out
}

/// Random signs with a unit at e0 and squares of -1 on the other basis vectors.
fn random_unital_signs(rng: &mut ChaCha8Rng) -> Vec<f64> {
    let mut s: Vec<f64> = (0..DIM * DIM)
        .map(|_| if rng.random::<bool>() { 1.0 } else { -1.0 })
        .collect();
    for k in 0..DIM {
        s[k] = 1.0;
        s[k * DIM] = 1.0;
    }
    for k in 1..DIM {
        s[k * DIM + k] = -1.0;
    }
    s
}

/// A Gaussian structure tensor of variance 1/32, with e0 acting as the unit when `unital`.
fn dense_tensor(rng: &mut ChaCha8Rng, unital: bool) -> Vec<f64> {
    let scale = 1.0 / (DIM as f64).sqrt();
    let mut t: Vec<f64> = (0..DIM * DIM * DIM)
        .map(|_| {
            let x: f64 = StandardNormal.sample(rng);
            x * scale
        })
        .collect();
    if unital {
        for j in 0..DIM {
            for k in 0..DIM {
                let delta = if j == k { 1.0 } else { 0.0 };
                t[j * DIM + k] = delta;
                t[(j * DIM) * DIM + k] = delta;
            }
        }
    }
    t
}

/// Names and products of the algebras of the substitution test, the Cayley-Dickson pathion first.
fn algebras(seeds: &Seeds) -> Result<Vec<(String, Algebra)>> {
    let signs = |dim: usize, gammas: &[f64]| -> Result<Vec<f64>> { cd_sign_table(dim, gammas) };
    let mut out: Vec<(String, Algebra)> = vec![
        ("pathion_CD32".into(), Algebra::Xor(signs(32, &[-1.0; 5])?)),
        (
            "sedenion_x_Z2".into(),
            Algebra::Xor(embed_signs(&signs(16, &[-1.0; 4])?, 16)),
        ),
        (
            "octonion_x_Z2^2".into(),
            Algebra::Xor(embed_signs(&signs(8, &[-1.0; 3])?, 8)),
        ),
        (
            "quaternion_x_Z2^3".into(),
            Algebra::Xor(embed_signs(&signs(4, &[-1.0; 2])?, 4)),
        ),
        (
            "group_algebra_Z2^5".into(),
            Algebra::Xor(vec![1.0; DIM * DIM]),
        ),
        (
            "clifford_Cl(0,5)".into(),
            Algebra::Xor(clifford_signs(-1.0)),
        ),
        ("clifford_Cl(5,0)".into(), Algebra::Xor(clifford_signs(1.0))),
        (
            "split_CD32_top_level".into(),
            Algebra::Xor(signs(32, &[-1.0, -1.0, -1.0, -1.0, 1.0])?),
        ),
        (
            "split_CD32_all_levels".into(),
            Algebra::Xor(signs(32, &[1.0; 5])?),
        ),
    ];
    let mut rng = stream(seeds.signs, 0, 0);
    for k in 0..4 {
        out.push((
            format!("random_unital_signs_{k}"),
            Algebra::Xor(random_unital_signs(&mut rng)),
        ));
    }
    let mut rng = stream(seeds.dense, 0, 0);
    out.push((
        "dense_random_unital".into(),
        Algebra::Dense(dense_tensor(&mut rng, true)),
    ));
    out.push((
        "dense_random".into(),
        Algebra::Dense(dense_tensor(&mut rng, false)),
    ));
    Ok(out)
}

/// Names of the algebras whose order decomposition is reported.
const ORDERED: [&str; 6] = [
    "pathion_CD32",
    "sedenion_x_Z2",
    "octonion_x_Z2^2",
    "random_unital_signs_0",
    "dense_random_unital",
    "dense_random",
];

/// Mean norms of four identities on random unit triples: the associator, the alternative
/// law `[a,a,b]`, the flexible law `[a,b,a]` and the power `[a,a,a]`.
fn algebra_properties(alg: &Algebra, seed: u64) -> [f64; 4] {
    let mut rng = stream(seed, 1, 1);
    let unit = |rng: &mut ChaCha8Rng| -> Vector {
        let mut v = [0.0; DIM];
        for x in &mut v {
            *x = StandardNormal.sample(rng);
        }
        let n = vnorm(&v);
        v.iter_mut().for_each(|x| *x /= n);
        v
    };
    let mut sums = [0.0; 4];
    for _ in 0..PROPERTY_TRIPLES {
        let (a, b, c) = (unit(&mut rng), unit(&mut rng), unit(&mut rng));
        sums[0] += vnorm(&alg.associator(&a, &b, &c));
        sums[1] += vnorm(&alg.associator(&a, &a, &b));
        sums[2] += vnorm(&alg.associator(&a, &b, &a));
        sums[3] += vnorm(&alg.associator(&a, &a, &a));
    }
    sums.map(|s| s / PROPERTY_TRIPLES as f64)
}

/// The 19 populations of a cell in a 32-vector divided by their norm; the
/// slots 19..32 stay zero (identity slot map).
fn unit32(pops: &[f64]) -> Vector {
    let mut v = [0.0; DIM];
    v[..Q].copy_from_slice(&pops[..Q]);
    let n = vnorm(&v);
    if n > NORM_FLOOR {
        v.iter_mut().for_each(|x| *x /= n);
    }
    v
}

/// Associator, Gram volume and step difference of the cell triple
/// (p2 - l1 - l0, p2 - l1, p2) built from the end state and the last two increments.
fn triple_scores(alg: &Algebra, end: &[f64], l0: &[f64], l1: &[f64]) -> [f64; 3] {
    let mut p1 = [0.0; Q];
    let mut p0 = [0.0; Q];
    for k in 0..Q {
        p1[k] = end[k] - l1[k];
        p0[k] = p1[k] - l0[k];
    }
    let (u0, u1, u2) = (unit32(&p0), unit32(&p1), unit32(end));
    [
        vnorm(&alg.associator(&u0, &u1, &u2)),
        gram_volume(&u0, &u1, &u2),
        distance(&u2, &u1),
    ]
}

// -------------------------------------------------------------------- seeds

/// Seed values and where they come from.
struct Seeds {
    labels: u64,
    block: u64,
    shuffle: u64,
    phase: u64,
    signs: u64,
    dense: u64,
    triples: u64,
    orbit_direct: u64,
    records: Vec<Value>,
}

fn read_seeds(path: &Path) -> Result<Seeds> {
    let text = std::fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;
    let draw: Value =
        serde_json::from_str(&text).with_context(|| format!("parse {}", path.display()))?;
    let values = draw["values"]
        .as_array()
        .context("the QRNG draw holds no values array")?;
    let name = path
        .file_name()
        .map_or_else(String::new, |n| n.to_string_lossy().into_owned());
    let mut records = Vec::new();
    let mut take = |use_of: &str, index: usize| -> Result<u64> {
        let value = values
            .get(index)
            .and_then(Value::as_u64)
            .with_context(|| format!("QRNG index {index} is not an unsigned value"))?;
        records.push(json!({"use": use_of, "draw": name, "index": index, "value": value}));
        Ok(value)
    };
    let labels = take("label permutations", SEED_LABELS)?;
    let block = take("block-permuted increments", SEED_BLOCK)?;
    let shuffle = take("drawn increments", SEED_SHUFFLE)?;
    let phase = take("phase-randomized increments", SEED_PHASE)?;
    let signs = take("random sign cocycles", SEED_SIGNS)?;
    let dense = take("dense random products", SEED_DENSE)?;
    let triples = take("random unit triples of the property table", SEED_TRIPLES)?;
    let orbit_direct = take("direct relabeling of whole orbits", SEED_ORBIT_DIRECT)?;
    Ok(Seeds {
        labels,
        block,
        shuffle,
        phase,
        signs,
        dense,
        triples,
        orbit_direct,
        records,
    })
}

// ----------------------------------------------------------------- symmetry

/// A lattice symmetry: a cell map and the direction map that goes with it.
struct Generator {
    name: &'static str,
    cell: Vec<usize>,
    dir: [usize; Q],
}

/// The symmetries of the double shear layer with the transverse sine
/// perturbation: `a` is the reflection x -> NX/2 - x with the shift y -> y + NY/2 (the
/// shear changes sign under the shift and the reflection restores it),
/// `b` is the shift x -> x + NX/2 with the reflection y -> -y (the transverse
/// velocity changes sign under both), and the z layers are shifted and
/// reflected. Each acts on the populations through the velocity reflection that
/// accompanies its spatial reflection.
fn generators(lattice: &D3Q19Lattice) -> Result<Vec<Generator>> {
    type Map = fn(usize, usize, usize) -> (usize, usize, usize);
    let specs: [(&'static str, Map, [i32; 3]); 4] = [
        (
            "shear_inversion",
            |x, y, z| ((NX / 2 + NX - x) % NX, (y + NY / 2) % NY, z),
            [-1, 1, 1],
        ),
        (
            "transverse_reflection",
            |x, y, z| ((x + NX / 2) % NX, (NY - y) % NY, z),
            [1, -1, 1],
        ),
        ("z_shift", |x, y, z| (x, y, (z + 1) % NZ), [1, 1, 1]),
        ("z_reflection", |x, y, z| (x, y, (NZ - z) % NZ), [1, 1, -1]),
    ];
    let mut out = Vec::new();
    for (name, map, flip) in specs {
        let mut cell = vec![0; CELLS];
        for z in 0..NZ {
            for y in 0..NY {
                for x in 0..NX {
                    let (nx, ny, nz) = map(x, y, z);
                    cell[z * NX * NY + y * NX + x] = nz * NX * NY + ny * NX + nx;
                }
            }
        }
        let mut dir = [0; Q];
        for (d, slot) in dir.iter_mut().enumerate() {
            let v = lattice.velocities[d];
            let target = [flip[0] * v[0], flip[1] * v[1], flip[2] * v[2]];
            *slot = lattice
                .velocities
                .iter()
                .position(|&w| w == target)
                .context("a velocity reflection leaves the D3Q19 set")?;
        }
        out.push(Generator { name, cell, dir });
    }
    Ok(out)
}

/// Orbits of the cells under the generators that hold on a state.
struct Orbits {
    id: Vec<usize>,
    count: usize,
    /// Orbit size -> number of orbits of that size.
    sizes: BTreeMap<usize, usize>,
    /// Per generator: name, largest relative deviation, cells that obey it.
    generators: Vec<(&'static str, f64, usize)>,
}

fn find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

/// Orbits of `state` (cell-major populations): cells are linked by a generator when the
/// image population of every direction agrees to `tolerance` of the largest population.
fn orbits_of(state: &[f64], gens: &[Generator], tolerance: f64) -> Orbits {
    let scale = state
        .iter()
        .fold(0.0_f64, |m, &x| m.max(x.abs()))
        .max(f64::MIN_POSITIVE);
    let mut parent: Vec<usize> = (0..CELLS).collect();
    let mut report = Vec::new();
    for g in gens {
        let mut worst = 0.0_f64;
        let mut obey = 0;
        for cell in 0..CELLS {
            let image = g.cell[cell];
            let dev = (0..Q)
                .map(|d| (state[image * Q + g.dir[d]] - state[cell * Q + d]).abs())
                .fold(0.0, f64::max)
                / scale;
            worst = worst.max(dev);
            if dev <= tolerance {
                obey += 1;
                let (a, b) = (find(&mut parent, cell), find(&mut parent, image));
                if a != b {
                    parent[a.max(b)] = a.min(b);
                }
            }
        }
        report.push((g.name, worst, obey));
    }
    let mut label = vec![usize::MAX; CELLS];
    let mut id = vec![0; CELLS];
    let mut size: Vec<usize> = Vec::new();
    for (cell, slot) in id.iter_mut().enumerate() {
        let root = find(&mut parent, cell);
        if label[root] == usize::MAX {
            label[root] = size.len();
            size.push(0);
        }
        *slot = label[root];
        size[label[root]] += 1;
    }
    let mut sizes = BTreeMap::new();
    for &s in &size {
        *sizes.entry(s).or_insert(0) += 1;
    }
    Orbits {
        id,
        count: size.len(),
        sizes,
        generators: report,
    }
}

/// Relative difference of each score between a cell and its image under `g`, over the cells
/// whose populations obey `g` to `tolerance`: median and maximum of
/// `|s - s'| / max(|s|, |s'|)`. A score that ignores the order of the 19 populations (the
/// Gram volume, the step difference, the Mach number, the smallest population share and
/// |c - a|) reads equal values at the two cells; the associator reads the populations in the
/// slots of the identity slot map, and the velocity reflection permutes those slots.
fn score_image_deviation(
    state: &[f64],
    scores: &[Vec<f64>],
    g: &Generator,
    tolerance: f64,
) -> Value {
    let scale = state
        .iter()
        .fold(0.0_f64, |m, &x| m.max(x.abs()))
        .max(f64::MIN_POSITIVE);
    let obey: Vec<usize> = (0..CELLS)
        .filter(|&cell| {
            let image = g.cell[cell];
            (0..Q).all(|d| {
                (state[image * Q + g.dir[d]] - state[cell * Q + d]).abs() / scale <= tolerance
            })
        })
        .collect();
    let by_score = scores.iter().enumerate().map(|(k, col)| {
        let rel: Vec<f64> = obey
            .iter()
            .map(|&c| {
                let (a, b) = (col[c], col[g.cell[c]]);
                let top = a.abs().max(b.abs());
                if top == 0.0 { 0.0 } else { (a - b).abs() / top }
            })
            .collect();
        (
            SCORE_NAMES[k].to_string(),
            json!({"median": median(&rel), "max": rel.iter().copied().fold(0.0, f64::max)}),
        )
    });
    json!({
        "generator": g.name,
        "cells_compared": obey.len(),
        "by_score": by_score.collect::<serde_json::Map<_, _>>(),
    })
}

fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

// --------------------------------------------------------------------- runs

/// One re-simulated run: the 64 states that end at the anchor, the labels,
/// the quartiles and the six scores of the anchor.
struct NullRun {
    key: ConfigKey,
    first: usize,
    anchor: usize,
    states: Vec<f64>,
    labels: Vec<bool>,
    quartile: Vec<usize>,
    scores: Vec<Vec<f64>>,
}

impl NullRun {
    fn state(&self, t: usize) -> &[f64] {
        &self.states[t * CELLS * Q..(t + 1) * CELLS * Q]
    }
}

fn simulate(lattice: &D3Q19Lattice, cfg: Config, eps: f64, first: usize) -> Result<NullRun> {
    if first < FORECAST_LEAD + HISTORY {
        bail!("first violating step {first} leaves fewer than {HISTORY} states before the anchor");
    }
    let anchor = first - FORECAST_LEAD;
    let mut solver = fresh_solver(cfg, eps);
    let mut ring: VecDeque<Vec<f64>> = VecDeque::with_capacity(HISTORY);
    let mut first_bad: Vec<Option<usize>> = vec![None; CELLS];
    for step in 0..=anchor + FORECAST_WINDOW {
        if step > 0 {
            let _ = solver.phase1_collision();
            let _ = solver.phase2_streaming();
        }
        if step <= anchor && violation_in(&solver).is_some() {
            bail!(
                "tau {} U0 {} delta {}: a bad population at step {step}, before anchor {anchor}",
                cfg.tau,
                cfg.u0,
                cfg.delta
            );
        }
        if step <= anchor && step + HISTORY > anchor {
            let mut buffer = if ring.len() == HISTORY {
                ring.pop_front().unwrap_or_default()
            } else {
                Vec::with_capacity(CELLS * Q)
            };
            snapshot_into(&solver, &mut buffer);
            ring.push_back(buffer);
        }
        if step > anchor {
            mark_first_bad(&solver, &mut first_bad, step);
        }
    }
    let mut states = Vec::with_capacity(HISTORY * CELLS * Q);
    for s in &ring {
        states.extend_from_slice(s);
    }
    let base = cell_scores(
        lattice,
        &states[(HISTORY - 3) * CELLS * Q..(HISTORY - 2) * CELLS * Q],
        &states[(HISTORY - 2) * CELLS * Q..(HISTORY - 1) * CELLS * Q],
        &states[(HISTORY - 1) * CELLS * Q..],
    );
    let two_step: Vec<f64> = (0..CELLS)
        .into_par_iter()
        .map(|cell| {
            let a = unit_vector(
                &states[(HISTORY - 3) * CELLS * Q..(HISTORY - 2) * CELLS * Q],
                cell,
            );
            let c = unit_vector(&states[(HISTORY - 1) * CELLS * Q..], cell);
            distance(&c, &a)
        })
        .collect();
    let quartile = population_quartiles(&base.min_population_share);
    Ok(NullRun {
        key: ConfigKey {
            tau: cfg.tau,
            u0: cfg.u0,
            delta: cfg.delta,
        },
        first,
        anchor,
        states,
        labels: first_bad.iter().map(Option::is_some).collect(),
        quartile,
        scores: vec![
            base.associator,
            base.gram_volume,
            base.step_difference,
            base.mach,
            base.min_population_share,
            two_step,
        ],
    })
}

/// Configurations to run: the scored ones, or with `heldout` the kept scan rows
/// that no score file lists, each with its first violating step.
fn collect_configs(args: &NullArgs) -> Result<Vec<(Config, f64, usize)>> {
    let mut outputs = Vec::new();
    for path in &args.json {
        let text =
            std::fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;
        let out: Output =
            serde_json::from_str(&text).with_context(|| format!("parse {}", path.display()))?;
        outputs.push(out);
    }
    let same = |a: &Config, b: &Config| a.tau == b.tau && a.u0 == b.u0 && a.delta == b.delta;
    let scored: Vec<Config> = outputs
        .iter()
        .flat_map(|o| o.scores.iter())
        .map(|c| Config {
            tau: c.tau,
            u0: c.u0,
            delta: c.delta,
        })
        .collect();
    let mut wanted: Vec<(Config, f64, usize)> = Vec::new();
    for out in &outputs {
        if args.heldout {
            for row in out.scan.iter().filter(|r| r.kept) {
                let cfg = Config {
                    tau: row.tau,
                    u0: row.u0,
                    delta: row.delta,
                };
                let first = row
                    .first_violation_step
                    .context("a kept row without a violation")?;
                if !scored.iter().any(|s| same(s, &cfg))
                    && !wanted.iter().any(|(w, _, _)| same(w, &cfg))
                {
                    wanted.push((cfg, out.eps, first));
                }
            }
        } else {
            for c in &out.scores {
                let cfg = Config {
                    tau: c.tau,
                    u0: c.u0,
                    delta: c.delta,
                };
                if !wanted.iter().any(|(w, _, _)| same(w, &cfg)) {
                    wanted.push((cfg, out.eps, c.first_violation_step));
                }
            }
        }
    }
    if wanted.is_empty() {
        bail!("the inputs hold no configuration to run");
    }
    Ok(wanted)
}

// -------------------------------------------------------------------- nulls

/// A (run, quartile) pair with enough positives, as indices into a run.
struct PairSel {
    quartile: usize,
    cells: Vec<usize>,
    labels: Vec<bool>,
}

fn select(values: &[f64], cells: &[usize]) -> Vec<f64> {
    cells.iter().map(|&c| values[c]).collect()
}

/// The exchangeable-label null of one level for one pair.
struct LevelNull {
    positives: usize,
    negatives: usize,
    p_above_bound: f64,
    mean: f64,
    threshold: f64,
    /// Per score: the share of null areas at least the observed oriented area, with the observed draw counted.
    p_ge: [f64; 6],
}

fn level_null(
    positives: usize,
    negatives: usize,
    observed: &[f64; 6],
    draws: usize,
    rng: &mut ChaCha8Rng,
) -> LevelNull {
    if positives == 0 || negatives == 0 || draws == 0 {
        return LevelNull {
            positives,
            negatives,
            p_above_bound: f64::NAN,
            mean: f64::NAN,
            threshold: f64::NAN,
            p_ge: [f64::NAN; 6],
        };
    }
    let mut null = oriented_null(positives, positives + negatives, draws, rng);
    let p_above_bound = null.iter().filter(|&&a| a > P13C_BOUND).count() as f64 / draws as f64;
    let mean = null.iter().sum::<f64>() / draws as f64;
    let mut p_ge = [f64::NAN; 6];
    for (slot, &obs) in p_ge.iter_mut().zip(observed) {
        let at_least = null.iter().filter(|&&a| a >= obs - 1e-12).count();
        *slot = (at_least + 1) as f64 / (draws + 1) as f64;
    }
    null.sort_by(f64::total_cmp);
    LevelNull {
        positives,
        negatives,
        p_above_bound,
        mean,
        threshold: quantile(&null, P13D_QUANTILE),
        p_ge,
    }
}

/// Cell-level exchangeable units of one pair: the cells of the pair grouped by symmetry
/// orbit, each unit with one label and the sum of its cells' mean ranks per score.
struct DirectUnits {
    size: Vec<usize>,
    label: Vec<bool>,
    rank_sum: Vec<[f64; 6]>,
    /// Units of equal size, the strata inside which labels are exchanged.
    strata: Vec<Vec<usize>>,
    positive_cells: usize,
    negative_cells: usize,
}

/// Groups `cells` by `orbit_of`; fails when a unit holds both labels or a score is not finite.
fn direct_units(
    orbit_of: &[usize],
    cells: &[usize],
    labels: &[bool],
    scores: &[Vec<f64>],
) -> std::result::Result<DirectUnits, String> {
    let values: Vec<Vec<f64>> = scores.iter().map(|s| select(s, cells)).collect();
    if values.iter().flatten().any(|v| !v.is_finite()) {
        return Err("a score of the pair is not finite".to_string());
    }
    let ranks: Vec<Vec<f64>> = values.iter().map(|v| mean_ranks(v)).collect();
    let mut slot: BTreeMap<usize, usize> = BTreeMap::new();
    let mut size = Vec::new();
    let mut label = Vec::new();
    let mut rank_sum: Vec<[f64; 6]> = Vec::new();
    for (i, &cell) in cells.iter().enumerate() {
        let u = *slot.entry(orbit_of[cell]).or_insert_with(|| {
            size.push(0);
            label.push(labels[i]);
            rank_sum.push([0.0; 6]);
            size.len() - 1
        });
        if label[u] != labels[i] {
            return Err("an orbit of the pair holds both labels".to_string());
        }
        size[u] += 1;
        for k in 0..6 {
            rank_sum[u][k] += ranks[k][i];
        }
    }
    let mut by_size: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for (u, &s) in size.iter().enumerate() {
        by_size.entry(s).or_default().push(u);
    }
    let positive_cells = (0..size.len()).filter(|&u| label[u]).map(|u| size[u]).sum();
    Ok(DirectUnits {
        negative_cells: cells.len() - positive_cells,
        size,
        label,
        rank_sum,
        strata: by_size.into_values().collect(),
        positive_cells,
    })
}

/// Rank-sum area of the units flagged positive, for every score.
fn direct_areas(units: &DirectUnits, positive: &[bool]) -> [f64; 6] {
    let mut sums = [0.0; 6];
    for u in (0..positive.len()).filter(|&u| positive[u]) {
        for (s, r) in sums.iter_mut().zip(&units.rank_sum[u]) {
            *s += r;
        }
    }
    let (n1, n0) = (units.positive_cells as f64, units.negative_cells as f64);
    sums.map(|s| (s - n1 * (n1 + 1.0) / 2.0) / (n1 * n0))
}

/// The null of the cell-level oriented areas of one pair under relabeling of whole orbits:
/// labels are exchanged among the units of one size, so the number of positive cells stays
/// fixed, and the area of every draw is taken from the actual scores of the cells.
struct DirectNull {
    units: usize,
    positive_units: usize,
    draws: usize,
    /// Per score: 0.95 quantile of the oriented null, its value on each half of the draws,
    /// the mean, the share above the P13c bound and the share at least the observed area.
    threshold: [f64; 6],
    threshold_halves: [[f64; 6]; 2],
    mean: [f64; 6],
    p_above_bound: [f64; 6],
    p_ge: [f64; 6],
    /// Largest difference between the unit areas of the identity labeling and the observed raw areas.
    identity_difference: f64,
}

fn direct_null(
    units: &DirectUnits,
    raw: &[f64; 6],
    draws: usize,
    seed: u64,
    run: u64,
    pair: u64,
) -> std::result::Result<DirectNull, String> {
    let identity = direct_areas(units, &units.label);
    let identity_difference = identity
        .iter()
        .zip(raw)
        .map(|(a, b)| (a - b).abs())
        .fold(0.0, f64::max);
    if identity_difference > 1e-9 {
        return Err(format!(
            "the unit areas differ from the cell areas by {identity_difference:e}"
        ));
    }
    if units.positive_cells == 0 || units.negative_cells == 0 || draws == 0 {
        return Err("a class of the pair is empty".to_string());
    }
    let positive_per_stratum: Vec<usize> = units
        .strata
        .iter()
        .map(|s| s.iter().filter(|&&u| units.label[u]).count())
        .collect();
    let chunks = draws.div_ceil(DIRECT_CHUNK);
    let areas: Vec<[f64; 6]> = (0..chunks)
        .into_par_iter()
        .flat_map_iter(|c| {
            let mut rng = stream(seed, run, pair * 1000 + c as u64);
            let count = DIRECT_CHUNK.min(draws - c * DIRECT_CHUNK);
            let mut flag = vec![false; units.size.len()];
            let mut order: Vec<Vec<usize>> = units.strata.clone();
            (0..count)
                .map(|_| {
                    flag.iter_mut().for_each(|f| *f = false);
                    for (stratum, &npos) in order.iter_mut().zip(&positive_per_stratum) {
                        for k in 0..npos.min(stratum.len()) {
                            let j = rng.random_range(k..stratum.len());
                            stratum.swap(k, j);
                            flag[stratum[k]] = true;
                        }
                    }
                    direct_areas(units, &flag).map(|a| a.max(1.0 - a))
                })
                .collect::<Vec<_>>()
        })
        .collect();
    let observed = raw.map(oriented);
    let column = |k: usize, from: usize, to: usize| -> Vec<f64> {
        let mut v: Vec<f64> = areas[from..to].iter().map(|a| a[k]).collect();
        v.sort_by(f64::total_cmp);
        v
    };
    let half = areas.len() / 2;
    let mut out = DirectNull {
        units: units.size.len(),
        positive_units: units.label.iter().filter(|&&l| l).count(),
        draws: areas.len(),
        threshold: [f64::NAN; 6],
        threshold_halves: [[f64::NAN; 6]; 2],
        mean: [f64::NAN; 6],
        p_above_bound: [f64::NAN; 6],
        p_ge: [f64::NAN; 6],
        identity_difference,
    };
    for (k, &obs) in observed.iter().enumerate() {
        let all = column(k, 0, areas.len());
        out.threshold[k] = quantile(&all, P13D_QUANTILE);
        out.threshold_halves[0][k] = quantile(&column(k, 0, half), P13D_QUANTILE);
        out.threshold_halves[1][k] = quantile(&column(k, half, areas.len()), P13D_QUANTILE);
        out.mean[k] = all.iter().sum::<f64>() / all.len() as f64;
        out.p_above_bound[k] =
            all.iter().filter(|&&a| a > P13C_BOUND).count() as f64 / all.len() as f64;
        let at_least = all.iter().filter(|&&a| a >= obs - 1e-12).count();
        out.p_ge[k] = (at_least + 1) as f64 / (all.len() + 1) as f64;
    }
    Ok(out)
}

/// Shifts (dy, dx) of the torus null in the order of the nulls' record: y outer, x inner, the identity left out.
fn torus_shifts() -> Vec<(usize, usize)> {
    let mut out = Vec::with_capacity(NX * NY - 1);
    for dy in 0..NY {
        for dx in 0..NX {
            if (dy, dx) != (0, 0) {
                out.push((dy, dx));
            }
        }
    }
    out
}

/// Oriented ROC area of the z = 0 score field translated by each shift,
/// against the fixed labels of the cells in `cells0`.
fn torus_null(
    field0: &[f64],
    cells0: &[usize],
    labels0: &[bool],
    shifts: &[(usize, usize)],
) -> Vec<f64> {
    shifts
        .par_iter()
        .map(|&(dy, dx)| {
            let values: Vec<f64> = cells0
                .iter()
                .map(|&c| field0[((c / NX + dy) % NY) * NX + (c % NX + dx) % NX])
                .collect();
            oriented(auc(&values, labels0))
        })
        .collect()
}

/// Random order of the blocks of the increment series.
fn block_order(rng: &mut ChaCha8Rng) -> Vec<usize> {
    let mut blocks: Vec<usize> = (0..INCREMENTS / BLOCK).collect();
    for k in (1..blocks.len()).rev() {
        blocks.swap(k, rng.random_range(0..=k));
    }
    blocks
}

/// Two distinct increment indices, the first two of a random permutation.
fn drawn_pair(rng: &mut ChaCha8Rng) -> (usize, usize) {
    let i = rng.random_range(0..INCREMENTS);
    let mut j = rng.random_range(0..INCREMENTS - 1);
    if j >= i {
        j += 1;
    }
    (i, j)
}

/// Surrogate scores of the increment nulls: for each cell, the associator,
/// Gram volume and step difference of `nsur` series per kind, laid out
/// `[kind][score][surrogate]`. Kinds: block permutation, drawn increments,
/// phase randomization. The end state is fixed; the last two increments come from the
/// cell's own 63 increments.
fn increment_surrogates(
    run_index: usize,
    run: &NullRun,
    pathion: &Algebra,
    seeds: &Seeds,
    nsur: usize,
) -> Vec<Vec<f64>> {
    let plan = FftPlanner::<f64>::new().plan_fft_forward(INCREMENTS);
    let bins = INCREMENTS / 2;
    let twiddle: Vec<[Complex<f64>; 2]> = (1..=bins)
        .map(|k| {
            let angle = |s: usize| {
                2.0 * std::f64::consts::PI * (k * (INCREMENTS - 2 + s)) as f64 / INCREMENTS as f64
            };
            [
                Complex::from_polar(1.0, angle(0)),
                Complex::from_polar(1.0, angle(1)),
            ]
        })
        .collect();
    (0..CELLS)
        .into_par_iter()
        .map(|cell| {
            let mut inc = vec![[0.0; Q]; INCREMENTS];
            for (t, row) in inc.iter_mut().enumerate() {
                let (s0, s1) = (run.state(t), run.state(t + 1));
                for (d, x) in row.iter_mut().enumerate() {
                    *x = s1[cell * Q + d] - s0[cell * Q + d];
                }
            }
            let end = &run.state(HISTORY - 1)[cell * Q..(cell + 1) * Q];
            let mut out = vec![0.0; 9 * nsur];
            let mut put = |kind: usize, t: usize, s: [f64; 3]| {
                for (k, v) in s.into_iter().enumerate() {
                    out[(kind * 3 + k) * nsur + t] = v;
                }
            };
            let mut rng = stream(seeds.block, run_index as u64, cell as u64);
            for t in 0..nsur {
                let order = block_order(&mut rng);
                let b = order[order.len() - 1];
                put(
                    0,
                    t,
                    triple_scores(
                        pathion,
                        end,
                        &inc[b * BLOCK + BLOCK - 2],
                        &inc[b * BLOCK + BLOCK - 1],
                    ),
                );
            }
            let mut rng = stream(seeds.shuffle, run_index as u64, cell as u64);
            for t in 0..nsur {
                let (i, j) = drawn_pair(&mut rng);
                put(1, t, triple_scores(pathion, end, &inc[i], &inc[j]));
            }
            let mut spectrum = vec![[Complex::new(0.0, 0.0); 32]; Q];
            let mut buffer = vec![Complex::new(0.0, 0.0); INCREMENTS];
            for (d, bins_of) in spectrum.iter_mut().enumerate() {
                for (t, b) in buffer.iter_mut().enumerate() {
                    *b = Complex::new(inc[t][d], 0.0);
                }
                plan.process(&mut buffer);
                bins_of[..=bins].copy_from_slice(&buffer[..=bins]);
            }
            let mut rng = stream(seeds.phase, run_index as u64, cell as u64);
            for t in 0..nsur {
                let phased: Vec<[Complex<f64>; 2]> = twiddle
                    .iter()
                    .map(|tw| {
                        let phase = Complex::from_polar(
                            1.0,
                            2.0 * std::f64::consts::PI * rng.random::<f64>(),
                        );
                        [phase * tw[0], phase * tw[1]]
                    })
                    .collect();
                let mut last = [[0.0; Q]; 2];
                for (d, bins_of) in spectrum.iter().enumerate() {
                    for (s, slot) in last.iter_mut().enumerate() {
                        slot[d] = phase_sample(bins_of, &phased, s);
                    }
                }
                put(2, t, triple_scores(pathion, end, &last[0], &last[1]));
            }
            out
        })
        .collect()
}

// ------------------------------------------------------- logistic regression

/// Sample of a phase-randomized series at one of its last two steps: the
/// mean plus twice the real part of the phased positive-frequency bins, scaled by the length.
fn phase_sample(bins_of: &[Complex<f64>], phased: &[[Complex<f64>; 2]], s: usize) -> f64 {
    let acc: f64 = (1..=phased.len())
        .map(|k| (bins_of[k] * phased[k - 1][s]).re)
        .sum();
    (bins_of[0].re + 2.0 * acc) / INCREMENTS as f64
}

/// Iterations of the Newton fit of a logistic model.
const LOGIT_ITERATIONS: usize = 200;

/// A Newton fit of a logistic model with an intercept.
struct LogitFit {
    ll: f64,
    /// Linear predictor of each case.
    eta: Vec<f64>,
    /// Fitted coefficients, intercept first; the tests read them.
    #[cfg(test)]
    beta: Vec<f64>,
    /// The classes separate: the likelihood has no finite maximum, so the
    /// coefficients and the likelihood-ratio statistic carry no meaning.
    separated: bool,
}

/// Newton fit of a logistic model with an intercept.
///
/// The maximum of the likelihood is finite exactly when no hyperplane keeps
/// every case of a class on its side. The fit reports `separated` when the
/// linear predictor of an iterate puts every case on the side of its own class
/// (a certificate of complete separation), or when the iteration has not
/// converged after `LOGIT_ITERATIONS` steps (the coefficients of a separated
/// fit grow without bound, and with them the step). A large coefficient alone
/// proves nothing: nearly collinear columns give finite coefficients of
/// either sign and large size.
fn logit_fit(columns: &[&[f64]], y: &[bool]) -> LogitFit {
    let n = y.len();
    let p = columns.len() + 1;
    let x = |i: usize, j: usize| if j == 0 { 1.0 } else { columns[j - 1][i] };
    let mut beta = vec![0.0; p];
    let eta_of = |beta: &[f64]| -> Vec<f64> {
        (0..n)
            .map(|i| {
                (0..p)
                    .map(|j| beta[j] * x(i, j))
                    .sum::<f64>()
                    .clamp(-50.0, 50.0)
            })
            .collect()
    };
    let mut separated = false;
    let mut converged = false;
    for _ in 0..LOGIT_ITERATIONS {
        let eta = eta_of(&beta);
        let mu: Vec<f64> = eta.iter().map(|e| 1.0 / (1.0 + (-e).exp())).collect();
        let mut grad = vec![0.0; p];
        let mut hess = vec![0.0; p * p];
        for i in 0..n {
            let r = f64::from(u8::from(y[i])) - mu[i];
            let w = mu[i] * (1.0 - mu[i]);
            for j in 0..p {
                grad[j] += x(i, j) * r;
        if eta
            .iter()
            .zip(y)
            .all(|(&e, &yy)| if yy { e > 0.0 } else { e < 0.0 })
        {
            separated = true;
            break;
        }
                for k in 0..p {
                    hess[j * p + k] += x(i, j) * x(i, k) * w;
                }
            }
        }
        for j in 0..p {
            hess[j * p + j] += 1e-8;
        }
        let step = solve(&mut hess, &mut grad, p);
        let largest = step.iter().fold(0.0_f64, |m, s| m.max(s.abs()));
        for (b, s) in beta.iter_mut().zip(&step) {
            *b += s;
        }
        if largest < 1e-10 {
            break;
        }
    }
    let eta = eta_of(&beta);
    let ll = eta
        .iter()
        .zip(y)
        .map(|(e, &yy)| {
            converged = true;
            let mu = (1.0 / (1.0 + (-e).exp())).clamp(1e-12, 1.0 - 1e-12);
            if yy { mu.ln() } else { (1.0 - mu).ln() }
        })
    let separated = separated || !converged;
        .sum();
    LogitFit {
        ll,
        eta,
        #[cfg(test)]
        beta,
        separated,
    }
}

/// Solution of `a x = b` by Gaussian elimination with partial pivoting (`a` is `p x p`).
fn solve(a: &mut [f64], b: &mut [f64], p: usize) -> Vec<f64> {
    for col in 0..p {
        let pivot = (col..p)
            .max_by(|&i, &j| a[i * p + col].abs().total_cmp(&a[j * p + col].abs()))
            .unwrap_or(col);
        for k in 0..p {
            a.swap(col * p + k, pivot * p + k);
        }
        b.swap(col, pivot);
        let d = a[col * p + col];
        if d.abs() < 1e-300 {
            continue;
        }
        for row in col + 1..p {
            let f = a[row * p + col] / d;
            for k in col..p {
                a[row * p + k] -= f * a[col * p + k];
            }
            b[row] -= f * b[col];
        }
    }
    let mut x = vec![0.0; p];
    for row in (0..p).rev() {
        let tail: f64 = (row + 1..p).map(|k| a[row * p + k] * x[k]).sum();
        let d = a[row * p + row];
        x[row] = if d.abs() < 1e-300 {
            0.0
        } else {
            (b[row] - tail) / d
        };
    }
    x
}

/// Normal scores of the ranks of `x`.
fn normal_scores(x: &[f64]) -> Vec<f64> {
    let normal = Normal::new(0.0, 1.0).expect("standard normal");
    let n = x.len() as f64;
    mean_ranks(x)
        .into_iter()
        .map(|r| normal.inverse_cdf((r - 0.5) / n))
        .collect()
}

/// Likelihood-ratio statistic, p-value, separation flag and gain in ROC area from
/// adding the first column to the others.
fn likelihood_ratio(columns: &[Vec<f64>], y: &[bool]) -> (f64, f64, bool, f64) {
    let reduced: Vec<&[f64]> = columns[1..].iter().map(Vec::as_slice).collect();
    let full: Vec<&[f64]> = columns.iter().map(Vec::as_slice).collect();
    let reduced_fit = logit_fit(&reduced, y);
    let full_fit = logit_fit(&full, y);
    let stat = (2.0 * (full_fit.ll - reduced_fit.ll)).max(0.0);
    let p = ChiSquared::new(1.0).map_or(f64::NAN, |c| 1.0 - c.cdf(stat));
    (
        stat,
        p,
        reduced_fit.separated || full_fit.separated,
        auc(&full_fit.eta, y) - auc(&reduced_fit.eta, y),
    )
}

// ------------------------------------------------------------ per-run output

/// Logistic likelihood-ratio result of the associator given the product-free scores.
struct LrRow {
    orbits: usize,
    orbit_positives: usize,
    /// Four product-free scores, then five (with |c - a|): (statistic, p, separated, area gain).
    four: (f64, f64, bool, f64),
    five: (f64, f64, bool, f64),
}

struct PairOut {
    run: usize,
    quartile: usize,
    cells: usize,
    positives: usize,
    raw: [f64; 6],
    oriented: [f64; 6],
    /// Cell, z-layer and orbit levels.
    levels: Vec<LevelNull>,
    /// Direct orbit relabeling of the cell-level areas, or why it is unavailable.
    direct: std::result::Result<DirectNull, String>,
    orbit_mixed: usize,
    /// Per score, the oriented area of every shifted field.
    torus: Vec<Vec<f64>>,
    z0_diff: f64,
    spearman_gram: f64,
    spearman_two_step: f64,
    algebra_raw: Vec<f64>,
    algebra_spearman: Vec<f64>,
    /// Raw areas of the first- and second-order terms of the ordered algebras.
    order_raw: Vec<[f64; 2]>,
    /// Kind x score: mean over surrogates of the raw area, minus the observed raw area, in absolute value.
    inc_shift: [[f64; 3]; 3],
    lr: Option<LrRow>,
}

struct RunOut {
    index: usize,
    key: ConfigKey,
    first: usize,
    anchor: usize,
    pairs: Vec<PairOut>,
    retained_auc_diff: Option<f64>,
    kernel_rel_diff: f64,
    symmetry: Value,
    alg_max_norm: Vec<f64>,
    /// Per ordered algebra: median zeroth, first and second order shares of the associator.
    order_share: Vec<[f64; 3]>,
    order_spearman: Vec<f64>,
    /// Kind x score x surrogate: pairs of this run above the bound.
    inc_counts: Vec<Vec<Vec<usize>>>,
}

fn retained_areas(a: &super::ScoreAucs) -> [Option<f64>; 5] {
    [
        a.associator.unoriented_auc,
        a.gram_volume.unoriented_auc,
        a.step_difference.unoriented_auc,
        a.mach.unoriented_auc,
        a.min_population_share.unoriented_auc,
    ]
}

/// Largest difference between the areas of the re-simulated run and the retained forecast record.
fn retained_difference(run: &NullRun, retained: &super::RunForecast) -> Result<f64> {
    if retained.config != run.key || retained.anchor != run.anchor {
        bail!("the retained forecast run differs in configuration or anchor");
    }
    let mut worst = 0.0_f64;
    for q in &retained.quartiles {
        let cells: Vec<usize> = (0..CELLS)
            .filter(|&c| run.quartile[c] == q.quartile)
            .collect();
        let labels: Vec<bool> = cells.iter().map(|&c| run.labels[c]).collect();
        let positives = labels.iter().filter(|&&l| l).count();
        if cells.len() != q.cells || positives != q.positives {
            bail!(
                "quartile {} differs from the retained forecast record in cells or positives",
                q.quartile
            );
        }
        for (k, want) in retained_areas(&q.auc).into_iter().enumerate() {
            let got = auc(&select(&run.scores[k], &cells), &labels);
            match want {
                Some(w) => worst = worst.max((got - w).abs()),
                None if got.is_finite() => {
                    bail!("a retained area is absent where the rerun has one")
                }
                None => {}
            }
        }
    }
    if worst > 1e-12 {
        bail!("the rerun differs from the retained forecast record by {worst:e}");
    }
    Ok(worst)
}

/// Inputs shared by every run.
#[derive(Clone, Copy)]
struct RunContext<'a> {
    algs: &'a [(String, Algebra)],
    gens: &'a [Generator],
    seeds: &'a Seeds,
    args: &'a NullArgs,
    shifts: &'a [(usize, usize)],
}

fn process_run(
    index: usize,
    run: &NullRun,
    retained: Option<&super::RunForecast>,
    ctx: &RunContext,
) -> Result<RunOut> {
    let RunContext {
        algs,
        gens,
        seeds,
        args,
        shifts,
    } = *ctx;
    let retained_auc_diff = retained.map(|r| retained_difference(run, r)).transpose()?;
    let layer = NX * NY;
    let mut selected = Vec::new();
    let mut all_positives = Vec::new();
    for q in 0..QUARTILES {
        let cells: Vec<usize> = (0..CELLS).filter(|&c| run.quartile[c] == q).collect();
        let labels: Vec<bool> = cells.iter().map(|&c| run.labels[c]).collect();
        let positives = labels.iter().filter(|&&l| l).count();
        all_positives.push(positives);
        if positives >= P13C_MIN_POSITIVES && positives < cells.len() {
            selected.push(PairSel {
                quartile: q,
                cells,
                labels,
            });
        }
    }
    let positives_gcd = all_positives.iter().fold(0, |g, &p| gcd(g, p));

    // Orbits of the anchor state and their aggregates.
    let orbits = orbits_of(run.state(HISTORY - 1), gens, SYMMETRY_TOLERANCE);
    let strict_orbits = orbits_of(run.state(HISTORY - 1), gens, SYMMETRY_STRICT_TOLERANCE).count;
    let n_orbits = orbits.count;
    let mut o_count = vec![0usize; n_orbits];
    let mut o_quartile = vec![0.0; n_orbits];
    // A pair's index addresses its random streams: the pairs run from the highest
    // quartile to the lowest.
    selected.reverse();
    let mut o_label = vec![0.0; n_orbits];
    let mut o_score = vec![vec![0.0; n_orbits]; 6];
    for cell in 0..CELLS {
        let o = orbits.id[cell];
        o_count[o] += 1;
        o_quartile[o] += (QUARTILES - 1 - run.quartile[cell]) as f64;
        o_label[o] += f64::from(u8::from(run.labels[cell]));
        for (k, col) in o_score.iter_mut().enumerate() {
            col[o] += run.scores[k][cell];
        }
    }
    for o in 0..n_orbits {
        let c = o_count[o] as f64;
        // An orbit that spans quartiles joins the quartile of the rounded mean score
        // index (ties to the even index), which is the reflection of the population
        // quartile.
        o_quartile[o] = (QUARTILES - 1) as f64 - (o_quartile[o] / c).round_ties_even();
        o_label[o] /= c;
        o_score.iter_mut().for_each(|col| col[o] /= c);
    }
    let mixed = o_label.iter().filter(|&&l| l > 0.0 && l < 1.0).count();
    let symmetry = json!({
        "generators": orbits.generators.iter().map(|(n, dev, cells)| json!({
            "name": n, "max_relative_deviation": dev, "cells_obeying": cells, "cells": CELLS})).collect::<Vec<_>>(),
        "tolerance": SYMMETRY_TOLERANCE,
        "orbits_at_strict_tolerance": strict_orbits,
        "strict_tolerance": SYMMETRY_STRICT_TOLERANCE,
        "orbits": n_orbits,
        "orbit_size_counts": orbits.sizes.iter().map(|(s, c)| (s.to_string(), json!(c))).collect::<serde_json::Map<_, _>>(),
        "orbits_with_mixed_labels": mixed,
        "score_image_deviation": gens.iter().map(|g| score_image_deviation(
            run.state(HISTORY - 1), &run.scores, g, SYMMETRY_TOLERANCE)).collect::<Vec<_>>(),
        "label_and_quartile_agreement": gens.iter().map(|g| json!({
            "name": g.name,
            "cells_with_equal_label_and_quartile_at_the_image": (0..CELLS)
                .filter(|&c| run.labels[c] == run.labels[g.cell[c]] && run.quartile[c] == run.quartile[g.cell[c]])
                .count()})).collect::<Vec<_>>(),
        "quartile_positives": all_positives,
        "positives_gcd": positives_gcd,
        "z_layers_bitwise_identical": (1..NZ).all(|z| run.state(HISTORY - 1)[z * layer * Q..(z + 1) * layer * Q]
            == run.state(HISTORY - 1)[..layer * Q]),
    });

    // Algebra substitution and order decomposition on the observed triple.
    let triples: Vec<[Vector; 3]> = (0..CELLS)
        .into_par_iter()
        .map(|cell| {
            [HISTORY - 3, HISTORY - 2, HISTORY - 1]
                .map(|t| unit32(&run.state(t)[cell * Q..(cell + 1) * Q]))
        })
        .collect();
    let norms: Vec<Vec<f64>> = algs
        .iter()
        .map(|(_, alg)| {
            triples
                .par_iter()
                .map(|t| vnorm(&alg.associator(&t[0], &t[1], &t[2])))
                .collect()
        })
        .collect();
    let kernel_rel_diff = norms[0]
        .iter()
        .zip(&run.scores[0])
        .map(|(a, b)| (a - b).abs() / b.abs().max(1e-300))
        .fold(0.0, f64::max);
    let ordered: Vec<usize> = ORDERED
        .iter()
        .filter_map(|name| algs.iter().position(|(n, _)| n == name))
        .collect();
    let mut order_terms: Vec<[Vec<f64>; 3]> = Vec::new();
    let mut order_share = Vec::new();
    let mut order_spearman = Vec::new();
    for &ai in &ordered {
        let alg = &algs[ai].1;
        let terms: Vec<[f64; 3]> = triples
            .par_iter()
            .map(|t| {
                let d1 = vsub(&t[1], &t[0]);
                let d2 = vsub(&t[2], &t[0]);
                let a = &t[0];
                let t0 = vnorm(&alg.associator(a, a, a));
                let first_a = alg.associator(a, a, &d2);
                let first_b = alg.associator(a, &d1, a);
                let mut first = [0.0; DIM];
                for k in 0..DIM {
                    first[k] = first_a[k] + first_b[k];
                }
                [t0, vnorm(&first), vnorm(&alg.associator(a, &d1, &d2))]
            })
            .collect();
        let col = |j: usize| terms.iter().map(|t| t[j]).collect::<Vec<f64>>();
        let share = |j: usize| {
            let r: Vec<f64> = terms
                .iter()
                .zip(&norms[ai])
                .map(|(t, n)| t[j] / n.max(1e-300))
                .collect();
            median(&r).unwrap_or(f64::NAN)
        };
        order_share.push([share(0), share(1), share(2)]);
        order_spearman.push(spearman(&norms[ai], &col(1)));
        order_terms.push([col(0), col(1), col(2)]);
    }

    // Increment surrogates.
    let nsur = args.surrogates;
    let surrogate = increment_surrogates(index, run, &algs[0].1, seeds, nsur);
    let mut inc_counts = vec![vec![vec![0usize; nsur]; 3]; 3];

    // Pairs.
    let shifts_ref = shifts;
    let mut pairs = Vec::new();
    for (pi, p) in selected.iter().enumerate() {
        let raw: [f64; 6] =
            std::array::from_fn(|k| auc(&select(&run.scores[k], &p.cells), &p.labels));
        let observed: [f64; 6] = raw.map(oriented);
        let n_pos = p.labels.iter().filter(|&&l| l).count();
        let n_cells = p.cells.len();
        let cells0: Vec<usize> = p.cells.iter().copied().filter(|&c| c < layer).collect();
        let labels0: Vec<bool> = cells0.iter().map(|&c| run.labels[c]).collect();
        let pos0 = labels0.iter().filter(|&&l| l).count();
        let members: Vec<usize> = (0..n_orbits)
            .filter(|&o| o_quartile[o] as usize == p.quartile)
            .collect();
        let o_y: Vec<bool> = members.iter().map(|&o| o_label[o] >= 0.5).collect();
        let o_pos = o_y.iter().filter(|&&y| y).count();
        let orbit_mixed = members
            .iter()
            .filter(|&&o| o_label[o] > 0.0 && o_label[o] < 1.0)
            .count();
        let level_inputs = [
            (n_pos, n_cells - n_pos),
            (pos0, labels0.len() - pos0),
            (o_pos, members.len() - o_pos),
        ];
        let levels: Vec<LevelNull> = level_inputs
            .par_iter()
            .enumerate()
            .map(|(lv, &(pos, neg))| {
                let mut rng = stream(seeds.labels, index as u64, (pi * 3 + lv) as u64);
                level_null(pos, neg, &observed, args.label_draws, &mut rng)
            })
            .collect();
        let direct = direct_units(&orbits.id, &p.cells, &p.labels, &run.scores).and_then(|units| {
            direct_null(
                &units,
                &raw,
                args.label_draws,
                seeds.orbit_direct,
                index as u64,
                pi as u64,
            )
        });
        let mut z0_diff = 0.0_f64;
        let torus: Vec<Vec<f64>> = (0..6)
            .map(|k| {
                let field0 = &run.scores[k][..layer];
                let a0 = auc(&select(field0, &cells0), &labels0);
                z0_diff = z0_diff.max((a0 - raw[k]).abs());
                torus_null(field0, &cells0, &labels0, shifts_ref)
            })
            .collect();
        let alg_raw: Vec<f64> = norms
            .iter()
            .map(|n| auc(&select(n, &p.cells), &p.labels))
            .collect();
        let pathion_sel = select(&norms[0], &p.cells);
        let alg_spearman: Vec<f64> = norms
            .iter()
            .map(|n| spearman(&select(n, &p.cells), &pathion_sel))
            .collect();
        let order_raw: Vec<[f64; 2]> = order_terms
            .iter()
            .map(|t| {
                [
                    auc(&select(&t[1], &p.cells), &p.labels),
                    auc(&select(&t[2], &p.cells), &p.labels),
                ]
            })
            .collect();
        let mut inc_shift = [[0.0; 3]; 3];
        for kind in 0..3 {
            for score in 0..3 {
                let mut mean_raw = 0.0;
                for (t, count) in inc_counts[kind][score].iter_mut().enumerate() {
                    let idx = (kind * 3 + score) * nsur + t;
                    let values: Vec<f64> = p.cells.iter().map(|&c| surrogate[c][idx]).collect();
                    let a = auc(&values, &p.labels);
                    mean_raw += a / nsur as f64;
                    if oriented(a) > P13C_BOUND {
                        *count += 1;
                    }
                }
                inc_shift[kind][score] = (mean_raw - raw[score]).abs();
            }
        }
        let lr = if o_pos >= 2 && members.len() - o_pos >= 2 {
            let z: Vec<Vec<f64>> = (0..6)
                .map(|k| normal_scores(&members.iter().map(|&o| o_score[k][o]).collect::<Vec<_>>()))
                .collect();
            let four = likelihood_ratio(&z[..5], &o_y);
            let five = likelihood_ratio(&z, &o_y);
            Some(LrRow {
                orbits: members.len(),
                orbit_positives: o_pos,
                four,
                five,
            })
        } else {
            None
        };
        pairs.push(PairOut {
            run: index,
            quartile: p.quartile,
            cells: n_cells,
            positives: n_pos,
            raw,
            oriented: observed,
            levels,
            direct,
            orbit_mixed,
            torus,
            z0_diff,
            spearman_gram: spearman(
                &select(&run.scores[0], &p.cells),
                &select(&run.scores[1], &p.cells),
            ),
            spearman_two_step: spearman(
                &select(&run.scores[0], &p.cells),
                &select(&run.scores[5], &p.cells),
            ),
            algebra_raw: alg_raw,
            algebra_spearman: alg_spearman,
            order_raw,
            inc_shift,
            lr,
        });
    }
    Ok(RunOut {
        index,
        key: run.key,
        first: run.first,
        anchor: run.anchor,
        pairs,
        retained_auc_diff,
        kernel_rel_diff,
        symmetry,
        alg_max_norm: norms
            .iter()
            .map(|n| n.iter().fold(0.0_f64, |m, &x| m.max(x)))
            .collect(),
        order_share,
        order_spearman,
        inc_counts,
    })
}

// ----------------------------------------------------------------- assembly

fn per_score(f: &dyn Fn(usize) -> Value) -> Value {
    Value::Object(
        SCORE_NAMES
            .iter()
            .enumerate()
            .map(|(k, n)| ((*n).to_string(), f(k)))
            .collect(),
    )
}

fn count_where<T>(items: &[T], f: impl Fn(&T) -> bool) -> usize {
    items.iter().filter(|x| f(x)).count()
}

fn max_of(values: impl IntoIterator<Item = f64>) -> f64 {
    values.into_iter().fold(f64::NEG_INFINITY, f64::max)
}

fn sha256_hex(path: &Path) -> Result<String> {
    let bytes = std::fs::read(path).with_context(|| format!("read {}", path.display()))?;
    Ok(Sha256::digest(&bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect())
}

/// Tail probability `P(count >= observed)` of a Poisson-binomial law.
fn tail(law: &[f64], observed: usize) -> f64 {
    law.iter().skip(observed).sum()
}

fn label_section(pairs: &[&PairOut]) -> Value {
    let levels = ["cell", "z_layer", "orbit"];
    let mut out = serde_json::Map::new();
    for (lv, name) in levels.iter().enumerate() {
        let p_above: Vec<f64> = pairs.iter().map(|p| p.levels[lv].p_above_bound).collect();
        let law = poisson_binomial(&p_above);
        let body = per_score(&|k| {
            let observed = count_where(pairs, |p| p.oriented[k] > P13C_BOUND);
            let p_ge: Vec<f64> = pairs.iter().map(|p| p.levels[lv].p_ge[k]).collect();
            json!({
                "observed_count_above_bound": observed,
                "p_count_at_least_observed": tail(&law, observed),
                "pairs_bh_q_below_0_05": count_below(&benjamini_hochberg(&p_ge), 0.05),
                "pairs_p_below_0_05": count_below(&p_ge, 0.05),
                "p_at_least_observed_by_pair": p_ge,
            })
        });
        out.insert(
            (*name).to_string(),
            json!({
                "expected_count_above_bound": p_above.iter().sum::<f64>(),
                "p_count_at_least_8": tail(&law, 8),
                "mean_null_oriented_area": pairs.iter().map(|p| p.levels[lv].mean).sum::<f64>() / pairs.len() as f64,
                "units_by_pair": pairs.iter().map(|p| json!([p.levels[lv].positives, p.levels[lv].negatives])).collect::<Vec<_>>(),
                "p_above_bound_by_pair": p_above,
                "by_score": body,
            }),
        );
    }
    Value::Object(out)
}

fn torus_section(pairs: &[&PairOut]) -> Value {
    let n = pairs[0].torus[0].len();
    let xonly = NX - 1;
    let denominator = |m: usize| (m + 1) as f64;
    let mut pair_p = Vec::new();
    let mut count_p = Vec::new();
    let rows: Vec<Value> = (0..SCORE_NAMES.len())
        .map(|k| {
        let observed = count_where(pairs, |p| p.oriented[k] > P13C_BOUND);
        let counts: Vec<usize> = (0..n)
            .map(|s| count_where(pairs, |p| p.torus[k][s] > P13C_BOUND))
            .collect();
        let at_least = |m: usize| counts[..m].iter().filter(|&&c| c >= observed).count();
        let p_of = |m: usize| -> Vec<f64> {
            pairs
                .iter()
                .map(|p| {
                    ((0..m).filter(|&s| p.torus[k][s] >= p.oriented[k] - 1e-12).count() + 1) as f64 / denominator(m)
                })
                .collect()
        };
        let (all_p, x_p) = (p_of(n), p_of(xonly));
        let mut sorted: Vec<f64> = counts.iter().map(|&c| c as f64).collect();
        sorted.sort_by(f64::total_cmp);
        let null_mean_area = pairs.iter().flat_map(|p| p.torus[k].iter()).sum::<f64>() / (n * pairs.len()) as f64;
        pair_p.push((all_p.clone(), x_p.clone()));
        let record = json!({
            "observed_count_above_bound": observed,
            "null_mean_count": counts.iter().sum::<usize>() as f64 / n as f64,
            "null_q95_count": quantile(&sorted, 0.95),
            "p_count_at_least_observed": (at_least(n) + 1) as f64 / denominator(n),
            "xshift_null_mean_count": counts[..xonly].iter().sum::<usize>() as f64 / xonly as f64,
            "xshift_p_count_at_least_observed": (at_least(xonly) + 1) as f64 / denominator(xonly),
            "null_mean_oriented_area": null_mean_area,
            "per_pair_p": all_p,
            "per_pair_xshift_p": x_p,
            "observed_oriented_by_pair": pairs.iter().map(|p| p.oriented[k]).collect::<Vec<_>>(),
        });
        count_p.push((
            (at_least(n) + 1) as f64 / denominator(n),
            (at_least(xonly) + 1) as f64 / denominator(xonly),
        ));
        record
        })
        .collect();
    let by_score = Value::Object(
        SCORE_NAMES
            .iter()
            .zip(rows)
            .map(|(n, v)| ((*n).to_string(), v))
            .collect(),
    );
    let mut multiplicity = serde_json::Map::new();
    for (family, scores) in [("five_scores", 5usize), ("six_scores", 6usize)] {
        for (null, pick) in [("torus", 0usize), ("xshift", 1usize)] {
            let p: Vec<f64> = (0..scores)
                .flat_map(|k| {
                    if pick == 0 {
                        pair_p[k].0.clone()
                    } else {
                        pair_p[k].1.clone()
                    }
                })
                .collect();
            let (bh, hm) = (benjamini_hochberg(&p), holm(&p));
            let m = pairs.len();
            let counts_p: Vec<f64> = (0..scores)
                .map(|k| {
                    if pick == 0 {
                        count_p[k].0
                    } else {
                        count_p[k].1
                    }
                })
                .collect();
            let holm_counts = holm(&counts_p);
            multiplicity.insert(
                format!("{null}_{family}"),
                json!({
                    "family_size": p.len(),
                    "by_score": SCORE_NAMES[..scores].iter().enumerate().map(|(k, name)| (
                        (*name).to_string(),
                        json!({
                            "pairs_bh_q_below_0_05": count_below(&bh[k * m..(k + 1) * m], 0.05),
                            "pairs_holm_below_0_05": count_below(&hm[k * m..(k + 1) * m], 0.05),
                            "count_p": counts_p[k],
                            "count_p_holm_over_scores": holm_counts[k],
                        }),
                    )).collect::<serde_json::Map<_, _>>(),
                }),
            );
        }
    }
    json!({
        "shifts": n,
        "xshifts": xonly,
        "z0_matches_full_max_difference": pairs.iter().map(|p| p.z0_diff).fold(0.0, f64::max),
        "by_score": by_score,
        "multiplicity": Value::Object(multiplicity),
    })
}

fn increment_section(outs: &[RunOut], pairs: &[&PairOut], nsur: usize) -> Value {
    let kinds = ["block_permuted", "drawn_increments", "phase_randomized"];
    let scores = ["associator", "gram_volume", "step_difference"];
    let mut out = serde_json::Map::new();
    for (kind, kname) in kinds.iter().enumerate() {
        let body: serde_json::Map<String, Value> = scores
            .iter()
            .enumerate()
            .map(|(s, sname)| {
                let counts: Vec<usize> = (0..nsur)
                    .map(|t| outs.iter().map(|o| o.inc_counts[kind][s][t]).sum())
                    .collect();
                let shifts: Vec<f64> = pairs.iter().map(|p| p.inc_shift[kind][s]).collect();
                (
                    (*sname).to_string(),
                    json!({
                        "observed_count_above_bound": count_where(pairs, |p| p.oriented[s] > P13C_BOUND),
                        "count_above_bound_per_surrogate": counts,
                        "median_surrogate_count": median(&counts.iter().map(|&c| c as f64).collect::<Vec<_>>()),
                        "median_pair_abs_shift_of_raw_area": median(&shifts),
                        "pairs_shift_above_0_1": count_where(&shifts, |&x| x > 0.1),
                    }),
                )
            })
            .collect();
        let differs = count_where(pairs, |p| {
            (p.inc_shift[kind][0] - p.inc_shift[kind][2]).abs() > 0.1
        });
        out.insert(
            (*kname).to_string(),
            json!({"by_score": Value::Object(body), "pairs_associator_shift_differs_from_step_shift_by_more_than_0_1": differs}),
        );
    }
    Value::Object(out)
}

fn algebra_section(
    algs: &[(String, Algebra)],
    outs: &[&RunOut],
    pairs: &[&PairOut],
    seed: u64,
) -> Value {
    let path: Vec<f64> = pairs.iter().map(|p| p.algebra_raw[0]).collect();
    let mut out = serde_json::Map::new();
    for (ai, (name, alg)) in algs.iter().enumerate() {
        let raw: Vec<f64> = pairs.iter().map(|p| p.algebra_raw[ai]).collect();
        let diff: Vec<f64> = raw.iter().zip(&path).map(|(a, b)| (a - b).abs()).collect();
        let props = algebra_properties(alg, seed);
        out.insert(
            name.clone(),
            json!({
                "mean_norm_on_random_unit_triples": {
                    "associator_abc": props[0], "alternative_aab": props[1],
                    "flexible_aba": props[2], "power_aaa": props[3]},
                "max_associator_norm_on_the_runs": max_of(outs.iter().map(|o| o.alg_max_norm[ai])),
                "median_abs_dauc_vs_pathion": median(&diff),
                "pairs_abs_dauc_above_0_05": count_where(&diff, |&d| d > 0.05),
                "pairs_abs_dauc_above_0_1": count_where(&diff, |&d| d > 0.1),
                "median_spearman_with_pathion": median(&pairs.iter().map(|p| p.algebra_spearman[ai]).collect::<Vec<_>>()),
                "oriented_above_bound": count_where(&raw, |&a| oriented(a) > P13C_BOUND),
                "raw_area_by_pair": raw,
            }),
        );
    }
    Value::Object(out)
}

fn order_section(algs: &[(String, Algebra)], outs: &[&RunOut], pairs: &[&PairOut]) -> Value {
    let names: Vec<&str> = ORDERED
        .iter()
        .copied()
        .filter(|n| algs.iter().any(|(a, _)| a == n))
        .collect();
    let mut out = serde_json::Map::new();
    for (i, name) in names.iter().enumerate() {
        let ai = algs.iter().position(|(a, _)| a == name).unwrap_or(0);
        let med = |j: usize| median(&outs.iter().map(|o| o.order_share[i][j]).collect::<Vec<_>>());
        let d_first: Vec<f64> = pairs
            .iter()
            .map(|p| (p.order_raw[i][0] - p.algebra_raw[ai]).abs())
            .collect();
        let d_second: Vec<f64> = pairs
            .iter()
            .map(|p| (p.order_raw[i][1] - p.algebra_raw[ai]).abs())
            .collect();
        out.insert(
            (*name).to_string(),
            json!({
                "zeroth_over_full_median": med(0),
                "first_over_full_median": med(1),
                "second_over_full_median": med(2),
                "spearman_full_first_median": median(&outs.iter().map(|o| o.order_spearman[i]).collect::<Vec<_>>()),
                "median_abs_dauc_first_vs_full": median(&d_first),
                "median_abs_dauc_second_vs_full": median(&d_second),
            }),
        );
    }
    Value::Object(out)
}

fn lr_section(pairs: &[&PairOut]) -> Value {
    let rows: Vec<(&PairOut, &LrRow)> = pairs
        .iter()
        .filter_map(|p| p.lr.as_ref().map(|l| (*p, l)))
        .collect();
    let summarize = |pick: &dyn Fn(&LrRow) -> (f64, f64, bool, f64)| -> Value {
        let all: Vec<(f64, f64, bool, f64)> = rows.iter().map(|(_, l)| pick(l)).collect();
        let free: Vec<f64> = all.iter().filter(|r| !r.2).map(|r| r.1).collect();
        let every: Vec<f64> = all.iter().map(|r| r.1).collect();
        let gains: Vec<f64> = all.iter().map(|r| r.3).collect();
        json!({
            "pairs": all.len(),
            "separated": count_where(&all, |r| r.2),
            "not_separated_p_below_0_05": count_below(&free, 0.05),
            "not_separated_bh_q_below_0_05": count_below(&benjamini_hochberg(&free), 0.05),
            "all_bh_q_below_0_05": count_below(&benjamini_hochberg(&every), 0.05),
            "all_holm_below_0_05": count_below(&holm(&every), 0.05),
            "median_area_gain": median(&gains),
            "p_by_pair": every,
        })
    };
    json!({
        "orbit_level": true,
        "four_product_free": summarize(&|l| l.four),
        "five_product_free_with_two_step_difference": summarize(&|l| l.five),
        "orbits_and_positives_by_pair": rows.iter().map(|(_, l)| json!([l.orbits, l.orbit_positives])).collect::<Vec<_>>(),
    })
}

/// The call of P13d for one pair: the largest product-free area and whether the associator
/// area exceeds both the threshold and that area plus the margin, or the reason the pair is
/// skipped. A non-finite area or threshold gives no call, since `f64::max` would drop it.
fn p13d_decide(
    oriented: &[f64; 6],
    threshold: f64,
) -> std::result::Result<(f64, bool), &'static str> {
    if !oriented[0].is_finite() {
        return Err("the associator area is not finite");
    }
    if !threshold.is_finite() {
        return Err("the orbit null threshold is not finite");
    }
    if oriented[PRODUCT_FREE].iter().any(|a| !a.is_finite()) {
        return Err("a product-free area is not finite");
    }
    let best = max_of(oriented[PRODUCT_FREE].iter().copied());
    Ok((best, oriented[0] > threshold.max(best + P13D_MARGIN)))
}

/// Verdict of P13d over the pairs that received a call.
fn p13d_verdict(calls: usize, decided: usize) -> &'static str {
    if decided < P13D_MIN_PAIRS {
        "undecided"
    } else if calls * 2 <= decided {
        "held"
    } else {
        "failed"
    }
}

fn p13d_section(pairs: &[&PairOut], heldout: bool) -> Value {
    let direct_threshold = |p: &PairOut| p.direct.as_ref().map_or(f64::NAN, |d| d.threshold[0]);
    let mut rows = Vec::new();
    let mut skipped = Vec::new();
    let mut calls = 0usize;
    let mut calls_direct = 0usize;
    for p in pairs {
        let (rank_sum, direct) = (p.levels[2].threshold, direct_threshold(p));
        let by_rank_sum = p13d_decide(&p.oriented, rank_sum);
        calls_direct += usize::from(matches!(p13d_decide(&p.oriented, direct), Ok((_, true))));
        let head = json!({"run": p.run, "quartile": p.quartile,
            "associator_oriented": p.oriented[0],
            "orbit_positives": p.levels[2].positives, "orbit_negatives": p.levels[2].negatives});
        match by_rank_sum {
            Ok((best, call)) => {
                calls += usize::from(call);
                let mut row = head;
                row["orbit_null_quantile"] = json!(rank_sum);
                row["orbit_null_quantile_direct_relabeling"] = json!(direct);
                row["best_product_free_oriented"] = json!(best);
                row["call"] = json!(call);
                rows.push(row);
            }
            Err(reason) => {
                let mut row = head;
                row["skip_reason"] = json!(reason);
                skipped.push(row);
            }
        }
    }
    let verdict = p13d_verdict(calls, rows.len());
    let mut section = json!({
        "set": if heldout { "heldout" } else { "scored_configurations" },
        "quantile": P13D_QUANTILE,
        "margin": P13D_MARGIN,
        "minimum_pairs": P13D_MIN_PAIRS,
        "threshold_law": "rank-sum law of the orbit counts",
        "pairs": rows.len(),
        "calls": calls,
        "pairs_skipped": skipped.len(),
        "calls_by_direct_relabeling": calls_direct,
        "by_pair": rows,
        "skipped": skipped,
    });
    if heldout {
        section["verdict"] = json!(verdict);
    } else {
        section["note"] = json!("the scored configurations set the rule; they carry no verdict");
    }
    section
}

/// The direct orbit null beside the rank-sum law of the orbit level: per score, the quantile,
/// its two halves, the count law of the areas above the P13c bound and the per-pair tail.
fn direct_section(pairs: &[&PairOut]) -> Value {
    let ok: Vec<(&PairOut, &DirectNull)> = pairs
        .iter()
        .filter_map(|p| p.direct.as_ref().ok().map(|d| (*p, d)))
        .collect();
    let unavailable: Vec<Value> = pairs
        .iter()
        .filter_map(|p| {
            p.direct
                .as_ref()
                .err()
                .map(|e| json!({"run": p.run, "quartile": p.quartile, "reason": e}))
        })
        .collect();
    let law_pairs = ok.len() == pairs.len();
    let by_score = per_score(&|k| {
        let p_above: Vec<f64> = ok.iter().map(|(_, d)| d.p_above_bound[k]).collect();
        let law = poisson_binomial(&p_above);
        let observed = count_where(&ok, |(p, _)| p.oriented[k] > P13C_BOUND);
        let p_ge: Vec<f64> = ok.iter().map(|(_, d)| d.p_ge[k]).collect();
        let diff: Vec<f64> = ok
            .iter()
            .map(|(p, d)| d.threshold[k] - p.levels[2].threshold)
            .collect();
        let halves: Vec<f64> = ok
            .iter()
            .map(|(_, d)| (d.threshold_halves[0][k] - d.threshold_halves[1][k]).abs())
            .collect();
        json!({
            "observed_count_above_bound": observed,
            "expected_count_above_bound": p_above.iter().sum::<f64>(),
            "p_count_at_least_observed": tail(&law, observed),
            "pairs_bh_q_below_0_05": count_below(&benjamini_hochberg(&p_ge), 0.05),
            "pairs_p_below_0_05": count_below(&p_ge, 0.05),
            "mean_null_oriented_area": ok.iter().map(|(_, d)| d.mean[k]).sum::<f64>() / ok.len().max(1) as f64,
            "quantile_by_pair": ok.iter().map(|(_, d)| d.threshold[k]).collect::<Vec<_>>(),
            "quantile_minus_rank_sum_law_by_pair": diff,
            "pairs_quantile_differs_from_rank_sum_law_by_more_than_0_02": count_where(&diff, |d| d.abs() > 0.02),
            "max_abs_quantile_difference_between_halves": halves.iter().copied().fold(0.0, f64::max),
            "p_at_least_observed_by_pair": p_ge,
        })
    });
    json!({
        "law": "labels exchanged among whole orbits of equal size inside the pair; the area of each draw is the cell-level area of the actual scores",
        "draws_per_pair": ok.first().map(|(_, d)| d.draws),
        "pairs_available": ok.len(),
        "pairs_unavailable": unavailable,
        "all_pairs_available": law_pairs,
        "units_and_positive_units_by_pair": ok.iter().map(|(_, d)| json!([d.units, d.positive_units])).collect::<Vec<_>>(),
        "max_identity_difference": ok.iter().map(|(_, d)| d.identity_difference).fold(0.0, f64::max),
        "by_score": by_score,
    })
}

fn assemble(
    args: &NullArgs,
    seeds: &Seeds,
    algs: &[(String, Algebra)],
    outs: &[RunOut],
    retained: Option<&Forecast>,
) -> Result<Value> {
    let pairs: Vec<&PairOut> = outs.iter().flat_map(|o| o.pairs.iter()).collect();
    // Runs that supply no pair (every cell bad, or too few positives) stay out of the per-run statistics.
    let supplying: Vec<&RunOut> = outs.iter().filter(|o| !o.pairs.is_empty()).collect();
    if pairs.is_empty() {
        bail!("no (run, quartile) pair holds {P13C_MIN_POSITIVES} positives and both classes");
    }
    let at_most = count_where(&pairs, |p| p.oriented[0] <= P13C_BOUND);
    let above = pairs.len() - at_most;
    let verdict = if at_most * 2 > pairs.len() {
        "held"
    } else if above * 2 > pairs.len() {
        "failed"
    } else {
        "undecided"
    };
    let observed = per_score(&|k| {
        json!({
            "oriented_above_bound": count_where(&pairs, |p| p.oriented[k] > P13C_BOUND),
            "raw_above_bound": count_where(&pairs, |p| p.raw[k] > P13C_BOUND),
            "raw_below_complement_of_bound": count_where(&pairs, |p| p.raw[k] < 1.0 - P13C_BOUND),
            "raw_below_half": count_where(&pairs, |p| p.raw[k] < 0.5),
            "oriented_by_pair": pairs.iter().map(|p| p.oriented[k]).collect::<Vec<_>>(),
        })
    });
    let excess = |end: usize| -> Vec<f64> {
        pairs
            .iter()
            .map(|p| p.oriented[0] - max_of(p.oriented[1..end].iter().copied()))
            .collect()
    };
    let (excess4, excess5) = (excess(5), excess(6));
    let two_step_raw: Vec<f64> = pairs.iter().map(|p| p.raw[5]).collect();
    let assoc_raw: Vec<f64> = pairs.iter().map(|p| p.raw[0]).collect();
    let dauc: Vec<f64> = two_step_raw
        .iter()
        .zip(&assoc_raw)
        .map(|(a, b)| (a - b).abs())
        .collect();
    let retained_p13c = retained.map(|f| {
        json!({"pairs": f.p13c.pairs_with_enough_positives, "at_most": f.p13c.pairs_associator_at_most_bound,
               "above": f.p13c.pairs_associator_above_bound, "verdict": f.p13c.verdict})
    });
    let mut inputs = serde_json::Map::new();
    for path in args.json.iter().chain(std::iter::once(&args.draw_json)) {
        inputs.insert(path.display().to_string(), json!(sha256_hex(path)?));
    }
    if !args.heldout {
        inputs.insert(
            args.forecast_json.display().to_string(),
            json!(sha256_hex(&args.forecast_json)?),
        );
    }
    let p13d_key = if args.heldout {
        "p13d_rule_applied"
    } else {
        "p13d_rule_calibration"
    };
    Ok(json!({
        "schema": "lbm-late-failure-null-v1",
        "heldout": args.heldout,
        "bound": P13C_BOUND,
        "min_positives": P13C_MIN_POSITIVES,
        "history_states": HISTORY,
        "label_draws": args.label_draws,
        "surrogates_per_kind": args.surrogates,
        "rng": "ChaCha8, one stream per (use, run, cell or pair), seeded from the draw value through splitmix64",
        "seeds": seeds.records,
        "input_sha256": Value::Object(inputs),
        "runs": outs.iter().map(|o| json!({
            "index": o.index, "tau": o.key.tau, "u0": o.key.u0, "delta": o.key.delta,
            "first_violation_step": o.first, "anchor": o.anchor, "pairs": o.pairs.len(),
            "max_abs_area_difference_vs_retained_forecast": o.retained_auc_diff,
            "max_relative_associator_difference_vs_cd_kernel": o.kernel_rel_diff,
            "symmetry": o.symmetry,
        })).collect::<Vec<_>>(),
        "pairs": pairs.iter().map(|p| json!({"run": p.run, "quartile": p.quartile, "cells": p.cells,
            "positives": p.positives, "orbit_mixed_labels": p.orbit_mixed, "raw_area": p.raw.to_vec()})).collect::<Vec<_>>(),
        "p13c_better_orientation": {
            "pairs": pairs.len(), "at_most_bound": at_most, "above_bound": above, "verdict": verdict,
            "retained_forecast_record": retained_p13c,
        },
        "observed_by_score": observed,
        "product_free": {
            "associator_excess_over_best_of_four_above_0_02": count_where(&excess4, |&e| e > 0.02),
            "associator_excess_over_best_of_five_above_0_02": count_where(&excess5, |&e| e > 0.02),
            "median_spearman_associator_two_step_difference": median(&pairs.iter().map(|p| p.spearman_two_step).collect::<Vec<_>>()),
            "median_spearman_associator_gram_volume": median(&pairs.iter().map(|p| p.spearman_gram).collect::<Vec<_>>()),
            "median_abs_area_difference_two_step_vs_associator": median(&dauc),
            "excess_over_best_of_five_by_pair": excess5,
        },
        "label_permutation_null": label_section(&pairs),
        "orbit_direct_relabeling": direct_section(&pairs),
        "torus_shift_null": torus_section(&pairs),
        "increment_nulls": increment_section(outs, &pairs, args.surrogates),
        "algebra_substitution": algebra_section(algs, &supplying, &pairs, seeds.triples),
        "order_decomposition": order_section(algs, &supplying, &pairs),
        "likelihood_ratio": lr_section(&pairs),
        (p13d_key): p13d_section(&pairs, args.heldout),
    }))
}

pub fn forecast_null(args: &NullArgs) -> Result<()> {
    let seeds = read_seeds(&args.draw_json)?;
    let retained: Option<Forecast> = if args.heldout {
        None
    } else {
        let text = std::fs::read_to_string(&args.forecast_json)
            .with_context(|| format!("read {}", args.forecast_json.display()))?;
        Some(
            serde_json::from_str(&text)
                .with_context(|| format!("parse {}", args.forecast_json.display()))?,
        )
    };
    let wanted = collect_configs(args)?;
    if let Some(f) = &retained
        && f.runs.len() != wanted.len()
    {
        bail!(
            "the retained forecast holds {} runs and the inputs score {}",
            f.runs.len(),
            wanted.len()
        );
    }
    let lattice = D3Q19Lattice::new();
    let gens = generators(&lattice)?;
    let algs = algebras(&seeds)?;
    let shifts = torus_shifts();
    let ctx = RunContext {
        algs: &algs,
        gens: &gens,
        seeds: &seeds,
        args,
        shifts: &shifts,
    };
    let mut outs = Vec::new();
    for (i, &(cfg, eps, first)) in wanted.iter().enumerate() {
        eprintln!(
            "run {i}: tau {} U0 {} delta {} first violation {first}",
            cfg.tau, cfg.u0, cfg.delta
        );
        let run = simulate(&lattice, cfg, eps, first)?;
        let record = match &retained {
            Some(f) => Some(
                f.runs
                    .iter()
                    .find(|r| r.config == run.key)
                    .context("no retained forecast run for this configuration")?,
            ),
            None => None,
        };
        let out = process_run(i, &run, record, &ctx)?;
        eprintln!("run {i}: {} pairs", out.pairs.len());
        outs.push(out);
    }
    let report = assemble(args, &seeds, &algs, &outs, retained.as_ref())?;
    if let Some(parent) = args.out_json.parent() {
        std::fs::create_dir_all(parent).with_context(|| format!("create {}", parent.display()))?;
    }
    std::fs::write(&args.out_json, serde_json::to_string_pretty(&report)?)
        .with_context(|| format!("write {}", args.out_json.display()))?;
    eprintln!(
        "P13c under the better orientation: {}; wrote {}",
        report["p13c_better_orientation"]["verdict"],
        args.out_json.display()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use cd_kernel::batch_sliding_associator_norms_parallel;

    fn fixed_seeds() -> Seeds {
        Seeds {
            labels: 11,
            block: 12,
            shuffle: 13,
            phase: 14,
            signs: 15,
            dense: 16,
            triples: 17,
            orbit_direct: 18,
            records: Vec::new(),
        }
    }

    #[test]
    fn adjusted_p_values_match_hand_computation() {
        let p = [0.01, 0.04, 0.03, 0.005];
        let bh = benjamini_hochberg(&p);
        let want_bh = [0.02, 0.04, 0.04, 0.02];
        let hm = holm(&p);
        let want_holm = [0.03, 0.06, 0.06, 0.02];
        for k in 0..4 {
            assert!((bh[k] - want_bh[k]).abs() < 1e-12, "bh {k}: {}", bh[k]);
            assert!((hm[k] - want_holm[k]).abs() < 1e-12, "holm {k}: {}", hm[k]);
        }
    }

    #[test]
    fn poisson_binomial_of_two_fair_coins_is_binomial() {
        let law = poisson_binomial(&[0.5, 0.5]);
        assert_eq!(law.len(), 3);
        assert!(
            (law[0] - 0.25).abs() < 1e-15
                && (law[1] - 0.5).abs() < 1e-15
                && (law[2] - 0.25).abs() < 1e-15
        );
        assert!((tail(&law, 1) - 0.75).abs() < 1e-15);
    }

    #[test]
    fn quantile_interpolates_between_order_statistics() {
        let sorted = [1.0, 2.0, 3.0, 4.0, 5.0];
        assert!((quantile(&sorted, 0.5) - 3.0).abs() < 1e-15);
        assert!((quantile(&sorted, 0.95) - 4.8).abs() < 1e-12);
    }

    #[test]
    fn oriented_null_mean_follows_the_normal_approximation_of_the_rank_sum() {
        let mut rng = stream(7, 0, 0);
        let null = oriented_null(10, 100, 20000, &mut rng);
        let mean = null.iter().sum::<f64>() / null.len() as f64;
        // E max(A, 1 - A) = 1/2 + sd(A) sqrt(2/pi), sd(A)^2 = (n + 1) / (12 n1 n0).
        let sd = (101.0_f64 / (12.0 * 10.0 * 90.0)).sqrt();
        let want = 0.5 + sd * (2.0 / std::f64::consts::PI).sqrt();
        assert!((mean - want).abs() < 0.004, "{mean} against {want}");
        assert!(null.iter().all(|&a| (0.5..=1.0).contains(&a)));
    }

    #[test]
    fn doubling_signs_reproduce_the_quaternions_and_stay_on_the_xor_index() {
        let s = cd_sign_table(4, &[-1.0; 2]).expect("table");
        assert_eq!(s[4 + 2], 1.0, "e1 e2 = e3");
        assert_eq!(s[2 * 4 + 1], -1.0, "e2 e1 = -e3");
        assert_eq!(s[4 + 1], -1.0, "e1 e1 = -1");
        assert!(
            (0..4).all(|q| s[q] == 1.0 && s[q * 4] == 1.0),
            "e0 is the unit"
        );
    }

    #[test]
    fn substitution_controls_have_the_properties_that_name_them() {
        let algs = algebras(&fixed_seeds()).expect("algebras");
        let props = |name: &str| {
            let (_, alg) = algs.iter().find(|(n, _)| n == name).expect(name);
            algebra_properties(alg, 5)
        };
        let path = props("pathion_CD32");
        assert!(
            path[0] > 0.5 && path[1] > 0.1,
            "pathion is neither associative nor alternative"
        );
        assert!(
            path[2] < 1e-12 && path[3] < 1e-12,
            "pathion is flexible and power-associative"
        );
        let octo = props("octonion_x_Z2^2");
        assert!(
            octo[0] > 0.5 && octo[1] < 1e-12,
            "the octonion signs are alternative and not associative"
        );
        for name in [
            "quaternion_x_Z2^3",
            "group_algebra_Z2^5",
            "clifford_Cl(0,5)",
            "clifford_Cl(5,0)",
        ] {
            assert!(props(name)[0] < 1e-12, "{name} is associative");
        }
        let random = props("random_unital_signs_0");
        assert!(
            random[0] > 0.5 && random[2] > 0.1,
            "random signs break flexibility"
        );
    }

    #[test]
    fn xor_pathion_associator_agrees_with_the_kernel() {
        let algs = algebras(&fixed_seeds()).expect("algebras");
        let mut rng = stream(3, 0, 0);
        let mut pops = || -> Vec<f64> { (0..Q).map(|_| rng.random::<f64>() + 0.01).collect() };
        let triple = [pops(), pops(), pops()];
        let unit = triple.clone().map(|p| unit32(&p));
        let ours = vnorm(&algs[0].1.associator(&unit[0], &unit[1], &unit[2]));
        let padded: Vec<Vec<f64>> = unit.iter().map(|u| u.to_vec()).collect();
        let kernel = batch_sliding_associator_norms_parallel(&padded, DIM)[0];
        assert!(
            (ours - kernel).abs() < 1e-9 * kernel,
            "{ours} against {kernel}"
        );
    }

    #[test]
    fn phase_shortcut_equals_the_full_inverse_transform() {
        let mut rng = stream(9, 0, 0);
        let series: Vec<f64> = (0..INCREMENTS).map(|_| rng.random::<f64>() - 0.5).collect();
        let mut planner = FftPlanner::<f64>::new();
        let forward = planner.plan_fft_forward(INCREMENTS);
        let inverse = planner.plan_fft_inverse(INCREMENTS);
        let mut spectrum: Vec<Complex<f64>> =
            series.iter().map(|&x| Complex::new(x, 0.0)).collect();
        forward.process(&mut spectrum);
        let bins = INCREMENTS / 2;
        let phases: Vec<Complex<f64>> = (0..bins)
            .map(|_| Complex::from_polar(1.0, 2.0 * std::f64::consts::PI * rng.random::<f64>()))
            .collect();
        let mut full = spectrum.clone();
        for k in 1..=bins {
            full[k] = spectrum[k] * phases[k - 1];
            full[INCREMENTS - k] = full[k].conj();
        }
        inverse.process(&mut full);
        let phased: Vec<[Complex<f64>; 2]> = (1..=bins)
            .map(|k| {
                let angle = |s: usize| {
                    2.0 * std::f64::consts::PI * (k * (INCREMENTS - 2 + s)) as f64
                        / INCREMENTS as f64
                };
                [
                    phases[k - 1] * Complex::from_polar(1.0, angle(0)),
                    phases[k - 1] * Complex::from_polar(1.0, angle(1)),
                ]
            })
            .collect();
        for s in 0..2 {
            let want = full[INCREMENTS - 2 + s].re / INCREMENTS as f64;
            let got = phase_sample(&spectrum, &phased, s);
            assert!(
                (want - got).abs() < 1e-12,
                "sample {s}: {want} against {got}"
            );
            assert!(
                full[INCREMENTS - 2 + s].im.abs() / (INCREMENTS as f64) < 1e-12,
                "output is real"
            );
        }
        let power = |v: &[Complex<f64>]| v.iter().map(|c| c.norm_sqr()).sum::<f64>();
        assert!(
            (power(&full) / INCREMENTS as f64 - power(&spectrum)).abs() < 1e-9 * power(&spectrum)
        );
    }

    fn group_elements(gens: &[Generator]) -> Vec<(Vec<usize>, [usize; Q])> {
        let identity: (Vec<usize>, [usize; Q]) = ((0..CELLS).collect(), std::array::from_fn(|d| d));
        let mut elements = vec![identity];
        let mut frontier = 0;
        while frontier < elements.len() {
            let (cell, dir) = elements[frontier].clone();
            frontier += 1;
            for g in gens {
                let next: (Vec<usize>, [usize; Q]) = (
                    cell.iter().map(|&c| g.cell[c]).collect(),
                    std::array::from_fn(|d| g.dir[dir[d]]),
                );
                if !elements.contains(&next) {
                    elements.push(next);
                }
            }
        }
        elements
    }

    #[test]
    fn generated_symmetries_have_order_32_and_fix_a_symmetrized_state() {
        let gens = generators(&D3Q19Lattice::new()).expect("generators");
        let elements = group_elements(&gens);
        assert_eq!(elements.len(), 32, "4 in-plane images times 8 z-layer maps");
        let mut rng = stream(21, 0, 0);
        let random: Vec<f64> = (0..CELLS * Q).map(|_| rng.random::<f64>() + 0.01).collect();
        let mut symmetric = vec![0.0; CELLS * Q];
        for (cell, dir) in &elements {
            for c in 0..CELLS {
                for d in 0..Q {
                    symmetric[cell[c] * Q + dir[d]] += random[c * Q + d];
                }
            }
        }
        let orbits = orbits_of(&symmetric, &gens, SYMMETRY_TOLERANCE);
        assert!(
            orbits.generators.iter().all(|g| g.1 < 1e-12),
            "{:?}",
            orbits.generators
        );
        assert_eq!(orbits.sizes.keys().max().copied(), Some(16));
        let generic = orbits.sizes.get(&16).copied().unwrap_or(0) * 16;
        assert!(generic * 10 > CELLS * 9, "{generic} cells in orbits of 16");
        // A state without the symmetry joins no cells.
        let broken = orbits_of(&random, &gens, SYMMETRY_TOLERANCE);
        assert_eq!(broken.count, CELLS);
    }

    #[test]
    fn torus_null_of_a_planted_field_stays_below_the_observed_area() {
        let labels0: Vec<bool> = (0..NX * NY).map(|c| c / NX < 8 && c % NX < 8).collect();
        let field0: Vec<f64> = labels0
            .iter()
            .enumerate()
            .map(|(c, &l)| f64::from(u8::from(l)) + 1e-6 * c as f64)
            .collect();
        let cells0: Vec<usize> = (0..NX * NY).collect();
        let shifts = torus_shifts();
        assert_eq!(shifts.len(), NX * NY - 1);
        let null = torus_null(&field0, &cells0, &labels0, &shifts);
        let observed = oriented(auc(&field0, &labels0));
        assert!(observed > 0.99);
        assert!(
            null.iter().all(|&a| a < observed),
            "a shifted field must rank worse than the aligned one"
        );
    }

    #[test]
    fn likelihood_ratio_detects_a_planted_signal_and_not_noise() {
        let mut rng = stream(4, 0, 0);
        let n = 600;
        let y: Vec<bool> = (0..n).map(|_| rng.random::<f64>() < 0.3).collect();
        let noise = |rng: &mut ChaCha8Rng| -> Vec<f64> {
            (0..n).map(|_| StandardNormal.sample(rng)).collect()
        };
        let signal: Vec<f64> = y
            .iter()
            .map(|&l| {
                let x: f64 = StandardNormal.sample(&mut rng);
                f64::from(u8::from(l)) * 1.2 + x
            })
            .collect();
        let (n1, n2) = (noise(&mut rng), noise(&mut rng));
        let (_, p_signal, _, _) = likelihood_ratio(&[signal, n1.clone()], &y);
        assert!(p_signal < 1e-6, "{p_signal}");
        let (_, p_noise, _, _) = likelihood_ratio(&[n2, n1], &y);
        assert!(p_noise > 1e-3, "{p_noise}");
    }

    #[test]
    fn block_permuted_series_keeps_the_end_state_and_supplies_the_last_two_increments() {
        let mut rng = stream(31, 0, 0);
        let inc: Vec<[f64; Q]> = (0..INCREMENTS)
            .map(|_| std::array::from_fn(|_| rng.random::<f64>() - 0.5))
            .collect();
        let total = |series: &[[f64; Q]]| -> [f64; Q] {
            std::array::from_fn(|d| series.iter().map(|row| row[d]).sum())
        };
        let want = total(&inc);
        let blocks = INCREMENTS / BLOCK;
        let mut last = vec![0usize; blocks];
        for _ in 0..9000 {
            let order = block_order(&mut rng);
    /// Two normal-score columns that differ by about 0.05 and a label drawn from the
    /// logistic law of their difference: the maximum-likelihood coefficients are finite
    /// near -16 and 16, and the classes overlap.
    fn correlated_columns_with_a_finite_fit() -> (Vec<f64>, Vec<f64>, Vec<bool>) {
        let mut rng = stream(41, 0, 0);
        let n = 400;
        let base: Vec<f64> = (0..n).map(|_| StandardNormal.sample(&mut rng)).collect();
        let jitter: Vec<f64> = base
            .iter()
            .map(|&b| {
                let e: f64 = StandardNormal.sample(&mut rng);
                b + 0.05 * e
            })
            .collect();
        let (z1, z2) = (normal_scores(&base), normal_scores(&jitter));
        let y: Vec<bool> = z1
            .iter()
            .zip(&z2)
            .map(|(a, b)| rng.random::<f64>() < 1.0 / (1.0 + (-16.0 * (b - a)).exp()))
            .collect();
        (z1, z2, y)
    }

    #[test]
    fn correlated_columns_with_large_finite_coefficients_are_not_separated() {
        let (z1, z2, y) = correlated_columns_with_a_finite_fit();
        let fit = logit_fit(&[&z1, &z2], &y);
        assert!(
            fit.beta[1] < -15.0 && fit.beta[2] > 15.0,
            "the coefficients exceed the size of 15 that once marked separation: {:?}",
            fit.beta
        );
        assert!(
            fit.eta.iter().zip(&y).any(|(&e, &yy)| (e > 0.0) != yy),
            "the fitted predictor misclassifies a case, so no hyperplane separates"
        );
        assert!(!fit.separated, "{:?}", fit.beta);
        let (_, p, separated, _) = likelihood_ratio(&[z1, z2], &y);
        assert!(!separated && p.is_finite());
    }

    #[test]
    fn separable_classes_are_flagged() {
        let mut rng = stream(42, 0, 0);
        let n = 200;
        let x: Vec<f64> = (0..n).map(|_| StandardNormal.sample(&mut rng)).collect();
        let noise: Vec<f64> = (0..n).map(|_| StandardNormal.sample(&mut rng)).collect();
        let y: Vec<bool> = x.iter().map(|&v| v > 0.3).collect();
        assert!(
            logit_fit(&[&x, &noise], &y).separated,
            "complete separation"
        );
        assert!(likelihood_ratio(&[x, noise], &y).2);
        // Cases at x = 0 carry both labels: no hyperplane separates strictly, yet the
        // likelihood has no finite maximum.
        let mut tied: Vec<f64> = (0..40).map(|i| f64::from(i) - 19.5).collect();
        let mut labels: Vec<bool> = tied.iter().map(|&v| v > 0.0).collect();
        tied.extend([0.0; 6]);
        labels.extend([true, true, true, false, false, false]);
        assert!(
            logit_fit(&[&tied], &labels).separated,
            "quasi-complete separation"
        );
    }

            let mut sorted = order.clone();
            sorted.sort_unstable();
            assert_eq!(
                sorted,
                (0..blocks).collect::<Vec<_>>(),
                "a permutation of the blocks"
            );
            let series: Vec<[f64; Q]> = order
                .iter()
                .flat_map(|&b| inc[b * BLOCK..(b + 1) * BLOCK].iter().copied())
                .collect();
            assert_eq!(series.len(), INCREMENTS);
            let got = total(&series);
            assert!(
                (0..Q).all(|d| (got[d] - want[d]).abs() < 1e-12),
                "the end state is fixed"
            );
            let b = order[blocks - 1];
            assert_eq!(series[INCREMENTS - 2], inc[b * BLOCK + BLOCK - 2]);
            assert_eq!(series[INCREMENTS - 1], inc[b * BLOCK + BLOCK - 1]);
            last[b] += 1;
        }
        assert!(
            last.iter().all(|&n| n.abs_diff(1000) < 150),
            "the final block is uniform: {last:?}"
        );
    }

    #[test]
    fn drawn_increment_pair_is_two_distinct_indices_covering_the_series() {
        let mut rng = stream(32, 0, 0);
        let mut seen = [false; INCREMENTS];
        for _ in 0..4000 {
            let (i, j) = drawn_pair(&mut rng);
            assert!(i != j && i < INCREMENTS && j < INCREMENTS);
            seen[i] = true;
            seen[j] = true;
        }
        assert!(seen.iter().all(|&s| s), "every increment is reachable");
    }

    #[test]
    fn heldout_configurations_are_the_kept_rows_that_no_score_file_lists() {
        let row = |u0: f64, kept: bool| {
            json!({"grid": "widened", "tau": 0.5, "u0": u0, "delta": 2.0,
                   "first_violation_step": if kept { json!(300) } else { Value::Null },
                   "bad_population_cells": Value::Null, "min_population": Value::Null, "kept": kept})
        };
        let score = |u0: f64| {
            json!({"tau": 0.5, "u0": u0, "delta": 2.0, "first_violation_step": 300,
                   "bad_population_cells": 16, "skipped_horizons": [], "horizons": []})
        };
        let record = json!({"nx": 64, "ny": 64, "nz": 4, "eps": 0.05, "max_steps": 6000, "min_kept_step": 200,
            "widened": true,
            "scan": [row(0.1, true), row(0.2, true), row(0.3, true), row(0.4, false)],
            "scores": [score(0.2)]});
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("scores.json");
        std::fs::write(&path, record.to_string()).expect("write");
        let mut args = NullArgs {
            json: vec![path],
            forecast_json: PathBuf::new(),
            draw_json: PathBuf::new(),
            out_json: PathBuf::new(),
            surrogates: 1,
            label_draws: 1,
            heldout: true,
        };
        let held: Vec<f64> = collect_configs(&args)
            .expect("held out")
            .iter()
            .map(|(c, _, _)| c.u0)
            .collect();
        assert_eq!(held, vec![0.1, 0.3]);
        args.heldout = false;
        let scored: Vec<f64> = collect_configs(&args)
            .expect("scored")
            .iter()
            .map(|(c, _, _)| c.u0)
            .collect();
        assert_eq!(scored, vec![0.2]);
    }

    /// Six identical score columns for `units` orbits of `size` cells, each cell scoring
    /// `unit_value(unit) + spread(cell)`; the labels are positive for the first `positives` orbits.
    fn planted_pair(
        units: usize,
        size: usize,
        positives: usize,
        unit_value: impl Fn(usize) -> f64,
        spread: impl Fn(usize) -> f64,
    ) -> (Vec<usize>, Vec<usize>, Vec<bool>, Vec<Vec<f64>>) {
        let n = units * size;
        let orbit_of: Vec<usize> = (0..n).map(|c| c / size).collect();
        let cells: Vec<usize> = (0..n).collect();
        let labels: Vec<bool> = (0..n).map(|c| c / size < positives).collect();
        let column: Vec<f64> = (0..n).map(|c| unit_value(c / size) + spread(c)).collect();
        (orbit_of, cells, labels, vec![column; 6])
    }

    fn raw_areas(scores: &[Vec<f64>], cells: &[usize], labels: &[bool]) -> [f64; 6] {
        std::array::from_fn(|k| auc(&select(&scores[k], cells), labels))
    }

    #[test]
    fn direct_null_matches_the_rank_sum_law_when_orbits_score_alike() {
        // Equal scores inside an orbit and equal orbit sizes: the cell-level area is the
        // orbit-level area, so the direct quantile follows the rank-sum law of the orbits.
        let (orbit_of, cells, labels, scores) = planted_pair(64, 16, 6, |u| u as f64, |_| 0.0);
        let raw = raw_areas(&scores, &cells, &labels);
        let units = direct_units(&orbit_of, &cells, &labels, &scores).expect("units");
        let direct = direct_null(&units, &raw, 20000, 31, 0, 0).expect("direct");
        assert!(direct.identity_difference < 1e-12);
        let mut rng = stream(32, 0, 0);
        let mut law = oriented_null(6, 64, 20000, &mut rng);
        law.sort_by(f64::total_cmp);
        let want = quantile(&law, P13D_QUANTILE);
        assert!(
            (direct.threshold[0] - want).abs() < 0.015,
            "{} against {want}",
            direct.threshold[0]
        );
        assert!((direct.threshold_halves[0][0] - direct.threshold_halves[1][0]).abs() < 0.03);
    }

    #[test]
    fn direct_null_narrows_when_cells_of_an_orbit_score_apart() {
        // Cell scores that ignore the orbit: the orbit-level law treats each orbit as one
        // tie-free rank and overstates the spread of the cell-level area.
        let (orbit_of, cells, labels, scores) =
            planted_pair(64, 16, 6, |_| 0.0, |c| ((c * 2_654_435_761) % 1000) as f64);
        let raw = raw_areas(&scores, &cells, &labels);
        let units = direct_units(&orbit_of, &cells, &labels, &scores).expect("units");
        let direct = direct_null(&units, &raw, 20000, 33, 0, 0).expect("direct");
        let mut rng = stream(34, 0, 0);
        let mut law = oriented_null(6, 64, 20000, &mut rng);
        law.sort_by(f64::total_cmp);
        let rank_sum = quantile(&law, P13D_QUANTILE);
        assert!(
            direct.threshold[0] < rank_sum - 0.1,
            "{} against {rank_sum}",
            direct.threshold[0]
        );
    }

    #[test]
    fn direct_units_reject_mixed_orbits_and_non_finite_scores() {
        let (orbit_of, cells, mut labels, mut scores) =
            planted_pair(8, 4, 2, |u| u as f64, |_| 0.0);
        labels[1] = !labels[1];
        let err = direct_units(&orbit_of, &cells, &labels, &scores).err();
        assert_eq!(
            err.as_deref(),
            Some("an orbit of the pair holds both labels")
        );
        labels[1] = !labels[1];
        scores[3][5] = f64::NAN;
        let err = direct_units(&orbit_of, &cells, &labels, &scores).err();
        assert_eq!(err.as_deref(), Some("a score of the pair is not finite"));
    }

    #[test]
    fn p13d_skips_a_pair_whose_area_or_threshold_is_not_finite() {
        let ok = [0.9, 0.5, 0.6, 0.55, 0.52, 0.58];
        let (best, call) = p13d_decide(&ok, 0.7).expect("finite inputs");
        assert!((best - 0.6).abs() < 1e-15 && call);
        assert_eq!(p13d_decide(&ok, 0.95), Ok((0.6, false)));
        let mut a = ok;
        a[0] = f64::NAN;
        assert!(p13d_decide(&a, 0.7).is_err());
        assert!(p13d_decide(&ok, f64::NAN).is_err());
        for k in 1..6 {
            let mut b = ok;
            b[k] = f64::NAN;
            assert_eq!(
                p13d_decide(&b, 0.7),
                Err("a product-free area is not finite")
            );
        }
        // The margin applies against the best product-free area.
        let close = [0.62, 0.5, 0.6, 0.55, 0.52, 0.58];
        assert_eq!(p13d_decide(&close, 0.5).map(|r| r.1), Ok(false));
    }

    #[test]
    fn p13d_reports_no_verdict_below_the_pair_floor_and_reads_a_majority_above_it() {
        assert_eq!(p13d_verdict(7, 7), "undecided");
        assert_eq!(p13d_verdict(4, 8), "held");
        assert_eq!(p13d_verdict(5, 8), "failed");
        assert_eq!(p13d_verdict(0, 8), "held");
    }

    #[test]
    fn linear_solver_returns_the_known_solution() {
        let mut a = vec![2.0, 1.0, 1.0, 3.0];
        let mut b = vec![5.0, 10.0];
        let x = solve(&mut a, &mut b, 2);
        assert!((x[0] - 1.0).abs() < 1e-12 && (x[1] - 3.0).abs() < 1e-12);
    }
}
