// SPDX-License-Identifier: MIT
//! Null tests for the associator precursor ratio of claim C-1618.
//!
//! The statistic is the mean of the 6 associator norms that end at a peak
//! divided by the mean of the 6 norms before them, taken over the norm peaks
//! above the 95th percentile. An associator norm at index q reads samples
//! q..q+9 of the record, so the late window of a peak at p shares samples with
//! the peak's own triple. This binary measures three things on the ACE
//! magnetic-field record (December 2004 and January 2005):
//!
//! 1. the ratio at window offsets 0, 4, 10, 20, 40 before each peak (at offset
//!    10 no window sample is read by the peak's own triple);
//! 2. the Spearman correlation of the norms with the increment energy summed
//!    over the same 8-sample span, and the epoch profile of the increment
//!    energy and the field magnitude around the peaks;
//! 3. the same numbers on two nulls: a phase-randomized copy (one shared set
//!    of phases for all four columns keeps every power and cross spectrum) and
//!    the record's own increments permuted inside one-hour blocks (keeps
//!    every increment, destroys their time order below one hour).
//!
//! Output: one JSON file; a summary table on stderr.

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};
use cd_kernel::batch_sliding_associator_norms_parallel;
use clap::Parser;
use rand::seq::SliceRandom;
use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha8Rng;
use rustfft::FftPlanner;
use rustfft::num_complex::Complex;
use serde::Serialize;

/// Samples per Takens window; four channels make the 32-dimensional vector.
const STEPS: usize = 8;
/// Embedding dimension (a pathion).
const DIM: usize = 4 * STEPS;
/// Number of norms in each of the early and late halves of the ratio window.
const HALF_WINDOW: usize = 6;
/// Percentile above which a local maximum of the norm series is a peak.
const PEAK_PERCENTILE: f64 = 95.0;
/// Offsets, in norm indices, between the late window and the peak.
const OFFSETS: [usize; 5] = [0, 4, 10, 20, 40];
/// Epoch profile extent around each peak, in samples.
const LAGS_BEFORE: usize = 24;
const LAGS_AFTER: usize = 16;
/// Length of the blocks inside which the increments are permuted (one hour
/// of 16-second samples). The ratio's window spans 12 norms, 22 samples.
const SHUFFLE_BLOCK: usize = 225;

#[derive(Parser)]
#[command(name = "cd-precursor-null")]
#[command(about = "Associator precursor ratio against overlap-free offsets and two nulls")]
struct Cli {
    /// Directory holding ac_h0_mfi_2004.csv and ac_h0_mfi_2005.csv.
    #[arg(long, default_value = "data/external/ace")]
    data_dir: PathBuf,

    /// Seed of the ChaCha8 stream that drives both randomized series.
    #[arg(long, default_value_t = 20_261_114)]
    seed: u64,

    /// Output JSON path.
    #[arg(
        long,
        default_value = "data/output/heliosphere/ablations/cd_precursor_null.json"
    )]
    out_json: PathBuf,
}

#[derive(Debug, Serialize)]
struct RatioStats {
    offset: usize,
    peaks_used: usize,
    median: f64,
    mean: f64,
    fraction_above_1: f64,
}

/// Median over peaks of a series at each lag, divided by the series' median.
#[derive(Debug, Serialize)]
struct Profile {
    first_lag: i64,
    values: Vec<f64>,
}

#[derive(Debug, Serialize)]
struct SeriesResult {
    rows: usize,
    windows: usize,
    norm_mean: f64,
    norm_p95: f64,
    peaks: usize,
    ratio_by_offset: Vec<RatioStats>,
    spearman_norm_vs_windowed_energy: f64,
    increment_kurtosis_bx: f64,
    raw_energy_profile: Profile,
    normalized_energy_profile: Profile,
    field_magnitude_profile: Profile,
}

#[derive(Debug, Serialize)]
struct Output {
    seed: u64,
    record: SeriesResult,
    phase_randomized: SeriesResult,
    shuffled_increments: SeriesResult,
}

/// Load [Bx, By, Bz, |B|] rows of one month from an ACE MFI CSV.
///
/// Columns: ISO time, |B|, Bx, By, Bz. A row is kept when its time starts with
/// `prefix` and its four numbers parse, are finite and are below 1e4 in magnitude
/// (the file marks fill values with large magnitudes and non-numbers).
fn load_month(path: &Path, prefix: &str, rows: &mut Vec<[f64; 4]>) -> Result<()> {
    let file = File::open(path).with_context(|| format!("open {}", path.display()))?;
    for line in BufReader::new(file).lines() {
        let line = line.with_context(|| format!("read {}", path.display()))?;
        if !line.starts_with(prefix) {
            continue;
        }
        let fields: Vec<&str> = line.split(',').collect();
        if fields.len() < 5 {
            continue;
        }
        let parse = |i: usize| fields[i].trim().parse::<f64>();
        if let (Ok(b), Ok(bx), Ok(by), Ok(bz)) = (parse(1), parse(2), parse(3), parse(4)) {
            let row = [bx, by, bz, b];
            if row.iter().all(|v| v.is_finite() && v.abs() < 1.0e4) {
                rows.push(row);
            }
        }
    }
    Ok(())
}

fn load_ace(dir: &Path) -> Result<Vec<[f64; 4]>> {
    let mut rows = Vec::new();
    load_month(&dir.join("ac_h0_mfi_2004.csv"), "2004-12", &mut rows)?;
    load_month(&dir.join("ac_h0_mfi_2005.csv"), "2005-01", &mut rows)?;
    if rows.len() < 10_000 {
        bail!("too few ACE rows in {}: {}", dir.display(), rows.len());
    }
    Ok(rows)
}

/// Unit-normalized Takens windows: window s holds rows s..s+STEPS row-major.
fn embed_unit(rows: &[[f64; 4]]) -> Result<Vec<Vec<f64>>> {
    let n = rows.len().saturating_sub(STEPS);
    let mut out = Vec::with_capacity(n);
    for s in 0..n {
        let mut v: Vec<f64> = rows[s..s + STEPS].iter().flatten().copied().collect();
        let norm = v.iter().map(|x| x * x).sum::<f64>().sqrt();
        if norm.is_nan() || norm <= 0.0 {
            bail!("embedding window {s} has zero norm");
        }
        v.iter_mut().for_each(|x| *x /= norm);
        out.push(v);
    }
    Ok(out)
}

/// Percentile with linear interpolation between order statistics.
fn percentile(values: &[f64], pct: f64) -> f64 {
    let mut sorted = values.to_vec();
    sorted.sort_by(f64::total_cmp);
    let pos = pct / 100.0 * (sorted.len() - 1) as f64;
    let lo = pos.floor() as usize;
    let hi = (lo + 1).min(sorted.len() - 1);
    sorted[lo] + (sorted[hi] - sorted[lo]) * (pos - lo as f64)
}

fn median(values: &[f64]) -> f64 {
    if values.is_empty() {
        return f64::NAN;
    }
    let mut sorted = values.to_vec();
    sorted.sort_by(f64::total_cmp);
    let n = sorted.len();
    if n % 2 == 1 {
        sorted[n / 2]
    } else {
        0.5 * (sorted[n / 2 - 1] + sorted[n / 2])
    }
}

fn mean(values: &[f64]) -> f64 {
    values.iter().sum::<f64>() / values.len() as f64
}

/// Indices that exceed the percentile and are local maxima. A plateau counts
/// once, at its first sample (strictly greater than the left neighbor, at
/// least the right neighbor).
fn peak_indices(norms: &[f64], pct: f64) -> Vec<usize> {
    let threshold = percentile(norms, pct);
    (1..norms.len().saturating_sub(1))
        .filter(|&i| norms[i] > threshold && norms[i] > norms[i - 1] && norms[i] >= norms[i + 1])
        .collect()
}

/// Late/early ratio of the two 6-norm windows that end `back` indices before
/// each peak; a peak whose early window would start before index 0 is skipped.
fn offset_ratio(norms: &[f64], peaks: &[usize], back: usize) -> RatioStats {
    let window = 2 * HALF_WINDOW;
    let mut ratios = Vec::new();
    for &p in peaks {
        if p < back + window {
            continue;
        }
        let hi = p - back;
        let early = mean(&norms[hi - window..hi - HALF_WINDOW]);
        let late = mean(&norms[hi - HALF_WINDOW..hi]);
        if early > 1e-20 {
            ratios.push(late / early);
        }
    }
    let above = ratios.iter().filter(|&&r| r > 1.0).count();
    RatioStats {
        offset: back,
        peaks_used: ratios.len(),
        median: median(&ratios),
        mean: if ratios.is_empty() {
            f64::NAN
        } else {
            mean(&ratios)
        },
        fraction_above_1: above as f64 / ratios.len() as f64,
    }
}

/// Squared increment of the three field components between consecutive rows.
fn raw_increment_energy(rows: &[[f64; 4]]) -> Vec<f64> {
    rows.windows(2)
        .map(|w| (0..3).map(|c| (w[1][c] - w[0][c]).powi(2)).sum())
        .collect()
}

/// Squared increment divided by the squared field magnitude of the earlier row.
fn normalized_increment_energy(rows: &[[f64; 4]], raw: &[f64]) -> Vec<f64> {
    rows.iter()
        .zip(raw)
        .map(|(r, e)| e / (r[..3].iter().map(|x| x * x).sum::<f64>()))
        .collect()
}

/// Sum of `energy` over STEPS consecutive samples starting at each index,
/// truncated to `len` entries.
fn windowed_sum(energy: &[f64], len: usize) -> Vec<f64> {
    energy
        .windows(STEPS)
        .take(len)
        .map(|w| w.iter().sum())
        .collect()
}

/// Ranks 1..n with ties sharing their mean rank.
fn ranks(x: &[f64]) -> Vec<f64> {
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
    pearson(&ranks(x), &ranks(y))
}

/// Fourth central moment over the squared variance.
fn kurtosis(x: &[f64]) -> f64 {
    let m = mean(x);
    let m2 = x.iter().map(|v| (v - m).powi(2)).sum::<f64>() / x.len() as f64;
    let m4 = x.iter().map(|v| (v - m).powi(4)).sum::<f64>() / x.len() as f64;
    m4 / (m2 * m2)
}

/// Median over peaks of `series` at lags -LAGS_BEFORE..=LAGS_AFTER, over the
/// median of the whole series. Peaks too close to either end are dropped.
fn epoch_profile(series: &[f64], peaks: &[usize]) -> Profile {
    let kept: Vec<usize> = peaks
        .iter()
        .copied()
        .filter(|&p| p >= LAGS_BEFORE && p + LAGS_AFTER < series.len())
        .collect();
    let overall = median(series);
    let values = (0..=LAGS_BEFORE + LAGS_AFTER)
        .map(|k| {
            let at: Vec<f64> = kept.iter().map(|&p| series[p + k - LAGS_BEFORE]).collect();
            median(&at) / overall
        })
        .collect();
    Profile {
        first_lag: -(LAGS_BEFORE as i64),
        values,
    }
}

/// Every statistic of one four-column series.
fn analyze(rows: &[[f64; 4]]) -> Result<SeriesResult> {
    let embedded = embed_unit(rows)?;
    let windows = embedded.len();
    let norms = batch_sliding_associator_norms_parallel(&embedded, DIM);
    drop(embedded);
    let peaks = peak_indices(&norms, PEAK_PERCENTILE);

    let raw = raw_increment_energy(rows);
    let normalized = normalized_increment_energy(rows, &raw);
    let windowed = windowed_sum(&normalized, norms.len());
    let bx_increments: Vec<f64> = rows.windows(2).map(|w| w[1][0] - w[0][0]).collect();
    let magnitude: Vec<f64> = rows[..rows.len() - 1]
        .iter()
        .map(|r| r[..3].iter().map(|x| x * x).sum::<f64>().sqrt())
        .collect();

    Ok(SeriesResult {
        rows: rows.len(),
        windows,
        norm_mean: mean(&norms),
        norm_p95: percentile(&norms, PEAK_PERCENTILE),
        peaks: peaks.len(),
        ratio_by_offset: OFFSETS
            .iter()
            .map(|&b| offset_ratio(&norms, &peaks, b))
            .collect(),
        spearman_norm_vs_windowed_energy: spearman(&norms[..windowed.len()], &windowed),
        increment_kurtosis_bx: kurtosis(&bx_increments),
        raw_energy_profile: epoch_profile(&raw, &peaks),
        normalized_energy_profile: epoch_profile(&normalized, &peaks),
        field_magnitude_profile: epoch_profile(&magnitude, &peaks),
    })
}

/// Phase randomization of each column with one phase set shared by all
/// columns: the power spectrum of every column and every cross spectrum
/// survive, the phase structure does not. DC and (for even length) Nyquist
/// bins keep phase 0 so the inverse transform stays real.
fn phase_randomize(rows: &[[f64; 4]], rng: &mut ChaCha8Rng) -> Vec<[f64; 4]> {
    let n = rows.len();
    let bins = n / 2 + 1;
    let phase: Vec<Complex<f64>> = (0..bins)
        .map(|k| {
            let u: f64 = rng.random();
            let last_even = n.is_multiple_of(2) && k == bins - 1;
            if k == 0 || last_even {
                Complex::new(1.0, 0.0)
            } else {
                Complex::from_polar(1.0, 2.0 * std::f64::consts::PI * u)
            }
        })
        .collect();
    let mut planner = FftPlanner::<f64>::new();
    let forward = planner.plan_fft_forward(n);
    let inverse = planner.plan_fft_inverse(n);

    let mut out = vec![[0.0; 4]; n];
    for c in 0..4 {
        let mean_c = rows.iter().map(|r| r[c]).sum::<f64>() / n as f64;
        let mut buf: Vec<Complex<f64>> = rows
            .iter()
            .map(|r| Complex::new(r[c] - mean_c, 0.0))
            .collect();
        forward.process(&mut buf);
        for k in 0..bins {
            buf[k] *= phase[k];
        }
        // Real-signal symmetry: bin n-k is the conjugate of bin k. The DC and
        // Nyquist bins of a real signal are real.
        buf[0].im = 0.0;
        if n.is_multiple_of(2) {
            buf[n / 2].im = 0.0;
        }
        for k in 1..n.div_ceil(2) {
            buf[n - k] = buf[k].conj();
        }
        inverse.process(&mut buf);
        for (o, b) in out.iter_mut().zip(&buf) {
            o[c] = b.re / n as f64 + mean_c;
        }
    }
    out
}

/// The record's three-component increments, permuted inside consecutive
/// blocks of SHUFFLE_BLOCK increments.
fn permuted_increments(rows: &[[f64; 4]], rng: &mut ChaCha8Rng) -> Vec<[f64; 3]> {
    let mut increments: Vec<[f64; 3]> = rows
        .windows(2)
        .map(|w| [w[1][0] - w[0][0], w[1][1] - w[0][1], w[1][2] - w[0][2]])
        .collect();
    for block in increments.chunks_mut(SHUFFLE_BLOCK) {
        block.shuffle(rng);
    }
    increments
}

/// Shuffled-increment series: the block-permuted increments summed from the
/// record's first row; the fourth column is the magnitude of the other
/// three. Every increment of the record survives unchanged and the series
/// meets the record at each block boundary, so the field magnitude stays at
/// the record's level. Order in time is destroyed below the block length and
/// kept above it.
fn shuffled_increment_series(rows: &[[f64; 4]], rng: &mut ChaCha8Rng) -> Vec<[f64; 4]> {
    let increments = permuted_increments(rows, rng);
    let n = rows.len();
    let mut columns: Vec<Vec<f64>> = Vec::with_capacity(3);
    for c in 0..3 {
        let mut walk = Vec::with_capacity(n);
        let mut acc = rows.first().map_or(0.0, |r| r[c]);
        walk.push(acc);
        for inc in &increments {
            acc += inc[c];
            walk.push(acc);
        }
        columns.push(walk);
    }
    (0..n)
        .map(|i| {
            let (x, y, z) = (columns[0][i], columns[1][i], columns[2][i]);
            [x, y, z, (x * x + y * y + z * z).sqrt()]
        })
        .collect()
}

fn report(name: &str, s: &SeriesResult) {
    eprintln!(
        "{name}: rows {} windows {} norm mean {:.6} p95 {:.6} peaks {}",
        s.rows, s.windows, s.norm_mean, s.norm_p95, s.peaks
    );
    for r in &s.ratio_by_offset {
        eprintln!(
            "  offset {:>2}: peaks {:>5} median {:.3} mean {:.3} above-1 {:.3}",
            r.offset, r.peaks_used, r.median, r.mean, r.fraction_above_1
        );
    }
    eprintln!(
        "  spearman(norm, windowed energy) {:.4}  Bx increment kurtosis {:.2}",
        s.spearman_norm_vs_windowed_energy, s.increment_kurtosis_bx
    );
    let at = |p: &Profile, lag: i64| p.values[(lag - p.first_lag) as usize];
    eprintln!(
        "  raw energy profile: lag -24 {:.3}, -1 {:.3}, +4 {:.3}; field magnitude: lag -24 {:.3}, +4 {:.3}",
        at(&s.raw_energy_profile, -24),
        at(&s.raw_energy_profile, -1),
        at(&s.raw_energy_profile, 4),
        at(&s.field_magnitude_profile, -24),
        at(&s.field_magnitude_profile, 4)
    );
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let rows = load_ace(&cli.data_dir)?;
    let mut rng = ChaCha8Rng::seed_from_u64(cli.seed);

    let record = analyze(&rows)?;
    let phase_randomized = analyze(&phase_randomize(&rows, &mut rng))?;
    let shuffled_increments = analyze(&shuffled_increment_series(&rows, &mut rng))?;

    report("record", &record);
    report("phase_randomized", &phase_randomized);
    report("shuffled_increments", &shuffled_increments);

    let output = Output {
        seed: cli.seed,
        record,
        phase_randomized,
        shuffled_increments,
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

    fn test_rows(n: usize, seed: u64) -> Vec<[f64; 4]> {
        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        (0..n)
            .map(|_| {
                let mut r = [0.0; 4];
                for v in &mut r {
                    *v = rng.random::<f64>() * 10.0 - 3.0;
                }
                r
            })
            .collect()
    }

    #[test]
    fn spike_shoulder_raises_offset_zero_ratio_only() {
        // A spike at index 30 with a raised sample just before it: the late
        // window at offset 0 holds the shoulder, the window at offset 10 holds
        // only the constant background.
        let mut norms = vec![1.0; 60];
        norms[29] = 3.0;
        norms[30] = 10.0;
        let peaks = peak_indices(&norms, PEAK_PERCENTILE);
        assert_eq!(peaks, vec![30]);
        let at0 = offset_ratio(&norms, &peaks, 0);
        assert!(at0.median > 1.0, "offset 0 ratio {}", at0.median);
        assert_eq!(at0.fraction_above_1, 1.0);
        let at10 = offset_ratio(&norms, &peaks, 10);
        assert_eq!(at10.median, 1.0);
        assert_eq!(at10.fraction_above_1, 0.0);
    }

    #[test]
    fn peak_detection_on_a_hand_written_series() {
        let norms = [1.0, 2.0, 1.0, 6.0, 6.0, 2.0, 9.0, 3.0, 1.0, 4.0, 1.0];
        // 50th percentile of the sorted values is 2.0; a plateau counts once
        // at its first sample; the value equal to the threshold does not count.
        assert_eq!(percentile(&norms, 50.0), 2.0);
        assert_eq!(peak_indices(&norms, 50.0), vec![3, 6, 9]);
        assert_eq!(percentile(&[1.0, 2.0, 3.0, 4.0], 50.0), 2.5);
    }

    #[test]
    fn spearman_of_a_monotone_transform_is_one() {
        let x = [0.3, -1.0, 5.0, 2.2, 9.1, 4.4, -7.0];
        let y: Vec<f64> = x.iter().map(|v: &f64| v.powi(3) + 2.0 * v).collect();
        assert!((spearman(&x, &y) - 1.0).abs() < 1e-12);
        let reversed: Vec<f64> = x.iter().map(|v| -v.exp()).collect();
        assert!((spearman(&x, &reversed) + 1.0).abs() < 1e-12);
    }

    fn power_spectrum(column: &[f64]) -> Vec<f64> {
        let n = column.len();
        let m = column.iter().sum::<f64>() / n as f64;
        let mut buf: Vec<Complex<f64>> = column.iter().map(|v| Complex::new(v - m, 0.0)).collect();
        FftPlanner::<f64>::new()
            .plan_fft_forward(n)
            .process(&mut buf);
        buf.iter().map(|b| b.norm_sqr()).collect()
    }

    #[test]
    fn phase_randomization_keeps_each_column_power_spectrum() {
        for n in [64usize, 63] {
            let rows = test_rows(n, 7);
            let mut rng = ChaCha8Rng::seed_from_u64(11);
            let copy = phase_randomize(&rows, &mut rng);
            let mut moved = false;
            for c in 0..4 {
                let before: Vec<f64> = rows.iter().map(|r| r[c]).collect();
                let after: Vec<f64> = copy.iter().map(|r| r[c]).collect();
                let (pb, pa) = (power_spectrum(&before), power_spectrum(&after));
                let scale = pb.iter().copied().fold(0.0, f64::max);
                for (a, b) in pa.iter().zip(&pb) {
                    assert!(
                        (a - b).abs() <= 1e-9 * scale,
                        "n {n} column {c}: {a} vs {b}"
                    );
                }
                moved |= before.iter().zip(&after).any(|(a, b)| (a - b).abs() > 1e-3);
            }
            assert!(moved, "phases left the series unchanged for n {n}");
        }
    }

    #[test]
    fn increment_permutation_keeps_the_multiset() {
        let rows = test_rows(200, 3);
        let original: Vec<[f64; 3]> = rows
            .windows(2)
            .map(|w| [w[1][0] - w[0][0], w[1][1] - w[0][1], w[1][2] - w[0][2]])
            .collect();
        let mut rng = ChaCha8Rng::seed_from_u64(5);
        let shuffled = permuted_increments(&rows, &mut rng);
        assert_eq!(shuffled.len(), original.len());
        assert_ne!(shuffled, original);
        for c in 0..3 {
            let mut a: Vec<f64> = original.iter().map(|v| v[c]).collect();
            let mut b: Vec<f64> = shuffled.iter().map(|v| v[c]).collect();
            a.sort_by(f64::total_cmp);
            b.sort_by(f64::total_cmp);
            assert_eq!(a, b, "component {c}");
        }
        // The series holds the same increments and meets the record at every
        // block boundary.
        let series = shuffled_increment_series(&rows, &mut ChaCha8Rng::seed_from_u64(5));
        assert_eq!(series.len(), rows.len());
        for c in 0..3 {
            let mut a: Vec<f64> = original.iter().map(|v| v[c]).collect();
            let mut b: Vec<f64> = series.windows(2).map(|w| w[1][c] - w[0][c]).collect();
            a.sort_by(f64::total_cmp);
            b.sort_by(f64::total_cmp);
            for (x, y) in a.iter().zip(&b) {
                assert!((x - y).abs() < 1e-9, "component {c}");
            }
        }
        let rows = test_rows(2 * SHUFFLE_BLOCK + 40, 4);
        let series = shuffled_increment_series(&rows, &mut ChaCha8Rng::seed_from_u64(6));
        for boundary in [0, SHUFFLE_BLOCK, 2 * SHUFFLE_BLOCK] {
            for c in 0..3 {
                assert!((series[boundary][c] - rows[boundary][c]).abs() < 1e-9);
            }
        }
        assert_ne!(series[SHUFFLE_BLOCK / 2], rows[SHUFFLE_BLOCK / 2]);
    }
}
