// SPDX-License-Identifier: MIT
//! Controls for the THEMIS crossing precursor ratio of claim C-1619.
//!
//! The statistic of `themis-cd-crossing-survey` is the mean of the last 6 of 12
//! associator norms over the mean of the 6 before them, computed from the 22
//! FGM rows that end at the row before a catalogued magnetopause crossing. An
//! associator norm at index q reads rows q to q+9 of the 22 (three Takens
//! windows of 8 rows, each shifted by one), so a norm near the crossing reads
//! the crossing's own field jump. This binary measures, for the crossings and for
//! rows drawn at random times:
//!
//! 1. the ratio of three series (the associator norms, the increment energy
//!    normalized by the squared field, and the raw increment energy, each
//!    summed over 9 increments from index q) at window ends 0, 12, 24, 48 and
//!    96 rows before the crossing;
//! 2. the same ratios on the 22 rows that start two rows after the crossing,
//!    each series reversed so the ratio reads near six over far six. The 12
//!    values before the crossing read rows i-22 to i-2 (the last row of the
//!    22 enters no Takens vector and no energy window), so the mirrored
//!    values read rows i+2 to i+22;
//! 3. the offset-0 and mirrored ratios on the gap-free, isolated and clustered
//!    subsets (a cadence gap is a time step above 1.5 times the file's median
//!    among the 22 rows before the crossing or the 22 rows of the mirrored
//!    window; isolated means no other catalogued crossing within 120 rows);
//! 4. the per-lag median of the raw increment energy from 100 rows before to
//!    100 rows after the event.
//!
//! A random-time control index is drawn uniformly from the rows of the file at
//! or after `--back-rows` and kept when it lies more than 400 rows from every
//! catalogued crossing. Both rules count every catalogued crossing of the
//! probe, those before `--back-rows` and those of the adjacent days included,
//! at the signed row positions of `crossing_positions`.
//!
//! The default seed is index 0 of the ANU QRNG draw retained at
//! `data/output/audit/claim-family-evidence-adjudication/anu_qrng/draw-2026-11-15T230053Z.json`.
//!
//! Output: one JSON file that binds the sha256 of the catalog and of every day
//! file read; a summary on stderr.

use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use anyhow::{Context, Result, bail};
use cd_kernel::batch_sliding_associator_norms_parallel;
use clap::Parser;
use rand::{RngExt, SeedableRng};
use rand_chacha::ChaCha8Rng;
use serde::Serialize;
use sha2::{Digest, Sha256};

/// Index 0 of the retained ANU QRNG draw named by `QRNG_DRAW`.
const QRNG_SEED: u64 = 57_236;
const QRNG_DRAW: &str =
    "data/output/audit/claim-family-evidence-adjudication/anu_qrng/draw-2026-11-15T230053Z.json#0";
/// Seconds in a day: the offset of the adjacent days' crossing times.
const DAY_SECS: f64 = 86_400.0;
/// Rows per Takens window; four channels (bx, by, bz, |B|) make the 32-vector.
const STEPS: usize = 8;
const DIM: usize = 4 * STEPS;
/// Rows one ratio reads: three Takens windows, each shifted by one.
const NEED: usize = STEPS + 14;
/// Norms in a ratio window and in each of its halves.
const NORMS: usize = NEED - STEPS - 2;
const HALF: usize = NORMS / 2;
/// Increments one associator norm reads, summed by the windowed energies.
const ENERGY_WINDOW: usize = STEPS + 1;
/// Window ends, in rows before the crossing row.
const OFFSETS: [usize; 5] = [0, 12, 24, 48, 96];
/// Crossings closer than this many rows to another crossing are clustered.
const ISOLATION_ROWS: usize = 120;
/// A control index lies farther than this from every crossing of its file.
const CONTROL_SPAN: usize = 400;
/// Random draws per crossing before the control is abandoned.
const CONTROL_DRAWS: usize = 40;
/// A time step above this multiple of the file's median step is a gap.
const GAP_FACTOR: f64 = 1.5;
/// Rows between the event and the mirrored window's first row. The values
/// before the event read rows up to i - 2, so their reflection starts at i + 2.
const MIRROR_SKIP: usize = 2;
/// Profile extent in rows around the event.
const PROFILE_LAG: usize = 100;

#[derive(Parser)]
#[command(name = "themis-cd-crossing-null")]
#[command(about = "THEMIS crossing ratio against random-time, mirror and energy controls")]
struct Cli {
    /// Path to THEMIS crossing catalog TXT (Staples et al. 2020 v2).
    #[arg(
        long,
        default_value = "data/external/crossing_lists/themis_mp_crossings_v2.txt"
    )]
    crossings_txt: PathBuf,

    /// Directory containing th{probe}_fgm_{year}_{doy:03}.csv files.
    #[arg(long, default_value = "data/external/themis")]
    fgm_dir: PathBuf,

    /// Probe filter (single letter).
    #[arg(long, default_value = "a")]
    probe: String,

    /// First row index an event may take, and the rows a file needs before it.
    #[arg(long, default_value_t = 120)]
    back_rows: usize,

    /// Seed of the ChaCha8 stream that draws the random-time controls; the
    /// default is `QRNG_SEED`.
    #[arg(long, default_value_t = QRNG_SEED)]
    seed: u64,

    /// Output JSON path.
    #[arg(
        long,
        default_value = "data/output/heliosphere/ablations/themis_cd_crossing_null.json"
    )]
    out_json: PathBuf,
}

/// One crossing entry of the catalog.
struct Crossing {
    year: u32,
    doy: u32,
    secs_from_midnight: f64,
}

/// One FGM row parsed from the CSV.
struct FgmRow {
    secs: f64,
    b: [f64; 3],
}

/// Ratios of the three series of one window: associator norms, normalized
/// increment energy, raw increment energy. NaN marks a dropped ratio.
type Triple = [f64; 3];
const SERIES_NAMES: [&str; 3] = ["assoc", "energy_norm", "energy_raw"];

/// Everything measured at one event (a crossing or a control).
struct Event {
    gap: bool,
    isolated: bool,
    offsets: [Triple; OFFSETS.len()],
    mirror: Option<Triple>,
    profile: Option<Vec<f64>>,
}

#[derive(Debug, Serialize)]
struct Summary {
    n: usize,
    median: f64,
    p25: f64,
    p75: f64,
    mean: f64,
    mean_log: f64,
    above_1_0: f64,
    above_1_1: f64,
    above_1_5: f64,
}

#[derive(Debug, Serialize)]
struct TripleSummary {
    assoc: Summary,
    energy_norm: Summary,
    energy_raw: Summary,
}

#[derive(Debug, Serialize)]
struct OffsetSummary {
    offset: usize,
    summary: TripleSummary,
}

#[derive(Debug, Serialize)]
struct SubsetSummary {
    events: usize,
    offset_0: TripleSummary,
    mirror_after: TripleSummary,
}

/// Median over events of the raw increment energy at lags -100..=100.
#[derive(Debug, Serialize)]
struct Profile {
    events: usize,
    first_lag: i64,
    median_by_lag: Vec<f64>,
}

#[derive(Debug, Serialize)]
struct KindResult {
    events: usize,
    gap_events: usize,
    isolated_events: usize,
    by_offset: Vec<OffsetSummary>,
    mirror_after: TripleSummary,
    gap_free: SubsetSummary,
    isolated: SubsetSummary,
    clustered: SubsetSummary,
    raw_energy_profile_all: Profile,
    raw_energy_profile_isolated: Profile,
}

#[derive(Debug, Default, Serialize)]
struct SkipCounts {
    missing_file: usize,
    load_error: usize,
    short_file: usize,
    before_back_rows: usize,
    /// Crossings whose offset-0 associator ratio is dropped (early mean below
    /// 1e-20, or a window with a zero-norm Takens vector).
    ratio_dropped: usize,
}

#[derive(Debug, Serialize)]
struct SkippedFile {
    year: u32,
    doy: u32,
    reason: &'static str,
    crossings: usize,
    detail: Option<String>,
}

#[derive(Debug, Serialize)]
struct InputFile {
    name: String,
    sha256: String,
}

#[derive(Debug, Serialize)]
struct Output {
    seed: u64,
    seed_source: String,
    catalog_sha256: String,
    input_files: Vec<InputFile>,
    probe: String,
    back_rows: usize,
    catalog_crossings: usize,
    files: usize,
    skipped: usize,
    skipped_by_cause: SkipCounts,
    skipped_files: Vec<SkippedFile>,
    crossing: KindResult,
    random: KindResult,
}

/// Day of year (1-based) of a calendar date.
fn date_to_doy(year: u32, month: u32, day: u32) -> Option<u32> {
    if !(1..=12).contains(&month) {
        return None;
    }
    let leap = (year.is_multiple_of(4) && !year.is_multiple_of(100)) || year.is_multiple_of(400);
    let days_in_month: [u32; 12] = [
        31,
        if leap { 29 } else { 28 },
        31,
        30,
        31,
        30,
        31,
        31,
        30,
        31,
        30,
        31,
    ];
    Some(days_in_month[..(month as usize - 1)].iter().sum::<u32>() + day)
}

/// Parse `YYYY-MM-DDTHH:MM:SSZ` (or with a fractional second) into the
/// crossing's year, day of year and seconds from midnight.
fn parse_crossing_timestamp(ts: &str) -> Option<Crossing> {
    let t_pos = ts.find('T')?;
    let date_part = &ts[..t_pos];
    let time_part = ts[t_pos + 1..].trim_end_matches('Z');

    let date_fields: Vec<u32> = date_part
        .split('-')
        .filter_map(|s| s.parse().ok())
        .collect();
    if date_fields.len() < 3 {
        return None;
    }
    let (year, month, day) = (date_fields[0], date_fields[1], date_fields[2]);
    let doy = date_to_doy(year, month, day)?;

    let time_fields: Vec<&str> = time_part.split(':').collect();
    if time_fields.len() < 3 {
        return None;
    }
    let hh: f64 = time_fields[0].parse().ok()?;
    let mm: f64 = time_fields[1].parse().ok()?;
    let ss: f64 = time_fields[2].parse().ok()?;
    Some(Crossing {
        year,
        doy,
        secs_from_midnight: hh * 3600.0 + mm * 60.0 + ss,
    })
}

/// Parse an FGM timestamp `2008-07-04T00:00:02.734Z` into seconds from midnight.
fn parse_fgm_timestamp_secs(ts: &str) -> Option<f64> {
    let t_pos = ts.find('T')?;
    let time_part = ts[t_pos + 1..].trim_end_matches('Z');
    let fields: Vec<&str> = time_part.split(':').collect();
    if fields.len() < 3 {
        return None;
    }
    let hh: f64 = fields[0].parse().ok()?;
    let mm: f64 = fields[1].parse().ok()?;
    let ss: f64 = fields[2].parse().ok()?;
    Some(hh * 3600.0 + mm * 60.0 + ss)
}

/// Crossings of one probe grouped by (year, day of year), in catalog order
/// inside a group, and the number parsed.
fn parse_catalog(content: &str, probe: &str) -> (BTreeMap<(u32, u32), Vec<f64>>, usize) {
    let mut groups: BTreeMap<(u32, u32), Vec<f64>> = BTreeMap::new();
    let mut total = 0usize;
    for line in content.lines() {
        if line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() < 8 || fields[7].trim() != probe {
            continue;
        }
        if let Some(c) = parse_crossing_timestamp(fields[0].trim()) {
            groups
                .entry((c.year, c.doy))
                .or_default()
                .push(c.secs_from_midnight);
            total += 1;
        }
    }
    (groups, total)
}

/// Load the rows of a THEMIS FGM CSV (Bx, By, Bz in GSE nT). A row with a
/// timestamp or number that does not parse, or a non-finite component, is
/// dropped; a record whose field count differs from the header's fails the
/// file.
fn load_fgm_csv(path: &Path) -> Result<Vec<FgmRow>> {
    let mut rdr = csv::ReaderBuilder::new()
        .has_headers(true)
        .from_path(path)?;
    let mut rows = Vec::new();
    for result in rdr.records() {
        let record = result?;
        if record.len() < 4 {
            continue;
        }
        let Some(secs) = parse_fgm_timestamp_secs(&record[0]) else {
            continue;
        };
        let (Ok(bx), Ok(by), Ok(bz)) = (
            record[1].trim().parse::<f64>(),
            record[2].trim().parse::<f64>(),
            record[3].trim().parse::<f64>(),
        ) else {
            continue;
        };
        if bx.is_finite() && by.is_finite() && bz.is_finite() {
            rows.push(FgmRow {
                secs,
                b: [bx, by, bz],
            });
        }
    }
    Ok(rows)
}

/// Unit-normalized 32-vectors of the Takens windows of `rows` (8 rows by bx,
/// by, bz, |B|); a window of zero norm is dropped.
fn build_embeddings(rows: &[[f64; 3]]) -> Vec<Vec<f64>> {
    let mut embedded = Vec::with_capacity(rows.len().saturating_sub(STEPS));
    for start in 0..rows.len().saturating_sub(STEPS) {
        let mut v = vec![0.0f64; DIM];
        for (s, r) in rows[start..start + STEPS].iter().enumerate() {
            let bmag = (r[0] * r[0] + r[1] * r[1] + r[2] * r[2]).sqrt();
            v[s * 4..s * 4 + 3].copy_from_slice(r);
            v[s * 4 + 3] = bmag;
        }
        let norm: f64 = v.iter().map(|x| x * x).sum::<f64>().sqrt();
        if norm > 1e-15 {
            v.iter_mut().for_each(|x| *x /= norm);
            embedded.push(v);
        }
    }
    embedded
}

/// Squared increment of the three components from row t to row t + 1.
fn raw_increment_energy(rows: &[[f64; 3]]) -> Vec<f64> {
    rows.windows(2)
        .map(|w| (0..3).map(|c| (w[1][c] - w[0][c]).powi(2)).sum::<f64>())
        .collect()
}

/// The 12 values of each series over the 22 rows of a window.
struct Series {
    /// None when a Takens vector of the window has zero norm.
    assoc: Option<Vec<f64>>,
    energy_norm: Vec<f64>,
    energy_raw: Vec<f64>,
}

/// Sum of `NORMS` windows of `ENERGY_WINDOW` consecutive values, window q
/// starting at q.
fn windowed(x: &[f64]) -> Vec<f64> {
    (0..NORMS)
        .map(|q| x[q..q + ENERGY_WINDOW].iter().sum())
        .collect()
}

fn series(window: &[[f64; 3]]) -> Series {
    debug_assert_eq!(window.len(), NEED);
    let embedded = build_embeddings(window);
    let assoc = (embedded.len() == NEED - STEPS)
        .then(|| batch_sliding_associator_norms_parallel(&embedded, DIM));
    let raw = raw_increment_energy(window);
    let normalized: Vec<f64> = window
        .iter()
        .zip(&raw)
        .map(|(r, e)| e / r.iter().map(|x| x * x).sum::<f64>())
        .collect();
    Series {
        assoc,
        energy_norm: windowed(&normalized),
        energy_raw: windowed(&raw),
    }
}

/// Late six over early six of a 12-value series, or near six over far six
/// when `mirror` is set (the series read from a window after the event, whose
/// first six values lie nearest the event). NaN when the denominator is below
/// 1e-20 or not finite.
fn ratio(x: &[f64], mirror: bool) -> f64 {
    let (first, second) = (&x[..HALF], &x[HALF..]);
    let (early, late) = if mirror {
        (second, first)
    } else {
        (first, second)
    };
    let early_mean = early.iter().sum::<f64>() / HALF as f64;
    let late_mean = late.iter().sum::<f64>() / HALF as f64;
    if early_mean >= 1e-20 && early_mean.is_finite() {
        late_mean / early_mean
    } else {
        f64::NAN
    }
}

fn triple(window: &[[f64; 3]], mirror: bool) -> Triple {
    let s = series(window);
    [
        s.assoc.map_or(f64::NAN, |a| ratio(&a, mirror)),
        ratio(&s.energy_norm, mirror),
        ratio(&s.energy_raw, mirror),
    ]
}

/// Nearest-rank percentile of a sorted list: index round(p / 100 * (n - 1)).
fn nearest_rank(sorted: &[f64], p: f64) -> f64 {
    let idx = ((p / 100.0) * (sorted.len() - 1) as f64).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

/// Median with the mean of the two middle values for an even count.
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

/// Summary of the finite ratios in `ratios`.
fn summarize(ratios: &[f64]) -> Summary {
    let mut sorted: Vec<f64> = ratios.iter().copied().filter(|r| r.is_finite()).collect();
    sorted.sort_by(f64::total_cmp);
    let n = sorted.len();
    if n == 0 {
        return Summary {
            n,
            median: f64::NAN,
            p25: f64::NAN,
            p75: f64::NAN,
            mean: f64::NAN,
            mean_log: f64::NAN,
            above_1_0: f64::NAN,
            above_1_1: f64::NAN,
            above_1_5: f64::NAN,
        };
    }
    let share =
        |threshold: f64| sorted.iter().filter(|&&r| r > threshold).count() as f64 / n as f64;
    let logs: Vec<f64> = sorted
        .iter()
        .filter(|&&r| r > 0.0)
        .map(|r| r.ln())
        .collect();
    Summary {
        n,
        median: nearest_rank(&sorted, 50.0),
        p25: nearest_rank(&sorted, 25.0),
        p75: nearest_rank(&sorted, 75.0),
        mean: sorted.iter().sum::<f64>() / n as f64,
        mean_log: logs.iter().sum::<f64>() / logs.len() as f64,
        above_1_0: share(1.0),
        above_1_1: share(1.1),
        above_1_5: share(1.5),
    }
}

/// Summaries of the three series over `events`, each read through `pick`.
fn triple_summary(events: &[&Event], pick: impl Fn(&Event) -> Option<Triple>) -> TripleSummary {
    let picked: Vec<Triple> = events.iter().filter_map(|e| pick(e)).collect();
    let column = |k: usize| summarize(&picked.iter().map(|t| t[k]).collect::<Vec<f64>>());
    TripleSummary {
        assoc: column(0),
        energy_norm: column(1),
        energy_raw: column(2),
    }
}

fn subset_summary(events: &[&Event], keep: impl Fn(&Event) -> bool) -> SubsetSummary {
    let kept: Vec<&Event> = events.iter().copied().filter(|e| keep(e)).collect();
    SubsetSummary {
        events: kept.len(),
        offset_0: triple_summary(&kept, |e| Some(e.offsets[0])),
        mirror_after: triple_summary(&kept, |e| e.mirror),
    }
}

fn profile(events: &[&Event]) -> Profile {
    let with: Vec<&Vec<f64>> = events.iter().filter_map(|e| e.profile.as_ref()).collect();
    let median_by_lag = (0..=2 * PROFILE_LAG)
        .map(|l| median(&with.iter().map(|p| p[l]).collect::<Vec<f64>>()))
        .collect();
    Profile {
        events: with.len(),
        first_lag: -(PROFILE_LAG as i64),
        median_by_lag,
    }
}

fn kind_result(events: &[Event]) -> KindResult {
    let all: Vec<&Event> = events.iter().collect();
    KindResult {
        events: events.len(),
        gap_events: events.iter().filter(|e| e.gap).count(),
        isolated_events: events.iter().filter(|e| e.isolated).count(),
        by_offset: OFFSETS
            .iter()
            .enumerate()
            .map(|(k, &offset)| OffsetSummary {
                offset,
                summary: triple_summary(&all, |e| Some(e.offsets[k])),
            })
            .collect(),
        mirror_after: triple_summary(&all, |e| e.mirror),
        gap_free: subset_summary(&all, |e| !e.gap),
        isolated: subset_summary(&all, |e| e.isolated),
        clustered: subset_summary(&all, |e| !e.isolated),
        raw_energy_profile_all: profile(&all),
        raw_energy_profile_isolated: profile(
            &all.iter()
                .copied()
                .filter(|e| e.isolated)
                .collect::<Vec<_>>(),
        ),
    }
}

/// The measurements at row `i` of one file; `near_crossings` counts the other
/// analyzed crossings of the file within ISOLATION_ROWS of the row.
fn measure_event(
    rows: &[[f64; 3]],
    secs: &[f64],
    i: usize,
    median_dt: f64,
    near_crossings: usize,
) -> Event {
    let largest_step = |from: usize| {
        (from..from + NEED - 1)
            .map(|j| secs[j + 1] - secs[j])
            .fold(f64::NEG_INFINITY, f64::max)
    };
    let offsets = OFFSETS.map(|k| triple(&rows[i - k - NEED..i - k], false));
    let after = i + MIRROR_SKIP;
    let has_mirror = after + NEED <= rows.len();
    let mirror = has_mirror.then(|| triple(&rows[after..after + NEED], true));
    let gap_limit = GAP_FACTOR * median_dt;
    let gap = largest_step(i - NEED) > gap_limit || (has_mirror && largest_step(after) > gap_limit);
    let profile = (i >= PROFILE_LAG && i + PROFILE_LAG + 2 <= rows.len())
        .then(|| raw_increment_energy(&rows[i - PROFILE_LAG..i + PROFILE_LAG + 2]));
    Event {
        gap,
        isolated: near_crossings == 0,
        offsets,
        mirror,
        profile,
    }
}

/// A random row index in `back..rows` that lies more than CONTROL_SPAN rows
/// from every index in `crossings`, from up to CONTROL_DRAWS uniform draws.
fn draw_control(
    rng: &mut ChaCha8Rng,
    rows: usize,
    back: usize,
    crossings: &[i64],
) -> Option<usize> {
    for _ in 0..CONTROL_DRAWS {
        let j = rng.random_range(back..rows);
        if crossings.iter().all(|&c| row_distance(c, j) > CONTROL_SPAN) {
            return Some(j);
        }
    }
    None
}

/// Rows between a signed crossing position and a row of the file.
fn row_distance(position: i64, row: usize) -> usize {
    let row = i64::try_from(row).unwrap_or(i64::MAX);
    usize::try_from(position.abs_diff(row)).unwrap_or(usize::MAX)
}

/// Signed row positions of crossing times given in seconds of the file's day.
/// A time inside the file takes its nearest row; a time before the first row
/// or after the last lies beyond that end by its distance in median steps, so
/// the crossings of the adjacent days and of a gap at the day's edge keep their
/// distance from the file's rows.
fn crossing_positions(secs: &[f64], median_dt: f64, targets: &[f64]) -> Vec<i64> {
    let first = secs[0];
    let last_row = secs.len() - 1;
    let last = secs[last_row];
    let steps = |gap: f64| {
        let n = (gap / median_dt).ceil();
        if n.is_finite() && n < 9.0e15 {
            n as i64
        } else {
            i64::MAX / 4
        }
    };
    targets
        .iter()
        .map(|&t| {
            if t < first {
                -steps(first - t)
            } else if t > last {
                i64::try_from(last_row).unwrap_or(i64::MAX / 4) + steps(t - last)
            } else {
                i64::try_from(nearest_row(secs, t)).unwrap_or(i64::MAX / 4)
            }
        })
        .collect()
}

/// Days in a calendar year.
fn days_in_year(year: u32) -> u32 {
    if (year.is_multiple_of(4) && !year.is_multiple_of(100)) || year.is_multiple_of(400) {
        366
    } else {
        365
    }
}

/// The (year, day of year) keys of the days before and after a day.
fn adjacent_days(year: u32, doy: u32) -> [(u32, u32); 2] {
    let previous = if doy > 1 {
        (year, doy - 1)
    } else {
        (year - 1, days_in_year(year - 1))
    };
    let next = if doy < days_in_year(year) {
        (year, doy + 1)
    } else {
        (year + 1, 1)
    };
    [previous, next]
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// Index of the row whose time is nearest `target` (the earlier row on a tie).
fn nearest_row(secs: &[f64], target: f64) -> usize {
    let pos = secs.partition_point(|&s| s < target);
    if pos == 0 {
        0
    } else if pos >= secs.len() {
        secs.len() - 1
    } else if (secs[pos] - target).abs() < (secs[pos - 1] - target).abs() {
        pos
    } else {
        pos - 1
    }
}

fn report(name: &str, k: &KindResult) {
    eprintln!(
        "{name}: events {} gap {} isolated {}",
        k.events, k.gap_events, k.isolated_events
    );
    let line = |label: &str, t: &TripleSummary| {
        let part = |s: &Summary| format!("{:.4}/{:.4}/{:.4}", s.median, s.above_1_0, s.mean_log);
        eprintln!(
            "  {label:<12} n {:>5}  {}: {}  {}: {}  {}: {}",
            t.assoc.n,
            SERIES_NAMES[0],
            part(&t.assoc),
            SERIES_NAMES[1],
            part(&t.energy_norm),
            SERIES_NAMES[2],
            part(&t.energy_raw)
        );
    };
    for o in &k.by_offset {
        line(&format!("offset {}", o.offset), &o.summary);
    }
    line("mirror after", &k.mirror_after);
    for (label, s) in [
        ("gap-free", &k.gap_free),
        ("isolated", &k.isolated),
        ("clustered", &k.clustered),
    ] {
        line(&format!("{label} 0"), &s.offset_0);
        line(&format!("{label} mir"), &s.mirror_after);
    }
    let at = |p: &Profile, lag: i64| p.median_by_lag[(lag - p.first_lag) as usize];
    let lags = [-100, -50, -20, -10, -5, -2, -1, 0, 1, 2, 5, 10, 20, 50, 100];
    for (label, p) in [
        ("all", &k.raw_energy_profile_all),
        ("isolated", &k.raw_energy_profile_isolated),
    ] {
        let values: Vec<String> = lags.iter().map(|&l| format!("{:.2}", at(p, l))).collect();
        eprintln!(
            "  raw energy profile ({label}, {} events) at lags {lags:?}: {}",
            p.events,
            values.join(" ")
        );
    }
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    if cli.back_rows < OFFSETS[OFFSETS.len() - 1] + NEED {
        bail!(
            "--back-rows {} is below the {} rows the largest offset reads",
            cli.back_rows,
            OFFSETS[OFFSETS.len() - 1] + NEED
        );
    }
    eprintln!("Parsing crossing catalog: {}", cli.crossings_txt.display());
    let content = std::fs::read_to_string(&cli.crossings_txt)
        .with_context(|| format!("read {}", cli.crossings_txt.display()))?;
    let catalog_sha256 = sha256_hex(content.as_bytes());
    let (groups, catalog_crossings) = parse_catalog(&content, &cli.probe);
    eprintln!(
        "Probe '{}' crossings parsed: {catalog_crossings} across {} file groups",
        cli.probe,
        groups.len()
    );

    let mut rng = ChaCha8Rng::seed_from_u64(cli.seed);
    let mut skips = SkipCounts::default();
    let mut skipped_files = Vec::new();
    let mut files = 0usize;
    let mut input_files: Vec<InputFile> = Vec::new();
    let mut crossing_events: Vec<Event> = Vec::new();
    let mut control_events: Vec<Event> = Vec::new();

    for (&(year, doy), crossing_secs) in &groups {
        let path = cli
            .fgm_dir
            .join(format!("th{}_fgm_{}_{:03}.csv", cli.probe, year, doy));
        let mut skip_file = |reason: &'static str, detail: Option<String>, counter: &mut usize| {
            *counter += crossing_secs.len();
            skipped_files.push(SkippedFile {
                year,
                doy,
                reason,
                crossings: crossing_secs.len(),
                detail,
            });
        };
        if !path.exists() {
            skip_file("missing_file", None, &mut skips.missing_file);
            continue;
        }
        let bytes = std::fs::read(&path).with_context(|| format!("read {}", path.display()))?;
        input_files.push(InputFile {
            name: path
                .file_name()
                .map(|n| n.to_string_lossy().into_owned())
                .unwrap_or_default(),
            sha256: sha256_hex(&bytes),
        });
        drop(bytes);
        let loaded = match load_fgm_csv(&path) {
            Ok(r) => r,
            Err(e) => {
                skip_file("load_error", Some(e.to_string()), &mut skips.load_error);
                continue;
            }
        };
        if loaded.len() < cli.back_rows + STEPS {
            skip_file("short_file", None, &mut skips.short_file);
            continue;
        }
        files += 1;
        let secs: Vec<f64> = loaded.iter().map(|r| r.secs).collect();
        let rows: Vec<[f64; 3]> = loaded.iter().map(|r| r.b).collect();
        let steps: Vec<f64> = secs.windows(2).map(|w| w[1] - w[0]).collect();
        let median_dt = median(&steps);

        let mut indices = Vec::new();
        for &target in crossing_secs {
            let i = nearest_row(&secs, target);
            if i < cli.back_rows {
                skips.before_back_rows += 1;
            } else {
                indices.push(i);
            }
        }
        // Every catalogued crossing of the probe bounds isolation and controls:
        // the day's own (analyzable or not) and the adjacent days', shifted by
        // a day so their positions fall beyond the file's ends.
        let mut catalogued = crossing_secs.clone();
        let [previous, next] = adjacent_days(year, doy);
        if let Some(times) = groups.get(&previous) {
            catalogued.extend(times.iter().map(|t| t - DAY_SECS));
        }
        if let Some(times) = groups.get(&next) {
            catalogued.extend(times.iter().map(|t| t + DAY_SECS));
        }
        let positions = crossing_positions(&secs, median_dt, &catalogued);
        let near = |i: usize, own: usize| {
            positions
                .iter()
                .filter(|&&c| row_distance(c, i) <= ISOLATION_ROWS)
                .count()
                .saturating_sub(own)
        };
        for &i in &indices {
            crossing_events.push(measure_event(&rows, &secs, i, median_dt, near(i, 1)));
        }
        for _ in 0..indices.len() {
            if let Some(j) = draw_control(&mut rng, rows.len(), cli.back_rows, &positions) {
                control_events.push(measure_event(&rows, &secs, j, median_dt, near(j, 0)));
            }
        }
    }

    skips.ratio_dropped = crossing_events
        .iter()
        .filter(|e| !e.offsets[0][0].is_finite())
        .count();
    let skipped = skips.missing_file
        + skips.load_error
        + skips.short_file
        + skips.before_back_rows
        + skips.ratio_dropped;
    let crossing = kind_result(&crossing_events);
    let random = kind_result(&control_events);

    eprintln!(
        "\nCrossings analyzed (offset-0 associator ratio): {}  skipped: {skipped} {skips:?}  files: {files}",
        crossing.by_offset[0].summary.assoc.n
    );
    for f in &skipped_files {
        eprintln!(
            "  skipped file {}-{:03}: {} ({} crossings) {}",
            f.year,
            f.doy,
            f.reason,
            f.crossings,
            f.detail.as_deref().unwrap_or("")
        );
    }
    let s = &crossing.by_offset[0].summary.assoc;
    eprintln!(
        "survey statistic: median {:.4} mean {:.4} p25 {:.4} p75 {:.4} share above 1 {:.4}",
        s.median, s.mean, s.p25, s.p75, s.above_1_0
    );
    report("crossings", &crossing);
    report("random", &random);

    let output = Output {
        seed: cli.seed,
        seed_source: if cli.seed == QRNG_SEED {
            format!("qrng:{QRNG_DRAW}")
        } else {
            "--seed".to_string()
        },
        catalog_sha256,
        input_files,
        probe: cli.probe.clone(),
        back_rows: cli.back_rows,
        catalog_crossings,
        files,
        skipped,
        skipped_by_cause: skips,
        skipped_files,
        crossing,
        random,
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

    /// A slow ramp in bx with a unit step in bx at row 15 (the late half of the
    /// 22 rows).
    fn stepped_rows() -> Vec<[f64; 3]> {
        (0..NEED)
            .map(|t| {
                let step = if t >= 15 { 1.0 } else { 0.0 };
                [1.0 + 0.001 * t as f64 + step, 0.5, 0.2]
            })
            .collect()
    }

    #[test]
    fn a_late_step_raises_both_energy_ratios_and_reversal_lowers_them() {
        let rows = stepped_rows();
        let forward = triple(&rows, false);
        assert!(forward[1] > 1.0 && forward[2] > 1.0, "forward {forward:?}");
        let mut reversed = rows;
        reversed.reverse();
        let back = triple(&reversed, false);
        assert!(back[1] < 1.0 && back[2] < 1.0, "reversed {back:?}");
    }

    #[test]
    fn a_field_symmetric_about_the_event_has_equal_raw_energy_ratios_on_both_sides() {
        let i = 30usize;
        let rows: Vec<[f64; 3]> = (0..2 * i + 1)
            .map(|t| {
                let d = t.abs_diff(i) as f64;
                [
                    5.0 + 0.3 * d + 0.01 * d * d,
                    2.0 - 0.02 * d * d,
                    1.0 + (0.4 * d).sin(),
                ]
            })
            .collect();
        let before = triple(&rows[i - NEED..i], false);
        let after = i + MIRROR_SKIP;
        let mirrored = triple(&rows[after..after + NEED], true);
        assert!(
            (before[2] - mirrored[2]).abs() < 1e-9 * before[2].abs(),
            "before {before:?} mirrored {mirrored:?}"
        );
    }

    #[test]
    fn mirror_reads_near_six_over_far_six() {
        let x: Vec<f64> = (0..NORMS)
            .map(|q| if q < HALF { 4.0 } else { 1.0 })
            .collect();
        assert_eq!(ratio(&x, true), 4.0);
        assert_eq!(ratio(&x, false), 0.25);
        let zero = vec![0.0; NORMS];
        assert!(ratio(&zero, false).is_nan());
    }

    #[test]
    fn nearest_rank_matches_the_survey_rule() {
        let sorted = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0];
        // round(0.50 * 9) = round(4.5) = 5; round(0.25 * 9) = 2; round(0.75 * 9) = 7.
        assert_eq!(nearest_rank(&sorted, 50.0), 6.0);
        assert_eq!(nearest_rank(&sorted, 25.0), 3.0);
        assert_eq!(nearest_rank(&sorted, 75.0), 8.0);
        assert_eq!(nearest_rank(&sorted, 100.0), 10.0);
        let s = summarize(&[0.5, 2.0, f64::NAN, 4.0]);
        assert_eq!(s.n, 3);
        assert!((s.above_1_0 - 2.0 / 3.0).abs() < 1e-12);
    }

    #[test]
    fn day_of_year_follows_the_leap_rule() {
        assert_eq!(date_to_doy(2008, 3, 1), Some(61));
        assert_eq!(date_to_doy(2009, 3, 1), Some(60));
        assert_eq!(date_to_doy(2009, 13, 1), None);
        let c = parse_crossing_timestamp("2008-03-01T01:02:03Z").expect("timestamp parses");
        assert_eq!((c.year, c.doy), (2008, 61));
        assert_eq!(c.secs_from_midnight, 3723.0);
    }

    #[test]
    fn control_indices_stay_clear_of_every_crossing() {
        // 30 lies before the first analyzable row and -250 and 3150 belong to
        // the adjacent days; each still excludes the rows near it.
        let crossings = [-250i64, 30, 1000, 1500, 2990, 3150];
        let mut rng = ChaCha8Rng::seed_from_u64(9);
        let mut drawn = 0;
        for _ in 0..500 {
            if let Some(j) = draw_control(&mut rng, 3000, 120, &crossings) {
                drawn += 1;
                assert!((120..3000).contains(&j));
                for &c in &crossings {
                    assert!(
                        row_distance(c, j) > CONTROL_SPAN,
                        "control {j} near crossing {c}"
                    );
                }
            }
        }
        assert!(drawn > 0);
    }

    #[test]
    fn positions_place_outside_times_beyond_the_file_ends() {
        let secs: Vec<f64> = (0..1000).map(|r| 30.0 + 3.0 * f64::from(r)).collect();
        let pos = crossing_positions(&secs, 3.0, &[96.0, -60.0, 30.0 + 3.0 * 999.0 + 30.0]);
        assert_eq!(pos, vec![22, -30, 1009]);
    }

    #[test]
    fn a_crossing_before_back_rows_still_counts_for_isolation() {
        // The catalog example of 2014-04-25: 00:01:36 and 00:07:04, 328 s apart
        // on a 3-second file. The first lies before row 120 and is not
        // analyzed; the second is, and it is not isolated.
        let secs: Vec<f64> = (0..2000).map(|r| 3.0 * f64::from(r)).collect();
        let pos = crossing_positions(&secs, 3.0, &[96.0, 424.0]);
        let second = nearest_row(&secs, 424.0);
        assert!(second >= 120);
        let near = pos
            .iter()
            .filter(|&&c| row_distance(c, second) <= ISOLATION_ROWS)
            .count()
            - 1;
        assert_eq!(near, 1);
    }

    #[test]
    fn adjacent_days_cross_year_ends() {
        assert_eq!(adjacent_days(2008, 1), [(2007, 365), (2008, 2)]);
        assert_eq!(adjacent_days(2008, 366), [(2008, 365), (2009, 1)]);
        assert_eq!(adjacent_days(2009, 365), [(2009, 364), (2010, 1)]);
    }

    #[test]
    fn nearest_row_takes_the_closer_neighbor() {
        let secs = [0.0, 3.0, 6.0, 9.0];
        assert_eq!(nearest_row(&secs, -5.0), 0);
        assert_eq!(nearest_row(&secs, 4.0), 1);
        assert_eq!(nearest_row(&secs, 5.0), 2);
        assert_eq!(nearest_row(&secs, 99.0), 3);
    }

    #[test]
    fn catalog_filters_probe_and_skips_comments() {
        let text = "# header\n2008-03-01T01:02:03Z\t0\t0\t0\t0\t0\t0\ta\n\
                    2008-03-01T02:00:00Z\t0\t0\t0\t0\t0\t0\tb\n\
                    2008-03-01T03:00:00Z\t0\t0\t0\t0\t0\t0\ta\n";
        let (groups, total) = parse_catalog(text, "a");
        assert_eq!(total, 2);
        assert_eq!(groups[&(2008, 61)], vec![3723.0, 10800.0]);
    }
}
