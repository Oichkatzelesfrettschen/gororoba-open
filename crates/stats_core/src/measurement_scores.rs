// SPDX-License-Identifier: MIT
//! Linear scores and their complete covariance under multinomial sampling.
//!
//! Every column is one mutually exclusive outcome of the same observation law.
//! Zero-score outcomes remain in the total count. Two score rows share trials,
//! so their covariance generally does not vanish. The caller owns the sampling
//! unit, the complete outcome partition, and any postselection or time metadata.
//! Accepted-event counts describe a conditional law; this module cannot turn
//! them into unconditional attempt counts or establish independent sampling.
//!
//! For counts `n[j]`, total `N`, proportions `p[j] = n[j] / N`, and score columns
//! `s[j]`, the estimated mean is `mu = sum_j p[j] s[j]`. The centered empirical
//! second moment is `M = sum_j p[j] (s[j] - mu) (s[j] - mu)^T`. The plug-in
//! covariance of the mean is `M / N`; its unbiased estimate is `M / (N - 1)`.
//! These are sampling-model estimates, not calibrated confidence intervals.
//!
//! The arithmetic carries every rounding residual through the error-free
//! transformations of Ogita, Rump and Oishi, "Accurate sum and dot product",
//! SIAM J. Sci. Comput. 26(6), 1955-1988 (2005): TwoSum (Algorithm 3.1,
//! Theorem 3.4), TwoProductFMA (Algorithm 3.5, through `f64::mul_add`) and
//! Dot2 (Algorithm 5.3, Proposition 5.5). Only outcomes with nonzero count
//! enter; `k` counts them.
//!
//! - Each row is shifted by the score `a` of the most frequent outcome. The
//!   offsets `d[j] = s[j] - a` are exact TwoSum pairs, so a constant row has
//!   exactly zero offsets, and one power of two rescales them so the largest
//!   lies in `[1, 2)`. The rescaling keeps large scores from overflowing when
//!   squared and small ones from underflowing.
//! - The weights `w[j] = n[j] / 2^K`, with `2^K` the least power of two at
//!   least `N`, are exact, and so is their total `W = N / 2^K`.
//! - The mean offset is Dot2 over the `2k` products of each weight with both
//!   parts of its offset, held as a double-length pair and divided by `W` with
//!   the remainder `fma(-q, W, x)` carried.
//! - Each centered value `d[j]` minus the mean pair combines all four parts
//!   through TwoSum, so it keeps the residuals of the offset and of the mean.
//!   No single anchor choice discards a small score beside a large one.
//! - Each covariance entry is Dot2 over the triple products
//!   `w[j] c_x[j] c_y[j]`: TwoProductFMA forms the leading parts and the
//!   products with the low parts join the error term. The double-length sum is
//!   divided by `W` and by the estimator denominator, rounded once and scaled
//!   back by the powers of two of its two rows.
//!
//! With `eps = 2^-53`, `gamma_n = n eps / (1 - n eps)` and no underflow,
//! Proposition 5.5 applied to the doubled vectors bounds the mean by
//! `|mean - mu| <= eps |mu| + (gamma_{2k}^2 + O(eps^2)) sum_j p[j] |s[j] - a|`,
//! a relative error of `eps + gamma_{2k}^2 kappa` for the condition number
//! `kappa = sum_j p[j] |s[j] - a| / |mu|`. Centering against a mean pair with
//! error `delta` changes the exact centered moment by `delta_x delta_y` only,
//! since the exact centered values have zero weighted sum. hypothesis: the
//! proof of Proposition 5.5 carried through the triple products bounds each
//! entry of `M` by
//! `eps |M_xy| + (gamma_k^2 + O(eps^2)) sum_j p[j] |c_x[j] c_y[j]| + |delta_x delta_y|`,
//! so its relative error is `eps + gamma_k^2 kappa_xy` up to terms of order
//! `eps^4`. The paper states the bound for a dot product only; this
//! covariance form is derived here and has no independent check beyond the
//! exact-value tests below. A variance has `kappa = 1`
//! and is therefore rounded once to within those terms. The modal anchor
//! carries probability at least `1 / k`, so `kappa` for the mean is at most
//! `k + 1` times the anchor-free condition number `sum_j p[j] |s[j]| / |mu|`.
//!
//! The remaining limit is the conditioning: once `gamma^2 kappa` approaches
//! `eps` the result is no longer accurate to working precision, and at
//! `kappa >= 1 / gamma^2` no digit is guaranteed. Overflow of an offset, a
//! centered value or a rescaled result returns an arithmetic error. TwoProductFMA
//! loses exactness below `2^-969`, which the rescaling reaches only for
//! scores more than about `2^900` times smaller than the largest offset of
//! their row. A nonzero leading product or a nonzero result that underflows to
//! zero is an arithmetic error, so no failure silently reports exact zero
//! uncertainty; a subnormal result carries the absolute error of gradual
//! underflow.

use nalgebra::{DMatrix, DVector};

/// Largest admitted total, so every count and total converts exactly to f64.
///
/// Larger totals are rejected even when a particular integer is representable.
pub const MAX_EXACT_TOTAL_COUNT: u64 = 1_u64 << 53;

/// Finite-sample convention for estimating the covariance of the score means.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CovarianceEstimator {
    /// Substitute empirical probabilities in the multinomial covariance law.
    /// This estimate has expectation `(N - 1) / N` times the true covariance.
    PlugIn,
    /// Divide the empirical centered second moment by `N - 1`; requires `N >= 2`.
    Unbiased,
}

/// Invalid input or an unrepresentable floating-point calculation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MeasurementScoreError {
    /// The outcome list or the list of score rows is empty.
    EmptyInput,
    /// The number of score columns differs from the number of outcomes.
    DimensionMismatch,
    /// All outcome counts are zero.
    ZeroTotalCount,
    /// Summing the integer counts overflows u64.
    CountOverflow,
    /// The total exceeds the explicitly supported exact-integer range.
    CountPrecisionLoss,
    /// The unbiased estimator receives fewer than two observations.
    InsufficientCount,
    /// A score is NaN or infinite, including a score for an unobserved outcome.
    NonFiniteScore,
    /// Arithmetic is nonfinite or a nonzero product underflows to zero.
    Arithmetic,
}

impl std::fmt::Display for MeasurementScoreError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let message = match self {
            Self::EmptyInput => "outcomes and score rows must be nonempty",
            Self::DimensionMismatch => "score columns and outcome counts disagree",
            Self::ZeroTotalCount => "the total observation count must be positive",
            Self::CountOverflow => "the integer count sum overflows u64",
            Self::CountPrecisionLoss => "the total count exceeds 2^53",
            Self::InsufficientCount => "unbiased covariance requires two observations",
            Self::NonFiniteScore => "all outcome scores must be finite",
            Self::Arithmetic => "a score calculation overflows or underflows",
        };
        formatter.write_str(message)
    }
}

impl std::error::Error for MeasurementScoreError {}

/// Joint estimates from one count vector and its declared outcome scores.
#[derive(Debug, Clone, PartialEq)]
pub struct MultinomialScoreEstimate {
    /// Includes every outcome supplied by the caller, including zero-score ones.
    pub total_count: u64,
    /// Retained explicitly so downstream consumers know the finite-sample law.
    pub estimator: CovarianceEstimator,
    /// One mean per score row, in that row's caller-defined units.
    pub means: DVector<f64>,
    /// Full covariance of the means, in the corresponding products of units.
    pub covariance_of_means: DMatrix<f64>,
}

fn finite(value: f64) -> Result<f64, MeasurementScoreError> {
    if value.is_finite() {
        Ok(value)
    } else {
        Err(MeasurementScoreError::Arithmetic)
    }
}

fn product(left: f64, right: f64) -> Result<f64, MeasurementScoreError> {
    let result = finite(left * right)?;
    if result == 0.0 && left != 0.0 && right != 0.0 {
        Err(MeasurementScoreError::Arithmetic)
    } else {
        Ok(result)
    }
}

/// An unevaluated sum `high + low`; after `two_sum`, `high` is the rounded sum
/// and `high == 0` implies `low == 0`.
#[derive(Debug, Clone, Copy, Default)]
struct DoubleLength {
    high: f64,
    low: f64,
}

/// TwoSum (Algorithm 3.1): `left + right == high + low` exactly, underflow
/// included, whenever no intermediate overflows.
fn two_sum(left: f64, right: f64) -> Result<DoubleLength, MeasurementScoreError> {
    let high = finite(left + right)?;
    let right_part = high - left;
    let low = finite((left - (high - right_part)) + (right - right_part))?;
    Ok(DoubleLength { high, low })
}

/// TwoProductFMA (Algorithm 3.5) for a leading product, whose underflow to zero
/// from nonzero factors is an arithmetic error.
fn two_product(left: f64, right: f64) -> Result<DoubleLength, MeasurementScoreError> {
    let high = product(left, right)?;
    let low = finite(left.mul_add(right, -high))?;
    Ok(DoubleLength { high, low })
}

/// TwoProductFMA for a residual product, which may underflow harmlessly.
fn two_product_residual(left: f64, right: f64) -> Result<DoubleLength, MeasurementScoreError> {
    let high = finite(left * right)?;
    let low = finite(left.mul_add(right, -high))?;
    Ok(DoubleLength { high, low })
}

/// Dot2 (Algorithm 5.3): TwoSum accumulates the leading parts and the plain sum
/// `error` collects the TwoSum residuals with each product's low part.
#[derive(Debug, Clone, Copy, Default)]
struct CompensatedDot {
    sum: f64,
    error: f64,
}

impl CompensatedDot {
    fn add(&mut self, term: DoubleLength, extra_error: f64) -> Result<(), MeasurementScoreError> {
        let step = two_sum(self.sum, term.high)?;
        self.sum = step.high;
        self.error = finite(self.error + (step.low + (term.low + extra_error)))?;
        Ok(())
    }

    fn finish(self) -> Result<DoubleLength, MeasurementScoreError> {
        two_sum(self.sum, self.error)
    }
}

/// Divides a double-length value by a float; FMA forms the remainder of the
/// leading quotient exactly, so the quotient pair errs by `O(eps^2)` relative.
fn divide(value: DoubleLength, divisor: f64) -> Result<DoubleLength, MeasurementScoreError> {
    let high = finite(value.high / divisor)?;
    if high == 0.0 && value.high != 0.0 {
        return Err(MeasurementScoreError::Arithmetic);
    }
    let remainder = (-high).mul_add(divisor, value.high);
    let low = finite((remainder + value.low) / divisor)?;
    two_sum(high, low)
}

/// Subtracts one double-length value from another, carrying all four parts.
fn subtract(
    left: DoubleLength,
    right: DoubleLength,
) -> Result<DoubleLength, MeasurementScoreError> {
    let leading = two_sum(left.high, -right.high)?;
    let trailing = two_sum(left.low, -right.low)?;
    let combined = two_sum(leading.high, trailing.high)?;
    two_sum(
        combined.high,
        finite((leading.low + trailing.low) + combined.low)?,
    )
}

/// Exponent `e` with `2^e <= |value| < 2^(e + 1)` for finite nonzero `value`.
fn binary_exponent(value: f64) -> i32 {
    let bits = value.abs().to_bits();
    let biased = (bits >> 52) as i32;
    if biased == 0 {
        63 - bits.leading_zeros() as i32 - 1074
    } else {
        biased - 1023
    }
}

/// `2^exponent` for a normal exponent in `-1022..=1023`.
fn power_of_two(exponent: i32) -> f64 {
    f64::from_bits(((exponent + 1023) as u64) << 52)
}

/// Multiplies by `2^exponent` with at most one rounding. The partial factor
/// goes first, so a later full step either stays exact or sends an already
/// subnormal value to zero, which is also the correctly rounded result.
fn scale_by_power_of_two(value: f64, exponent: i32) -> f64 {
    const STEP: i32 = 1000;
    let partial = exponent % STEP;
    let mut scaled = value * power_of_two(partial);
    let mut remaining = exponent - partial;
    while remaining > 0 {
        scaled *= power_of_two(STEP);
        remaining -= STEP;
    }
    while remaining < 0 {
        scaled *= power_of_two(-STEP);
        remaining += STEP;
    }
    scaled
}

/// Scales a result back to caller units; a nonzero value that underflows to
/// zero or overflows is an arithmetic error.
fn rescale_result(value: f64, exponent: i32) -> Result<f64, MeasurementScoreError> {
    let scaled = finite(scale_by_power_of_two(value, exponent))?;
    if scaled == 0.0 && value != 0.0 {
        Err(MeasurementScoreError::Arithmetic)
    } else {
        Ok(scaled)
    }
}

/// Estimate means and their full covariance from independent multinomial trials.
///
/// `scores[(i, j)]` is the score of observable `i` on outcome `j`. All supplied
/// outcomes, including those assigned score zero, contribute to the denominator.
/// Outcomes with zero count contribute no arithmetic weight but must still have
/// finite scores. The total count is checked as an integer before conversion.
///
/// The plug-in estimate uses denominator `N`; the unbiased estimate uses `N - 1`
/// after forming the centered empirical second moment. One observation permits
/// only the plug-in estimate, whose zero variance does not prove a deterministic
/// underlying law. The same qualification applies to any unobserved category.
///
/// Complexity is `O(m^2 k)` time and `O(m k + m^2)` additional storage for `m`
/// score rows and `k` outcomes. A returned covariance is symmetric by construction.
/// Floating-point roundoff still applies; the routine does not regularize it.
///
/// # Errors
///
/// Returns an error for empty inputs, dimension mismatch, nonfinite scores,
/// zero or overflowing total counts, totals above `2^53`, insufficient unbiased
/// observations, or nonfinite/underflowing intermediate arithmetic. An arithmetic
/// rejection can occur even if a different numerical representation can resolve
/// the final result. No omitted category or sample provenance is inferred.
///
/// # Examples
///
/// ```
/// use nalgebra::DMatrix;
/// use stats_core::measurement_scores::{CovarianceEstimator, multinomial_scores};
///
/// let scores = DMatrix::from_row_slice(1, 4, &[1.0, 0.0, 0.0, -1.0]);
/// let result = multinomial_scores(&[1, 1, 1, 1], &scores,
///                                 CovarianceEstimator::PlugIn).unwrap();
/// assert_eq!(result.total_count, 4);
/// assert_eq!(result.means[0], 0.0);
/// assert_eq!(result.covariance_of_means[(0, 0)], 0.125);
/// ```
pub fn multinomial_scores(
    counts: &[u64],
    scores: &DMatrix<f64>,
    estimator: CovarianceEstimator,
) -> Result<MultinomialScoreEstimate, MeasurementScoreError> {
    if counts.is_empty() || scores.nrows() == 0 {
        return Err(MeasurementScoreError::EmptyInput);
    }
    if scores.ncols() != counts.len() {
        return Err(MeasurementScoreError::DimensionMismatch);
    }
    if scores.iter().any(|score| !score.is_finite()) {
        return Err(MeasurementScoreError::NonFiniteScore);
    }
    let total_count = counts.iter().try_fold(0_u64, |sum, count| {
        sum.checked_add(*count)
            .ok_or(MeasurementScoreError::CountOverflow)
    })?;
    if total_count == 0 {
        return Err(MeasurementScoreError::ZeroTotalCount);
    }
    if total_count > MAX_EXACT_TOTAL_COUNT {
        return Err(MeasurementScoreError::CountPrecisionLoss);
    }
    let denominator = match estimator {
        CovarianceEstimator::PlugIn => total_count,
        CovarianceEstimator::Unbiased if total_count >= 2 => total_count - 1,
        CovarianceEstimator::Unbiased => return Err(MeasurementScoreError::InsufficientCount),
    } as f64;
    let observed: Vec<usize> = (0..counts.len())
        .filter(|outcome| counts[*outcome] != 0)
        .collect();
    let weight_scale = total_count.next_power_of_two() as f64;
    let weights: Vec<f64> = observed
        .iter()
        .map(|outcome| counts[*outcome] as f64 / weight_scale)
        .collect();
    let weight_total = total_count as f64 / weight_scale;
    let mut modal = 0;
    for (outcome, count) in counts.iter().enumerate() {
        if *count > counts[modal] {
            modal = outcome;
        }
    }
    let mut means = DVector::zeros(scores.nrows());
    let mut centered = Vec::with_capacity(scores.nrows());
    let mut exponents = Vec::with_capacity(scores.nrows());
    for row in 0..scores.nrows() {
        let anchor = scores[(row, modal)];
        let offsets = observed
            .iter()
            .map(|outcome| two_sum(scores[(row, *outcome)], -anchor))
            .collect::<Result<Vec<_>, _>>()?;
        let largest = offsets
            .iter()
            .fold(0.0_f64, |largest, offset| largest.max(offset.high.abs()));
        let exponent = if largest == 0.0 {
            0
        } else {
            binary_exponent(largest)
        };
        let offsets: Vec<DoubleLength> = offsets
            .iter()
            .map(|offset| DoubleLength {
                high: scale_by_power_of_two(offset.high, -exponent),
                low: scale_by_power_of_two(offset.low, -exponent),
            })
            .collect();
        let mut numerator = CompensatedDot::default();
        for (offset, weight) in offsets.iter().zip(&weights) {
            numerator.add(two_product(*weight, offset.high)?, 0.0)?;
            numerator.add(two_product_residual(*weight, offset.low)?, 0.0)?;
        }
        let mean_offset = divide(numerator.finish()?, weight_total)?;
        let leading = two_sum(anchor, rescale_result(mean_offset.high, exponent)?)?;
        let trailing = scale_by_power_of_two(mean_offset.low, exponent);
        means[row] = finite(leading.high + (leading.low + trailing))?;
        centered.push(
            offsets
                .iter()
                .map(|offset| subtract(*offset, mean_offset))
                .collect::<Result<Vec<_>, _>>()?,
        );
        exponents.push(exponent);
    }
    let mut covariance_of_means = DMatrix::zeros(scores.nrows(), scores.nrows());
    for row in 0..scores.nrows() {
        for column in 0..=row {
            let mut moment = CompensatedDot::default();
            for ((left, right), weight) in centered[row].iter().zip(&centered[column]).zip(&weights)
            {
                let weighted = two_product(*weight, left.high)?;
                let weighted_low = finite(weighted.low + weight * left.low)?;
                let leading = two_product(weighted.high, right.high)?;
                let cross = finite(weighted.high * right.low + weighted_low * right.high)?;
                moment.add(leading, cross)?;
            }
            let moment = divide(divide(moment.finish()?, weight_total)?, denominator)?;
            let covariance = rescale_result(moment.high, exponents[row] + exponents[column])?;
            covariance_of_means[(row, column)] = covariance;
            covariance_of_means[(column, row)] = covariance;
        }
    }
    Ok(MultinomialScoreEstimate {
        total_count,
        estimator,
        means,
        covariance_of_means,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn zero_score_outcomes_remain_in_the_denominator() {
        let scores = DMatrix::from_row_slice(1, 4, &[1.0, 0.0, 0.0, -1.0]);
        let result =
            multinomial_scores(&[1, 1, 1, 1], &scores, CovarianceEstimator::PlugIn).unwrap();
        assert_eq!(result.total_count, 4);
        assert_eq!(result.means[0], 0.0);
        assert_eq!(result.covariance_of_means[(0, 0)], 0.125);
    }

    #[test]
    fn shared_outcomes_preserve_covariance_and_estimator_convention() {
        // Indicator expansion gives E[X^2]=0.7, E[Y^2]=0.8, E[XY]=-0.5.
        let scores = DMatrix::from_row_slice(2, 3, &[1.0, 0.0, -1.0, 0.0, 1.0, 1.0]);
        let expected = DMatrix::from_row_slice(2, 2, &[0.061, -0.026, -0.026, 0.016]);
        for (estimator, correction) in [
            (CovarianceEstimator::PlugIn, 1.0),
            (CovarianceEstimator::Unbiased, 10.0 / 9.0),
        ] {
            let result = multinomial_scores(&[2, 3, 5], &scores, estimator).unwrap();
            assert_eq!(result.estimator, estimator);
            assert_relative_eq!(
                result.means,
                DVector::from_vec(vec![-0.3, 0.8]),
                epsilon = 1e-15
            );
            assert_relative_eq!(
                result.covariance_of_means,
                &expected * correction,
                epsilon = 1e-16
            );
        }
    }

    #[test]
    fn full_covariance_matches_pairwise_indicator_identity() {
        let counts = [3, 0, 2, 7];
        let scores = DMatrix::from_row_slice(
            3,
            4,
            &[1.0, -5.0, 0.0, -2.0, 0.0, 9.0, 3.0, 4.0, 5.0, 1.0, 7.0, 2.0],
        );
        let result = multinomial_scores(&counts, &scores, CovarianceEstimator::PlugIn).unwrap();
        // Independent identity: Cov(mean) = sum_{j<k} n_j n_k
        // (s_j-s_k)(s_j-s_k)^T / N^3. No empirical mean is used here.
        let mut expected = DMatrix::zeros(3, 3);
        for first in 0..counts.len() {
            for second in first + 1..counts.len() {
                let difference = scores.column(first) - scores.column(second);
                let weight = counts[first] as f64 * counts[second] as f64 / 12_f64.powi(3);
                expected += weight * &difference * difference.transpose();
            }
        }
        assert_relative_eq!(result.covariance_of_means, expected, epsilon = 1e-15);
    }

    #[test]
    fn outcome_permutation_and_zero_count_categories_preserve_estimates() {
        let scores = DMatrix::from_row_slice(2, 3, &[1.0, 0.0, -1.0, 0.0, 1.0, 1.0]);
        let result = multinomial_scores(&[2, 3, 5], &scores, CovarianceEstimator::PlugIn).unwrap();
        let permuted =
            DMatrix::from_row_slice(2, 4, &[-1.0, 1.0, f64::MAX, 0.0, 1.0, 0.0, -f64::MAX, 1.0]);
        let other =
            multinomial_scores(&[5, 2, 0, 3], &permuted, CovarianceEstimator::PlugIn).unwrap();
        assert_eq!(other.total_count, result.total_count);
        assert_relative_eq!(other.means, result.means, epsilon = 1e-15);
        assert_relative_eq!(
            other.covariance_of_means,
            result.covariance_of_means,
            epsilon = 1e-16
        );
    }

    #[test]
    fn affine_score_changes_transform_the_full_covariance() {
        let scores = DMatrix::from_row_slice(2, 3, &[1.0, 0.0, -1.0, 0.0, 1.0, 1.0]);
        let result =
            multinomial_scores(&[2, 3, 5], &scores, CovarianceEstimator::Unbiased).unwrap();
        let transform = DMatrix::from_row_slice(2, 2, &[2.0, -3.0, 1.0, 4.0]);
        let shift = DVector::from_vec(vec![10.0, -7.0]);
        let mut transformed_scores = &transform * scores;
        for mut column in transformed_scores.column_iter_mut() {
            column += &shift;
        }
        let transformed = multinomial_scores(
            &[2, 3, 5],
            &transformed_scores,
            CovarianceEstimator::Unbiased,
        )
        .unwrap();
        assert_relative_eq!(
            transformed.means,
            &transform * result.means + shift,
            epsilon = 1e-14
        );
        assert_relative_eq!(
            transformed.covariance_of_means,
            &transform * result.covariance_of_means * transform.transpose(),
            epsilon = 1e-14,
        );
    }

    #[test]
    fn large_common_offset_keeps_small_variance() {
        let offset = 2_f64.powi(50);
        let scores =
            DMatrix::from_row_slice(1, 4, &[offset, offset + 2.0, offset + 4.0, offset + 6.0]);
        let result =
            multinomial_scores(&[1, 1, 1, 1], &scores, CovarianceEstimator::PlugIn).unwrap();
        assert_eq!(result.means[0], offset + 3.0);
        assert_eq!(result.covariance_of_means[(0, 0)], 1.25);
    }

    #[test]
    fn rounded_mean_preserves_adjacent_float_variance() {
        let next = f64::from_bits(1.0_f64.to_bits() + 1);
        let scores = DMatrix::from_row_slice(1, 2, &[1.0, next]);
        let result = multinomial_scores(&[1, 1], &scores, CovarianceEstimator::PlugIn).unwrap();
        // The exact mean is 1 + 2^-53 and rounds to 1 under ties-to-even.
        // The pairwise identity gives (2^-52)^2 / 2^3 = 2^-107.
        assert_eq!(result.means[0], 1.0);
        assert_eq!(result.covariance_of_means[(0, 0)], 2_f64.powi(-107));
    }

    #[test]
    fn imbalanced_counts_keep_the_rare_outcome_mean() {
        // N = 2^53 and one rare outcome of score 3: the exact mean is 3 / 2^53,
        // and the exact plug-in variance of the mean is 9 (N - 1) / N^3.
        let scores = DMatrix::from_row_slice(1, 2, &[0.0, 3.0]);
        let counts = [MAX_EXACT_TOTAL_COUNT - 1, 1];
        let result = multinomial_scores(&counts, &scores, CovarianceEstimator::PlugIn).unwrap();
        let total = MAX_EXACT_TOTAL_COUNT as f64;
        assert_eq!(result.means[0], 3.0 / total);
        assert_relative_eq!(
            result.covariance_of_means[(0, 0)],
            9.0 * (total - 1.0) / (total * total * total),
            max_relative = 1e-15,
        );
    }

    #[test]
    fn imbalanced_counts_keep_the_rare_outcome_mean_in_either_order() {
        let total = MAX_EXACT_TOTAL_COUNT as f64;
        let scores = DMatrix::from_row_slice(1, 2, &[3.0, 0.0]);
        let counts = [1, MAX_EXACT_TOTAL_COUNT - 1];
        let result = multinomial_scores(&counts, &scores, CovarianceEstimator::PlugIn).unwrap();
        assert_eq!(result.means[0], 3.0 / total);
        assert_relative_eq!(
            result.covariance_of_means[(0, 0)],
            9.0 * (total - 1.0) / (total * total * total),
            max_relative = 1e-15,
        );
    }

    /// Outcome orders of three columns.
    const ORDERS: [[usize; 3]; 6] = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];

    fn permuted(
        counts: [u64; 3],
        scores: &DMatrix<f64>,
        order: [usize; 3],
    ) -> ([u64; 3], DMatrix<f64>) {
        let counts = order.map(|outcome| counts[outcome]);
        let scores = DMatrix::from_fn(scores.nrows(), 3, |row, column| {
            scores[(row, order[column])]
        });
        (counts, scores)
    }

    fn assert_estimate(result: &MultinomialScoreEstimate, means: [f64; 2], covariance: [f64; 3]) {
        assert_eq!(result.means[0], means[0]);
        assert_eq!(result.means[1], means[1]);
        for (entry, expected) in [(0, 0), (1, 0), (1, 1)].into_iter().zip(covariance) {
            assert_relative_eq!(
                result.covariance_of_means[entry],
                expected,
                max_relative = 1e-15,
            );
        }
        assert_eq!(
            result.covariance_of_means[(0, 1)],
            result.covariance_of_means[(1, 0)]
        );
    }

    #[test]
    fn mixed_scale_scores_keep_low_order_mean_and_covariance() {
        // N = 3 and p[j] = 1/3. Row means: (2^54 - 2^54 + 1) / 3 = 1/3 and 1/3.
        // Centered rows: [2^54 - 1/3, -2^54 - 1/3, 2/3] and [-1/3, -1/3, 2/3].
        // Plug-in covariance (1/9) sum_j c_x[j] c_y[j]:
        //   C00 = ((2^54 - 1/3)^2 + (2^54 + 1/3)^2 + 4/9) / 9 = 2^109/9 + 2/27,
        //   C01 = (-2^54/3 + 1/9 + 2^54/3 + 1/9 + 4/9) / 9 = 2/27,
        //   C11 = (1/9 + 1/9 + 4/9) / 9 = 2/27.
        // 2/27 lies below half an ulp of 2^109/9, so C00 rounds to 2^109/9.
        let large = 2_f64.powi(54);
        let scores = DMatrix::from_row_slice(2, 3, &[large, -large, 1.0, 0.0, 0.0, 1.0]);
        for order in ORDERS {
            let (counts, scores) = permuted([1, 1, 1], &scores, order);
            let result = multinomial_scores(&counts, &scores, CovarianceEstimator::PlugIn).unwrap();
            assert_estimate(
                &result,
                [1.0 / 3.0, 1.0 / 3.0],
                [2_f64.powi(109) / 9.0, 2.0 / 27.0, 2.0 / 27.0],
            );
        }
    }

    #[test]
    fn unequal_counts_with_mixed_scales_keep_low_order_terms() {
        // N = 20 and p = [3, 7, 10] / 20, so the rounded proportions are inexact.
        // Means: (21 - 21) 2^50 / 20 + 10/20 = 1/2 and 1/2.
        // Centered rows: [7 2^50 - 1/2, -3 2^50 - 1/2, 1/2] and [-1/2, -1/2, 1/2].
        // Centered moments sum_j p[j] c_x[j] c_y[j]:
        //   M00 = 0.15 (49 2^100 - 7 2^50 + 1/4) + 0.35 (9 2^100 + 3 2^50 + 1/4)
        //         + 0.125 = 10.5 2^100 + 1/4,
        //   M01 = -0.525 2^50 + 0.0375 + 0.525 2^50 + 0.0875 + 0.125 = 1/4,
        //   M11 = 1/4.
        // Plug-in covariance M / 20: C00 = 0.525 2^100 + 1/80, C01 = C11 = 1/80.
        let large = 2_f64.powi(50);
        let scores =
            DMatrix::from_row_slice(2, 3, &[7.0 * large, -3.0 * large, 1.0, 0.0, 0.0, 1.0]);
        for order in ORDERS {
            let (counts, scores) = permuted([3, 7, 10], &scores, order);
            let result = multinomial_scores(&counts, &scores, CovarianceEstimator::PlugIn).unwrap();
            assert_estimate(
                &result,
                [0.5, 0.5],
                [0.525 * 2_f64.powi(100), 1.0 / 80.0, 1.0 / 80.0],
            );
        }
    }

    #[test]
    fn score_units_rescale_covariance_without_changing_the_law() {
        let base = DMatrix::from_row_slice(2, 3, &[1.0, 0.0, -1.0, 0.0, 1.0, 1.0]);
        let result = multinomial_scores(&[2, 3, 5], &base, CovarianceEstimator::PlugIn).unwrap();
        for scale in [1e-120, 1e120] {
            let scaled =
                multinomial_scores(&[2, 3, 5], &(&base * scale), CovarianceEstimator::PlugIn)
                    .unwrap();
            assert_relative_eq!(scaled.means / scale, result.means, epsilon = 1e-15);
            assert_relative_eq!(
                scaled.covariance_of_means / scale / scale,
                result.covariance_of_means,
                epsilon = 1e-15,
            );
        }
    }

    #[test]
    fn count_scaling_precedes_squaring_large_scores() {
        let scores = DMatrix::from_row_slice(1, 2, &[-1e160, 1e160]);
        let counts = [MAX_EXACT_TOTAL_COUNT / 2; 2];
        let result = multinomial_scores(&counts, &scores, CovarianceEstimator::PlugIn).unwrap();
        let standard_error = 1e160 / (MAX_EXACT_TOTAL_COUNT as f64).sqrt();
        assert_eq!(result.means[0], 0.0);
        assert_relative_eq!(
            result.covariance_of_means[(0, 0)],
            standard_error * standard_error,
            max_relative = 1e-15,
        );
    }

    #[test]
    fn constant_scores_and_a_single_observation_have_zero_plugin_variance() {
        let constant = DMatrix::from_row_slice(1, 2, &[f64::MAX, f64::MAX]);
        let result = multinomial_scores(&[1, 2], &constant, CovarianceEstimator::Unbiased).unwrap();
        assert_eq!(result.means[0], f64::MAX);
        assert_eq!(result.covariance_of_means[(0, 0)], 0.0);
        let single = DMatrix::from_row_slice(1, 2, &[5.0, -100.0]);
        let result = multinomial_scores(&[1, 0], &single, CovarianceEstimator::PlugIn).unwrap();
        assert_eq!(result.means[0], 5.0);
        assert_eq!(result.covariance_of_means[(0, 0)], 0.0);
        assert_eq!(
            multinomial_scores(&[1, 0], &single, CovarianceEstimator::Unbiased),
            Err(MeasurementScoreError::InsufficientCount),
        );
    }

    #[test]
    fn count_policy_accepts_exact_boundary_and_rejects_larger_totals() {
        let scores = DMatrix::from_row_slice(1, 2, &[-1.0, 1.0]);
        let result = multinomial_scores(
            &[MAX_EXACT_TOTAL_COUNT / 2; 2],
            &scores,
            CovarianceEstimator::PlugIn,
        )
        .unwrap();
        assert_relative_eq!(
            result.covariance_of_means[(0, 0)],
            1.0 / MAX_EXACT_TOTAL_COUNT as f64,
            max_relative = 1e-15,
        );
        assert_eq!(
            multinomial_scores(
                &[MAX_EXACT_TOTAL_COUNT, 1],
                &scores,
                CovarianceEstimator::PlugIn
            ),
            Err(MeasurementScoreError::CountPrecisionLoss),
        );
        assert_eq!(
            multinomial_scores(&[u64::MAX, 1], &scores, CovarianceEstimator::PlugIn),
            Err(MeasurementScoreError::CountOverflow),
        );
    }

    #[test]
    fn malformed_and_nonfinite_inputs_are_rejected() {
        let scores = DMatrix::from_row_slice(1, 2, &[0.0, 1.0]);
        for (counts, expected) in [
            (&[][..], MeasurementScoreError::EmptyInput),
            (&[1][..], MeasurementScoreError::DimensionMismatch),
            (&[0, 0][..], MeasurementScoreError::ZeroTotalCount),
        ] {
            assert_eq!(
                multinomial_scores(counts, &scores, CovarianceEstimator::PlugIn),
                Err(expected)
            );
        }
        assert_eq!(
            multinomial_scores(&[1, 2], &DMatrix::zeros(0, 2), CovarianceEstimator::PlugIn),
            Err(MeasurementScoreError::EmptyInput),
        );
        for invalid in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            let invalid_scores = DMatrix::from_row_slice(1, 2, &[1.0, invalid]);
            assert_eq!(
                multinomial_scores(&[1, 0], &invalid_scores, CovarianceEstimator::PlugIn),
                Err(MeasurementScoreError::NonFiniteScore),
            );
        }
    }

    #[test]
    fn overflow_and_underflow_never_report_zero_uncertainty() {
        for scores in [
            DMatrix::from_row_slice(1, 2, &[-f64::MAX, f64::MAX]),
            DMatrix::from_row_slice(1, 2, &[0.0, 1e-200]),
        ] {
            assert_eq!(
                multinomial_scores(&[1, 1], &scores, CovarianceEstimator::PlugIn),
                Err(MeasurementScoreError::Arithmetic),
            );
        }
    }
}
