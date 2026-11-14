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
//! Means use offset centering and compensated sums. Covariance uses a Gram
//! matrix of centered scores weighted by `sqrt(p[j] / denominator)`, so a large
//! score is reduced by the sample-size factor before it is squared. Arithmetic
//! errors include nonfinite intermediates and nonzero products that underflow
//! to zero; such failures never silently report exact zero uncertainty.

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

/// Neumaier compensated summation preserves small terms beside large offsets.
fn compensated_sum(
    terms: impl Iterator<Item = Result<f64, MeasurementScoreError>>,
) -> Result<f64, MeasurementScoreError> {
    let mut sum: f64 = 0.0;
    let mut correction: f64 = 0.0;
    for term in terms {
        let term = term?;
        let next = finite(sum + term)?;
        let error = if sum.abs() >= term.abs() {
            (sum - next) + term
        } else {
            (term - next) + sum
        };
        correction = finite(correction + error)?;
        sum = next;
    }
    finite(sum + correction)
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
    let probabilities: Vec<f64> = counts
        .iter()
        .map(|count| *count as f64 / total_count as f64)
        .collect();
    let weights: Vec<f64> = probabilities
        .iter()
        .map(|probability| (probability / denominator).sqrt())
        .collect();
    let mut means = DVector::zeros(scores.nrows());
    let mut weighted_centered = DMatrix::zeros(scores.nrows(), scores.ncols());
    for row in 0..scores.nrows() {
        let mut minimum = f64::INFINITY;
        let mut maximum = f64::NEG_INFINITY;
        for (column, count) in counts.iter().enumerate() {
            if *count != 0 {
                minimum = minimum.min(scores[(row, column)]);
                maximum = maximum.max(scores[(row, column)]);
            }
        }
        // Same-sign ranges use subtraction to preserve small representable
        // differences beside a common offset. Opposite extremes use half sums.
        let range = maximum - minimum;
        let anchor = if range.is_finite() {
            minimum + range / 2.0
        } else {
            minimum / 2.0 + maximum / 2.0
        };
        let offsets: Vec<f64> = counts
            .iter()
            .enumerate()
            .map(|(column, count)| {
                if *count == 0 {
                    Ok(0.0)
                } else {
                    finite(scores[(row, column)] - anchor)
                }
            })
            .collect::<Result<_, _>>()?;
        let mean_offset = compensated_sum(
            offsets
                .iter()
                .zip(&probabilities)
                .map(|(offset, probability)| product(*offset, *probability)),
        )?;
        means[row] = finite(anchor + mean_offset)?;
        for (column, count) in counts.iter().enumerate() {
            if *count != 0 {
                let centered = finite(offsets[column] - mean_offset)?;
                weighted_centered[(row, column)] = product(centered, weights[column])?;
            }
        }
    }
    let mut covariance_of_means = DMatrix::zeros(scores.nrows(), scores.nrows());
    for row in 0..scores.nrows() {
        for column in 0..=row {
            let covariance = compensated_sum((0..counts.len()).map(|outcome| {
                product(
                    weighted_centered[(row, outcome)],
                    weighted_centered[(column, outcome)],
                )
            }))?;
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
