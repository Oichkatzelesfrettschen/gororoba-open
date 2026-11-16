// SPDX-License-Identifier: MIT
//! Partial-qubit compatibility under a declared Pauli-readout model.
//!
//! Separate X/Y binomial records do not measure Z. Coordinate confidence
//! bounds apply to outcome means; interpreting them as Pauli expectations
//! additionally assumes a common prepared state and calibrated measurements.
//! No function here submits circuits, supplies missing observations, or
//! assigns a prior to the unknown Z component.

use std::{error::Error, fmt};

const MAX_EXACT_COUNT: u64 = (1_u64 << 53) - 1;

/// Invalid input or failure to bracket the constrained likelihood optimum.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CompatibilityError {
    /// Counts are empty, outside support, or not exactly representable in f64.
    Counts,
    /// An interval is unordered, non-finite, or outside expectation support.
    Interval,
    /// Family size or familywise failure probability is invalid.
    Coverage,
    /// The constrained estimator did not produce a finite bracket.
    Convergence,
}

impl fmt::Display for CompatibilityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Counts => "invalid binomial counts",
            Self::Interval => "invalid expectation interval",
            Self::Coverage => "invalid simultaneous-coverage contract",
            Self::Convergence => "constrained likelihood bracket failed",
        })
    }
}
impl Error for CompatibilityError {}

/// A closed, validated interval in [-1, 1].
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ExpectationInterval {
    lower: f64,
    upper: f64,
}

impl ExpectationInterval {
    /// Construct a finite ordered interval.
    ///
    /// # Errors
    /// Returns `CompatibilityError::Interval` outside the stated domain.
    pub fn new(lower: f64, upper: f64) -> Result<Self, CompatibilityError> {
        if !lower.is_finite() || !upper.is_finite() || lower < -1.0 || upper > 1.0 || lower > upper {
            return Err(CompatibilityError::Interval);
        }
        Ok(Self { lower, upper })
    }

    /// Return the closed endpoints, without selecting an estimate.
    pub fn endpoints(self) -> [f64; 2] {
        [self.lower, self.upper]
    }

    fn nearest_zero(self) -> f64 {
        0.0_f64.clamp(self.lower, self.upper)
    }
}

fn expectation(zeros: u64, shots: u64) -> Result<f64, CompatibilityError> {
    if shots == 0 || zeros > shots || shots > MAX_EXACT_COUNT {
        return Err(CompatibilityError::Counts);
    }
    Ok(2.0 * zeros as f64 / shots as f64 - 1.0)
}

/// Simultaneous Hoeffding interval for one expectation in a fixed family.
///
/// The union bound needs independent stationary repetitions within each
/// circuit; it does not need independence between different coordinates.
/// Filtering the display must not reduce `family_size`.
///
/// # Errors
/// Returns `Counts` for invalid counts and `Coverage` for a zero or
/// unrepresentable family size or a failure probability outside (0, 1).
pub fn simultaneous_coordinate(
    zeros: u64,
    shots: u64,
    family_size: u64,
    alpha: f64,
) -> Result<ExpectationInterval, CompatibilityError> {
    let point = expectation(zeros, shots)?;
    if family_size == 0
        || family_size > MAX_EXACT_COUNT
        || !alpha.is_finite()
        || !(0.0..1.0).contains(&alpha)
        || alpha == 0.0
    {
        return Err(CompatibilityError::Coverage);
    }
    // Log-domain evaluation avoids overflow for very small positive alpha.
    let log_term = (2.0 * family_size as f64).ln() - alpha.ln();
    let radius = (2.0 * log_term / shots as f64).sqrt();
    ExpectationInterval::new((point - radius).max(-1.0), (point + radius).min(1.0))
}

/// Project an X/Y rectangle intersected with the Bloch ball onto Z.
///
/// `None` denotes an empty intersection. `Some` gives possible Z values,
/// not a measured Z interval, purity estimate, or posterior distribution.
pub fn compatible_z(x: ExpectationInterval, y: ExpectationInterval) -> Option<ExpectationInterval> {
    let minimum_radius = x.nearest_zero().hypot(y.nearest_zero());
    if minimum_radius > 1.0 {
        return None;
    }
    let extent = ((1.0 - minimum_radius) * (1.0 + minimum_radius))
        .max(0.0)
        .sqrt();
    Some(ExpectationInterval {
        lower: -extent,
        upper: extent,
    })
}

/// A transverse likelihood estimate; deliberately contains no inferred Z.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct TransverseEstimate {
    /// Raw count-derived expectation pair, preserved even outside the disk.
    pub raw: [f64; 2],
    /// Likelihood-maximizing X/Y pair constrained to the unit disk.
    pub fitted: [f64; 2],
    /// Whether the disk constraint changed the raw point.
    pub constrained: bool,
}

fn axis(raw: f64, shots: f64, multiplier: f64) -> f64 {
    let a = raw.abs();
    if a == 0.0 {
        return 0.0;
    }
    if a == 1.0 && multiplier <= shots / 2.0 {
        return raw.signum();
    }
    let (mut low, mut high) = (0.0, a);
    for _ in 0..80 {
        let t = (low + high) / 2.0;
        let derivative = if a == 1.0 {
            shots / (1.0 + t) - multiplier * t
        } else {
            shots * (a - t) / (1.0 - t * t) - multiplier * t
        };
        if derivative > 0.0 {
            low = t;
        } else {
            high = t;
        }
    }
    raw.signum() * (low + high) / 2.0
}

/// Maximize separate binomial X/Y likelihoods over x*x + y*y <= 1.
///
/// The multiplier solves the concave disk-constrained problem; unequal shot
/// counts generally make radial projection incorrect. The raw point is kept.
///
/// # Errors
/// Returns `Counts` for invalid counts or `Convergence` when no finite
/// multiplier bracket is found within the bounded search.
pub fn constrained_xy(
    x_zeros: u64,
    x_shots: u64,
    y_zeros: u64,
    y_shots: u64,
) -> Result<TransverseEstimate, CompatibilityError> {
    let raw = [expectation(x_zeros, x_shots)?, expectation(y_zeros, y_shots)?];
    if raw[0].hypot(raw[1]) <= 1.0 {
        return Ok(TransverseEstimate {
            raw,
            fitted: raw,
            constrained: false,
        });
    }
    let coordinates = |multiplier| {
        [
            axis(raw[0], x_shots as f64, multiplier),
            axis(raw[1], y_shots as f64, multiplier),
        ]
    };
    let (mut low, mut high) = (0.0, x_shots.max(y_shots) as f64);
    let mut bracketed = false;
    for _ in 0..64 {
        let p = coordinates(high);
        if p[0].hypot(p[1]) <= 1.0 {
            bracketed = true;
            break;
        }
        high *= 2.0;
    }
    if !bracketed || !high.is_finite() {
        return Err(CompatibilityError::Convergence);
    }
    for _ in 0..80 {
        let middle = (low + high) / 2.0;
        let p = coordinates(middle);
        if p[0].hypot(p[1]) > 1.0 {
            low = middle;
        } else {
            high = middle;
        }
    }
    Ok(TransverseEstimate {
        raw,
        fitted: coordinates(high),
        constrained: true,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_z_remains_an_interval() {
        let point = ExpectationInterval::new(0.0, 0.0).unwrap();
        assert_eq!(compatible_z(point, point).unwrap().endpoints(), [-1.0, 1.0]);
    }

    #[test]
    fn positivity_can_be_empty_or_tangent() {
        let large = ExpectationInterval::new(0.9, 1.0).unwrap();
        assert!(compatible_z(large, large).is_none());
        let one = ExpectationInterval::new(1.0, 1.0).unwrap();
        let zero = ExpectationInterval::new(0.0, 0.0).unwrap();
        assert_eq!(compatible_z(one, zero).unwrap().endpoints(), [-0.0, 0.0]);
    }

    #[test]
    fn interval_rejects_nan_and_reversed_order() {
        assert!(ExpectationInterval::new(f64::NAN, 1.0).is_err());
        assert!(ExpectationInterval::new(0.8, 0.7).is_err());
    }

    #[test]
    fn fixed_family_matches_coordinate_contract() {
        let bounds = simultaneous_coordinate(512, 1024, 52, 0.05)
            .unwrap()
            .endpoints();
        assert!((bounds[1] - 0.1221561114790031).abs() < 1e-14);
    }

    #[test]
    fn invalid_count_and_coverage_contracts_fail() {
        assert!(constrained_xy(1, 0, 1, 1).is_err());
        assert!(simultaneous_coordinate(1, 1, 0, 0.05).is_err());
        assert!(simultaneous_coordinate(1, 1, 1, 0.0).is_err());
        assert!(constrained_xy(0, u64::MAX, 1, 1).is_err());
    }

    #[test]
    fn symmetric_mle_has_equal_coordinates() {
        let result = constrained_xy(10, 10, 10, 10).unwrap();
        assert!(result.constrained);
        for value in result.fitted {
            assert!((value - std::f64::consts::FRAC_1_SQRT_2).abs() < 1e-14);
        }
    }

    #[test]
    fn unequal_shots_preclude_radial_projection() {
        let result = constrained_xy(100, 100, 10, 10).unwrap();
        assert!(result.fitted[0] > result.fitted[1]);
        assert!((result.fitted[0].hypot(result.fitted[1]) - 1.0).abs() < 1e-14);
        assert_eq!(result.raw, [1.0, 1.0]);
    }

    #[test]
    fn interior_is_preserved() {
        let result = constrained_xy(6, 10, 7, 10).unwrap();
        assert!(!result.constrained);
        assert_eq!(result.raw, result.fitted);
    }
}
