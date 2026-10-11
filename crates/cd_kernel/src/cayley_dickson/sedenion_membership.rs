//! Separate exact sedenion membership from numerical proximity.
//!
//! Write `v = (x_1 + u, x_2 + w)` with imaginary octonions `u,w`.
//! A nonzero sedenion is a zero divisor precisely when `x_1=x_2=0`,
//! `|u|^2=|w|^2`, and `<u,w>=0`. Equal norms alone omit two scalar
//! constraints and orthogonality. These criteria apply to 16 coordinates;
//! other Cayley-Dickson dimensions require a multiplication-matrix kernel.

use num_rational::BigRational;
use num_traits::Zero;
use thiserror::Error;

/// A domain failure, distinct from a valid element outside the zero locus.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum SedenionDomainError {
    #[error("sedenion membership requires 16 coordinates, received {actual}")]
    Dimension { actual: usize },
    #[error("coordinate {index} is nonfinite")]
    NonfiniteCoordinate { index: usize },
    #[error("exact coordinate {index} has a zero denominator")]
    InvalidRationalCoordinate { index: usize },
    #[error("the zero vector has no projective proximity to the nonzero zero-divisor locus")]
    ZeroVector,
    #[error("proximity thresholds must be finite and satisfy 0 <= near < separated")]
    InvalidThresholds,
}

/// Exact component constraints; the zero vector satisfies these equations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSedenionConstraints {
    pub first_scalar: BigRational,
    pub second_scalar: BigRational,
    pub first_imaginary_norm_squared: BigRational,
    pub second_imaginary_norm_squared: BigRational,
    pub imaginary_inner_product: BigRational,
}

impl ExactSedenionConstraints {
    /// The quartic `s^2 + 2s(A+B) + (A-B)^2 + 4 gamma^2`.
    pub fn d2(&self) -> BigRational {
        let scalar_norm_squared =
            &self.first_scalar * &self.first_scalar + &self.second_scalar * &self.second_scalar;
        let imaginary_sum =
            &self.first_imaginary_norm_squared + &self.second_imaginary_norm_squared;
        let imaginary_difference =
            &self.first_imaginary_norm_squared - &self.second_imaginary_norm_squared;
        &scalar_norm_squared * &scalar_norm_squared
            + BigRational::from_integer(2.into()) * scalar_norm_squared * imaginary_sum
            + &imaginary_difference * &imaginary_difference
            + BigRational::from_integer(4.into())
                * &self.imaginary_inner_product
                * &self.imaginary_inner_product
    }

    pub fn satisfies_component_constraints(&self) -> bool {
        self.first_scalar.is_zero()
            && self.second_scalar.is_zero()
            && self.first_imaginary_norm_squared == self.second_imaginary_norm_squared
            && self.imaginary_inner_product.is_zero()
    }
}

/// Compute exact constraints without floating-point conversion or tolerance.
pub fn sedenion_constraints_exact(
    coordinates: &[BigRational],
) -> Result<ExactSedenionConstraints, SedenionDomainError> {
    check_dimension(coordinates.len())?;
    if let Some(index) = coordinates.iter().position(|value| value.denom().is_zero()) {
        return Err(SedenionDomainError::InvalidRationalCoordinate { index });
    }
    let squared_norm = |values: &[BigRational]| values.iter().map(|value| value * value).sum();
    Ok(ExactSedenionConstraints {
        first_scalar: coordinates[0].clone(),
        second_scalar: coordinates[8].clone(),
        first_imaginary_norm_squared: squared_norm(&coordinates[1..8]),
        second_imaginary_norm_squared: squared_norm(&coordinates[9..16]),
        imaginary_inner_product: coordinates[1..8]
            .iter()
            .zip(&coordinates[9..16])
            .map(|(first, second)| first * second)
            .sum(),
    })
}

/// Exact membership in the nonzero sedenion zero-divisor locus over Q.
///
/// Rational coordinates embed in the reals. Zero returns `Ok(false)`;
/// dimensions other than 16 return an error, even when a zero-padded vector
/// happens to describe a sedenion subalgebra.
pub fn sedenion_membership_exact(coordinates: &[BigRational]) -> Result<bool, SedenionDomainError> {
    let constraints = sedenion_constraints_exact(coordinates)?;
    Ok(coordinates.iter().any(|value| !value.is_zero())
        && constraints.satisfies_component_constraints())
}

/// Numerical residual thresholds, in dimensionless unit-input coordinates.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SedenionProximityThresholds {
    pub near: f64,
    pub separated: f64,
}

/// Numerical classification; `Near` establishes proximity only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SedenionProximityClass {
    Near,
    Indeterminate,
    Separated,
}

/// Absolute component residuals evaluated after unit Euclidean normalization.
///
/// The scalar entries are `|x_1|/||v||` and `|x_2|/||v||`;
/// `equal_norm` is `|A-B|/||v||^2`, and `orthogonality` is
/// `|gamma|/||v||^2`. Their maximum is a constraint residual, not a
/// geometric distance or a smoothness test. The gradient of D_2 vanishes
/// on its zero locus, so D_2 alone cannot test regularity.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SedenionComponentResiduals {
    pub first_scalar: f64,
    pub second_scalar: f64,
    pub equal_norm: f64,
    pub orthogonality: f64,
}

impl SedenionComponentResiduals {
    pub fn maximum(self) -> f64 {
        self.first_scalar
            .max(self.second_scalar)
            .max(self.equal_norm)
            .max(self.orthogonality)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SedenionProximity {
    pub classification: SedenionProximityClass,
    pub residuals: SedenionComponentResiduals,
    /// `D_2(v)/||v||^4`; unrelated to a block-encoding operator scale.
    pub normalized_d2: f64,
    /// Absolute numerical guard band used at each classification boundary.
    pub roundoff_allowance: f64,
}

/// Classify normalized constraint residuals, with an explicit undecided band.
///
/// Division by the largest coordinate precedes every square; unit-input
/// normalization therefore works for finite subnormal and near-maximum inputs.
/// A fixed `128*EPSILON` absolute guard widens each threshold boundary.
/// The guard is a numerical policy, not an outward-rounded interval certificate.
/// `Near` requires `maximum + guard <= near`; `Separated` requires
/// `maximum - guard >= separated`. Remaining cases are `Indeterminate`.
/// Thresholds express an application tolerance, never an exact membership
/// certificate. Nonfinite inputs, zero inputs, and wrong dimensions fail.
pub fn sedenion_proximity(
    coordinates: &[f64],
    thresholds: SedenionProximityThresholds,
) -> Result<SedenionProximity, SedenionDomainError> {
    validate_finite_sedenion(coordinates)?;
    if !thresholds.near.is_finite()
        || !thresholds.separated.is_finite()
        || thresholds.near < 0.0
        || thresholds.near >= thresholds.separated
    {
        return Err(SedenionDomainError::InvalidThresholds);
    }
    let scale = coordinates
        .iter()
        .map(|value| value.abs())
        .fold(0.0, f64::max);
    if scale == 0.0 {
        return Err(SedenionDomainError::ZeroVector);
    }
    let scaled: [f64; 16] = std::array::from_fn(|index| coordinates[index] / scale);
    let scaled_norm = scaled.iter().map(|value| value * value).sum::<f64>().sqrt();
    let unit: [f64; 16] = std::array::from_fn(|index| scaled[index] / scaled_norm);
    let first_norm: f64 = unit[1..8].iter().map(|value| value * value).sum();
    let second_norm: f64 = unit[9..16].iter().map(|value| value * value).sum();
    let inner: f64 = unit[1..8]
        .iter()
        .zip(&unit[9..16])
        .map(|(first, second)| first * second)
        .sum();
    let scalar_norm = unit[0] * unit[0] + unit[8] * unit[8];
    let residuals = SedenionComponentResiduals {
        first_scalar: unit[0].abs(),
        second_scalar: unit[8].abs(),
        equal_norm: (first_norm - second_norm).abs(),
        orthogonality: inner.abs(),
    };
    let roundoff_allowance = 128.0 * f64::EPSILON;
    let classification = if residuals.maximum() + roundoff_allowance <= thresholds.near {
        SedenionProximityClass::Near
    } else if residuals.maximum() - roundoff_allowance >= thresholds.separated {
        SedenionProximityClass::Separated
    } else {
        SedenionProximityClass::Indeterminate
    };
    Ok(SedenionProximity {
        classification,
        residuals,
        normalized_d2: scalar_norm * scalar_norm
            + 2.0 * scalar_norm * (first_norm + second_norm)
            + (first_norm - second_norm).powi(2)
            + 4.0 * inner * inner,
        roundoff_allowance,
    })
}

fn check_dimension(actual: usize) -> Result<(), SedenionDomainError> {
    if actual == 16 {
        Ok(())
    } else {
        Err(SedenionDomainError::Dimension { actual })
    }
}

pub(super) fn validate_finite_sedenion(coordinates: &[f64]) -> Result<(), SedenionDomainError> {
    check_dimension(coordinates.len())?;
    if let Some(index) = coordinates.iter().position(|value| !value.is_finite()) {
        return Err(SedenionDomainError::NonfiniteCoordinate { index });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exact_pair(first: usize, second: usize) -> [BigRational; 16] {
        std::array::from_fn(|index| {
            BigRational::from_integer(i32::from(index == first || index == second).into())
        })
    }

    fn thresholds() -> SedenionProximityThresholds {
        SedenionProximityThresholds {
            near: 1e-12,
            separated: 1e-10,
        }
    }

    #[test]
    fn exact_membership_checks_scalars_parallel_halves_and_nonzero() {
        for pair in [(0, 9), (1, 9), (1, 8)] {
            let coordinates = exact_pair(pair.0, pair.1);
            assert!(!sedenion_membership_exact(&coordinates).unwrap());
            assert_eq!(
                sedenion_constraints_exact(&coordinates).unwrap().d2(),
                BigRational::from_integer(4.into())
            );
        }
        let mut member = exact_pair(1, 10);
        let rational_scale = BigRational::new(7.into(), 13.into());
        for value in &mut member {
            *value *= &rational_scale;
        }
        assert!(sedenion_membership_exact(&member).unwrap());
        assert!(sedenion_constraints_exact(&member).unwrap().d2().is_zero());
        let zero: [BigRational; 16] = std::array::from_fn(|_| BigRational::zero());
        assert!(!sedenion_membership_exact(&zero).unwrap());
        assert!(matches!(
            sedenion_membership_exact(&member[..8]),
            Err(SedenionDomainError::Dimension { actual: 8 })
        ));
        member[3] = BigRational::new_raw(1.into(), 0.into());
        assert_eq!(
            sedenion_membership_exact(&member),
            Err(SedenionDomainError::InvalidRationalCoordinate { index: 3 })
        );
    }

    #[test]
    fn exact_membership_covers_all_84_standard_factors() {
        let mut count = 0;
        for first_index in 1..8 {
            for second_index in 9..16 {
                if second_index == first_index + 8 {
                    continue;
                }
                for sign in [-1, 1] {
                    let mut coordinates = exact_pair(first_index, second_index);
                    coordinates[second_index] = BigRational::from_integer(sign.into());
                    assert!(sedenion_membership_exact(&coordinates).unwrap());
                    assert!(
                        sedenion_constraints_exact(&coordinates)
                            .unwrap()
                            .d2()
                            .is_zero()
                    );
                    count += 1;
                }
            }
        }
        assert_eq!(count, 84);
    }

    #[test]
    fn compatibility_functions_reject_invalid_domains_and_zero_membership() {
        use crate::cayley_dickson::{is_zero_divisor_koebisu, koebisu_d2};

        for dimension in [0, 8, 15, 17, 32] {
            let coordinates = vec![1.0; dimension];
            assert!(koebisu_d2(&coordinates).is_nan());
            assert!(!is_zero_divisor_koebisu(&coordinates, 1e-12));
        }
        assert_eq!(koebisu_d2(&[0.0; 16]), 0.0);
        assert!(!is_zero_divisor_koebisu(&[0.0; 16], 1e-12));
        for first_index in [0, 1] {
            let mut coordinates = [0.0; 16];
            coordinates[first_index] = 1.0;
            coordinates[9] = 1.0;
            assert_eq!(koebisu_d2(&coordinates), 4.0);
            assert!(!is_zero_divisor_koebisu(&coordinates, 1e-12));
        }
        let mut nonfinite = [0.0; 16];
        nonfinite[9] = f64::NAN;
        assert!(koebisu_d2(&nonfinite).is_nan());
        assert!(!is_zero_divisor_koebisu(&nonfinite, 1e-12));
    }

    #[test]
    fn numerical_proximity_is_scale_invariant_and_rejects_counterexamples() {
        for scale in [f64::from_bits(1), 1e-300, 1.0, 1e300, f64::MAX, -f64::MAX] {
            for (first, second, expected) in [
                (1, 10, SedenionProximityClass::Near),
                (0, 9, SedenionProximityClass::Separated),
                (1, 9, SedenionProximityClass::Separated),
            ] {
                let mut coordinates = [0.0; 16];
                coordinates[first] = scale;
                coordinates[second] = scale;
                let proximity = sedenion_proximity(&coordinates, thresholds()).unwrap();
                assert_eq!(proximity.classification, expected);
                assert!(proximity.normalized_d2.is_finite());
            }
        }
    }

    #[test]
    fn numerical_proximity_retains_indeterminate_region_and_domain_errors() {
        let mut coordinates = [0.0; 16];
        coordinates[1] = 1.0;
        coordinates[10] = 1.0;
        coordinates[0] = 1e-11;
        assert_eq!(
            sedenion_proximity(&coordinates, thresholds())
                .unwrap()
                .classification,
            SedenionProximityClass::Indeterminate
        );
        for dimension in [0, 8, 15, 17, 32] {
            assert_eq!(
                sedenion_proximity(&vec![1.0; dimension], thresholds()),
                Err(SedenionDomainError::Dimension { actual: dimension })
            );
        }
        assert_eq!(
            sedenion_proximity(&[0.0; 16], thresholds()),
            Err(SedenionDomainError::ZeroVector)
        );
        for invalid in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            coordinates[3] = invalid;
            assert_eq!(
                sedenion_proximity(&coordinates, thresholds()),
                Err(SedenionDomainError::NonfiniteCoordinate { index: 3 })
            );
        }
        assert_eq!(
            sedenion_proximity(
                &[1.0; 16],
                SedenionProximityThresholds {
                    near: 1.0,
                    separated: 1.0
                }
            ),
            Err(SedenionDomainError::InvalidThresholds)
        );
    }
}
