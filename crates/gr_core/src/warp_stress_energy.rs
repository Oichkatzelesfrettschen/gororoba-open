// SPDX-License-Identifier: MIT
//! Exact local source requirements for a stationary planar shift metric.
//!
//! With signature (-,+,+,+), x0 = c*t and spatial coordinates in one length
//! unit, consider ds^2 = -dx0^2 + (dx - B(y)*dx0)^2 + dy^2 + dz^2.
//! The Eulerian orthonormal frame has e_0 = (1,B,0,0) and spatial unit
//! coordinate vectors. Write q = dB/dy and r = d^2 B/dy^2. Direct contraction
//! of the Riemann tensor, with the convention of `crate::metric`, gives
//!
//! G_ab = [[-q^2/4, r/2, 0, 0], [r/2, -3*q^2/4, 0, 0],
//!         [0, 0, q^2/4, 0], [0, 0, 0, -q^2/4]], R = q^2/2.
//!
//! These are covariant orthonormal components. If lengths are metres,
//! G_ab is in m^-2 and the required SI source is T_ab = G_ab*c^4/(8*pi*G).
//! This is a local exact counterexample fixture, not a finite warp bubble,
//! a realizable material source, or an observed gravitational field.
//!
//! At r=0, ideal electromagnetic Casimir stress normal to x can match G_00
//! and both x and y pressures, but its positive z pressure has the opposite
//! sign from G_zz. Matching an energy density therefore does not suffice
//! to identify the complete source. The finite-difference curvature test
//! derives all components independently from the metric coefficients.
//!
//! References: Alcubierre (1994), Class. Quantum Grav. 11, L73, metric and
//! source construction; Brown and Maclay (1969), Phys. Rev. 184, 1272,
//! ideal-conductor electromagnetic stress tensor.

use crate::metric::{DIM, MetricComponents};

/// Exact curvature data in the Eulerian orthonormal frame.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PlanarShiftCurvature {
    /// Covariant Einstein tensor in inverse-length squared.
    pub einstein_orthonormal: MetricComponents,
    /// Ricci scalar in inverse-length squared.
    pub ricci_scalar: f64,
}

/// Failure to represent a requested planar-shift curvature.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlanarShiftTensorError {
    /// At least one derivative is NaN or infinite.
    NonFiniteDerivative,
    /// A nonzero tensor component underflows or a component overflows.
    NumericalRange,
}

impl std::fmt::Display for PlanarShiftTensorError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NonFiniteDerivative => {
                formatter.write_str("planar-shift derivatives must be finite")
            }
            Self::NumericalRange => {
                formatter.write_str("planar-shift curvature exceeds floating-point range")
            }
        }
    }
}

impl std::error::Error for PlanarShiftTensorError {}

/// Evaluate the complete local Einstein tensor for a stationary B(y) shift.
///
/// `first_derivative` is dB/dy in inverse-length and `second_derivative` is
/// d^2 B/dy^2 in inverse-length squared. B itself is dimensionless and drops
/// out of the Eulerian-frame result. Both derivatives must describe the same
/// smooth profile at the same point. The function specifies the gravitational
/// source required by that profile; it does not construct or validate matter.
///
/// # Errors
/// Returns [`PlanarShiftTensorError::NonFiniteDerivative`] for a nonfinite
/// derivative, or [`PlanarShiftTensorError::NumericalRange`] when a nonzero
/// component underflows to zero or any component overflows.
pub fn planar_shift_curvature(
    first_derivative: f64,
    second_derivative: f64,
) -> Result<PlanarShiftCurvature, PlanarShiftTensorError> {
    if !first_derivative.is_finite() || !second_derivative.is_finite() {
        return Err(PlanarShiftTensorError::NonFiniteDerivative);
    }
    // Squaring q/2 avoids an intermediate q^2 overflow when q^2/4 is finite.
    let quarter_gradient_squared = (0.5 * first_derivative).powi(2);
    let flux = 0.5 * second_derivative;
    let longitudinal_stress = -3.0 * quarter_gradient_squared;
    let ricci_scalar = 2.0 * quarter_gradient_squared;
    if !longitudinal_stress.is_finite()
        || !ricci_scalar.is_finite()
        || (first_derivative != 0.0 && quarter_gradient_squared == 0.0)
        || (second_derivative != 0.0 && flux == 0.0)
    {
        return Err(PlanarShiftTensorError::NumericalRange);
    }
    let mut einstein_orthonormal = [[0.0; DIM]; DIM];
    einstein_orthonormal[0][0] = -quarter_gradient_squared;
    einstein_orthonormal[0][1] = flux;
    einstein_orthonormal[1][0] = flux;
    einstein_orthonormal[1][1] = longitudinal_stress;
    einstein_orthonormal[2][2] = quarter_gradient_squared;
    einstein_orthonormal[3][3] = -quarter_gradient_squared;
    Ok(PlanarShiftCurvature {
        einstein_orthonormal,
        ricci_scalar,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::metric::{SpacetimeMetric, full_curvature};

    #[test]
    fn uniform_shift_is_flat() {
        let result = planar_shift_curvature(0.0, 0.0).unwrap();
        assert_eq!(result.einstein_orthonormal, [[0.0; DIM]; DIM]);
        assert_eq!(result.ricci_scalar, 0.0);
    }

    #[test]
    fn trace_and_momentum_follow_derivative_order() {
        let result = planar_shift_curvature(4.0, 6.0).unwrap();
        let expected = [
            [-4.0, 3.0, 0.0, 0.0],
            [3.0, -12.0, 0.0, 0.0],
            [0.0, 0.0, 4.0, 0.0],
            [0.0, 0.0, 0.0, -4.0],
        ];
        assert_eq!(result.einstein_orthonormal, expected);
        let trace = -expected[0][0] + expected[1][1] + expected[2][2] + expected[3][3];
        assert_eq!(trace, -result.ricci_scalar);
        let reversed_gradient = planar_shift_curvature(-4.0, 6.0).unwrap();
        assert_eq!(result, reversed_gradient);
        let reversed_curvature = planar_shift_curvature(4.0, -6.0).unwrap();
        assert_eq!(reversed_curvature.einstein_orthonormal[0][1], -3.0);
        assert_eq!(reversed_curvature.einstein_orthonormal[0][0], -4.0);
    }

    #[test]
    fn energy_density_match_leaves_a_stress_residual() {
        let required = planar_shift_curvature(2.0, 0.0).unwrap();
        // kappa*T for ideal conductor plates normal to x, with kappa*K=1.
        let casimir_source = [
            [-1.0, 0.0, 0.0, 0.0],
            [0.0, -3.0, 0.0, 0.0],
            [0.0, 0.0, 1.0, 0.0],
            [0.0, 0.0, 0.0, 1.0],
        ];
        assert_eq!(required.einstein_orthonormal[0][0], casimir_source[0][0]);
        assert_eq!(required.einstein_orthonormal[1][1], casimir_source[1][1]);
        assert_eq!(required.einstein_orthonormal[2][2], casimir_source[2][2]);
        assert_eq!(
            required.einstein_orthonormal[3][3] - casimir_source[3][3],
            -2.0
        );
    }

    #[test]
    fn rejects_nonfinite_and_unrepresentable_components() {
        for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert_eq!(
                planar_shift_curvature(value, 0.0).unwrap_err(),
                PlanarShiftTensorError::NonFiniteDerivative
            );
            assert_eq!(
                planar_shift_curvature(0.0, value).unwrap_err(),
                PlanarShiftTensorError::NonFiniteDerivative
            );
        }
        for value in [f64::MAX, f64::MIN_POSITIVE, f64::from_bits(1)] {
            assert_eq!(
                planar_shift_curvature(value, 0.0).unwrap_err(),
                PlanarShiftTensorError::NumericalRange
            );
        }
        assert_eq!(
            planar_shift_curvature(0.0, f64::from_bits(1)).unwrap_err(),
            PlanarShiftTensorError::NumericalRange
        );
        let result = planar_shift_curvature(1.4e154, f64::MAX).unwrap();
        assert!(result.ricci_scalar.is_finite());
        assert!(
            result
                .einstein_orthonormal
                .iter()
                .flatten()
                .all(|value| value.is_finite())
        );
    }

    struct QuadraticPlanarShift;

    impl SpacetimeMetric for QuadraticPlanarShift {
        fn metric_components(&self, point: &[f64; DIM]) -> MetricComponents {
            let y = point[2];
            let b = 0.2 + 0.4 * y - 0.15 * y * y;
            [
                [-1.0 + b * b, -b, 0.0, 0.0],
                [-b, 1.0, 0.0, 0.0],
                [0.0, 0.0, 1.0, 0.0],
                [0.0, 0.0, 0.0, 1.0],
            ]
        }
    }

    #[test]
    fn full_metric_curvature_matches_every_orthonormal_component() {
        // The generic curvature engine uses a polar-coordinate step rule for
        // index 2; y=0.7 keeps this Cartesian fixture away from its zero step.
        let point = [0.0, 0.0, 0.7, 0.0];
        let curvature = full_curvature(&QuadraticPlanarShift, &point);
        let y = point[2];
        let b = 0.2 + 0.4 * y - 0.15 * y * y;
        let q = 0.4 - 0.3 * y;
        let expected = planar_shift_curvature(q, -0.3).unwrap();
        // e_a^mu: the outer index names the orthonormal basis vector.
        let frame = [
            [1.0, b, 0.0, 0.0],
            [0.0, 1.0, 0.0, 0.0],
            [0.0, 0.0, 1.0, 0.0],
            [0.0, 0.0, 0.0, 1.0],
        ];
        for (a, frame_a) in frame.iter().enumerate() {
            for (b, frame_b) in frame.iter().enumerate() {
                let mut component = 0.0;
                for (mu, &basis_a) in frame_a.iter().enumerate() {
                    for (nu, &basis_b) in frame_b.iter().enumerate() {
                        let coordinate_component = curvature.ricci[mu][nu]
                            - 0.5 * curvature.g[mu][nu] * curvature.ricci_scalar;
                        component += basis_a * basis_b * coordinate_component;
                    }
                }
                assert!(
                    (component - expected.einstein_orthonormal[a][b]).abs() < 2e-4,
                    "G_hat[{a}][{b}] numerical={component}, exact={}",
                    expected.einstein_orthonormal[a][b]
                );
            }
        }
        assert!((curvature.ricci_scalar - expected.ricci_scalar).abs() < 2e-4);
    }
}
