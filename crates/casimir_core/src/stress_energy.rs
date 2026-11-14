// SPDX-License-Identifier: GPL-2.0-or-later
//! Ideal electromagnetic parallel-plate stress in an orthonormal SI frame.
//!
//! Brown and Maclay, "Vacuum Stress between Conducting Plates: An Image
//! Solution", Phys. Rev. 184, 1272 (1969), DOI:10.1103/PhysRev.184.1272,
//! give the zero-temperature vacuum stress between infinite perfect conductors.
//! With signature (-,+,+,+) and plate normal z, the covariant tensor is
//! K * diag(-1, 1, 1, -3), where K = pi^2*hbar*c/(720*a^4).
//! Its components have units J/m^3, numerically equal to Pa for stresses.
//!
//! The reference excludes the plates, supports, exterior field, material
//! response, temperature and edge corrections. A negative vacuum contribution
//! does not determine the total mass-energy or spacetime of an apparatus.
//!
//! The electromagnetic stress reference is separate from scalar worldline
//! sampling. Gies and Klingmueller, "Worldline algorithms for Casimir
//! configurations", Phys. Rev. D 74, 045002 (2006), p. 8, footnote 3, distinguish
//! the loop-center effective-action integrand from physical local T_00 by a
//! total derivative. Their scalar boundary calculation also does not generally
//! determine the electromagnetic result for curved boundaries.

use crate::energy::casimir_parallel_plates_exact;

// The SI definitions fix h and c exactly; hbar = h/(2*pi).
const HBAR_C_J_M: f64 = 6.626_070_15e-34 / std::f64::consts::TAU * 299_792_458.0;

/// Axis normal to the two conducting plates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlateNormal {
    X,
    Y,
    Z,
}

impl PlateNormal {
    fn index(self) -> usize {
        match self {
            Self::X => 0,
            Self::Y => 1,
            Self::Z => 2,
        }
    }
}

/// Input or arithmetic error in the ideal electromagnetic stress reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CasimirStressError {
    /// Plate separation is nonpositive or nonfinite.
    InvalidSeparation,
    /// A null-ray direction is zero or contains a nonfinite component.
    InvalidDirection,
    /// Observer velocity is nonfinite or has magnitude at least c.
    InvalidObserverVelocity,
    /// A required nonzero result underflows, or a result is nonfinite.
    NumericalRange,
}

impl std::fmt::Display for CasimirStressError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::InvalidSeparation => "plate separation must be finite and positive",
            Self::InvalidDirection => "null-ray direction must be finite and nonzero",
            Self::InvalidObserverVelocity => "observer velocity must be finite and subluminal",
            Self::NumericalRange => "electromagnetic stress result exceeds floating-point range",
        })
    }
}

impl std::error::Error for CasimirStressError {}

/// Validated vacuum contribution for infinite, zero-temperature perfect plates.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct IdealParallelPlateStress {
    separation_m: f64,
    normal: PlateNormal,
    magnitude_j_m3: f64,
    energy_per_area_j_m2: f64,
}

/// Construct the analytic electromagnetic reference with plate separation in m.
///
/// Repeated division preserves representable results when computing a^4 would
/// overflow. Arithmetic checks establish numerical representability; they do
/// not establish the physical accuracy of the ideal-conductor approximation.
///
/// # Errors
/// Returns `InvalidSeparation` for nonpositive or nonfinite separation.
/// Returns `NumericalRange` when the nonzero energy density or area energy
/// underflows, or when the energy density, area energy or pressure is nonfinite.
pub fn ideal_parallel_plate_stress_si(
    separation_m: f64,
    normal: PlateNormal,
) -> Result<IdealParallelPlateStress, CasimirStressError> {
    if !separation_m.is_finite() || separation_m <= 0.0 {
        return Err(CasimirStressError::InvalidSeparation);
    }
    let mut energy_per_area = -casimir_parallel_plates_exact(1.0) * HBAR_C_J_M;
    for _ in 0..3 {
        energy_per_area /= separation_m;
    }
    let magnitude = energy_per_area / separation_m;
    if !energy_per_area.is_finite()
        || energy_per_area <= 0.0
        || !magnitude.is_finite()
        || magnitude <= 0.0
        || !(3.0 * magnitude).is_finite()
    {
        return Err(CasimirStressError::NumericalRange);
    }
    Ok(IdealParallelPlateStress {
        separation_m,
        normal,
        magnitude_j_m3: magnitude,
        energy_per_area_j_m2: -energy_per_area,
    })
}

impl IdealParallelPlateStress {
    /// Distance between the plates in m.
    pub fn separation_m(self) -> f64 {
        self.separation_m
    }

    /// Principal axis normal to the conducting surfaces.
    pub fn normal(self) -> PlateNormal {
        self.normal
    }

    /// Energy density measured by an observer at rest relative to the plates.
    pub fn energy_density_j_m3(self) -> f64 {
        -self.magnitude_j_m3
    }

    /// Vacuum interaction energy per plate area, E/A = rho*a.
    pub fn energy_per_area_j_m2(self) -> f64 {
        self.energy_per_area_j_m2
    }

    /// Signed normal stress; a negative value gives an attractive plate force.
    pub fn normal_pressure_pa(self) -> f64 {
        -3.0 * self.magnitude_j_m3
    }

    /// Principal pressures along x, y and z.
    pub fn pressures_pa(self) -> [f64; 3] {
        let mut pressures = [self.magnitude_j_m3; 3];
        pressures[self.normal.index()] = self.normal_pressure_pa();
        pressures
    }

    /// Covariant orthonormal tensor in coordinate order (ct, x, y, z).
    pub fn tensor_j_m3(self) -> [[f64; 4]; 4] {
        let mut tensor = [[0.0; 4]; 4];
        tensor[0][0] = self.energy_density_j_m3();
        for (axis, pressure) in self.pressures_pa().into_iter().enumerate() {
            tensor[axis + 1][axis + 1] = pressure;
        }
        tensor
    }

    /// Lorentzian contraction -rho + p_x + p_y + p_z; zero up to roundoff.
    pub fn trace_j_m3(self) -> f64 {
        self.pressures_pa()
            .into_iter()
            .fold(-self.energy_density_j_m3(), |sum, pressure| sum + pressure)
    }

    /// T_ab k^a k^b for k=(1,n), with the supplied direction normalized to n.
    ///
    /// The analytic contraction -4*K*n_normal^2 avoids cancellation near a
    /// tangential ray. The normalization fixes the arbitrary null-vector scale,
    /// so reported contractions can be compared across directions.
    ///
    /// # Errors
    /// Returns `InvalidDirection` for a zero or nonfinite direction.
    /// Returns `NumericalRange` for overflow or when a nonzero contraction
    /// underflows, including loss of a nonzero normal component in normalization.
    pub fn null_contraction_j_m3(self, direction: [f64; 3]) -> Result<f64, CasimirStressError> {
        if direction.iter().any(|component| !component.is_finite()) {
            return Err(CasimirStressError::InvalidDirection);
        }
        let scale = direction
            .iter()
            .map(|component| component.abs())
            .fold(0.0, f64::max);
        if scale == 0.0 {
            return Err(CasimirStressError::InvalidDirection);
        }
        let scaled = direction.map(|component| component / scale);
        let norm = scaled[0].hypot(scaled[1]).hypot(scaled[2]);
        let normal_component = scaled[self.normal.index()] / norm;
        // Squaring a tiny direction first can underflow before K rescales it.
        // The equal factors also avoid an overflowing intermediate 4*K.
        let doubled_normal = 2.0 * normal_component;
        let contraction = (-self.magnitude_j_m3 * doubled_normal) * doubled_normal;
        if !contraction.is_finite() || (direction[self.normal.index()] != 0.0 && contraction == 0.0)
        {
            return Err(CasimirStressError::NumericalRange);
        }
        Ok(contraction)
    }

    /// T_ab u^a u^b for a timelike observer with spatial velocity v/c.
    ///
    /// u=gamma*(1,v/c) has norm -1. Factoring 1-|v/c|^2 retains accuracy near
    /// the light cone. The normal velocity controls the density change;
    /// tangential boosts preserve the parallel-plate vacuum density.
    ///
    /// # Errors
    /// Returns `InvalidObserverVelocity` for nonfinite velocity or speed at
    /// least c. Returns `NumericalRange` when the contracted density is
    /// nonfinite or a nonzero result underflows.
    pub fn observer_energy_density_j_m3(
        self,
        velocity_over_c: [f64; 3],
    ) -> Result<f64, CasimirStressError> {
        if velocity_over_c
            .iter()
            .any(|component| !component.is_finite())
        {
            return Err(CasimirStressError::InvalidObserverVelocity);
        }
        let speed = velocity_over_c[0]
            .hypot(velocity_over_c[1])
            .hypot(velocity_over_c[2]);
        if speed >= 1.0 {
            return Err(CasimirStressError::InvalidObserverVelocity);
        }
        let normal_velocity = velocity_over_c[self.normal.index()];
        let one_minus_speed_squared = (1.0 - speed) * (1.0 + speed);
        let factor = 1.0 + 4.0 * normal_velocity * normal_velocity / one_minus_speed_squared;
        let density = -self.magnitude_j_m3 * factor;
        if !density.is_finite() || density == 0.0 {
            return Err(CasimirStressError::NumericalRange);
        }
        Ok(density)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn electromagnetic_stresses_have_physical_sign_and_orientation() {
        for normal in [PlateNormal::X, PlateNormal::Y, PlateNormal::Z] {
            let stress = ideal_parallel_plate_stress_si(1e-6, normal).unwrap();
            assert_relative_eq!(
                stress.energy_density_j_m3(),
                -4.333_752_6e-4,
                max_relative = 1e-8
            );
            assert_eq!(stress.separation_m(), 1e-6);
            assert_eq!(stress.normal(), normal);
            assert!(stress.normal_pressure_pa() < 0.0);
            let tensor = stress.tensor_j_m3();
            for (row, entries) in tensor.iter().enumerate() {
                for (column, &value) in entries.iter().enumerate() {
                    if row != column {
                        assert_eq!(value, 0.0);
                    }
                }
            }
            for (axis, pressure) in stress.pressures_pa().into_iter().enumerate() {
                let expected = if axis == normal.index() {
                    3.0 * stress.energy_density_j_m3()
                } else {
                    -stress.energy_density_j_m3()
                };
                assert_eq!(pressure, expected);
                assert_eq!(tensor[axis + 1][axis + 1], pressure);
            }
            assert!(stress.trace_j_m3().abs() <= 4.0 * f64::EPSILON * stress.magnitude_j_m3);
        }
    }

    #[test]
    fn pressure_equals_negative_energy_area_derivative() {
        let separation = 2.5e-6;
        let step = separation * 1e-4;
        let at = |gap| ideal_parallel_plate_stress_si(gap, PlateNormal::Z).unwrap();
        let stress = at(separation);
        let pressure = -(at(separation + step).energy_per_area_j_m2()
            - at(separation - step).energy_per_area_j_m2())
            / (2.0 * step);
        assert_relative_eq!(pressure, stress.normal_pressure_pa(), max_relative = 1e-7);
        assert_relative_eq!(
            stress.energy_per_area_j_m2(),
            separation * stress.energy_density_j_m3(),
            max_relative = 4.0 * f64::EPSILON
        );
    }

    #[test]
    fn density_and_area_energy_have_distinct_dilation_powers() {
        let small = ideal_parallel_plate_stress_si(1e-6, PlateNormal::Z).unwrap();
        let large = ideal_parallel_plate_stress_si(2e-6, PlateNormal::Z).unwrap();
        assert_eq!(
            small.energy_density_j_m3(),
            16.0 * large.energy_density_j_m3()
        );
        assert_eq!(
            small.normal_pressure_pa(),
            16.0 * large.normal_pressure_pa()
        );
        assert_eq!(
            small.energy_per_area_j_m2(),
            8.0 * large.energy_per_area_j_m2()
        );
        let scalar = crate::energy::scalar_parallel_plates_exact(1e-6) * HBAR_C_J_M;
        assert_relative_eq!(
            small.energy_per_area_j_m2(),
            2.0 * scalar,
            max_relative = 1e-15
        );
    }

    #[test]
    fn null_direction_contractions_resolve_anisotropic_energy_condition() {
        let stress = ideal_parallel_plate_stress_si(1e-6, PlateNormal::Z).unwrap();
        let rho = stress.energy_density_j_m3();
        assert_eq!(stress.null_contraction_j_m3([1.0, 0.0, 0.0]).unwrap(), 0.0);
        assert_eq!(
            stress.null_contraction_j_m3([0.0, 0.0, 1.0]).unwrap(),
            4.0 * rho
        );
        assert_relative_eq!(
            stress.null_contraction_j_m3([3.0, 0.0, 4.0]).unwrap(),
            64.0 * rho / 25.0,
            max_relative = 1e-15
        );
        assert_relative_eq!(
            stress.null_contraction_j_m3([f64::MAX; 3]).unwrap(),
            4.0 * rho / 3.0,
            max_relative = 1e-15
        );
    }

    #[test]
    fn null_contraction_preserves_tiny_direction_with_large_density() {
        let stress = ideal_parallel_plate_stress_si(1e-57, PlateNormal::Z).unwrap();
        let contraction = stress.null_contraction_j_m3([1.0, 0.0, 1e-200]).unwrap();
        assert!(contraction.is_finite() && contraction < 0.0);
        assert_relative_eq!(
            (contraction * 1e200) / (stress.energy_density_j_m3() * 1e-200),
            4.0,
            max_relative = 1e-15
        );
    }

    #[test]
    fn observer_contraction_matches_tensor_and_boost_symmetries() {
        let stress = ideal_parallel_plate_stress_si(1e-6, PlateNormal::Z).unwrap();
        let rho = stress.energy_density_j_m3();
        assert_eq!(
            stress
                .observer_energy_density_j_m3([0.6, 0.0, 0.0])
                .unwrap(),
            rho
        );
        assert_relative_eq!(
            stress
                .observer_energy_density_j_m3([0.0, 0.0, 0.6])
                .unwrap(),
            3.25 * rho,
            max_relative = 1e-15
        );
        let velocity = [0.1, 0.2, -0.3];
        let gamma = (1.0_f64 - velocity.iter().map(|value| value * value).sum::<f64>())
            .sqrt()
            .recip();
        let observer = [
            gamma,
            gamma * velocity[0],
            gamma * velocity[1],
            gamma * velocity[2],
        ];
        let tensor = stress.tensor_j_m3();
        let direct: f64 = tensor
            .iter()
            .enumerate()
            .map(|(row, entries)| {
                entries
                    .iter()
                    .enumerate()
                    .map(|(column, value)| value * observer[row] * observer[column])
                    .sum::<f64>()
            })
            .sum();
        assert_relative_eq!(
            stress.observer_energy_density_j_m3(velocity).unwrap(),
            direct,
            max_relative = 1e-15
        );
    }

    #[test]
    fn invalid_separations_and_unrepresentable_stresses_are_rejected() {
        for separation in [0.0, -1.0, f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert_eq!(
                ideal_parallel_plate_stress_si(separation, PlateNormal::Z).unwrap_err(),
                CasimirStressError::InvalidSeparation
            );
        }
        for separation in [1e-100, 1e100, 1.5e-84] {
            assert_eq!(
                ideal_parallel_plate_stress_si(separation, PlateNormal::Z).unwrap_err(),
                CasimirStressError::NumericalRange
            );
        }
        let extreme = ideal_parallel_plate_stress_si(2e70, PlateNormal::Z).unwrap();
        assert!(extreme.energy_density_j_m3() < 0.0);
        assert!(extreme.normal_pressure_pa().is_finite());
    }

    #[test]
    fn invalid_directions_and_observers_are_rejected() {
        let stress = ideal_parallel_plate_stress_si(1e-6, PlateNormal::Z).unwrap();
        for direction in [[0.0; 3], [f64::NAN, 0.0, 1.0], [f64::INFINITY, 0.0, 1.0]] {
            assert_eq!(
                stress.null_contraction_j_m3(direction).unwrap_err(),
                CasimirStressError::InvalidDirection
            );
        }
        for velocity in [
            [1.0, 0.0, 0.0],
            [0.8, 0.8, 0.0],
            [f64::NAN, 0.0, 0.0],
            [f64::INFINITY, 0.0, 0.0],
        ] {
            assert_eq!(
                stress.observer_energy_density_j_m3(velocity).unwrap_err(),
                CasimirStressError::InvalidObserverVelocity
            );
        }
        assert_eq!(
            stress
                .null_contraction_j_m3([1e300, 0.0, 1e-300])
                .unwrap_err(),
            CasimirStressError::NumericalRange
        );
    }

    #[test]
    fn contraction_overflow_is_reported_separately_from_valid_tensor() {
        let stress = ideal_parallel_plate_stress_si(1.75e-84, PlateNormal::Z).unwrap();
        assert_eq!(
            stress.null_contraction_j_m3([0.0, 0.0, 1.0]).unwrap_err(),
            CasimirStressError::NumericalRange
        );
        assert_eq!(
            stress
                .observer_energy_density_j_m3([0.0, 0.0, 0.9])
                .unwrap_err(),
            CasimirStressError::NumericalRange
        );
    }
}
