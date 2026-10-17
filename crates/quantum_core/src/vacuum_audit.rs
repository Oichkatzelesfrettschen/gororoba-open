// SPDX-License-Identifier: MIT
//! Bounded falsifiers for equilibrium-vacuum work and passive-memory claims.
//!
//! The models separate state preparation, ordered quantum noise, recoverable
//! classical storage, and first-law accounting. Each calculation returns its
//! own model consequence; agreement supplies neither device nor QPU evidence.

/// Invalid physical domains or unrepresentable floating-point calculations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VacuumAuditError {
    /// Empty or unequal energy and probability lists.
    Shape,
    /// A physical parameter lies outside the documented finite domain.
    Domain,
    /// Probabilities differ from unity by more than 1e-12.
    Normalization,
    /// A calculation overflows, or nonzero memory storage or dissipation underflows.
    Arithmetic,
}

fn finite(value: f64) -> Result<f64, VacuumAuditError> {
    if value.is_finite() {
        Ok(value)
    } else {
        Err(VacuumAuditError::Arithmetic)
    }
}

fn positive(value: f64) -> Result<(), VacuumAuditError> {
    if value.is_finite() && value > 0.0 {
        Ok(())
    } else {
        Err(VacuumAuditError::Domain)
    }
}

/// Energies use the caller's common unit and reference the minimum input energy.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct DiagonalErgotropy {
    pub energy_above_ground: f64,
    pub passive_energy_above_ground: f64,
    pub extractable_work: f64,
}

/// Maximum work under arbitrary cyclic unitaries for a finite diagonal state.
///
/// Each probability belongs to the energy at the same index. Inputs may arrive
/// in any order. Ascending energies paired with descending populations give the
/// passive energy (Allahverdyan, Balian and Nieuwenhuizen, EPL 67, 565, 2004).
/// Probabilities must be finite, nonnegative and sum to unity within 1e-12;
/// accepted rounding error is normalized before computing either expectation.
/// Subtracting the ground energy before summation preserves common-offset
/// invariance within the resolution of the supplied f64 energy differences.
/// Work sums nonnegative population-swap contributions in O(n^2) time instead
/// of subtracting total expectations with potentially large common terms.
/// Finite truncation and arbitrary-unitary control remain model assumptions.
pub fn diagonal_ergotropy(
    energies: &[f64],
    probabilities: &[f64],
) -> Result<DiagonalErgotropy, VacuumAuditError> {
    if energies.is_empty() || energies.len() != probabilities.len() {
        return Err(VacuumAuditError::Shape);
    }
    if energies.iter().any(|value| !value.is_finite())
        || probabilities
            .iter()
            .any(|value| !value.is_finite() || *value < 0.0)
    {
        return Err(VacuumAuditError::Domain);
    }
    let normalization = finite(probabilities.iter().sum())?;
    if (normalization - 1.0).abs() > 1e-12 {
        return Err(VacuumAuditError::Normalization);
    }
    let ground = energies.iter().copied().min_by(f64::total_cmp).unwrap();
    let mut relative = energies
        .iter()
        .map(|energy| finite(energy - ground))
        .collect::<Result<Vec<_>, _>>()?;
    let energy_above_ground = finite(
        relative
            .iter()
            .zip(probabilities)
            .map(|(energy, population)| energy * (population / normalization))
            .sum(),
    )?;
    let mut aligned: Vec<_> = relative
        .iter()
        .copied()
        .zip(probabilities.iter().copied())
        .collect();
    aligned.sort_by(|left, right| left.0.total_cmp(&right.0));
    relative.sort_by(f64::total_cmp);
    let mut descending = probabilities.to_vec();
    descending.sort_by(|left, right| right.total_cmp(left));
    let passive_energy_above_ground = finite(
        relative
            .iter()
            .zip(descending)
            .map(|(energy, population)| energy * (population / normalization))
            .sum(),
    )?;
    // Population transport sums nonnegative swap work. Subtracting two full
    // energy expectations would erase small work beside an unchanged high level.
    let mut extractable_work = 0.0;
    for lower in 0..aligned.len() {
        let upper = (lower..aligned.len())
            .max_by(|&left, &right| aligned[left].1.total_cmp(&aligned[right].1))
            .unwrap();
        let gap = finite(aligned[upper].0 - aligned[lower].0)?;
        let population_difference = (aligned[upper].1 - aligned[lower].1) / normalization;
        extractable_work = finite(extractable_work + finite(gap * population_difference)?)?;
        let lower_population = aligned[lower].1;
        aligned[lower].1 = aligned[upper].1;
        aligned[upper].1 = lower_population;
    }
    Ok(DiagonalErgotropy {
        energy_above_ground,
        passive_energy_above_ground,
        extractable_work,
    })
}

/// Coefficients of 2*pi*delta(omega +/- omega_0), in square metres.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct OscillatorLineWeights {
    pub positive_frequency_m2: f64,
    pub negative_frequency_m2: f64,
    pub position_variance_m2: f64,
}

/// Ordered displacement spectrum of an isolated thermal harmonic oscillator.
///
/// Inputs are mass in kg, positive angular frequency in rad/s, and temperature
/// in K >= 0. Convention: Sqq(omega) = integral dt exp(+i*omega*t)<q(t)q(0)>.
/// Sqq = 2*pi*[w_plus*delta(omega-omega_0) + w_minus*delta(omega+omega_0)].
/// Delta has units seconds, so Sqq has units m^2*s; returned line weights have
/// units m^2. Positive frequency describes bath absorption and negative
/// frequency bath emission (Clerk et al., RMP 82, 1155, 2010, Sec. II.B).
/// Vacuum has w_minus=0 and w_plus=hbar/(2*m*omega_0). The symmetrized spectrum
/// loses that ordering and cannot by itself establish extractable power.
/// Stable exp_m1 and an exp(-x) branch handle classical and low-temperature
/// regimes. Constants use the repository's rounded hbar and exact SI k_B.
pub fn oscillator_line_weights(
    mass_kg: f64,
    omega_rad_s: f64,
    temperature_k: f64,
) -> Result<OscillatorLineWeights, VacuumAuditError> {
    const HBAR: f64 = 1.054_571_817e-34;
    const K_B: f64 = 1.380_649e-23;
    positive(mass_kg)?;
    positive(omega_rad_s)?;
    if !temperature_k.is_finite() || temperature_k < 0.0 {
        return Err(VacuumAuditError::Domain);
    }
    let zero_point = finite((HBAR / mass_kg) / omega_rad_s / 2.0)?;
    positive(zero_point)?;
    let occupation = if temperature_k == 0.0 {
        0.0
    } else {
        // Compute in log space before exponentiation so extreme positive
        // inputs reach the correct low-temperature limit without x overflow.
        let log_ratio = HBAR.ln() + omega_rad_s.ln() - K_B.ln() - temperature_k.ln();
        if log_ratio > 745.0_f64.ln() {
            0.0
        } else if log_ratio > 50.0_f64.ln() {
            let ratio = log_ratio.exp();
            let decay = (-ratio).exp();
            decay / (1.0 - decay)
        } else {
            finite(1.0 / log_ratio.exp().exp_m1())?
        }
    };
    let negative_frequency_m2 = finite(zero_point * occupation)?;
    let positive_frequency_m2 = finite(zero_point + negative_frequency_m2)?;
    let position_variance_m2 = finite(positive_frequency_m2 + negative_frequency_m2)?;
    Ok(OscillatorLineWeights {
        positive_frequency_m2,
        negative_frequency_m2,
        position_variance_m2,
    })
}

/// Instantaneous state and powers of a passive exponential mechanical memory.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ExponentialMemoryPower {
    pub stored_energy_j: f64,
    pub drive_power_w: f64,
    pub dissipation_w: f64,
    pub stored_energy_rate_w: f64,
    pub force_rate_n_per_s: f64,
}

/// Audit Fdot = k*v - F/tau, equivalent to an exponential velocity kernel.
///
/// Force F is in N, imposed velocity v in m/s, stiffness k > 0 in N/m, and
/// relaxation time tau > 0 in s. Storage E=F^2/(2*k) obeys the exact continuous
/// identity dE/dt = F*v - F^2/(k*tau). Positive F*v supplies the memory.
/// A nonzero initial force represents stored preparation energy. The function
/// evaluates an instantaneous identity; sampled integration needs its own
/// discretization error bounds and a device model needs its own constitutive
/// and calibration evidence.
/// Nonzero force with storage or dissipation rounded to zero returns Arithmetic;
/// callers need higher precision for those regimes.
pub fn exponential_memory_power(
    force_n: f64,
    velocity_m_per_s: f64,
    stiffness_n_per_m: f64,
    relaxation_s: f64,
) -> Result<ExponentialMemoryPower, VacuumAuditError> {
    positive(stiffness_n_per_m)?;
    positive(relaxation_s)?;
    if !force_n.is_finite() || !velocity_m_per_s.is_finite() {
        return Err(VacuumAuditError::Domain);
    }
    let displacement_m = finite(force_n / stiffness_n_per_m)?;
    let stored_energy_j = finite((0.5 * force_n) * displacement_m)?;
    if force_n != 0.0 && stored_energy_j == 0.0 {
        return Err(VacuumAuditError::Arithmetic);
    }
    let relaxation_force_rate = finite(force_n / relaxation_s)?;
    let dissipation_w = finite(relaxation_force_rate * displacement_m)?;
    if force_n != 0.0 && dissipation_w == 0.0 {
        return Err(VacuumAuditError::Arithmetic);
    }
    let drive_power_w = finite(force_n * velocity_m_per_s)?;
    let stored_energy_rate_w = finite(drive_power_w - dissipation_w)?;
    let force_rate_n_per_s =
        finite(finite(stiffness_n_per_m * velocity_m_per_s)? - relaxation_force_rate)?;
    Ok(ExponentialMemoryPower {
        stored_energy_j,
        drive_power_w,
        dissipation_w,
        stored_energy_rate_w,
        force_rate_n_per_s,
    })
}

/// First-law residual Win + Qin - Wout - Qout - deltaE, in joules.
///
/// The first four inputs are finite nonnegative boundary-transfer magnitudes;
/// deltaE is a finite signed final-minus-initial stored energy. A closed cycle
/// additionally requires deltaE=0 within independently declared measurement
/// uncertainty. A vanishing residual establishes energy accounting only;
/// reservoir temperatures, entropy production, uncertainty and omitted input
/// channels require separate evidence before a second-law claim can be tested.
/// Neumaier compensation retains small signed residuals beside large common
/// flows. Every sum and correction must remain finite; overflow returns Arithmetic.
pub fn energy_closure_residual(
    work_in_j: f64,
    heat_in_j: f64,
    work_out_j: f64,
    heat_out_j: f64,
    delta_energy_j: f64,
) -> Result<f64, VacuumAuditError> {
    if [work_in_j, heat_in_j, work_out_j, heat_out_j]
        .iter()
        .any(|value| !value.is_finite() || *value < 0.0)
        || !delta_energy_j.is_finite()
    {
        return Err(VacuumAuditError::Domain);
    }
    let mut sum = 0.0_f64;
    let mut correction = 0.0;
    for term in [
        work_in_j,
        heat_in_j,
        -work_out_j,
        -heat_out_j,
        -delta_energy_j,
    ] {
        let next = finite(sum + term)?;
        let roundoff = if sum.abs() >= term.abs() {
            finite(finite(sum - next)? + term)?
        } else {
            finite(finite(term - next)? + sum)?
        };
        correction = finite(correction + roundoff)?;
        sum = next;
    }
    finite(sum + correction)
}
#[cfg(test)]
mod tests {
    use super::*;

    fn close(actual: f64, expected: f64) {
        assert!(
            (actual - expected).abs() <= 1e-12 * expected.abs().max(1e-300),
            "actual={actual}, expected={expected}"
        );
    }

    #[test]
    fn population_inversion_has_extractable_work_and_ground_state_has_none() {
        let inverted = diagonal_ergotropy(&[0.0, 2.0], &[0.25, 0.75]).unwrap();
        close(inverted.energy_above_ground, 1.5);
        close(inverted.passive_energy_above_ground, 0.5);
        close(inverted.extractable_work, 1.0);
        close(
            diagonal_ergotropy(&[2.0, 0.0], &[0.0, 1.0])
                .unwrap()
                .extractable_work,
            0.0,
        );
    }

    #[test]
    fn degenerate_levels_and_large_common_energy_shift_preserve_work() {
        close(
            diagonal_ergotropy(&[4.0, 4.0], &[0.2, 0.8])
                .unwrap()
                .extractable_work,
            0.0,
        );
        let shifted = diagonal_ergotropy(&[1e15, 1e15 + 2.0], &[0.25, 0.75]).unwrap();
        close(shifted.extractable_work, 1.0);
    }

    #[test]
    fn diagonal_state_rejects_invalid_inputs_and_overflow() {
        for (energies, probabilities) in [
            (vec![], vec![]),
            (vec![0.0], vec![0.5]),
            (vec![0.0, 1.0], vec![-0.1, 1.1]),
            (vec![f64::NAN], vec![1.0]),
            (vec![0.0], vec![f64::INFINITY]),
            (vec![-f64::MAX, f64::MAX], vec![0.5, 0.5]),
            (vec![0.0, 1.0], vec![1.0]),
        ] {
            assert!(diagonal_ergotropy(&energies, &probabilities).is_err());
        }
    }

    #[test]
    fn vacuum_spectrum_has_absorption_line_and_zero_emission_line() {
        let spectrum = oscillator_line_weights(1.0, 1.0, 0.0).unwrap();
        close(spectrum.positive_frequency_m2, 5.272_859_085e-35);
        assert_eq!(spectrum.negative_frequency_m2, 0.0);
        close(spectrum.position_variance_m2, 5.272_859_085e-35);
    }

    #[test]
    fn thermal_line_ratio_obeys_detailed_balance_and_classical_limit() {
        // hbar*omega/(k_B*T) = 1, using exact SI defining constants.
        let thermal = oscillator_line_weights(1.0, 1.0, 1.054_571_817e-34 / 1.380_649e-23).unwrap();
        close(
            thermal.negative_frequency_m2 / thermal.positive_frequency_m2,
            (-1.0_f64).exp(),
        );
        let classical = oscillator_line_weights(2.0, 3.0, 300.0).unwrap();
        close(classical.position_variance_m2, 2.301_081_666_666_666_5e-22);
        assert!(oscillator_line_weights(1.0, 1.0, 1e-300).is_ok());
    }

    #[test]
    fn oscillator_rejects_invalid_units_domain_and_unrepresentable_results() {
        for (mass, omega, temperature) in [
            (0.0, 1.0, 0.0),
            (1.0, -1.0, 0.0),
            (1.0, 1.0, -1.0),
            (f64::NAN, 1.0, 1.0),
            (1e-300, 1e-300, 1e300),
        ] {
            assert!(oscillator_line_weights(mass, omega, temperature).is_err());
        }
    }

    #[test]
    fn memory_release_and_driven_storage_obey_power_balance() {
        // F=4 N, k=2 N/m, tau=2 s: E=4 J, dissipation=4 W.
        let release = exponential_memory_power(4.0, 0.0, 2.0, 2.0).unwrap();
        close(release.stored_energy_j, 4.0);
        close(release.dissipation_w, 4.0);
        close(release.stored_energy_rate_w, -4.0);
        let driven = exponential_memory_power(4.0, 3.0, 2.0, 2.0).unwrap();
        close(driven.drive_power_w, 12.0);
        close(driven.stored_energy_rate_w, 8.0);
        close(driven.force_rate_n_per_s, 4.0);
        for (force, velocity, stiffness, tau) in [
            (1.0, 1.0, 0.0, 1.0),
            (1.0, 1.0, 1.0, -1.0),
            (f64::MAX, 2.0, 1.0, 1.0),
        ] {
            assert!(exponential_memory_power(force, velocity, stiffness, tau).is_err());
        }
    }

    #[test]
    fn unaffected_high_energy_population_preserves_small_extractable_work() {
        let result = diagonal_ergotropy(&[0.0, 1.0, 1e16], &[0.25, 0.5, 0.25]).unwrap();
        close(result.extractable_work, 0.25);
    }

    #[test]
    fn memory_rejects_underflowed_storage_and_matches_force_balance() {
        assert_eq!(
            exponential_memory_power(1e-200, 0.0, 1.0, 1e-200),
            Err(VacuumAuditError::Arithmetic)
        );
        let driven = exponential_memory_power(4.0, 3.0, 2.0, 2.0).unwrap();
        close(
            driven.stored_energy_rate_w,
            (4.0 / 2.0) * (2.0 * 3.0 - 4.0 / 2.0),
        );
        let release = exponential_memory_power(4.0, 0.0, 2.0, 2.0).unwrap();
        close(
            release.stored_energy_rate_w,
            (4.0 / 2.0) * (2.0 * 0.0 - 4.0 / 2.0),
        );
    }

    #[test]
    fn ledger_preserves_small_signed_residual_beside_large_flows() {
        close(
            energy_closure_residual(1e16, 1.0, 1e16, 0.0, 0.0).unwrap(),
            1.0,
        );
        close(
            energy_closure_residual(1e16, 0.0, 1e16, 1.0, 0.0).unwrap(),
            -1.0,
        );
        close(
            energy_closure_residual(1e16, 1.0, 1e16, 0.0, 1.0).unwrap(),
            0.0,
        );
    }

    #[test]
    fn ledger_distinguishes_closed_accounting_from_energy_claims() {
        close(
            energy_closure_residual(10.0, 2.0, 7.0, 1.0, 4.0).unwrap(),
            0.0,
        );
        close(
            energy_closure_residual(0.0, 0.0, 1.0, 0.0, 0.0).unwrap(),
            -1.0,
        );
        // First-law closure alone permits a heat-to-work cycle.
        close(
            energy_closure_residual(0.0, 5.0, 5.0, 0.0, 0.0).unwrap(),
            0.0,
        );
        assert!(energy_closure_residual(f64::NAN, 0.0, 0.0, 0.0, 0.0).is_err());
        assert!(energy_closure_residual(-1.0, 0.0, 0.0, 0.0, 0.0).is_err());
        assert!(energy_closure_residual(f64::MAX, f64::MAX, 0.0, 0.0, 0.0).is_err());
    }
}
