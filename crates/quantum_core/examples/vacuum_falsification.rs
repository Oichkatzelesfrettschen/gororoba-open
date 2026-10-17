// SPDX-License-Identifier: MIT
//! Deterministic model checks; stdout contains calculations rather than measurements.

use std::f64::consts::PI;

use algebra_experimental::novel_algorithms::zpe_lbm_collision::zpe_bgk_collision;
use quantum_core::{
    casimir::{C, HBAR},
    vacuum_audit::{
        diagonal_ergotropy, energy_closure_residual, exponential_memory_power,
        oscillator_line_weights,
    },
};

const GRAVITATIONAL_CONSTANT: f64 = 6.674_30e-11;
const ELECTRON_MASS_KG: f64 = 9.109_383_713_9e-31;
const JULIAN_YEAR_S: f64 = 31_557_600.0;
const NOMINAL_SOLAR_LUMINOSITY_W: f64 = 3.828e26;

fn regulated_em_density(cutoff_rad_per_m: f64) -> f64 {
    HBAR * C * cutoff_rad_per_m.powi(4) / (8.0 * PI * PI)
}

fn ideal_plate_energy(gap_m: f64, area_m2: f64) -> f64 {
    -PI * PI * HBAR * C * area_m2 / (720.0 * gap_m.powi(3))
}

fn row(quantity: &str, value: f64, unit: &str, boundary: &str) {
    println!("{quantity}\t{value:.15e}\t{unit}\tanalytic_or_model\t{boundary}");
}

fn main() {
    println!("quantity\tvalue\tunit\tevidence_class\tboundary");
    let planck_length_m = (HBAR * GRAVITATIONAL_CONSTANT / C.powi(3)).sqrt();
    row(
        "planck_length",
        planck_length_m,
        "m",
        "CODATA-rounded constants",
    );
    let cutoff_energy_j = regulated_em_density(1.0 / planck_length_m) * 1e-6;
    row(
        "cutoff_energy_one_cm3",
        cutoff_energy_j,
        "J",
        "k_max=1/l_P; hard 3-momentum cutoff",
    );
    row(
        "wavelength_cutoff_energy_one_cm3",
        cutoff_energy_j * (2.0 * PI).powi(4),
        "J",
        "k_max=2*pi/l_P",
    );
    row(
        "cutoff_times_ten_density_ratio",
        regulated_em_density(10.0) / regulated_em_density(1.0),
        "1",
        "free electromagnetic mode count",
    );
    let galaxy_energy_j = 1e11 * NOMINAL_SOLAR_LUMINOSITY_W * 1e10 * JULIAN_YEAR_S;
    row(
        "illustrative_galaxy_energy",
        galaxy_energy_j,
        "J",
        "1e11 nominal solar luminosities for 1e10 Julian years",
    );
    row(
        "infographic_to_galaxy_ratio",
        1e107 / galaxy_energy_j,
        "1",
        "illustrative luminosity assumption",
    );
    row(
        "population_over_rate",
        1e57 / 1.7e57,
        "s",
        "conditional stationary population; rate attribution unverified",
    );
    row(
        "real_pair_rest_energy",
        2.0 * ELECTRON_MASS_KG * C * C,
        "J",
        "real electron and positron; excludes virtual-line interpretation",
    );

    let near_energy_j = ideal_plate_energy(100e-9, 1e-12);
    let far_energy_j = ideal_plate_energy(200e-9, 1e-12);
    let approach_work_j = far_energy_j - near_energy_j;
    row(
        "ideal_plate_energy",
        near_energy_j,
        "J",
        "100 nm gap; 1 um^2; perfect conductors; T=0",
    );
    row(
        "ideal_plate_pressure",
        3.0 * near_energy_j / (1e-12 * 100e-9),
        "Pa",
        "perfect-conductor planar limit",
    );
    row(
        "casimir_approach_work",
        approach_work_j,
        "J",
        "200 nm to 100 nm; conservative ideal model",
    );
    row(
        "casimir_reset_work",
        approach_work_j,
        "J",
        "100 nm to 200 nm; same model and parameters",
    );
    row(
        "casimir_cycle_residual",
        energy_closure_residual(approach_work_j, 0.0, approach_work_j, 0.0, 0.0).unwrap(),
        "J",
        "complete ideal approach/reset; fixed boundary parameters",
    );

    let ground = diagonal_ergotropy(&[0.5, 1.5, 2.5], &[1.0, 0.0, 0.0]).unwrap();
    row(
        "ground_ergotropy",
        ground.extractable_work,
        "hbar*omega",
        "three levels; arbitrary cyclic unitary",
    );
    let spectrum = oscillator_line_weights(1e-15, 2.0 * PI * 1e6, 0.0).unwrap();
    row(
        "vacuum_absorption_line_weight",
        spectrum.positive_frequency_m2,
        "m^2",
        "coefficient of 2*pi*delta(omega-omega_0)",
    );
    row(
        "vacuum_emission_line_weight",
        spectrum.negative_frequency_m2,
        "m^2",
        "coefficient of 2*pi*delta(omega+omega_0)",
    );
    let memory = exponential_memory_power(4.0, 3.0, 2.0, 2.0).unwrap();
    row(
        "memory_storage_rate",
        memory.stored_energy_rate_w,
        "W",
        "F=4 N; v=3 m/s; k=2 N/m; tau=2 s",
    );
    row(
        "unaccounted_output_residual",
        energy_closure_residual(0.0, 0.0, 1.0, 0.0, 0.0).unwrap(),
        "J",
        "1 J output; zero declared inputs and storage change",
    );

    let mut node = [0.0; 16];
    node[1] = 1.0;
    let equilibrium = node;
    let mut operand = [0.0; 16];
    operand[2] = 1.0;
    zpe_bgk_collision(&mut node, &equilibrium, 1.0, &operand);
    row(
        "commutator_population_sum_change",
        node.iter().sum::<f64>() - 1.0,
        "1",
        "node=equilibrium=e1; operand=e2; relaxation=1",
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cutoff_prescriptions_have_declared_quartic_ratio() {
        assert!((regulated_em_density(2.0) / regulated_em_density(1.0) - 16.0).abs() < 1e-12);
        let ratio = regulated_em_density(2.0 * PI) / regulated_em_density(1.0);
        assert!((ratio - (2.0 * PI).powi(4)).abs() < 1e-10);
    }

    #[test]
    fn ideal_plate_pressure_is_negative_energy_derivative_per_area() {
        let gap_m = 100e-9;
        let step_m = gap_m * 1e-5;
        let area_m2 = 1e-12;
        let derivative = (ideal_plate_energy(gap_m + step_m, area_m2)
            - ideal_plate_energy(gap_m - step_m, area_m2))
            / (2.0 * step_m);
        let pressure_pa = -PI * PI * HBAR * C / (240.0 * gap_m.powi(4));
        assert!(((-derivative / area_m2) / pressure_pa - 1.0).abs() < 1e-8);
    }

    #[test]
    fn undersampled_fundamental_aliases_to_slow_envelope() {
        let sampling_hz: f64 = 249.9e9;
        let true_hz: f64 = 500e9;
        let alias_hz = true_hz - 2.0 * sampling_hz;
        assert!((alias_hz - 0.2e9).abs() < 1.0);
        for sample in 0..100 {
            let time_s = f64::from(sample) / sampling_hz;
            let original = (2.0 * PI * true_hz * time_s).cos();
            let alias = (2.0 * PI * alias_hz * time_s).cos();
            assert!((original - alias).abs() < 1e-10);
        }
    }
}
