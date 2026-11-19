// SPDX-License-Identifier: MIT

//! Analytic audit of an energy-density-only gravitational inference.
//!
//! Brown and Maclay (1969) supply the ideal electromagnetic plate tensor.
//! An exact stationary planar-shift tensor matches its energy density while
//! a transverse stress fails Einstein's equation. This local counterexample
//! neither reproduces White's sphere-cylinder worldline calculation nor
//! supplies a finite bubble, physical apparatus or measured observable.

use casimir_core::stress_energy::{PlateNormal, ideal_parallel_plate_stress_si};
use clap::Parser;
use gr_core::warp_stress_energy::planar_shift_curvature;
use rayon::prelude::*;
use serde::Serialize;
use std::{error::Error, f64::consts::PI, fmt::Write as _, fs, io, path::PathBuf};

// CODATA 2022 central value; its uncertainty is distinct from numerical error.
const GRAVITATIONAL_CONSTANT_M3_KG_S2: f64 = 6.67430e-11;
// SI defining constant.
const SPEED_OF_LIGHT_M_S: f64 = 299_792_458.0;
const LABELS: [&str; 4] = ["0", "x", "y", "z"];

#[derive(Debug, Parser)]
#[command(about = "Audit a local full-tensor counterexample to energy-density matching")]
struct Args {
    /// Ideal parallel-plate gaps in metres, not sphere-cylinder dimensions.
    #[arg(long, value_delimiter = ',', num_args = 1.., default_value = "1e-6,4e-6")]
    gaps_m: Vec<f64>,
    /// Destination for the two TSV tables and summary.json.
    #[arg(long)]
    output_dir: PathBuf,
}

#[derive(Debug, Serialize)]
struct GapAudit {
    gap_m: f64,
    energy_density_j_m3: f64,
    energy_per_area_j_m2: f64,
    normal_pressure_pa: f64,
    source_scale_m_inverse2: f64,
    matched_shift_derivative_m_inverse: f64,
    einstein_orthonormal_m_inverse2: [[f64; 4]; 4],
    ideal_vacuum_tensor_j_m3: [[f64; 4]; 4],
    residual_m_inverse2: [[f64; 4]; 4],
    residual_over_source_scale: [[f64; 4]; 4],
    max_normalized_residual: f64,
    energy_density_matches: bool,
    full_tensor_matches: bool,
}

#[derive(Debug, Serialize)]
struct Summary {
    schema: &'static str,
    evidence_class: &'static str,
    conclusion: &'static str,
    coordinate_convention: &'static str,
    orthonormal_frame: &'static str,
    ideal_plate_normal: &'static str,
    gravitational_constant_m3_kg_s2: f64,
    speed_of_light_m_s: f64,
    einstein_coupling_m_per_j: f64,
    assumptions: Vec<&'static str>,
    unresolved_physical_requirements: Vec<&'static str>,
    cases: Vec<GapAudit>,
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message.into())
}

fn einstein_coupling() -> f64 {
    8.0 * PI * GRAVITATIONAL_CONSTANT_M3_KG_S2 / SPEED_OF_LIGHT_M_S.powi(4)
}

fn audit_gap(gap_m: f64) -> Result<GapAudit, String> {
    let plates =
        ideal_parallel_plate_stress_si(gap_m, PlateNormal::X).map_err(|error| error.to_string())?;
    let magnitude = -plates.energy_density_j_m3();
    let kappa = einstein_coupling();
    let source_scale = kappa * magnitude;
    // Subnormal source scales cannot retain the relative precision required by
    // the dimensionless residual contract, even when the density remains finite.
    if !source_scale.is_finite() || source_scale < f64::MIN_POSITIVE {
        return Err("ideal vacuum source scale exceeds the supported numerical range".into());
    }
    let first_derivative = 2.0 * source_scale.sqrt();
    let curvature =
        planar_shift_curvature(first_derivative, 0.0).map_err(|error| error.to_string())?;
    let ideal_tensor = plates.tensor_j_m3();
    let mut residual = [[0.0; 4]; 4];
    let mut normalized = [[0.0; 4]; 4];
    let mut maximum = 0.0_f64;
    for (mu, row) in normalized.iter_mut().enumerate() {
        for (nu, value) in row.iter_mut().enumerate() {
            // Scaling before subtraction preserves the dimensionless mismatch
            // at tiny but representable gravitational source strengths.
            *value = curvature.einstein_orthonormal[mu][nu] / source_scale
                - ideal_tensor[mu][nu] / magnitude;
            residual[mu][nu] =
                curvature.einstein_orthonormal[mu][nu] - kappa * ideal_tensor[mu][nu];
            if !value.is_finite() || !residual[mu][nu].is_finite() {
                return Err("tensor residual exceeds floating-point range".into());
            }
            maximum = maximum.max(value.abs());
        }
    }
    let tolerance = 64.0 * f64::EPSILON;
    let energy_density_matches = normalized[0][0].abs() <= tolerance;
    let full_tensor_matches = maximum <= tolerance;
    if !energy_density_matches || full_tensor_matches || (normalized[3][3] + 2.0).abs() > tolerance
    {
        return Err("the analytic tensor counterexample failed its defining invariant".into());
    }
    Ok(GapAudit {
        gap_m,
        energy_density_j_m3: plates.energy_density_j_m3(),
        energy_per_area_j_m2: plates.energy_per_area_j_m2(),
        normal_pressure_pa: plates.normal_pressure_pa(),
        source_scale_m_inverse2: source_scale,
        matched_shift_derivative_m_inverse: first_derivative,
        einstein_orthonormal_m_inverse2: curvature.einstein_orthonormal,
        ideal_vacuum_tensor_j_m3: ideal_tensor,
        residual_m_inverse2: residual,
        residual_over_source_scale: normalized,
        max_normalized_residual: maximum,
        energy_density_matches,
        full_tensor_matches,
    })
}

fn audit(gaps: &[f64]) -> Result<Summary, io::Error> {
    if gaps.is_empty() {
        return Err(invalid("at least one ideal plate gap is required"));
    }
    let cases = gaps
        .par_iter()
        .map(|&gap| audit_gap(gap))
        .collect::<Result<Vec<_>, _>>()
        .map_err(invalid)?;
    Ok(Summary {
        schema: "casimir-warp-evidence-v1",
        evidence_class: "analytic_reference_and_local_tensor_counterexample",
        conclusion: "energy_density_matching_alone_is_insufficient_for_the_full_einstein_equation",
        coordinate_convention: "x0=ct; signature (-+++); ds2=-(dx0)^2+[dx-B(y)dx0]^2+dy^2+dz^2",
        orthonormal_frame: "Eulerian n=(1,B,0,0), ex=(0,1,0,0), ey=(0,0,1,0), ez=(0,0,0,1)",
        ideal_plate_normal: "x",
        gravitational_constant_m3_kg_s2: GRAVITATIONAL_CONSTANT_M3_KG_S2,
        speed_of_light_m_s: SPEED_OF_LIGHT_M_S,
        einstein_coupling_m_per_j: einstein_coupling(),
        assumptions: vec![
            "Ideal EM reference: infinite perfectly conducting parallel plates at zero temperature.",
            "The tensor is the vacuum contribution; plate and support stresses are outside this reference.",
            "The stationary planar shift is evaluated locally with B''=0 and (B')^2/4=kappa*K.",
            "The matched derivative is an algebraic construction, not an inferred propagation speed.",
            "The source scale kappa*K has inverse-square-metre units; it is not a measured curvature invariant.",
            "Worldline center-of-mass effective-action density is distinct from local stress-energy.",
        ],
        unresolved_physical_requirements: vec![
            "A justified renormalized local stress tensor for the actual geometry, material and quantum state.",
            "A complete apparatus contribution, conservation law and consistent gravitational boundary data.",
            "A self-consistent spacetime solution and an observable with quantified conventional alternatives.",
            "Calibrated physical measurements; neither a QPU encoding nor this reference supplies them.",
        ],
        cases,
    })
}

fn tables(summary: &Summary) -> Result<(String, String), std::fmt::Error> {
    let mut scalars = String::from(
        "gap_m\tenergy_density_j_m3\tenergy_per_area_j_m2\tnormal_pressure_pa\tsource_scale_m_inverse2\tmatched_shift_derivative_m_inverse\tenergy_density_matches\tfull_tensor_matches\tmax_normalized_residual\n",
    );
    let mut tensors = String::from(
        "gap_m\tmu\tnu\teinstein_m_inverse2\tideal_vacuum_j_m3\tresidual_m_inverse2\tresidual_over_source_scale\n",
    );
    for case in &summary.cases {
        writeln!(
            scalars,
            "{:.17e}\t{:.17e}\t{:.17e}\t{:.17e}\t{:.17e}\t{:.17e}\t{}\t{}\t{:.17e}",
            case.gap_m,
            case.energy_density_j_m3,
            case.energy_per_area_j_m2,
            case.normal_pressure_pa,
            case.source_scale_m_inverse2,
            case.matched_shift_derivative_m_inverse,
            case.energy_density_matches,
            case.full_tensor_matches,
            case.max_normalized_residual
        )?;
        for (mu, label_mu) in LABELS.iter().enumerate() {
            for (nu, label_nu) in LABELS.iter().enumerate() {
                writeln!(
                    tensors,
                    "{:.17e}\t{}\t{}\t{:.17e}\t{:.17e}\t{:.17e}\t{:.17e}",
                    case.gap_m,
                    label_mu,
                    label_nu,
                    case.einstein_orthonormal_m_inverse2[mu][nu],
                    case.ideal_vacuum_tensor_j_m3[mu][nu],
                    case.residual_m_inverse2[mu][nu],
                    case.residual_over_source_scale[mu][nu]
                )?;
            }
        }
    }
    Ok((scalars, tensors))
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();
    let summary = audit(&args.gaps_m)?;
    let (scalars, tensors) = tables(&summary)?;
    let mut json = serde_json::to_string_pretty(&summary)?;
    json.push('\n');
    fs::create_dir_all(&args.output_dir)?;
    fs::write(args.output_dir.join("reference_scalars.tsv"), scalars)?;
    fs::write(args.output_dir.join("tensor_residuals.tsv"), tensors)?;
    fs::write(args.output_dir.join("summary.json"), json)?;
    println!(
        "{} analytic references: energy density matches; the full tensor fails (normalized zz residual -2)",
        summary.cases.len()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matched_energy_retains_transverse_stress_counterexample() {
        let summary = audit(&[1e-6, 4e-6]).expect("representable ideal references");
        for case in &summary.cases {
            assert!(case.energy_density_matches);
            assert!(!case.full_tensor_matches);
            assert!((case.residual_over_source_scale[3][3] + 2.0).abs() < 1e-14);
            assert!(case.residual_over_source_scale[0][0].abs() < 1e-14);
            assert!((case.max_normalized_residual - 2.0).abs() < 1e-14);
        }
        assert!(
            (summary.cases[0].source_scale_m_inverse2 / summary.cases[1].source_scale_m_inverse2
                - 256.0)
                .abs()
                < 1e-10
        );
    }

    #[test]
    fn invalid_or_unrepresentable_inputs_return_errors() {
        assert!(audit(&[]).is_err());
        for gap in [0.0, -1.0, f64::NAN, f64::INFINITY, 1e-100, 1e100] {
            assert!(audit_gap(gap).is_err(), "gap {gap}");
        }
    }

    #[test]
    fn rejects_subnormal_gravitational_scale_before_residual_normalization() {
        let gap = 1e63;
        let plates = ideal_parallel_plate_stress_si(gap, PlateNormal::X).expect("finite density");
        let scale = -einstein_coupling() * plates.energy_density_j_m3();
        assert!(scale.is_subnormal());
        assert!(audit_gap(gap).is_err());
    }

    #[test]
    fn reports_preserve_all_components_and_evidence_class() {
        let summary = audit(&[1e-6]).expect("reference");
        let (scalars, tensors) = tables(&summary).expect("format");
        assert_eq!(scalars.lines().count(), 2);
        assert_eq!(tensors.lines().count(), 17);
        let value = serde_json::to_value(summary).expect("JSON");
        assert_eq!(
            value["evidence_class"],
            "analytic_reference_and_local_tensor_counterexample"
        );
        assert_eq!(value["cases"][0]["full_tensor_matches"], false);
    }
}
