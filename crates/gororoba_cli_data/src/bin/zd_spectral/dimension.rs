//! Finite-graph spectral-dimension census, full heat trace v2.
//!
//! Each CD dimension selects the first cross-assessor component. The curve
//! includes its stationary mode and is a graph diagnostic, not a measurement
//! of physical spacetime or a recovered cosmological dimensional flow.

use algebra_analysis::spectral_dimension::{dimensional_flow_analysis, spectral_gap_census};
use std::path::PathBuf;

#[derive(clap::Args)]
pub struct Cli {
    /// Minimum CD dimension (power of two, at least 16).
    #[arg(long, default_value = "16")]
    min_dim: usize,
    /// Maximum CD dimension (power of two, no smaller than min_dim).
    #[arg(long, default_value = "256")]
    max_dim: usize,
    /// Number of logarithmically spaced diffusion-time samples.
    #[arg(long, default_value = "300")]
    t_points: usize,
    /// Minimum positive diffusion time.
    #[arg(long, default_value = "0.01")]
    t_min: f64,
    /// Maximum finite diffusion time.
    #[arg(long, default_value = "50.0")]
    t_max: f64,
    /// Output directory; versioned filenames leave historical CSVs untouched.
    #[arg(long, default_value = "data/csv")]
    output_dir: PathBuf,
}

fn dimensions(minimum: usize, maximum: usize) -> anyhow::Result<Vec<usize>> {
    anyhow::ensure!(
        minimum >= 16 && minimum.is_power_of_two(),
        "minimum dimension must be a power of two at least 16",
    );
    anyhow::ensure!(
        maximum >= minimum && maximum.is_power_of_two(),
        "maximum dimension must be a power of two no smaller than the minimum",
    );
    let mut dimensions = vec![minimum];
    let mut current = minimum;
    while current < maximum {
        current = current
            .checked_mul(2)
            .ok_or_else(|| anyhow::anyhow!("dimension ladder overflows usize"))?;
        dimensions.push(current);
    }
    Ok(dimensions)
}

pub fn run(cli: Cli) -> anyhow::Result<()> {
    let dims = dimensions(cli.min_dim, cli.max_dim)?;
    anyhow::ensure!(cli.t_points >= 3, "at least three diffusion-time points are required");
    anyhow::ensure!(
        cli.t_min.is_finite()
            && cli.t_max.is_finite()
            && cli.t_min > 0.0
            && cli.t_max > cli.t_min,
        "diffusion times must satisfy finite 0 < t_min < t_max",
    );
    eprintln!("ZD spectral census: full trace v2, first component per algebra dimension");
    eprintln!("Dimensions: {dims:?}");
    eprintln!("Time range [{}, {}], {} samples", cli.t_min, cli.t_max, cli.t_points);
    let result = dimensional_flow_analysis(&dims, cli.t_min, cli.t_max, cli.t_points);
    eprintln!(
        "{:<8} {:>6} {:>8} {:>12} {:>10}",
        "CD_dim", "comps", "nodes", "flat_window", "flatness",
    );
    for value in &result.dimensions {
        let (dimension, flatness) = match &value.plateau {
            Some(window) => (format!("{:.4}", window.d_s), format!("{:.4}", window.flatness_score)),
            None => ("N/A".to_string(), "N/A".to_string()),
        };
        eprintln!(
            "{:<8} {:>6} {:>8} {:>12} {:>10}",
            value.cd_dim, value.n_components, value.nodes_per_component, dimension, flatness,
        );
    }
    std::fs::create_dir_all(&cli.output_dir)?;
    std::fs::write(
        cli.output_dir.join("zd_spectral_full_trace_v2_convention.txt"),
        "schema: finite-graph-full-heat-trace-v2\n\
         P(t): sum_i exp(-lambda_i*t)/N, including zero modes\n\
         d_s(t): 2*t*sum_i lambda_i*exp(-lambda_i*t)/sum_i exp(-lambda_i*t)\n\
         scope: first cross-assessor component, not the disconnected union\n\
         flatness_score: max(0, 1 - std/abs(mean)); not R-squared\n\
         plateau: flat-window candidate only; finite-size endpoints may be flat\n\
         is_expander: historical finite-graph heuristic, not a family theorem\n\
         physical interpretation: no inference of spacetime dimension\n",
    )?;

    let curve_path = cli.output_dir.join("zd_spectral_full_trace_v2_curves.csv");
    let mut writer = csv::Writer::from_path(&curve_path)?;
    writer.write_record(["cd_dim", "ln_t", "d_s"])?;
    for value in &result.dimensions {
        for &(log_t, dimension) in &value.curve {
            writer.write_record([
                value.cd_dim.to_string(),
                format!("{log_t:.17e}"),
                format!("{dimension:.17e}"),
            ])?;
        }
    }
    writer.flush()?;

    let window_path = cli.output_dir.join("zd_spectral_full_trace_v2_flat_windows.csv");
    let mut writer = csv::Writer::from_path(&window_path)?;
    writer.write_record([
        "cd_dim", "n_components", "first_component_nodes", "d_s_mean",
        "ln_t_min", "ln_t_max", "flatness_score",
    ])?;
    for value in &result.dimensions {
        if let Some(window) = &value.plateau {
            writer.write_record([
                value.cd_dim.to_string(),
                value.n_components.to_string(),
                value.nodes_per_component.to_string(),
                format!("{:.17e}", window.d_s),
                format!("{:.17e}", window.ln_t_min),
                format!("{:.17e}", window.ln_t_max),
                format!("{:.17e}", window.flatness_score),
            ])?;
        }
    }
    writer.flush()?;

    let eigen_path = cli.output_dir.join("zd_spectral_full_trace_v2_eigenvalues.csv");
    let mut writer = csv::Writer::from_path(&eigen_path)?;
    writer.write_record(["cd_dim", "eigenvalue_index", "eigenvalue"])?;
    for value in &result.dimensions {
        for (index, eigenvalue) in value.eigenvalues.iter().enumerate() {
            writer.write_record([
                value.cd_dim.to_string(), index.to_string(), format!("{eigenvalue:.17e}"),
            ])?;
        }
    }
    writer.flush()?;

    let gap_path = cli.output_dir.join("zd_spectral_first_component_v2_gap.csv");
    let mut writer = csv::Writer::from_path(&gap_path)?;
    writer.write_record([
        "cd_dim", "n_components", "first_component_nodes", "lambda_2",
        "lambda_max", "gap_ratio", "finite_gap_heuristic",
    ])?;
    for value in spectral_gap_census(&dims) {
        writer.write_record([
            value.cd_dim.to_string(),
            value.n_components.to_string(),
            value.nodes_per_component.to_string(),
            format!("{:.17e}", value.lambda_2),
            format!("{:.17e}", value.lambda_max),
            format!("{:.17e}", value.gap_ratio),
            value.is_expander.to_string(),
        ])?;
    }
    writer.flush()?;
    eprintln!("Versioned full-trace files written to {}", cli.output_dir.display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dimension_ladder_is_finite_and_validated() {
        assert_eq!(dimensions(16, 64).unwrap(), vec![16, 32, 64]);
        assert!(dimensions(0, 256).is_err());
        assert!(dimensions(17, 256).is_err());
        assert!(dimensions(64, 16).is_err());
        assert!(dimensions(16, 65).is_err());
        let last = 1_usize << (usize::BITS - 1);
        assert_eq!(dimensions(last, last).unwrap(), vec![last]);
    }
}
