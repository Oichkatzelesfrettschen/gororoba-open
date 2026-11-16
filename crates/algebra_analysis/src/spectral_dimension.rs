// SPDX-License-Identifier: MIT
//! Finite-graph heat traces and scale-dependent spectral dimensions.
//!
//! The return probability is Tr(exp(-t L))/N, including every zero mode.
//! Its logarithmic derivative is evaluated analytically from the spectrum,
//! rather than by smoothing and differencing a possibly underflowed trace.
//! For a finite graph the full-trace dimension tends to zero at both ends
//! of diffusion time. A continuum-like plateau, when present, is intermediate.
//! The positive-mode relaxation trace is a separately named observable.
//! None of these graph observables establishes physical spacetime dimensions.

use nalgebra::{DMatrix, DVector};
use petgraph::graph::UnGraph;

use crate::boxkites::{MotifComponent, motif_components_for_cross_assessors};

/// Which eigenmodes participate in the normalized trace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeatTraceConvention {
    /// Uniform mean of return probabilities, including stationary modes.
    Full,
    /// Normalized positive-mode relaxation; not a graph return probability.
    PositiveModes,
}

/// Invalid spectrum, time, or unrepresentable numerical result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeatTraceError {
    EmptySpectrum,
    InvalidSpectrum,
    InvalidTime,
    NoPositiveModes,
    NumericalOverflow,
}

/// Stable heat-trace evaluation. A finite log trace may have an underflowed
/// probability of zero; its logarithmic derivative remains available.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct HeatTrace {
    pub probability: f64,
    pub log_probability: f64,
    pub spectral_dimension: f64,
    pub zero_modes: usize,
    pub retained_modes: usize,
    pub convention: HeatTraceConvention,
}

/// Evaluate a declared trace and d_s(t) = -2 d ln(P)/d ln(t).
///
/// A shifted exponential sum avoids underflow in the logarithmic derivative.
/// The caller must clamp eigensolver roundoff before passing a Laplacian
/// spectrum: negative or non-finite eigenvalues are not silently discarded.
///
/// # Errors
/// Rejects an empty or invalid spectrum, negative/non-finite time, absent
/// positive modes under that convention, or unrepresentable results.
pub fn evaluate_heat_trace(
    eigenvalues: &[f64],
    t: f64,
    convention: HeatTraceConvention,
) -> Result<HeatTrace, HeatTraceError> {
    if eigenvalues.is_empty() {
        return Err(HeatTraceError::EmptySpectrum);
    }
    if !t.is_finite() || t < 0.0 {
        return Err(HeatTraceError::InvalidTime);
    }
    if eigenvalues.iter().any(|x| !x.is_finite() || *x < 0.0) {
        return Err(HeatTraceError::InvalidSpectrum);
    }
    let keep = |x: &&f64| convention == HeatTraceConvention::Full || **x > 0.0;
    let retained_modes = eigenvalues.iter().filter(keep).count();
    if retained_modes == 0 {
        return Err(HeatTraceError::NoPositiveModes);
    }
    let minimum = eigenvalues
        .iter()
        .filter(keep)
        .copied()
        .fold(f64::INFINITY, f64::min);
    let base = minimum * t;
    if !base.is_finite() {
        return Err(HeatTraceError::NumericalOverflow);
    }
    let (sum, moment) = eigenvalues.iter().filter(keep).fold(
        (0.0_f64, 0.0_f64),
        |(sum, moment), &eigenvalue| {
            let exponent = (eigenvalue - minimum) * t;
            if exponent.is_infinite() {
                // lim x exp(-x) = 0; never evaluate infinity times zero.
                (sum, moment)
            } else {
                let weight = (-exponent).exp();
                (sum + weight, moment + exponent * weight)
            }
        },
    );
    let log_probability = -base + sum.ln() - (retained_modes as f64).ln();
    let spectral_dimension = 2.0 * (base + moment / sum);
    if !log_probability.is_finite() || !spectral_dimension.is_finite() {
        return Err(HeatTraceError::NumericalOverflow);
    }
    Ok(HeatTrace {
        probability: log_probability.exp(),
        log_probability,
        spectral_dimension,
        zero_modes: eigenvalues.iter().filter(|&&x| x == 0.0).count(),
        retained_modes,
        convention,
    })
}

/// Full finite-graph return probability, including all stationary modes.
///
/// # Panics
/// Panics on invalid inputs; use evaluate_heat_trace for a checked interface.
pub fn heat_kernel_return_probability(eigenvalues: &[f64], t: f64) -> f64 {
    evaluate_heat_trace(eigenvalues, t, HeatTraceConvention::Full)
        .expect("full heat trace requires a valid nonempty spectrum and time")
        .probability
}

/// Legacy positive-mode normalization, deliberately not called a return probability.
///
/// # Errors
/// Rejects invalid inputs and a spectrum without positive modes.
pub fn positive_mode_relaxation_trace(
    eigenvalues: &[f64],
    t: f64,
) -> Result<HeatTrace, HeatTraceError> {
    evaluate_heat_trace(eigenvalues, t, HeatTraceConvention::PositiveModes)
}

/// A flat-window candidate; the score is not a coefficient of determination.
#[derive(Debug, Clone)]
pub struct PlateauFit {
    pub d_s: f64,
    pub ln_t_min: f64,
    pub ln_t_max: f64,
    /// max(0, 1 - standard_deviation/abs(mean)); a perfectly zero window is 1.
    pub flatness_score: f64,
}

/// Analysis of the first cross-assessor component, with its full spectrum.
/// Other components are counted, not assumed isospectral or aggregated.
#[derive(Debug, Clone)]
pub struct DimensionResult {
    pub cd_dim: usize,
    pub n_components: usize,
    pub nodes_per_component: usize,
    pub curve: Vec<(f64, f64)>,
    pub plateau: Option<PlateauFit>,
    pub eigenvalues: Vec<f64>,
}

#[derive(Debug, Clone)]
pub struct DimensionalFlowResult {
    pub dimensions: Vec<DimensionResult>,
}

pub trait EigenSolver {
    fn eigenvalues(&self, matrix: &DMatrix<f64>) -> Vec<f64>;
}

pub struct DenseEigenSolver;

impl EigenSolver for DenseEigenSolver {
    fn eigenvalues(&self, matrix: &DMatrix<f64>) -> Vec<f64> {
        let eigen = matrix.clone().symmetric_eigen();
        let mut values: Vec<_> = eigen.eigenvalues.iter().copied().collect();
        values.sort_by(f64::total_cmp);
        values
    }
}

/// Combinatorial Laplacian with compact indices even after graph-node removal.
pub fn build_graph_laplacian(graph: &UnGraph<(), ()>) -> DMatrix<f64> {
    let indices: std::collections::HashMap<_, _> = graph
        .node_indices()
        .enumerate()
        .map(|(index, node)| (node, index))
        .collect();
    let mut laplacian = DMatrix::zeros(indices.len(), indices.len());
    for edge in graph.edge_indices() {
        let (u, v) = graph.edge_endpoints(edge).expect("existing edge has endpoints");
        let (i, j) = (indices[&u], indices[&v]);
        laplacian[(i, i)] += 1.0;
        laplacian[(j, j)] += 1.0;
        laplacian[(i, j)] -= 1.0;
        laplacian[(j, i)] -= 1.0;
    }
    laplacian
}

pub fn build_laplacian_from_component(component: &MotifComponent) -> DMatrix<f64> {
    let indices: std::collections::HashMap<_, _> = component
        .nodes
        .iter()
        .enumerate()
        .map(|(index, &node)| (node, index))
        .collect();
    let mut laplacian = DMatrix::zeros(indices.len(), indices.len());
    for &(u, v) in &component.edges {
        let (i, j) = (indices[&u], indices[&v]);
        laplacian[(i, i)] += 1.0;
        laplacian[(j, j)] += 1.0;
        laplacian[(i, j)] -= 1.0;
        laplacian[(j, i)] -= 1.0;
    }
    laplacian
}

/// Clamp only caller-declared numerical dust.
///
/// # Panics
/// Panics if epsilon is negative/non-finite or an eigenvalue is non-finite.
pub fn clamp_zero_eigenvalues(eigenvalues: &mut [f64], epsilon: f64) {
    assert!(epsilon.is_finite() && epsilon >= 0.0, "invalid clamp tolerance");
    for eigenvalue in eigenvalues {
        assert!(eigenvalue.is_finite(), "non-finite eigenvalue");
        if eigenvalue.abs() <= epsilon {
            *eigenvalue = 0.0;
        }
    }
}

/// Positive logarithmic grid, using log interpolation to avoid ratio overflow.
///
/// # Panics
/// Panics unless n >= 2 and 0 < t_min < t_max are finite.
pub fn geom_linspace(t_min: f64, t_max: f64, n: usize) -> Vec<f64> {
    assert!(n >= 2, "need at least two points");
    assert!(t_min.is_finite() && t_min > 0.0, "invalid minimum time");
    assert!(t_max.is_finite() && t_max > t_min, "invalid maximum time");
    let low = t_min.ln();
    let high = t_max.ln();
    (0..n)
        .map(|i| {
            if i == 0 {
                t_min
            } else if i == n - 1 {
                t_max
            } else {
                (low + (high - low) * i as f64 / (n - 1) as f64).exp()
            }
        })
        .collect()
}

/// Savitzky-Golay helper retained for callers; not used to estimate heat-trace slopes.
/// A short input is unchanged. Fits use an SVD, not singular normal equations.
///
/// # Panics
/// Panics on invalid window/order, non-finite values or nonuniform abscissae.
pub fn savitzky_golay_smooth(
    data: &[(f64, f64)],
    window: usize,
    order: usize,
) -> Vec<(f64, f64)> {
    assert!(window >= 3 && window % 2 == 1 && order < window, "invalid smoothing window");
    assert!(data.iter().all(|(x, y)| x.is_finite() && y.is_finite()), "non-finite data");
    if data.len() < window {
        return data.to_vec();
    }
    let spacing = data[1].0 - data[0].0;
    assert!(spacing > 0.0 && spacing.is_finite(), "invalid abscissa spacing");
    assert!(
        data.windows(2).all(|pair| {
            let actual = pair[1].0 - pair[0].0;
            (actual - spacing).abs() <= 1e-9 * spacing
        }),
        "smoothing requires uniform abscissae",
    );
    let half = window / 2;
    let design = DMatrix::from_fn(order + 1, window, |power, point| {
        let x = (point as f64 - half as f64) / half as f64;
        (0..power).fold(1.0, |value, _| value * x)
    });
    let mut target = DVector::zeros(order + 1);
    target[0] = 1.0;
    let weights = design
        .svd(true, true)
        .solve(&target, f64::EPSILON * window as f64)
        .expect("valid smoothing design has a least-squares solution");
    let mut output = data.to_vec();
    for i in half..data.len() - half {
        output[i].1 = weights
            .iter()
            .enumerate()
            .map(|(j, weight)| weight * data[i + j - half].1)
            .sum();
    }
    output
}

/// Exact logarithmic derivative at the interior grid points (n_points - 2).
/// This preserves the historical grid shape but changes its trace definition.
///
/// # Panics
/// Panics on invalid spectrum/grid; no smoothed underflow is interpreted as data.
pub fn graph_spectral_dimension(
    eigenvalues: &[f64],
    t_min: f64,
    t_max: f64,
    n_points: usize,
) -> Vec<(f64, f64)> {
    assert!(n_points >= 3, "need at least three spectral samples");
    geom_linspace(t_min, t_max, n_points)
        .into_iter()
        .skip(1)
        .take(n_points - 2)
        .map(|t| {
            let value = evaluate_heat_trace(eigenvalues, t, HeatTraceConvention::Full)
                .expect("spectral dimension requires a valid full heat trace");
            (t.ln(), value.spectral_dimension)
        })
        .collect()
}

/// Longest interior flat-window candidate under a caller-declared slope threshold.
/// A finite-graph zero-dimensional endpoint is also flat; this diagnostic alone
/// does not identify a continuum plateau, its extent or a physical dimension.
/// Invalid/non-finite/nonincreasing data return no candidate.
pub fn extract_plateau(curve: &[(f64, f64)], threshold: f64) -> Option<PlateauFit> {
    if curve.len() < 5
        || !threshold.is_finite()
        || threshold < 0.0
        || curve.iter().any(|(x, y)| !x.is_finite() || !y.is_finite())
        || curve.windows(2).any(|pair| pair[1].0 <= pair[0].0)
    {
        return None;
    }
    let (mut best_start, mut best_length, mut start, mut length) = (0, 0, 0, 0);
    for i in 1..curve.len() - 1 {
        let slope = (curve[i + 1].1 - curve[i - 1].1) / (curve[i + 1].0 - curve[i - 1].0);
        if slope.abs() <= threshold {
            if length == 0 {
                start = i;
            }
            length += 1;
            if length > best_length {
                best_start = start;
                best_length = length;
            }
        } else {
            length = 0;
        }
    }
    if best_length < 3 {
        return None;
    }
    let selected = &curve[best_start..best_start + best_length];
    let scale = selected.iter().map(|(_, y)| y.abs()).fold(0.0_f64, f64::max);
    let (mean, score) = if scale == 0.0 {
        (0.0, 1.0)
    } else {
        let scaled_mean = selected.iter().map(|(_, y)| y / scale).sum::<f64>() / best_length as f64;
        let variance = selected
            .iter()
            .map(|(_, y)| (y / scale - scaled_mean).powi(2))
            .sum::<f64>()
            / best_length as f64;
        let score = if scaled_mean == 0.0 { 0.0 } else { (1.0 - variance.sqrt() / scaled_mean.abs()).max(0.0) };
        (scale * scaled_mean, score)
    };
    Some(PlateauFit {
        d_s: mean,
        ln_t_min: selected[0].0,
        ln_t_max: selected[selected.len() - 1].0,
        flatness_score: score,
    })
}

/// Full spectrum of the FIRST cross-assessor component, not the disconnected union.
/// The caller must not assume the remaining components are isospectral.
pub fn zd_laplacian_eigenvalues(dim: usize) -> Vec<f64> {
    let components = motif_components_for_cross_assessors(dim);
    let Some(first) = components.first() else {
        return Vec::new();
    };
    let mut eigenvalues = DenseEigenSolver.eigenvalues(&build_laplacian_from_component(first));
    clamp_zero_eigenvalues(&mut eigenvalues, 1e-12);
    eigenvalues
}

pub fn analyze_single_dimension(dim: usize, t_min: f64, t_max: f64, n_points: usize) -> DimensionResult {
    let components = motif_components_for_cross_assessors(dim);
    let n_components = components.len();
    let nodes_per_component = components.first().map_or(0, |component| component.nodes.len());
    let eigenvalues = zd_laplacian_eigenvalues(dim);
    let curve = if eigenvalues.is_empty() {
        Vec::new()
    } else {
        graph_spectral_dimension(&eigenvalues, t_min, t_max, n_points)
    };
    let threshold = if nodes_per_component <= 10 { 0.5 } else { 0.2 };
    let plateau = extract_plateau(&curve, threshold);
    DimensionResult { cd_dim: dim, n_components, nodes_per_component, curve, plateau, eigenvalues }
}

pub fn dimensional_flow_analysis(dims: &[usize], t_min: f64, t_max: f64, n_points: usize) -> DimensionalFlowResult {
    DimensionalFlowResult {
        dimensions: dims.iter().map(|&dim| analyze_single_dimension(dim, t_min, t_max, n_points)).collect(),
    }
}

#[derive(Debug, Clone)]
pub struct SpectralGapResult {
    pub cd_dim: usize,
    pub n_components: usize,
    pub nodes_per_component: usize,
    pub lambda_2: f64,
    pub lambda_max: f64,
    pub gap_ratio: f64,
    /// Historical finite-graph screening heuristic, not a proof of an expander family.
    pub is_expander: bool,
    pub eigenvalues: Vec<f64>,
}

/// Smallest positive eigenvalue, independent of input ordering; zero if absent.
pub fn spectral_gap(eigenvalues: &[f64]) -> f64 {
    eigenvalues.iter().copied().filter(|&x| x > 0.0).min_by(f64::total_cmp).unwrap_or(0.0)
}

pub fn spectral_gap_census(dims: &[usize]) -> Vec<SpectralGapResult> {
    dims.iter().map(|&dim| {
        let components = motif_components_for_cross_assessors(dim);
        let nodes_per_component = components.first().map_or(0, |component| component.nodes.len());
        let mut eigenvalues = zd_laplacian_eigenvalues(dim);
        eigenvalues.retain(|&value| value > 0.0);
        let lambda_2 = spectral_gap(&eigenvalues);
        let lambda_max = eigenvalues.iter().copied().fold(0.0_f64, f64::max);
        let gap_ratio = if lambda_max > 0.0 { lambda_2 / lambda_max } else { 0.0 };
        SpectralGapResult {
            cd_dim: dim,
            n_components: components.len(),
            nodes_per_component,
            lambda_2,
            lambda_max,
            gap_ratio,
            is_expander: nodes_per_component > 0 && gap_ratio > 1.0 / (2.0 * nodes_per_component as f64),
            eigenvalues,
        }
    }).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn complete_graph(n: usize) -> UnGraph<(), ()> {
        let mut graph = UnGraph::new_undirected();
        let nodes: Vec<_> = (0..n).map(|_| graph.add_node(())).collect();
        for i in 0..n {
            for j in i + 1..n { graph.add_edge(nodes[i], nodes[j], ()); }
        }
        graph
    }

    #[test]
    fn two_node_trace_includes_stationary_mode() {
        for t in [0.0_f64, 0.1, 0.5, 1.0, 5.0, 1e6] {
            let result = evaluate_heat_trace(&[0.0, 2.0], t, HeatTraceConvention::Full).unwrap();
            let exponential = (-2.0 * t).exp();
            assert!((result.probability - (1.0 + exponential) / 2.0).abs() < 1e-14);
            assert!((result.spectral_dimension - 4.0 * t * exponential / (1.0 + exponential)).abs() < 1e-14);
            assert_eq!(result.zero_modes, 1);
        }
    }

    #[test]
    fn positive_modes_are_a_distinct_observable() {
        let result = positive_mode_relaxation_trace(&[0.0, 2.0], 1000.0).unwrap();
        assert_eq!(result.spectral_dimension, 4000.0);
        assert_eq!(result.log_probability, -2000.0);
        assert_eq!(result.probability, 0.0);
        assert_eq!(result.retained_modes, 1);
    }

    #[test]
    fn disconnected_limit_and_isolated_vertices() {
        let result = evaluate_heat_trace(&[0.0, 0.0, 2.0, 3.0], 1e6, HeatTraceConvention::Full).unwrap();
        assert!((result.probability - 0.5).abs() < 1e-14);
        assert_eq!(result.spectral_dimension, 0.0);
        let isolated = evaluate_heat_trace(&[0.0, 0.0], 1e300, HeatTraceConvention::Full).unwrap();
        assert_eq!(isolated.probability, 1.0);
        assert_eq!(isolated.spectral_dimension, 0.0);
        assert_eq!(positive_mode_relaxation_trace(&[0.0], 1.0), Err(HeatTraceError::NoPositiveModes));
    }

    #[test]
    fn invalid_spectrum_and_time_are_refused() {
        for spectrum in [&[-1.0][..], &[f64::NAN][..], &[f64::INFINITY][..]] {
            assert_eq!(evaluate_heat_trace(spectrum, 1.0, HeatTraceConvention::Full), Err(HeatTraceError::InvalidSpectrum));
        }
        assert_eq!(evaluate_heat_trace(&[], 1.0, HeatTraceConvention::Full), Err(HeatTraceError::EmptySpectrum));
        for t in [-1.0, f64::NAN, f64::INFINITY] {
            assert_eq!(evaluate_heat_trace(&[0.0], t, HeatTraceConvention::Full), Err(HeatTraceError::InvalidTime));
        }
    }

    #[test]
    fn overflowing_positive_exponents_have_zero_weight() {
        let result = evaluate_heat_trace(&[0.0, f64::MAX], f64::MAX, HeatTraceConvention::Full).unwrap();
        assert!((result.probability - 0.5).abs() < 1e-14);
        assert_eq!(result.spectral_dimension, 0.0);
        assert_eq!(positive_mode_relaxation_trace(&[f64::MAX], f64::MAX), Err(HeatTraceError::NumericalOverflow));
    }

    #[test]
    fn complete_graph_has_finite_size_return_not_linear_divergence() {
        let graph = complete_graph(6);
        let mut spectrum = DenseEigenSolver.eigenvalues(&build_graph_laplacian(&graph));
        clamp_zero_eigenvalues(&mut spectrum, 1e-12);
        assert_eq!(spectrum.iter().filter(|&&x| x == 0.0).count(), 1);
        assert!((spectral_gap(&spectrum) - 6.0).abs() < 1e-10);
        let curve = graph_spectral_dimension(&spectrum, 0.01, 10.0, 200);
        assert_eq!(curve.len(), 198);
        for &(log_t, dimension) in &curve {
            let t = log_t.exp();
            let exponential = (-6.0 * t).exp();
            let expected = 60.0 * t * exponential / (1.0 + 5.0 * exponential);
            assert!((dimension - expected).abs() < 1e-10);
        }
        assert!(curve.last().unwrap().1 < 1e-20);
    }

    #[test]
    fn cycle_has_intermediate_one_dimensional_window() {
        let n = 100;
        let spectrum: Vec<_> = (0..n).map(|k| 2.0 - 2.0 * (std::f64::consts::TAU * k as f64 / n as f64).cos()).collect();
        for t in [20.0, 30.0, 50.0] {
            let dimension = evaluate_heat_trace(&spectrum, t, HeatTraceConvention::Full).unwrap().spectral_dimension;
            assert!((dimension - 1.0).abs() < 0.02);
        }
        assert!(evaluate_heat_trace(&spectrum, 1e6, HeatTraceConvention::Full).unwrap().spectral_dimension < 1e-20);
    }

    #[test]
    fn normalized_union_of_identical_components_preserves_trace() {
        let spectrum = [0.0, 2.0, 3.0];
        let union = spectrum.repeat(7);
        for t in [0.0, 0.1, 2.0, 100.0] {
            let a = evaluate_heat_trace(&spectrum, t, HeatTraceConvention::Full).unwrap();
            let b = evaluate_heat_trace(&union, t, HeatTraceConvention::Full).unwrap();
            assert!((a.probability - b.probability).abs() < 1e-14);
            assert!((a.spectral_dimension - b.spectral_dimension).abs() < 1e-14);
        }
    }

    #[test]
    fn spectrum_rescaling_is_inverse_time_rescaling() {
        let a = evaluate_heat_trace(&[0.0, 1.0, 3.0], 0.7, HeatTraceConvention::Full).unwrap();
        let b = evaluate_heat_trace(&[0.0, 4.0, 12.0], 0.175, HeatTraceConvention::Full).unwrap();
        assert!((a.probability - b.probability).abs() < 1e-14);
        assert!((a.spectral_dimension - b.spectral_dimension).abs() < 1e-14);
    }

    #[test]
    fn logarithmic_grid_handles_wide_dynamic_range() {
        let times = geom_linspace(1e-200, 1e200, 11);
        assert_eq!(times[0], 1e-200);
        assert_eq!(times[10], 1e200);
        assert!(times.iter().all(|t| t.is_finite() && *t > 0.0));
        assert!(times.windows(2).all(|pair| pair[1] > pair[0]));
    }

    #[test]
    fn smoothing_preserves_polynomials() {
        for degree in 0_i32..=3 {
            let data: Vec<_> = (0..30).map(|i| (i as f64, (i as f64 / 30.0).powi(degree))).collect();
            let smooth = savitzky_golay_smooth(&data, 7, 3);
            for (a, b) in data.iter().zip(smooth) { assert!((a.1 - b.1).abs() < 1e-12); }
        }
    }

    #[test]
    fn flatness_is_named_and_invalid_candidates_are_absent() {
        let data: Vec<_> = (0..10).map(|i| (i as f64, 1.0)).collect();
        let candidate = extract_plateau(&data, 0.0).unwrap();
        assert_eq!(candidate.d_s, 1.0);
        assert_eq!(candidate.flatness_score, 1.0);
        assert!(extract_plateau(&[(0.0, f64::NAN); 6], 0.5).is_none());
        assert!(extract_plateau(&data, -1.0).is_none());
    }

    #[test]
    fn representative_component_keeps_its_zero_mode() {
        let result = analyze_single_dimension(16, 0.01, 50.0, 100);
        assert_eq!(result.n_components, 7);
        assert_eq!(result.nodes_per_component, 6);
        assert_eq!(result.eigenvalues.len(), 6);
        assert_eq!(result.eigenvalues.iter().filter(|&&x| x == 0.0).count(), 1);
        assert!(!result.curve.is_empty());
    }
}
