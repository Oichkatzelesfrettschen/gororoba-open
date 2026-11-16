// SPDX-License-Identifier: MIT
//! Tensor-network entropy facade with declared subsystem semantics.
//!
//! Site zero is the most significant state-vector bit. Entropies are in
//! nats. These types represent pure states; reduced entropy is not an
//! entanglement measure for an arbitrary mixed global state. PEPS row-cut
//! approximations are not substituted for an exact subsystem contraction.

use nalgebra::{DMatrix, SVD};
use num_complex::Complex64;
use rayon::prelude::*;

pub use crate::mps::{MatrixProductState, MpsTensor};
pub use crate::peps::{Peps, PepsTensor};
pub use crate::tensor_network_classical::{
    CircuitEvolutionResult, EntropyResult, TensorNetworkState, bell_state_entropy,
    ghz_state_entropy, prepare_bell_state, prepare_ghz_state, simulate_random_circuit,
};

/// Default bound on a dense coefficient matrix or an MPS bond Gram matrix.
/// SVD/eigensolver workspace is additional. The dense helper accepts a budget.
pub const DEFAULT_ENTROPY_AMPLITUDE_LIMIT: usize = 1 << 20;

/// Invalid state, partition, tolerance, or unsupported contraction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntropyError {
    /// A subsystem repeats a site or addresses a site outside the state.
    InvalidSubsystem,
    /// Coefficients or tensor dimensions do not define a finite nonzero state.
    InvalidState,
    /// The requested contraction exceeds its declared matrix-element budget.
    AllocationLimit,
    /// The backend has no exact contraction for the requested question.
    UnsupportedContraction,
    /// A product-state tolerance is negative or non-finite.
    InvalidTolerance,
    /// A finite decomposition fails to converge or violates positivity.
    NumericalFailure,
}

fn partition(n_sites: usize, subsystem: &[usize]) -> Result<Vec<usize>, EntropyError> {
    let mut selected = subsystem.to_vec();
    selected.sort_unstable();
    if selected.iter().any(|&site| site >= n_sites)
        || selected.windows(2).any(|pair| pair[0] == pair[1])
    {
        return Err(EntropyError::InvalidSubsystem);
    }
    Ok(selected)
}

fn state_size(n_sites: usize) -> Result<usize, EntropyError> {
    u32::try_from(n_sites)
        .ok()
        .and_then(|bits| 1_usize.checked_shl(bits))
        .ok_or(EntropyError::AllocationLimit)
}

/// Exact pure-state entropy of an arbitrary set of qubit sites, in nats.
///
/// The smaller partition is the SVD row index. Nonzero inputs are normalized
/// through their Schmidt weights. The input coefficients are not mutated.
///
/// # Errors
/// Rejects invalid sites, coefficient count, non-finite or zero states, and
/// a dense coefficient matrix above `max_amplitudes` (excluding SVD workspace).
pub fn pure_state_subsystem_entropy(
    coefficients: &[Complex64],
    n_sites: usize,
    subsystem: &[usize],
    max_amplitudes: usize,
) -> Result<f64, EntropyError> {
    let selected = partition(n_sites, subsystem)?;
    let size = state_size(n_sites)?;
    if coefficients.len() != size
        || coefficients
            .iter()
            .any(|z| !z.re.is_finite() || !z.im.is_finite())
    {
        return Err(EntropyError::InvalidState);
    }
    let maximum = coefficients
        .iter()
        .map(|z| z.re.abs().max(z.im.abs()))
        .fold(0.0_f64, f64::max);
    if maximum == 0.0 || !maximum.is_finite() {
        return Err(EntropyError::InvalidState);
    }
    if selected.is_empty() || selected.len() == n_sites {
        return Ok(0.0);
    }
    if size > max_amplitudes {
        return Err(EntropyError::AllocationLimit);
    }
    let complement: Vec<_> = (0..n_sites)
        .filter(|site| !selected.contains(site))
        .collect();
    let (rows, columns) = if selected.len() <= complement.len() {
        (&selected, &complement)
    } else {
        (&complement, &selected)
    };
    let extract = |index: usize, sites: &[usize]| {
        sites.iter().fold(0_usize, |word, &site| {
            (word << 1) | ((index >> (n_sites - 1 - site)) & 1)
        })
    };
    let mut matrix =
        DMatrix::<Complex64>::zeros(state_size(rows.len())?, state_size(columns.len())?);
    for (index, &coefficient) in coefficients.iter().enumerate() {
        matrix[(extract(index, rows), extract(index, columns))] = coefficient / maximum;
    }
    let singular = matrix.svd(false, false).singular_values;
    let normalization: f64 = singular.iter().map(|s| s * s).sum();
    if !normalization.is_finite() || normalization <= 0.0 {
        return Err(EntropyError::InvalidState);
    }
    let entropy: f64 = singular
        .iter()
        .map(|s| s * s / normalization)
        .filter(|&p| p > 0.0)
        .map(|p| -p * p.ln())
        .sum();
    if entropy.is_finite() {
        Ok(entropy.max(0.0))
    } else {
        Err(EntropyError::InvalidState)
    }
}

/// Pure-state entropies with checked partition support.
pub trait EntanglementMeasure {
    /// Entropy of exactly the named sites in nats.
    ///
    /// # Errors
    /// Returns an error for invalid state, unsupported partition, or budget.
    fn try_entanglement_entropy(&self, subsystem: &[usize]) -> Result<f64, EntropyError>;

    /// Compatibility entry point for an exact supported partition.
    ///
    /// # Panics
    /// Panics when the checked method returns an error. Use that method when
    /// the partition or contraction cost is not already qualified.
    fn entanglement_entropy(&self, subsystem: &[usize]) -> f64 {
        self.try_entanglement_entropy(subsystem)
            .expect("entropy requires a valid state and a supported exact partition")
    }

    /// Check every prefix cut of a pure state, not only the first site.
    /// The tolerance applies per cut, not to a global distance from product.
    ///
    /// # Errors
    /// Returns an error for invalid tolerance or any unavailable entropy.
    fn try_is_product_state(&self, tolerance: f64) -> Result<bool, EntropyError> {
        if !tolerance.is_finite() || tolerance < 0.0 {
            return Err(EntropyError::InvalidTolerance);
        }
        self.try_entanglement_entropy(&[])?;
        for cut in 1..self.n_sites() {
            let sites: Vec<_> = (0..cut).collect();
            if self.try_entanglement_entropy(&sites)? > tolerance {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Compatibility product test for exact supported cuts.
    ///
    /// # Panics
    /// Panics on invalid tolerance or unavailable contraction.
    fn is_product_state(&self, tolerance: f64) -> bool {
        self.try_is_product_state(tolerance)
            .expect("product test requires all relevant exact cuts")
    }

    /// Number of qubit sites.
    fn n_sites(&self) -> usize;
}

impl EntanglementMeasure for TensorNetworkState {
    fn try_entanglement_entropy(&self, subsystem: &[usize]) -> Result<f64, EntropyError> {
        let selected = partition(self.n_qubits(), subsystem)?;
        if selected.is_empty() || selected.len() == self.n_qubits() {
            // A trivial cut has zero entropy; the real coefficients are
            // checked in place so no complex copy is built.
            return real_state_cut_entropy(self.coefficients(), self.n_qubits());
        }
        if state_size(self.n_qubits())? > DEFAULT_ENTROPY_AMPLITUDE_LIMIT {
            return Err(EntropyError::AllocationLimit);
        }
        let coefficients: Vec<_> = self
            .coefficients()
            .iter()
            .map(|&x| Complex64::new(x, 0.0))
            .collect();
        pure_state_subsystem_entropy(
            &coefficients,
            self.n_qubits(),
            subsystem,
            DEFAULT_ENTROPY_AMPLITUDE_LIMIT,
        )
    }

    fn n_sites(&self) -> usize {
        self.n_qubits()
    }
}

/// Zero entropy of an empty or full cut, after the same state checks as
/// `pure_state_subsystem_entropy`, read from real coefficients in place.
fn real_state_cut_entropy(coefficients: &[f64], n_sites: usize) -> Result<f64, EntropyError> {
    if coefficients.len() != state_size(n_sites)? || coefficients.iter().any(|x| !x.is_finite()) {
        return Err(EntropyError::InvalidState);
    }
    if coefficients.iter().all(|&x| x == 0.0) {
        return Err(EntropyError::InvalidState);
    }
    Ok(0.0)
}

fn validate_mps(state: &MatrixProductState) -> Result<(), EntropyError> {
    if state.tensors.len() != state.n_qubits {
        return Err(EntropyError::InvalidState);
    }
    let mut previous_right = 1;
    for tensor in &state.tensors {
        let expected = tensor
            .chi_left
            .checked_mul(2)
            .and_then(|n| n.checked_mul(tensor.chi_right));
        if tensor.physical_dim != 2
            || tensor.chi_left != previous_right
            || tensor.chi_right == 0
            || expected != Some(tensor.data.len())
            || tensor
                .data
                .iter()
                .any(|z| !z.re.is_finite() || !z.im.is_finite())
            || tensor.data.iter().all(|z| z.re == 0.0 && z.im == 0.0)
        {
            return Err(EntropyError::InvalidState);
        }
        for bond in [tensor.chi_left, tensor.chi_right] {
            if bond
                .checked_mul(bond)
                .is_none_or(|n| n > DEFAULT_ENTROPY_AMPLITUDE_LIMIT)
            {
                return Err(EntropyError::AllocationLimit);
            }
        }
        previous_right = tensor.chi_right;
    }
    if previous_right != 1 {
        return Err(EntropyError::InvalidState);
    }
    Ok(())
}

fn max_component(values: impl Iterator<Item = Complex64>) -> f64 {
    values
        .map(|z| z.re.abs().max(z.im.abs()))
        .fold(0.0_f64, f64::max)
}

/// Left-canonical form of a validated MPS by a QR sweep, one matrix per site.
///
/// Row `2 * left + physical` and column `right` index each matrix, whose
/// columns are orthonormal, so the chain contracts to the original state up
/// to one positive global scale and no entry of a partial contraction exceeds
/// one. Each tensor is divided by its largest component, the triangular
/// factor carried from the previous site is absorbed, and the columns of the
/// product are equilibrated before the QR, so bond gauges that cancel across
/// sites (`diag(1e100, 1e-100)` against its inverse) are never squared or
/// multiplied into an underflowing partial product. The dropped scale is
/// irrelevant to every entropy, which normalizes its input.
fn mps_left_canonical(state: &MatrixProductState) -> Result<Vec<DMatrix<Complex64>>, EntropyError> {
    let mut carry = DMatrix::from_element(1, 1, Complex64::new(1.0, 0.0));
    let mut sites = Vec::with_capacity(state.n_qubits);
    for tensor in &state.tensors {
        let entries: Vec<Complex64> = tensor
            .data
            .iter()
            .map(|z| Complex64::new(z.re, z.im))
            .collect();
        let tensor_scale = max_component(entries.iter().copied());
        let rows = carry.nrows();
        let mut block = DMatrix::<Complex64>::zeros(rows * 2, tensor.chi_right);
        for j in 0..rows {
            for physical in 0..2 {
                for right in 0..tensor.chi_right {
                    let mut sum = Complex64::new(0.0, 0.0);
                    for left in 0..tensor.chi_left {
                        let entry = entries[(left * 2 + physical) * tensor.chi_right + right];
                        sum += carry[(j, left)] * (entry / tensor_scale);
                    }
                    block[(j * 2 + physical, right)] = sum;
                }
            }
        }
        let scale = max_component(block.iter().copied());
        if scale == 0.0 || !scale.is_finite() {
            return Err(EntropyError::InvalidState);
        }
        for z in block.iter_mut() {
            *z /= scale;
        }
        let column_scale: Vec<f64> = (0..block.ncols())
            .map(|column| {
                let largest = max_component(block.column(column).iter().copied());
                if largest > 0.0 { largest } else { 1.0 }
            })
            .collect();
        for (column, &factor) in column_scale.iter().enumerate() {
            for z in block.column_mut(column).iter_mut() {
                *z /= factor;
            }
        }
        let qr = block.qr();
        let mut triangular = qr.r();
        for (column, &factor) in column_scale.iter().enumerate() {
            for z in triangular.column_mut(column).iter_mut() {
                *z *= factor;
            }
        }
        sites.push(qr.q());
        carry = triangular;
    }
    Ok(sites)
}

/// Entropy in nats of the Schmidt probabilities s^2 / sum(s^2).
fn schmidt_entropy(values: &[f64]) -> Result<f64, EntropyError> {
    if values.iter().any(|&v| !v.is_finite() || v < 0.0) {
        return Err(EntropyError::NumericalFailure);
    }
    let top = values.iter().copied().fold(0.0_f64, f64::max);
    if top <= 0.0 {
        return Err(EntropyError::InvalidState);
    }
    let weights: Vec<f64> = values.iter().map(|&v| (v / top) * (v / top)).collect();
    let total: f64 = weights.iter().sum();
    let entropy: f64 = weights
        .iter()
        .map(|&w| w / total)
        .filter(|&p| p > 0.0)
        .map(|p| -p * p.ln())
        .sum();
    if entropy.is_finite() {
        Ok(entropy.max(0.0))
    } else {
        Err(EntropyError::NumericalFailure)
    }
}

/// Dense coefficients of a validated MPS, up to one positive global scale,
/// contracted from the left-canonical form so no partial product overflows
/// or underflows through a bond gauge.
fn mps_scaled_coefficients(state: &MatrixProductState) -> Result<Vec<Complex64>, EntropyError> {
    let n_sites = state.n_qubits;
    let sites = mps_left_canonical(state)?;
    let rows: Vec<Vec<Complex64>> = sites
        .iter()
        .map(|matrix| {
            (0..matrix.nrows())
                .flat_map(|row| (0..matrix.ncols()).map(move |column| (row, column)))
                .map(|(row, column)| matrix[(row, column)])
                .collect()
        })
        .collect();
    let size = state_size(n_sites)?;
    Ok((0..size)
        .into_par_iter()
        .map(|basis| {
            let mut row = vec![Complex64::new(1.0, 0.0)];
            for (site, matrix) in sites.iter().enumerate() {
                let physical = (basis >> (n_sites - 1 - site)) & 1;
                let width = matrix.ncols();
                let mut next = vec![Complex64::new(0.0, 0.0); width];
                for (left, &weight) in row.iter().enumerate() {
                    let base = (left * 2 + physical) * width;
                    for (slot, &value) in next.iter_mut().zip(&rows[site][base..base + width]) {
                        *slot += weight * value;
                    }
                }
                row = next;
            }
            row[0]
        })
        .collect())
}

/// Entropies in nats of every prefix cut of a pure MPS, indexed by the
/// number of sites on the left: the result has `n_qubits + 1` entries and
/// the first and last are zero.
///
/// A QR sweep from the left makes every site an isometry
/// (`mps_left_canonical`). A sweep back from the right then takes the
/// singular values of each bond matrix with the left part still an isometry
/// and the right part already an isometry, so they are the Schmidt
/// coefficients of that cut in any input gauge. The sweeps cost O(n chi^3)
/// for all cuts together and never form a Gram matrix, so a bond gauge is
/// never squared.
///
/// # Errors
/// Rejects invalid tensor chains, excessive bond-matrix allocation, zero
/// states and failed decompositions.
pub fn mps_cut_entropies(state: &MatrixProductState) -> Result<Vec<f64>, EntropyError> {
    validate_mps(state)?;
    let mut sites = mps_left_canonical(state)?;
    let mut entropies = vec![0.0; state.n_qubits + 1];
    for site in (1..sites.len()).rev() {
        let right = sites[site].ncols();
        let mut wide = DMatrix::from_fn(sites[site].nrows() / 2, 2 * right, |left, column| {
            sites[site][(left * 2 + column / right, column % right)]
        });
        let scale = max_component(wide.iter().copied());
        if scale == 0.0 || !scale.is_finite() {
            return Err(EntropyError::InvalidState);
        }
        for z in wide.iter_mut() {
            *z /= scale;
        }
        let svd = SVD::try_new(wide, true, false, f64::EPSILON, 100_000)
            .ok_or(EntropyError::NumericalFailure)?;
        let values: Vec<f64> = svd.singular_values.iter().copied().collect();
        entropies[site] = schmidt_entropy(&values)?;
        let mut carried = svd.u.ok_or(EntropyError::NumericalFailure)?;
        for (column, &value) in values.iter().enumerate() {
            for z in carried.column_mut(column).iter_mut() {
                *z *= value;
            }
        }
        sites[site - 1] = &sites[site - 1] * carried;
    }
    Ok(entropies)
}

/// Entropy of the first `cut` sites of a pure MPS, invariant under any
/// bond gauge (see `mps_cut_entropies`).
///
/// # Errors
/// As `mps_cut_entropies`, and `InvalidSubsystem` for `cut > n_qubits`.
pub fn mps_prefix_entropy(state: &MatrixProductState, cut: usize) -> Result<f64, EntropyError> {
    mps_cut_entropies(state)?
        .get(cut)
        .copied()
        .ok_or(EntropyError::InvalidSubsystem)
}

impl EntanglementMeasure for MatrixProductState {
    fn try_entanglement_entropy(&self, subsystem: &[usize]) -> Result<f64, EntropyError> {
        let selected = partition(self.n_qubits, subsystem)?;
        validate_mps(self)?;
        if selected.iter().copied().eq(0..selected.len()) {
            return mps_prefix_entropy(self, selected.len());
        }
        if selected
            .iter()
            .copied()
            .eq(self.n_qubits - selected.len()..self.n_qubits)
        {
            return mps_prefix_entropy(self, self.n_qubits - selected.len());
        }
        if state_size(self.n_qubits)? > DEFAULT_ENTROPY_AMPLITUDE_LIMIT {
            return Err(EntropyError::AllocationLimit);
        }
        let coefficients = mps_scaled_coefficients(self)?;
        pure_state_subsystem_entropy(
            &coefficients,
            self.n_qubits,
            &selected,
            DEFAULT_ENTROPY_AMPLITUDE_LIMIT,
        )
    }

    fn n_sites(&self) -> usize {
        self.n_qubits
    }

    /// One canonical sweep yields every cut entropy, so the test costs
    /// O(n chi^3) rather than one chain contraction per cut.
    fn try_is_product_state(&self, tolerance: f64) -> Result<bool, EntropyError> {
        if !tolerance.is_finite() || tolerance < 0.0 {
            return Err(EntropyError::InvalidTolerance);
        }
        Ok(mps_cut_entropies(self)?
            .iter()
            .all(|&entropy| entropy <= tolerance))
    }
}

impl EntanglementMeasure for Peps {
    fn try_entanglement_entropy(&self, subsystem: &[usize]) -> Result<f64, EntropyError> {
        let n = self
            .rows
            .checked_mul(self.cols)
            .ok_or(EntropyError::InvalidState)?;
        partition(n, subsystem)?;
        if self.physical_dim != 2
            || self.tensors.len() != self.rows
            || self.tensors.iter().any(|row| row.len() != self.cols)
        {
            return Err(EntropyError::InvalidState);
        }
        let product = self.tensors.iter().flatten().all(|tensor| {
            tensor.chi_left == 1
                && tensor.chi_right == 1
                && tensor.chi_up == 1
                && tensor.chi_down == 1
        });
        if !product {
            return Err(EntropyError::UnsupportedContraction);
        }
        if self.tensors.iter().flatten().any(|tensor| {
            tensor.physical_dim != 2
                || tensor.data.len() != 2
                || tensor
                    .data
                    .iter()
                    .any(|z| !z.re.is_finite() || !z.im.is_finite())
                || tensor.data.iter().all(|z| z.re == 0.0 && z.im == 0.0)
        }) {
            return Err(EntropyError::InvalidState);
        }
        Ok(0.0)
    }

    fn n_sites(&self) -> usize {
        self.rows * self.cols
    }
}

/// Estimate memory for a named representation; unknown representations return zero.
///
/// # Panics
/// Panics if an estimate exceeds usize instead of overflowing to a small value.
pub fn estimate_memory_bytes(n_qubits: usize, representation: &str) -> usize {
    match representation {
        "statevector" => state_size(n_qubits).ok().and_then(|n| n.checked_mul(16)),
        "mps" => n_qubits.checked_mul(32 * 32 * 2 * 16),
        "peps" => n_qubits.checked_mul(4 * 4 * 4 * 4 * 2 * 16),
        _ => Some(0),
    }
    .expect("tensor-network memory estimate exceeds usize")
}

/// Heuristic representation choice; this does not certify a contraction cost.
pub fn suggest_representation(n_qubits: usize, geometry: &str) -> &'static str {
    match geometry {
        "chain" | "1d" | "linear" => {
            if n_qubits <= 20 {
                "statevector"
            } else {
                "mps"
            }
        }
        "grid" | "2d" | "lattice" => {
            if n_qubits <= 16 {
                "statevector"
            } else {
                "peps"
            }
        }
        "all_to_all" | "complete" => "statevector",
        _ => {
            if n_qubits <= 20 {
                "statevector"
            } else {
                "mps"
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bell_pair_away_from_site_zero_is_not_a_product() {
        let mut state = TensorNetworkState::new_zero_state(3);
        state.apply_hadamard(1);
        state.apply_cnot(1, 2);
        assert!(!state.is_product_state(1e-10));
        assert!(state.entanglement_entropy(&[0]).abs() < 1e-10);
        assert!((state.entanglement_entropy(&[1]) - 2.0_f64.ln()).abs() < 1e-10);
        assert!(state.entanglement_entropy(&[1, 2]).abs() < 1e-10);
        assert!((state.entanglement_entropy(&[0, 2]) - 2.0_f64.ln()).abs() < 1e-10);
    }

    #[test]
    fn mps_cut_uses_site_count_and_detects_later_entanglement() {
        let mut state = MatrixProductState::new_zero_state(3);
        state.apply_hadamard(1);
        state.apply_cnot(1, 2);
        assert!(!state.is_product_state(1e-10));
        assert!(state.entanglement_entropy(&[0]).abs() < 1e-10);
        assert!((state.entanglement_entropy(&[0, 1]) - 2.0_f64.ln()).abs() < 1e-10);
        assert!((state.entanglement_entropy(&[1]) - 2.0_f64.ln()).abs() < 1e-10);
    }

    #[test]
    fn mps_nonunitary_gauge_and_global_scale_leave_entropy_invariant() {
        let mut state = MatrixProductState::new_zero_state(2);
        state.apply_hadamard(0);
        state.apply_cnot(0, 1);
        let baseline = mps_prefix_entropy(&state, 1).unwrap();
        assert!((baseline - 2.0_f64.ln()).abs() < 1e-10);
        for left in 0..state.tensors[0].chi_left {
            for physical in 0..2 {
                for right in 0..state.tensors[0].chi_right {
                    let scale = if right == 0 { 3.0 } else { 0.25 };
                    let old = state.tensors[0].get(left, physical, right);
                    state.tensors[0].set(
                        left,
                        physical,
                        right,
                        faer::c64::new(old.re * scale, old.im * scale),
                    );
                }
            }
        }
        for left in 0..state.tensors[1].chi_left {
            for physical in 0..2 {
                let scale = if left == 0 { 3.0 } else { 0.25 };
                let old = state.tensors[1].get(left, physical, 0);
                state.tensors[1].set(
                    left,
                    physical,
                    0,
                    faer::c64::new(old.re / scale, old.im / scale),
                );
            }
        }
        for value in &mut state.tensors[0].data {
            *value = faer::c64::new(value.re * 7.0, value.im * 7.0);
        }
        assert!((mps_prefix_entropy(&state, 1).unwrap() - baseline).abs() < 1e-10);
        assert!((state.measure_entropy(1) - baseline).abs() < 1e-10);
    }

    #[test]
    fn mps_dense_fallback_reads_site_zero_as_most_significant_bit() {
        let mut state = MatrixProductState::new_zero_state(4);
        state.apply_hadamard(2);
        state.apply_cnot(2, 3);
        let ln2 = 2.0_f64.ln();
        assert!(state.entanglement_entropy(&[1]).abs() < 1e-10);
        assert!((state.entanglement_entropy(&[2]) - ln2).abs() < 1e-10);
        assert!((state.entanglement_entropy(&[1, 2]) - ln2).abs() < 1e-10);
        assert!((state.entanglement_entropy(&[0, 3]) - ln2).abs() < 1e-10);
        assert!(state.entanglement_entropy(&[2, 3]).abs() < 1e-10);
        assert!((state.entanglement_entropy(&[3]) - ln2).abs() < 1e-10);
    }

    #[test]
    fn mps_dense_fallback_survives_cancelling_tensor_scales() {
        let scale_tensors = |state: &mut MatrixProductState| {
            for (site, tensor) in state.tensors.iter_mut().enumerate() {
                let factor = if site < 2 { 1e200 } else { 1e-200 };
                for value in &mut tensor.data {
                    *value = faer::c64::new(value.re * factor, value.im * factor);
                }
            }
        };
        let mut zero = MatrixProductState::new_zero_state(4);
        scale_tensors(&mut zero);
        assert_eq!(zero.try_entanglement_entropy(&[1]), Ok(0.0));
        assert_eq!(zero.try_entanglement_entropy(&[0, 2]), Ok(0.0));
        assert_eq!(zero.try_entanglement_entropy(&[0]), Ok(0.0));

        let mut bell = MatrixProductState::new_zero_state(4);
        bell.apply_hadamard(2);
        bell.apply_cnot(2, 3);
        scale_tensors(&mut bell);
        let ln2 = 2.0_f64.ln();
        assert!(bell.try_entanglement_entropy(&[1]).unwrap().abs() < 1e-10);
        assert!((bell.try_entanglement_entropy(&[2]).unwrap() - ln2).abs() < 1e-10);
        assert!((bell.try_entanglement_entropy(&[0, 3]).unwrap() - ln2).abs() < 1e-10);
    }

    #[test]
    fn oversized_state_trivial_cuts_are_zero_and_product_test_hits_budget() {
        let state = TensorNetworkState::new_zero_state(21);
        assert_eq!(
            state.try_is_product_state(1e-10),
            Err(EntropyError::AllocationLimit),
        );
        assert_eq!(
            state.try_entanglement_entropy(&[0]),
            Err(EntropyError::AllocationLimit),
        );
        assert_eq!(state.try_entanglement_entropy(&[]), Ok(0.0));
        let all: Vec<usize> = (0..21).collect();
        assert_eq!(state.try_entanglement_entropy(&all), Ok(0.0));
    }

    #[test]
    fn trivial_cuts_still_reject_invalid_real_states() {
        let mut state = TensorNetworkState::new_zero_state(2);
        state.apply_x(0);
        assert_eq!(state.try_entanglement_entropy(&[]), Ok(0.0));
        assert_eq!(
            real_state_cut_entropy(&[0.0, 0.0, 0.0, 0.0], 2),
            Err(EntropyError::InvalidState),
        );
        assert_eq!(
            real_state_cut_entropy(&[1.0, f64::NAN, 0.0, 0.0], 2),
            Err(EntropyError::InvalidState),
        );
        assert_eq!(
            real_state_cut_entropy(&[1.0, 0.0], 2),
            Err(EntropyError::InvalidState),
        );
    }

    #[test]
    fn zero_mps_and_malformed_bonds_are_rejected() {
        let mut state = MatrixProductState::new_zero_state(2);
        state.tensors[0].data.fill(faer::c64::new(0.0, 0.0));
        assert_eq!(
            state.try_entanglement_entropy(&[]),
            Err(EntropyError::InvalidState),
        );
        let mut state = MatrixProductState::new_zero_state(2);
        state.tensors[1].chi_left = 3;
        assert_eq!(
            state.try_entanglement_entropy(&[0]),
            Err(EntropyError::InvalidState),
        );
    }

    #[test]
    fn complex_noncontiguous_partition_and_complement_agree() {
        let mut coefficients = vec![Complex64::new(0.0, 0.0); 8];
        coefficients[0] = Complex64::new(std::f64::consts::FRAC_1_SQRT_2, 0.0);
        coefficients[5] = Complex64::new(0.0, std::f64::consts::FRAC_1_SQRT_2);
        let entropy =
            |sites: &[usize]| pure_state_subsystem_entropy(&coefficients, 3, sites, 8).unwrap();
        assert!(entropy(&[0, 2]).abs() < 1e-10);
        assert!(entropy(&[1]).abs() < 1e-10);
        assert!((entropy(&[0]) - 2.0_f64.ln()).abs() < 1e-10);
        assert!((entropy(&[0]) - entropy(&[1, 2])).abs() < 1e-10);
        assert!(entropy(&[2, 0]).abs() < 1e-10);
    }

    #[test]
    fn invalid_partitions_states_and_budgets_are_errors() {
        let state = TensorNetworkState::new_zero_state(3);
        assert_eq!(
            state.try_entanglement_entropy(&[1, 1]),
            Err(EntropyError::InvalidSubsystem),
        );
        assert_eq!(
            state.try_entanglement_entropy(&[3]),
            Err(EntropyError::InvalidSubsystem),
        );
        assert_eq!(
            state.try_is_product_state(f64::NAN),
            Err(EntropyError::InvalidTolerance),
        );
        let coefficients = vec![Complex64::new(0.0, 0.0); 8];
        assert_eq!(
            pure_state_subsystem_entropy(&coefficients, 3, &[0], 8),
            Err(EntropyError::InvalidState),
        );
        let coefficients = vec![Complex64::new(1.0, 0.0); 8];
        assert_eq!(
            pure_state_subsystem_entropy(&coefficients, 3, &[0], 4),
            Err(EntropyError::AllocationLimit),
        );
    }

    /// Multiplies the bond between `bond` and `bond + 1` by `diag(diagonal)` on
    /// the left site and its inverse on the right site: the state is unchanged.
    fn apply_bond_gauge(state: &mut MatrixProductState, bond: usize, diagonal: &[f64]) {
        let width = state.tensors[bond].chi_right;
        assert_eq!(width, diagonal.len());
        for (index, value) in state.tensors[bond].data.iter_mut().enumerate() {
            let factor = diagonal[index % width];
            *value = faer::c64::new(value.re * factor, value.im * factor);
        }
        let chi_right = state.tensors[bond + 1].chi_right;
        for (index, value) in state.tensors[bond + 1].data.iter_mut().enumerate() {
            let factor = diagonal[index / (2 * chi_right)];
            *value = faer::c64::new(value.re / factor, value.im / factor);
        }
    }

    #[test]
    fn mps_cancelling_bond_gauges_do_not_underflow_the_dense_contraction() {
        let mut state = MatrixProductState::new_zero_state(4);
        state.apply_hadamard(0);
        state.apply_cnot(0, 1);
        state.apply_hadamard(2);
        state.apply_cnot(2, 3);
        apply_bond_gauge(&mut state, 0, &[1e100, 1e-100]);
        apply_bond_gauge(&mut state, 2, &[1e100, 1e-100]);
        let ln2 = 2.0_f64.ln();
        let entropy = state.try_entanglement_entropy(&[0, 2]).unwrap();
        assert!((entropy - 2.0 * ln2).abs() < 1e-10, "entropy {entropy}");
        assert!((state.try_entanglement_entropy(&[1, 2]).unwrap() - 2.0 * ln2).abs() < 1e-10);
        assert!(state.try_entanglement_entropy(&[0, 1]).unwrap().abs() < 1e-10);
        assert!((state.try_entanglement_entropy(&[0]).unwrap() - ln2).abs() < 1e-10);
    }

    #[test]
    fn mps_cancelling_bond_gauge_does_not_zero_the_prefix_entropy() {
        let mut state = MatrixProductState::new_zero_state(2);
        state.apply_hadamard(0);
        state.apply_cnot(0, 1);
        apply_bond_gauge(&mut state, 0, &[1e100, 1e-100]);
        let ln2 = 2.0_f64.ln();
        assert!((mps_prefix_entropy(&state, 1).unwrap() - ln2).abs() < 1e-10);
        assert!((state.measure_entropy(1) - ln2).abs() < 1e-10);
        assert!(!state.is_product_state(1e-10));
    }

    #[test]
    fn mps_cut_entropies_report_every_cut_from_one_sweep() {
        let ln2 = 2.0_f64.ln();
        let mut chain = MatrixProductState::new_zero_state(4);
        chain.apply_hadamard(1);
        chain.apply_cnot(1, 2);
        let entropies = mps_cut_entropies(&chain).unwrap();
        assert_eq!(entropies.len(), 5);
        for (cut, expected) in [0.0, 0.0, ln2, 0.0, 0.0].into_iter().enumerate() {
            assert!((entropies[cut] - expected).abs() < 1e-10, "cut {cut}");
            assert!((mps_prefix_entropy(&chain, cut).unwrap() - expected).abs() < 1e-10);
        }
        let mut ghz = MatrixProductState::new_zero_state(4);
        ghz.apply_hadamard(0);
        for site in 0..3 {
            ghz.apply_cnot(site, site + 1);
        }
        let entropies = mps_cut_entropies(&ghz).unwrap();
        for (cut, &entropy) in entropies.iter().enumerate().take(4).skip(1) {
            assert!((entropy - ln2).abs() < 1e-10, "cut {cut}");
        }
        assert_eq!(
            mps_prefix_entropy(&ghz, 5),
            Err(EntropyError::InvalidSubsystem),
        );
    }

    #[test]
    fn mps_cut_entropies_match_dense_schmidt_decomposition_after_gauging() {
        let mut seed = 0x2545_f491_4f6c_dd1d_u64;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed >> 11) as f64 / (1_u64 << 53) as f64 - 0.5
        };
        let n_sites = 5;
        let mut coefficients: Vec<Complex64> = (0..1_usize << n_sites)
            .map(|_| Complex64::new(next(), next()))
            .collect();
        let norm = coefficients
            .iter()
            .map(|z| z.norm_sqr())
            .sum::<f64>()
            .sqrt();
        for z in &mut coefficients {
            *z /= norm;
        }
        let amplitudes: Vec<faer::c64> = coefficients
            .iter()
            .map(|z| faer::c64::new(z.re, z.im))
            .collect();
        let mut state = MatrixProductState::from_state_vector(&amplitudes, n_sites);
        assert!(state.max_bond_dimension() >= 4);
        let rebuilt = state.to_state_vector();
        for (a, b) in amplitudes.iter().zip(&rebuilt) {
            assert!((a.re - b.re).abs() + (a.im - b.im).abs() < 1e-10);
        }
        let gauges = [1e30, 1e-30, 1e15, 1e-15];
        for bond in 0..n_sites - 1 {
            let width = state.tensors[bond].chi_right;
            apply_bond_gauge(&mut state, bond, &gauges[..width]);
        }
        let entropies = mps_cut_entropies(&state).unwrap();
        for (cut, &entropy) in entropies.iter().enumerate().take(n_sites).skip(1) {
            let sites: Vec<usize> = (0..cut).collect();
            let dense =
                pure_state_subsystem_entropy(&coefficients, n_sites, &sites, 1 << 20).unwrap();
            assert!(
                dense > 0.1,
                "cut {cut} is not entangled enough to discriminate"
            );
            assert!((entropy - dense).abs() < 1e-9, "cut {cut}");
        }
        for sites in [&[0_usize, 2][..], &[1, 3, 4], &[2], &[0, 4]] {
            let dense =
                pure_state_subsystem_entropy(&coefficients, n_sites, sites, 1 << 20).unwrap();
            let facade = state.try_entanglement_entropy(sites).unwrap();
            assert!((facade - dense).abs() < 1e-9, "subsystem {sites:?}");
        }
    }

    #[test]
    fn mps_product_test_uses_every_cut_and_checks_tolerance() {
        let mut state = MatrixProductState::new_zero_state(5);
        assert_eq!(state.try_is_product_state(0.0), Ok(true));
        assert_eq!(
            state.try_is_product_state(-1.0),
            Err(EntropyError::InvalidTolerance),
        );
        state.apply_hadamard(3);
        state.apply_cnot(3, 4);
        assert_eq!(state.try_is_product_state(1e-10), Ok(false));
        assert_eq!(state.try_is_product_state(1.0), Ok(true));
        state.tensors[2].data.fill(faer::c64::new(0.0, 0.0));
        assert_eq!(
            state.try_is_product_state(1.0),
            Err(EntropyError::InvalidState),
        );
    }

    #[test]
    fn product_peps_is_supported_but_general_contraction_is_not_invented() {
        let mut peps = Peps::new_zero_state(2, 2);
        assert!(peps.is_product_state(1e-10));
        assert_eq!(peps.try_entanglement_entropy(&[0, 3]), Ok(0.0));
        peps.tensors[0][0].chi_right = 2;
        assert_eq!(
            peps.try_entanglement_entropy(&[0]),
            Err(EntropyError::UnsupportedContraction),
        );
    }

    #[test]
    fn product_and_empty_cuts() {
        let state = TensorNetworkState::new_zero_state(4);
        assert!(state.is_product_state(1e-10));
        assert_eq!(state.entanglement_entropy(&[]), 0.0);
        assert_eq!(state.entanglement_entropy(&[0, 1, 2, 3]), 0.0);
        assert!(MatrixProductState::new_zero_state(4).is_product_state(1e-10));
    }

    #[test]
    #[should_panic(expected = "memory estimate exceeds usize")]
    fn statevector_memory_estimate_overflow_panics() {
        let _ = estimate_memory_bytes(60, "statevector");
    }

    #[test]
    #[should_panic(expected = "memory estimate exceeds usize")]
    fn statevector_memory_estimate_shift_overflow_panics() {
        let _ = estimate_memory_bytes(usize::BITS as usize, "statevector");
    }

    #[test]
    fn memory_and_representation_compatibility() {
        assert_eq!(estimate_memory_bytes(10, "statevector"), 16384);
        assert!(estimate_memory_bytes(20, "mps") < estimate_memory_bytes(20, "statevector"));
        assert_eq!(suggest_representation(8, "chain"), "statevector");
        assert_eq!(suggest_representation(30, "chain"), "mps");
        assert_eq!(suggest_representation(25, "grid"), "peps");
    }
}
