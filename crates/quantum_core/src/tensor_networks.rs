// SPDX-License-Identifier: MIT
//! Tensor-network entropy facade with declared subsystem semantics.
//!
//! Site zero is the most significant state-vector bit. Entropies are in
//! nats. These types represent pure states; reduced entropy is not an
//! entanglement measure for an arbitrary mixed global state. PEPS row-cut
//! approximations are not substituted for an exact subsystem contraction.

use nalgebra::{DMatrix, SymmetricEigen};
use num_complex::Complex64;

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
        if !selected.is_empty()
            && selected.len() != self.n_qubits()
            && state_size(self.n_qubits())? > DEFAULT_ENTROPY_AMPLITUDE_LIMIT
        {
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

fn normalized_gram(mut gram: DMatrix<Complex64>) -> Result<DMatrix<Complex64>, EntropyError> {
    if gram.iter().any(|z| !z.re.is_finite() || !z.im.is_finite()) {
        return Err(EntropyError::NumericalFailure);
    }
    let scale = gram
        .iter()
        .map(|z| z.re.abs().max(z.im.abs()))
        .fold(0.0_f64, f64::max);
    if scale == 0.0 {
        return Err(EntropyError::InvalidState);
    }
    gram /= Complex64::new(scale, 0.0);
    Ok((&gram + gram.adjoint()) * Complex64::new(0.5, 0.0))
}

fn mps_physical_matrix(tensor: &MpsTensor, physical: usize) -> DMatrix<Complex64> {
    // A positive local scalar changes only the discarded global normalization.
    let scale = tensor
        .data
        .iter()
        .map(|z| z.re.abs().max(z.im.abs()))
        .fold(0.0_f64, f64::max);
    DMatrix::from_fn(tensor.chi_left, tensor.chi_right, |left, right| {
        let value = tensor.get(left, physical, right);
        Complex64::new(value.re / scale, value.im / scale)
    })
}

/// Gauge-invariant prefix entropy from both MPS contraction environments.
///
/// For a coefficient matrix L R, the nonzero Schmidt probabilities are the
/// eigenvalues of sqrt(L* L) (R R*) sqrt(L* L), normalized by their sum.
/// A left Gram matrix alone is not the reduced state in an arbitrary gauge.
/// Each environment is rescaled by a positive scalar to avoid norm underflow.
///
/// # Errors
/// Rejects invalid tensor chains, excessive bond-matrix allocation, invalid
/// cuts, zero states and failed or nonpositive decompositions.
pub fn mps_prefix_entropy(state: &MatrixProductState, cut: usize) -> Result<f64, EntropyError> {
    validate_mps(state)?;
    if cut > state.n_qubits {
        return Err(EntropyError::InvalidSubsystem);
    }
    let mut left = DMatrix::from_element(1, 1, Complex64::new(1.0, 0.0));
    for tensor in &state.tensors[..cut] {
        let mut next = DMatrix::zeros(tensor.chi_right, tensor.chi_right);
        for physical in 0..2 {
            let a = mps_physical_matrix(tensor, physical);
            next += a.adjoint() * &left * &a;
        }
        left = normalized_gram(next)?;
    }
    let mut right = DMatrix::from_element(1, 1, Complex64::new(1.0, 0.0));
    for tensor in state.tensors[cut..].iter().rev() {
        let mut next = DMatrix::zeros(tensor.chi_left, tensor.chi_left);
        for physical in 0..2 {
            let a = mps_physical_matrix(tensor, physical);
            next += &a * &right * a.adjoint();
        }
        right = normalized_gram(next)?;
    }
    let decomposition = SymmetricEigen::try_new(left, 32.0 * f64::EPSILON, 100_000)
        .ok_or(EntropyError::NumericalFailure)?;
    if decomposition
        .eigenvalues
        .iter()
        .any(|&value| !value.is_finite() || value < -1e-10)
    {
        return Err(EntropyError::NumericalFailure);
    }
    let root = &decomposition.eigenvectors
        * DMatrix::from_diagonal(
            &decomposition
                .eigenvalues
                .map(|v| Complex64::new(v.max(0.0).sqrt(), 0.0)),
        )
        * decomposition.eigenvectors.adjoint();
    let effective = normalized_gram(&root * right * root.adjoint())?;
    let spectrum = SymmetricEigen::try_new(effective, 32.0 * f64::EPSILON, 100_000)
        .ok_or(EntropyError::NumericalFailure)?
        .eigenvalues;
    if spectrum
        .iter()
        .any(|&value| !value.is_finite() || value < -1e-10)
    {
        return Err(EntropyError::NumericalFailure);
    }
    let normalization: f64 = spectrum.iter().map(|v| v.max(0.0)).sum();
    if normalization <= 0.0 || !normalization.is_finite() {
        return Err(EntropyError::InvalidState);
    }
    Ok(spectrum
        .iter()
        .map(|v| v.max(0.0) / normalization)
        .filter(|&p| p > 0.0)
        .map(|p| -p * p.ln())
        .sum())
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
        let coefficients: Vec<_> = self
            .to_state_vector_parallel()
            .iter()
            .map(|z| Complex64::new(z.re, z.im))
            .collect();
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
            if n_qubits <= 20 { "statevector" } else { "mps" }
        }
        "grid" | "2d" | "lattice" => {
            if n_qubits <= 16 { "statevector" } else { "peps" }
        }
        "all_to_all" | "complete" => "statevector",
        _ => {
            if n_qubits <= 20 { "statevector" } else { "mps" }
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
                        left, physical, right,
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
                    left, physical, 0,
                    faer::c64::new(old.re / scale, old.im / scale),
                );
            }
        }
        for value in &mut state.tensors[0].data {
            *value = faer::c64::new(value.re * 7.0, value.im * 7.0);
        }
        assert!((mps_prefix_entropy(&state, 1).unwrap() - baseline).abs() < 1e-10);
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
        let entropy = |sites: &[usize]| {
            pure_state_subsystem_entropy(&coefficients, 3, sites, 8).unwrap()
        };
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
    fn memory_and_representation_compatibility() {
        assert_eq!(estimate_memory_bytes(10, "statevector"), 16384);
        assert!(estimate_memory_bytes(20, "mps") < estimate_memory_bytes(20, "statevector"));
        assert_eq!(suggest_representation(8, "chain"), "statevector");
        assert_eq!(suggest_representation(30, "chain"), "mps");
        assert_eq!(suggest_representation(25, "grid"), "peps");
    }
}
