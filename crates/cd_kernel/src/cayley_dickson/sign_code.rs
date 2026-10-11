//! Binary sign kernels and phase-exact controlled diagonal synthesis.
//!
//! The Schreier convention is `L_(a XOR b)^-1 L_a L_b`, acting on basis
//! vectors from right to left. Its diagonal exponent is
//! `F(b,x) + F(a,b XOR x) + F(a XOR b,x)` over GF(2), where
//! `(-1)^F(a,b) = cd_basis_mul_sign(dim,a,b)`. The normalized exponent adds
//! its value at zero and equals the ordinary coboundary `dF(a,b,x)`.
//! `F` is a 2-cochain; the nonzero coboundary prevents calling `F` a cocycle.
//!
//! The audit reconstructs both spans from these generators and checks the
//! explicit ANF basis for orders 2 through 8. `SchreierSignCode.v` separately
//! proves the all-order characterization for the recursive sign convention;
//! `SignCodeCardinality.v` counts the codewords through a unique enumeration.
//! The binary direct sum concerns sign codes and does not assert a direct
//! product of multiplication groups.

use super::SignTable;

/// Invalid finite sign-code or diagonal-phase input.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum SignCodeError {
    #[error("a Boolean truth table must have a positive power-of-two length")]
    InvalidTruthTableLength,
    #[error("the finite Schreier audit accepts orders 2 through 8")]
    UnsupportedAuditOrder,
    #[error("basis index {index} exceeds truth-table length {dimension}")]
    InvalidBasisIndex { index: usize, dimension: usize },
}

/// The projection `P(v)(x) = v(x) XOR v(0)` and its separate scalar sign.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalizedSignWord {
    normalized: Vec<bool>,
    scalar_sign: bool,
}

impl NormalizedSignWord {
    pub fn from_truth_table(exponents: &[bool]) -> Result<Self, SignCodeError> {
        if !exponents.len().is_power_of_two() {
            return Err(SignCodeError::InvalidTruthTableLength);
        }
        let scalar_sign = exponents[0];
        Ok(Self {
            normalized: exponents.iter().map(|&value| value ^ scalar_sign).collect(),
            scalar_sign,
        })
    }

    pub fn normalized(&self) -> &[bool] {
        &self.normalized
    }

    pub fn scalar_sign(&self) -> bool {
        self.scalar_sign
    }

    pub fn reconstruct(&self) -> Vec<bool> {
        self.normalized
            .iter()
            .map(|&value| value ^ self.scalar_sign)
            .collect()
    }

    /// Synthesize ANF phase gates, retaining the scalar bit as a Z gate on
    /// the control. Every monomial gate also includes that control.
    pub fn controlled_synthesis(&self) -> ControlledSignSynthesis {
        let mut coefficients = self.normalized.clone();
        let mut variable = 1;
        while variable < coefficients.len() {
            for mask in 0..coefficients.len() {
                if mask & variable != 0 {
                    coefficients[mask] ^= coefficients[mask ^ variable];
                }
            }
            variable <<= 1;
        }
        ControlledSignSynthesis {
            dimension: coefficients.len(),
            control_z: self.scalar_sign,
            monomial_masks: coefficients
                .iter()
                .enumerate()
                .filter_map(|(mask, &present)| present.then_some(mask))
                .collect(),
        }
    }
}

/// Exact gate semantics for `|c,x> -> (-1)^(c v(x)) |c,x>`.
///
/// A mask selects target bits of a multi-controlled phase gate. The separate
/// `control_z` implements the scalar sign when the control is one; omitting
/// that gate changes the relative phase between the two control branches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ControlledSignSynthesis {
    dimension: usize,
    control_z: bool,
    monomial_masks: Vec<usize>,
}

impl ControlledSignSynthesis {
    pub fn control_z(&self) -> bool {
        self.control_z
    }

    pub fn monomial_masks(&self) -> &[usize] {
        &self.monomial_masks
    }

    pub fn phase_on_basis(&self, control: bool, index: usize) -> Result<i8, SignCodeError> {
        if index >= self.dimension {
            return Err(SignCodeError::InvalidBasisIndex {
                index,
                dimension: self.dimension,
            });
        }
        let exponent = control
            && self
                .monomial_masks
                .iter()
                .fold(self.control_z, |parity, &mask| {
                    parity ^ (index & mask == mask)
                });
        Ok(if exponent { -1 } else { 1 })
    }
}

/// Observational equivalence of uncontrolled phase oracles: two real
/// diagonal phase tables agree up to a common scalar sign. Controlled
/// access is an additional resource and instead distinguishes complements.
pub fn uncontrolled_phase_equivalent(left: &[bool], right: &[bool]) -> Result<bool, SignCodeError> {
    let left_word = NormalizedSignWord::from_truth_table(left)?;
    let right_word = NormalizedSignWord::from_truth_table(right)?;
    Ok(left_word.normalized == right_word.normalized)
}

/// Finite evidence from all `2^(2n)` Schreier generators at one order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignCodeAudit {
    pub order: u32,
    pub generator_count: usize,
    pub kernel_rank: usize,
    pub normalized_rank: usize,
    pub anf_basis_rank: usize,
    pub kernel_in_characterization: bool,
    pub characterization_in_kernel: bool,
    pub normalized_in_characterization: bool,
    pub characterization_in_normalized: bool,
    pub scalar_in_kernel: bool,
    pub projection_equals_associator: bool,
}

type PackedWord = Vec<u64>;

fn schreier_exponent(signs: &SignTable, left: usize, right: usize, index: usize) -> bool {
    (signs.sign(right, index) < 0)
        ^ (signs.sign(left, right ^ index) < 0)
        ^ (signs.sign(left ^ right, index) < 0)
}

fn packed_word(dimension: usize, mut value: impl FnMut(usize) -> bool) -> PackedWord {
    let mut words = vec![0_u64; dimension.div_ceil(64)];
    for index in 0..dimension {
        if value(index) {
            words[index / 64] |= 1 << (index % 64);
        }
    }
    words
}

#[derive(Clone)]
struct BinarySpan {
    pivots: Vec<Option<PackedWord>>,
    rank: usize,
}

impl BinarySpan {
    fn new(dimension: usize) -> Self {
        Self {
            pivots: vec![None; dimension],
            rank: 0,
        }
    }

    fn reduce(&self, row: &mut [u64]) -> Option<usize> {
        for pivot in (0..self.pivots.len()).rev() {
            if row[pivot / 64] & (1 << (pivot % 64)) == 0 {
                continue;
            }
            match &self.pivots[pivot] {
                Some(basis) => row
                    .iter_mut()
                    .zip(basis)
                    .for_each(|(value, &basis_value)| *value ^= basis_value),
                None => return Some(pivot),
            }
        }
        None
    }

    fn insert(&mut self, mut row: PackedWord) {
        if let Some(pivot) = self.reduce(&mut row) {
            self.pivots[pivot] = Some(row);
            self.rank += 1;
        }
    }

    fn contains(&self, row: &[u64]) -> bool {
        self.reduce(&mut row.to_vec()).is_none()
    }

    fn contains_span(&self, other: &Self) -> bool {
        other.pivots.iter().flatten().all(|row| self.contains(row))
    }
}

/// Reconstruct the actual Schreier span independently of the characterized
/// formula, then verify both containments and the explicit ANF basis.
///
/// For `n >= 3`, the candidate normalized basis consists of each nonempty
/// proper subset of the lower `n-1` variables and the highest variable.
/// Its dimension is `2^(n-1)-1`. Order two uses the quaternion exception
/// `C_2 = 0` and `H_2 = <1>` separately.
pub fn audit_sign_code(order: u32) -> Result<SignCodeAudit, SignCodeError> {
    if !(2..=8).contains(&order) {
        return Err(SignCodeError::UnsupportedAuditOrder);
    }
    let dimension = 1_usize << order;
    let signs = SignTable::new(dimension);
    let exponent = |left, right| signs.sign(left, right) < 0;
    let mut kernel = BinarySpan::new(dimension);
    let mut normalized = BinarySpan::new(dimension);
    let mut projection_equals_associator = true;
    for left in 0..dimension {
        for right in 0..dimension {
            let raw = |index| schreier_exponent(&signs, left, right, index);
            let scalar = raw(0);
            kernel.insert(packed_word(dimension, raw));
            normalized.insert(packed_word(dimension, |index| raw(index) ^ scalar));
            projection_equals_associator &= (0..dimension).all(|index| {
                raw(index) ^ scalar
                    == exponent(left, right)
                        ^ exponent(left ^ right, index)
                        ^ exponent(right, index)
                        ^ exponent(left, right ^ index)
            });
        }
    }
    let mut candidate = BinarySpan::new(dimension);
    if order >= 3 {
        let lower_mask = dimension / 2 - 1;
        for mask in (1..lower_mask).chain(std::iter::once(dimension / 2)) {
            candidate.insert(packed_word(dimension, |index| index & mask == mask));
        }
    }
    let mut candidate_kernel = candidate.clone();
    let scalar_word = packed_word(dimension, |_| true);
    candidate_kernel.insert(scalar_word.clone());
    Ok(SignCodeAudit {
        order,
        generator_count: dimension * dimension,
        kernel_rank: kernel.rank,
        normalized_rank: normalized.rank,
        anf_basis_rank: candidate.rank,
        kernel_in_characterization: candidate_kernel.contains_span(&kernel),
        characterization_in_kernel: kernel.contains_span(&candidate_kernel),
        normalized_in_characterization: candidate.contains_span(&normalized),
        characterization_in_normalized: normalized.contains_span(&candidate),
        scalar_in_kernel: kernel.contains(&scalar_word),
        projection_equals_associator,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cayley_dickson::cd_multiply;

    #[test]
    fn raw_schreier_signs_match_ordered_recursive_left_operators() {
        for dimension in [4, 8, 16, 32] {
            let signs = SignTable::new(dimension);
            let basis: Vec<Vec<f64>> = (0..dimension)
                .map(|index| {
                    let mut vector = vec![0.0; dimension];
                    vector[index] = 1.0;
                    vector
                })
                .collect();
            assert_ne!(
                cd_multiply(&basis[1], &basis[2]),
                cd_multiply(&basis[2], &basis[1])
            );
            for (left, right) in [
                (0, 1),
                (1, 1),
                (1, 2),
                (2, 1),
                (1, dimension / 2),
                (dimension / 2, 1),
                (dimension / 2, dimension / 2 + 1),
            ] {
                let coset_columns: Vec<_> = basis
                    .iter()
                    .map(|vector| cd_multiply(&basis[left ^ right], vector))
                    .collect();
                // Recursive basis multiplication gives an orthogonal signed
                // permutation. Its transpose applies the inverse operator.
                for (column, image) in coset_columns.iter().enumerate() {
                    for (other_column, other_image) in coset_columns.iter().enumerate() {
                        let inner_product: f64 = image
                            .iter()
                            .zip(other_image)
                            .map(|(first, second)| first * second)
                            .sum();
                        assert_eq!(
                            inner_product,
                            if column == other_column { 1.0 } else { 0.0 }
                        );
                    }
                }
                for (index, vector) in basis.iter().enumerate() {
                    let right_image = cd_multiply(&basis[right], vector);
                    let composed_image = cd_multiply(&basis[left], &right_image);
                    let actual: Vec<f64> = coset_columns
                        .iter()
                        .map(|column| {
                            column
                                .iter()
                                .zip(&composed_image)
                                .map(|(first, second)| first * second)
                                .sum()
                        })
                        .collect();
                    let mut expected = vec![0.0; dimension];
                    expected[index] = if schreier_exponent(&signs, left, right, index) {
                        -1.0
                    } else {
                        1.0
                    };
                    assert_eq!(
                        actual, expected,
                        "dimension={dimension}, left={left}, right={right}, input={index}"
                    );
                }
            }
        }
    }

    #[test]
    fn schreier_span_both_containments_rank_and_basis_through_order_eight() {
        for order in 2..=8 {
            let audit = audit_sign_code(order).unwrap();
            let expected_rank = if order == 2 {
                0
            } else {
                (1 << (order - 1)) - 1
            };
            assert_eq!(audit.normalized_rank, expected_rank, "{audit:?}");
            assert_eq!(audit.anf_basis_rank, expected_rank, "{audit:?}");
            assert_eq!(audit.kernel_rank, expected_rank + 1, "{audit:?}");
            assert!(audit.kernel_in_characterization, "{audit:?}");
            assert!(audit.characterization_in_kernel, "{audit:?}");
            assert!(audit.normalized_in_characterization, "{audit:?}");
            assert!(audit.characterization_in_normalized, "{audit:?}");
            assert!(audit.scalar_in_kernel, "{audit:?}");
            assert!(audit.projection_equals_associator, "{audit:?}");
        }
    }

    #[test]
    fn projection_and_controlled_synthesis_exhaust_all_three_variable_functions() {
        for truth_mask in 0_u32..256 {
            let exponents: Vec<bool> = (0..8).map(|index| truth_mask & (1 << index) != 0).collect();
            let word = NormalizedSignWord::from_truth_table(&exponents).unwrap();
            assert!(!word.normalized()[0]);
            assert_eq!(word.reconstruct(), exponents);
            assert_eq!(
                NormalizedSignWord::from_truth_table(word.normalized())
                    .unwrap()
                    .normalized(),
                word.normalized()
            );
            let synthesis = word.controlled_synthesis();
            assert_eq!(synthesis.control_z(), exponents[0]);
            assert!(!synthesis.monomial_masks().contains(&0));
            for (index, &exponent) in exponents.iter().enumerate() {
                assert_eq!(synthesis.phase_on_basis(false, index), Ok(1));
                assert_eq!(
                    synthesis.phase_on_basis(true, index),
                    Ok(if exponent { -1 } else { 1 })
                );
            }
        }
    }

    #[test]
    fn controlled_access_distinguishes_scalar_signs() {
        let zero = [false; 8];
        let one = [true; 8];
        assert_eq!(uncontrolled_phase_equivalent(&zero, &one), Ok(true));
        let positive = NormalizedSignWord::from_truth_table(&zero)
            .unwrap()
            .controlled_synthesis();
        let negative = NormalizedSignWord::from_truth_table(&one)
            .unwrap()
            .controlled_synthesis();
        assert!(negative.control_z());
        assert!(negative.monomial_masks().is_empty());
        assert_eq!(
            positive.phase_on_basis(false, 0),
            negative.phase_on_basis(false, 0)
        );
        assert_ne!(
            positive.phase_on_basis(true, 0),
            negative.phase_on_basis(true, 0)
        );
        let mut other = zero;
        other[1] = true;
        assert_eq!(uncontrolled_phase_equivalent(&zero, &other), Ok(false));
    }

    #[test]
    fn invalid_domains_are_explicit() {
        for truth_table in [vec![], vec![false; 3]] {
            assert_eq!(
                NormalizedSignWord::from_truth_table(&truth_table),
                Err(SignCodeError::InvalidTruthTableLength)
            );
        }
        assert_eq!(
            audit_sign_code(1),
            Err(SignCodeError::UnsupportedAuditOrder)
        );
        assert_eq!(
            audit_sign_code(9),
            Err(SignCodeError::UnsupportedAuditOrder)
        );
        let synthesis = NormalizedSignWord::from_truth_table(&[true])
            .unwrap()
            .controlled_synthesis();
        assert_eq!(synthesis.phase_on_basis(true, 0), Ok(-1));
        assert!(matches!(
            synthesis.phase_on_basis(true, 1),
            Err(SignCodeError::InvalidBasisIndex { .. })
        ));
    }
}
