//! Finite Boolean metrics and observable phase-oracle recovery experiments.
//!
//! The highest doubling-generator row is the permanent negative control
//! `f(u,t) = [u != 0] XOR t`. Its increasing algebraic degree coexists with
//! nonlinearity two and algebraic immunity two. The audit independently
//! measures these quantities for orders 3 through 11.
//!
//! Oracle recovery assumes a supplied finite candidate list and exact,
//! noiseless queries. Uncontrolled phase access identifies truth tables up
//! to complementation. Controlled phase access adds a coherent reference
//! branch and distinguishes the scalar sign. Query transcripts are constructive
//! upper bounds for this protocol; they supply no query-complexity lower bound.

use super::{cd_basis_mul_sign, sign_code::NormalizedSignWord};
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BooleanPhaseError {
    #[error("the finite Boolean audit requires a power-of-two table of at most 2048 entries")]
    InvalidTruthTable,
    #[error("the highest-generator replay accepts orders 3 through 11")]
    UnsupportedOrder,
    #[error("the candidate list must be nonempty with a common truth-table dimension")]
    InvalidCandidates,
    #[error("query index {index} is outside a truth table of length {dimension}")]
    InvalidQuery { index: usize, dimension: usize },
}

/// Invalid degree promise or incomplete low-weight value-query transcript.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum DegreePromisedAnfError {
    #[error(
        "degree-promised interpolation accepts at most eight variables and degree at most the variable count"
    )]
    InvalidDegreePromise,
    #[error("interpolation requires each low-weight input exactly once and no other samples")]
    InvalidLowWeightSamples,
}

/// Query inputs for a Boolean polynomial with externally promised degree <= d.
///
/// The domain is bounded at eight variables. There are sum_{k=0}^d binom(n,k)
/// inputs; the subset-monomial evaluation matrix on them is unit triangular.
pub fn low_weight_query_inputs(
    variable_count: u32,
    maximum_degree: u32,
) -> Result<Vec<usize>, DegreePromisedAnfError> {
    if variable_count > 8 || maximum_degree > variable_count {
        return Err(DegreePromisedAnfError::InvalidDegreePromise);
    }
    Ok((0..1_usize << variable_count)
        .filter(|input| input.count_ones() <= maximum_degree)
        .collect())
}

/// Recover ANF monomial masks from the complete low-weight value-query set.
///
/// Uniqueness assumes the external degree promise. The returned polynomial
/// matches the supplied samples; unqueried higher-degree terms can alias them,
/// so this API does not certify the degree of an unseen oracle. Ordinary value
/// queries and uniform-input Walsh probabilities are different access models.
pub fn recover_degree_promised_anf(
    variable_count: u32,
    maximum_degree: u32,
    samples: &[(usize, bool)],
) -> Result<Vec<usize>, DegreePromisedAnfError> {
    let query_inputs = low_weight_query_inputs(variable_count, maximum_degree)?;
    let mut coefficients = std::collections::BTreeMap::new();
    for &(input, output) in samples {
        if coefficients.insert(input, output).is_some() {
            return Err(DegreePromisedAnfError::InvalidLowWeightSamples);
        }
    }
    if coefficients.keys().copied().collect::<Vec<_>>() != query_inputs {
        return Err(DegreePromisedAnfError::InvalidLowWeightSamples);
    }
    for variable in 0..variable_count {
        let bit = 1_usize << variable;
        for &input in &query_inputs {
            if input & bit != 0 {
                let subset_coefficient = coefficients[&(input ^ bit)];
                *coefficients.get_mut(&input).expect("validated query input") ^= subset_coefficient;
            }
        }
    }
    Ok(coefficients
        .into_iter()
        .filter_map(|(mask, coefficient)| coefficient.then_some(mask))
        .collect())
}

/// Exact integer Walsh spectrum and Mobius-derived algebraic degree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BooleanSpectrum {
    pub algebraic_degree: u32,
    pub nonlinearity: usize,
    pub walsh_coefficients: Vec<i64>,
}

/// Compute `W_f(y)=sum_x (-1)^(f(x)+x.y)` without floating-point arithmetic.
pub fn boolean_spectrum(truth: &[bool]) -> Result<BooleanSpectrum, BooleanPhaseError> {
    validate_truth_table(truth)?;
    let mut coefficients = truth.to_vec();
    let mut stride = 1;
    while stride < truth.len() {
        for mask in 0..truth.len() {
            if mask & stride != 0 {
                coefficients[mask] ^= coefficients[mask ^ stride];
            }
        }
        stride *= 2;
    }
    let algebraic_degree = coefficients
        .iter()
        .enumerate()
        .filter_map(|(mask, &present)| present.then_some(mask.count_ones()))
        .max()
        .unwrap_or(0);
    let mut walsh_coefficients: Vec<i64> = truth
        .iter()
        .map(|&value| if value { -1 } else { 1 })
        .collect();
    stride = 1;
    while stride < truth.len() {
        for block in (0..truth.len()).step_by(2 * stride) {
            for offset in 0..stride {
                let first = walsh_coefficients[block + offset];
                let second = walsh_coefficients[block + offset + stride];
                walsh_coefficients[block + offset] = first + second;
                walsh_coefficients[block + offset + stride] = first - second;
            }
        }
        stride *= 2;
    }
    let maximum = walsh_coefficients
        .iter()
        .map(|value| value.unsigned_abs())
        .max()
        .unwrap();
    Ok(BooleanSpectrum {
        algebraic_degree,
        nonlinearity: (truth.len() - maximum as usize) / 2,
        walsh_coefficients,
    })
}

/// Exact certificate that the family's algebraic immunity is two.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlgebraicImmunityCertificate {
    /// Ranks of constant/linear evaluation matrices on f=0 and f=1.
    pub affine_support_ranks: [usize; 2],
    pub affine_coefficient_count: usize,
    /// Monomial masks of a nonzero degree-two annihilator of f.
    pub annihilator_monomials: Vec<usize>,
    pub algebraic_immunity: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratorBooleanAudit {
    pub order: u32,
    pub truth_table: Vec<bool>,
    pub matches_highest_generator_sign_row: bool,
    pub spectrum: BooleanSpectrum,
    pub immunity: AlgebraicImmunityCertificate,
}

/// Audit `f(u,t)=[u!=0] XOR t` against the actual Cayley-Dickson sign row.
///
/// Full affine support ranks exclude every nonzero annihilator of degree
/// zero or one for both f and f+1. The independently evaluated monomial
/// `x_0*t` annihilates f and has degree two, fixing the exact minimum.
pub fn audit_highest_generator_boolean_family(
    order: u32,
) -> Result<GeneratorBooleanAudit, BooleanPhaseError> {
    if !(3..=11).contains(&order) {
        return Err(BooleanPhaseError::UnsupportedOrder);
    }
    let dimension = 1_usize << order;
    let highest = dimension / 2;
    let truth_table: Vec<bool> = (0..dimension)
        .map(|index| (index & (highest - 1) != 0) ^ (index & highest != 0))
        .collect();
    let matches_highest_generator_sign_row = truth_table
        .iter()
        .enumerate()
        .all(|(index, &value)| value == (cd_basis_mul_sign(dimension, highest, index) < 0));
    let affine_coefficient_count = order as usize + 1;
    let affine_support_ranks = [false, true].map(|support_value| {
        binary_rank(
            truth_table
                .iter()
                .enumerate()
                .filter_map(|(index, &value)| {
                    (value == support_value).then_some(1_u64 | ((index as u64) << 1))
                }),
            affine_coefficient_count,
        )
    });
    let annihilator_monomials = vec![highest | 1];
    let witness_annihilates = truth_table
        .iter()
        .enumerate()
        .all(|(index, &value)| !(value && evaluate_monomials(&annihilator_monomials, index)));
    // These assertions validate the family-specific certificate rather than
    // substituting its expected immunity for a measurement.
    assert_eq!(affine_support_ranks, [affine_coefficient_count; 2]);
    assert!(witness_annihilates);
    assert!((0..dimension).any(|index| evaluate_monomials(&annihilator_monomials, index)));
    Ok(GeneratorBooleanAudit {
        order,
        spectrum: boolean_spectrum(&truth_table)?,
        truth_table,
        matches_highest_generator_sign_row,
        immunity: AlgebraicImmunityCertificate {
            affine_support_ranks,
            affine_coefficient_count,
            annihilator_monomials,
            algebraic_immunity: 2,
        },
    })
}

/// Resources and associated deterministic one-call observation experiments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OracleAccess {
    /// `|x,b> -> |x,b XOR f(x)>`; prepare b=0 and measure the output bit.
    Value,
    /// `|x> -> (-1)^f(x)|x>`; prepare `(|0>+|x>)/sqrt(2)` and measure
    /// in its plus/minus basis to observe `f(x) XOR f(0)`. The x=0
    /// observation is known to be zero and needs no oracle call.
    UncontrolledPhase,
    /// `|c,x> -> (-1)^(c*f(x))|c,x>`; prepare the control in |+>,
    /// apply the oracle, and measure the control in its plus/minus basis.
    ControlledPhase,
}

impl OracleAccess {
    /// Canonical representative of the complete observable equivalence class.
    pub fn representative(self, truth: &[bool]) -> Result<Vec<bool>, BooleanPhaseError> {
        validate_truth_table(truth)?;
        match self {
            Self::UncontrolledPhase => Ok(NormalizedSignWord::from_truth_table(truth)
                .expect("validated truth-table dimension")
                .normalized()
                .to_vec()),
            Self::Value | Self::ControlledPhase => Ok(truth.to_vec()),
        }
    }

    /// Exact output bit of the experiment specified by this access model.
    pub fn observe(self, truth: &[bool], index: usize) -> Result<bool, BooleanPhaseError> {
        validate_truth_table(truth)?;
        if index >= truth.len() {
            return Err(BooleanPhaseError::InvalidQuery {
                index,
                dimension: truth.len(),
            });
        }
        Ok(match self {
            Self::UncontrolledPhase => truth[index] ^ truth[0],
            Self::Value | Self::ControlledPhase => truth[index],
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OracleQuery {
    pub input: usize,
    pub observed_bit: bool,
    pub remaining_classes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OracleRecovery {
    pub access: OracleAccess,
    pub initial_class_count: usize,
    pub representative: Vec<bool>,
    /// Each recorded experiment consumes one oracle call.
    pub queries: Vec<OracleQuery>,
}

/// The recovery algorithm receives only this observable query interface.
pub trait ObservableBooleanOracle {
    fn dimension(&self) -> usize;
    fn access(&self) -> OracleAccess;
    fn observe(&mut self, index: usize) -> Result<bool, BooleanPhaseError>;
}

/// Exact classical simulation of the resource-specific observation experiment.
pub struct TruthTableOracle<'a> {
    truth: &'a [bool],
    access: OracleAccess,
    oracle_calls: usize,
}

impl<'a> TruthTableOracle<'a> {
    pub fn new(truth: &'a [bool], access: OracleAccess) -> Result<Self, BooleanPhaseError> {
        validate_truth_table(truth)?;
        Ok(Self {
            truth,
            access,
            oracle_calls: 0,
        })
    }

    pub fn oracle_calls(&self) -> usize {
        self.oracle_calls
    }
}

impl ObservableBooleanOracle for TruthTableOracle<'_> {
    fn dimension(&self) -> usize {
        self.truth.len()
    }

    fn access(&self) -> OracleAccess {
        self.access
    }

    fn observe(&mut self, index: usize) -> Result<bool, BooleanPhaseError> {
        let result = self.access.observe(self.truth, index)?;
        if self.access != OracleAccess::UncontrolledPhase || index != 0 {
            self.oracle_calls += 1;
        }
        Ok(result)
    }
}

/// Recover the promised candidate's observable class by adaptive elimination.
///
/// The candidate list is public. The caller promises that the hidden function
/// belongs to one of its observable classes; the query protocol cannot certify
/// that promise. Hidden access occurs only through the oracle's `observe`.
/// The algorithm chooses the first coordinate separating surviving classes. Complements collapse
/// before querying under uncontrolled phase access. The transcript proves an
/// achievable query count for this candidate list and observation protocol.
pub fn recover_observable_class(
    oracle: &mut impl ObservableBooleanOracle,
    candidates: &[Vec<bool>],
) -> Result<OracleRecovery, BooleanPhaseError> {
    let dimension = oracle.dimension();
    let access = oracle.access();
    if candidates.is_empty()
        || candidates
            .iter()
            .any(|candidate| candidate.len() != dimension)
    {
        return Err(BooleanPhaseError::InvalidCandidates);
    }
    let mut classes: Vec<Vec<bool>> = candidates
        .iter()
        .map(|candidate| access.representative(candidate))
        .collect::<Result<BTreeSet<_>, _>>()?
        .into_iter()
        .collect();
    let initial_class_count = classes.len();
    let mut queries = Vec::new();
    while classes.len() > 1 {
        let input = (0..dimension)
            .find(|&index| {
                classes
                    .iter()
                    .skip(1)
                    .any(|candidate| candidate[index] != classes[0][index])
            })
            .expect("distinct canonical classes differ at a coordinate");
        let observed_bit = oracle.observe(input)?;
        classes.retain(|candidate| candidate[input] == observed_bit);
        queries.push(OracleQuery {
            input,
            observed_bit,
            remaining_classes: classes.len(),
        });
    }
    let representative = classes.pop().expect("a nonempty candidate class remains");
    Ok(OracleRecovery {
        access,
        initial_class_count,
        representative,
        queries,
    })
}

/// Exact probabilities after H^n, one uncontrolled phase call, and H^n.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WalshMeasurement {
    pub probability_numerators: Vec<u64>,
    pub probability_denominator: u64,
    pub oracle_calls: usize,
}

pub fn walsh_measurement(truth: &[bool]) -> Result<WalshMeasurement, BooleanPhaseError> {
    let spectrum = boolean_spectrum(truth)?;
    Ok(WalshMeasurement {
        probability_numerators: spectrum
            .walsh_coefficients
            .iter()
            .map(|value| (value * value) as u64)
            .collect(),
        probability_denominator: (truth.len() * truth.len()) as u64,
        oracle_calls: 1,
    })
}

fn validate_truth_table(truth: &[bool]) -> Result<(), BooleanPhaseError> {
    if truth.len().is_power_of_two() && truth.len() <= 1 << 11 {
        Ok(())
    } else {
        Err(BooleanPhaseError::InvalidTruthTable)
    }
}

fn evaluate_monomials(monomials: &[usize], index: usize) -> bool {
    monomials
        .iter()
        .fold(false, |value, &mask| value ^ (index & mask == mask))
}

pub(super) fn binary_rank(rows: impl IntoIterator<Item = u64>, columns: usize) -> usize {
    let mut pivots = vec![0_u64; columns];
    let mut rank = 0;
    for mut row in rows {
        for column in (0..columns).rev() {
            if row & (1 << column) == 0 {
                continue;
            }
            if pivots[column] == 0 {
                pivots[column] = row;
                rank += 1;
                break;
            }
            row ^= pivots[column];
        }
    }
    rank
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cayley_dickson::SignTable;

    #[test]
    fn low_weight_recovery_covers_each_coefficient_and_requires_its_samples() {
        for (variables, degree, query_count) in [(3, 1, 4), (4, 2, 11), (5, 3, 26), (6, 4, 57)] {
            let inputs = low_weight_query_inputs(variables, degree).unwrap();
            assert_eq!(inputs.len(), query_count);
            for coefficients in inputs
                .iter()
                .map(|&mask| vec![mask])
                .chain([inputs.clone()])
            {
                let samples: Vec<_> = inputs
                    .iter()
                    .map(|&input| (input, evaluate_monomials(&coefficients, input)))
                    .collect();
                assert_eq!(
                    recover_degree_promised_anf(variables, degree, &samples).unwrap(),
                    coefficients
                );
                assert_eq!(
                    recover_degree_promised_anf(variables, degree, &samples[1..]),
                    Err(DegreePromisedAnfError::InvalidLowWeightSamples)
                );
            }
            let higher_degree_mask = (1 << (degree + 1)) - 1;
            let aliased_samples: Vec<_> = inputs
                .iter()
                .map(|&input| (input, evaluate_monomials(&[higher_degree_mask], input)))
                .collect();
            assert!(aliased_samples.iter().all(|sample| !sample.1));
            assert!(
                recover_degree_promised_anf(variables, degree, &aliased_samples)
                    .unwrap()
                    .is_empty()
            );
            assert!(evaluate_monomials(
                &[higher_degree_mask],
                higher_degree_mask
            ));
        }
        assert_eq!(
            recover_degree_promised_anf(0, 0, &[(0, true)]).unwrap(),
            vec![0]
        );
        let complete_inputs = low_weight_query_inputs(8, 8).unwrap();
        assert_eq!(complete_inputs.len(), 256);
        let complete_samples: Vec<_> = complete_inputs
            .iter()
            .map(|&input| (input, evaluate_monomials(&[255], input)))
            .collect();
        assert_eq!(
            recover_degree_promised_anf(8, 8, &complete_samples).unwrap(),
            vec![255]
        );
        for (variables, degree) in [(9, 0), (3, 4), (u32::MAX, 0), (3, u32::MAX)] {
            assert_eq!(
                low_weight_query_inputs(variables, degree),
                Err(DegreePromisedAnfError::InvalidDegreePromise)
            );
        }
        for samples in [
            vec![(0, false), (0, true)],
            vec![],
            vec![(1, false)],
            vec![(0, false), (1, false)],
        ] {
            assert_eq!(
                recover_degree_promised_anf(0, 0, &samples),
                Err(DegreePromisedAnfError::InvalidLowWeightSamples)
            );
        }
    }

    #[test]
    fn translated_cubics_collide_in_walsh_probabilities_beyond_complementation() {
        for variables in [3, 5] {
            let first: Vec<_> = (0..1 << variables)
                .map(|input| evaluate_monomials(&[7], input))
                .collect();
            let second: Vec<_> = (0..1 << variables)
                .map(|input| evaluate_monomials(&[6, 7], input))
                .collect();
            assert_ne!(first, second);
            assert_ne!(first.iter().map(|value| !value).collect::<Vec<_>>(), second);
            assert!((0..first.len()).all(|input| second[input] == first[input ^ 1]));
            assert_eq!(
                walsh_measurement(&first).unwrap(),
                walsh_measurement(&second).unwrap()
            );
            assert_ne!(
                OracleAccess::UncontrolledPhase
                    .representative(&first)
                    .unwrap(),
                OracleAccess::UncontrolledPhase
                    .representative(&second)
                    .unwrap()
            );
        }
    }

    #[test]
    fn walsh_transform_matches_direct_sums_and_affine_distance() {
        for mask in 0_u16..256 {
            let truth: Vec<bool> = (0..8).map(|index| mask & (1 << index) != 0).collect();
            let spectrum = boolean_spectrum(&truth).unwrap();
            let mut nearest_affine_distance = truth.len();
            for frequency in 0_usize..8 {
                let direct_walsh: i64 = truth
                    .iter()
                    .enumerate()
                    .map(|(index, &value)| {
                        if value ^ ((index & frequency).count_ones() % 2 != 0) {
                            -1
                        } else {
                            1
                        }
                    })
                    .sum();
                assert_eq!(spectrum.walsh_coefficients[frequency], direct_walsh);
                for constant in [false, true] {
                    let distance = truth
                        .iter()
                        .enumerate()
                        .filter(|&(index, &value)| {
                            value != (constant ^ ((index & frequency).count_ones() % 2 != 0))
                        })
                        .count();
                    nearest_affine_distance = nearest_affine_distance.min(distance);
                }
            }
            assert_eq!(spectrum.nonlinearity, nearest_affine_distance);
        }
    }

    #[test]
    fn highest_generator_negative_control_replays_through_order_eleven() {
        for order in 3..=11 {
            let audit = audit_highest_generator_boolean_family(order).unwrap();
            assert!(audit.matches_highest_generator_sign_row);
            assert_eq!(audit.spectrum.algebraic_degree, order - 1);
            assert_eq!(audit.spectrum.nonlinearity, 2);
            assert_eq!(audit.immunity.algebraic_immunity, 2);
            assert_eq!(audit.immunity.affine_support_ranks, [order as usize + 1; 2]);
            let measurement = walsh_measurement(&audit.truth_table).unwrap();
            assert_eq!(
                measurement.probability_numerators.iter().sum::<u64>(),
                measurement.probability_denominator
            );
        }
    }

    #[test]
    fn octonion_associator_control_is_linear_with_deterministic_walsh_outcome() {
        let signs = SignTable::new(8);
        let (first, second) = (1, 4);
        let truth: Vec<bool> = (0..8)
            .map(|index| {
                signs.sign(first, second)
                    * signs.sign(first ^ second, index)
                    * signs.sign(second, index)
                    * signs.sign(first, second ^ index)
                    < 0
            })
            .collect();
        assert_eq!(
            truth,
            (0..8).map(|index| index & 2 != 0).collect::<Vec<_>>()
        );
        let spectrum = boolean_spectrum(&truth).unwrap();
        assert_eq!(spectrum.algebraic_degree, 1);
        assert_eq!(spectrum.nonlinearity, 0);
        let measurement = walsh_measurement(&truth).unwrap();
        assert_eq!(
            measurement.probability_numerators,
            vec![0, 0, 64, 0, 0, 0, 0, 0]
        );
        assert_eq!(measurement.probability_denominator, 64);
        assert_eq!(measurement.oracle_calls, 1);
    }

    #[test]
    fn finite_recovery_respects_phase_quotients_and_control_resource() {
        let candidates: Vec<Vec<bool>> = (0_u16..256)
            .map(|mask| (0..8).map(|index| mask & (1 << index) != 0).collect())
            .collect();
        for access in [
            OracleAccess::Value,
            OracleAccess::UncontrolledPhase,
            OracleAccess::ControlledPhase,
        ] {
            for hidden in &candidates {
                let mut oracle = TruthTableOracle::new(hidden, access).unwrap();
                let result = recover_observable_class(&mut oracle, &candidates).unwrap();
                assert_eq!(
                    result.representative,
                    access.representative(hidden).unwrap()
                );
                let phase = access == OracleAccess::UncontrolledPhase;
                assert_eq!(result.initial_class_count, if phase { 128 } else { 256 });
                assert_eq!(result.queries.len(), if phase { 7 } else { 8 });
                assert_eq!(oracle.oracle_calls(), result.queries.len());
                let queried: BTreeSet<usize> =
                    result.queries.iter().map(|query| query.input).collect();
                assert_eq!(queried.len(), result.queries.len());
            }
        }
        let truth = &candidates[73];
        let complement: Vec<bool> = truth.iter().map(|value| !value).collect();
        assert_eq!(
            walsh_measurement(truth).unwrap(),
            walsh_measurement(&complement).unwrap()
        );
        assert_eq!(
            OracleAccess::UncontrolledPhase
                .representative(truth)
                .unwrap(),
            OracleAccess::UncontrolledPhase
                .representative(&complement)
                .unwrap()
        );
        assert_ne!(
            OracleAccess::ControlledPhase.observe(truth, 0).unwrap(),
            OracleAccess::ControlledPhase
                .observe(&complement, 0)
                .unwrap()
        );
    }

    #[test]
    fn oracle_and_metric_domains_are_explicit() {
        assert_eq!(
            boolean_spectrum(&[]),
            Err(BooleanPhaseError::InvalidTruthTable)
        );
        assert_eq!(
            boolean_spectrum(&[true; 3]),
            Err(BooleanPhaseError::InvalidTruthTable)
        );
        assert_eq!(
            audit_highest_generator_boolean_family(2),
            Err(BooleanPhaseError::UnsupportedOrder)
        );
        assert_eq!(
            OracleAccess::Value.observe(&[false; 8], 8),
            Err(BooleanPhaseError::InvalidQuery {
                index: 8,
                dimension: 8
            })
        );
        let mut oracle = TruthTableOracle::new(&[false; 8], OracleAccess::Value).unwrap();
        assert_eq!(
            recover_observable_class(&mut oracle, &[]),
            Err(BooleanPhaseError::InvalidCandidates)
        );
        assert_eq!(
            recover_observable_class(&mut oracle, &[vec![true; 4]]),
            Err(BooleanPhaseError::InvalidCandidates)
        );
    }
}
