//! Bounded Boolean label permutations and exact modular-arithmetic witnesses.
//!
//! Target-excluding cubes are involutions on one through five data bits. Their
//! controlled words describe basis labels with an outer control in the high
//! bit. Diagonal signs, coherent circuit phases, ancillas, gate synthesis and
//! device execution require their own semantics and evidence.

use super::boolean_phase::binary_rank;

pub const MAX_BOOLEAN_PERMUTATION_WIDTH: u32 = 5;

#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BooleanPermutationError {
    #[error("Boolean permutation words support one through five data bits")]
    InvalidWidth,
    #[error("a target cube must exclude its target and constrain only data bits")]
    InvalidCube,
    #[error("basis input {input} lies outside the domain of size {size}")]
    InvalidInput { input: usize, size: usize },
    #[error("a complete permutation must be a bijection on two through 32 labels")]
    InvalidPermutation,
    #[error(
        "identity-padded modular maps require modulus 3 through 31 and an invertible multiplier"
    )]
    InvalidModularMap,
    #[error("the retained modular target-flip witnesses cover multipliers 2, 4 and 16 modulo 21")]
    UnsupportedWitness,
}

/// A data predicate whose target exclusion is checked by TargetFlipWord::new.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TargetCube {
    pub target: u32,
    pub control_mask: usize,
    pub control_state: usize,
}

/// An immutable, validated word of label-flip involutions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TargetFlipWord {
    data_width: u32,
    cubes: Vec<TargetCube>,
}

impl TargetFlipWord {
    pub fn new(data_width: u32, cubes: Vec<TargetCube>) -> Result<Self, BooleanPermutationError> {
        if !(1..=MAX_BOOLEAN_PERMUTATION_WIDTH).contains(&data_width) {
            return Err(BooleanPermutationError::InvalidWidth);
        }
        let size = 1_usize << data_width;
        if cubes.iter().any(|cube| {
            cube.target >= data_width
                || cube.control_mask >= size
                || cube.control_state & !cube.control_mask != 0
                || cube.control_mask & (1 << cube.target) != 0
        }) {
            return Err(BooleanPermutationError::InvalidCube);
        }
        Ok(Self { data_width, cubes })
    }

    pub fn data_width(&self) -> u32 {
        self.data_width
    }

    pub fn cubes(&self) -> &[TargetCube] {
        &self.cubes
    }

    pub fn apply_data(&self, mut input: usize) -> Result<usize, BooleanPermutationError> {
        let size = 1_usize << self.data_width;
        if input >= size {
            return Err(BooleanPermutationError::InvalidInput { input, size });
        }
        for cube in &self.cubes {
            if input & cube.control_mask == cube.control_state {
                input ^= 1 << cube.target;
            }
        }
        Ok(input)
    }

    /// Bit data_width is the control; the lower bits are the data label.
    pub fn apply_controlled(&self, packed: usize) -> Result<usize, BooleanPermutationError> {
        let control = 1_usize << self.data_width;
        if packed >= 2 * control {
            return Err(BooleanPermutationError::InvalidInput {
                input: packed,
                size: 2 * control,
            });
        }
        if packed & control == 0 {
            Ok(packed)
        } else {
            Ok(control | self.apply_data(packed & (control - 1))?)
        }
    }

    /// Every cube excludes its target, so reversing the word gives its inverse.
    pub fn inverse(&self) -> Self {
        Self {
            data_width: self.data_width,
            cubes: self.cubes.iter().rev().copied().collect(),
        }
    }
}

/// The label and separate diagonal sign of one signed-XOR basis action.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignedBasisImage {
    pub label: usize,
    pub negative: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignedXorTranslation {
    translation: usize,
    sign_exponents: Vec<bool>,
}

impl SignedXorTranslation {
    pub fn new(
        translation: usize,
        sign_exponents: Vec<bool>,
    ) -> Result<Self, BooleanPermutationError> {
        let size = sign_exponents.len();
        if !(2..=32).contains(&size) || !size.is_power_of_two() || translation >= size {
            return Err(BooleanPermutationError::InvalidPermutation);
        }
        Ok(Self {
            translation,
            sign_exponents,
        })
    }

    /// Fixing the zero label forces identity label action; diagonal signs remain.
    pub fn fixes_zero_label(&self) -> bool {
        self.translation == 0
    }

    pub fn apply_basis(&self, input: usize) -> Result<SignedBasisImage, BooleanPermutationError> {
        let size = self.sign_exponents.len();
        if input >= size {
            return Err(BooleanPermutationError::InvalidInput { input, size });
        }
        Ok(SignedBasisImage {
            label: input ^ self.translation,
            negative: self.sign_exponents[input],
        })
    }
}

fn permutation_width(permutation: &[usize]) -> Result<u32, BooleanPermutationError> {
    let size = permutation.len();
    if !(2..=32).contains(&size) || !size.is_power_of_two() {
        return Err(BooleanPermutationError::InvalidPermutation);
    }
    let mut seen = vec![false; size];
    for &image in permutation {
        if image >= size || seen[image] {
            return Err(BooleanPermutationError::InvalidPermutation);
        }
        seen[image] = true;
    }
    Ok(size.trailing_zeros())
}

pub fn inverse_permutation(permutation: &[usize]) -> Result<Vec<usize>, BooleanPermutationError> {
    permutation_width(permutation)?;
    let mut inverse = vec![0; permutation.len()];
    for (input, &image) in permutation.iter().enumerate() {
        inverse[image] = input;
    }
    Ok(inverse)
}

/// Identity padding on unused labels is part of the mathematical map.
/// The register uses the minimum binary width that represents `0..modulus`.
pub fn identity_padded_modular_permutation(
    modulus: usize,
    multiplier: usize,
) -> Result<Vec<usize>, BooleanPermutationError> {
    if !(3..=31).contains(&modulus) {
        return Err(BooleanPermutationError::InvalidModularMap);
    }
    let normalized = multiplier % modulus;
    let (mut first, mut second) = (normalized, modulus);
    while second != 0 {
        (first, second) = (second, first % second);
    }
    if first != 1 {
        return Err(BooleanPermutationError::InvalidModularMap);
    }
    let width = usize::BITS - (modulus - 1).leading_zeros();
    Ok((0..1 << width)
        .map(|input| {
            if input < modulus {
                normalized * input % modulus
            } else {
                input
            }
        })
        .collect())
}

/// Constant and degree-one ANF coefficients of a complete finite bijection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineSkeleton {
    pub data_width: u32,
    pub constant: usize,
    pub linear_rows: Vec<usize>,
    pub linear_rank: usize,
}

pub fn affine_skeleton(permutation: &[usize]) -> Result<AffineSkeleton, BooleanPermutationError> {
    let width = permutation_width(permutation)?;
    let constant = permutation[0];
    let linear_rows: Vec<_> = (0..width)
        .map(|output_bit| {
            (0..width).fold(0, |row, input_bit| {
                row | (((permutation[1 << input_bit] ^ constant) >> output_bit & 1) << input_bit)
            })
        })
        .collect();
    let linear_rank = binary_rank(linear_rows.iter().map(|&row| row as u64), width as usize);
    Ok(AffineSkeleton {
        data_width: width,
        constant,
        linear_rows,
        linear_rank,
    })
}

const fn cube(target: u32, control_mask: usize, control_state: usize) -> TargetCube {
    TargetCube {
        target,
        control_mask,
        control_state,
    }
}

const N21_DOUBLE: [TargetCube; 17] = [
    cube(4, 12, 0),
    cube(4, 15, 3),
    cube(1, 5, 4),
    cube(1, 29, 28),
    cube(2, 27, 11),
    cube(3, 16, 0),
    cube(3, 23, 3),
    cube(2, 18, 2),
    cube(2, 25, 9),
    cube(2, 27, 18),
    cube(1, 4, 0),
    cube(1, 9, 0),
    cube(1, 28, 24),
    cube(0, 18, 2),
    cube(0, 30, 18),
    cube(4, 9, 0),
    cube(4, 15, 6),
];
const N21_QUADRUPLE: [TargetCube; 17] = [
    cube(2, 27, 9),
    cube(2, 10, 0),
    cube(2, 9, 0),
    cube(0, 10, 0),
    cube(0, 28, 28),
    cube(0, 16, 16),
    cube(0, 4, 0),
    cube(4, 9, 1),
    cube(1, 29, 12),
    cube(3, 18, 2),
    cube(1, 24, 8),
    cube(4, 11, 3),
    cube(0, 30, 18),
    cube(0, 24, 16),
    cube(2, 27, 18),
    cube(2, 10, 0),
    cube(2, 18, 0),
];

/// The finite words certified by TargetFlipN21's network_correct theorems.
///
/// All 32 data labels and both control branches belong to the contract. The
/// words are retained witnesses, not an optimizer or a physical gate estimate.
pub fn n21_target_flip_witness(
    multiplier: usize,
) -> Result<TargetFlipWord, BooleanPermutationError> {
    match multiplier {
        2 => TargetFlipWord::new(5, N21_DOUBLE.to_vec()),
        4 => TargetFlipWord::new(5, N21_QUADRUPLE.to_vec()),
        16 => Ok(TargetFlipWord::new(5, N21_QUADRUPLE.to_vec())?.inverse()),
        _ => Err(BooleanPermutationError::UnsupportedWitness),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_supported_target_excluding_cube_is_a_controlled_label_involution() {
        let mut cube_count = 0;
        for width in 1..=MAX_BOOLEAN_PERMUTATION_WIDTH {
            let size = 1_usize << width;
            for target in 0..width {
                for control_mask in 0..size {
                    if control_mask & (1 << target) != 0 {
                        continue;
                    }
                    for control_state in 0..size {
                        if control_state & !control_mask != 0 {
                            continue;
                        }
                        let word = TargetFlipWord::new(
                            width,
                            vec![cube(target, control_mask, control_state)],
                        )
                        .unwrap();
                        for input in 0..size {
                            assert_eq!(
                                word.apply_data(word.apply_data(input).unwrap()).unwrap(),
                                input
                            );
                            assert_eq!(word.apply_controlled(input).unwrap(), input);
                            let enabled = size | input;
                            assert_eq!(
                                word.apply_controlled(word.apply_controlled(enabled).unwrap())
                                    .unwrap(),
                                enabled
                            );
                        }
                        cube_count += 1;
                    }
                }
            }
        }
        assert_eq!(cube_count, 547);
    }

    #[test]
    fn power_of_two_moduli_use_minimal_registers_for_permutation_consumers() {
        for (modulus, expected_width, expected) in [
            (4, 2, vec![0, 3, 2, 1]),
            (8, 3, vec![0, 3, 6, 1, 4, 7, 2, 5]),
            (
                16,
                4,
                vec![0, 3, 6, 9, 12, 15, 2, 5, 8, 11, 14, 1, 4, 7, 10, 13],
            ),
        ] {
            let permutation = identity_padded_modular_permutation(modulus, 3).unwrap();
            assert_eq!(permutation, expected);
            assert_eq!(permutation.len(), modulus);
            assert_eq!(
                affine_skeleton(&permutation).unwrap().data_width,
                expected_width
            );
            let inverse = inverse_permutation(&permutation).unwrap();
            assert_eq!(
                affine_skeleton(&inverse).unwrap().data_width,
                expected_width
            );
            for (input, &image) in permutation.iter().enumerate() {
                assert_eq!(inverse[image], input);
            }
        }
    }

    #[test]
    fn every_admitted_modulus_has_exact_residue_and_identity_padding_domains() {
        for modulus in 3..=31 {
            let identity = identity_padded_modular_permutation(modulus, 1).unwrap();
            let negation = identity_padded_modular_permutation(modulus, modulus - 1).unwrap();
            assert_eq!(identity.len(), modulus.next_power_of_two());
            assert_eq!(identity, (0..identity.len()).collect::<Vec<_>>());
            assert_eq!(negation.len(), identity.len());
            assert!(identity.len() / 2 < modulus);
            for (input, &image) in negation.iter().enumerate() {
                let expected = if input == 0 || input >= modulus {
                    input
                } else {
                    modulus - input
                };
                assert_eq!(image, expected);
            }
            assert_eq!(inverse_permutation(&negation).unwrap(), negation);
        }
    }

    #[test]
    fn n21_words_cover_all_labels_and_control_branches_with_inverse_and_mutations() {
        for multiplier in [2, 4, 16] {
            let word = n21_target_flip_witness(multiplier).unwrap();
            let expected = identity_padded_modular_permutation(21, multiplier).unwrap();
            assert_eq!(expected.len(), 32);
            assert_eq!(&expected[21..], &(21..32).collect::<Vec<_>>());
            for (input, &image) in expected.iter().enumerate() {
                assert_eq!(word.apply_data(input).unwrap(), image);
                assert_eq!(word.apply_controlled(input).unwrap(), input);
                assert_eq!(word.apply_controlled(32 | input).unwrap(), 32 | image);
                assert_eq!(word.inverse().apply_data(image).unwrap(), input);
            }
            for deleted in 0..word.cubes().len() {
                let mut cubes = word.cubes().to_vec();
                cubes.remove(deleted);
                let mutant = TargetFlipWord::new(5, cubes).unwrap();
                assert!(
                    expected
                        .iter()
                        .enumerate()
                        .any(|(input, &image)| mutant.apply_data(input).unwrap() != image)
                );
            }
        }
    }

    #[test]
    fn permutation_invertibility_does_not_force_an_invertible_affine_skeleton() {
        let doubling = identity_padded_modular_permutation(21, 2).unwrap();
        let inverse = inverse_permutation(&doubling).unwrap();
        assert_eq!(
            inverse,
            identity_padded_modular_permutation(21, 11).unwrap()
        );
        assert_eq!(affine_skeleton(&doubling).unwrap().linear_rank, 5);
        assert_eq!(affine_skeleton(&inverse).unwrap().linear_rank, 4);
        for multiplier in [4, 16] {
            assert_eq!(
                affine_skeleton(&identity_padded_modular_permutation(21, multiplier).unwrap())
                    .unwrap()
                    .linear_rank,
                5
            );
        }
        let affine = vec![1, 3, 0, 2];
        let skeleton = affine_skeleton(&affine).unwrap();
        assert_eq!(skeleton.constant, 1);
        assert_eq!(skeleton.linear_rows, vec![2, 1]);
        assert_eq!(skeleton.linear_rank, 2);
    }

    #[test]
    fn fixing_zero_preserves_identity_labels_without_erasing_diagonal_signs() {
        let diagonal = SignedXorTranslation::new(0, vec![true, false, false, true]).unwrap();
        assert!(diagonal.fixes_zero_label());
        assert_eq!(
            diagonal.apply_basis(0).unwrap(),
            SignedBasisImage {
                label: 0,
                negative: true
            }
        );
        for label in 0..4 {
            assert_eq!(diagonal.apply_basis(label).unwrap().label, label);
        }
        let translated = SignedXorTranslation::new(2, vec![false; 4]).unwrap();
        assert!(!translated.fixes_zero_label());
        assert_eq!(translated.apply_basis(0).unwrap().label, 2);
    }

    #[test]
    fn malformed_cubes_permutations_and_out_of_domain_labels_fail_closed() {
        for width in [0, 6, u32::MAX] {
            assert_eq!(
                TargetFlipWord::new(width, vec![]),
                Err(BooleanPermutationError::InvalidWidth)
            );
        }
        for invalid in [
            cube(5, 0, 0),
            cube(0, 1, 0),
            cube(0, 32, 0),
            cube(0, 2, 1),
            cube(u32::MAX, 0, 0),
        ] {
            assert_eq!(
                TargetFlipWord::new(5, vec![invalid]),
                Err(BooleanPermutationError::InvalidCube)
            );
        }
        for permutation in [
            vec![],
            vec![0],
            vec![0, 0],
            vec![0, 2],
            vec![0, 1, 2],
            (0..64).collect(),
        ] {
            assert_eq!(
                affine_skeleton(&permutation),
                Err(BooleanPermutationError::InvalidPermutation)
            );
            assert_eq!(
                inverse_permutation(&permutation),
                Err(BooleanPermutationError::InvalidPermutation)
            );
        }
        for (modulus, multiplier) in [(0, 2), (2, 1), (32, 1), (21, 3)] {
            assert_eq!(
                identity_padded_modular_permutation(modulus, multiplier),
                Err(BooleanPermutationError::InvalidModularMap)
            );
        }
        let word = n21_target_flip_witness(2).unwrap();
        assert!(word.apply_data(32).is_err());
        assert!(word.apply_controlled(64).is_err());
        assert!(n21_target_flip_witness(11).is_err());
        assert!(SignedXorTranslation::new(4, vec![false; 4]).is_err());
        assert!(SignedXorTranslation::new(0, vec![false; 3]).is_err());
        assert!(
            SignedXorTranslation::new(0, vec![false; 2])
                .unwrap()
                .apply_basis(2)
                .is_err()
        );
    }
}
