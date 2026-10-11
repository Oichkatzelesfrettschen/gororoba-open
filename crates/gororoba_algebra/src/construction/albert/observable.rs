//! Fixed-input Albert Jordan associators in trace-metric coordinates.
//!
//! `T_{A,B}(X) = (A circle B) circle X - A circle (B circle X)` is linear in
//! X. Its values measure Jordan nonassociativity, which also occurs in special
//! Jordan algebras. A nonzero value therefore supplies no exceptionality test.
//! The operator can be non-self-adjoint: its trace adjoint is `T_{B,A}`.

use super::AlbertElement;
use nalgebra::{DMatrix, SVD};
use num_rational::BigRational;
use num_traits::Zero;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlbertObservableError {
    NonfiniteInput,
    NonfiniteResult,
}

impl std::fmt::Display for AlbertObservableError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for AlbertObservableError {}

/// A and B stay fixed for the lifetime of the linear map. Coordinate matrices
/// act on `AlbertElement::coordinates`; the trace Gram matrix supplies the
/// adjoint and the orthonormal matrix used for a spectral norm.
#[derive(Debug, Clone)]
pub struct AlbertLinearizedAssociator {
    left: AlbertElement,
    right: AlbertElement,
    jordan_pair: AlbertElement,
    coordinate_matrix: [[f64; 27]; 27],
    orthonormal_matrix: [[f64; 27]; 27],
}

impl AlbertLinearizedAssociator {
    pub fn new(left: AlbertElement, right: AlbertElement) -> Result<Self, AlbertObservableError> {
        if left
            .coordinates()
            .iter()
            .chain(right.coordinates().iter())
            .any(|value| !value.is_finite())
        {
            return Err(AlbertObservableError::NonfiniteInput);
        }
        let jordan_pair = left.jordan_product(&right);
        let mut operator = Self {
            left,
            right,
            jordan_pair,
            coordinate_matrix: [[0.0; 27]; 27],
            orthonormal_matrix: [[0.0; 27]; 27],
        };
        for column in 0..27 {
            let mut basis = [0.0; 27];
            basis[column] = 1.0;
            let image = operator
                .apply(&AlbertElement::from_coordinates(basis))?
                .coordinates();
            for (row, value) in image.into_iter().enumerate() {
                operator.coordinate_matrix[row][column] = value;
                let row_weight: f64 = if row < 3 { 1.0 } else { 2.0 };
                let column_weight: f64 = if column < 3 { 1.0 } else { 2.0 };
                let normalized = value * (row_weight / column_weight).sqrt();
                if !normalized.is_finite() {
                    return Err(AlbertObservableError::NonfiniteResult);
                }
                operator.orthonormal_matrix[row][column] = normalized;
            }
        }
        Ok(operator)
    }

    pub fn apply(&self, input: &AlbertElement) -> Result<AlbertElement, AlbertObservableError> {
        if input.coordinates().iter().any(|value| !value.is_finite()) {
            return Err(AlbertObservableError::NonfiniteInput);
        }
        let first = self.jordan_pair.jordan_product(input).coordinates();
        let second = self
            .left
            .jordan_product(&self.right.jordan_product(input))
            .coordinates();
        let difference = std::array::from_fn(|index| first[index] - second[index]);
        if difference.iter().any(|value| !value.is_finite()) {
            return Err(AlbertObservableError::NonfiniteResult);
        }
        Ok(AlbertElement::from_coordinates(difference))
    }

    pub fn coordinate_matrix(&self) -> &[[f64; 27]; 27] {
        &self.coordinate_matrix
    }

    /// `sqrt(G) M inv(sqrt(G))` acts on orthonormal trace coordinates.
    pub fn orthonormal_matrix(&self) -> &[[f64; 27]; 27] {
        &self.orthonormal_matrix
    }

    /// The coordinate adjoint is `G^-1 M^T G`, rather than `M^T`.
    pub fn trace_adjoint_coordinate_matrix(&self) -> [[f64; 27]; 27] {
        std::array::from_fn(|row| {
            std::array::from_fn(|column| {
                let row_weight = if row < 3 { 1.0 } else { 2.0 };
                let column_weight = if column < 3 { 1.0 } else { 2.0 };
                self.coordinate_matrix[column][row] * column_weight / row_weight
            })
        })
    }

    /// Floating-point largest singular value in the trace inner product.
    /// The SVD is a numerical value, rather than an interval-certified bound.
    pub fn trace_operator_norm(&self) -> f64 {
        let matrix = DMatrix::from_fn(27, 27, |row, column| self.orthonormal_matrix[row][column]);
        SVD::new(matrix, false, false).singular_values.max()
    }

    /// Exact squared Frobenius bound of the stored coordinate matrix:
    /// `sum_ij (G_ii / G_jj) M_ij^2`. Every finite f64 entry has an exact
    /// rational representation. For a nonzero matrix, taking the square root
    /// gives a sufficient block-encoding scale because the spectral norm is
    /// at most Frobenius. A zero matrix permits any positive encoding scale.
    /// The certificate bounds the stored matrix; floating-point construction
    /// error relative to ideal real arithmetic remains a separate quantity.
    pub fn trace_frobenius_norm_squared_exact(&self) -> BigRational {
        let mut squared_norm = BigRational::zero();
        for (row, entries) in self.coordinate_matrix.iter().enumerate() {
            for (column, entry) in entries.iter().enumerate() {
                let value = BigRational::from_float(*entry).expect("finite matrix entry");
                let row_weight = if row < 3 { 1 } else { 2 };
                let column_weight = if column < 3 { 1 } else { 2 };
                let ratio = BigRational::new(row_weight.into(), column_weight.into());
                squared_norm += &value * &value * ratio;
            }
        }
        squared_norm
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn real_symmetric(matrix: [[f64; 3]; 3]) -> AlbertElement {
        let mut result = AlbertElement::diagonal(matrix[0][0], matrix[1][1], matrix[2][2]);
        result.off[0][0] = matrix[1][2];
        result.off[1][0] = matrix[0][2];
        result.off[2][0] = matrix[0][1];
        result
    }

    fn matrix_product(left: [[f64; 3]; 3], right: [[f64; 3]; 3]) -> [[f64; 3]; 3] {
        std::array::from_fn(|row| {
            std::array::from_fn(|column| {
                (0..3)
                    .map(|inner| left[row][inner] * right[inner][column])
                    .sum()
            })
        })
    }

    fn commutator(left: [[f64; 3]; 3], right: [[f64; 3]; 3]) -> [[f64; 3]; 3] {
        let forward = matrix_product(left, right);
        let reverse = matrix_product(right, left);
        std::array::from_fn(|row| {
            std::array::from_fn(|column| forward[row][column] - reverse[row][column])
        })
    }

    #[test]
    fn fixed_associator_matches_independent_special_jordan_double_commutator() {
        let left = [[1.0, 2.0, -1.0], [2.0, 0.0, 3.0], [-1.0, 3.0, 4.0]];
        let right = [[0.0, -2.0, 3.0], [-2.0, 5.0, 1.0], [3.0, 1.0, -1.0]];
        let input = [[2.0, 1.0, -3.0], [1.0, 4.0, -2.0], [-3.0, -2.0, 1.0]];
        let expected = commutator(right, commutator(left, input));
        let expected = expected.map(|row| row.map(|entry| entry / 4.0));
        let operator =
            AlbertLinearizedAssociator::new(real_symmetric(left), real_symmetric(right)).unwrap();
        assert_eq!(
            operator
                .apply(&real_symmetric(input))
                .unwrap()
                .coordinates(),
            real_symmetric(expected).coordinates()
        );
    }

    #[test]
    fn diagonal_subalgebra_and_unit_controls_vanish() {
        let operator = AlbertLinearizedAssociator::new(
            AlbertElement::diagonal(1.0, 3.0, -2.0),
            AlbertElement::diagonal(2.0, -1.0, 4.0),
        )
        .unwrap();
        assert_eq!(
            operator
                .apply(&AlbertElement::diagonal(3.0, 7.0, -2.0))
                .unwrap()
                .coordinates(),
            [0.0; 27]
        );
        let arbitrary =
            AlbertElement::from_coordinates(std::array::from_fn(|index| index as f64 - 13.0));
        let unit_operator =
            AlbertLinearizedAssociator::new(AlbertElement::diagonal(1.0, 1.0, 1.0), arbitrary)
                .unwrap();
        assert_eq!(*unit_operator.coordinate_matrix(), [[0.0; 27]; 27]);
        assert_eq!(unit_operator.trace_operator_norm(), 0.0);
        assert_eq!(
            unit_operator.trace_frobenius_norm_squared_exact(),
            BigRational::zero()
        );
    }

    #[test]
    fn special_jordan_nonassociativity_is_a_nonzero_control() {
        let projection = AlbertElement::diagonal(1.0, 0.0, 0.0);
        let operator = AlbertLinearizedAssociator::new(projection.clone(), projection).unwrap();
        let mut input = AlbertElement::zero();
        input.off[2][0] = 1.0;
        let mut expected = [0.0; 27];
        expected[19] = 0.25;
        assert_eq!(operator.apply(&input).unwrap().coordinates(), expected);
        assert_eq!(operator.trace_operator_norm(), 0.25);
        // Sixteen off-diagonal octonion coordinates each carry eigenvalue 1/4.
        assert_eq!(
            operator.trace_frobenius_norm_squared_exact(),
            BigRational::from_integer(1.into())
        );
    }

    #[test]
    fn frobenius_bound_weights_diagonal_off_diagonal_transfers() {
        let projection = AlbertElement::diagonal(1.0, 0.0, 0.0);
        let mut real_off_diagonal = AlbertElement::zero();
        real_off_diagonal.off[2][0] = 1.0;
        let operator = AlbertLinearizedAssociator::new(projection, real_off_diagonal).unwrap();
        // The real (0,1) coordinate maps to (-1/2, 1/2, 0), contributing 1/4.
        // Eight (0,2) octonion coordinates map to (1,2) with coefficient 1/4.
        assert_eq!(
            operator.trace_frobenius_norm_squared_exact(),
            BigRational::new(3.into(), 4.into())
        );
        assert!((operator.trace_operator_norm() - 0.5).abs() < 1e-14);
    }

    #[test]
    fn trace_adjoint_swaps_fixed_arguments_and_matrix_is_linear() {
        let left =
            AlbertElement::from_coordinates(std::array::from_fn(|index| (index % 4) as f64 - 1.0));
        let right =
            AlbertElement::from_coordinates(std::array::from_fn(|index| (index % 5) as f64 - 2.0));
        let forward = AlbertLinearizedAssociator::new(left.clone(), right.clone()).unwrap();
        let reverse = AlbertLinearizedAssociator::new(right, left).unwrap();
        assert_eq!(
            forward.trace_adjoint_coordinate_matrix(),
            *reverse.coordinate_matrix()
        );
        assert_ne!(forward.coordinate_matrix(), reverse.coordinate_matrix());
        let coordinates = std::array::from_fn(|index| (index % 7) as f64 - 3.0);
        let image = forward
            .apply(&AlbertElement::from_coordinates(coordinates))
            .unwrap()
            .coordinates();
        for (row, expected) in image.iter().enumerate() {
            let actual: f64 = forward.coordinate_matrix()[row]
                .iter()
                .zip(coordinates)
                .map(|(entry, coordinate)| entry * coordinate)
                .sum();
            assert_eq!(actual, *expected);
        }
        let mut mixed = [0.0; 27];
        mixed[0] = 3.0;
        mixed[4] = 2.0;
        let normalized = AlbertElement::from_coordinates(mixed).orthonormal_coordinates();
        let expected = forward
            .apply(&AlbertElement::from_coordinates(mixed))
            .unwrap()
            .orthonormal_coordinates();
        for (row, expected_coordinate) in expected.iter().enumerate() {
            let actual: f64 = forward.orthonormal_matrix()[row]
                .iter()
                .zip(normalized)
                .map(|(entry, coordinate)| entry * coordinate)
                .sum();
            assert!((actual - expected_coordinate).abs() < 1e-12);
        }
    }

    #[test]
    fn nonfinite_inputs_and_arithmetic_overflow_fail_explicitly() {
        let unit = AlbertElement::diagonal(1.0, 1.0, 1.0);
        let invalid = AlbertElement::diagonal(f64::NAN, 0.0, 0.0);
        assert!(matches!(
            AlbertLinearizedAssociator::new(invalid.clone(), unit.clone()),
            Err(AlbertObservableError::NonfiniteInput)
        ));
        let operator = AlbertLinearizedAssociator::new(unit.clone(), unit).unwrap();
        assert!(matches!(
            operator.apply(&invalid),
            Err(AlbertObservableError::NonfiniteInput)
        ));
        let huge = AlbertElement::diagonal(f64::MAX, 0.0, 0.0);
        assert!(matches!(
            AlbertLinearizedAssociator::new(huge.clone(), huge),
            Err(AlbertObservableError::NonfiniteResult)
        ));
    }
}
