//! Rational multiplication, kernel and constant-rank certificates.
//!
//! The certificates describe the real Cayley-Dickson convention of
//! `cd_kernel::cayley_dickson::cd_basis_mul_sign`. Exact rational input gives
//! exact rank over both Q and R. Kernel columns solve `a * b = 0` for left
//! multiplication and `b * a = 0` for right multiplication.

use cd_kernel::cayley_dickson::cd_basis_mul_sign;
use nalgebra::DMatrix;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

pub type ExactMatrix = DMatrix<BigRational>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MultiplicationSide {
    Left,
    Right,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CertificateError {
    InvalidDimension(usize),
    InvalidRationalValue,
    InvalidPivotIndices,
    SingularPivot,
    /// The fixed chart's rank stratum excludes the supplied point.
    NonzeroSchurComplement,
}

impl std::fmt::Display for CertificateError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for CertificateError {}

fn validate_coordinates(coordinates: &[BigRational]) -> Result<(), CertificateError> {
    if !coordinates.len().is_power_of_two() {
        return Err(CertificateError::InvalidDimension(coordinates.len()));
    }
    if coordinates.iter().any(|value| value.denom().is_zero()) {
        return Err(CertificateError::InvalidRationalValue);
    }
    Ok(())
}

pub(crate) fn valid_rational_matrix(matrix: &ExactMatrix) -> bool {
    matrix.iter().all(|entry| !entry.denom().is_zero())
}

fn valid_cd_matrix(matrix: &ExactMatrix) -> bool {
    matrix.is_square() && matrix.ncols().is_power_of_two() && valid_rational_matrix(matrix)
}

/// Form the multiplication matrix in every positive power-of-two dimension.
pub fn multiplication_matrix_exact(
    coordinates: &[BigRational],
    side: MultiplicationSide,
) -> Result<ExactMatrix, CertificateError> {
    validate_coordinates(coordinates)?;
    let dimension = coordinates.len();
    let mut matrix = ExactMatrix::zeros(dimension, dimension);
    for (input_basis, coordinate) in coordinates.iter().enumerate() {
        for column in 0..dimension {
            let (left, right) = match side {
                MultiplicationSide::Left => (input_basis, column),
                MultiplicationSide::Right => (column, input_basis),
            };
            matrix[(input_basis ^ column, column)] =
                if cd_basis_mul_sign(dimension, left, right) > 0 {
                    coordinate.clone()
                } else {
                    -coordinate
                };
        }
    }
    Ok(matrix)
}

/// Reduced row echelon form and its pivot columns, with exact arithmetic.
pub(crate) fn row_reduce(matrix: &ExactMatrix) -> (ExactMatrix, Vec<usize>) {
    let mut reduced = matrix.clone();
    let mut pivots = Vec::new();
    for column in 0..matrix.ncols() {
        let pivot_row = pivots.len();
        let Some(nonzero_row) =
            (pivot_row..matrix.nrows()).find(|&row| !reduced[(row, column)].is_zero())
        else {
            continue;
        };
        reduced.swap_rows(pivot_row, nonzero_row);
        let pivot = reduced[(pivot_row, column)].clone();
        for entry in 0..matrix.ncols() {
            reduced[(pivot_row, entry)] /= &pivot;
        }
        for row in 0..matrix.nrows() {
            if row == pivot_row {
                continue;
            }
            let factor = reduced[(row, column)].clone();
            if factor.is_zero() {
                continue;
            }
            for entry in 0..matrix.ncols() {
                let correction = &factor * &reduced[(pivot_row, entry)];
                reduced[(row, entry)] -= correction;
            }
        }
        pivots.push(column);
        if pivots.len() == matrix.nrows() {
            break;
        }
    }
    (reduced, pivots)
}

pub(crate) fn exact_rank(matrix: &ExactMatrix) -> usize {
    row_reduce(matrix).1.len()
}

fn submatrix(matrix: &ExactMatrix, rows: &[usize], columns: &[usize]) -> ExactMatrix {
    ExactMatrix::from_fn(rows.len(), columns.len(), |row, column| {
        matrix[(rows[row], columns[column])].clone()
    })
}

fn complement(dimension: usize, pivots: &[usize]) -> Vec<usize> {
    (0..dimension)
        .filter(|index| !pivots.contains(index))
        .collect()
}

fn determinant(matrix: &ExactMatrix) -> BigRational {
    assert!(matrix.is_square());
    let mut triangular = matrix.clone();
    let mut result = BigRational::one();
    for column in 0..matrix.ncols() {
        let Some(pivot_row) =
            (column..matrix.nrows()).find(|&row| !triangular[(row, column)].is_zero())
        else {
            return BigRational::zero();
        };
        if column != pivot_row {
            triangular.swap_rows(column, pivot_row);
            result = -result;
        }
        let pivot = triangular[(column, column)].clone();
        result *= &pivot;
        for row in column + 1..matrix.nrows() {
            let factor = &triangular[(row, column)] / &pivot;
            for entry in column + 1..matrix.ncols() {
                let correction = &factor * &triangular[(column, entry)];
                triangular[(row, entry)] -= correction;
            }
            triangular[(row, column)] = BigRational::zero();
        }
    }
    result
}

/// Rational scaling data separates unit input from block-encoding scale.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OperatorScaling {
    pub input_norm_squared: BigRational,
    /// `alpha = sum_i |a_i|` bounds `||L_a||_2` and `||R_a||_2` because each
    /// basis multiplication matrix is an orthogonal signed permutation.
    pub block_encoding_alpha: BigRational,
    /// For `a / ||a||_2`, the squared sufficient block scale is
    /// `alpha^2 / ||a||_2^2`. Zero input has no unit normalization.
    pub unit_input_block_alpha_squared: Option<BigRational>,
}

impl OperatorScaling {
    pub fn for_input(coordinates: &[BigRational]) -> Result<Self, CertificateError> {
        validate_coordinates(coordinates)?;
        let input_norm_squared: BigRational = coordinates.iter().map(|value| value * value).sum();
        let block_encoding_alpha: BigRational = coordinates.iter().map(Signed::abs).sum();
        let unit_input_block_alpha_squared = (!input_norm_squared.is_zero())
            .then(|| &block_encoding_alpha * &block_encoding_alpha / &input_norm_squared);
        Ok(Self {
            input_norm_squared,
            block_encoding_alpha,
            unit_input_block_alpha_squared,
        })
    }

    fn has_valid_rationals(&self) -> bool {
        !self.input_norm_squared.denom().is_zero()
            && !self.block_encoding_alpha.denom().is_zero()
            && self
                .unit_input_block_alpha_squared
                .as_ref()
                .is_none_or(|value| !value.denom().is_zero())
    }
}

/// A nonsingular rank-sized minor gives the lower rank bound. Independent
/// kernel columns give the matching upper bound by rank-nullity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnnihilatorCertificate {
    pub matrix: ExactMatrix,
    pub kernel_basis: ExactMatrix,
    pub pivot_rows: Vec<usize>,
    pub pivot_columns: Vec<usize>,
    pub pivot_minor_determinant: BigRational,
    pub scaling: OperatorScaling,
}

impl AnnihilatorCertificate {
    pub fn rank(&self) -> usize {
        self.pivot_columns.len()
    }

    pub fn nullity(&self) -> usize {
        self.kernel_basis.ncols()
    }

    /// Check a supplied partner family spans the full kernel. The check uses
    /// the retained multiplication matrix and independently recomputes rank.
    pub fn kernel_span_equals(&self, partners: &ExactMatrix) -> bool {
        valid_cd_matrix(&self.matrix)
            && valid_rational_matrix(partners)
            && partners.nrows() == self.matrix.ncols()
            && exact_rank(partners) + exact_rank(&self.matrix) == self.matrix.ncols()
            && (&self.matrix * partners).iter().all(Zero::is_zero)
    }

    /// Verify both rank bounds and all retained data against the stated input.
    pub fn verify(&self, coordinates: &[BigRational], side: MultiplicationSide) -> bool {
        if !valid_cd_matrix(&self.matrix)
            || !valid_rational_matrix(&self.kernel_basis)
            || self.pivot_minor_determinant.denom().is_zero()
            || !self.scaling.has_valid_rationals()
        {
            return false;
        }
        let Ok(expected) = multiplication_matrix_exact(coordinates, side) else {
            return false;
        };
        let Ok(expected_scaling) = OperatorScaling::for_input(coordinates) else {
            return false;
        };
        let dimension = coordinates.len();
        if self.matrix != expected
            || self.scaling != expected_scaling
            || self.pivot_rows.len() != self.rank()
            || !valid_indices(&self.pivot_rows, dimension)
            || !valid_indices(&self.pivot_columns, dimension)
            || self.kernel_basis.nrows() != dimension
            || self.rank() + self.nullity() != dimension
        {
            return false;
        }
        let minor = submatrix(&self.matrix, &self.pivot_rows, &self.pivot_columns);
        let actual_determinant = determinant(&minor);
        actual_determinant == self.pivot_minor_determinant
            && !actual_determinant.is_zero()
            && exact_rank(&self.kernel_basis) == self.nullity()
            && (&self.matrix * &self.kernel_basis)
                .iter()
                .all(Zero::is_zero)
    }

    /// For a verified certificate, `matrix / alpha` is a contraction for
    /// nonzero input. The method supplies the encoded matrix and scale,
    /// rather than a quantum circuit.
    pub fn block_normalized_matrix(&self) -> Option<ExactMatrix> {
        (valid_cd_matrix(&self.matrix)
            && self.scaling.has_valid_rationals()
            && self.scaling.block_encoding_alpha.is_positive())
        .then(|| {
            self.matrix
                .map(|entry| entry / &self.scaling.block_encoding_alpha)
        })
    }
}

fn valid_indices(indices: &[usize], dimension: usize) -> bool {
    indices
        .iter()
        .enumerate()
        .all(|(position, &index)| index < dimension && !indices[..position].contains(&index))
}

pub fn annihilator_certificate(
    coordinates: &[BigRational],
    side: MultiplicationSide,
) -> Result<AnnihilatorCertificate, CertificateError> {
    let matrix = multiplication_matrix_exact(coordinates, side)?;
    let (reduced, pivot_columns) = row_reduce(&matrix);
    let pivot_rows = row_reduce(&matrix.transpose()).1;
    let free_columns = complement(matrix.ncols(), &pivot_columns);
    let mut kernel_basis = ExactMatrix::zeros(matrix.ncols(), free_columns.len());
    for (basis_column, &free_column) in free_columns.iter().enumerate() {
        kernel_basis[(free_column, basis_column)] = BigRational::one();
        for (pivot_row, &pivot_column) in pivot_columns.iter().enumerate() {
            kernel_basis[(pivot_column, basis_column)] = -&reduced[(pivot_row, free_column)];
        }
    }
    let pivot_minor_determinant = determinant(&submatrix(&matrix, &pivot_rows, &pivot_columns));
    Ok(AnnihilatorCertificate {
        matrix,
        kernel_basis,
        pivot_rows,
        pivot_columns,
        pivot_minor_determinant,
        scaling: OperatorScaling::for_input(coordinates)?,
    })
}

/// Fixed pivot rows and columns define a relative chart on the rank-r locus.
/// Its domain is `det(P(a)) != 0` and `S(a) - R(a) P(a)^-1 Q(a) = 0`.
/// A chart point has kernel frame `[-P^-1 Q; I]` in pivot/free order.
/// These equations describe an algebraic rank stratum; smoothness requires
/// an independent regularity argument for the equations on parameter space.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantRankChart {
    pub dimension: usize,
    pub side: MultiplicationSide,
    pub pivot_rows: Vec<usize>,
    pub pivot_columns: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChartPointCertificate {
    pub pivot_determinant: BigRational,
    pub schur_complement: ExactMatrix,
    /// Rows follow the original Cayley-Dickson basis order.
    pub kernel_frame: ExactMatrix,
}

impl ConstantRankChart {
    pub fn at(
        coordinates: &[BigRational],
        side: MultiplicationSide,
    ) -> Result<Self, CertificateError> {
        let certificate = annihilator_certificate(coordinates, side)?;
        Ok(Self {
            dimension: coordinates.len(),
            side,
            pivot_rows: certificate.pivot_rows,
            pivot_columns: certificate.pivot_columns,
        })
    }

    /// Admit a point only after evaluating both chart-domain conditions.
    pub fn certify(
        &self,
        coordinates: &[BigRational],
    ) -> Result<ChartPointCertificate, CertificateError> {
        if coordinates.len() != self.dimension {
            return Err(CertificateError::InvalidDimension(coordinates.len()));
        }
        if self.pivot_rows.len() != self.pivot_columns.len()
            || !valid_indices(&self.pivot_rows, self.dimension)
            || !valid_indices(&self.pivot_columns, self.dimension)
        {
            return Err(CertificateError::InvalidPivotIndices);
        }
        let matrix = multiplication_matrix_exact(coordinates, self.side)?;
        let free_rows = complement(self.dimension, &self.pivot_rows);
        let free_columns = complement(self.dimension, &self.pivot_columns);
        let pivot = submatrix(&matrix, &self.pivot_rows, &self.pivot_columns);
        let pivot_determinant = determinant(&pivot);
        if pivot_determinant.is_zero() {
            return Err(CertificateError::SingularPivot);
        }
        let upper_right = submatrix(&matrix, &self.pivot_rows, &free_columns);
        let lower_left = submatrix(&matrix, &free_rows, &self.pivot_columns);
        let lower_right = submatrix(&matrix, &free_rows, &free_columns);
        let rank = self.pivot_columns.len();
        let augmented = ExactMatrix::from_fn(rank, self.dimension, |row, column| {
            if column < rank {
                pivot[(row, column)].clone()
            } else {
                upper_right[(row, column - rank)].clone()
            }
        });
        let (solved, _) = row_reduce(&augmented);
        let inverse_times_upper = ExactMatrix::from_fn(rank, free_columns.len(), |row, column| {
            solved[(row, rank + column)].clone()
        });
        let schur_complement = lower_right - lower_left * &inverse_times_upper;
        if schur_complement.iter().any(|entry| !entry.is_zero()) {
            return Err(CertificateError::NonzeroSchurComplement);
        }
        let mut kernel_frame = ExactMatrix::zeros(self.dimension, free_columns.len());
        for (column, &free_column) in free_columns.iter().enumerate() {
            kernel_frame[(free_column, column)] = BigRational::one();
            for (row, &pivot_column) in self.pivot_columns.iter().enumerate() {
                kernel_frame[(pivot_column, column)] = -&inverse_times_upper[(row, column)];
            }
        }
        Ok(ChartPointCertificate {
            pivot_determinant,
            schur_complement,
            kernel_frame,
        })
    }
}

/// The nonzero rational scalar orbit of `e_1 + e_10` in 32D (A_5).
/// Every point lies in the same rank-24 chart: scalar multiplication preserves
/// the pivot minor and Schur equation, while zero reaches a rank boundary.
pub fn a5_scalar_orbit_point(scale: BigRational) -> Result<Vec<BigRational>, CertificateError> {
    if scale.denom().is_zero() {
        return Err(CertificateError::InvalidRationalValue);
    }
    if scale.is_zero() {
        return Err(CertificateError::SingularPivot);
    }
    let mut point = vec![BigRational::zero(); 32];
    point[1] = scale.clone();
    point[10] = scale;
    Ok(point)
}

#[cfg(test)]
mod tests {
    use super::*;
    use cd_kernel::cayley_dickson::cd_multiply;
    use num_traits::ToPrimitive;

    fn integer(value: i64) -> BigRational {
        BigRational::from_integer(value.into())
    }

    #[test]
    fn invalid_dimensions_and_zero_have_explicit_behavior() {
        for dimension in [0, 3, 15] {
            assert_eq!(
                annihilator_certificate(&vec![integer(0); dimension], MultiplicationSide::Left),
                Err(CertificateError::InvalidDimension(dimension))
            );
        }
        let zero = vec![integer(0); 16];
        let certificate = annihilator_certificate(&zero, MultiplicationSide::Left).unwrap();
        assert_eq!((certificate.rank(), certificate.nullity()), (0, 16));
        assert!(certificate.verify(&zero, MultiplicationSide::Left));
        assert_eq!(certificate.block_normalized_matrix(), None);
        assert_eq!(certificate.scaling.unit_input_block_alpha_squared, None);
    }

    #[test]
    fn malformed_rationals_fail_before_arithmetic_or_certificate_comparison() {
        let base = a5_scalar_orbit_point(integer(1)).unwrap();
        let chart = ConstantRankChart::at(&base, MultiplicationSide::Left).unwrap();
        let certificate = annihilator_certificate(&base, MultiplicationSide::Left).unwrap();
        for numerator in [0, 1] {
            let invalid = BigRational::new_raw(numerator.into(), 0.into());
            let mut input = base.clone();
            input[0] = invalid.clone();
            assert_eq!(
                multiplication_matrix_exact(&input, MultiplicationSide::Left),
                Err(CertificateError::InvalidRationalValue)
            );
            assert_eq!(
                annihilator_certificate(&input, MultiplicationSide::Left),
                Err(CertificateError::InvalidRationalValue)
            );
            assert_eq!(
                OperatorScaling::for_input(&input),
                Err(CertificateError::InvalidRationalValue)
            );
            assert_eq!(
                chart.certify(&input),
                Err(CertificateError::InvalidRationalValue)
            );
            assert_eq!(
                a5_scalar_orbit_point(invalid.clone()),
                Err(CertificateError::InvalidRationalValue)
            );
            assert!(!certificate.verify(&input, MultiplicationSide::Left));
            let mut damaged = certificate.clone();
            damaged.matrix[(0, 0)] = invalid.clone();
            assert!(!damaged.verify(&base, MultiplicationSide::Left));
            assert!(!damaged.kernel_span_equals(&certificate.kernel_basis));
            assert_eq!(damaged.block_normalized_matrix(), None);
            damaged = certificate.clone();
            damaged.kernel_basis[(0, 0)] = invalid.clone();
            assert!(!damaged.verify(&base, MultiplicationSide::Left));
            assert!(!certificate.kernel_span_equals(&damaged.kernel_basis));
            damaged = certificate.clone();
            damaged.pivot_minor_determinant = invalid.clone();
            assert!(!damaged.verify(&base, MultiplicationSide::Left));
            damaged = certificate.clone();
            damaged.scaling.block_encoding_alpha = invalid;
            assert!(!damaged.verify(&base, MultiplicationSide::Left));
            assert_eq!(damaged.block_normalized_matrix(), None);
        }
        let raw_unit = BigRational::new_raw((-2).into(), (-2).into());
        let raw_input = a5_scalar_orbit_point(raw_unit).unwrap();
        assert!(
            annihilator_certificate(&raw_input, MultiplicationSide::Left)
                .unwrap()
                .verify(&base, MultiplicationSide::Left)
        );
    }

    #[test]
    fn exact_matrices_match_recursive_multiplication_in_both_orders() {
        for dimension in [1, 2, 4, 8, 16, 32] {
            let coordinates: Vec<_> = (0..dimension)
                .map(|index| integer(index as i64 % 7 - 3))
                .collect();
            let floats: Vec<_> = coordinates
                .iter()
                .map(|value| value.to_f64().unwrap())
                .collect();
            for side in [MultiplicationSide::Left, MultiplicationSide::Right] {
                let matrix = multiplication_matrix_exact(&coordinates, side).unwrap();
                for column in 0..dimension {
                    let mut basis = vec![0.0; dimension];
                    basis[column] = 1.0;
                    let expected = match side {
                        MultiplicationSide::Left => cd_multiply(&floats, &basis),
                        MultiplicationSide::Right => cd_multiply(&basis, &floats),
                    };
                    for row in 0..dimension {
                        assert_eq!(matrix[(row, column)].to_f64().unwrap(), expected[row]);
                    }
                }
            }
        }
    }

    #[test]
    fn all_84_assessor_diagonals_have_certified_rank_twelve() {
        for assessor in crate::boxkites::primitive_assessors() {
            for sign in [-1, 1] {
                let mut input = vec![integer(0); 16];
                input[assessor.low] = integer(1);
                input[assessor.high] = integer(sign);
                let factor = crate::reggiani::StandardZeroDivisor {
                    assessor_low: assessor.low,
                    assessor_high: assessor.high,
                    diagonal_sign: sign as i32,
                    vector: input.iter().map(|value| value.to_f64().unwrap()).collect(),
                };
                let partners = crate::reggiani::standard_zero_divisor_partners(&factor);
                let partner_matrix = ExactMatrix::from_fn(16, partners.len(), |row, column| {
                    if row == partners[column].assessor_low {
                        integer(1)
                    } else if row == partners[column].assessor_high {
                        integer(i64::from(partners[column].diagonal_sign))
                    } else {
                        integer(0)
                    }
                });
                for side in [MultiplicationSide::Left, MultiplicationSide::Right] {
                    let certificate = annihilator_certificate(&input, side).unwrap();
                    assert_eq!((certificate.rank(), certificate.nullity()), (12, 4));
                    assert!(determinant(&certificate.matrix).is_zero());
                    assert!(certificate.verify(&input, side));
                    assert!(certificate.kernel_span_equals(&partner_matrix));
                }
            }
        }
    }

    #[test]
    fn invalid_sedenion_predicate_fixtures_are_invertible() {
        for first_basis in [0, 1] {
            let mut input = vec![integer(0); 16];
            input[first_basis] = integer(1);
            input[9] = integer(1);
            let certificate = annihilator_certificate(&input, MultiplicationSide::Left).unwrap();
            assert_eq!(certificate.rank(), 16);
            assert_eq!(certificate.pivot_minor_determinant, integer(256));
            assert!(certificate.verify(&input, MultiplicationSide::Left));
            let square = &certificate.matrix * &certificate.matrix;
            let negative_two_identity = ExactMatrix::identity(16, 16) * integer(-2);
            if first_basis == 1 {
                assert_eq!(square, negative_two_identity);
            } else {
                assert_ne!(square, negative_two_identity);
                assert!(!square[(9, 0)].is_zero());
            }
        }
    }

    #[test]
    fn certificate_mutations_fail_and_scaling_is_explicit() {
        let mut input = vec![integer(0); 16];
        input[1] = integer(1);
        input[10] = integer(1);
        let certificate = annihilator_certificate(&input, MultiplicationSide::Left).unwrap();
        assert_eq!(certificate.scaling.input_norm_squared, integer(2));
        assert_eq!(certificate.scaling.block_encoding_alpha, integer(2));
        assert_eq!(
            certificate.scaling.unit_input_block_alpha_squared,
            Some(integer(2))
        );
        let normalized = certificate.block_normalized_matrix().unwrap();
        assert_eq!(normalized * integer(2), certificate.matrix);
        assert!(certificate.kernel_span_equals(&certificate.kernel_basis));
        let incomplete_partners = certificate.kernel_basis.columns(0, 3).into_owned();
        assert!(!certificate.kernel_span_equals(&incomplete_partners));
        assert!(!certificate.kernel_span_equals(&ExactMatrix::zeros(15, 4)));
        let mut damaged = certificate.clone();
        damaged.kernel_basis[(0, 0)] += integer(1);
        assert!(!damaged.verify(&input, MultiplicationSide::Left));
        damaged = certificate.clone();
        damaged.pivot_minor_determinant += integer(1);
        assert!(!damaged.verify(&input, MultiplicationSide::Left));
        damaged = certificate;
        damaged.pivot_rows[0] = 16;
        assert!(!damaged.verify(&input, MultiplicationSide::Left));
    }

    #[test]
    fn a5_chart_admits_scalar_domain_and_detects_rank_boundaries() {
        let base = a5_scalar_orbit_point(integer(1)).unwrap();
        let chart = ConstantRankChart::at(&base, MultiplicationSide::Left).unwrap();
        assert_eq!(chart.pivot_columns.len(), 24);
        let base_certificate = chart.certify(&base).unwrap();
        for scale in [
            integer(-3),
            integer(2),
            BigRational::new(2.into(), 7.into()),
        ] {
            let point = a5_scalar_orbit_point(scale.clone()).unwrap();
            let certificate = chart.certify(&point).unwrap();
            assert_eq!(certificate.kernel_frame, base_certificate.kernel_frame);
            assert_eq!(
                certificate.pivot_determinant,
                &base_certificate.pivot_determinant * scale.pow(24)
            );
            assert!(certificate.schur_complement.iter().all(Zero::is_zero));
            let matrix = multiplication_matrix_exact(&point, MultiplicationSide::Left).unwrap();
            assert!(
                (matrix * certificate.kernel_frame)
                    .iter()
                    .all(Zero::is_zero)
            );
        }
        assert_eq!(
            chart.certify(&vec![integer(0); 32]),
            Err(CertificateError::SingularPivot)
        );
        let mut rank_jump = base;
        rank_jump[0] = integer(1);
        let certificate = annihilator_certificate(&rank_jump, MultiplicationSide::Left).unwrap();
        assert_eq!(certificate.rank(), 32);
        assert_eq!(
            chart.certify(&rank_jump),
            Err(CertificateError::NonzeroSchurComplement)
        );
    }

    #[test]
    fn chart_rejects_invalid_pivot_domains() {
        let point = a5_scalar_orbit_point(integer(1)).unwrap();
        let chart = ConstantRankChart::at(&point, MultiplicationSide::Left).unwrap();
        assert_eq!(
            chart.certify(&point[..16]),
            Err(CertificateError::InvalidDimension(16))
        );
        let mut invalid = chart.clone();
        invalid.pivot_rows[0] = 32;
        assert_eq!(
            invalid.certify(&point),
            Err(CertificateError::InvalidPivotIndices)
        );
        invalid = chart.clone();
        invalid.pivot_columns[0] = invalid.pivot_columns[1];
        assert_eq!(
            invalid.certify(&point),
            Err(CertificateError::InvalidPivotIndices)
        );
        invalid = chart;
        invalid.pivot_columns.pop();
        assert_eq!(
            invalid.certify(&point),
            Err(CertificateError::InvalidPivotIndices)
        );
    }
}
