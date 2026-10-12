// SPDX-License-Identifier: GPL-2.0-or-later
//! Exact centered skew-Schur acceleration certificates in dimension 32.
//!
//! The real adjoint identity in Biss--Christensen--Dugger--Isaksen, Lemma
//! 2.3, makes pure left multiplication skew-symmetric. At a doubly-pure
//! center, `S(x) = D(x) + B(x)^T A(x)^-1 B(x)` describes the fixed-nullity
//! locus in the invertible pivot domain. Its first two derivatives and a
//! constant-norm sphere give necessary acceleration equations. A compatible
//! certificate establishes a full affine solution space for those equations;
//! curve existence and smoothness require independent arguments.

use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::exact_annihilator::{
    AnnihilatorCertificate, ExactMatrix, MultiplicationSide, annihilator_certificate, determinant,
    multiplication_matrix_exact, row_reduce, valid_rational_matrix,
};

pub const SCHUR_DIMENSION: usize = 32;
const COEFFICIENT_COUNT: usize = SCHUR_DIMENSION - 2;
const CENTER_NULLITIES: [usize; 4] = [4, 8, 12, 16];

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchurAccelerationError {
    InvalidDimension(usize),
    InvalidRationalValue,
    NonDoublyPureCoordinates,
    ZeroCenter,
    UnsupportedNullity(usize),
    InvalidChart,
    SingularPivot,
    InvalidCertificate,
    InvalidParameterCount(usize),
}

impl std::fmt::Display for SchurAccelerationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for SchurAccelerationError {}

fn valid_values(values: &[BigRational]) -> bool {
    values.iter().all(|value| !value.denom().is_zero())
}

fn validate_coordinates(
    values: &[BigRational],
    allow_zero: bool,
) -> Result<(), SchurAccelerationError> {
    if values.len() != SCHUR_DIMENSION {
        return Err(SchurAccelerationError::InvalidDimension(values.len()));
    }
    if !valid_values(values) {
        return Err(SchurAccelerationError::InvalidRationalValue);
    }
    if !values[0].is_zero() || !values[SCHUR_DIMENSION / 2].is_zero() {
        return Err(SchurAccelerationError::NonDoublyPureCoordinates);
    }
    if !allow_zero && values.iter().all(Zero::is_zero) {
        return Err(SchurAccelerationError::ZeroCenter);
    }
    Ok(())
}

fn coordinate_indices() -> Vec<usize> {
    (1..SCHUR_DIMENSION)
        .filter(|&index| index != SCHUR_DIMENSION / 2)
        .collect()
}

fn upper_triangle(dimension: usize) -> Vec<(usize, usize)> {
    (0..dimension)
        .flat_map(|row| (row + 1..dimension).map(move |column| (row, column)))
        .collect()
}

fn matrix_shape(matrix: &ExactMatrix, rows: usize, columns: usize) -> bool {
    matrix.nrows() == rows && matrix.ncols() == columns && valid_rational_matrix(matrix)
}

fn vector_shape(values: &[BigRational], size: usize) -> bool {
    values.len() == size && valid_values(values)
}

fn zero_matrix(matrix: &ExactMatrix) -> bool {
    matrix.iter().all(Zero::is_zero)
}

fn vector(values: &[BigRational]) -> ExactMatrix {
    ExactMatrix::from_column_slice(values.len(), 1, values)
}

fn values(matrix: &ExactMatrix) -> Vec<BigRational> {
    matrix.iter().cloned().collect()
}

fn dot(left: &[BigRational], right: &[BigRational]) -> BigRational {
    left.iter()
        .zip(right)
        .map(|(left, right)| left * right)
        .sum()
}

fn select(matrix: &ExactMatrix, rows: &[usize], columns: &[usize]) -> ExactMatrix {
    ExactMatrix::from_fn(rows.len(), columns.len(), |row, column| {
        matrix[(rows[row], columns[column])].clone()
    })
}

fn valid_indices(indices: &[usize], dimension: usize) -> bool {
    indices.iter().all(|&index| index < dimension)
        && indices
            .iter()
            .enumerate()
            .all(|(position, index)| !indices[..position].contains(index))
}

fn homogeneous_kernel(matrix: &ExactMatrix) -> (ExactMatrix, Vec<usize>) {
    let (reduced, pivots) = row_reduce(matrix);
    let free = (0..matrix.ncols())
        .filter(|index| !pivots.contains(index))
        .collect::<Vec<_>>();
    let mut kernel = ExactMatrix::zeros(matrix.ncols(), free.len());
    for (position, &column) in free.iter().enumerate() {
        kernel[(column, position)] = BigRational::one();
        for (row, &pivot) in pivots.iter().enumerate() {
            kernel[(pivot, position)] = -&reduced[(row, column)];
        }
    }
    (kernel, pivots)
}

fn particular(matrix: &ExactMatrix, rhs: &[BigRational]) -> Option<Vec<BigRational>> {
    let augmented = ExactMatrix::from_fn(matrix.nrows(), matrix.ncols() + 1, |row, column| {
        if column == matrix.ncols() {
            rhs[row].clone()
        } else {
            matrix[(row, column)].clone()
        }
    });
    let (reduced, pivots) = row_reduce(&augmented);
    if pivots.contains(&matrix.ncols()) {
        return None;
    }
    let mut result = vec![BigRational::zero(); matrix.ncols()];
    for (row, &column) in pivots.iter().enumerate() {
        result[column] = reduced[(row, matrix.ncols())].clone();
    }
    Some(result)
}

fn inverse(matrix: &ExactMatrix) -> Option<ExactMatrix> {
    let dimension = matrix.nrows();
    let augmented = ExactMatrix::from_fn(dimension, 2 * dimension, |row, column| {
        if column < dimension {
            matrix[(row, column)].clone()
        } else {
            BigRational::from_integer(usize::from(row == column - dimension).into())
        }
    });
    let (reduced, pivots) = row_reduce(&augmented);
    if pivots != (0..dimension).collect::<Vec<_>>() {
        return None;
    }
    Some(reduced.columns(dimension, dimension).into_owned())
}

fn ambient(coefficients: &[BigRational]) -> Vec<BigRational> {
    let mut result = vec![BigRational::zero(); SCHUR_DIMENSION];
    for (coordinate, value) in coordinate_indices().into_iter().zip(coefficients) {
        result[coordinate] = value.clone();
    }
    result
}

/// A complete kernel and independent image columns give a centered skew frame.
/// The inverse pivot witnesses the local chart domain without a unit-norm
/// normalization, which could introduce irrational center coordinates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CenteredSchurChart {
    pub center: Vec<BigRational>,
    pub center_certificate: AnnihilatorCertificate,
    pub complement: ExactMatrix,
    pub kernel: ExactMatrix,
    pub center_pivot: ExactMatrix,
    pub center_pivot_inverse: ExactMatrix,
}

impl CenteredSchurChart {
    pub fn new(center: &[BigRational]) -> Result<Self, SchurAccelerationError> {
        validate_coordinates(center, false)?;
        let certificate = annihilator_certificate(center, MultiplicationSide::Left)
            .map_err(|_| SchurAccelerationError::InvalidRationalValue)?;
        if !CENTER_NULLITIES.contains(&certificate.nullity()) {
            return Err(SchurAccelerationError::UnsupportedNullity(
                certificate.nullity(),
            ));
        }
        let complement = select(
            &certificate.matrix,
            &(0..SCHUR_DIMENSION).collect::<Vec<_>>(),
            &certificate.pivot_columns,
        );
        let pivot = complement.transpose() * &certificate.matrix * &complement;
        let pivot_inverse = inverse(&pivot).ok_or(SchurAccelerationError::SingularPivot)?;
        let chart = Self {
            center: center.to_vec(),
            kernel: certificate.kernel_basis.clone(),
            center_certificate: certificate,
            complement,
            center_pivot: pivot,
            center_pivot_inverse: pivot_inverse,
        };
        if !chart.verify() {
            return Err(SchurAccelerationError::InvalidChart);
        }
        Ok(chart)
    }

    pub fn nullity(&self) -> usize {
        self.center_certificate.nullity()
    }

    /// Validate the source operator, both frame spaces, and both inverse laws.
    /// Orthogonal complete kernel columns and an invertible image pivot make
    /// the combined frame invertible over both the rationals and the reals.
    pub fn verify(&self) -> bool {
        if validate_coordinates(&self.center, false).is_err()
            || !self
                .center_certificate
                .verify(&self.center, MultiplicationSide::Left)
        {
            return false;
        }
        let nullity = self.nullity();
        if !CENTER_NULLITIES.contains(&nullity) {
            return false;
        }
        let rank = SCHUR_DIMENSION - nullity;
        if !matrix_shape(&self.complement, SCHUR_DIMENSION, rank)
            || !matrix_shape(&self.kernel, SCHUR_DIMENSION, nullity)
            || !matrix_shape(&self.center_pivot, rank, rank)
            || !matrix_shape(&self.center_pivot_inverse, rank, rank)
        {
            return false;
        }
        let operator = &self.center_certificate.matrix;
        let complement = select(
            operator,
            &(0..SCHUR_DIMENSION).collect::<Vec<_>>(),
            &self.center_certificate.pivot_columns,
        );
        self.complement == complement
            && self.kernel == self.center_certificate.kernel_basis
            && zero_matrix(&(operator + operator.transpose()))
            && zero_matrix(&(operator * &self.kernel))
            && zero_matrix(&(self.complement.transpose() * &self.kernel))
            && self.center_pivot == self.complement.transpose() * operator * &self.complement
            && &self.center_pivot * &self.center_pivot_inverse == ExactMatrix::identity(rank, rank)
            && &self.center_pivot_inverse * &self.center_pivot == ExactMatrix::identity(rank, rank)
    }

    pub fn linearized(&self) -> Result<LinearizedSchurConstraint, SchurAccelerationError> {
        if !self.verify() {
            return Err(SchurAccelerationError::InvalidChart);
        }
        Ok(derivative(self))
    }

    /// Evaluate the fixed chart only after checking its invertible pivot.
    /// A zero Schur residual establishes the center's nullity on that domain.
    pub fn schur_at(
        &self,
        coordinates: &[BigRational],
    ) -> Result<ExactMatrix, SchurAccelerationError> {
        validate_coordinates(coordinates, false)?;
        if !self.verify() {
            return Err(SchurAccelerationError::InvalidChart);
        }
        let operator = multiplication_matrix_exact(coordinates, MultiplicationSide::Left)
            .map_err(|_| SchurAccelerationError::InvalidRationalValue)?;
        let pivot = self.complement.transpose() * &operator * &self.complement;
        let pivot_inverse = inverse(&pivot).ok_or(SchurAccelerationError::SingularPivot)?;
        let cross = self.complement.transpose() * &operator * &self.kernel;
        let diagonal = self.kernel.transpose() * operator * &self.kernel;
        Ok(diagonal + cross.transpose() * pivot_inverse * cross)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearizedSchurConstraint {
    pub coordinate_indices: Vec<usize>,
    pub upper_triangle_indices: Vec<(usize, usize)>,
    pub direction_matrices: Vec<ExactMatrix>,
    pub coefficient_matrix: ExactMatrix,
    pub center_coefficients: Vec<BigRational>,
    pub rank: usize,
    pub kernel_basis: ExactMatrix,
    pub sphere_kernel_basis: ExactMatrix,
}

fn sphere_system(derivative: &ExactMatrix, center: &[BigRational]) -> ExactMatrix {
    ExactMatrix::from_fn(derivative.nrows() + 1, COEFFICIENT_COUNT, |row, column| {
        if row == derivative.nrows() {
            center[column].clone()
        } else {
            derivative[(row, column)].clone()
        }
    })
}

fn derivative(chart: &CenteredSchurChart) -> LinearizedSchurConstraint {
    let indices = coordinate_indices();
    let entries = upper_triangle(chart.nullity());
    let directions = indices
        .iter()
        .map(|&index| {
            let mut coefficients = vec![BigRational::zero(); SCHUR_DIMENSION];
            coefficients[index] = BigRational::one();
            let operator = multiplication_matrix_exact(&coefficients, MultiplicationSide::Left)
                .expect("validated basis coordinates have exact multiplication matrices");
            chart.kernel.transpose() * operator * &chart.kernel
        })
        .collect::<Vec<_>>();
    let coefficient_matrix =
        ExactMatrix::from_fn(entries.len(), COEFFICIENT_COUNT, |row, column| {
            directions[column][entries[row]].clone()
        });
    let center_coefficients = indices
        .iter()
        .map(|&index| chart.center[index].clone())
        .collect::<Vec<_>>();
    let (kernel_basis, pivots) = homogeneous_kernel(&coefficient_matrix);
    let (sphere_kernel_basis, _) =
        homogeneous_kernel(&sphere_system(&coefficient_matrix, &center_coefficients));
    LinearizedSchurConstraint {
        coordinate_indices: indices,
        upper_triangle_indices: entries,
        direction_matrices: directions,
        coefficient_matrix,
        center_coefficients,
        rank: pivots.len(),
        kernel_basis,
        sphere_kernel_basis,
    }
}

impl LinearizedSchurConstraint {
    fn has_valid_shapes(&self, nullity: usize) -> bool {
        let rows = nullity * (nullity - 1) / 2;
        self.rank < COEFFICIENT_COUNT
            && self.coordinate_indices == coordinate_indices()
            && self.upper_triangle_indices == upper_triangle(nullity)
            && self.direction_matrices.len() == COEFFICIENT_COUNT
            && self
                .direction_matrices
                .iter()
                .all(|matrix| matrix_shape(matrix, nullity, nullity))
            && matrix_shape(&self.coefficient_matrix, rows, COEFFICIENT_COUNT)
            && vector_shape(&self.center_coefficients, COEFFICIENT_COUNT)
            && matrix_shape(
                &self.kernel_basis,
                COEFFICIENT_COUNT,
                COEFFICIENT_COUNT - self.rank,
            )
            && matrix_shape(
                &self.sphere_kernel_basis,
                COEFFICIENT_COUNT,
                COEFFICIENT_COUNT - self.rank - 1,
            )
    }

    pub fn verify(&self, chart: &CenteredSchurChart) -> bool {
        chart.verify() && self.has_valid_shapes(chart.nullity()) && *self == derivative(chart)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccelerationStatus {
    FirstOrderInadmissible,
    SecondOrderObstructed,
    SecondOrderCompatible,
}

/// Every acceleration is `particular + kernel_basis * parameters`.
/// A nonzero rank minor and independent free rows prove completeness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AffineAccelerationSpace {
    pub schur_particular: Vec<BigRational>,
    pub radial_correction: BigRational,
    pub particular: Vec<BigRational>,
    pub kernel_basis: ExactMatrix,
    pub rank: usize,
    pub pivot_rows: Vec<usize>,
    pub pivot_columns: Vec<usize>,
    pub pivot_determinant: BigRational,
}

/// A nonzero pairing with a left-kernel covector excludes every acceleration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AccelerationObstruction {
    pub covector: Vec<BigRational>,
    pub pairing: BigRational,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchurAccelerationCertificate {
    pub chart: CenteredSchurChart,
    pub direction: Vec<BigRational>,
    pub linearized: LinearizedSchurConstraint,
    pub direction_cross: ExactMatrix,
    pub first_schur_derivative: ExactMatrix,
    pub quadratic_term: ExactMatrix,
    pub system_matrix: ExactMatrix,
    pub system_rhs: Vec<BigRational>,
    pub first_order_residual: Vec<BigRational>,
    pub status: AccelerationStatus,
    pub affine_space: Option<AffineAccelerationSpace>,
    pub obstruction: Option<AccelerationObstruction>,
}

struct DirectionEquations {
    cross: ExactMatrix,
    diagonal: ExactMatrix,
    quadratic: ExactMatrix,
    system: ExactMatrix,
    rhs: Vec<BigRational>,
    first_order: Vec<BigRational>,
}

fn equations(
    chart: &CenteredSchurChart,
    direction: &[BigRational],
    linearized: &LinearizedSchurConstraint,
) -> DirectionEquations {
    let operator = multiplication_matrix_exact(direction, MultiplicationSide::Left)
        .expect("validated direction coordinates have exact multiplication matrices");
    let cross = chart.complement.transpose() * &operator * &chart.kernel;
    let diagonal = chart.kernel.transpose() * operator * &chart.kernel;
    let quadratic = cross.transpose() * &chart.center_pivot_inverse * &cross;
    let system = sphere_system(
        &linearized.coefficient_matrix,
        &linearized.center_coefficients,
    );
    let two = BigRational::from_integer(2.into());
    let mut rhs = linearized
        .upper_triangle_indices
        .iter()
        .map(|&entry| -&two * &quadratic[entry])
        .collect::<Vec<_>>();
    rhs.push(-dot(direction, direction));
    // Direct operator residuals also verify the coordinate derivative map.
    let mut first_order = linearized
        .upper_triangle_indices
        .iter()
        .map(|&entry| diagonal[entry].clone())
        .collect::<Vec<_>>();
    first_order.push(dot(&chart.center, direction));
    DirectionEquations {
        cross,
        diagonal,
        quadratic,
        system,
        rhs,
        first_order,
    }
}

pub fn certify_schur_acceleration(
    chart: &CenteredSchurChart,
    direction: &[BigRational],
) -> Result<SchurAccelerationCertificate, SchurAccelerationError> {
    validate_coordinates(direction, true)?;
    if !chart.verify() {
        return Err(SchurAccelerationError::InvalidChart);
    }
    let linearized = derivative(chart);
    let data = equations(chart, direction, &linearized);
    let mut status = AccelerationStatus::FirstOrderInadmissible;
    let mut affine_space = None;
    let mut obstruction = None;
    if data.first_order.iter().all(Zero::is_zero) {
        let (left_kernel, _) = homogeneous_kernel(&data.system.transpose());
        for column in left_kernel.column_iter() {
            let covector = column.iter().cloned().collect::<Vec<_>>();
            let pairing = dot(&covector, &data.rhs);
            if !pairing.is_zero() {
                obstruction = Some(AccelerationObstruction { covector, pairing });
                break;
            }
        }
        if obstruction.is_some() {
            status = AccelerationStatus::SecondOrderObstructed;
        } else {
            status = AccelerationStatus::SecondOrderCompatible;
            let schur_particular = particular(
                &linearized.coefficient_matrix,
                &data.rhs[..data.rhs.len() - 1],
            )
            .ok_or(SchurAccelerationError::InvalidCertificate)?;
            let center = &linearized.center_coefficients;
            let radial_correction = (data
                .rhs
                .last()
                .expect("sphere equation supplies a final row")
                - dot(center, &schur_particular))
                / dot(center, center);
            let corrected = schur_particular
                .iter()
                .zip(center)
                .map(|(value, coordinate)| value + &radial_correction * coordinate)
                .collect();
            let (kernel_basis, columns) = homogeneous_kernel(&data.system);
            let rows = row_reduce(
                &select(
                    &data.system,
                    &(0..data.system.nrows()).collect::<Vec<_>>(),
                    &columns,
                )
                .transpose(),
            )
            .1;
            let minor = determinant(&select(&data.system, &rows, &columns));
            affine_space = Some(AffineAccelerationSpace {
                schur_particular,
                radial_correction,
                particular: corrected,
                kernel_basis,
                rank: columns.len(),
                pivot_rows: rows,
                pivot_columns: columns,
                pivot_determinant: minor,
            });
        }
    }
    let certificate = SchurAccelerationCertificate {
        chart: chart.clone(),
        direction: direction.to_vec(),
        linearized,
        direction_cross: data.cross,
        first_schur_derivative: data.diagonal,
        quadratic_term: data.quadratic,
        system_matrix: data.system,
        system_rhs: data.rhs,
        first_order_residual: data.first_order,
        status,
        affine_space,
        obstruction,
    };
    if !certificate.verify() {
        return Err(SchurAccelerationError::InvalidCertificate);
    }
    Ok(certificate)
}

fn verify_affine_space(
    space: &AffineAccelerationSpace,
    data: &DirectionEquations,
    linearized: &LinearizedSchurConstraint,
) -> bool {
    let rank = space.rank;
    if !(1..=COEFFICIENT_COUNT).contains(&rank)
        || rank != linearized.rank + 1
        || space.pivot_rows.len() != rank
        || space.pivot_columns.len() != rank
        || !valid_indices(&space.pivot_rows, data.system.nrows())
        || !valid_indices(&space.pivot_columns, COEFFICIENT_COUNT)
        || !vector_shape(&space.schur_particular, COEFFICIENT_COUNT)
        || !vector_shape(&space.particular, COEFFICIENT_COUNT)
        || !matrix_shape(
            &space.kernel_basis,
            COEFFICIENT_COUNT,
            COEFFICIENT_COUNT - rank,
        )
        || space.radial_correction.denom().is_zero()
        || space.pivot_determinant.denom().is_zero()
        || space.pivot_determinant.is_zero()
    {
        return false;
    }
    let free = (0..COEFFICIENT_COUNT)
        .filter(|index| !space.pivot_columns.contains(index))
        .collect::<Vec<_>>();
    let center = &linearized.center_coefficients;
    let correction = (&data.rhs[data.rhs.len() - 1] - dot(center, &space.schur_particular))
        / dot(center, center);
    let corrected = space
        .schur_particular
        .iter()
        .zip(center)
        .map(|(value, coordinate)| value + &correction * coordinate)
        .collect::<Vec<_>>();
    determinant(&select(
        &data.system,
        &space.pivot_rows,
        &space.pivot_columns,
    )) == space.pivot_determinant
        && select(
            &space.kernel_basis,
            &free,
            &(0..free.len()).collect::<Vec<_>>(),
        ) == ExactMatrix::identity(free.len(), free.len())
        && zero_matrix(&(&data.system * &space.kernel_basis))
        && &linearized.coefficient_matrix * vector(&space.schur_particular)
            == vector(&data.rhs[..data.rhs.len() - 1])
        && zero_matrix(&(&linearized.coefficient_matrix * vector(center)))
        && correction == space.radial_correction
        && corrected == space.particular
        && &data.system * vector(&space.particular) == vector(&data.rhs)
}

impl SchurAccelerationCertificate {
    /// Rebuild the source chart, all thirty derivative directions and direct
    /// residuals before checking witnesses. The verifier never calls the
    /// acceleration certificate constructor or trusts its retained status.
    pub fn verify(&self) -> bool {
        if validate_coordinates(&self.direction, true).is_err() || !self.chart.verify() {
            return false;
        }
        let nullity = self.chart.nullity();
        let rows = nullity * (nullity - 1) / 2 + 1;
        if !self.linearized.has_valid_shapes(nullity)
            || !matrix_shape(&self.direction_cross, SCHUR_DIMENSION - nullity, nullity)
            || !matrix_shape(&self.first_schur_derivative, nullity, nullity)
            || !matrix_shape(&self.quadratic_term, nullity, nullity)
            || !matrix_shape(&self.system_matrix, rows, COEFFICIENT_COUNT)
            || !vector_shape(&self.system_rhs, rows)
            || !vector_shape(&self.first_order_residual, rows)
        {
            return false;
        }
        let expected = derivative(&self.chart);
        if self.linearized != expected {
            return false;
        }
        let data = equations(&self.chart, &self.direction, &expected);
        if self.direction_cross != data.cross
            || self.first_schur_derivative != data.diagonal
            || self.quadratic_term != data.quadratic
            || !zero_matrix(&(&data.quadratic + data.quadratic.transpose()))
            || self.system_matrix != data.system
            || self.system_rhs != data.rhs
            || self.first_order_residual != data.first_order
        {
            return false;
        }
        if data.first_order.iter().any(|value| !value.is_zero()) {
            return self.status == AccelerationStatus::FirstOrderInadmissible
                && self.affine_space.is_none()
                && self.obstruction.is_none();
        }
        match self.status {
            AccelerationStatus::FirstOrderInadmissible => false,
            AccelerationStatus::SecondOrderObstructed => {
                let Some(obstruction) = &self.obstruction else {
                    return false;
                };
                self.affine_space.is_none()
                    && vector_shape(&obstruction.covector, data.system.nrows())
                    && !obstruction.pairing.denom().is_zero()
                    && !obstruction.pairing.is_zero()
                    && obstruction.covector.last().is_some_and(Zero::is_zero)
                    && zero_matrix(&(vector(&obstruction.covector).transpose() * &data.system))
                    && dot(&obstruction.covector, &data.rhs) == obstruction.pairing
            }
            AccelerationStatus::SecondOrderCompatible => {
                let Some(space) = &self.affine_space else {
                    return false;
                };
                if self.obstruction.is_some() || !verify_affine_space(space, &data, &expected) {
                    return false;
                }
                self.direct_member(&ambient(&space.particular), &data.quadratic)
            }
        }
    }

    fn direct_member(&self, acceleration: &[BigRational], quadratic: &ExactMatrix) -> bool {
        let Ok(operator) = multiplication_matrix_exact(acceleration, MultiplicationSide::Left)
        else {
            return false;
        };
        let two = BigRational::from_integer(2.into());
        zero_matrix(
            &(self.chart.kernel.transpose() * operator * &self.chart.kernel + quadratic * two),
        ) && dot(&self.chart.center, acceleration) == -dot(&self.direction, &self.direction)
    }

    pub fn verify_member(&self, acceleration: &[BigRational]) -> bool {
        validate_coordinates(acceleration, true).is_ok()
            && self.verify()
            && self.status == AccelerationStatus::SecondOrderCompatible
            && self.direct_member(acceleration, &self.quadratic_term)
    }

    /// Return all ambient coordinates, preserving the two purity constraints.
    pub fn acceleration(
        &self,
        parameters: &[BigRational],
    ) -> Result<Vec<BigRational>, SchurAccelerationError> {
        if !self.verify() || self.status != AccelerationStatus::SecondOrderCompatible {
            return Err(SchurAccelerationError::InvalidCertificate);
        }
        let space = self
            .affine_space
            .as_ref()
            .ok_or(SchurAccelerationError::InvalidCertificate)?;
        if parameters.len() != COEFFICIENT_COUNT - space.rank {
            return Err(SchurAccelerationError::InvalidParameterCount(
                parameters.len(),
            ));
        }
        if !valid_values(parameters) {
            return Err(SchurAccelerationError::InvalidRationalValue);
        }
        Ok(ambient(&values(
            &(vector(&space.particular) + &space.kernel_basis * vector(parameters)),
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact_annihilator::exact_rank;

    fn integer(value: i64) -> BigRational {
        BigRational::from_integer(value.into())
    }

    fn fraction(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(numerator.into(), denominator.into())
    }

    fn fixture(entries: &[(usize, BigRational)]) -> Vec<BigRational> {
        let mut result = vec![BigRational::zero(); SCHUR_DIMENSION];
        for (index, coefficient) in entries {
            result[*index] = coefficient.clone();
        }
        result
    }

    fn centers() -> Vec<(Vec<BigRational>, usize)> {
        vec![
            (
                fixture(&[
                    (1, integer(1)),
                    (10, fraction(1, 4)),
                    (18, fraction(5, 8)),
                    (25, fraction(1, 8)),
                ]),
                4,
            ),
            (fixture(&[(1, integer(1)), (10, integer(1))]), 8),
            (fixture(&[(1, integer(1)), (18, integer(1))]), 12),
            (
                fixture(&[
                    (1, integer(1)),
                    (10, integer(1)),
                    (18, integer(1)),
                    (25, integer(-1)),
                ]),
                16,
            ),
        ]
    }

    fn curved() -> SchurAccelerationCertificate {
        let center = fixture(&[(1, integer(1)), (10, integer(1))]);
        let chart = CenteredSchurChart::new(&center).unwrap();
        certify_schur_acceleration(&chart, &fixture(&[(3, integer(1))])).unwrap()
    }

    fn obstructed() -> SchurAccelerationCertificate {
        let center = fixture(&[(1, integer(1)), (18, integer(1))]);
        let chart = CenteredSchurChart::new(&center).unwrap();
        certify_schur_acceleration(&chart, &fixture(&[(11, integer(1))])).unwrap()
    }

    #[test]
    fn all_four_center_nullities_have_complete_frames_and_zero_acceleration_spaces() {
        for (center, expected_nullity) in centers() {
            let chart = CenteredSchurChart::new(&center).unwrap();
            assert_eq!(chart.nullity(), expected_nullity);
            assert!(chart.verify());
            assert!(zero_matrix(&chart.schur_at(&center).unwrap()));
            let derivative = chart.linearized().unwrap();
            assert!(derivative.verify(&chart));
            assert_eq!(derivative.coordinate_indices.len(), COEFFICIENT_COUNT);
            assert_eq!(derivative.direction_matrices.len(), COEFFICIENT_COUNT);
            assert_eq!(exact_rank(&derivative.coefficient_matrix), derivative.rank);
            assert!(zero_matrix(
                &(&derivative.coefficient_matrix * &derivative.kernel_basis)
            ));
            let zero = certify_schur_acceleration(&chart, &fixture(&[])).unwrap();
            assert_eq!(zero.status, AccelerationStatus::SecondOrderCompatible);
            let space = zero.affine_space.as_ref().unwrap();
            assert_eq!(space.rank, derivative.rank + 1);
            assert_eq!(space.kernel_basis.ncols(), COEFFICIENT_COUNT - space.rank);
            let parameters = (0..space.kernel_basis.ncols())
                .map(|index| BigRational::new((index + 1).into(), (index + 2).into()))
                .collect::<Vec<_>>();
            assert!(zero.verify_member(&zero.acceleration(&parameters).unwrap()));
            let radial = certify_schur_acceleration(&chart, &center).unwrap();
            assert_eq!(radial.status, AccelerationStatus::FirstOrderInadmissible);
            assert!(!radial.first_order_residual.last().unwrap().is_zero());
            assert!(radial.affine_space.is_none() && radial.obstruction.is_none());
        }
    }

    #[test]
    fn curved_e3_requires_transverse_acceleration_and_retains_all_twenty_three_parameters() {
        let certificate = curved();
        assert_eq!(
            certificate.status,
            AccelerationStatus::SecondOrderCompatible
        );
        let space = certificate.affine_space.as_ref().unwrap();
        assert_eq!(certificate.linearized.rank, 6);
        assert_eq!(space.rank, 7);
        assert_eq!(space.kernel_basis.ncols(), 23);
        assert!(certificate.verify_member(&fixture(&[(1, integer(-1))])));
        for invalid in [
            fixture(&[]),
            fixture(&[(1, integer(1))]),
            fixture(&[(1, fraction(-1, 2))]),
            fixture(&[(1, fraction(-1, 2)), (10, fraction(-1, 2))]),
        ] {
            assert!(!certificate.verify_member(&invalid));
        }
        assert_eq!(exact_rank(&certificate.quadratic_term), 8);
        let parameters = (0..23)
            .map(|index| fraction(index + 1, index + 2))
            .collect::<Vec<_>>();
        let acceleration = certificate.acceleration(&parameters).unwrap();
        assert!(certificate.verify_member(&acceleration));
        assert!(acceleration[0].is_zero() && acceleration[16].is_zero());
    }

    #[test]
    fn e11_has_a_nonzero_separator_even_after_the_independent_norm_row() {
        let certificate = obstructed();
        assert_eq!(
            certificate.status,
            AccelerationStatus::SecondOrderObstructed
        );
        assert_eq!(certificate.linearized.rank, 8);
        assert_eq!(certificate.linearized.sphere_kernel_basis.ncols(), 21);
        let entries = &certificate.linearized.upper_triangle_indices;
        let left = entries.iter().position(|&entry| entry == (0, 1)).unwrap();
        let right = entries.iter().position(|&entry| entry == (4, 5)).unwrap();
        assert_eq!(
            certificate.system_matrix.row(left),
            certificate.system_matrix.row(right)
        );
        assert_eq!(certificate.system_rhs[left], integer(2));
        assert_eq!(certificate.system_rhs[right], integer(-2));
        let mut covector = vec![BigRational::zero(); certificate.system_matrix.nrows()];
        covector[left] = integer(-1);
        covector[right] = integer(1);
        assert!(zero_matrix(
            &(vector(&covector).transpose() * &certificate.system_matrix)
        ));
        assert_eq!(dot(&covector, &certificate.system_rhs), integer(-4));
        let separator = certificate.obstruction.as_ref().unwrap();
        assert!(!separator.pairing.is_zero());
        assert!(separator.covector.last().unwrap().is_zero());
        assert!(!certificate.verify_member(&fixture(&[])));
        assert_eq!(
            certificate.acceleration(&[]),
            Err(SchurAccelerationError::InvalidCertificate)
        );
    }

    #[test]
    fn rational_curve_samples_retain_nullity_while_straight_samples_gain_rank() {
        let certificate = curved();
        for parameter in [fraction(-1, 2), fraction(1, 2), integer(1), integer(2)] {
            let squared = &parameter * &parameter;
            let denominator = integer(4) + &squared;
            let point = fixture(&[
                (1, (integer(4) - &squared) / &denominator),
                (3, integer(4) * &parameter / &denominator),
                (10, integer(1)),
            ]);
            assert_eq!(dot(&point, &point), integer(2));
            assert!(zero_matrix(&certificate.chart.schur_at(&point).unwrap()));
            let direct = annihilator_certificate(&point, MultiplicationSide::Left).unwrap();
            assert_eq!(direct.nullity(), 8);
            let straight = fixture(&[(1, integer(1)), (3, parameter.clone()), (10, integer(1))]);
            let residual = certificate.chart.schur_at(&straight).unwrap();
            assert_eq!(exact_rank(&residual), 8);
            assert_eq!(determinant(&residual), parameter.pow(16));
        }
        let outside = fixture(&[(1, integer(1)), (10, integer(-1))]);
        let outside_operator =
            multiplication_matrix_exact(&outside, MultiplicationSide::Left).unwrap();
        let outside_pivot = certificate.chart.complement.transpose()
            * outside_operator
            * &certificate.chart.complement;
        assert!(determinant(&outside_pivot).is_zero());
        assert_eq!(
            certificate.chart.schur_at(&outside),
            Err(SchurAccelerationError::SingularPivot)
        );
    }

    #[test]
    fn rational_direction_and_center_rescalings_follow_the_quadratic_laws() {
        let certificate = curved();
        for factor in [fraction(-3, 2), fraction(2, 3), integer(0)] {
            let scaled =
                certify_schur_acceleration(&certificate.chart, &fixture(&[(3, factor.clone())]))
                    .unwrap();
            assert_eq!(scaled.status, AccelerationStatus::SecondOrderCompatible);
            assert_eq!(
                scaled.quadratic_term,
                &certificate.quadratic_term * (&factor * &factor)
            );
            assert!(scaled.verify_member(&fixture(&[(1, -&factor * &factor)])));
        }
        for factor in [fraction(-3, 2), fraction(2, 3)] {
            let center = certificate
                .chart
                .center
                .iter()
                .map(|value| &factor * value)
                .collect::<Vec<_>>();
            let chart = CenteredSchurChart::new(&center).unwrap();
            let scaled = certify_schur_acceleration(&chart, &fixture(&[(3, integer(1))])).unwrap();
            assert_eq!(chart.nullity(), 8);
            assert_eq!(
                scaled.quadratic_term,
                certificate.quadratic_term.map(|value| value / &factor)
            );
            assert!(scaled.verify_member(&fixture(&[(1, -integer(1) / &factor)])));
        }
    }

    #[test]
    fn dense_first_order_kernel_vectors_have_independently_checked_statuses() {
        for (center, _) in centers() {
            let chart = CenteredSchurChart::new(&center).unwrap();
            let derivative = chart.linearized().unwrap();
            let parameters = (0..derivative.sphere_kernel_basis.ncols())
                .map(|index| BigRational::new((index + 1).into(), (index + 2).into()))
                .collect::<Vec<_>>();
            let direction = ambient(&values(
                &(&derivative.sphere_kernel_basis * vector(&parameters)),
            ));
            let certificate = certify_schur_acceleration(&chart, &direction).unwrap();
            assert_ne!(
                certificate.status,
                AccelerationStatus::FirstOrderInadmissible
            );
            assert!(certificate.first_order_residual.iter().all(Zero::is_zero));
            assert!(certificate.verify());
        }
    }

    #[test]
    fn chart_mutations_and_unsupported_centers_fail_before_direction_arithmetic() {
        let certificate = curved();
        for mutation in 0..10 {
            let mut chart = certificate.chart.clone();
            match mutation {
                0 => chart.center[1] += integer(1),
                1 => {
                    chart.center.pop();
                }
                2 => chart.complement[(0, 0)] += integer(1),
                3 => chart.kernel[(0, 0)] += integer(1),
                4 => chart.center_pivot[(0, 0)] += integer(1),
                5 => chart.center_pivot_inverse[(0, 0)] += integer(1),
                6 => chart.center_certificate.matrix[(0, 0)] += integer(1),
                7 => chart.center_certificate.pivot_columns[0] = SCHUR_DIMENSION,
                8 => chart.complement = ExactMatrix::zeros(1, 1),
                9 => chart.center_certificate.kernel_basis = ExactMatrix::zeros(1, 1),
                _ => unreachable!(),
            }
            assert!(!chart.verify(), "chart mutation {mutation}");
            assert_eq!(
                certify_schur_acceleration(&chart, &fixture(&[])),
                Err(SchurAccelerationError::InvalidChart)
            );
        }
        assert_eq!(
            CenteredSchurChart::new(&fixture(&[])),
            Err(SchurAccelerationError::ZeroCenter)
        );
        assert_eq!(
            CenteredSchurChart::new(&fixture(&[(1, integer(1))])),
            Err(SchurAccelerationError::UnsupportedNullity(0))
        );
        for length in [0, 4, 16, 31, 33, 64, 4096] {
            assert_eq!(
                CenteredSchurChart::new(&vec![integer(0); length]),
                Err(SchurAccelerationError::InvalidDimension(length))
            );
        }
    }

    #[test]
    fn every_retained_equation_field_rejects_an_exact_mutation() {
        let original = curved();
        for mutation in 0..19 {
            let mut certificate = original.clone();
            match mutation {
                0 => certificate.direction[3] += integer(1),
                1 => {
                    certificate.direction.pop();
                }
                2 => certificate.linearized.coordinate_indices[0] = 0,
                3 => certificate.linearized.upper_triangle_indices[0] = (0, 0),
                4 => certificate.linearized.direction_matrices[0][(0, 0)] += integer(1),
                5 => certificate.linearized.coefficient_matrix[(0, 0)] += integer(1),
                6 => certificate.linearized.center_coefficients[0] += integer(1),
                7 => certificate.linearized.rank += 1,
                8 => certificate.linearized.kernel_basis[(0, 0)] += integer(1),
                9 => certificate.linearized.sphere_kernel_basis[(0, 0)] += integer(1),
                10 => certificate.direction_cross[(0, 0)] += integer(1),
                11 => certificate.first_schur_derivative[(0, 0)] += integer(1),
                12 => certificate.quadratic_term[(0, 0)] += integer(1),
                13 => certificate.system_matrix[(0, 0)] += integer(1),
                14 => certificate.system_rhs[0] += integer(1),
                15 => certificate.first_order_residual[0] += integer(1),
                16 => certificate.affine_space = None,
                17 => certificate.status = AccelerationStatus::FirstOrderInadmissible,
                18 => {
                    certificate.obstruction = Some(AccelerationObstruction {
                        covector: vec![integer(0); certificate.system_matrix.nrows()],
                        pairing: integer(1),
                    })
                }
                _ => unreachable!(),
            }
            assert!(!certificate.verify(), "equation mutation {mutation}");
        }
    }

    #[test]
    fn incomplete_affine_frames_and_false_radial_corrections_are_rejected() {
        let original = curved();
        for mutation in 0..14 {
            let mut certificate = original.clone();
            let space = certificate.affine_space.as_mut().unwrap();
            match mutation {
                0 => space.schur_particular[0] += integer(1),
                1 => space.radial_correction += integer(1),
                2 => space.particular[0] += integer(1),
                3 => space.kernel_basis[(0, 0)] += integer(1),
                4 => space.kernel_basis = space.kernel_basis.columns(0, 22).into_owned(),
                5 => space.rank += 1,
                6 => space.rank = usize::MAX,
                7 => space.pivot_rows[0] = space.pivot_rows[1],
                8 => space.pivot_columns[0] = space.pivot_columns[1],
                9 => space.pivot_rows[0] = certificate.system_matrix.nrows(),
                10 => space.pivot_columns[0] = COEFFICIENT_COUNT,
                11 => space.pivot_determinant += integer(1),
                12 => space.pivot_determinant = integer(0),
                13 => {
                    space.particular.pop();
                }
                _ => unreachable!(),
            }
            assert!(!certificate.verify(), "affine mutation {mutation}");
        }
    }

    #[test]
    fn damaged_separators_and_status_reassignment_fail_closed() {
        let original = obstructed();
        for mutation in 0..7 {
            let mut certificate = original.clone();
            let separator = certificate.obstruction.as_mut().unwrap();
            match mutation {
                0 => separator.covector.fill(integer(0)),
                1 => {
                    separator.covector.pop();
                }
                2 => separator.covector[0] += integer(1),
                3 => separator.pairing += integer(1),
                4 => separator.pairing = integer(0),
                5 => *separator.covector.last_mut().unwrap() = integer(1),
                6 => certificate.status = AccelerationStatus::SecondOrderCompatible,
                _ => unreachable!(),
            }
            assert!(!certificate.verify(), "separator mutation {mutation}");
        }
        let mut missing = original;
        missing.obstruction = None;
        assert!(!missing.verify());
        let curved = curved();
        let mut radial = certify_schur_acceleration(&curved.chart, &curved.chart.center).unwrap();
        radial.status = AccelerationStatus::SecondOrderCompatible;
        radial.affine_space = curved.affine_space;
        assert!(!radial.verify());
    }

    #[test]
    fn malformed_rationals_purity_and_parameter_shapes_receive_explicit_rejection() {
        let original = curved();
        for coordinate in [0, SCHUR_DIMENSION / 2] {
            let direction = fixture(&[(coordinate, integer(1))]);
            assert_eq!(
                certify_schur_acceleration(&original.chart, &direction),
                Err(SchurAccelerationError::NonDoublyPureCoordinates)
            );
            assert!(!original.verify_member(&direction));
        }
        assert_eq!(
            certify_schur_acceleration(&original.chart, &vec![integer(0); 31]),
            Err(SchurAccelerationError::InvalidDimension(31))
        );
        assert_eq!(
            original.acceleration(&[]),
            Err(SchurAccelerationError::InvalidParameterCount(0))
        );
        let invalid = BigRational::new_raw(1.into(), 0.into());
        let mut direction = fixture(&[]);
        direction[3] = invalid.clone();
        assert_eq!(
            certify_schur_acceleration(&original.chart, &direction),
            Err(SchurAccelerationError::InvalidRationalValue)
        );
        assert!(!original.verify_member(&direction));
        let mut parameters = vec![integer(0); 23];
        parameters[0] = invalid.clone();
        assert_eq!(
            original.acceleration(&parameters),
            Err(SchurAccelerationError::InvalidRationalValue)
        );
        for mutation in 0..10 {
            let mut certificate = original.clone();
            match mutation {
                0 => certificate.direction[3] = invalid.clone(),
                1 => certificate.chart.center[1] = invalid.clone(),
                2 => certificate.linearized.direction_matrices[0][(0, 0)] = invalid.clone(),
                3 => certificate.direction_cross[(0, 0)] = invalid.clone(),
                4 => certificate.quadratic_term[(0, 0)] = invalid.clone(),
                5 => certificate.system_rhs[0] = invalid.clone(),
                6 => certificate.first_order_residual[0] = invalid.clone(),
                7 => certificate.affine_space.as_mut().unwrap().radial_correction = invalid.clone(),
                8 => {
                    certificate.affine_space.as_mut().unwrap().kernel_basis[(0, 0)] =
                        invalid.clone()
                }
                9 => certificate.affine_space.as_mut().unwrap().pivot_determinant = invalid.clone(),
                _ => unreachable!(),
            }
            assert!(
                !certificate.verify(),
                "malformed rational mutation {mutation}"
            );
        }
    }
}
