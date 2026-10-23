"""Exact local skew-Schur charts for dimension-32 Cayley-Dickson elements.

A verified nonzero doubly-pure zero divisor supplies a fixed complement and
kernel. Every rational point in its invertible pivot domain admits an exact
reduction, including points with a nonzero residual and zero-dimensional
kernel. The residual certificate, congruence and lift certify the full rank.
The polynomial contract applies to real coefficients; finite evaluations
supply regression evidence rather than a global rank-locus classification.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Any

import sympy as sp

import parallel
from rank_charts import (
    RankCertificate,
    RationalMatrix,
    multiplication_matrix,
    rank_certificate,
    verify_rank_certificate,
)

DIMENSION = 32
COORDINATE_INDICES = tuple(index for index in range(DIMENSION) if index not in (0, 16))
CENTER_NULLITIES = (4, 8, 12, 16)


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def _rational(value: object) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise ValueError("coordinates require exact integers or Fractions")
    return Fraction(value)


def _coordinates(values: Sequence[int | Fraction], *, allow_zero: bool = False) -> tuple[Fraction, ...]:
    if isinstance(values, (str, bytes)) or not isinstance(values, Sequence) or len(values) != DIMENSION:
        raise ValueError("coordinates require 32 exact rational entries")
    result = tuple(_rational(value) for value in values)
    if result[0] or result[16]:
        raise ValueError("doubly-pure coordinates require entries 0 and 16 to vanish")
    if not allow_zero and not any(result):
        raise ValueError("the origin is outside the nonzero chart domain")
    return result


def _fraction(value: sp.Expr) -> Fraction:
    return Fraction(int(value.p), int(value.q))


def _rows(matrix: sp.Matrix) -> RationalMatrix:
    return tuple(tuple(_fraction(matrix[row, column]) for column in range(matrix.cols)) for row in range(matrix.rows))


def _matrix(rows: RationalMatrix, row_count: int, column_count: int) -> sp.Matrix:
    if (
        not isinstance(rows, tuple)
        or len(rows) != row_count
        or any(not isinstance(row, tuple) or len(row) != column_count for row in rows)
        or any(type(value) is not Fraction for row in rows for value in row)
    ):
        raise ValueError("retained matrices require immutable Fraction rows with the declared shape")
    return sp.Matrix(row_count, column_count, lambda row, column: sp.Rational(rows[row][column]))


def _indices(indices: tuple[int, ...], dimension: int) -> tuple[int, ...]:
    if not isinstance(indices, tuple) or any(type(index) is not int or not 0 <= index < dimension for index in indices):
        raise ValueError("retained indices require an immutable tuple of in-range integers")
    if len(set(indices)) != len(indices):
        raise ValueError("retained indices must be distinct")
    return indices


def _kernel(matrix: sp.Matrix) -> tuple[sp.Matrix, tuple[int, ...]]:
    reduced, pivots = matrix.rref()
    free = tuple(index for index in range(matrix.cols) if index not in pivots)
    kernel = sp.zeros(matrix.cols, len(free))
    for position, column in enumerate(free):
        kernel[column, position] = 1
        for row, pivot in enumerate(pivots):
            kernel[pivot, position] = -reduced[row, column]
    return kernel, tuple(int(index) for index in pivots)


def _basis_matrix(coordinate: int) -> sp.Matrix:
    return sp.Matrix(multiplication_matrix(tuple(int(index == coordinate) for index in range(DIMENSION))))


@dataclass(frozen=True)
class ReducedRankCertificate:
    dimension: int
    pivot_rows: tuple[int, ...]
    pivot_columns: tuple[int, ...]
    pivot_determinant: Fraction
    kernel_basis: RationalMatrix

    @property
    def rank(self) -> int:
        return len(self.pivot_columns)

    @property
    def nullity(self) -> int:
        return self.dimension - self.rank


def _reduced_certificate(matrix: sp.Matrix) -> ReducedRankCertificate:
    kernel, columns = _kernel(matrix)
    rows = tuple(int(index) for index in matrix[:, list(columns)].T.rref()[1]) if columns else ()
    determinant = matrix.extract(rows, columns).det()
    return ReducedRankCertificate(matrix.rows, rows, columns, _fraction(determinant), _rows(kernel))


def verify_reduced_rank_certificate(matrix_rows: RationalMatrix, certificate: ReducedRankCertificate) -> bool:
    """Prove both rank bounds by a nonzero minor and a complete free-row kernel."""
    try:
        if not isinstance(certificate, ReducedRankCertificate) or type(certificate.dimension) is not int:
            return False
        dimension = certificate.dimension
        if dimension not in CENTER_NULLITIES:
            return False
        matrix = _matrix(matrix_rows, dimension, dimension)
        rows = _indices(certificate.pivot_rows, dimension)
        columns = _indices(certificate.pivot_columns, dimension)
        if len(rows) != len(columns) or type(certificate.pivot_determinant) is not Fraction:
            return False
        free = tuple(index for index in range(dimension) if index not in columns)
        kernel = _matrix(certificate.kernel_basis, dimension, len(free))
        determinant = matrix.extract(rows, columns).det()
        return bool(
            determinant != 0
            and determinant == certificate.pivot_determinant
            and kernel.extract(free, range(len(free))) == sp.eye(len(free))
            and matrix * kernel == sp.zeros(dimension, len(free))
        )
    except (ValueError, TypeError, AttributeError, IndexError):
        return False


@dataclass(frozen=True)
class SkewSchurChart:
    center_certificate: RankCertificate
    complement: RationalMatrix
    kernel: RationalMatrix
    transform: RationalMatrix
    inverse_transform: RationalMatrix
    projection: RationalMatrix

    @property
    def reduced_dimension(self) -> int:
        return self.center_certificate.nullity

    @property
    def pivot_dimension(self) -> int:
        return DIMENSION - self.reduced_dimension

    @classmethod
    def from_certificate(cls, certificate: RankCertificate) -> SkewSchurChart:
        """Select canonical independent columns and a canonical complete kernel."""
        try:
            _validate_center(certificate)
        except (ValueError, TypeError, AttributeError, IndexError) as error:
            raise ValueError("center requires an intact nonzero doubly-pure rank certificate") from error
        matrix = sp.Matrix(certificate.matrix)
        kernel, columns = _kernel(matrix)
        complement = matrix[:, list(columns)]
        transform = complement.row_join(kernel)
        inverse = transform.inv()
        chart = cls(
            certificate,
            _rows(complement),
            _rows(kernel),
            _rows(transform),
            _rows(inverse),
            _rows(inverse[len(columns) :, :]),
        )
        _require(verify_skew_schur_chart(chart), "constructed skew-Schur chart fails verification")
        return chart

    def reduce(self, coordinates: Sequence[int | Fraction]) -> SkewSchurPoint:
        """Certify any nonzero rational input with an invertible fixed pivot."""
        values = _coordinates(coordinates)
        if not verify_skew_schur_chart(self):
            raise ValueError("reduction requires an intact skew-Schur chart")
        complement = sp.Matrix(self.complement)
        kernel = sp.Matrix(self.kernel)
        matrix = sp.Matrix(multiplication_matrix(values))
        pivot = complement.T * matrix * complement
        determinant = pivot.det()
        if determinant == 0:
            raise ValueError("pivot determinant vanishes; the point lies outside this chart")
        cross = complement.T * matrix * kernel
        diagonal = kernel.T * matrix * kernel
        inverse_cross = pivot.inv() * cross
        schur = diagonal + cross.T * inverse_cross
        lift = kernel - complement * inverse_cross
        congruence = sp.eye(DIMENSION)
        congruence[: self.pivot_dimension, self.pivot_dimension :] = -inverse_cross
        reduced_certificate = _reduced_certificate(schur)
        reduced_kernel = _matrix(reduced_certificate.kernel_basis, self.reduced_dimension, reduced_certificate.nullity)
        point = SkewSchurPoint(
            self,
            values,
            _rows(matrix),
            _rows(pivot),
            _rows(cross),
            _rows(diagonal),
            _fraction(determinant),
            _rows(schur),
            _rows(lift),
            _rows(lift.T * lift),
            _rows(congruence),
            reduced_certificate,
            _rows(lift * reduced_kernel),
        )
        _require(verify_skew_schur_point(self, point), "constructed skew-Schur point fails verification")
        return point

    def symbolic_domain(self) -> SchurPolynomialContract:
        """Return executable exact linear blocks and unexpanded cofactor recipes."""
        if not verify_skew_schur_chart(self):
            raise ValueError("polynomial contract requires an intact skew-Schur chart")
        complement, kernel = sp.Matrix(self.complement), sp.Matrix(self.kernel)
        records = parallel.ordered_map(
            _direction_blocks, [(coordinate, self.complement, self.kernel) for coordinate in COORDINATE_INDICES]
        )
        _require(complement.cols + kernel.cols == DIMENSION, "polynomial block dimensions disagree")
        return SchurPolynomialContract(
            self,
            COORDINATE_INDICES,
            tuple(record[0] for record in records),
            tuple(record[1] for record in records),
            tuple(record[2] for record in records),
        )

    def derivative_at_center(self) -> LinearizedSchurConstraint:
        """Return dS[h]=V.T*L_h*V and linearized sphere-tangent bounds."""
        contract = self.symbolic_domain()
        dimension = self.reduced_dimension
        entries = tuple((row, column) for row in range(dimension) for column in range(row + 1, dimension))
        derivative = sp.Matrix(
            len(entries),
            30,
            lambda row, column: sp.Rational(contract.diagonal_coefficients[column][entries[row][0]][entries[row][1]]),
        )
        center = tuple(self.center_certificate.coordinates[index] for index in COORDINATE_INDICES)
        kernel, pivots = _kernel(derivative)
        constraint = sp.Matrix(1, 30, center)
        unit_kernel, unit_pivots = _kernel(derivative.col_join(constraint))
        _require(derivative * constraint.T == sp.zeros(len(entries), 1), "radial direction fails the derivative kernel")
        _require(len(unit_pivots) == len(pivots) + 1, "sphere constraint fails independence")
        return LinearizedSchurConstraint(
            COORDINATE_INDICES,
            entries,
            contract.diagonal_coefficients,
            _rows(derivative),
            center,
            len(pivots),
            _rows(kernel),
            _rows(unit_kernel),
        )


def _validate_center(certificate: RankCertificate) -> None:
    if not isinstance(certificate, RankCertificate):
        raise ValueError("center requires a rank certificate")
    values = _coordinates(certificate.coordinates)
    if certificate.side != "left" or certificate.nullity not in CENTER_NULLITIES:
        raise ValueError("center requires left multiplication and nullity 4, 8, 12, or 16")
    if not isinstance(certificate.coordinates, tuple) or any(
        type(value) is not Fraction for value in certificate.coordinates
    ):
        raise ValueError("center coordinates require immutable Fractions")
    _matrix(certificate.matrix, DIMENSION, DIMENSION)
    _matrix(certificate.kernel_basis, DIMENSION, certificate.nullity)
    _indices(certificate.pivot_rows, DIMENSION)
    _indices(certificate.pivot_columns, DIMENSION)
    if any(
        type(value) is not Fraction
        for value in (certificate.pivot_determinant, certificate.input_norm_squared, certificate.block_encoding_alpha)
    ):
        raise ValueError("center scalar fields require Fractions")
    if not verify_rank_certificate(values, certificate):
        raise ValueError("center rank certificate fails verification")


def verify_skew_schur_chart(chart: SkewSchurChart) -> bool:
    """Validate every retained chart field and deterministic basis choice."""
    try:
        if not isinstance(chart, SkewSchurChart):
            return False
        _validate_center(chart.center_certificate)
        pivot_size, reduced_size = chart.pivot_dimension, chart.reduced_dimension
        matrix = sp.Matrix(chart.center_certificate.matrix)
        complement = _matrix(chart.complement, DIMENSION, pivot_size)
        kernel = _matrix(chart.kernel, DIMENSION, reduced_size)
        transform = _matrix(chart.transform, DIMENSION, DIMENSION)
        inverse = _matrix(chart.inverse_transform, DIMENSION, DIMENSION)
        projection = _matrix(chart.projection, reduced_size, DIMENSION)
        canonical_kernel, columns = _kernel(matrix)
        return bool(
            matrix + matrix.T == sp.zeros(DIMENSION)
            and kernel == canonical_kernel
            and complement == matrix[:, list(columns)]
            and complement.T * kernel == sp.zeros(pivot_size, reduced_size)
            and transform == complement.row_join(kernel)
            and transform * inverse == sp.eye(DIMENSION)
            and inverse * transform == sp.eye(DIMENSION)
            and projection == inverse[pivot_size:, :]
            and (complement.T * matrix * complement).det() != 0
            and matrix * kernel == sp.zeros(DIMENSION, reduced_size)
        )
    except (ValueError, TypeError, AttributeError, IndexError):
        return False


@dataclass(frozen=True)
class SkewSchurPoint:
    chart: SkewSchurChart
    coordinates: tuple[Fraction, ...]
    matrix: RationalMatrix
    pivot: RationalMatrix
    cross: RationalMatrix
    diagonal: RationalMatrix
    pivot_determinant: Fraction
    schur_complement: RationalMatrix
    lift: RationalMatrix
    gram_metric: RationalMatrix
    congruence: RationalMatrix
    reduced_certificate: ReducedRankCertificate
    full_kernel: RationalMatrix

    @property
    def rank(self) -> int:
        return self.chart.pivot_dimension + self.reduced_certificate.rank

    @property
    def nullity(self) -> int:
        return self.reduced_certificate.nullity

    def certify_reduced_rank(self) -> ReducedRankCertificate:
        if not verify_skew_schur_point(self.chart, self):
            raise ValueError("reduced-rank certification requires an intact point")
        return self.reduced_certificate

    def lift_vector(self, coordinates: Sequence[int | Fraction]) -> tuple[Fraction, ...]:
        """Lift exact reduced kernel coordinates; normalization uses gram_metric."""
        if not verify_skew_schur_point(self.chart, self):
            raise ValueError("vector lift requires an intact point")
        if (
            isinstance(coordinates, (str, bytes))
            or not isinstance(coordinates, Sequence)
            or len(coordinates) != self.chart.reduced_dimension
        ):
            raise ValueError("reduced vector length differs from the residual dimension")
        vector = sp.Matrix([_rational(value) for value in coordinates])
        if sp.Matrix(self.schur_complement) * vector != sp.zeros(self.chart.reduced_dimension, 1):
            raise ValueError("reduced vector lies outside the residual kernel")
        return tuple(_fraction(value) for value in sp.Matrix(self.lift) * vector)

    def project_vector(self, coordinates: Sequence[int | Fraction]) -> tuple[Fraction, ...]:
        """Invert the lift on the full kernel, without restricting partner support."""
        if not verify_skew_schur_point(self.chart, self):
            raise ValueError("vector projection requires an intact point")
        if (
            isinstance(coordinates, (str, bytes))
            or not isinstance(coordinates, Sequence)
            or len(coordinates) != DIMENSION
        ):
            raise ValueError("partner vector requires 32 exact rational entries")
        vector = sp.Matrix([_rational(value) for value in coordinates])
        if sp.Matrix(self.matrix) * vector != sp.zeros(DIMENSION, 1):
            raise ValueError("partner vector lies outside the full kernel")
        return tuple(_fraction(value) for value in sp.Matrix(self.chart.projection) * vector)


def verify_skew_schur_point(chart: SkewSchurChart, point: SkewSchurPoint) -> bool:
    """Check matrix provenance, congruence, both rank bounds, lift and metric."""
    try:
        if not verify_skew_schur_chart(chart) or not isinstance(point, SkewSchurPoint) or point.chart != chart:
            return False
        values = _coordinates(point.coordinates)
        if not isinstance(point.coordinates, tuple) or any(type(value) is not Fraction for value in point.coordinates):
            return False
        pivot_size, reduced_size = chart.pivot_dimension, chart.reduced_dimension
        matrix = _matrix(point.matrix, DIMENSION, DIMENSION)
        pivot = _matrix(point.pivot, pivot_size, pivot_size)
        cross = _matrix(point.cross, pivot_size, reduced_size)
        diagonal = _matrix(point.diagonal, reduced_size, reduced_size)
        schur = _matrix(point.schur_complement, reduced_size, reduced_size)
        lift = _matrix(point.lift, DIMENSION, reduced_size)
        metric = _matrix(point.gram_metric, reduced_size, reduced_size)
        congruence = _matrix(point.congruence, DIMENSION, DIMENSION)
        if type(point.pivot_determinant) is not Fraction or not point.pivot_determinant:
            return False
        if not verify_reduced_rank_certificate(point.schur_complement, point.reduced_certificate):
            return False
        if point.reduced_certificate.dimension != reduced_size:
            return False
        full_kernel = _matrix(point.full_kernel, DIMENSION, point.nullity)
        reduced_kernel = _matrix(point.reduced_certificate.kernel_basis, reduced_size, point.nullity)
        complement, kernel = sp.Matrix(chart.complement), sp.Matrix(chart.kernel)
        transform, projection = sp.Matrix(chart.transform), sp.Matrix(chart.projection)
        if point.matrix != multiplication_matrix(values) or pivot != complement.T * matrix * complement:
            return False
        if pivot.det() != point.pivot_determinant:
            return False
        inverse_cross = pivot.inv() * cross
        expected_congruence = sp.eye(DIMENSION)
        expected_congruence[:pivot_size, pivot_size:] = -inverse_cross
        blocked = pivot.row_join(cross).col_join((-cross.T).row_join(diagonal))
        target = sp.diag(pivot, schur)
        residual = sp.zeros(pivot_size, reduced_size).col_join(schur)
        return bool(
            matrix + matrix.T == sp.zeros(DIMENSION)
            and cross == complement.T * matrix * kernel
            and diagonal == kernel.T * matrix * kernel
            and transform.T * matrix * transform == blocked
            and schur == diagonal + cross.T * inverse_cross
            and schur + schur.T == sp.zeros(reduced_size)
            and congruence == expected_congruence
            and congruence.T * blocked * congruence == target
            and lift == kernel - complement * inverse_cross
            and transform.T * matrix * lift == residual
            and projection * lift == sp.eye(reduced_size)
            and metric == lift.T * lift
            and full_kernel == lift * reduced_kernel
            and matrix * full_kernel == sp.zeros(DIMENSION, point.nullity)
            and projection * full_kernel == reduced_kernel
        )
    except (ValueError, TypeError, AttributeError, IndexError):
        return False


def _direction_blocks(
    task: tuple[int, RationalMatrix, RationalMatrix],
) -> tuple[RationalMatrix, RationalMatrix, RationalMatrix]:
    coordinate, complement_rows, kernel_rows = task
    complement, kernel = sp.Matrix(complement_rows), sp.Matrix(kernel_rows)
    matrix = _basis_matrix(coordinate)
    return (
        _rows(complement.T * matrix * complement),
        _rows(complement.T * matrix * kernel),
        _rows(kernel.T * matrix * kernel),
    )


@dataclass(frozen=True)
class ClearedSchurPoint:
    determinant: Fraction
    adjugate: RationalMatrix
    schur_numerator: RationalMatrix
    lift_numerator: RationalMatrix


@dataclass(frozen=True)
class SchurPolynomialContract:
    """Exact matrix-polynomial DAG: linear blocks, determinant, and cofactors.

    The formulas delta=det(A), Sbar=delta*D+B.T*adj(A)*B and
    Hbar=delta*V-U*adj(A)*B define polynomials on all thirty real variables.
    The rational chart and incidence equivalence require delta != 0.
    """

    chart: SkewSchurChart
    coordinate_indices: tuple[int, ...]
    pivot_coefficients: tuple[RationalMatrix, ...]
    cross_coefficients: tuple[RationalMatrix, ...]
    diagonal_coefficients: tuple[RationalMatrix, ...]

    def _validate(self) -> None:
        if (
            not verify_skew_schur_chart(self.chart)
            or _indices(self.coordinate_indices, DIMENSION) != COORDINATE_INDICES
        ):
            raise ValueError("polynomial contract has an invalid chart or coordinate order")
        for sequence in (self.pivot_coefficients, self.cross_coefficients, self.diagonal_coefficients):
            if not isinstance(sequence, tuple) or len(sequence) != 30:
                raise ValueError("polynomial contract requires thirty immutable coefficient matrices")
        pivot_size, reduced_size = self.chart.pivot_dimension, self.chart.reduced_dimension
        for position, coordinate in enumerate(COORDINATE_INDICES):
            actual = (
                self.pivot_coefficients[position],
                self.cross_coefficients[position],
                self.diagonal_coefficients[position],
            )
            for rows, shape in zip(
                actual,
                ((pivot_size, pivot_size), (pivot_size, reduced_size), (reduced_size, reduced_size)),
                strict=True,
            ):
                _matrix(rows, *shape)
            if actual != _direction_blocks((coordinate, self.chart.complement, self.chart.kernel)):
                raise ValueError("polynomial coefficient differs from its exact multiplication operator")

    def symbolic_blocks(self) -> tuple[tuple[sp.Symbol, ...], sp.Matrix, sp.Matrix, sp.Matrix]:
        """Build only linear entries; determinant/cofactor expansion stays deferred."""
        self._validate()
        symbols = tuple(sp.Symbol(f"x{index}", real=True) for index in COORDINATE_INDICES)
        blocks = []
        for coefficients in (self.pivot_coefficients, self.cross_coefficients, self.diagonal_coefficients):
            rows, columns = len(coefficients[0]), len(coefficients[0][0])
            block = sp.zeros(rows, columns)
            for symbol, coefficient in zip(symbols, coefficients, strict=True):
                block += symbol * sp.Matrix(coefficient)
            blocks.append(block)
        return symbols, blocks[0], blocks[1], blocks[2]

    def determinant_expression(self) -> sp.Expr:
        return sp.Determinant(sp.ImmutableMatrix(self.symbolic_blocks()[1]))

    def cofactor_expression(self, row: int, column: int) -> sp.Expr:
        """Return adj(A)[row,column], retaining its minor determinant unexpanded."""
        pivot_size = self.chart.pivot_dimension
        if type(row) is not int or type(column) is not int or not 0 <= row < pivot_size or not 0 <= column < pivot_size:
            raise ValueError("cofactor indices lie outside the pivot matrix")
        pivot = self.symbolic_blocks()[1]
        minor = pivot.extract(
            [index for index in range(pivot_size) if index != column],
            [index for index in range(pivot_size) if index != row],
        )
        return (-1) ** (row + column) * sp.Determinant(sp.ImmutableMatrix(minor))

    def evaluate(self, coordinates: Sequence[int | Fraction]) -> ClearedSchurPoint:
        """Evaluate the cleared polynomials, including their singular-pivot values.

        An even skew matrix with zero determinant has corank at least two,
        hence every codimension-one minor vanishes and its adjugate is zero.
        """
        values = _coordinates(coordinates, allow_zero=True)
        self._validate()
        blocks = []
        for coefficients in (self.pivot_coefficients, self.cross_coefficients, self.diagonal_coefficients):
            block = sp.zeros(len(coefficients[0]), len(coefficients[0][0]))
            for coordinate, coefficient in zip(COORDINATE_INDICES, coefficients, strict=True):
                block += values[coordinate] * sp.Matrix(coefficient)
            blocks.append(block)
        pivot, cross, diagonal = blocks
        determinant = pivot.det()
        adjugate = determinant * pivot.inv() if determinant else sp.zeros(pivot.rows)
        schur = determinant * diagonal + cross.T * adjugate * cross
        lift = determinant * sp.Matrix(self.chart.kernel) - sp.Matrix(self.chart.complement) * adjugate * cross
        matrix = sp.Matrix(multiplication_matrix(values))
        _require(
            sp.Matrix(self.chart.transform).T * matrix * lift
            == sp.zeros(self.chart.pivot_dimension, self.chart.reduced_dimension).col_join(schur),
            "cleared lift identity fails",
        )
        _require(
            sp.Matrix(self.chart.projection) * lift == determinant * sp.eye(self.chart.reduced_dimension),
            "cleared inverse identity fails",
        )
        return ClearedSchurPoint(_fraction(determinant), _rows(adjugate), _rows(schur), _rows(lift))

    def description(self) -> dict[str, object]:
        return {
            "coefficient_domain": "x in R^32, x[0]=x[16]=0",
            "coordinate_indices": list(self.coordinate_indices),
            "pivot_dimension": self.chart.pivot_dimension,
            "residual_dimension": self.chart.reduced_dimension,
            "chart_inequation": "delta=det(A) != 0",
            "cleared_residual": "Sbar=delta*D+B.T*adj(A)*B",
            "cleared_lift": "Hbar=delta*V-U*adj(A)*B",
            "degree_bounds": {
                "delta": self.chart.pivot_dimension,
                "Sbar": self.chart.pivot_dimension + 1,
                "Hbar": self.chart.pivot_dimension,
            },
            "rank_locus": "rank(L)=r+s iff Sbar has a nonzero s-minor and all (s+1)-minors vanish on delta!=0",
            "kernel_incidence": "Sbar*w=0, w.T*Hbar.T*Hbar*w=delta^2; y=Hbar*w/delta, w=J*y",
            "scope": (
                "fixed pivot domain; coverage, smooth strata, attachments and unrestricted topology "
                "require further proofs"
            ),
        }


@dataclass(frozen=True)
class LinearizedSchurConstraint:
    coordinate_indices: tuple[int, ...]
    upper_triangle_indices: tuple[tuple[int, int], ...]
    direction_matrices: tuple[RationalMatrix, ...]
    coefficient_matrix: RationalMatrix
    unit_base_constraint: tuple[Fraction, ...]
    rank: int
    nullspace_basis: RationalMatrix
    unit_base_nullspace_basis: RationalMatrix

    @property
    def linearized_dimension(self) -> int:
        return 30 - self.rank

    @property
    def unit_base_linearized_dimension(self) -> int:
        return 29 - self.rank


def verify_linearized_schur_constraint(chart: SkewSchurChart, constraint: LinearizedSchurConstraint) -> bool:
    """Verify every derivative field and its stated linearized dimension bounds."""
    try:
        if not isinstance(constraint, LinearizedSchurConstraint) or not verify_skew_schur_chart(chart):
            return False
        dimension = chart.reduced_dimension
        entries = tuple((row, column) for row in range(dimension) for column in range(row + 1, dimension))
        if (
            _indices(constraint.coordinate_indices, DIMENSION) != COORDINATE_INDICES
            or constraint.upper_triangle_indices != entries
            or not isinstance(constraint.upper_triangle_indices, tuple)
            or any(
                not isinstance(pair, tuple) or any(type(index) is not int for index in pair)
                for pair in constraint.upper_triangle_indices
            )
            or type(constraint.rank) is not int
            or not 0 <= constraint.rank <= 29
            or not isinstance(constraint.direction_matrices, tuple)
            or len(constraint.direction_matrices) != 30
            or not isinstance(constraint.unit_base_constraint, tuple)
            or len(constraint.unit_base_constraint) != 30
            or any(type(value) is not Fraction for value in constraint.unit_base_constraint)
        ):
            return False
        for direction in constraint.direction_matrices:
            _matrix(direction, dimension, dimension)
        _matrix(constraint.coefficient_matrix, len(entries), 30)
        _matrix(constraint.nullspace_basis, 30, 30 - constraint.rank)
        _matrix(constraint.unit_base_nullspace_basis, 30, 29 - constraint.rank)
        return constraint == chart.derivative_at_center()
    except (ValueError, TypeError, AttributeError, IndexError):
        return False


def _fixture(sparse: dict[int, int | Fraction]) -> tuple[Fraction, ...]:
    return tuple(Fraction(sparse.get(index, 0)) for index in range(DIMENSION))


def _audit_center(task: tuple[str, dict[int, int | Fraction], int]) -> dict[str, object]:
    label, sparse, expected_nullity = task
    values = _fixture(sparse)
    chart = SkewSchurChart.from_certificate(rank_certificate(values))
    _require(chart.reduced_dimension == expected_nullity, "center nullity differs from the independent certificate")
    point = chart.reduce(values)
    derivative = chart.derivative_at_center()
    _require(point.nullity == expected_nullity, "center residual changes rank")
    _require(verify_linearized_schur_constraint(chart, derivative), "derivative fields fail verification")
    _require(
        not verify_linearized_schur_constraint(chart, replace(derivative, rank=derivative.rank + 1)),
        "altered derivative rank accepted",
    )
    contract = chart.symbolic_domain()
    cleared = contract.evaluate(values)
    _require(
        sp.Matrix(cleared.schur_numerator) == point.pivot_determinant * sp.Matrix(point.schur_complement),
        "cleared residual disagrees",
    )
    _require(
        sp.Matrix(cleared.lift_numerator) == point.pivot_determinant * sp.Matrix(point.lift), "cleared lift disagrees"
    )
    return {
        "label": label,
        "nullity": point.nullity,
        "pivot_determinant": str(point.pivot_determinant),
        "linearized_rank": derivative.rank,
        "unit_base_linearized_dimension": derivative.unit_base_linearized_dimension,
        "coordinate_directions": len(derivative.direction_matrices),
    }


def audit_skew_schur_charts() -> dict[str, object]:
    """Check exact finite inputs, rank certificates, domains and damaged fields."""
    fixtures = [
        ("nullity4", {1: Fraction(1), 10: Fraction(1, 4), 18: Fraction(5, 8), 25: Fraction(1, 8)}, 4),
        ("nullity8", {1: 1, 10: 1}, 8),
        ("nullity12", {1: 1, 18: 1}, 12),
        ("nullity16", {1: 1, 10: 1, 18: 1, 25: -1}, 16),
    ]
    centers = parallel.ordered_map(_audit_center, fixtures, min_items=2)
    values = _fixture({1: 1, 10: 1})
    chart = SkewSchurChart.from_certificate(rank_certificate(values))
    points = []
    for name, coordinates in (
        ("straight", _fixture({1: 1, 3: 1, 10: 1})),
        ("curved", _fixture({1: Fraction(3, 5), 3: Fraction(4, 5), 10: 1})),
        ("dense", _fixture({index: Fraction(index + 1, 31) for index in COORDINATE_INDICES})),
    ):
        point = chart.reduce(coordinates)
        independent = rank_certificate(coordinates)
        _require(point.rank == independent.rank, "residual rank differs from full certificate")
        _require(point.certify_reduced_rank() == point.reduced_certificate, "reduced certificate changes")
        reduced_kernel = _matrix(point.reduced_certificate.kernel_basis, chart.reduced_dimension, point.nullity)
        if point.nullity:
            vector = tuple(_fraction(value) for value in reduced_kernel[:, 0])
            lifted = point.lift_vector(vector)
            _require(point.project_vector(lifted) == vector, "partner inverse fails")
            _require(
                sum(value * value for value in lifted)
                == (sp.Matrix(vector).T * sp.Matrix(point.gram_metric) * sp.Matrix(vector))[0],
                "sphere metric identity fails",
            )
        else:
            _require(point.full_kernel == tuple(() for _ in range(DIMENSION)), "empty full kernel loses its rows")
        points.append(
            {
                "label": name,
                "full_rank": point.rank,
                "residual_rank": point.reduced_certificate.rank,
                "nullity": point.nullity,
            }
        )
    center_point = chart.reduce(values)
    damaged_count = 0
    for field in (
        "matrix",
        "pivot",
        "cross",
        "diagonal",
        "schur_complement",
        "lift",
        "gram_metric",
        "congruence",
        "full_kernel",
    ):
        original = getattr(center_point, field)
        damaged = tuple(
            tuple(value + int(row == 0 and column == 0) for column, value in enumerate(entries))
            for row, entries in enumerate(original)
        )
        _require(
            not verify_skew_schur_point(chart, replace(center_point, **dict[str, Any]({field: damaged}))),
            f"altered {field} accepted",
        )
        damaged_count += 1
    for field in ("complement", "kernel", "transform", "inverse_transform", "projection"):
        original = getattr(chart, field)
        damaged = tuple(
            tuple(value + int(row == 0 and column == 0) for column, value in enumerate(entries))
            for row, entries in enumerate(original)
        )
        _require(
            not verify_skew_schur_chart(replace(chart, **dict[str, Any]({field: damaged}))),
            f"altered chart {field} accepted",
        )
        damaged_count += 1
    _require(
        not verify_skew_schur_point(chart, replace(center_point, pivot_determinant=center_point.pivot_determinant + 1)),
        "altered point determinant accepted",
    )
    damaged_count += 1
    damaged_certificate = replace(
        center_point.reduced_certificate, kernel_basis=_rows(sp.zeros(chart.reduced_dimension))
    )
    _require(
        not verify_skew_schur_point(chart, replace(center_point, reduced_certificate=damaged_certificate)),
        "altered reduced kernel accepted",
    )
    damaged_count += 1
    rejected_count = 0
    invalid_inputs: list[object] = [
        [0] * 32,
        [0] * 30,
        [0.0] * 32,
        [False] * 32,
        _fixture({0: 1, 1: 1}),
        _fixture({16: 1, 1: 1}),
        _fixture({1: 1, 10: -1}),
    ]
    for invalid in invalid_inputs:
        try:
            chart.reduce(invalid)  # type: ignore[arg-type]
        except ValueError:
            rejected_count += 1
        else:
            raise RuntimeError("invalid point or singular pivot accepted")
    for invalid_center in (
        rank_certificate([0] * 32),
        rank_certificate(_fixture({1: 1})),
        rank_certificate(values, side="right"),
        replace(chart.center_certificate, pivot_determinant=Fraction(0)),
    ):
        try:
            SkewSchurChart.from_certificate(invalid_center)
        except ValueError:
            rejected_count += 1
        else:
            raise RuntimeError("invalid center accepted")
    contract = chart.symbolic_domain()
    singular_polynomial_checks = 0
    for singular in ([0] * 32, _fixture({1: 1, 10: -1})):
        cleared = contract.evaluate(singular)
        _require(
            cleared.determinant == 0
            and not any(value for row in cleared.adjugate for value in row)
            and not any(value for row in cleared.schur_numerator for value in row)
            and not any(value for row in cleared.lift_numerator for value in row),
            "cleared singular-pivot evaluation fails",
        )
        singular_polynomial_checks += 1
    changed_coefficient = _rows(sp.Matrix(contract.pivot_coefficients[0]) + sp.eye(chart.pivot_dimension))
    damaged_contract = replace(contract, pivot_coefficients=(changed_coefficient,) + contract.pivot_coefficients[1:])
    try:
        damaged_contract.evaluate(values)
    except ValueError:
        damaged_count += 1
    else:
        raise RuntimeError("altered polynomial coefficient accepted")
    for change in (
        {"coordinates": tuple(Fraction(2) * value for value in values)},
        {"matrix": _rows(sp.zeros(DIMENSION))},
        {"kernel_basis": _rows(sp.zeros(DIMENSION, chart.reduced_dimension))},
        {
            "pivot_rows": (chart.center_certificate.pivot_rows[1], chart.center_certificate.pivot_rows[0])
            + chart.center_certificate.pivot_rows[2:]
        },
        {"pivot_columns": (True,) + chart.center_certificate.pivot_columns[1:]},
        {"input_norm_squared": Fraction(3)},
        {"block_encoding_alpha": Fraction(3)},
    ):
        altered = replace(chart.center_certificate, **dict[str, Any](change))
        try:
            SkewSchurChart.from_certificate(altered)
        except ValueError:
            damaged_count += 1
        else:
            raise RuntimeError("altered center certificate accepted")
    for reduced_change in (
        {"dimension": True},
        {"pivot_rows": (0,)},
        {"pivot_columns": (0,)},
        {"pivot_determinant": Fraction(2)},
    ):
        altered_reduced = replace(center_point.reduced_certificate, **dict[str, Any](reduced_change))
        _require(
            not verify_reduced_rank_certificate(center_point.schur_complement, altered_reduced),
            "altered reduced rank certificate accepted",
        )
        damaged_count += 1
    return {
        "schema": "dimension32-skew-schur-charts-v1",
        "qpu_executed": False,
        "centers": centers,
        "points": points,
        "damaged_fields_rejected": damaged_count,
        "invalid_inputs_rejected": rejected_count,
        "singular_polynomial_evaluations": singular_polynomial_checks,
        "polynomial_contract": contract.description(),
        "linearized_scope": (
            "necessary first-order constraints and dimension bounds; nonlinear equations decide local rank"
        ),
        "global_scope": "finite chart regressions; unrestricted topology and finite atlas coverage remain open",
    }


def main() -> int:
    print(json.dumps(audit_skew_schur_charts(), indent=2, sort_keys=True, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
