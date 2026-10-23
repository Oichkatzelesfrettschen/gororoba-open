"""Exact second-order certificates for dimension-32 centered Schur charts.

The equations D(h)=0, D(a)=-2 B(h).T A0^(-1) B(h) constrain a
same-nullity curve through the center. The sphere through the rational center
adds <x0,h>=0 and <x0,a>=-||h||^2. A compatible certificate describes all
formal accelerations; curve existence and smoothness require further proof.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Any, Literal

import sympy as sp

import parallel
from rank_charts import RationalMatrix, multiplication_matrix, rank_certificate
from skew_schur_charts import (
    COORDINATE_INDICES,
    DIMENSION,
    LinearizedSchurConstraint,
    SkewSchurChart,
    _coordinates,
    _fraction,
    _indices,
    _kernel,
    _matrix,
    _rational,
    _rows,
    verify_linearized_schur_constraint,
    verify_skew_schur_chart,
)

RationalVector = tuple[Fraction, ...]
AccelerationStatus = Literal["first_order_inadmissible", "second_order_obstructed", "second_order_compatible"]


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def _vector(values: RationalVector, size: int) -> sp.Matrix:
    if not isinstance(values, tuple) or len(values) != size or any(type(value) is not Fraction for value in values):
        raise ValueError("retained vectors require immutable Fractions with the declared length")
    return sp.Matrix(size, 1, [sp.Rational(value) for value in values])


def _values(vector: sp.Matrix) -> RationalVector:
    return tuple(_fraction(value) for value in vector)


def _ambient(coefficients: sp.Matrix) -> RationalVector:
    values = [Fraction(0)] * DIMENSION
    for coordinate, value in zip(COORDINATE_INDICES, coefficients, strict=True):
        values[coordinate] = _fraction(value)
    return tuple(values)


def _particular(matrix: sp.Matrix, rhs: sp.Matrix) -> sp.Matrix:
    reduced, pivots = matrix.row_join(rhs).rref()
    if matrix.cols in pivots:
        raise ValueError("the rational acceleration equations are inconsistent")
    result = sp.zeros(matrix.cols, 1)
    for row, column in enumerate(pivots):
        result[column] = reduced[row, matrix.cols]
    return result


@dataclass(frozen=True)
class AffineAccelerationSpace:
    """All normalized formal accelerations: particular + kernel_basis * u.

    Columns use the thirty doubly-pure coordinate directions. The nonzero
    rank minor and free-row identity certify a complete homogeneous frame.
    The radial correction converts schur_particular to particular without
    changing its Schur derivative.
    """

    schur_particular: RationalVector
    radial_correction: Fraction
    particular: RationalVector
    kernel_basis: RationalMatrix
    rank: int
    pivot_rows: tuple[int, ...]
    pivot_columns: tuple[int, ...]
    pivot_determinant: Fraction


@dataclass(frozen=True)
class AccelerationObstruction:
    """A separating covector satisfies covector.T*M=0 and pairing != 0."""

    covector: RationalVector
    pairing: Fraction


@dataclass(frozen=True)
class SchurAccelerationCertificate:
    chart: SkewSchurChart
    direction: RationalVector
    linearized: LinearizedSchurConstraint
    direction_cross: RationalMatrix
    first_schur_derivative: RationalMatrix
    quadratic_term: RationalMatrix
    system_matrix: RationalMatrix
    system_rhs: RationalVector
    first_order_residual: RationalVector
    status: AccelerationStatus
    affine_space: AffineAccelerationSpace | None
    obstruction: AccelerationObstruction | None

    def acceleration(self, parameters: Sequence[int | Fraction]) -> RationalVector:
        """Evaluate the complete affine space and return 32 ambient coordinates."""
        if not verify_schur_acceleration_certificate(self.chart, self) or self.affine_space is None:
            raise ValueError("acceleration evaluation requires a verified compatible certificate")
        free_dimension = 30 - self.affine_space.rank
        if (
            isinstance(parameters, (str, bytes))
            or not isinstance(parameters, Sequence)
            or len(parameters) != free_dimension
        ):
            raise ValueError("acceleration parameters require one exact coefficient per free direction")
        coefficients = sp.Matrix(free_dimension, 1, [_rational(value) for value in parameters])
        particular = _vector(self.affine_space.particular, 30)
        kernel = _matrix(self.affine_space.kernel_basis, 30, free_dimension)
        return _ambient(particular + kernel * coefficients)


def certify_schur_acceleration(
    chart: SkewSchurChart,
    direction: Sequence[int | Fraction],
    *,
    linearized: LinearizedSchurConstraint | None = None,
) -> SchurAccelerationCertificate:
    """Certify exact rational first-order admission and formal acceleration.

    The fixed norm is the center's norm, so arbitrary nonzero rational
    centers remain admissible without an irrational normalization. Directions
    may use every doubly-pure coordinate; the zero direction is admitted.
    """
    if not verify_skew_schur_chart(chart):
        raise ValueError("acceleration certification requires a verified centered chart")
    values = _coordinates(direction, allow_zero=True)
    derivative = chart.derivative_at_center() if linearized is None else linearized
    if not verify_linearized_schur_constraint(chart, derivative):
        raise ValueError("linearized constraint does not verify against the centered chart")
    complement, kernel = sp.Matrix(chart.complement), sp.Matrix(chart.kernel)
    center = sp.Matrix(chart.center_certificate.coordinates)
    center_matrix = sp.Matrix(chart.center_certificate.matrix)
    direction_matrix = sp.Matrix(multiplication_matrix(values))
    pivot = complement.T * center_matrix * complement
    cross = complement.T * direction_matrix * kernel
    diagonal = kernel.T * direction_matrix * kernel
    quadratic = cross.T * pivot.inv() * cross
    derivative_map = sp.Matrix(derivative.coefficient_matrix)
    center_coefficients = sp.Matrix([center[index] for index in COORDINATE_INDICES])
    direction_coefficients = sp.Matrix([values[index] for index in COORDINATE_INDICES])
    system = derivative_map.col_join(center_coefficients.T)
    rhs = sp.Matrix(
        [-2 * quadratic[row, column] for row, column in derivative.upper_triangle_indices]
        + [-direction_coefficients.dot(direction_coefficients)]
    )
    first_order = system * direction_coefficients
    affine_space = None
    obstruction = None
    status: AccelerationStatus = "first_order_inadmissible"
    if first_order == sp.zeros(system.rows, 1):
        for covector in system.T.nullspace():
            pairing = (covector.T * rhs)[0]
            if pairing:
                obstruction = AccelerationObstruction(_values(covector), _fraction(pairing))
                break
        if obstruction is not None:
            status = "second_order_obstructed"
        else:
            status = "second_order_compatible"
            schur_particular = _particular(derivative_map, rhs[:-1, :])
            radial_correction = (rhs[-1] - center_coefficients.dot(schur_particular)) / center.dot(center)
            particular = schur_particular + radial_correction * center_coefficients
            homogeneous, columns = _kernel(system)
            rows = tuple(int(index) for index in system[:, list(columns)].T.rref()[1])
            affine_space = AffineAccelerationSpace(
                _values(schur_particular),
                _fraction(radial_correction),
                _values(particular),
                _rows(homogeneous),
                len(columns),
                rows,
                columns,
                _fraction(system.extract(rows, columns).det()),
            )
    certificate = SchurAccelerationCertificate(
        chart,
        values,
        derivative,
        _rows(cross),
        _rows(diagonal),
        _rows(quadratic),
        _rows(system),
        _values(rhs),
        _values(first_order),
        status,
        affine_space,
        obstruction,
    )
    _require(
        verify_schur_acceleration_certificate(chart, certificate),
        "constructed acceleration certificate fails verification",
    )
    return certificate


def _verify_affine_space(
    space: AffineAccelerationSpace,
    system: sp.Matrix,
    rhs: sp.Matrix,
    center: sp.Matrix,
    derivative_rank: int,
) -> bool:
    if not isinstance(space, AffineAccelerationSpace) or type(space.rank) is not int:
        return False
    if space.rank != derivative_rank + 1 or not 1 <= space.rank <= 30:
        return False
    if type(space.radial_correction) is not Fraction or type(space.pivot_determinant) is not Fraction:
        return False
    rows = _indices(space.pivot_rows, system.rows)
    columns = _indices(space.pivot_columns, 30)
    if len(rows) != space.rank or len(columns) != space.rank:
        return False
    free = tuple(index for index in range(30) if index not in columns)
    homogeneous = _matrix(space.kernel_basis, 30, len(free))
    particular = _vector(space.particular, 30)
    schur_particular = _vector(space.schur_particular, 30)
    derivative_map = system[:-1, :]
    determinant = system.extract(rows, columns).det()
    correction = (rhs[-1] - center.dot(schur_particular)) / center.dot(center)
    return bool(
        determinant != 0
        and determinant == space.pivot_determinant
        and homogeneous.extract(free, range(len(free))) == sp.eye(len(free))
        and system * homogeneous == sp.zeros(system.rows, len(free))
        and derivative_map * schur_particular == rhs[:-1, :]
        and derivative_map * center == sp.zeros(derivative_map.rows, 1)
        and correction == space.radial_correction
        and particular == schur_particular + correction * center
        and system * particular == rhs
    )


def verify_schur_acceleration_certificate(chart: SkewSchurChart, certificate: SchurAccelerationCertificate) -> bool:
    """Rebuild all thirty directions and verify each retained field exactly.

    The verifier reconstructs multiplication matrices, the quadratic term,
    both systems and the direct acceleration residual. It never calls the
    certificate constructor or accepts a status without its exact witness.
    """
    try:
        if not isinstance(certificate, SchurAccelerationCertificate) or not verify_skew_schur_chart(chart):
            return False
        if certificate.chart != chart or (
            certificate.chart is not chart and not verify_skew_schur_chart(certificate.chart)
        ):
            return False
        if not verify_linearized_schur_constraint(chart, certificate.linearized):
            return False
        derivative = certificate.linearized
        if type(certificate.status) is not str:
            return False
        if certificate.status not in ("first_order_inadmissible", "second_order_obstructed", "second_order_compatible"):
            return False
        stored_direction = _vector(certificate.direction, DIMENSION)
        direction = _coordinates(certificate.direction, allow_zero=True)
        complement, kernel = sp.Matrix(chart.complement), sp.Matrix(chart.kernel)
        center = sp.Matrix(chart.center_certificate.coordinates)
        matrix = sp.Matrix(multiplication_matrix(direction))
        pivot = complement.T * sp.Matrix(multiplication_matrix(chart.center_certificate.coordinates)) * complement
        cross = complement.T * matrix * kernel
        diagonal = kernel.T * matrix * kernel
        quadratic = cross.T * pivot.inv() * cross
        reduced_dimension = chart.reduced_dimension
        entries = tuple(
            (row, column) for row in range(reduced_dimension) for column in range(row + 1, reduced_dimension)
        )
        basis_columns = []
        for coordinate in COORDINATE_INDICES:
            operator = sp.Matrix(multiplication_matrix(tuple(int(index == coordinate) for index in range(DIMENSION))))
            derivative_matrix = kernel.T * operator * kernel
            basis_columns.append(sp.Matrix([derivative_matrix[row, column] for row, column in entries]))
        derivative_map = sp.Matrix.hstack(*basis_columns)
        center_coefficients = sp.Matrix([center[index] for index in COORDINATE_INDICES])
        system = derivative_map.col_join(center_coefficients.T)
        rhs = sp.Matrix(
            [-2 * quadratic[row, column] for row, column in entries] + [-stored_direction.dot(stored_direction)]
        )
        first_order = sp.Matrix([diagonal[row, column] for row, column in entries] + [center.dot(stored_direction)])
        if not (
            derivative_map == sp.Matrix(derivative.coefficient_matrix)
            and _matrix(certificate.direction_cross, chart.pivot_dimension, reduced_dimension) == cross
            and _matrix(certificate.first_schur_derivative, reduced_dimension, reduced_dimension) == diagonal
            and _matrix(certificate.quadratic_term, reduced_dimension, reduced_dimension) == quadratic
            and quadratic + quadratic.T == sp.zeros(reduced_dimension)
            and _matrix(certificate.system_matrix, len(entries) + 1, 30) == system
            and _vector(certificate.system_rhs, len(entries) + 1) == rhs
            and _vector(certificate.first_order_residual, len(entries) + 1) == first_order
        ):
            return False
        if first_order != sp.zeros(system.rows, 1):
            return bool(
                certificate.status == "first_order_inadmissible"
                and certificate.affine_space is None
                and certificate.obstruction is None
            )
        if certificate.status == "second_order_obstructed":
            obstruction = certificate.obstruction
            if certificate.affine_space is not None or not isinstance(obstruction, AccelerationObstruction):
                return False
            if type(obstruction.pairing) is not Fraction or not obstruction.pairing:
                return False
            covector = _vector(obstruction.covector, system.rows)
            return bool(
                covector.T * system == sp.zeros(1, 30)
                and covector[-1] == 0
                and (covector.T * rhs)[0] == obstruction.pairing
            )
        if certificate.status != "second_order_compatible" or certificate.obstruction is not None:
            return False
        space = certificate.affine_space
        if space is None or not _verify_affine_space(space, system, rhs, center_coefficients, derivative.rank):
            return False
        acceleration = sp.Matrix(_ambient(_vector(space.particular, 30)))
        acceleration_matrix = sp.Matrix(multiplication_matrix(_values(acceleration)))
        return bool(
            kernel.T * acceleration_matrix * kernel + 2 * quadratic == sp.zeros(reduced_dimension)
            and center.dot(acceleration) == -stored_direction.dot(stored_direction)
        )
    except (ValueError, TypeError, AttributeError, IndexError, ZeroDivisionError):
        return False


def verify_acceleration_member(
    certificate: SchurAccelerationCertificate, acceleration: Sequence[int | Fraction]
) -> bool:
    """Check a full ambient acceleration by its independently rebuilt operator."""
    try:
        if (
            not verify_schur_acceleration_certificate(certificate.chart, certificate)
            or certificate.affine_space is None
        ):
            return False
        values = _coordinates(acceleration, allow_zero=True)
        chart = certificate.chart
        complement, kernel = sp.Matrix(chart.complement), sp.Matrix(chart.kernel)
        center = sp.Matrix(chart.center_certificate.coordinates)
        direction = sp.Matrix(certificate.direction)
        pivot = complement.T * sp.Matrix(multiplication_matrix(_values(center))) * complement
        cross = complement.T * sp.Matrix(multiplication_matrix(_values(direction))) * kernel
        direct_second = kernel.T * sp.Matrix(multiplication_matrix(values)) * kernel + 2 * cross.T * pivot.inv() * cross
        return bool(
            direct_second == sp.zeros(chart.reduced_dimension)
            and center.dot(sp.Matrix(values)) == -direction.dot(direction)
        )
    except (ValueError, TypeError, AttributeError, IndexError, ZeroDivisionError):
        return False


def _fixture(entries: dict[int, int | Fraction]) -> RationalVector:
    return tuple(Fraction(entries.get(index, 0)) for index in range(DIMENSION))


def _alter_matrix(values: RationalMatrix) -> RationalMatrix:
    return tuple(
        tuple(value + Fraction(int(row == 0 and column == 0)) for column, value in enumerate(entries))
        for row, entries in enumerate(values)
    )


def _alter_vector(values: RationalVector) -> RationalVector:
    return (values[0] + 1, *values[1:])


def _audit_center(task: tuple[str, dict[int, int | Fraction], int]) -> dict[str, object]:
    label, entries, expected_nullity = task
    center = _fixture(entries)
    chart = SkewSchurChart.from_certificate(rank_certificate(center))
    derivative = chart.derivative_at_center()
    _require(chart.reduced_dimension == expected_nullity, "audit center nullity differs")
    zero = certify_schur_acceleration(chart, _fixture({}), linearized=derivative)
    _require(zero.status == "second_order_compatible", "zero direction fails formal compatibility")
    space = zero.affine_space
    _require(space is not None, "zero direction loses its affine space")
    if space is None:
        raise RuntimeError("zero direction has no acceleration space")
    parameters = [Fraction(index + 1, index + 2) for index in range(30 - space.rank)]
    acceleration = zero.acceleration(parameters)
    _require(verify_acceleration_member(zero, acceleration), "affine parameterization fails direct membership")
    tangent = sp.Matrix(derivative.unit_base_nullspace_basis)
    tangent_direction = _ambient(tangent * sp.Matrix([Fraction(index + 1, index + 2) for index in range(tangent.cols)]))
    tangent_certificate = certify_schur_acceleration(chart, tangent_direction, linearized=derivative)
    _require(
        tangent_certificate.status != "first_order_inadmissible", "dense exact tangent fails first-order constraints"
    )
    radial = certify_schur_acceleration(chart, center, linearized=derivative)
    _require(radial.status == "first_order_inadmissible", "radial direction passes the sphere constraint")
    scaled_center = tuple(-Fraction(3, 2) * value for value in center)
    scaled_chart = SkewSchurChart.from_certificate(rank_certificate(scaled_center))
    scaled_zero = certify_schur_acceleration(scaled_chart, _fixture({}))
    _require(scaled_zero.status == "second_order_compatible", "rational center rescaling changes zero compatibility")
    _require(scaled_chart.reduced_dimension == expected_nullity, "rational center rescaling changes nullity")
    return {
        "label": label,
        "nullity": expected_nullity,
        "derivative_rank": derivative.rank,
        "free_acceleration_dimension": 30 - space.rank,
        "dense_tangent_status": tangent_certificate.status,
        "zero_direction": zero.status,
        "radial_direction": radial.status,
        "negative_rational_center_rescaling": scaled_zero.status,
        "all_thirty_derivative_directions_verified": True,
        "affine_parameterization_verified": True,
    }


def _damaged(value: Any, **fields: Any) -> Any:
    """Construct deliberately ill-typed audit fixtures without weakening public types."""
    return replace(value, **fields)


def _audit_mutations(
    chart: SkewSchurChart, compatible: SchurAccelerationCertificate, obstructed: SchurAccelerationCertificate
) -> list[str]:
    space = compatible.affine_space
    obstruction = obstructed.obstruction
    if space is None or obstruction is None:
        raise RuntimeError("mutation fixtures require both compatible and obstructed witnesses")
    invalid_certificates: list[tuple[str, SkewSchurChart, Any]] = [
        ("certificate_type", chart, None),
        ("status", chart, _damaged(compatible, status="invalid")),
        ("direction_value", chart, _damaged(compatible, direction=_alter_vector(compatible.direction))),
        ("direction_shape", chart, _damaged(compatible, direction=compatible.direction[:-1])),
        ("direction_mutability", chart, _damaged(compatible, direction=list(compatible.direction))),
        ("direction_float", chart, _damaged(compatible, direction=(0.0, *compatible.direction[1:]))),
        ("direction_bool", chart, _damaged(compatible, direction=(False, *compatible.direction[1:]))),
        ("chart", chart, _damaged(compatible, chart=_damaged(chart, complement=_alter_matrix(chart.complement)))),
        (
            "equal_chart_integer_entries",
            chart,
            _damaged(
                compatible,
                chart=_damaged(chart, complement=tuple(tuple(int(value) for value in row) for row in chart.complement)),
            ),
        ),
        ("derivative_rank", chart, _damaged(compatible, linearized=_damaged(compatible.linearized, rank=0))),
        ("cross", chart, _damaged(compatible, direction_cross=_alter_matrix(compatible.direction_cross))),
        (
            "first_derivative",
            chart,
            _damaged(compatible, first_schur_derivative=_alter_matrix(compatible.first_schur_derivative)),
        ),
        ("quadratic", chart, _damaged(compatible, quadratic_term=_alter_matrix(compatible.quadratic_term))),
        ("system", chart, _damaged(compatible, system_matrix=_alter_matrix(compatible.system_matrix))),
        ("rhs", chart, _damaged(compatible, system_rhs=_alter_vector(compatible.system_rhs))),
        (
            "first_order",
            chart,
            _damaged(compatible, first_order_residual=_alter_vector(compatible.first_order_residual)),
        ),
        ("compatible_without_space", chart, _damaged(compatible, affine_space=None)),
        ("compatible_with_separator", chart, _damaged(compatible, obstruction=obstruction)),
        (
            "false_first_order_failure",
            chart,
            _damaged(compatible, status="first_order_inadmissible", affine_space=None),
        ),
    ]
    space_mutations = [
        ("space_type", None),
        ("space_rank", _damaged(space, rank=space.rank + 1)),
        ("space_rank_bool", _damaged(space, rank=True)),
        ("space_rows", _damaged(space, pivot_rows=(space.pivot_rows[0],) * space.rank)),
        ("space_columns", _damaged(space, pivot_columns=(space.pivot_columns[0],) * space.rank)),
        ("space_minor", _damaged(space, pivot_determinant=space.pivot_determinant + 1)),
        ("space_kernel", _damaged(space, kernel_basis=_alter_matrix(space.kernel_basis))),
        ("space_kernel_width", _damaged(space, kernel_basis=tuple(row[:-1] for row in space.kernel_basis))),
        ("space_schur_particular", _damaged(space, schur_particular=_alter_vector(space.schur_particular))),
        ("space_particular", _damaged(space, particular=_alter_vector(space.particular))),
        ("space_radial", _damaged(space, radial_correction=space.radial_correction + 1)),
        ("space_radial_float", _damaged(space, radial_correction=float(space.radial_correction))),
    ]
    invalid_certificates.extend(
        (label, chart, _damaged(compatible, affine_space=value)) for label, value in space_mutations
    )
    obstruction_mutations = [
        ("separator_missing", None),
        ("separator_zero", _damaged(obstruction, covector=tuple(Fraction(0) for _ in obstruction.covector))),
        ("separator_shape", _damaged(obstruction, covector=obstruction.covector[:-1])),
        ("separator_value", _damaged(obstruction, covector=_alter_vector(obstruction.covector))),
        ("separator_pairing", _damaged(obstruction, pairing=obstruction.pairing + 1)),
        ("separator_pairing_zero", _damaged(obstruction, pairing=Fraction(0))),
        ("separator_pairing_float", _damaged(obstruction, pairing=float(obstruction.pairing))),
    ]
    invalid_certificates.extend(
        (label, obstructed.chart, _damaged(obstructed, obstruction=value)) for label, value in obstruction_mutations
    )
    for label, actual_chart, damaged in invalid_certificates:
        _require(not verify_schur_acceleration_certificate(actual_chart, damaged), f"mutation accepted: {label}")
    return [label for label, _, _ in invalid_certificates]


def audit_schur_acceleration() -> dict[str, object]:
    """Check exact arbitrary-direction contracts, affine frames and bad inputs."""
    centers = parallel.ordered_map(
        _audit_center,
        [
            ("nullity4", {1: Fraction(1), 10: Fraction(1, 4), 18: Fraction(5, 8), 25: Fraction(1, 8)}, 4),
            ("nullity8", {1: 1, 10: 1}, 8),
            ("nullity12", {1: 1, 18: 1}, 12),
            ("nullity16", {1: 1, 10: 1, 18: 1, 25: -1}, 16),
        ],
        min_items=2,
    )
    center = _fixture({1: 1, 10: 1})
    chart = SkewSchurChart.from_certificate(rank_certificate(center))
    compatible = certify_schur_acceleration(chart, _fixture({3: 1}))
    _require(compatible.status == "second_order_compatible", "curved fixture loses its acceleration")
    _require(verify_acceleration_member(compatible, _fixture({1: -1})), "curved acceleration fails membership")
    _require(
        not verify_acceleration_member(compatible, _fixture({1: Fraction(-1, 2), 10: Fraction(-1, 2)})),
        "radial-only acceleration passes",
    )
    _require(not verify_acceleration_member(compatible, _fixture({})), "straight acceleration passes")
    _require(not verify_acceleration_member(compatible, _fixture({1: 1})), "reversed Schur sign passes")
    _require(not verify_acceleration_member(compatible, _fixture({1: Fraction(-1, 2)})), "missing factor two passes")
    quadratic = sp.Matrix(compatible.quadratic_term)
    _require((2 * quadratic).rank() == 8, "straight second derivative loses rank")
    rescalings = []
    for factor in (Fraction(-3, 2), Fraction(2, 3), Fraction(0)):
        scaled = certify_schur_acceleration(chart, _fixture({3: factor}), linearized=compatible.linearized)
        _require(scaled.status == "second_order_compatible", "direction rescaling changes compatibility")
        _require(
            verify_acceleration_member(scaled, _fixture({1: -(factor**2)})), "scaled acceleration fails quadratic law"
        )
        rescalings.append(str(factor))
    center_rescalings = []
    for factor in (Fraction(-3, 2), Fraction(2, 3)):
        scaled_chart = SkewSchurChart.from_certificate(rank_certificate(tuple(factor * value for value in center)))
        scaled = certify_schur_acceleration(scaled_chart, _fixture({3: 1}))
        _require(scaled.status == "second_order_compatible", "center rescaling changes curvature compatibility")
        _require(
            sp.Matrix(scaled.quadratic_term) == quadratic / factor, "center rescaling changes inverse quadratic law"
        )
        _require(verify_acceleration_member(scaled, _fixture({1: -1 / factor})), "inverse-scaled acceleration fails")
        combined = certify_schur_acceleration(scaled_chart, _fixture({3: factor}), linearized=scaled.linearized)
        _require(sp.Matrix(combined.quadratic_term) == factor * quadratic, "joint rescaling changes quadratic law")
        _require(verify_acceleration_member(combined, _fixture({1: -factor})), "joint-scaled acceleration fails")
        center_rescalings.append(str(factor))
    obstructed_chart = SkewSchurChart.from_certificate(rank_certificate(_fixture({1: 1, 18: 1})))
    obstructed = certify_schur_acceleration(obstructed_chart, _fixture({11: 1}))
    _require(obstructed.status == "second_order_obstructed", "e11 fixture loses its obstruction")
    entries = obstructed.linearized.upper_triangle_indices
    left, right = entries.index((0, 1)), entries.index((4, 5))
    _require(
        obstructed.system_matrix[left] == obstructed.system_matrix[right],
        "contradictory rows have different coefficients",
    )
    _require(
        obstructed.system_rhs[left] == 2 and obstructed.system_rhs[right] == -2, "contradictory rows lose opposite rhs"
    )
    _require(not verify_acceleration_member(obstructed, _fixture({})), "obstructed certificate admits an acceleration")
    mutations = _audit_mutations(chart, compatible, obstructed)
    invalid_inputs: list[tuple[str, Any]] = [
        ("dimension", [0] * 31),
        ("scalar", 3),
        ("text", "0" * 32),
        ("float", [0.0] * 32),
        ("boolean", [False] * 32),
        ("real_coordinate", _fixture({0: 1})),
        ("half_coordinate", _fixture({16: 1})),
    ]
    for label, direction in invalid_inputs:
        try:
            certify_schur_acceleration(chart, direction)
        except ValueError:
            pass
        else:
            raise RuntimeError(f"invalid direction accepted: {label}")
    invalid_parameters: Any = [0.0] * 23
    for label, operation in (
        (
            "damaged_chart",
            lambda: certify_schur_acceleration(
                replace(chart, complement=_alter_matrix(chart.complement)), _fixture({})
            ),
        ),
        (
            "damaged_derivative",
            lambda: certify_schur_acceleration(chart, _fixture({}), linearized=replace(compatible.linearized, rank=0)),
        ),
        ("obstructed_parameterization", lambda: obstructed.acceleration([])),
        ("parameter_dimension", lambda: compatible.acceleration([])),
        ("parameter_float", lambda: compatible.acceleration(invalid_parameters)),
    ):
        try:
            operation()
        except ValueError:
            invalid_inputs.append((label, None))
        else:
            raise RuntimeError(f"invalid operation accepted: {label}")
    return {
        "scope": (
            "exact formal second-order compatibility; actual curves, smooth strata and attachments "
            "require further proof"
        ),
        "centers": centers,
        "curved_acceleration": "-e1 at x0=e1+e10, h=e3",
        "straight_second_derivative_rank": int((2 * quadratic).rank()),
        "radial_only_acceleration_rejected": True,
        "direction_rescalings": rescalings,
        "nonzero_center_and_joint_rescalings": center_rescalings,
        "obstruction": {
            "center": "e1+e18",
            "direction": "e11",
            "rows": [[0, 1], [4, 5]],
            "shared_coefficient": "2(a1-a18)",
            "rhs": [2, -2],
            "status": obstructed.status,
        },
        "rejected_mutations": mutations,
        "rejected_inputs": [label for label, _ in invalid_inputs],
    }


if __name__ == "__main__":
    print(json.dumps(audit_schur_acceleration(), indent=2, sort_keys=True))
