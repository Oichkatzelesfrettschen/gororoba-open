"""Exact real quadratic-compatible velocities at the center e1+e18.

The Schur cokernel equations on the constant-norm first-order space have
real zero set A15 union B17, intersecting in dimension thirteen. The exact
rational evaluator describes formal second-order compatibility. Actual
curves, a tangent-cone equality and local topology require separate proofs.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Any, Literal

import sympy as sp

import parallel
from cd_core import cd_sign
from rank_charts import RationalMatrix, multiplication_matrix, rank_certificate
from skew_schur_charts import (
    COORDINATE_INDICES,
    DIMENSION,
    SkewSchurChart,
    _coordinates,
    _fraction,
    _indices,
    _kernel,
    _matrix,
    _rows,
    verify_skew_schur_chart,
)

TANGENT_DIMENSION = 21
CENTER = tuple(Fraction(int(index in (1, 18))) for index in range(DIMENSION))
RESIDUAL_INDICES = tuple((row, column) for row in range(12) for column in range(row + 1, 12))
MONOMIAL_PAIRS = tuple((index, index) for index in range(TANGENT_DIMENSION)) + tuple(
    (left, right) for left in range(TANGENT_DIMENSION) for right in range(left + 1, TANGENT_DIMENSION)
)
DirectionStatus = Literal["first_order_inadmissible", "second_order_obstructed", "second_order_compatible"]


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


@dataclass(frozen=True)
class ExactKernelFrame:
    """A nonzero rank minor and free-row identity prove a complete kernel."""

    basis: RationalMatrix
    pivot_rows: tuple[int, ...]
    pivot_columns: tuple[int, ...]
    pivot_determinant: Fraction


@dataclass(frozen=True)
class CoordinatePlane:
    name: str
    zero_coordinates: tuple[int, ...]

    @property
    def dimension(self) -> int:
        return TANGENT_DIMENSION - len(self.zero_coordinates)


@dataclass(frozen=True)
class NullityTwelveLocusCertificate:
    chart: SkewSchurChart
    coordinate_indices: tuple[int, ...]
    residual_indices: tuple[tuple[int, int], ...]
    derivative_matrix: RationalMatrix
    tangent_frame: ExactKernelFrame
    cokernel_frame: ExactKernelFrame
    ambient_tangent_basis: RationalMatrix
    monomial_pairs: tuple[tuple[int, int], ...]
    coefficient_matrix: RationalMatrix
    generator_matrix: RationalMatrix
    reconstruction_matrix: RationalMatrix
    rank_minor_rows: tuple[int, ...]
    rank_minor_columns: tuple[int, ...]
    rank_minor_determinant: Fraction
    first_sos_weights: tuple[Fraction, ...]
    forced_zero_coordinates: tuple[int, ...]
    second_sos_rows: tuple[int, ...]
    factor_coordinates: tuple[tuple[int, ...], ...]
    planes: tuple[CoordinatePlane, ...]

    @property
    def intersection_dimension(self) -> int:
        return TANGENT_DIMENSION - len(set().union(*(plane.zero_coordinates for plane in self.planes)))


@dataclass(frozen=True)
class NullityTwelveDirection:
    """Exact rational membership, scoped to formal second-order solvability."""

    direction: tuple[Fraction, ...]
    status: DirectionStatus
    tangent_coordinates: tuple[Fraction, ...] | None
    quadratic_values: tuple[Fraction, ...] | None
    components: tuple[str, ...]


def _frame(matrix: sp.Matrix) -> ExactKernelFrame:
    kernel, columns = _kernel(matrix)
    rows = tuple(int(index) for index in matrix[:, list(columns)].T.rref()[1])
    return ExactKernelFrame(_rows(kernel), rows, columns, _fraction(matrix.extract(rows, columns).det()))


def _verify_frame(matrix: sp.Matrix, frame: ExactKernelFrame, rank: int) -> bool:
    if not isinstance(frame, ExactKernelFrame) or type(frame.pivot_determinant) is not Fraction:
        return False
    rows = _indices(frame.pivot_rows, matrix.rows)
    columns = _indices(frame.pivot_columns, matrix.cols)
    if len(rows) != rank or len(columns) != rank:
        return False
    free = tuple(index for index in range(matrix.cols) if index not in columns)
    kernel = _matrix(frame.basis, matrix.cols, matrix.cols - rank)
    determinant = matrix.extract(rows, columns).det()
    return bool(
        determinant != 0
        and determinant == frame.pivot_determinant
        and columns == tuple(matrix.rref()[1])
        and kernel.extract(free, range(len(free))) == sp.eye(len(free))
        and matrix * kernel == sp.zeros(matrix.rows, len(free))
    )


def _ambient(tangent: sp.Matrix) -> sp.Matrix:
    result = sp.zeros(DIMENSION, tangent.cols)
    for position, coordinate in enumerate(COORDINATE_INDICES):
        result[coordinate, :] = tangent[position, :]
    return result


def _direct_operator(values: Sequence[Any]) -> sp.Matrix:
    """Reconstruct left multiplication independently of multiplication_matrix."""
    return sp.Matrix(
        DIMENSION,
        DIMENSION,
        lambda row, column: cd_sign(DIMENSION, row ^ column, column) * values[row ^ column],
    )


def _quadratic_column(
    task: tuple[RationalMatrix, RationalMatrix, RationalMatrix, RationalMatrix, bool],
) -> RationalMatrix:
    left, right, inverse_left, inverse_right, mixed = task
    quadratic = sp.Matrix(left).T * sp.Matrix(inverse_right)
    if mixed:
        quadratic += sp.Matrix(right).T * sp.Matrix(inverse_left)
    return _rows(sp.Matrix([quadratic[row, column] for row, column in RESIDUAL_INDICES]))


def _projected_coefficients(crosses: list[sp.Matrix], inverse: sp.Matrix, cokernel: sp.Matrix) -> sp.Matrix:
    solved = [inverse * cross for cross in crosses]
    cross_rows = [_rows(cross) for cross in crosses]
    solved_rows = [_rows(solution) for solution in solved]
    columns = parallel.ordered_map(
        _quadratic_column,
        [
            (cross_rows[left], cross_rows[right], solved_rows[left], solved_rows[right], left != right)
            for left, right in MONOMIAL_PAIRS
        ],
    )
    return cokernel.T * sp.Matrix.hstack(*(sp.Matrix(column) for column in columns))


def _form_row(task: tuple[RationalMatrix, tuple[RationalMatrix, ...], tuple[Fraction, ...]]) -> tuple[Fraction, ...]:
    inverse_rows, output_columns, covector = task
    inverse = sp.Matrix(inverse_rows)
    form = sp.zeros(TANGENT_DIMENSION)
    for value, (left, right) in zip(covector, RESIDUAL_INDICES, strict=True):
        if value:
            form += value * sp.Matrix(output_columns[left]).T * inverse * sp.Matrix(output_columns[right])
    return tuple(
        _fraction(form[left, right] if left == right else form[left, right] + form[right, left])
        for left, right in MONOMIAL_PAIRS
    )


def _independent_coefficients(crosses: list[sp.Matrix], inverse: sp.Matrix, cokernel: sp.Matrix) -> sp.Matrix:
    """Expand one cokernel quadratic form per row, rather than polarize columns."""
    output_columns = tuple(_rows(sp.Matrix.hstack(*(cross[:, output] for cross in crosses))) for output in range(12))
    tasks = [
        (_rows(inverse), output_columns, tuple(_fraction(value) for value in cokernel[:, column]))
        for column in range(cokernel.cols)
    ]
    return sp.Matrix(parallel.ordered_map(_form_row, tasks, min_items=8))


def _canonical_quadrics(variables: tuple[sp.Symbol, ...]) -> tuple[sp.Expr, ...]:
    z = variables
    return (
        z[6] ** 2 - z[16] ** 2,
        z[5] * z[6] - z[13] * z[16],
        z[13] * z[6] + z[16] * z[5],
        z[17] * z[5] - z[13] * z[20] + z[16] * z[17] + z[20] * z[6],
        z[13] * z[19] + z[18] * z[5] + z[16] * z[18] - z[19] * z[6],
        z[19] * z[5] - z[13] * z[18] + z[16] * z[19] + z[18] * z[6],
        z[13] * z[17] + z[20] * z[5] + z[16] * z[20] - z[17] * z[6],
        z[16] * z[6],
    )


def certify_nullity_twelve_locus() -> NullityTwelveLocusCertificate:
    """Derive every quadratic coefficient and certify its full real zero set."""
    chart = SkewSchurChart.from_certificate(rank_certificate(CENTER))
    complement, kernel = sp.Matrix(chart.complement), sp.Matrix(chart.kernel)
    derivative_columns = []
    for coordinate in COORDINATE_INDICES:
        operator = sp.Matrix(multiplication_matrix(tuple(int(index == coordinate) for index in range(DIMENSION))))
        diagonal = kernel.T * operator * kernel
        derivative_columns.append(sp.Matrix([diagonal[row, column] for row, column in RESIDUAL_INDICES]))
    derivative = sp.Matrix.hstack(*derivative_columns)
    radial = sp.Matrix(1, 30, [CENTER[index] for index in COORDINATE_INDICES])
    tangent_frame = _frame(derivative.col_join(radial))
    cokernel_frame = _frame(derivative.T)
    ambient = _ambient(sp.Matrix(tangent_frame.basis))
    crosses = [
        complement.T
        * sp.Matrix(multiplication_matrix(tuple(_fraction(value) for value in ambient[:, column])))
        * kernel
        for column in range(TANGENT_DIMENSION)
    ]
    pivot = complement.T * sp.Matrix(multiplication_matrix(CENTER)) * complement
    coefficients = _projected_coefficients(crosses, pivot.inv(), sp.Matrix(cokernel_frame.basis))
    reduced, columns = coefficients.rref()
    rows = tuple(int(index) for index in coefficients.T.rref()[1])
    certificate = NullityTwelveLocusCertificate(
        chart=chart,
        coordinate_indices=COORDINATE_INDICES,
        residual_indices=RESIDUAL_INDICES,
        derivative_matrix=_rows(derivative),
        tangent_frame=tangent_frame,
        cokernel_frame=cokernel_frame,
        ambient_tangent_basis=_rows(ambient),
        monomial_pairs=MONOMIAL_PAIRS,
        coefficient_matrix=_rows(coefficients),
        generator_matrix=_rows(reduced[:8, :]),
        reconstruction_matrix=_rows(coefficients[:, list(columns)]),
        rank_minor_rows=rows,
        rank_minor_columns=tuple(int(index) for index in columns),
        rank_minor_determinant=_fraction(coefficients.extract(rows, columns).det()),
        first_sos_weights=(Fraction(1), *(Fraction(0) for _ in range(6)), Fraction(4)),
        forced_zero_coordinates=(6, 16),
        second_sos_rows=(3, 4, 5, 6),
        factor_coordinates=((5, 13), (17, 18, 19, 20)),
        planes=(CoordinatePlane("A15", (6, 16, 17, 18, 19, 20)), CoordinatePlane("B17", (5, 6, 13, 16))),
    )
    _require(verify_nullity_twelve_locus(certificate), "constructed quadratic-locus certificate fails verification")
    return certificate


def _pairs(values: tuple[tuple[int, int], ...], expected: tuple[tuple[int, int], ...]) -> bool:
    return bool(
        isinstance(values, tuple)
        and all(
            isinstance(pair, tuple) and len(pair) == 2 and all(type(index) is int for index in pair) for pair in values
        )
        and values == expected
    )


def _verify_real_locus(certificate: NullityTwelveLocusCertificate, generators: sp.Matrix) -> bool:
    variables = tuple(sp.Symbol(f"z{index}", real=True) for index in range(TANGENT_DIMENSION))
    monomials = sp.Matrix([variables[left] * variables[right] for left, right in MONOMIAL_PAIRS])
    polynomials = tuple(sp.expand(value) for value in generators * monomials)
    if polynomials != tuple(sp.expand(value) for value in _canonical_quadrics(variables)):
        return False
    if (
        not isinstance(certificate.first_sos_weights, tuple)
        or len(certificate.first_sos_weights) != 8
        or any(type(value) is not Fraction for value in certificate.first_sos_weights)
        or certificate.first_sos_weights != (Fraction(1), *(Fraction(0) for _ in range(6)), Fraction(4))
        or _indices(certificate.forced_zero_coordinates, TANGENT_DIMENSION) != (6, 16)
        or _indices(certificate.second_sos_rows, 8) != (3, 4, 5, 6)
        or not isinstance(certificate.factor_coordinates, tuple)
        or len(certificate.factor_coordinates) != 2
        or tuple(_indices(group, TANGENT_DIMENSION) for group in certificate.factor_coordinates)
        != ((5, 13), (17, 18, 19, 20))
        or not isinstance(certificate.planes, tuple)
        or len(certificate.planes) != 2
    ):
        return False
    forced = certificate.forced_zero_coordinates
    first_sum = sum(
        weight * polynomial**2 for weight, polynomial in zip(certificate.first_sos_weights, polynomials, strict=True)
    )
    if sp.expand(first_sum - sum(variables[index] ** 2 for index in forced) ** 2) != 0:
        return False
    reduced = tuple(sp.expand(value.subs({variables[index]: 0 for index in forced})) for value in polynomials)
    if any(reduced[index] != 0 for index in range(8) if index not in certificate.second_sos_rows):
        return False
    product = sp.prod(sum(variables[index] ** 2 for index in group) for group in certificate.factor_coordinates)
    if sp.expand(sum(reduced[index] ** 2 for index in certificate.second_sos_rows) - product) != 0:
        return False
    expected_planes = (CoordinatePlane("A15", (6, 16, 17, 18, 19, 20)), CoordinatePlane("B17", (5, 6, 13, 16)))
    for plane, expected in zip(certificate.planes, expected_planes, strict=True):
        if (
            not isinstance(plane, CoordinatePlane)
            or type(plane.name) is not str
            or _indices(plane.zero_coordinates, TANGENT_DIMENSION) != expected.zero_coordinates
            or plane.name != expected.name
        ):
            return False
        if any(
            sp.expand(value.subs({variables[index]: 0 for index in plane.zero_coordinates})) != 0
            for value in polynomials
        ):
            return False
    return certificate.intersection_dimension == 13


def verify_nullity_twelve_locus(certificate: NullityTwelveLocusCertificate) -> bool:
    """Rebuild exact operators, frames and all coefficients without the constructor.

    Rank minors and reconstruction certify complete equation coverage. Two
    polynomial sum-of-squares identities and coordinate-plane inclusions
    certify the real zero set; finite rational samples play no role in that
    symbolic identity check.
    """
    try:
        if not isinstance(certificate, NullityTwelveLocusCertificate):
            return False
        if not verify_skew_schur_chart(certificate.chart):
            return False
        chart = certificate.chart
        if chart.center_certificate.coordinates != CENTER or chart.reduced_dimension != 12:
            return False
        if (
            _indices(certificate.coordinate_indices, DIMENSION) != COORDINATE_INDICES
            or not _pairs(certificate.residual_indices, RESIDUAL_INDICES)
            or not _pairs(certificate.monomial_pairs, MONOMIAL_PAIRS)
            or type(certificate.rank_minor_determinant) is not Fraction
        ):
            return False
        derivative = _matrix(certificate.derivative_matrix, 66, 30)
        tangent = _matrix(certificate.tangent_frame.basis, 30, 21)
        cokernel = _matrix(certificate.cokernel_frame.basis, 66, 58)
        ambient = _matrix(certificate.ambient_tangent_basis, DIMENSION, 21)
        coefficients = _matrix(certificate.coefficient_matrix, 58, 231)
        generators = _matrix(certificate.generator_matrix, 8, 231)
        reconstruction = _matrix(certificate.reconstruction_matrix, 58, 8)
        rows = _indices(certificate.rank_minor_rows, 58)
        columns = _indices(certificate.rank_minor_columns, 231)
        if len(rows) != 8 or len(columns) != 8 or not _verify_real_locus(certificate, generators):
            return False
        determinant = coefficients.extract(rows, columns).det()
        if not (
            determinant != 0
            and determinant == certificate.rank_minor_determinant
            and generators[:, list(columns)] == sp.eye(8)
            and reconstruction == coefficients[:, list(columns)]
            and reconstruction * generators == coefficients
        ):
            return False
        complement, kernel = sp.Matrix(chart.complement), sp.Matrix(chart.kernel)
        expected_columns = []
        for coordinate in COORDINATE_INDICES:
            operator = _direct_operator(tuple(int(index == coordinate) for index in range(DIMENSION)))
            block = kernel.T * operator * kernel
            expected_columns.append(sp.Matrix([block[row, column] for row, column in RESIDUAL_INDICES]))
        if derivative != sp.Matrix.hstack(*expected_columns):
            return False
        radial = sp.Matrix(1, 30, [CENTER[index] for index in COORDINATE_INDICES])
        if not (
            _verify_frame(derivative.col_join(radial), certificate.tangent_frame, 9)
            and _verify_frame(derivative.T, certificate.cokernel_frame, 8)
            and ambient == _ambient(tangent)
            and derivative * radial.T == sp.zeros(66, 1)
            and (radial * radial.T)[0] == 2
        ):
            return False
        pivot = complement.T * _direct_operator(CENTER) * complement
        crosses = [complement.T * _direct_operator(ambient[:, column]) * kernel for column in range(TANGENT_DIMENSION)]
        return coefficients == _independent_coefficients(crosses, pivot.inv(), cokernel)
    except (ValueError, TypeError, AttributeError, IndexError, ZeroDivisionError):
        return False


def classify_nullity_twelve_direction(
    certificate: NullityTwelveLocusCertificate, direction: Sequence[int | Fraction]
) -> NullityTwelveDirection:
    """Classify a rational direction for formal constant-norm acceleration.

    Fractions and integers are accepted; floating-point and Boolean entries
    are rejected. Compatibility makes no claim about actual curve existence.
    """
    values = _coordinates(direction, allow_zero=True)
    if not verify_nullity_twelve_locus(certificate):
        raise ValueError("direction classification requires a verified quadratic-locus certificate")
    coefficients = sp.Matrix([values[index] for index in COORDINATE_INDICES])
    derivative = sp.Matrix(certificate.derivative_matrix)
    radial = sp.Matrix(1, 30, [CENTER[index] for index in COORDINATE_INDICES])
    if derivative.col_join(radial) * coefficients != sp.zeros(67, 1):
        return NullityTwelveDirection(values, "first_order_inadmissible", None, None, ())
    free = tuple(index for index in range(30) if index not in certificate.tangent_frame.pivot_columns)
    tangent_coordinates = tuple(_fraction(coefficients[index]) for index in free)
    monomials = sp.Matrix([tangent_coordinates[left] * tangent_coordinates[right] for left, right in MONOMIAL_PAIRS])
    quadratic_values = tuple(_fraction(value) for value in sp.Matrix(certificate.generator_matrix) * monomials)
    components = tuple(
        plane.name
        for plane in certificate.planes
        if all(tangent_coordinates[index] == 0 for index in plane.zero_coordinates)
    )
    status: DirectionStatus = "second_order_compatible" if components else "second_order_obstructed"
    _require(
        bool(components) == all(value == 0 for value in quadratic_values),
        "coordinate-plane membership differs from quadrics",
    )
    return NullityTwelveDirection(values, status, tangent_coordinates, quadratic_values, components)


def symbolic_nullity_twelve_quadrics(
    certificate: NullityTwelveLocusCertificate,
) -> tuple[tuple[sp.Symbol, ...], tuple[sp.Expr, ...]]:
    """Return checked polynomial identities on arbitrary real tangent coordinates."""
    if not verify_nullity_twelve_locus(certificate):
        raise ValueError("symbolic equations require a verified quadratic-locus certificate")
    variables = tuple(sp.Symbol(f"z{index}", real=True) for index in range(TANGENT_DIMENSION))
    monomials = sp.Matrix([variables[left] * variables[right] for left, right in MONOMIAL_PAIRS])
    return variables, tuple(sp.expand(value) for value in sp.Matrix(certificate.generator_matrix) * monomials)


def _alter_matrix(matrix: RationalMatrix) -> RationalMatrix:
    return ((matrix[0][0] + 1, *matrix[0][1:]), *matrix[1:])


def _damaged(value: Any, **fields: Any) -> Any:
    return replace(value, **fields)


def _reject_mutation(task: tuple[str, Any]) -> str:
    label, damaged = task
    _require(not verify_nullity_twelve_locus(damaged), f"invalid certificate accepted: {label}")
    return str(label)


def audit_nullity_twelve_locus() -> dict[str, object]:
    """Audit symbolic completeness, exact membership, and fail-closed inputs."""
    certificate = certify_nullity_twelve_locus()
    mutations: list[tuple[str, Any]] = [("certificate_type", None)]
    for field in (
        "derivative_matrix",
        "ambient_tangent_basis",
        "coefficient_matrix",
        "generator_matrix",
        "reconstruction_matrix",
    ):
        values = getattr(certificate, field)
        mutations.extend(
            [
                (f"{field}_value", _damaged(certificate, **{field: _alter_matrix(values)})),
                (f"{field}_shape", _damaged(certificate, **{field: values[:-1]})),
                (f"{field}_mutable", _damaged(certificate, **{field: list(values)})),
                (
                    f"{field}_float",
                    _damaged(certificate, **{field: ((float(values[0][0]), *values[0][1:]), *values[1:])}),
                ),
            ]
        )
    for field in ("tangent_frame", "cokernel_frame"):
        frame = getattr(certificate, field)
        for label, damaged in (
            ("basis", _damaged(frame, basis=_alter_matrix(frame.basis))),
            ("minor", _damaged(frame, pivot_determinant=frame.pivot_determinant + 1)),
            ("columns", _damaged(frame, pivot_columns=frame.pivot_columns[:-1])),
            ("rows", _damaged(frame, pivot_rows=(frame.pivot_rows[0],) * len(frame.pivot_rows))),
        ):
            mutations.append((f"{field}_{label}", _damaged(certificate, **{field: damaged})))
    mutations.extend(
        [
            (
                "chart",
                _damaged(
                    certificate, chart=_damaged(certificate.chart, kernel=_alter_matrix(certificate.chart.kernel))
                ),
            ),
            ("coordinate_order", _damaged(certificate, coordinate_indices=tuple(reversed(COORDINATE_INDICES)))),
            ("residual_order", _damaged(certificate, residual_indices=tuple(reversed(RESIDUAL_INDICES)))),
            ("monomial_missing", _damaged(certificate, monomial_pairs=MONOMIAL_PAIRS[:-1])),
            ("monomial_order", _damaged(certificate, monomial_pairs=tuple(reversed(MONOMIAL_PAIRS)))),
            ("rank_minor", _damaged(certificate, rank_minor_determinant=Fraction(0))),
            ("rank_minor_rows", _damaged(certificate, rank_minor_rows=(0,) * 8)),
            ("rank_minor_columns", _damaged(certificate, rank_minor_columns=(0,) * 8)),
            ("sos_weight", _damaged(certificate, first_sos_weights=(Fraction(0),) * 8)),
            ("sos_boolean", _damaged(certificate, first_sos_weights=(True, *certificate.first_sos_weights[1:]))),
            ("forced_coordinates", _damaged(certificate, forced_zero_coordinates=(5, 16))),
            ("second_sos", _damaged(certificate, second_sos_rows=(2, 3, 4, 5))),
            ("sos_factors", _damaged(certificate, factor_coordinates=((5, 13), (17, 18, 19)))),
            ("plane_missing", _damaged(certificate, planes=certificate.planes[:1])),
            ("plane_enlarged", _damaged(certificate, planes=(CoordinatePlane("A15", (6, 16)), certificate.planes[1]))),
        ]
    )
    rejected = parallel.ordered_map(_reject_mutation, mutations, min_items=4)
    fixtures: tuple[tuple[str, dict[int, Fraction], DirectionStatus, tuple[str, ...]], ...] = (
        ("zero", {}, "second_order_compatible", ("A15", "B17")),
        ("A15", {8: Fraction(2, 3)}, "second_order_compatible", ("A15",)),
        ("B17", {15: Fraction(-3, 2), 28: Fraction(-3, 2)}, "second_order_compatible", ("B17",)),
        ("intersection", {3: Fraction(5, 7)}, "second_order_compatible", ("A15", "B17")),
        ("component_sum", {8: Fraction(1), 15: Fraction(1), 28: Fraction(1)}, "second_order_obstructed", ()),
        ("quadratic_obstruction", {11: Fraction(1)}, "second_order_obstructed", ()),
        ("radial", {1: Fraction(1), 18: Fraction(1)}, "first_order_inadmissible", ()),
        ("linear_schur", {2: Fraction(1)}, "first_order_inadmissible", ()),
    )
    membership = []
    for label, entries, expected_status, expected_components in fixtures:
        direction = tuple(entries.get(index, Fraction(0)) for index in range(DIMENSION))
        result = classify_nullity_twelve_direction(certificate, direction)
        _require(
            result.status == expected_status and result.components == expected_components, f"membership fails: {label}"
        )
        membership.append({"label": label, "status": result.status, "components": list(result.components)})
    invalid_inputs: list[tuple[str, Any]] = [
        ("scalar", 0),
        ("dimension", [0] * 31),
        ("float", [0.0] * 32),
        ("boolean", [False] * 32),
        ("text", "0" * 32),
        ("real_part", [1] + [0] * 31),
        ("half_part", [0] * 16 + [1] + [0] * 15),
    ]
    for label, direction in invalid_inputs:
        try:
            classify_nullity_twelve_direction(certificate, direction)
        except ValueError:
            pass
        else:
            raise RuntimeError(f"invalid direction accepted: {label}")
    return {
        "scope": "complete real formal second-order compatible velocity locus at e1+e18",
        "center_nullity": 12,
        "derivative_rank": len(certificate.cokernel_frame.pivot_columns),
        "constant_norm_linear_rank": len(certificate.tangent_frame.pivot_columns),
        "tangent_dimension": TANGENT_DIMENSION,
        "quadratic_coefficient_shape": [58, len(MONOMIAL_PAIRS)],
        "quadratic_rank": len(certificate.rank_minor_columns),
        "rank_minor_rows": list(certificate.rank_minor_rows),
        "rank_minor_columns": list(certificate.rank_minor_columns),
        "rank_minor_determinant": str(certificate.rank_minor_determinant),
        "planes": [
            {"name": plane.name, "zero_coordinates": list(plane.zero_coordinates), "dimension": plane.dimension}
            for plane in certificate.planes
        ],
        "intersection_dimension": certificate.intersection_dimension,
        "symbolic_real_zero_locus_verified": True,
        "membership": membership,
        "rejected_mutations": rejected,
        "rejected_inputs": [label for label, _ in invalid_inputs],
        "boundary": (
            "actual curves, tangent-cone equality, local stratum classification and topology require separate proofs"
        ),
    }


def main() -> int:
    print(json.dumps(audit_nullity_twelve_locus(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
