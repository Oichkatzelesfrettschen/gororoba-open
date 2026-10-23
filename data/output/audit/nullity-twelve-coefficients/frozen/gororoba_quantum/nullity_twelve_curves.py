"""Exact rational slices and real curve witnesses through e1+e18.

A four-parameter slice has constant nullity twelve on k != +/-1. Its
positive real normalization is sqrt(2 / norm_squared). Exact polynomial
kernel identities certify the external block; the embedded sedenion block
uses the published equal-norm orthogonal imaginary-factor theorem. Skew
Leibniz derivations supply eleven orbit directions, completing the A15
velocity plane. These local witnesses do not classify nearby rank strata.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from dataclasses import dataclass, replace
from fractions import Fraction
from itertools import combinations
from typing import Any

import sympy as sp
from sympy.polys.polyerrors import BasePolynomialError

import parallel
from cd_core import cd_sign
from nullity_twelve_locus import CENTER
from rank_charts import (
    RankCertificate,
    RationalMatrix,
    rank_certificate,
    verify_rank_certificate,
)
from skew_schur_charts import (
    COORDINATE_INDICES,
    SkewSchurChart,
    _fraction,
    _indices,
    _kernel,
    _matrix,
    _rational,
    _rows,
)

BETA, DELTA, KAPPA, PHASE = sp.symbols("beta delta k f", real=True)
POLYNOMIAL_VARIABLES = (BETA, DELTA, KAPPA)
SLICE_SUPPORT = (1, 2, 8, 9, 10, 17, 18, 24, 25, 26)
INTERNAL_INDICES = tuple(index for index in range(32) if not index & 4)
EXTERNAL_INDICES = tuple(index for index in range(32) if index & 4)
DERIVATION_PAIRS = tuple(combinations(range(1, 8), 2))
SymbolicMatrix = tuple[tuple[sp.Expr, ...], ...]


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def _operator(values: Sequence[Any], indices: tuple[int, ...] = tuple(range(32))) -> sp.Matrix:
    return sp.Matrix(
        len(indices),
        len(indices),
        lambda row, column: (
            cd_sign(32, indices[row] ^ indices[column], indices[column]) * values[indices[row] ^ indices[column]]
        ),
    )


def _symbolic_rows(matrix: sp.Matrix) -> SymbolicMatrix:
    return tuple(tuple(matrix[row, column] for column in range(matrix.cols)) for row in range(matrix.rows))


def _polynomial(value: sp.Expr) -> bool:
    try:
        return bool(
            isinstance(value, sp.Expr)
            and not value.atoms(sp.Float)
            and value.free_symbols <= set(POLYNOMIAL_VARIABLES)
            and sp.Poly(value, *POLYNOMIAL_VARIABLES, domain=sp.QQ).domain == sp.QQ
        )
    except (BasePolynomialError, TypeError, ValueError, AttributeError):
        return False


def _symbolic_matrix(rows: SymbolicMatrix, height: int, width: int) -> sp.Matrix:
    if (
        not isinstance(rows, tuple)
        or len(rows) != height
        or any(not isinstance(row, tuple) or len(row) != width for row in rows)
        or any(not _polynomial(value) for row in rows for value in row)
    ):
        raise ValueError("symbolic matrices require immutable exact rational polynomial entries")
    return sp.Matrix(rows)


def _zero(matrix: sp.Matrix) -> bool:
    return all(sp.Poly(value, *POLYNOMIAL_VARIABLES, domain=sp.QQ).is_zero for value in matrix)


def _base_numerator(beta: Any, delta: Any, crossing: Any) -> tuple[sp.Matrix, Any]:
    denominator = 4 * (1 - crossing**2)
    first = denominator * sp.eye(2) - sp.Matrix(
        [[beta**2 - delta**2, 2 * beta * delta], [2 * beta * delta, delta**2 - beta**2]]
    )
    rotation = sp.Matrix([[0, 1], [-1, 0]])
    second = -crossing * denominator * rotation - crossing * sp.Matrix(
        [[-2 * beta * delta, beta**2 - delta**2], [beta**2 - delta**2, 2 * beta * delta]]
    )
    vector = sp.zeros(32, 1)
    for row in range(2):
        for column in range(2):
            vector[16 * row + 1 + column] = first[row, column]
            vector[16 * row + 9 + column] = second[row, column]
    vector[8], vector[24] = beta * denominator, delta * denominator
    return vector, denominator


def _phase_vector(vector: sp.Matrix, phase: Any) -> sp.Matrix:
    cosine, sine = (1 - phase**2) / (1 + phase**2), 2 * phase / (1 + phase**2)
    result = vector.copy()
    for first, second in ((1, 9), (2, 10), (17, 25), (18, 26)):
        result[first] = cosine * vector[first] - sine * vector[second]
        result[second] = sine * vector[first] + cosine * vector[second]
    return result


def _norm_formula(beta: Any, delta: Any, crossing: Any) -> Any:
    radius_squared = beta**2 + delta**2
    return 2 * (1 + crossing**2) + radius_squared + (1 + crossing**2) * radius_squared**2 / (8 * (1 - crossing**2) ** 2)


@dataclass(frozen=True)
class NullityTwelveSlicePoint:
    """An unnormalized rational point; real normalization multiplies by sqrt(2/norm_squared)."""

    parameters: tuple[Fraction, ...]
    coordinates: tuple[Fraction, ...]
    norm_squared: Fraction
    rank_certificate: RankCertificate


def nullity_twelve_slice(
    beta: int | Fraction, delta: int | Fraction, k: int | Fraction, f: int | Fraction
) -> NullityTwelveSlicePoint:
    """Return an exact rational nullity-twelve point for crossing != +/-1.

    The rational phase uses cos=(1-f^2)/(1+f^2), sin=2f/(1+f^2).
    The real normalization is smooth and positive on the declared domain;
    normalized coordinates can be irrational and remain outside this API.
    """
    values = tuple(_rational(value) for value in (beta, delta, k, f))
    if values[2] in (Fraction(-1), Fraction(1)):
        raise ValueError("the slice domain excludes crossing equal to +/-1")
    numerator, denominator = _base_numerator(*values[:3])
    coordinates = tuple(_fraction(sp.cancel(value)) for value in _phase_vector(numerator / denominator, values[3]))
    norm_squared = sum((value**2 for value in coordinates), Fraction(0))
    result = NullityTwelveSlicePoint(values, coordinates, norm_squared, rank_certificate(coordinates))
    _require(verify_nullity_twelve_slice(result), "constructed rational slice point fails verification")
    return result


def verify_nullity_twelve_slice(point: NullityTwelveSlicePoint) -> bool:
    try:
        if (
            not isinstance(point, NullityTwelveSlicePoint)
            or not isinstance(point.parameters, tuple)
            or len(point.parameters) != 4
            or any(type(value) is not Fraction for value in point.parameters)
            or not isinstance(point.coordinates, tuple)
            or len(point.coordinates) != 32
            or any(type(value) is not Fraction for value in point.coordinates)
            or type(point.norm_squared) is not Fraction
        ):
            return False
        beta, delta, crossing, phase = point.parameters
        if crossing in (Fraction(-1), Fraction(1)):
            return False
        numerator, denominator = _base_numerator(beta, delta, crossing)
        expected = _phase_vector(numerator / denominator, phase)
        return bool(
            sp.Matrix(point.coordinates) == expected
            and point.norm_squared > 0
            and point.norm_squared == _norm_formula(beta, delta, crossing)
            and sum(value**2 for value in point.coordinates) == point.norm_squared
            and verify_rank_certificate(point.coordinates, point.rank_certificate)
            and point.rank_certificate.side == "left"
            and point.rank_certificate.nullity == 12
        )
    except (ValueError, TypeError, AttributeError, IndexError, ZeroDivisionError):
        return False


@dataclass(frozen=True)
class ExactColumnSpan:
    pivot_rows: tuple[int, ...]
    pivot_columns: tuple[int, ...]
    determinant: Fraction
    reconstruction: RationalMatrix


def _column_span(matrix: sp.Matrix) -> ExactColumnSpan:
    columns = tuple(int(index) for index in matrix.rref()[1])
    basis = matrix[:, list(columns)]
    rows = tuple(int(index) for index in basis.T.rref()[1])
    minor = basis[list(rows), :]
    reconstruction = minor.inv() * matrix[list(rows), :]
    return ExactColumnSpan(rows, columns, _fraction(minor.det()), _rows(reconstruction))


def _verify_span(matrix: sp.Matrix, certificate: ExactColumnSpan, rank: int) -> bool:
    if not isinstance(certificate, ExactColumnSpan) or type(certificate.determinant) is not Fraction:
        return False
    rows = _indices(certificate.pivot_rows, matrix.rows)
    columns = _indices(certificate.pivot_columns, matrix.cols)
    if len(rows) != rank or len(columns) != rank:
        return False
    reconstruction = _matrix(certificate.reconstruction, rank, matrix.cols)
    basis = matrix[:, list(columns)]
    return bool(
        certificate.determinant != 0
        and basis[list(rows), :].det() == certificate.determinant
        and basis * reconstruction == matrix
        and reconstruction[:, list(columns)] == sp.eye(rank)
    )


def _octonion_basis_operator(index: int, *, right: bool = False) -> sp.Matrix:
    return sp.Matrix(
        8,
        8,
        lambda row, column: (
            (cd_sign(8, column, index) if right else cd_sign(8, index, column)) if row == index ^ column else 0
        ),
    )


def _derivation(pair: tuple[int, int]) -> sp.Matrix:
    first, second = pair
    left_first, left_second = _octonion_basis_operator(first), _octonion_basis_operator(second)
    right_first, right_second = (
        _octonion_basis_operator(first, right=True),
        _octonion_basis_operator(second, right=True),
    )
    return (
        left_first * left_second
        - left_second * left_first
        + left_first * right_second
        - right_second * left_first
        + right_first * right_second
        - right_second * right_first
    )


def _verify_leibniz(rows: RationalMatrix) -> bool:
    """Check the repeated octonion derivation on all 32-dimensional basis products."""
    derivation = _matrix(rows, 8, 8)
    if derivation + derivation.T != sp.zeros(8) or derivation[:, 0] != sp.zeros(8, 1):
        return False
    extended = _rows(sp.diag(derivation, derivation, derivation, derivation))
    columns = [
        tuple((row, extended[row][column]) for row in range(32) if extended[row][column]) for column in range(32)
    ]
    for first in range(32):
        for second in range(32):
            residual = [Fraction(0)] * 32
            for row, value in columns[first ^ second]:
                residual[row] += cd_sign(32, first, second) * value
            for row, value in columns[first]:
                residual[row ^ second] -= value * cd_sign(32, row, second)
            for row, value in columns[second]:
                residual[first ^ row] -= value * cd_sign(32, first, row)
            if any(residual):
                return False
    return True


def _external_basis_operator(index: int) -> sp.Matrix:
    return _operator(tuple(int(position == index) for position in range(32)), EXTERNAL_INDICES)


def _phase_generator() -> sp.Matrix:
    return -_external_basis_operator(9) * _external_basis_operator(1) / 2


def _verify_phase(generator: sp.Matrix) -> bool:
    if generator + generator.T != sp.zeros(16) or generator * generator != -sp.eye(16) / 4:
        return False
    for first, second in ((1, 9), (2, 10), (17, 25), (18, 26)):
        left, right = _external_basis_operator(first), _external_basis_operator(second)
        if (
            generator * left - left * generator != right
            or generator * right - right * generator != -left
            or 4 * generator * left * generator != left
            or 4 * generator * right * generator != right
        ):
            return False
    for scalar in (8, 24):
        operator = _external_basis_operator(scalar)
        if generator * operator != operator * generator or -4 * generator * operator * generator != operator:
            return False
    return True


def _external_frames() -> tuple[sp.Matrix, sp.Matrix]:
    center = _operator(CENTER, EXTERNAL_INDICES)
    kernel, columns = _kernel(center)
    return sp.eye(16)[:, list(columns)], kernel


def _expected_denominator() -> sp.Expr:
    negative = BETA**2 + DELTA**2 + 4 * (KAPPA - 1) ** 2
    positive = BETA**2 + DELTA**2 + 4 * (KAPPA + 1) ** 2
    return (KAPPA - 1) * (KAPPA + 1) * negative**2 * positive**2


def _slice_differential() -> sp.Matrix:
    numerator, denominator = _base_numerator(BETA, DELTA, KAPPA)
    vector = _phase_vector(numerator / denominator, PHASE)
    parameters = (BETA, DELTA, KAPPA, PHASE)
    origin = dict.fromkeys(parameters, 0)
    return vector.jacobian(parameters).subs(origin)


def _a15_frame() -> sp.Matrix:
    chart = SkewSchurChart.from_certificate(rank_certificate(CENTER))
    kernel = sp.Matrix(chart.kernel)
    rows = tuple((row, column) for row in range(12) for column in range(row + 1, 12))
    derivative_columns = []
    for coordinate in COORDINATE_INDICES:
        block = kernel.T * _operator(tuple(int(index == coordinate) for index in range(32))) * kernel
        derivative_columns.append(sp.Matrix([block[row, column] for row, column in rows]))
    derivative = sp.Matrix.hstack(*derivative_columns)
    system = derivative.col_join(sp.Matrix(1, 30, [CENTER[index] for index in COORDINATE_INDICES]))
    tangent, _ = _kernel(system)
    ambient = sp.zeros(32, 21)
    for position, coordinate in enumerate(COORDINATE_INDICES):
        ambient[coordinate, :] = tangent[position, :]
    return ambient[:, [index for index in range(21) if index not in (6, 16, 17, 18, 19, 20)]]


@dataclass(frozen=True)
class NullityTwelveCurvesCertificate:
    external_complement: RationalMatrix
    external_kernel: RationalMatrix
    inverse_numerator: SymbolicMatrix
    inverse_denominator: sp.Expr
    kernel_numerator: SymbolicMatrix
    pivot_determinant: sp.Expr
    phase_generator: RationalMatrix
    derivations: tuple[RationalMatrix, ...]
    derivation_span: ExactColumnSpan
    orbit_span: ExactColumnSpan
    slice_differential: RationalMatrix
    a15_frame: RationalMatrix
    a15_reconstruction: RationalMatrix
    a15_determinant: Fraction


def certify_nullity_twelve_curves() -> NullityTwelveCurvesCertificate:
    """Construct polynomial, equivariance and local orbit-rank witnesses."""
    numerator, _ = _base_numerator(BETA, DELTA, KAPPA)
    operator = _operator(numerator, EXTERNAL_INDICES)
    complement, kernel = _external_frames()
    pivot, cross = complement.T * operator * complement, complement.T * operator * kernel
    inverse_numerator, denominator = pivot.to_DM().inv_den()
    inverse_numerator, denominator = inverse_numerator.cancel_denom(denominator)
    inverse_matrix, denominator_expression = inverse_numerator.to_Matrix(), denominator.as_expr()
    lifted = (kernel * denominator_expression - complement * inverse_matrix * cross).applyfunc(sp.expand)
    candidates = [_derivation(pair) for pair in DERIVATION_PAIRS]
    derivation_span = _column_span(sp.Matrix.hstack(*(matrix.reshape(64, 1) for matrix in candidates)))
    derivations = tuple(_rows(candidates[index]) for index in derivation_span.pivot_columns)
    orbit = sp.Matrix.hstack(
        *(sp.diag(*(sp.Matrix(matrix) for _ in range(4))) * sp.Matrix(CENTER) for matrix in derivations)
    )
    orbit_span = _column_span(orbit)
    differential = _slice_differential()
    completed = orbit[:, list(orbit_span.pivot_columns)].row_join(differential)
    a15 = _a15_frame()
    selected_rows = tuple(int(index) for index in a15.T.rref()[1])
    reconstruction = a15[list(selected_rows), :].inv() * completed[list(selected_rows), :]
    certificate = NullityTwelveCurvesCertificate(
        _rows(complement),
        _rows(kernel),
        _symbolic_rows(inverse_matrix),
        denominator_expression,
        _symbolic_rows(lifted),
        sp.factor(pivot.det(method="domain-ge")),
        _rows(_phase_generator()),
        derivations,
        derivation_span,
        orbit_span,
        _rows(differential),
        _rows(a15),
        _rows(reconstruction),
        _fraction(reconstruction.det()),
    )
    _require(verify_nullity_twelve_curves(certificate), "constructed curve certificate fails verification")
    return certificate


def _verify_internal_geometry() -> bool:
    for first in range(16):
        for second in range(16):
            if INTERNAL_INDICES[first ^ second] != INTERNAL_INDICES[first] ^ INTERNAL_INDICES[second] or cd_sign(
                16, first, second
            ) != cd_sign(32, INTERNAL_INDICES[first], INTERNAL_INDICES[second]):
                return False
    numerator, denominator = _base_numerator(BETA, DELTA, KAPPA)
    compact = numerator.extract(INTERNAL_INDICES, (0,))
    first, second = compact[:8, :], compact[8:, :]
    norm_numerator = sp.cancel(denominator**2 * _norm_formula(BETA, DELTA, KAPPA))
    if not (
        first[0] == 0
        and second[0] == 0
        and _zero(
            sp.Matrix(
                [first.dot(first) - second.dot(second), first.dot(second), numerator.dot(numerator) - norm_numerator]
            )
        )
    ):
        return False
    # The compact factors satisfy the sedenion criterion of Proposition 12.1
    # and Corollary 11.2 in Biss-Dugger-Isaksen, math/0511691. Their common
    # positive norm excludes the zero-factor exception.
    rotated = (_phase_vector(numerator, PHASE) * (1 + PHASE**2)).applyfunc(sp.cancel)
    compact_rotated = rotated.extract(INTERNAL_INDICES, (0,))
    first_rotated, second_rotated = compact_rotated[:8, :], compact_rotated[8:, :]
    residuals = [
        first_rotated.dot(first_rotated) - second_rotated.dot(second_rotated),
        first_rotated.dot(second_rotated),
        rotated.dot(rotated) - (1 + PHASE**2) ** 2 * norm_numerator,
    ]
    return all(sp.Poly(value, BETA, DELTA, KAPPA, PHASE, domain=sp.QQ).is_zero for value in residuals)


def verify_nullity_twelve_curves(certificate: NullityTwelveCurvesCertificate) -> bool:
    """Verify retained polynomial identities and finite exact rank witnesses.

    The verifier performs polynomial multiplication, not symbolic inversion.
    External kernel dimension eight follows from an invertible pivot and
    an eight-column kernel with a nonvanishing free-row minor. The internal
    nullity-four theorem applies because both imaginary factors are nonzero,
    orthogonal and equally long. Bilinear basis checks prove derivations.
    """
    try:
        if not isinstance(certificate, NullityTwelveCurvesCertificate):
            return False
        complement = _matrix(certificate.external_complement, 16, 8)
        kernel = _matrix(certificate.external_kernel, 16, 8)
        inverse = _symbolic_matrix(certificate.inverse_numerator, 8, 8)
        lifted = _symbolic_matrix(certificate.kernel_numerator, 16, 8)
        differential = _matrix(certificate.slice_differential, 32, 4)
        a15 = _matrix(certificate.a15_frame, 32, 15)
        reconstruction = _matrix(certificate.a15_reconstruction, 15, 15)
        generator = _matrix(certificate.phase_generator, 16, 16)
        if (
            not _polynomial(certificate.inverse_denominator)
            or not _polynomial(certificate.pivot_determinant)
            or type(certificate.a15_determinant) is not Fraction
            or not isinstance(certificate.derivations, tuple)
            or len(certificate.derivations) != 14
            or not _verify_phase(generator)
        ):
            return False
        expected_complement, expected_kernel = _external_frames()
        if complement != expected_complement or kernel != expected_kernel or complement.row_join(kernel).det() == 0:
            return False
        candidates = [_derivation(pair) for pair in DERIVATION_PAIRS]
        flattened = sp.Matrix.hstack(*(matrix.reshape(64, 1) for matrix in candidates))
        if not _verify_span(flattened, certificate.derivation_span, 14):
            return False
        derivations = [_matrix(rows, 8, 8) for rows in certificate.derivations]
        if any(
            matrix != candidates[index]
            for matrix, index in zip(derivations, certificate.derivation_span.pivot_columns, strict=True)
        ):
            return False
        if not all(parallel.ordered_map(_verify_leibniz, certificate.derivations, min_items=4)):
            return False
        orbit = sp.Matrix.hstack(*(sp.diag(*(matrix for _ in range(4))) * sp.Matrix(CENTER) for matrix in derivations))
        if not _verify_span(orbit, certificate.orbit_span, 11):
            return False
        completed = orbit[:, list(certificate.orbit_span.pivot_columns)].row_join(differential)
        if not (
            differential == _slice_differential()
            and a15 == _a15_frame()
            and a15 * reconstruction == completed
            and certificate.a15_determinant != 0
            and reconstruction.det() == certificate.a15_determinant
        ):
            return False
        denominator = certificate.inverse_denominator
        negative = BETA**2 + DELTA**2 + 4 * (KAPPA - 1) ** 2
        positive = BETA**2 + DELTA**2 + 4 * (KAPPA + 1) ** 2
        expected_determinant = (KAPPA - 1) ** 4 * (KAPPA + 1) ** 4 * negative**4 * positive**4
        if not _zero(
            sp.Matrix([denominator - _expected_denominator(), certificate.pivot_determinant - expected_determinant])
        ):
            return False
        numerator, _ = _base_numerator(BETA, DELTA, KAPPA)
        operator = _operator(numerator, EXTERNAL_INDICES)
        pivot, cross = complement.T * operator * complement, complement.T * operator * kernel
        if not (
            _zero(pivot * inverse - denominator * sp.eye(8))
            and _zero(lifted - kernel * denominator + complement * inverse * cross)
            and _zero(operator * lifted)
            and _zero(lifted[8:, :] - denominator * sp.eye(8))
            and _zero(sp.Matrix([pivot.det(method="domain-ge") - certificate.pivot_determinant]))
        ):
            return False
        norm = _norm_formula(BETA, DELTA, KAPPA)
        origin = {BETA: 0, DELTA: 0, KAPPA: 0}
        if norm.subs(origin) != 2 or any(
            sp.diff(norm, variable).subs(origin) != 0 for variable in POLYNOMIAL_VARIABLES
        ):
            return False
        return _verify_internal_geometry()
    except (ValueError, TypeError, AttributeError, IndexError, ZeroDivisionError, BasePolynomialError):
        return False


def _damage(value: Any, **fields: Any) -> Any:
    return replace(value, **fields)


def _changed(rows: RationalMatrix) -> RationalMatrix:
    return ((rows[0][0] + 1, *rows[0][1:]), *rows[1:])


def audit_nullity_twelve_curves() -> dict[str, object]:
    certificate = certify_nullity_twelve_curves()
    fixtures: list[tuple[int | Fraction, int | Fraction, int | Fraction, int | Fraction]] = [
        (0, 0, 0, 0),
        (1, 2, Fraction(1, 3), Fraction(2, 5)),
        (Fraction(-2, 3), Fraction(1, 7), -2, Fraction(-4, 3)),
        (0, 0, 2, 1),
    ]
    points = [nullity_twelve_slice(*parameters) for parameters in fixtures]
    invalid: list[tuple[str, tuple[Any, ...]]] = [
        ("positive_singular", (0, 0, 1, 0)),
        ("negative_singular", (0, 0, -1, 0)),
        ("float", (0.0, 0, 0, 0)),
        ("boolean", (0, False, 0, 0)),
        ("symbolic", (BETA, 0, 0, 0)),
    ]
    for label, parameters in invalid:
        try:
            nullity_twelve_slice(*parameters)
        except ValueError:
            pass
        else:
            raise RuntimeError(f"invalid slice input accepted: {label}")
    point = points[1]
    damaged_points = [
        ("point_type", None),
        ("point_coordinate", _damage(point, coordinates=(point.coordinates[0] + 1, *point.coordinates[1:]))),
        ("point_norm", _damage(point, norm_squared=point.norm_squared + 1)),
        ("point_float", _damage(point, parameters=(float(point.parameters[0]), *point.parameters[1:]))),
        ("point_rank", _damage(point, rank_certificate=_damage(point.rank_certificate, pivot_determinant=Fraction(0)))),
    ]
    for label, damaged_point in damaged_points:
        _require(not verify_nullity_twelve_slice(damaged_point), f"invalid point accepted: {label}")
    damaged_certificates = [
        ("certificate_type", None),
        ("phase_generator", _damage(certificate, phase_generator=_changed(certificate.phase_generator))),
        ("orbit_rank", _damage(certificate, orbit_span=_damage(certificate.orbit_span, determinant=Fraction(0)))),
        ("differential", _damage(certificate, slice_differential=_changed(certificate.slice_differential))),
        ("domain_polynomial", _damage(certificate, inverse_denominator=certificate.inverse_denominator + 1)),
        (
            "kernel_polynomial",
            _damage(
                certificate,
                kernel_numerator=(
                    (certificate.kernel_numerator[0][0] + 1, *certificate.kernel_numerator[0][1:]),
                    *certificate.kernel_numerator[1:],
                ),
            ),
        ),
        (
            "polynomial_float",
            _damage(
                certificate,
                inverse_numerator=(
                    (sp.Float(0), *certificate.inverse_numerator[0][1:]),
                    *certificate.inverse_numerator[1:],
                ),
            ),
        ),
        ("tangent_minor", _damage(certificate, a15_determinant=Fraction(0))),
        ("irrational_coefficient", _damage(certificate, inverse_denominator=sp.sqrt(2))),
        ("infinite_coefficient", _damage(certificate, inverse_denominator=sp.oo)),
        ("unexpected_symbol", _damage(certificate, inverse_denominator=sp.Symbol("other"))),
        ("mutable_polynomial_rows", _damage(certificate, inverse_numerator=list(certificate.inverse_numerator))),
    ]
    for label, damaged_certificate in damaged_certificates:
        _require(not verify_nullity_twelve_curves(damaged_certificate), f"invalid curve certificate accepted: {label}")
    return {
        "scope": "real smooth local curve witnesses and rational points at nullity twelve",
        "domain": "all real beta, delta, f; k != -1 and k != 1",
        "phase": "cos=(1-f^2)/(1+f^2), sin=2f/(1+f^2)",
        "normalization": "sqrt(2/norm_squared), positive and smooth on the domain",
        "internal_nullity": 4,
        "external_nullity": 8,
        "internal_theorem": "equal-norm orthogonal nonzero imaginary octonion factors; Biss-Dugger-Isaksen",
        "inverse_denominator": str(sp.factor(certificate.inverse_denominator)),
        "external_pivot_determinant": str(sp.factor(certificate.pivot_determinant)),
        "derivation_rank": len(certificate.derivation_span.pivot_columns),
        "orbit_rank": len(certificate.orbit_span.pivot_columns),
        "slice_rank": 4,
        "completed_A15_rank": 15,
        "A15_minor": str(certificate.a15_determinant),
        "points": [
            {
                "parameters": [str(value) for value in point.parameters],
                "norm_squared": str(point.norm_squared),
                "nullity": point.rank_certificate.nullity,
            }
            for point in points
        ],
        "rejected_inputs": [label for label, _ in invalid],
        "rejected_mutations": [label for label, _ in damaged_points + damaged_certificates],
        "boundary": "the local curve witnesses do not classify nearby rank strata or global topology",
    }


def main() -> int:
    print(json.dumps(audit_nullity_twelve_curves(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
