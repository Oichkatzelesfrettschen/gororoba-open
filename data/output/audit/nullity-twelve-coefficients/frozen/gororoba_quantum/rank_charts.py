"""Exact rational certificates for Cayley-Dickson rank loci and kernel charts.

The pivot-minor and Schur-complement contract follows open_gororoba's
exact_annihilator.rs. Rational evaluation supplies point certificates; the
same determinant identities describe every real point of each chart domain.
Kernel frames are rational and their transitions lie in GL(k,R). A sphere
fiber uses its frame Gram metric, rather than assuming orthogonal transitions.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from dataclasses import dataclass, replace
from fractions import Fraction

import sympy as sp

import parallel
from cd_core import cd_sign

RationalMatrix = tuple[tuple[Fraction, ...], ...]
MAX_DIMENSION = 256
SOURCE_SHA256 = "0769f94d0ceb9bf935324a5220c5905d2826e6b88be19ef7e0c45d6b4d96ead2"


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def _rational(value: object) -> Fraction:
    if isinstance(value, bool) or not isinstance(value, (int, Fraction)):
        raise ValueError("exact rational entries must be integers or Fractions")
    return Fraction(value)


def _coordinates(values: Sequence[int | Fraction]) -> tuple[Fraction, ...]:
    if isinstance(values, (str, bytes)):
        raise ValueError("coordinates must be a sequence of exact integers or Fractions")
    dimension = len(values)
    if dimension < 1 or dimension > MAX_DIMENSION or dimension & (dimension - 1):
        raise ValueError(f"coordinate count must be a power of two in [1, {MAX_DIMENSION}]")
    return tuple(_rational(value) for value in values)


def _side(side: str) -> None:
    if side not in ("left", "right"):
        raise ValueError("multiplication side must be left or right")


def _fractions(matrix: sp.Matrix) -> RationalMatrix:
    return tuple(
        tuple(Fraction(int(matrix[row, column].p), int(matrix[row, column].q)) for column in range(matrix.cols))
        for row in range(matrix.rows)
    )


def _matrix(rows: RationalMatrix) -> sp.Matrix:
    return sp.Matrix(tuple(tuple(_rational(value) for value in row) for row in rows))


def _indices(indices: Sequence[int], dimension: int) -> tuple[int, ...]:
    values = tuple(indices)
    if any(isinstance(value, bool) or not isinstance(value, int) or not 0 <= value < dimension for value in values):
        raise ValueError("pivot indices must be integers inside the coordinate range")
    if len(set(values)) != len(values):
        raise ValueError("pivot indices must be distinct")
    return values


def multiplication_matrix(coordinates: Sequence[int | Fraction], side: str = "left") -> RationalMatrix:
    """Return the exact matrix of x*y (left) or y*x (right)."""
    values = _coordinates(coordinates)
    _side(side)
    dimension = len(values)
    return tuple(
        tuple(
            values[row ^ column]
            * (cd_sign(dimension, row ^ column, column) if side == "left" else cd_sign(dimension, column, row ^ column))
            for column in range(dimension)
        )
        for row in range(dimension)
    )


@dataclass(frozen=True)
class RankCertificate:
    coordinates: tuple[Fraction, ...]
    side: str
    matrix: RationalMatrix
    kernel_basis: RationalMatrix
    pivot_rows: tuple[int, ...]
    pivot_columns: tuple[int, ...]
    pivot_determinant: Fraction
    input_norm_squared: Fraction
    block_encoding_alpha: Fraction

    @property
    def rank(self) -> int:
        return len(self.pivot_columns)

    @property
    def nullity(self) -> int:
        return len(self.coordinates) - self.rank


def rank_certificate(
    coordinates: Sequence[int | Fraction], side: str = "left", column_order: Sequence[int] | None = None
) -> RankCertificate:
    """Retain a nonzero rank-sized minor and an independent full kernel basis."""
    values = _coordinates(coordinates)
    matrix_rows = multiplication_matrix(values, side)
    matrix = _matrix(matrix_rows)
    dimension = len(values)
    order = tuple(range(dimension)) if column_order is None else _indices(column_order, dimension)
    if len(order) != dimension:
        raise ValueError("column_order must be a permutation of all coordinate indices")
    reordered = matrix[:, list(order)]
    _, local_pivots = reordered.rref()
    pivot_columns = tuple(order[index] for index in local_pivots)
    pivot_rows = tuple(int(index) for index in matrix[:, list(pivot_columns)].T.rref()[1])
    chart = ConstantRankChart(dimension, side, pivot_rows, pivot_columns)
    point = chart.certify(values)
    certificate = RankCertificate(
        values,
        side,
        matrix_rows,
        point.kernel_frame,
        pivot_rows,
        pivot_columns,
        point.pivot_determinant,
        sum((value * value for value in values), Fraction(0)),
        sum((abs(value) for value in values), Fraction(0)),
    )
    _require(verify_rank_certificate(values, certificate, side), "constructed rank certificate failed verification")
    return certificate


def verify_rank_certificate(
    coordinates: Sequence[int | Fraction], certificate: RankCertificate, side: str = "left"
) -> bool:
    """Verify rank bounds against the input, including every retained field."""
    try:
        values = _coordinates(coordinates)
        _side(side)
        if (
            not isinstance(certificate, RankCertificate)
            or values != _coordinates(certificate.coordinates)
            or side != certificate.side
        ):
            return False
        dimension = len(values)
        rows = _indices(certificate.pivot_rows, dimension)
        columns = _indices(certificate.pivot_columns, dimension)
        if len(rows) != len(columns):
            return False
        matrix = _matrix(certificate.matrix)
        kernel = _matrix(certificate.kernel_basis)
        pivot_determinant = _rational(certificate.pivot_determinant)
        input_norm_squared = _rational(certificate.input_norm_squared)
        block_encoding_alpha = _rational(certificate.block_encoding_alpha)
        if certificate.matrix != multiplication_matrix(values, side):
            return False
        if kernel.shape != (dimension, dimension - len(columns)):
            return False
        minor_determinant = matrix.extract(rows, columns).det()
        return bool(
            minor_determinant != 0
            and minor_determinant == pivot_determinant
            and kernel.rank() == dimension - len(columns)
            and matrix * kernel == sp.zeros(dimension, dimension - len(columns))
            and input_norm_squared == sum((value * value for value in values), Fraction(0))
            and block_encoding_alpha == sum((abs(value) for value in values), Fraction(0))
        )
    except (ValueError, TypeError, AttributeError, IndexError):
        return False


@dataclass(frozen=True)
class ConstantRankChart:
    dimension: int
    side: str
    pivot_rows: tuple[int, ...]
    pivot_columns: tuple[int, ...]

    @classmethod
    def from_certificate(cls, certificate: RankCertificate) -> ConstantRankChart:
        if not verify_rank_certificate(certificate.coordinates, certificate, certificate.side):
            raise ValueError("chart construction requires a verified rank certificate")
        return cls(len(certificate.coordinates), certificate.side, certificate.pivot_rows, certificate.pivot_columns)

    def certify(self, coordinates: Sequence[int | Fraction]) -> ChartPoint:
        values = _coordinates(coordinates)
        _side(self.side)
        if isinstance(self.dimension, bool) or len(values) != self.dimension:
            raise ValueError("chart dimension differs from the coordinate count")
        rows = _indices(self.pivot_rows, self.dimension)
        columns = _indices(self.pivot_columns, self.dimension)
        if len(rows) != len(columns):
            raise ValueError("chart pivot row and column counts must agree")
        free_rows = tuple(index for index in range(self.dimension) if index not in rows)
        free_columns = tuple(index for index in range(self.dimension) if index not in columns)
        matrix = _matrix(multiplication_matrix(values, self.side))
        pivot = matrix.extract(rows, columns)
        determinant = pivot.det()
        if determinant == 0:
            raise ValueError("pivot minor vanishes; the point lies outside this chart")
        upper_right = matrix.extract(rows, free_columns)
        inverse_times_upper = pivot.inv() * upper_right if rows else sp.zeros(0, len(free_columns))
        schur = matrix.extract(free_rows, free_columns) - matrix.extract(free_rows, columns) * inverse_times_upper
        if schur != sp.zeros(len(free_rows), len(free_columns)):
            raise ValueError("Schur complement is nonzero; the point lies outside the chart's rank stratum")
        frame = sp.zeros(self.dimension, len(free_columns))
        for free_position, free_column in enumerate(free_columns):
            frame[free_column, free_position] = 1
            for pivot_position, pivot_column in enumerate(columns):
                frame[pivot_column, free_position] = -inverse_times_upper[pivot_position, free_position]
        _require(matrix * frame == sp.zeros(self.dimension, len(free_columns)), "Schur kernel identity failed")
        return ChartPoint(
            self,
            values,
            Fraction(int(determinant.p), int(determinant.q)),
            _fractions(schur),
            _fractions(frame),
            free_columns,
        )

    def symbolic_domain(self) -> dict[str, object]:
        """Return the unexpanded polynomial contract valid for real coefficients.

        Expanding arbitrary large minors is unnecessary: the determinant and
        adjugate expressions themselves define exact real polynomial equations.
        """
        _side(self.side)
        _coordinates([0] * self.dimension)
        _indices(self.pivot_rows, self.dimension)
        _indices(self.pivot_columns, self.dimension)
        if len(self.pivot_rows) != len(self.pivot_columns):
            raise ValueError("chart pivot row and column counts must agree")
        return {
            "coefficient_domain": f"a in R^{self.dimension}",
            "multiplication_side": self.side,
            "pivot_rows": list(self.pivot_rows),
            "pivot_columns": list(self.pivot_columns),
            "rank": len(self.pivot_columns),
            "matrix_partition": "after the stated row/column permutations, A(a)=[[P,Q],[R,S]]",
            "inequation": "delta(a)=det(P(a)) != 0",
            "polynomial_equations": "delta(a)*S(a)-R(a)*adj(P(a))*Q(a)=0 entrywise",
            "polynomial_kernel_frame": "Khat(a)=[-adj(P(a))*Q(a);delta(a)*I] in pivot/free column order",
            "rational_kernel_frame": "K(a)=Khat(a)/delta(a); free coordinate rows form I",
            "real_locus_scope": "These conditions are equivalent to rank(A)=r on this pivot domain.",
            "regularity_scope": (
                "Kernel charts exist on the rank locus; smoothness of the base requires a separate proof."
            ),
        }


@dataclass(frozen=True)
class ChartPoint:
    chart: ConstantRankChart
    coordinates: tuple[Fraction, ...]
    pivot_determinant: Fraction
    schur_complement: RationalMatrix
    kernel_frame: RationalMatrix
    free_columns: tuple[int, ...]


def chart_transition(source: ChartPoint, target: ChartPoint) -> RationalMatrix:
    """Map target kernel coordinates to source coordinates using source free rows."""
    for point in (source, target):
        _coordinates(point.coordinates)
        _rational(point.pivot_determinant)
        _matrix(point.schur_complement)
        _indices(point.free_columns, len(point.coordinates))
    if source.coordinates != target.coordinates or source.chart.side != target.chart.side:
        raise ValueError("chart transitions require the same coefficient point and multiplication side")
    if len(source.free_columns) != len(target.free_columns):
        raise ValueError("chart transitions require equal kernel dimension")
    if source.chart.certify(source.coordinates) != source or target.chart.certify(target.coordinates) != target:
        raise ValueError("chart transition received an altered point certificate")
    source_frame, target_frame = _matrix(source.kernel_frame), _matrix(target.kernel_frame)
    transition = target_frame.extract(source.free_columns, range(len(target.free_columns)))
    reverse = source_frame.extract(target.free_columns, range(len(source.free_columns)))
    _require(source_frame * transition == target_frame, "kernel transition reconstruction failed")
    _require(transition * reverse == sp.eye(len(source.free_columns)), "kernel transition inverse failed")
    source_gram, target_gram = source_frame.T * source_frame, target_frame.T * target_frame
    _require(transition.T * source_gram * transition == target_gram, "kernel transition metric identity failed")
    return _fractions(transition)


def _audit_rank_fixture(fixture: tuple[int, dict[int, int], str]) -> dict[str, object]:
    dimension, sparse, side = fixture
    values = tuple(Fraction(sparse.get(index, 0)) for index in range(dimension))
    certificate = rank_certificate(values, side)
    _require(
        not verify_rank_certificate(
            values, replace(certificate, pivot_determinant=certificate.pivot_determinant + 1), side
        ),
        "damaged minor certificate accepted",
    )
    return {"dimension": dimension, "side": side, "rank": certificate.rank, "nullity": certificate.nullity}


def _audit_nonorthogonal_overlap() -> dict[str, object]:
    coefficients = {1: Fraction(3, 5), 2: Fraction(4, 5), 11: Fraction(1)}
    values = tuple(coefficients.get(index, Fraction(0)) for index in range(32))
    alternate_order = (
        3,
        7,
        29,
        20,
        19,
        5,
        0,
        10,
        14,
        26,
        17,
        21,
        27,
        23,
        2,
        22,
        4,
        25,
        6,
        18,
        11,
        30,
        9,
        12,
        15,
        16,
        8,
        1,
        13,
        28,
        31,
        24,
    )
    source = ConstantRankChart.from_certificate(rank_certificate(values)).certify(values)
    target = ConstantRankChart.from_certificate(rank_certificate(values, column_order=alternate_order)).certify(values)
    transition = _matrix(chart_transition(source, target))
    _require(transition.T * transition != sp.eye(transition.cols), "Gram fixture became orthogonal")
    return {
        "coordinates": [str(value) for value in values],
        "rank": len(source.chart.pivot_columns),
        "target_column_order": list(alternate_order),
        "transition": [[str(value) for value in row] for row in transition.tolist()],
        "gram_metric_preserved": True,
        "euclidean_metric_preserved": False,
    }


def audit_rank_charts() -> dict[str, object]:
    """Exercise source fixtures, rank boundaries, overlaps, and damaged certificates."""
    fixtures = [(1, {0: 0}), (4, {0: 1}), (16, {1: 1, 10: 1}), (32, {1: 1, 10: 1})]
    tasks = [(dimension, sparse, side) for dimension, sparse in fixtures for side in ("left", "right")]
    records = parallel.ordered_map(_audit_rank_fixture, tasks, min_items=2)
    values = tuple(Fraction(2, 7) if index in (1, 10) else Fraction(0) for index in range(32))
    orders = (tuple(range(32)), tuple(reversed(range(32))), tuple(range(1, 32)) + (0,))
    points = [
        ConstantRankChart.from_certificate(rank_certificate(values, column_order=order)).certify(values)
        for order in orders
    ]
    transitions = [[_matrix(chart_transition(source, target)) for target in points] for source in points]
    for first in range(3):
        for middle in range(3):
            for last in range(3):
                _require(
                    transitions[first][middle] * transitions[middle][last] == transitions[first][last],
                    "chart cocycle failed",
                )
    base_chart = points[0].chart
    rejected = 0
    for invalid_point in (tuple(Fraction(0) for _ in range(32)), (Fraction(1),) + values[1:]):
        try:
            base_chart.certify(invalid_point)
        except ValueError:
            rejected += 1
        else:
            raise RuntimeError("rank-boundary point admitted")
    for invalid in ([1.0] * 4, [True] * 4, [0] * 3, [0] * 512):
        try:
            rank_certificate(invalid)  # type: ignore[arg-type]
        except ValueError:
            rejected += 1
        else:
            raise RuntimeError("invalid exact coefficient domain accepted")
    zero_certificate = rank_certificate([0])
    for invalid_entry in (sp.Symbol("u"), sp.I, 0.5, True):
        damaged_fields = (
            {"coordinates": (invalid_entry,)},
            {"matrix": ((invalid_entry,),)},
            {"kernel_basis": ((invalid_entry,),)},
            {"pivot_determinant": invalid_entry},
            {"input_norm_squared": invalid_entry},
            {"block_encoding_alpha": invalid_entry},
        )
        for damaged_field in damaged_fields:
            _require(
                not verify_rank_certificate([0], replace(zero_certificate, **damaged_field)),
                "inexact or nonreal retained certificate entry accepted",
            )
            rejected += 1
    from rank_polynomials import evaluate_rank_polynomials

    polynomial = evaluate_rank_polynomials(values)
    _require(
        polynomial.predicted_nullity == len(points[0].free_columns), "Newton rank predicate disagrees with pivot chart"
    )
    return {
        "schema": "cayley-dickson-exact-rank-charts-v1",
        "qpu_executed": False,
        "arithmetic": "Fraction and SymPy exact rational arithmetic",
        "sympy_version": sp.__version__,
        "source_contract": "open_gororoba/crates/algebra_analysis/src/exact_annihilator.rs",
        "source_read_sha256": SOURCE_SHA256,
        "fixtures": records,
        "overlap_charts": len(points),
        "exact_cocycle_checks": 27,
        "nonorthogonal_overlap": _audit_nonorthogonal_overlap(),
        "rejected_inputs": rejected,
        "newton_predicate_nullity": polynomial.predicted_nullity,
        "symbolic_domain": base_chart.symbolic_domain(),
        "sphere_metric": "u^T K(a)^T K(a) u=1; raw transitions preserve this Gram metric and lie in GL(k,R)",
    }


def main() -> int:
    print(json.dumps(audit_rank_charts(), indent=2, sort_keys=True, allow_nan=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
