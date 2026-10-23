"""Rebuild the selected-center quadratic locus and exact rank-preserving curves."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import re
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any

import sympy as sp

INDICES = tuple(index for index in range(32) if index not in (0, 16))
SOURCE_FILES = (
    "docs/evidence/nullity_twelve_locus/replay.py",
    "docs/evidence/nullity_twelve_locus/curve_proof.py",
    "docs/notes/nullity_twelve_local_geometry.md",
    "gororoba_quantum/nullity_twelve_locus.py",
    "gororoba_quantum/nullity_twelve_curves.py",
    "gororoba_quantum/schur_acceleration.py",
    "gororoba_quantum/cd_core.py",
    "gororoba_quantum/rank_charts.py",
    "gororoba_quantum/skew_schur_charts.py",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def hashes(root: Path) -> dict[str, str]:
    return {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in SOURCE_FILES}


def operator(values: Any) -> sp.Matrix:
    from cd_core import cd_sign

    return sp.Matrix(32, 32, lambda row, column: cd_sign(32, row ^ column, column) * values[row ^ column])


def basis(index: int) -> sp.Matrix:
    return operator([int(position == index) for position in range(32)])


def record(matrix: sp.Matrix) -> dict[str, Any]:
    return {
        "shape": [matrix.rows, matrix.cols],
        "nonzero_entries": [
            [row, column, str(matrix[row, column])]
            for row in range(matrix.rows)
            for column in range(matrix.cols)
            if matrix[row, column]
        ],
    }


def quadratic_case() -> dict[str, Any]:
    from rank_charts import rank_certificate
    from skew_schur_charts import SkewSchurChart, verify_skew_schur_chart

    center = [int(index in (1, 18)) for index in range(32)]
    chart = SkewSchurChart.from_certificate(rank_certificate(center))
    require(verify_skew_schur_chart(chart), "centered chart fails verification")
    complement, kernel = sp.Matrix(chart.complement), sp.Matrix(chart.kernel)
    center_matrix = operator(center)
    require(center_matrix.rank() == 20 and kernel.cols == 12, "center rank differs")
    pivot = complement.T * center_matrix * complement
    inverse = pivot.inv()
    residual_positions = [(row, column) for row in range(12) for column in range(row + 1, 12)]
    derivative_blocks = [kernel.T * basis(index) * kernel for index in INDICES]
    derivative = sp.Matrix(
        66, 30, lambda row, column: derivative_blocks[column][residual_positions[row][0], residual_positions[row][1]]
    )
    radial = sp.Matrix(1, 30, [center[index] for index in INDICES])
    system = derivative.col_join(radial)
    tangent = sp.Matrix.hstack(*system.nullspace())
    cokernel = sp.Matrix.hstack(*derivative.T.nullspace())
    require(derivative.rank() == 8 and system.rank() == 9, "derivative rank differs")
    require(
        tangent.shape == (30, 21) and tangent.rank() == 21 and system * tangent == sp.zeros(67, 21),
        "tangent frame fails",
    )
    require(
        cokernel.shape == (66, 58) and cokernel.rank() == 58 and cokernel.T * derivative == sp.zeros(58, 30),
        "cokernel frame fails",
    )
    ambient_tangent = sp.zeros(32, 21)
    for position, index in enumerate(INDICES):
        ambient_tangent[index, :] = tangent[position, :]
    crosses = [complement.T * operator(ambient_tangent[:, column]) * kernel for column in range(21)]
    solved = [inverse * cross for cross in crosses]
    monomials = [(index, index) for index in range(21)] + [
        (left, right) for left in range(21) for right in range(left + 1, 21)
    ]
    coefficients = []
    for left, right in monomials:
        quadratic = crosses[left].T * solved[right]
        if left != right:
            quadratic += crosses[right].T * solved[left]
        coefficients.append(cokernel.T * sp.Matrix([quadratic[row, column] for row, column in residual_positions]))
    projected = sp.Matrix.hstack(*coefficients)
    require(projected.shape == (58, 231), "quadratic coefficient matrix shape differs")
    independent_rows = tuple(projected.T.rref()[1])
    reduced, pivot_columns = projected.rref()
    rank = len(pivot_columns)
    require(len(independent_rows) == rank, "independent row rank differs")
    variables = sp.symbols("z0:21", real=True)
    monomial_column = sp.Matrix([variables[left] * variables[right] for left, right in monomials])
    generators = []
    for index in range(rank):
        polynomial = sp.expand((reduced[index, :] * monomial_column)[0])
        form = sp.hessian(polynomial, variables) / 2
        nonzero_variables = sorted([str(value) for value in polynomial.free_symbols])
        generators.append(
            {
                "index": index,
                "polynomial": str(polynomial),
                "factorization": str(sp.factor(polynomial)),
                "matrix_rank": int(form.rank()),
                "variables": nonzero_variables,
                "form": record(form),
            }
        )
    original_generator_matrix = projected[list(independent_rows), :]
    independent_columns = tuple(original_generator_matrix.rref()[1])
    selector = original_generator_matrix[:, list(independent_columns)]
    reconstruction = projected[:, list(independent_columns)] * selector.inv()
    require(reconstruction * original_generator_matrix == projected, "complete generator reconstruction fails")
    rref_generators = reduced[:rank, :]
    rref_reconstruction = projected[:, list(pivot_columns)]
    require(rref_reconstruction * rref_generators == projected, "RREF generator reconstruction fails")
    require(projected.extract(independent_rows, pivot_columns).det() != 0, "quadratic rank minor vanishes")
    polynomials = list(rref_generators * monomial_column)
    require(
        sp.expand(polynomials[0] ** 2 + 4 * polynomials[7] ** 2 - (variables[6] ** 2 + variables[16] ** 2) ** 2) == 0,
        "first sum of squares identity fails",
    )
    reduced_polynomials = [
        sp.expand(polynomial.subs({variables[6]: 0, variables[16]: 0})) for polynomial in polynomials
    ]
    surviving = [polynomial for polynomial in reduced_polynomials if polynomial != 0]
    require(len(surviving) == 4, "reduced bilinear equation count differs")
    product = (variables[5] ** 2 + variables[13] ** 2) * sum(variables[index] ** 2 for index in (17, 18, 19, 20))
    require(
        sp.expand(sum(polynomial**2 for polynomial in surviving) - product) == 0, "second sum of squares identity fails"
    )
    zero_coordinates = {"plane_dimension15": (6, 16, 17, 18, 19, 20), "plane_dimension17": (5, 6, 13, 16)}
    for label, zero_indices in zero_coordinates.items():
        require(
            all(
                sp.expand(polynomial.subs({variables[index]: 0 for index in zero_indices})) == 0
                for polynomial in polynomials
            ),
            f"{label} fails quadratic inclusion",
        )
    from nullity_twelve_locus import certify_nullity_twelve_locus, verify_nullity_twelve_locus

    certificate = certify_nullity_twelve_locus()
    require(verify_nullity_twelve_locus(certificate), "production quadratic locus fails verification")
    comparisons = {
        "derivative_matrix": derivative,
        "ambient_tangent_basis": ambient_tangent,
        "coefficient_matrix": projected,
        "generator_matrix": rref_generators,
        "reconstruction_matrix": rref_reconstruction,
    }
    for name, expected in comparisons.items():
        require(sp.Matrix(getattr(certificate, name)) == expected, f"production {name} differs")
    require(sp.Matrix(certificate.tangent_frame.basis) == tangent, "production tangent frame differs")
    require(sp.Matrix(certificate.cokernel_frame.basis) == cokernel, "production cokernel frame differs")
    require(tuple(monomials) == certificate.monomial_pairs, "production monomial order differs")
    require(certificate.rank_minor_determinant == 2048, "production rank minor differs")
    require(certificate.intersection_dimension == 13, "production intersection dimension differs")
    membership = production_membership(certificate, ambient_tangent)
    result = {
        "membership_crosscheck": membership,
        "scope": "complete real quadratic-compatible velocity set at e1+e18; curve realization is checked separately",
        "center": "e1+e18",
        "nullity": 12,
        "coordinate_indices": list(INDICES),
        "tangent_basis": record(tangent),
        "ambient_tangent_basis": record(ambient_tangent),
        "derivative_matrix": record(derivative),
        "cokernel_basis": record(cokernel),
        "monomial_pairs": [list(pair) for pair in monomials],
        "coefficient_matrix": record(projected),
        "coefficient_matrix_rank": rank,
        "independent_original_rows": list(independent_rows),
        "original_generator_coefficients": record(original_generator_matrix),
        "complete_generator_reconstruction": record(reconstruction),
        "rref_generator_coefficients": record(reduced[:rank, :]),
        "rref_generator_reconstruction": record(rref_reconstruction),
        "rank_minor_columns": list(pivot_columns),
        "rank_minor_determinant": str(projected.extract(independent_rows, pivot_columns).det()),
        "generators": generators,
        "real_zero_locus": {
            "first_sos_identity": "g0^2+4*g7^2=(z6^2+z16^2)^2",
            "reduced_generators": [str(value) for value in surviving],
            "second_sos_identity": "sum(reduced_g3_to_g6^2)=(z5^2+z13^2)*(z17^2+z18^2+z19^2+z20^2)",
            "planes": [
                {"zero_coordinates": list(zero_indices), "dimension": 21 - len(zero_indices)}
                for zero_indices in zero_coordinates.values()
            ],
            "intersection_dimension": 13,
            "free_spectator_coordinates": [index for index in range(21) if index not in (5, 6, 13, 16, 17, 18, 19, 20)],
            "scope": (
                "exact real quadratic locus; curve realization and local stratum dimensions require separate proofs"
            ),
        },
    }
    return result


def production_membership(certificate: Any, tangent: sp.Matrix) -> list[dict[str, Any]]:
    from nullity_twelve_locus import classify_nullity_twelve_direction
    from schur_acceleration import certify_schur_acceleration, verify_schur_acceleration_certificate

    fixtures = []
    for plane in certificate.planes:
        parameters = sp.Matrix(
            [0 if index in plane.zero_coordinates else sp.Rational(index + 1, index + 2) for index in range(21)]
        )
        fixtures.append((plane.name, tangent * parameters, "second_order_compatible"))
    fixtures.extend(
        [
            ("e11", sp.Matrix([int(index == 11) for index in range(32)]), "second_order_obstructed"),
            ("sum_of_pieces", sp.Matrix([int(index in (8, 15, 28)) for index in range(32)]), "second_order_obstructed"),
        ]
    )
    records = []
    derivative = certificate.chart.derivative_at_center()
    for label, direction, expected_status in fixtures:
        values = tuple(Fraction(value) for value in direction)
        classified = classify_nullity_twelve_direction(certificate, values)
        acceleration = certify_schur_acceleration(certificate.chart, values, linearized=derivative)
        require(verify_schur_acceleration_certificate(certificate.chart, acceleration), "acceleration check fails")
        require(classified.status == acceleration.status == expected_status, "direct acceleration status differs")
        if label in ("A15", "B17"):
            require(classified.components == (label,), "dense plane membership differs")
        records.append(
            {
                "label": label,
                "direction": record(direction),
                "status": classified.status,
                "components": list(classified.components),
                "quadratic_values": [str(value) for value in classified.quadratic_values or ()],
            }
        )
    return records


def explicit_curve() -> dict[str, Any]:
    from rank_charts import rank_certificate
    from skew_schur_charts import SkewSchurChart

    parameter = sp.Symbol("t", real=True)
    center = sp.Matrix([int(index in (1, 18)) for index in range(32)])
    chart = SkewSchurChart.from_certificate(rank_certificate(tuple(int(value) for value in center)))
    complement, kernel = sp.Matrix(chart.complement), sp.Matrix(chart.kernel)
    denominator = 4 + parameter**2
    numerator = sp.zeros(32, 1)
    numerator[1] = 4 - parameter**2
    numerator[8] = 4 * parameter
    numerator[18] = denominator
    curve = numerator / denominator
    matrix = operator(numerator)
    pivot = complement.T * matrix * complement
    cross = complement.T * matrix * kernel
    diagonal = kernel.T * matrix * kernel
    determinant = sp.factor(pivot.det())
    require(determinant == 2**68 * denominator**4, "curve pivot determinant differs")
    residual = (diagonal + cross.T * pivot.inv() * cross).applyfunc(sp.factor)
    require(residual == sp.zeros(12), "curve Schur residual differs")
    require(sp.factor(curve.dot(curve) - 2) == 0, "curve norm differs")
    require(curve.subs(parameter, 0) == center, "curve center differs")
    expected_velocity = sp.Matrix([int(index == 8) for index in range(32)])
    require(curve.diff(parameter).subs(parameter, 0) == expected_velocity, "curve velocity differs")
    return {
        "numerator": record(numerator),
        "denominator": str(denominator),
        "numerator_pivot_determinant": str(determinant),
        "schur_residual": record(residual),
        "norm_squared": "2",
        "velocity": record(expected_velocity),
        "real_parameter_domain": "all real finite t",
        "nullity": 12,
    }


def production_curve_certificate() -> dict[str, Any]:
    from curve_proof import EXTERNAL, slice, zero

    from nullity_twelve_curves import certify_nullity_twelve_curves, verify_nullity_twelve_curves

    certificate = certify_nullity_twelve_curves()
    require(verify_nullity_twelve_curves(certificate), "production curve certificate fails")
    beta, delta, crossing = sp.symbols("beta delta k", real=True)
    denominator = 4 * (1 - crossing**2)
    numerator = (slice(beta, delta, crossing, sp.Integer(0)) * denominator).applyfunc(sp.cancel)
    external = operator(numerator).extract(EXTERNAL, EXTERNAL)
    complement, kernel = sp.Matrix(certificate.external_complement), sp.Matrix(certificate.external_kernel)
    require(complement.row_join(kernel).det() != 0, "external centered frame is incomplete")
    pivot = complement.T * external * complement
    inverse_numerator = sp.Matrix(certificate.inverse_numerator)
    inverse_denominator = certificate.inverse_denominator
    kernel_numerator = sp.Matrix(certificate.kernel_numerator)
    require(zero(pivot * inverse_numerator - inverse_denominator * sp.eye(8)), "polynomial inverse identity fails")
    require(zero(external * kernel_numerator), "polynomial kernel identity fails")
    require(
        zero(
            kernel_numerator
            - inverse_denominator * kernel
            + complement * inverse_numerator * complement.T * external * kernel
        ),
        "polynomial kernel lift differs",
    )
    projection = complement.row_join(kernel).inv()[8:, :]
    require(
        zero(projection * kernel_numerator - inverse_denominator * sp.eye(8)), "polynomial kernel rank witness fails"
    )
    minus = beta**2 + delta**2 + 4 * (crossing - 1) ** 2
    plus = beta**2 + delta**2 + 4 * (crossing + 1) ** 2
    expected_determinant = (crossing - 1) ** 4 * (crossing + 1) ** 4 * minus**4 * plus**4
    require(
        sp.expand(pivot.det(method="domain-ge") - expected_determinant) == 0,
        "external positive determinant identity differs",
    )
    require(
        sp.expand(certificate.pivot_determinant - expected_determinant) == 0, "production external determinant differs"
    )
    require(
        sp.expand(inverse_denominator - (crossing - 1) * (crossing + 1) * minus**2 * plus**2) == 0,
        "polynomial kernel denominator differs",
    )
    return {
        "external_complement": record(complement),
        "external_center_kernel": record(kernel),
        "inverse_numerator": record(inverse_numerator),
        "inverse_denominator": str(sp.factor(inverse_denominator)),
        "kernel_numerator": record(kernel_numerator),
        "kernel_projection": record(projection),
        "pivot_determinant": str(sp.factor(expected_determinant)),
        "phase_generator": record(sp.Matrix(certificate.phase_generator)),
        "slice_differential": record(sp.Matrix(certificate.slice_differential)),
        "a15_frame": record(sp.Matrix(certificate.a15_frame)),
        "a15_reconstruction": record(sp.Matrix(certificate.a15_reconstruction)),
        "a15_determinant": str(certificate.a15_determinant),
        "domain": "all real beta,delta,f with k != -1,1",
    }


def audit(root: Path) -> dict[str, Any]:
    before = hashes(root)
    sys.path.insert(0, str(root / "gororoba_quantum"))
    from curve_proof import audit_curves

    import nullity_twelve_curves
    import nullity_twelve_locus
    import parallel
    import schur_acceleration

    require(callable(nullity_twelve_curves.nullity_twelve_slice), "curve point API import fails")
    require(callable(nullity_twelve_locus.certify_nullity_twelve_locus), "certificate API import fails")
    require(callable(schur_acceleration.certify_schur_acceleration), "acceleration API import fails")
    require(callable(parallel.ordered_map), "parallel API import fails")
    result = {
        "schema": "nullity-twelve-locus-evidence-v1",
        "versions": {"python": platform.python_version(), "sympy": sp.__version__},
        "quadratic_locus": quadratic_case(),
        "explicit_e8_curve": explicit_curve(),
        "curve_realization": audit_curves(),
        "production_curve_certificate": production_curve_certificate(),
        "qpu_executed": False,
    }
    for source in SOURCE_FILES:
        if not source.startswith("gororoba_quantum/"):
            continue
        loaded = Path(str(sys.modules[Path(source).stem].__file__)).resolve()
        require(loaded == (root / source).resolve(), "loaded module differs from declared checkout")
    require(hashes(root) == before, "source or proof note changes during replay")
    return result


def adopt_recorded_interpreter(record: dict[str, Any], retained: dict[str, Any]) -> None:
    """Carry the retained interpreter release into a replay under the same Python major.minor.

    The patch release names the interpreter that wrote result.json; every
    other field compares byte for byte, and a replay under another
    major.minor, or against a retained value that is not a MAJOR.MINOR.PATCH
    release, keeps its own version and differs.
    """
    for holder, key, kept in (
        (record, "python_version", retained),
        (record.get("versions"), "python", retained.get("versions")),
    ):
        if isinstance(holder, dict) and isinstance(kept, dict) and key in holder and isinstance(kept.get(key), str):
            if (
                re.fullmatch(r"\d+\.\d+\.\d+", kept[key])
                and kept[key].split(".")[:2] == str(holder[key]).split(".")[:2]
            ):
                holder[key] = kept[key]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare rebuilt evidence with result.json")
    arguments = parser.parse_args()
    bundle = Path(__file__).resolve().parent
    record = audit(bundle.parents[2])
    if arguments.check:
        adopt_recorded_interpreter(record, json.loads((bundle / "result.json").read_bytes()))
    result = json.dumps(record, indent=2, sort_keys=True, allow_nan=False) + "\n"
    if arguments.check:
        require(result.encode() == (bundle / "result.json").read_bytes(), "nullity-twelve locus evidence differs")
        print("Complete quadratic locus, exact curve and source identities pass")
    else:
        print(result, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
