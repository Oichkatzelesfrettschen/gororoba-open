"""Exact identities for a real nullity-twelve family in dimension thirty-two."""

from __future__ import annotations

from fractions import Fraction

import sympy as sp

INTERNAL = tuple((index & 3) | ((index & 12) << 1) for index in range(16))
EXTERNAL = tuple(index ^ 4 for index in INTERNAL)
SLICE_SUPPORT = (1, 2, 8, 9, 10, 17, 18, 24, 25, 26)
SEED_SUPPORT = (1, 8, 10, 18, 25)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def column(index: int, dimension: int = 32) -> sp.Matrix:
    return sp.eye(dimension)[:, index]


def operator(values: sp.Matrix) -> sp.Matrix:
    from cd_core import cd_sign

    dimension = len(values)
    return sp.Matrix(
        dimension,
        dimension,
        lambda row, col: cd_sign(dimension, row ^ col, col) * values[row ^ col],
    )


def product(left: sp.Matrix, right: sp.Matrix) -> sp.Matrix:
    return operator(left) * right


def zero(matrix: sp.Matrix) -> bool:
    return all(sp.cancel(value) == 0 for value in matrix)


def entries(matrix: sp.Matrix) -> list[list[str]]:
    return [[str(value) for value in row] for row in matrix.tolist()]


def block(index: int) -> sp.Matrix:
    return operator(column(index)).extract(EXTERNAL, EXTERNAL)


def seed_proof() -> dict[str, object]:
    lower_sum, upper_difference, scalar = sp.symbols("u w b", real=True)
    denominator = lower_sum**2 - upper_difference**2
    lower_difference = -(scalar**2) * lower_sum / denominator
    upper_sum = scalar**2 * upper_difference / denominator
    values = sp.zeros(32, 1)
    values[1] = (lower_sum + lower_difference) / 2
    values[18] = (lower_sum - lower_difference) / 2
    values[10] = (upper_difference + upper_sum) / 2
    values[25] = (upper_sum - upper_difference) / 2
    values[8] = scalar
    external = operator(values).extract(EXTERNAL, EXTERNAL)
    center = block(1) + block(18)
    pivot_columns = center.rref()[1]
    complement = center[:, list(pivot_columns)]
    kernel = sp.Matrix.hstack(*center.nullspace())
    full_basis = complement.row_join(kernel)
    require(full_basis.det() != 0, "external complement and kernel fail to form a basis")
    pivot = (complement.T * external * complement).applyfunc(sp.cancel)
    off_diagonal = (complement.T * external * kernel).applyfunc(sp.cancel)
    diagonal = (kernel.T * external * kernel).applyfunc(sp.cancel)
    pivot_determinant = sp.factor(pivot.det(method="domain-ge"))
    require(sp.cancel(pivot_determinant - 256 * denominator**4) == 0, "external determinant identity fails")
    inverse = pivot.inv(method="DM").applyfunc(sp.cancel)
    require(zero(pivot * inverse - sp.eye(8)), "external inverse fails")
    schur = diagonal + off_diagonal.T * inverse * off_diagonal
    require(zero(schur), "external Schur residual fails")
    compact = values.extract(INTERNAL, (0,))
    first_half, second_half = compact[:8, :], compact[8:, :]
    require(first_half[0] == second_half[0] == 0, "compact octonion halves fail purity")
    require(
        sp.cancel(first_half.dot(first_half) - second_half.dot(second_half)) == 0,
        "compact octonion half norms disagree",
    )
    require(sp.cancel(first_half.dot(second_half)) == 0, "compact octonion halves fail orthogonality")
    return {
        "coordinates": {str(index): str(values[index]) for index in SEED_SUPPORT},
        "domain": "u^2-w^2 != 0",
        "external_complement": entries(complement),
        "external_kernel_at_center": entries(kernel),
        "external_basis_determinant": str(full_basis.det()),
        "external_pivot": entries(pivot),
        "external_off_diagonal": entries(off_diagonal),
        "external_diagonal": entries(diagonal),
        "external_pivot_determinant": str(pivot_determinant),
        "external_schur_zero": True,
        "internal_half_norm_squared": str(sp.factor(first_half.dot(first_half))),
        "internal_equal_norm_orthogonal_pure_halves": True,
    }


def quaternion_automorphism_proof() -> dict[str, object]:
    from cd_core import cd_sign

    cosine, sine = sp.symbols("c s", real=True)
    rotation = sp.eye(4)
    rotation[1, 1], rotation[1, 2] = cosine, -sine
    rotation[2, 1], rotation[2, 2] = sine, cosine
    circle = sp.groebner([cosine**2 + sine**2 - 1], cosine, sine)
    checked_coefficients = 0
    for left in range(4):
        for right in range(4):
            difference = product(rotation[:, left], rotation[:, right]) - (
                cd_sign(4, left, right) * rotation[:, left ^ right]
            )
            for coefficient in difference:
                require(circle.reduce(sp.expand(coefficient))[1] == 0, "quaternion rotation fails multiplicativity")
                checked_coefficients += 1
    require(rotation[:, 0] == column(0, 4), "quaternion rotation fails unit preservation")
    conjugation = sp.diag(1, -1, -1, -1)
    require(rotation * conjugation == conjugation * rotation, "quaternion rotation fails conjugation compatibility")
    return {
        "rotation": entries(rotation),
        "circle_relation": "c^2+s^2=1",
        "basis_product_coefficients_checked": checked_coefficients,
        "extension": "repeat this 4-by-4 rotation in eight diagonal blocks",
    }


def outer_rotation_proof() -> dict[str, object]:
    source = [operator(column(index)) for index in SEED_SUPPORT]
    rotated_source = [
        operator(column(index + 16)) if index < 16 else -operator(column(index - 16)) for index in SEED_SUPPORT
    ]
    checks = 0
    for left in range(len(source)):
        for right in range(left, len(source)):
            factor = 1 if left == right else 2
            if factor == 1:
                square_difference = source[left] ** 2 - rotated_source[left] ** 2
                mixed = source[left] * rotated_source[left] + rotated_source[left] * source[left]
            else:
                square_difference = (
                    source[left] * source[right]
                    + source[right] * source[left]
                    - rotated_source[left] * rotated_source[right]
                    - rotated_source[right] * rotated_source[left]
                )
                mixed = (
                    source[left] * rotated_source[right]
                    + rotated_source[right] * source[left]
                    + source[right] * rotated_source[left]
                    + rotated_source[left] * source[right]
                )
            require(square_difference == sp.zeros(32), "outer rotation square coefficient fails")
            require(mixed == sp.zeros(32), "outer rotation mixed coefficient fails")
            checks += 2
    return {
        "seed_support": list(SEED_SUPPORT),
        "quadratic_coefficient_matrices_checked": checks,
        "identities": ["L(Jx)^2=L(x)^2", "L(x)L(Jx)+L(Jx)L(x)=0"],
        "rotation": "(a,b) -> (c*a-s*b,s*a+c*b)",
    }


def slice(beta: sp.Expr, delta: sp.Expr, crossed: sp.Expr, phase: sp.Expr) -> sp.Matrix:
    denominator = 4 * (1 - crossed**2)
    symmetric = sp.Matrix([[beta**2 - delta**2, 2 * beta * delta], [2 * beta * delta, delta**2 - beta**2]])
    rotated_symmetric = sp.Matrix([[-2 * beta * delta, beta**2 - delta**2], [beta**2 - delta**2, 2 * beta * delta]])
    complex_structure = sp.Matrix([[0, 1], [-1, 0]])
    first_slots = sp.eye(2) - symmetric / denominator
    second_slots = -crossed * complex_structure - crossed * rotated_symmetric / denominator
    cosine = (1 - phase**2) / (1 + phase**2)
    sine = 2 * phase / (1 + phase**2)
    rotated_first = cosine * first_slots - sine * second_slots
    rotated_second = sine * first_slots + cosine * second_slots
    values = sp.zeros(32, 1)
    for row, base in enumerate((0, 16)):
        values[base + 1], values[base + 2] = rotated_first[row, 0], rotated_first[row, 1]
        values[base + 9], values[base + 10] = rotated_second[row, 0], rotated_second[row, 1]
    values[8], values[24] = beta, delta
    return values


def isotropy_slice_proof() -> dict[str, object]:
    radius, cosine, sine, crossed = sp.symbols("rho c s k", real=True)
    circle = sp.groebner([cosine**2 + sine**2 - 1], cosine, sine, radius, crossed)
    seed = slice(radius, sp.Integer(0), crossed, sp.Integer(0))
    outer = cosine * seed + sine * ((-seed[16:, :]).col_join(seed[:16, :]))
    quaternion_rotation = sp.eye(4)
    quaternion_rotation[1, 1], quaternion_rotation[1, 2] = cosine, -sine
    quaternion_rotation[2, 1], quaternion_rotation[2, 2] = sine, cosine
    extended = sp.diag(*([quaternion_rotation] * 8))
    general = slice(radius * cosine, radius * sine, crossed, sp.Integer(0))
    transformed = extended * outer
    for coefficient in transformed - general:
        numerator = sp.together(coefficient).as_numer_denom()[0]
        require(circle.reduce(sp.expand(numerator))[1] == 0, "slice isotropy identity fails")
    return {
        "coordinate_coefficients_checked": 32,
        "identity": "slice(rho*c,rho*s,k,0)=diag(g,...,g)(c*x+s*Jx), x=slice(rho,0,k,0)",
        "zero_radius_case": "beta=delta=0 is the seed with b=0",
    }


def phase_proof() -> dict[str, object]:
    phase = sp.symbols("f", real=True)
    generator = -block(9) * block(1) / 2
    require(generator.T == -generator, "phase generator fails skewness")
    require(generator**2 == -sp.eye(16) / 4, "phase generator square fails")
    pairs = ((1, 9), (2, 10), (17, 25), (18, 26))
    coefficient_checks = 0
    for first, second in pairs:
        first_block, second_block = block(first), block(second)
        require(generator * first_block - first_block * generator == second_block, "phase first commutator fails")
        require(generator * second_block - second_block * generator == -first_block, "phase second commutator fails")
        coefficient_checks += 2
    for scalar in (8, 24):
        require(generator * block(scalar) == block(scalar) * generator, "phase scalar commutator fails")
        coefficient_checks += 1
    numerator = sp.eye(16) + 2 * phase * generator
    for first, second in pairs:
        for source_index, image_index, image_sign in ((first, second, 1), (second, first, -1)):
            expected = (1 - phase**2) * block(source_index) + 2 * phase * image_sign * block(image_index)
            require(
                zero(numerator * block(source_index) * numerator.T - expected), "phase similarity coefficient fails"
            )
    for scalar in (8, 24):
        require(
            zero(numerator * block(scalar) * numerator.T - (1 + phase**2) * block(scalar)),
            "phase scalar similarity coefficient fails",
        )
    return {
        "external_generator": entries(generator),
        "coefficient_commutators_checked": coefficient_checks,
        "coefficient_similarity_identities_checked": 10,
        "formula": "M(phase(x))=(I+2*f*K)*M(x)*(I-2*f*K)/(1+f^2)",
        "parameter": "cos=(1-f^2)/(1+f^2), sin=2*f/(1+f^2)",
        "internal_action": "rotate imaginary slots in both compact octonion halves; fix scalar slots",
    }


def complete_slice_proof() -> dict[str, object]:
    beta, delta, crossed, phase = sp.symbols("beta delta k f", real=True)
    values = slice(beta, delta, crossed, phase)
    radius_squared = beta**2 + delta**2
    expected_norm = (
        2 * (1 + crossed**2) + radius_squared + ((1 + crossed**2) * radius_squared**2 / (8 * (1 - crossed**2) ** 2))
    )
    require(sp.cancel(values.dot(values) - expected_norm) == 0, "slice norm identity fails")
    compact = values.extract(INTERNAL, (0,))
    first, second = compact[:8, :], compact[8:, :]
    require(sp.cancel(first.dot(first) - second.dot(second)) == 0, "complete slice half norms disagree")
    require(sp.cancel(first.dot(second)) == 0, "complete slice half orthogonality fails")
    require(values[0] == values[16] == 0, "complete slice purity fails")
    origin = dict.fromkeys((beta, delta, crossed, phase), 0)
    require(values.subs(origin) == column(1) + column(18), "complete slice center fails")
    expected_differential = sp.Matrix.hstack(
        column(8), column(24), -column(10) + column(25), 2 * (column(9) + column(26))
    )
    differential = values.jacobian((beta, delta, crossed, phase)).subs(origin)
    require(differential == expected_differential, "complete slice differential fails")
    require(
        all(sp.diff(expected_norm, parameter).subs(origin) == 0 for parameter in (beta, delta, crossed, phase)),
        "normalization derivative fails",
    )
    return {
        "domain": "all real beta,delta,f and k != -1,1",
        "coordinates": {str(index): str(sp.factor(values[index])) for index in SLICE_SUPPORT},
        "norm_squared": str(expected_norm),
        "normalization": "multiply by sqrt(2/norm_squared); positive and smooth on the domain",
        "differential": entries(differential),
        "differential_rank": int(differential.rank()),
        "internal_equal_norm_orthogonal_pure_halves": True,
        "tangent_realization_scope": "combine with the eleven-dimensional diagonal octonion automorphism orbit",
    }


def samples() -> list[dict[str, object]]:
    from nullity_twelve_curves import nullity_twelve_slice, verify_nullity_twelve_slice
    from rank_charts import rank_certificate, verify_rank_certificate

    result = []
    parameters: list[tuple[int | Fraction, int | Fraction, int | Fraction, int | Fraction]] = [
        (0, 0, 0, 0),
        (Fraction(1, 3), Fraction(2, 5), Fraction(1, 4), Fraction(3, 7)),
        (Fraction(-2, 3), Fraction(4, 5), Fraction(3, 2), Fraction(-5, 3)),
        (0, 0, Fraction(9, 10), 2),
    ]
    for record in parameters:
        values = slice(*(sp.Rational(parameter) for parameter in record))
        certificate = rank_certificate(tuple(Fraction(value) for value in values))
        require(
            verify_rank_certificate(tuple(Fraction(value) for value in values), certificate),
            "sample certificate verification fails",
        )
        require(certificate.nullity == 12, "sample nullity fails")
        production = nullity_twelve_slice(*record)
        require(verify_nullity_twelve_slice(production), "production point verification fails")
        require(sp.Matrix(production.coordinates) == values, "independent and production slice formulas differ")
        require(production.norm_squared == certificate.input_norm_squared, "production norm differs")
        result.append(
            {
                "parameters": list(map(str, record)),
                "nullity": certificate.nullity,
                "norm_squared": str(certificate.input_norm_squared),
            }
        )
    return result


def extended_derivation(rows: list[list[int]]) -> int:
    from cd_core import cd_sign

    dimension = 32
    table = [[cd_sign(dimension, left, right) for right in range(dimension)] for left in range(dimension)]
    for left in range(dimension):
        for right in range(dimension):
            for output in range(dimension):
                actual = table[left][right] * rows[output][left ^ right]
                expected = (
                    rows[output ^ right][left] * table[output ^ right][right]
                    + rows[output ^ left][right] * table[left][output ^ left]
                )
                require(actual == expected, "dimension-32 derivation coefficient fails")
    matrix = sp.Matrix(rows)
    conjugation = sp.diag(1, *([-1] * 31))
    require(matrix * conjugation == conjugation * matrix, "extended conjugation identity fails")
    require(
        matrix + matrix.T == sp.zeros(dimension) and matrix[:, 0] == sp.zeros(dimension, 1),
        "extended skew/unit identities fail",
    )
    return dimension**2


def orbit_proof() -> dict[str, object]:
    from cd_core import cd_sign
    from parallel import ordered_map

    octonion_left = [operator(column(index, 8)) for index in range(8)]
    octonion_right = [
        sp.Matrix(8, 8, lambda row, col, index=index: cd_sign(8, col, index) if row == col ^ index else 0)
        for index in range(8)
    ]
    candidates = []
    for first in range(1, 8):
        for second in range(first + 1, 8):
            left_first, left_second = octonion_left[first], octonion_left[second]
            right_first, right_second = octonion_right[first], octonion_right[second]
            derivation = (
                left_first * left_second
                - left_second * left_first
                + left_first * right_second
                - right_second * left_first
                + right_first * right_second
                - right_second * right_first
            )
            require(derivation + derivation.T == sp.zeros(8), "octonion derivation skewness fails")
            require(derivation[:, 0] == sp.zeros(8, 1), "octonion derivation unit fails")
            for left in range(8):
                for right in range(8):
                    expected = octonion_right[right] * derivation[:, left] + octonion_left[left] * derivation[:, right]
                    require(
                        cd_sign(8, left, right) * derivation[:, left ^ right] == expected,
                        "octonion derivation Leibniz identity fails",
                    )
            candidates.append(((first, second), derivation))
    flattened = sp.Matrix.hstack(*(matrix.reshape(64, 1) for _, matrix in candidates))
    pivots = tuple(flattened.rref()[1])
    require(len(pivots) == 14, "octonion derivation span differs")
    selected = [candidates[index] for index in pivots]
    extended = [sp.diag(matrix, matrix, matrix, matrix) for _, matrix in selected]
    extended_checks = ordered_map(
        extended_derivation,
        [[[int(value) for value in row] for row in matrix.tolist()] for matrix in extended],
        min_items=4,
    )
    require(extended_checks == [1024] * 14, "per-derivation basis-pair check counts differ")
    center = column(1) + column(18)
    orbit = sp.Matrix.hstack(*(matrix * center for matrix in extended))
    require(orbit.rank() == 11, "automorphism orbit rank differs")
    slice_frame = sp.Matrix.hstack(column(8), column(24), -column(10) + column(25), 2 * (column(9) + column(26)))
    full = orbit.row_join(slice_frame)
    require(full.rank() == 15, "combined curve differential rank differs")
    expected = sp.Matrix.hstack(
        *(
            [column(index) for index in range(3, 9)]
            + [-column(2) + column(17)]
            + [column(index) for index in range(19, 25)]
            + [-column(10) + column(25), column(9) + column(26)]
        )
    )
    require(expected.rank() == 15 and expected.row_join(full).rank() == 15, "combined differential misses A15")
    rank_columns = tuple(full.rref()[1])
    rank_rows = tuple(full[:, list(rank_columns)].T.rref()[1])
    minor = full.extract(rank_rows, rank_columns).det()
    require(minor != 0, "combined differential rank witness vanishes")
    return {
        "basis_pairs": [list(pair) for pair, _ in selected],
        "derivations": [entries(matrix) for _, matrix in selected],
        "octonion_basis_pairs_checked": 21 * 64,
        "extended_basis_pairs_checked": sum(extended_checks),
        "derivation_span_dimension": 14,
        "orbit": entries(orbit),
        "orbit_rank": 11,
        "slice_frame": entries(slice_frame),
        "combined_differential": entries(full),
        "rank_rows": list(rank_rows),
        "rank_columns": list(rank_columns),
        "rank_minor": str(minor),
        "combined_image": "A15",
        "extension": "unit-preserving skew derivations commute with conjugation and extend through doubling",
    }


def audit_curves() -> dict[str, object]:
    from cd_core import cd_sign

    for left in range(16):
        for right in range(16):
            require(
                cd_sign(32, INTERNAL[left], INTERNAL[right]) == cd_sign(16, left, right),
                "embedded Cayley-Dickson subalgebra sign fails",
            )
    report = {
        "scope": "exact real selected-center slice and orbit; global attachments require separate proofs",
        "internal_indices": list(INTERNAL),
        "external_indices": list(EXTERNAL),
        "embedded_subalgebra_signs_checked": 256,
        "seed": seed_proof(),
        "quaternion_automorphism": quaternion_automorphism_proof(),
        "outer_rotation": outer_rotation_proof(),
        "isotropy_slice": isotropy_slice_proof(),
        "phase": phase_proof(),
        "complete_slice": complete_slice_proof(),
        "rational_rank_regressions": samples(),
        "orbit": orbit_proof(),
    }
    return report
