"""Cayley-Dickson basis arithmetic ported from open_gororoba cd_kernel.

The basis product is e_p * e_q = cd_sign(dim, p, q) * e_{p XOR q}, with the sign
recursion of cd_kernel::cayley_dickson::signs::cd_basis_mul_sign_iter and the
doubling (a,b)(c,d) = (ac - conj(d) b, d a + b conj(c)). The table determines
finite basis arithmetic and the signed two-support corpus. General real
membership and geometry use the separate arguments in algebra_circuit_rules.md.
"""

from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction
from itertools import combinations, permutations
from operator import index as integer_index
from typing import TypedDict

from parallel import ordered_map

ExactScalar = int | Fraction
ExactVector = tuple[Fraction, ...]
ExactMatrix = tuple[tuple[Fraction, ...], ...]


def _dimension(dim: int) -> None:
    if isinstance(dim, bool) or not isinstance(dim, int) or dim < 1 or dim & (dim - 1):
        raise ValueError(f"dimension must be a positive power of two, got {dim!r}")


def _index(dim: int, index: int) -> int:
    try:
        value = integer_index(index)
    except TypeError as error:
        raise ValueError(f"basis index {index!r} lies outside dimension {dim}") from error
    if isinstance(index, bool) or not 0 <= value < dim:
        raise ValueError(f"basis index {index!r} lies outside dimension {dim}")
    return value


def _length(dim: int, vector: Sequence[object], name: str) -> None:
    if len(vector) != dim:
        raise ValueError(f"{name} must contain exactly {dim} coordinates, got {len(vector)}")


def _exact_vector(dim: int, vector: Sequence[ExactScalar], name: str) -> ExactVector:
    _dimension(dim)
    _length(dim, vector, name)
    for index, value in enumerate(vector):
        if isinstance(value, bool) or not isinstance(value, int | Fraction):
            raise ValueError(f"{name} coordinate {index} must be int or Fraction, got {value!r}")
    return tuple(Fraction(value) for value in vector)


def cd_sign(dim: int, p: int, q: int) -> int:
    """Sign of e_p * e_q within a 2^k-dimensional Cayley-Dickson algebra."""
    _dimension(dim)
    p = _index(dim, p)
    q = _index(dim, q)
    sign = 1
    half = dim >> 1
    while half > 0:
        p_hi = p >= half
        q_hi = q >= half
        if not p_hi and not q_hi:
            pass
        elif not p_hi and q_hi:
            qh = q - half
            q = p
            p = qh
        elif p_hi and not q_hi:
            p -= half
            if q != 0:
                sign = -sign
        else:
            qh = q - half
            ph = p - half
            if qh == 0:
                return -sign
            p = qh
            q = ph
        half >>= 1
    return sign


def cd_multiply(dim: int, a: Sequence[float], b: Sequence[float]) -> list[float]:
    """Binary64 product, with exactly dim coordinates per operand.

    For finite normal intermediates, coordinate r has absolute forward error
    bounded by gamma_(2*dim) sum_p |a[p] b[p XOR r]|, with
    gamma_k=k*u/(1-k*u), u=2**-53 and k*u<1. Overflow, underflow and nonfinite
    arithmetic fall outside that bound. Use cd_multiply_exact for certificates.
    """
    _dimension(dim)
    _length(dim, a, "left operand")
    _length(dim, b, "right operand")
    out = [0.0] * dim
    for p in range(dim):
        ap = a[p]
        if ap == 0.0:
            continue
        for q in range(dim):
            bq = b[q]
            if bq == 0.0:
                continue
            out[p ^ q] += cd_sign(dim, p, q) * ap * bq
    return out


def cd_multiply_exact(dim: int, a: Sequence[ExactScalar], b: Sequence[ExactScalar]) -> ExactVector:
    """Bilinear product over rational coordinates, without floating conversion."""
    first = _exact_vector(dim, a, "left operand")
    second = _exact_vector(dim, b, "right operand")
    out = [Fraction(0)] * dim
    for left_index, left_value in enumerate(first):
        if left_value:
            for right_index, right_value in enumerate(second):
                if right_value:
                    out[left_index ^ right_index] += cd_sign(dim, left_index, right_index) * left_value * right_value
    return tuple(out)


def basis(dim: int, index: int, scale: float = 1.0) -> list[float]:
    _dimension(dim)
    index = _index(dim, index)
    v = [0.0] * dim
    v[index] = scale
    return v


def _lmat(dim: int, m: int) -> list[list[float]]:
    _dimension(dim)
    m = _index(dim, m)
    mat = [[0.0] * dim for _ in range(dim)]
    for q in range(dim):
        mat[m ^ q][q] = float(cd_sign(dim, m, q))
    return mat


def _matmul(a: list[list[float]], b: list[list[float]]) -> list[list[float]]:
    n = len(a)
    return [[sum(a[r][k] * b[k][c] for k in range(n)) for c in range(n)] for r in range(n)]


def left_mult_matrix_check(i: int, j: int) -> list[list[float]]:
    """W = L_{e_i e_j}^{-1} L_{e_i} L_{e_j} on the octonions, pure-Python.

    e_i e_j = cd_sign(8,i,j) e_{i^j}, so L_{e_i e_j} = cd_sign(8,i,j) L_{e_{i^j}}.
    L_{e_m} is a signed permutation, hence orthogonal, so its inverse is its
    transpose.
    """
    i, j = _index(8, i), _index(8, j)
    li, lj, lij = _lmat(8, i), _lmat(8, j), _lmat(8, i ^ j)
    s = cd_sign(8, i, j)
    inv = [[lij[c][r] / s for c in range(8)] for r in range(8)]
    return _matmul(inv, _matmul(li, lj))


def associator(dim: int, x: Sequence[float], y: Sequence[float], z: Sequence[float]) -> list[float]:
    left = cd_multiply(dim, cd_multiply(dim, x, y), z)
    right = cd_multiply(dim, x, cd_multiply(dim, y, z))
    return [lv - rv for lv, rv in zip(left, right, strict=True)]


def triple_sign(dim: int, i: int, j: int, k: int) -> tuple[int, int]:
    """Return (left_sign, right_sign) for (e_i e_j) e_k vs e_i (e_j e_k).

    Both land on e_{i^j^k}; equal signs mean the triple associates.
    """
    _dimension(dim)
    i, j, k = _index(dim, i), _index(dim, j), _index(dim, k)
    left = cd_sign(dim, i, j) * cd_sign(dim, i ^ j, k)
    right = cd_sign(dim, j, k) * cd_sign(dim, i, j ^ k)
    return left, right


def classify_octonion_triples() -> tuple[int, int]:
    """Count ordered distinct imaginary-unit triples that associate vs not."""
    assoc = anti = 0
    for i, j, k in permutations(range(1, 8), 3):
        left, right = triple_sign(8, i, j, k)
        if left == right:
            assoc += 1
        else:
            anti += 1
    return assoc, anti


def fano_completion(i: int, j: int) -> int:
    """Complete the Fano line of two distinct imaginary octonion basis units."""
    i, j = _index(8, i), _index(8, j)
    if i == 0 or j == 0 or i == j:
        raise ValueError(f"Fano indices must be distinct imaginary octonion units in 1..7, got {(i, j)!r}")
    for k in range(1, 8):
        if k in (i, j):
            continue
        left, right = triple_sign(8, i, j, k)
        if left == right:
            return k
    raise RuntimeError(f"Fano line completion missing for {(i, j)}")


def _signed_zero_rows(first_pair: tuple[int, int]) -> list[tuple[int, int, int, int, int, int]]:
    i, j = first_pair
    dim = 16
    found = []
    for t in (1, -1):
        for k, el in combinations(range(1, dim), 2):
            if len({i, j, k, el}) != 4:
                continue
            for s in (1, -1):
                prod = [0] * dim
                for p, ap in ((i, 1), (j, t)):
                    for q, bq in ((k, 1), (el, s)):
                        prod[p ^ q] += cd_sign(dim, p, q) * ap * bq
                if not any(prod):
                    found.append((i, j, t, k, el, s))
    return found


def sedenion_zero_divisor_corpus() -> list[tuple[int, int, int, int, int, int]]:
    """Signed zero-divisor pairs (e_i + t e_j)(e_k + s e_l) = 0 in the sedenions.

    Returns (i, j, t, k, l, s) with t, s in {+1, -1}, i<j, k<l, and the index
    sets disjoint: the row layout (u_low, u_high, u_sign, v_low, v_high, v_sign)
    of the kernel's reggiani_standard_zero_divisor_pairs.csv.
    """
    groups = ordered_map(_signed_zero_rows, list(combinations(range(1, 16), 2)))
    return [row for group in groups for row in group]


def sedenion_zero_divisors() -> list[tuple[tuple[int, int], tuple[int, int], int]]:
    """The t = +1 half of the corpus: (e_i + e_j)(e_k + s e_l) = 0.

    Returns (i, j), (k, l), s, the operand shape design B's LCU consumes.
    """
    return [((i, j), (k, el), s) for i, j, t, k, el, s in sedenion_zero_divisor_corpus() if t == 1]


def left_mult_matrix(dim: int, v: Sequence[float]) -> list[list[float]]:
    """L_v: x -> v x as a dim x dim matrix over the basis, L_v = sum_p v_p L_{e_p}."""
    _dimension(dim)
    _length(dim, v, "vector")
    mat = [[0.0] * dim for _ in range(dim)]
    for p, vp in enumerate(v):
        if vp == 0.0:
            continue
        for q in range(dim):
            mat[p ^ q][q] += vp * cd_sign(dim, p, q)
    return mat


def left_mult_matrix_exact(dim: int, vector: Sequence[ExactScalar]) -> ExactMatrix:
    """Exact left action, whose column q is vector * e_q."""
    coefficients = _exact_vector(dim, vector, "vector")
    return tuple(
        tuple(coefficients[row ^ column] * cd_sign(dim, row ^ column, column) for column in range(dim))
        for row in range(dim)
    )


def left_mult_determinant_exact(dim: int, vector: Sequence[ExactScalar]) -> Fraction:
    """Exact determinant of the left action on rational algebra coordinates."""
    return _determinant(left_mult_matrix_exact(dim, vector))


def _determinant(mat: Sequence[Sequence[ExactScalar]]) -> Fraction:
    """Gaussian elimination on a nonempty square rational matrix."""
    n = len(mat)
    if n == 0:
        raise ValueError("determinant matrix must be nonempty")
    a = []
    for row_index, row in enumerate(mat):
        _length(n, row, f"matrix row {row_index}")
        for value in row:
            if isinstance(value, bool) or not isinstance(value, int | Fraction):
                raise ValueError(f"matrix row {row_index} requires int or Fraction entries, got {value!r}")
        a.append([Fraction(value) for value in row])
    det = Fraction(1)
    for col in range(n):
        pivot = next((r for r in range(col, n) if a[r][col] != 0), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            det = -det
        det *= a[col][col]
        for r in range(col + 1, n):
            factor = a[r][col] / a[col][col]
            if factor:
                a[r] = [x - factor * y for x, y in zip(a[r], a[col], strict=True)]
    return det


class SedenionCounterexampleFacts(TypedDict):
    det: Fraction
    square_is_scalar: bool
    square_scale: Fraction | None


def sedenion_counterexamples() -> dict[str, SedenionCounterexampleFacts]:
    """det L_v and the squared-norm identity for e_0 + e_9 and e_1 + e_9 in the sedenions.

    Neither element is a zero divisor: det L_v = 256 for both, so a predicate
    that reads only the equal norms of the two octonion halves (both 1 here)
    or the polynomial that vanishes on e_0 + e_9 misclassifies them. The
    imaginary halves of e_1 + e_9 are parallel (e_1 and e_1 after the
    doubling), so L_v^2 = -2 I rather than the orthogonal zero-divisor
    structure.
    """
    dim = 16
    out: dict[str, SedenionCounterexampleFacts] = {}
    for name, (i, j) in (("e0+e9", (0, 9)), ("e1+e9", (1, 9))):
        v = [int(index in (i, j)) for index in range(dim)]
        mat = left_mult_matrix_exact(dim, v)
        square = tuple(
            tuple(sum((mat[row][k] * mat[k][column] for k in range(dim)), Fraction(0)) for column in range(dim))
            for row in range(dim)
        )
        identity_scale = square[0][0]
        is_scalar = all(square[r][c] == (identity_scale if r == c else 0.0) for r in range(dim) for c in range(dim))
        out[name] = {
            "det": _determinant(mat),
            "square_is_scalar": is_scalar,
            "square_scale": identity_scale if is_scalar else None,
        }
    return out


def _check_sedenion_counterexamples() -> None:
    found = sedenion_counterexamples()
    for name, facts in found.items():
        if facts["det"] != 256:
            raise RuntimeError(f"{name}: det L_v = {facts['det']}, expected 256")
    if not found["e1+e9"]["square_is_scalar"] or found["e1+e9"]["square_scale"] != -2:
        raise RuntimeError(f"e1+e9: L_v^2 is not -2 I: {found['e1+e9']}")
    if found["e0+e9"]["square_is_scalar"]:
        raise RuntimeError("e0+e9: L_v^2 is scalar, but e_0 + e_9 is not purely imaginary")
    # Every corpus zero divisor has a singular L_v, the property the counterexamples lack.
    for i, j, t, _k, _l, _s in sedenion_zero_divisor_corpus()[:8]:
        v = [int(index == i) + t * int(index == j) for index in range(16)]
        if left_mult_determinant_exact(16, v) != 0:
            raise RuntimeError(f"corpus zero divisor e_{i} {t:+d} e_{j} has invertible L_v")


if __name__ == "__main__":
    _check_sedenion_counterexamples()
    print(f"sedenion counterexamples: {sedenion_counterexamples()}")
    assoc, anti = classify_octonion_triples()
    print(f"octonion ordered distinct triples: associative={assoc} anti={anti} total={assoc + anti}")
    print(f"quaternion check e1*e2 -> sign {cd_sign(8, 1, 2)} index {1 ^ 2}")
    print(f"octonion non-associativity example A(e1,e2,e4) = {associator(8, basis(8, 1), basis(8, 2), basis(8, 4))}")
    zds = sedenion_zero_divisors()
    print(f"sedenion (e_i+e_j)(e_k+-e_l)=0 zero-divisor pairs: {len(zds)}")
    for entry in zds[:5]:
        print(
            f"  (e_{entry[0][0]}+e_{entry[0][1]}) * (e_{entry[1][0]}{'+' if entry[2] > 0 else '-'}e_{entry[1][1]}) = 0"
        )
