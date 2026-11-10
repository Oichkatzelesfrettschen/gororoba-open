// SPDX-License-Identifier: GPL-2.0-or-later
//! Cayley-Dickson tower as a twisted group algebra with exact integer and modular arithmetic.
//!
//!     A_k = R^sigma[Z_2^k],   e_p * e_q = sigma_k(p, q) * e_{p ^ q}
//!
//! with sigma_k from `signs::cd_basis_mul_sign_iter`. From D = 8 on sigma_k is a 2-cochain, not a
//! 2-cocycle: its coboundary is the associator sign omega below, which is -1 exactly on the
//! non-associating triples. Every structure constant is +-1, so
//! products of integer elements are exact in i64 and products of residues are exact in F_p.
//!
//! - The basis associator [e_a, e_b, e_c] vanishes when omega(a, b, c) = +1 and equals
//!   +-2 e_{a ^ b ^ c} when omega(a, b, c) = -1 (checked on every basis triple through D = 32 by
//!   the tests below).
//! - The number of non-associating ordered triples of distinct imaginary units equals
//!   N(D) = (D - 2)(D - 4)(D + 6) / 2; the tests enumerate it through D = 64. No proof for
//!   general D is recorded here.
//! - A two-blade product (e_i + t e_j)(e_k + s e_l) with disjoint nonzero supports vanishes iff
//!   i ^ j = k ^ l and the cross-ratio chi(i, j; k, l) = +1, with t s = -sigma(i, k) sigma(j, l).
//!   The four terms land pairwise on e_{i ^ k} = e_{j ^ l} and e_{i ^ l} = e_{j ^ k}; chi = +1 is
//!   the condition that one sign s cancels both pairs.

use super::signs::cd_basis_mul_sign_iter;

/// Discrete level of the Cayley-Dickson tower.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TwistedTowerLevel {
    /// Level 0: Real numbers R (D = 1).
    Real,
    /// Level 1: Complex numbers C (D = 2).
    Complex,
    /// Level 2: Quaternions H (D = 4).
    Quaternion,
    /// Level 3: Octonions O (D = 8).
    Octonion,
    /// Level 4: Sedenions S (D = 16).
    Sedenion,
    /// Level 5: Trigintaduonions / Pathions A_5 (D = 32).
    Trigintaduonion,
    /// Level 6: Chingons A_6 (D = 64).
    Chingon,
}

impl TwistedTowerLevel {
    /// Return the tower level for a power-of-two dimension.
    pub fn from_dimension(dim: usize) -> Option<Self> {
        match dim {
            1 => Some(Self::Real),
            2 => Some(Self::Complex),
            4 => Some(Self::Quaternion),
            8 => Some(Self::Octonion),
            16 => Some(Self::Sedenion),
            32 => Some(Self::Trigintaduonion),
            64 => Some(Self::Chingon),
            _ => None,
        }
    }

    /// Return the dimension D = 2^k.
    #[inline]
    pub const fn dimension(&self) -> usize {
        match self {
            Self::Real => 1,
            Self::Complex => 2,
            Self::Quaternion => 4,
            Self::Octonion => 8,
            Self::Sedenion => 16,
            Self::Trigintaduonion => 32,
            Self::Chingon => 64,
        }
    }

    /// Number of bits required to index the basis elements (k = log2(D)).
    #[inline]
    pub const fn basis_bits(&self) -> u32 {
        match self {
            Self::Real => 0,
            Self::Complex => 1,
            Self::Quaternion => 2,
            Self::Octonion => 3,
            Self::Sedenion => 4,
            Self::Trigintaduonion => 5,
            Self::Chingon => 6,
        }
    }

    /// Whether the algebra at this level is commutative.
    #[inline]
    pub const fn is_commutative(&self) -> bool {
        matches!(self, Self::Real | Self::Complex)
    }

    /// Whether the algebra at this level is associative.
    #[inline]
    pub const fn is_associative(&self) -> bool {
        matches!(self, Self::Real | Self::Complex | Self::Quaternion)
    }

    /// Whether the algebra at this level is alternative.
    #[inline]
    pub const fn is_alternative(&self) -> bool {
        matches!(
            self,
            Self::Real | Self::Complex | Self::Quaternion | Self::Octonion
        )
    }

    /// Whether zero divisors exist at this level.
    #[inline]
    pub const fn has_zero_divisors(&self) -> bool {
        matches!(self, Self::Sedenion | Self::Trigintaduonion | Self::Chingon)
    }

    /// Closed-form count of non-associating ordered triples of distinct imaginary units,
    /// N(D) = (D - 2)(D - 4)(D + 6) / 2, equal to the enumeration through D = 64.
    pub const fn non_associating_triple_count(&self) -> usize {
        let d = self.dimension();
        if d <= 4 {
            0
        } else {
            (d - 2) * (d - 4) * (d + 6) / 2
        }
    }

    /// Maximum, over index pairs (a, b), of the algebraic normal form degree over F_2 of
    /// c -> [omega(a, b, c) = -1]: 1 at D = 8 and n - 2 for D = 2^n >= 16 (enumerated through
    /// D = 64 in the tests). The degree of one pair depends on the pair and can be lower.
    pub const fn max_associator_anf_degree(&self) -> u32 {
        let n = self.basis_bits();
        if n < 3 {
            0
        } else if n == 3 {
            1
        } else {
            n - 2
        }
    }
}

/// Bitmask representation of active basis element supports.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BasisSupportMask(pub u64);

impl BasisSupportMask {
    #[inline]
    pub const fn empty() -> Self {
        Self(0)
    }

    #[inline]
    pub const fn single(index: usize) -> Self {
        if index < 64 {
            Self(1u64 << index)
        } else {
            Self(0)
        }
    }

    #[inline]
    pub const fn pair(i: usize, j: usize) -> Self {
        Self(Self::single(i).0 | Self::single(j).0)
    }

    #[inline]
    pub const fn contains(&self, index: usize) -> bool {
        if index < 64 {
            (self.0 & (1u64 << index)) != 0
        } else {
            false
        }
    }

    #[inline]
    pub const fn popcount(&self) -> u32 {
        self.0.count_ones()
    }

    #[inline]
    pub const fn xor(&self, other: Self) -> Self {
        Self(self.0 ^ other.0)
    }

    #[inline]
    pub const fn or(&self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    #[inline]
    pub const fn and(&self, other: Self) -> Self {
        Self(self.0 & other.0)
    }
}

/// Compute the basis associator sign omega(a, b, c) for three basis elements:
///     omega(a, b, c) = sigma(a, b) * sigma(a ^ b, c) * sigma(b, c) * sigma(a, b ^ c)
///
/// Returns +1 if the triple associates ([e_a, e_b, e_c] = 0).
/// Returns -1 if the triple non-associates ([e_a, e_b, e_c] = +-2 e_{a ^ b ^ c}).
#[inline]
pub fn basis_associator_sign(dim: usize, a: usize, b: usize, c: usize) -> i32 {
    let s_ab = cd_basis_mul_sign_iter(dim, a, b);
    let s_ab_c = cd_basis_mul_sign_iter(dim, a ^ b, c);
    let s_bc = cd_basis_mul_sign_iter(dim, b, c);
    let s_a_bc = cd_basis_mul_sign_iter(dim, a, b ^ c);
    s_ab * s_ab_c * s_bc * s_a_bc
}

/// Compute the gauge-invariant cocycle cross-ratio for two pairs of basis units:
///     chi(i, j; k, l) = sigma(i, k) * sigma(j, l) * sigma(i, l) * sigma(j, k)
///
/// On the skeleton i ^ j = k ^ l, chi = +1 indicates that the signed two-blade
/// product (e_i + t e_j)(e_k + s e_l) vanishes for a suitable choice of signs t, s.
#[inline]
pub fn cocycle_cross_ratio(dim: usize, i: usize, j: usize, k: usize, l: usize) -> i32 {
    let s_ik = cd_basis_mul_sign_iter(dim, i, k);
    let s_jl = cd_basis_mul_sign_iter(dim, j, l);
    let s_il = cd_basis_mul_sign_iter(dim, i, l);
    let s_jk = cd_basis_mul_sign_iter(dim, j, k);
    s_ik * s_jl * s_il * s_jk
}

/// Check whether the pair of index pairs ((i, j), (k, l)) forms a two-blade zero divisor.
///
/// Returns Some((t, s)) with t = 1 and the unique sign s in {+1, -1} such that
/// (e_i + t e_j)(e_k + s e_l) = 0, or None if no such zero product exists.
pub fn find_two_blade_zero_divisor_signs(
    dim: usize,
    i: usize,
    j: usize,
    k: usize,
    l: usize,
) -> Option<(i32, i32)> {
    if i == 0 || j == 0 || k == 0 || l == 0 || i == j || k == l {
        return None;
    }
    // Disjoint index support
    if i == k || i == l || j == k || j == l {
        return None;
    }
    // Skeleton condition: i ^ j == k ^ l
    if (i ^ j) != (k ^ l) {
        return None;
    }
    // Cross-ratio gauge condition: chi == +1
    if cocycle_cross_ratio(dim, i, j, k, l) != 1 {
        return None;
    }

    // Solve for s when t = 1:
    // (e_i + e_j)(e_k + s e_l) =
    // sigma(i, k) e_{i^k} + s sigma(i, l) e_{i^l} + sigma(j, k) e_{j^k} + s sigma(j, l) e_{j^l}
    // Since i^j = k^l, i^k = j^l and i^l = j^k.
    // Coefficient at e_{i^k}: sigma(i, k) + s sigma(j, l) = 0 => s = -sigma(i, k) * sigma(j, l)
    let s_ik = cd_basis_mul_sign_iter(dim, i, k);
    let s_jl = cd_basis_mul_sign_iter(dim, j, l);
    let s = -s_ik * s_jl;
    Some((1, s))
}

/// Enumerate every signed two-blade zero product (e_i + t e_j)(e_k + s e_l) = 0 at dimension
/// `dim`, as tuples (i, j, t, k, l, s) with 1 <= i < j < dim, 1 <= k < l < dim, disjoint supports
/// and t, s in {+1, -1}. D = 16 gives 336 products on 42 index pairs (84 signed elements);
/// D = 32 gives 5040 products on 294 index pairs (588 signed elements).
pub fn enumerate_two_blade_zero_products(
    dim: usize,
) -> Vec<(usize, usize, i32, usize, usize, i32)> {
    let mut zds = Vec::new();
    for i in 1..dim {
        for j in (i + 1)..dim {
            for k in 1..dim {
                for l in (k + 1)..dim {
                    if let Some((t, s)) = find_two_blade_zero_divisor_signs(dim, i, j, k, l) {
                        zds.push((i, j, t, k, l, s));
                        zds.push((i, j, -t, k, l, -s));
                    }
                }
            }
        }
    }
    zds
}

/// Sized integral Cayley-Dickson element over i64 coordinates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntegralCdElement<const D: usize> {
    pub coords: [i64; D],
}

impl<const D: usize> IntegralCdElement<D> {
    pub const fn zero() -> Self {
        Self { coords: [0; D] }
    }

    pub fn basis(index: usize, scale: i64) -> Self {
        assert!(index < D, "basis index exceeds dimension");
        let mut coords = [0; D];
        coords[index] = scale;
        Self { coords }
    }

    /// Multiply two integral elements exactly using the discrete sign table.
    pub fn mul_exact(&self, other: &Self) -> Self {
        let mut out = [0i64; D];
        for p in 0..D {
            let ap = self.coords[p];
            if ap == 0 {
                continue;
            }
            for q in 0..D {
                let bq = other.coords[q];
                if bq == 0 {
                    continue;
                }
                let sign = cd_basis_mul_sign_iter(D, p, q) as i64;
                out[p ^ q] += sign * ap * bq;
            }
        }
        Self { coords: out }
    }

    /// Exact associator [a, b, c] = (a * b) * c - a * (b * c).
    pub fn associator(&self, b: &Self, c: &Self) -> Self {
        let ab = self.mul_exact(b);
        let abc_left = ab.mul_exact(c);
        let bc = b.mul_exact(c);
        let abc_right = self.mul_exact(&bc);

        let mut out = [0i64; D];
        for (i, item) in out.iter_mut().enumerate() {
            *item = abc_left.coords[i] - abc_right.coords[i];
        }
        Self { coords: out }
    }

    /// Whether this element is identically zero.
    pub fn is_zero(&self) -> bool {
        self.coords.iter().all(|&c| c == 0)
    }

    /// Bitmask of nonzero coordinate supports.
    pub fn support_mask(&self) -> BasisSupportMask {
        let mut mask = 0u64;
        for (i, &c) in self.coords.iter().enumerate() {
            if c != 0 && i < 64 {
                mask |= 1u64 << i;
            }
        }
        BasisSupportMask(mask)
    }
}

/// Sized exact modular Cayley-Dickson element over F_p (u32 residue in [0, p-1]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModularCdElement<const D: usize> {
    pub coords: [u32; D],
    pub prime: u32,
}

impl<const D: usize> ModularCdElement<D> {
    pub const fn zero(prime: u32) -> Self {
        Self {
            coords: [0; D],
            prime,
        }
    }

    pub fn basis(index: usize, scale: u32, prime: u32) -> Self {
        assert!(index < D, "basis index exceeds dimension");
        let mut coords = [0; D];
        coords[index] = scale % prime;
        Self { coords, prime }
    }

    /// Multiply two modular elements over F_p.
    pub fn mul_mod(&self, other: &Self) -> Self {
        assert_eq!(self.prime, other.prime, "primes must match");
        let p = self.prime as u64;
        let mut accum = [0u64; D];

        for i in 0..D {
            let ai = self.coords[i] as u64;
            if ai == 0 {
                continue;
            }
            for j in 0..D {
                let bj = other.coords[j] as u64;
                if bj == 0 {
                    continue;
                }
                let sign = cd_basis_mul_sign_iter(D, i, j);
                let term = (ai * bj) % p;
                let target = i ^ j;
                if sign > 0 {
                    accum[target] = (accum[target] + term) % p;
                } else {
                    accum[target] = (accum[target] + p - term) % p;
                }
            }
        }

        let mut out = [0u32; D];
        for (slot, &acc) in out.iter_mut().zip(&accum) {
            *slot = (acc % p) as u32;
        }
        Self {
            coords: out,
            prime: self.prime,
        }
    }

    /// Signed base-256 digits of each coordinate for the four-GEMM INT8 product: the residue is
    /// first centered into (-p/2, p/2], then written a = 256 a1 + a0 with a0 in [-128, 127] and
    /// a1 in [-64, 64]. The digit bounds need p < 2^15.
    ///
    /// # Panics
    ///
    /// Panics when the prime is 2^15 or larger.
    pub fn split_base256_digits(&self) -> ([i8; D], [i8; D]) {
        assert!(
            self.prime < (1 << 15),
            "base-256 digit split needs p < 2^15"
        );
        let p = self.prime as i32;
        let mut digit0 = [0i8; D];
        let mut digit1 = [0i8; D];
        for (i, &coord) in self.coords.iter().enumerate() {
            let mut val = coord as i32;
            if val > p / 2 {
                val -= p;
            }
            let a0 = (val + 128).rem_euclid(256) - 128;
            let a1 = (val - a0) / 256;
            digit0[i] = a0 as i8;
            digit1[i] = a1 as i8;
        }
        (digit0, digit1)
    }
}

#[cfg(test)]
mod tests {
    use super::super::associator::cd_associator;
    use super::super::zero_divisors::find_zero_divisors_sign_table;
    use super::*;

    const LEVELS: [TwistedTowerLevel; 7] = [
        TwistedTowerLevel::Real,
        TwistedTowerLevel::Complex,
        TwistedTowerLevel::Quaternion,
        TwistedTowerLevel::Octonion,
        TwistedTowerLevel::Sedenion,
        TwistedTowerLevel::Trigintaduonion,
        TwistedTowerLevel::Chingon,
    ];

    fn enumerated_non_associating(dim: usize) -> usize {
        let mut count = 0;
        for a in 1..dim {
            for b in 1..dim {
                for c in 1..dim {
                    if a != b && b != c && a != c && basis_associator_sign(dim, a, b, c) == -1 {
                        count += 1;
                    }
                }
            }
        }
        count
    }

    fn max_anf_degree(dim: usize) -> u32 {
        let n = dim.trailing_zeros();
        let mut best = 0;
        for a in 0..dim {
            for b in 0..dim {
                let mut t: Vec<u8> = (0..dim)
                    .map(|c| u8::from(basis_associator_sign(dim, a, b, c) == -1))
                    .collect();
                for bit in 0..n {
                    for m in 0..dim {
                        if m >> bit & 1 == 1 {
                            t[m] ^= t[m ^ (1 << bit)];
                        }
                    }
                }
                for (m, &v) in t.iter().enumerate() {
                    if v == 1 {
                        best = best.max(m.count_ones());
                    }
                }
            }
        }
        best
    }

    #[test]
    fn closed_forms_equal_enumeration() {
        for level in LEVELS {
            let dim = level.dimension();
            assert_eq!(TwistedTowerLevel::from_dimension(dim), Some(level));
            assert_eq!(1usize << level.basis_bits(), dim);
            assert_eq!(
                level.non_associating_triple_count(),
                enumerated_non_associating(dim),
                "N({dim})"
            );
            assert_eq!(
                level.max_associator_anf_degree(),
                max_anf_degree(dim),
                "ANF degree at {dim}"
            );
            assert_eq!(level.is_associative(), enumerated_non_associating(dim) == 0);
        }
        assert_eq!(
            TwistedTowerLevel::Octonion.non_associating_triple_count(),
            168
        );
        assert_eq!(
            TwistedTowerLevel::Sedenion.non_associating_triple_count(),
            1848
        );
        assert_eq!(
            TwistedTowerLevel::Trigintaduonion.non_associating_triple_count(),
            15960
        );
        assert_eq!(
            TwistedTowerLevel::Chingon.non_associating_triple_count(),
            130_200
        );
    }

    #[test]
    fn omega_decides_every_basis_associator() {
        for dim in [4usize, 8, 16, 32] {
            for a in 0..dim {
                for b in 0..dim {
                    for c in 0..dim {
                        let x = IntegralCdElement::<32>::basis(a, 1);
                        let y = IntegralCdElement::<32>::basis(b, 1);
                        let z = IntegralCdElement::<32>::basis(c, 1);
                        let assoc = embedded_associator(dim, &x, &y, &z);
                        if basis_associator_sign(dim, a, b, c) == 1 {
                            assert!(assoc.is_zero(), "({a}, {b}, {c}) at {dim}");
                        } else {
                            assert_eq!(assoc.support_mask(), BasisSupportMask::single(a ^ b ^ c));
                            assert_eq!(assoc.coords[a ^ b ^ c].abs(), 2);
                        }
                    }
                }
            }
        }
    }

    /// Associator inside the subalgebra of dimension `dim`, computed with that level's signs.
    fn embedded_associator(
        dim: usize,
        x: &IntegralCdElement<32>,
        y: &IntegralCdElement<32>,
        z: &IntegralCdElement<32>,
    ) -> IntegralCdElement<32> {
        let mul = |u: &IntegralCdElement<32>, v: &IntegralCdElement<32>| {
            let mut out = IntegralCdElement::<32>::zero();
            for p in 0..dim {
                for q in 0..dim {
                    out.coords[p ^ q] +=
                        i64::from(cd_basis_mul_sign_iter(dim, p, q)) * u.coords[p] * v.coords[q];
                }
            }
            out
        };
        let left = mul(&mul(x, y), z);
        let right = mul(x, &mul(y, z));
        let mut out = IntegralCdElement::<32>::zero();
        for i in 0..32 {
            out.coords[i] = left.coords[i] - right.coords[i];
        }
        out
    }

    #[test]
    fn octonion_fano_lines_associate() {
        for (a, b, c) in [
            (1, 2, 3),
            (1, 4, 5),
            (1, 7, 6),
            (2, 4, 6),
            (2, 5, 7),
            (3, 4, 7),
            (3, 6, 5),
        ] {
            assert_eq!(basis_associator_sign(8, a, b, c), 1, "({a}, {b}, {c})");
        }
        assert_eq!(enumerated_non_associating(8), 7 * 6 * 5 - 42);
    }

    #[test]
    fn two_blade_census_and_cross_check() {
        for (dim, products, pairs) in [(16usize, 336usize, 42usize), (32, 5040, 294)] {
            let zds = enumerate_two_blade_zero_products(dim);
            assert_eq!(zds.len(), products, "products at {dim}");
            let index_pairs: std::collections::BTreeSet<_> =
                zds.iter().map(|z| (z.0, z.1)).collect();
            let elements: std::collections::BTreeSet<_> =
                zds.iter().map(|z| (z.0, z.1, z.2)).collect();
            assert_eq!(index_pairs.len(), pairs, "index pairs at {dim}");
            assert_eq!(elements.len(), 2 * pairs, "signed elements at {dim}");
            // The existing sign-table enumerator fixes t = +1, so it lists half of the products.
            assert_eq!(
                find_zero_divisors_sign_table(dim).len(),
                products / 2,
                "sign-table enumerator at {dim}"
            );
            for &(i, j, t, k, l, s) in &zds {
                let mut a = IntegralCdElement::<32>::zero();
                a.coords[i] = 1;
                a.coords[j] = i64::from(t);
                let mut b = IntegralCdElement::<32>::zero();
                b.coords[k] = 1;
                b.coords[l] = i64::from(s);
                let mut prod = IntegralCdElement::<32>::zero();
                for p in 0..dim {
                    for q in 0..dim {
                        prod.coords[p ^ q] += i64::from(cd_basis_mul_sign_iter(dim, p, q))
                            * a.coords[p]
                            * b.coords[q];
                    }
                }
                assert!(prod.is_zero(), "({i} + {t} e{j})(e{k} + {s} e{l}) at {dim}");
            }
        }
        assert_eq!(cocycle_cross_ratio(16, 1, 10, 4, 15), 1);
    }

    #[test]
    fn sedenion_zero_divisor_has_two_two_sided_inverses() {
        // x = e1 + e10 is a zero divisor: x (e4 - e15) = (e4 - e15) x = 0. With N(x) = 2,
        // x conj(x) = conj(x) x = 2, so conj(x) / 2 and conj(x) / 2 + (e4 - e15) are both
        // two-sided inverses; integer scaling by 2 keeps the check exact.
        let mut x = IntegralCdElement::<16>::zero();
        x.coords[1] = 1;
        x.coords[10] = 1;
        let mut z = IntegralCdElement::<16>::zero();
        z.coords[4] = 1;
        z.coords[15] = -1;
        let two = IntegralCdElement::<16>::basis(0, 2);
        let mut conj = IntegralCdElement::<16>::zero();
        conj.coords[1] = -1;
        conj.coords[10] = -1;
        let mut other = conj.clone();
        other.coords[4] = 2;
        other.coords[15] = -2;
        assert!(x.mul_exact(&z).is_zero() && z.mul_exact(&x).is_zero());
        for y in [&conj, &other] {
            assert_eq!(x.mul_exact(y), two);
            assert_eq!(y.mul_exact(&x), two);
        }
        assert_ne!(conj, other);
    }

    #[test]
    fn modular_product_and_digit_split() {
        let p = 32009u32;
        let mut a = ModularCdElement::<32>::zero(p);
        let mut b = ModularCdElement::<32>::zero(p);
        a.coords[1] = 1;
        a.coords[10] = 1;
        b.coords[4] = 1;
        b.coords[15] = 1;
        let prod = a.mul_mod(&b);
        assert_eq!(prod.coords[5], 2);
        assert_eq!(prod.coords[14], p - 2);

        // Every residue of F_32009 splits into in-range digits that reconstruct it mod p.
        for start in (0..p).step_by(32) {
            let mut elem = ModularCdElement::<32>::zero(p);
            for (i, slot) in elem.coords.iter_mut().enumerate() {
                *slot = (start + i as u32).min(p - 1);
            }
            let (d0, d1) = elem.split_base256_digits();
            for i in 0..32 {
                assert!((-64..=64).contains(&d1[i]), "a1 out of range");
                let value = 256 * i64::from(d1[i]) + i64::from(d0[i]);
                assert_eq!(value.rem_euclid(i64::from(p)), i64::from(elem.coords[i]));
            }
        }
    }

    #[test]
    #[should_panic(expected = "p < 2^15")]
    fn digit_split_rejects_wide_primes() {
        let elem = ModularCdElement::<4>::zero(40_009);
        let _ = elem.split_base256_digits();
    }

    #[test]
    fn quaternion_associates_and_octonion_does_not() {
        let e = |dim: usize, i: usize| {
            let mut v = vec![0.0; dim];
            v[i] = 1.0;
            v
        };
        let quat = cd_associator(&e(4, 1), &e(4, 2), &e(4, 3));
        assert!(quat.iter().all(|&v| v == 0.0));
        let oct = cd_associator(&e(8, 1), &e(8, 2), &e(8, 4));
        assert_eq!(oct.iter().map(|v| v * v).sum::<f64>(), 4.0);
    }
}
