// SPDX-License-Identifier: GPL-2.0-or-later
//! Cayley-Dickson tower as a twisted group algebra with exact integer and modular arithmetic.
//!
//! ```text
//! A_k = R^sigma[Z_2^k],   e_p * e_q = sigma_k(p, q) * e_{p ^ q}
//! ```
//!
//! with sigma_k from `signs::cd_basis_mul_sign_iter`; the twisted-group-algebra reading follows
//! `docs/physics/sedenion_standard_model.md`. From D = 8 on sigma_k is a 2-cochain, not a
//! 2-cocycle: its coboundary is the associator sign omega below, which is -1 exactly on the
//! non-associating triples. Every structure constant is +-1, so a product coordinate is a signed
//! sum of coordinate products.
//!
//! Domain contract: the dimension is a power of two in 1..=64 (the support mask holds 64
//! coordinates). `IntegralCdElement::mul_exact` checks every product and sum in i64 and returns
//! `Overflow` rather than a wrapped value, so an `Ok` product is exact. `ModularCdElement` holds
//! a prime modulus and residues below it, so `mul_mod` is exact in F_p; `new` reduces its input.
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
//!   the condition that one sign s cancels both pairs. The tests check every listed product at
//!   D = 16 and 32 and match the census against the sign-table enumerator; no wider range is
//!   tested.

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
///
/// # Panics
///
/// Panics in builds with debug assertions when `dim` is not a power of two or an index is not
/// below `dim`.
#[inline]
pub fn basis_associator_sign(dim: usize, a: usize, b: usize, c: usize) -> i32 {
    let s_ab = cd_basis_mul_sign_iter(dim, a, b);
    let s_ab_c = cd_basis_mul_sign_iter(dim, a ^ b, c);
    let s_bc = cd_basis_mul_sign_iter(dim, b, c);
    let s_a_bc = cd_basis_mul_sign_iter(dim, a, b ^ c);
    s_ab * s_ab_c * s_bc * s_a_bc
}

/// Compute the twist cross-ratio of two pairs of basis units, a product of four values of the
/// 2-cochain sigma:
///     chi(i, j; k, l) = sigma(i, k) * sigma(j, l) * sigma(i, l) * sigma(j, k)
///
/// A gauge change sigma'(p, q) = sigma(p, q) g(p) g(q) g(p ^ q) with g(p) in {+1, -1} multiplies
/// chi by g(i ^ k) g(j ^ l) g(i ^ l) g(j ^ k). That factor is 1 for every g exactly when
/// i ^ j = k ^ l (the XOR skeleton); off the skeleton chi depends on the gauge and the function
/// accepts such arguments without checking the skeleton. On the skeleton, chi = +1 indicates
/// that the signed two-blade product (e_i + t e_j)(e_k + s e_l) vanishes for a suitable choice
/// of signs t, s.
///
/// # Panics
///
/// Panics in builds with debug assertions when `dim` is not a power of two or an index is not
/// below `dim`.
#[inline]
pub fn twist_cross_ratio(dim: usize, i: usize, j: usize, k: usize, l: usize) -> i32 {
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
///
/// # Panics
///
/// Panics in builds with debug assertions when `dim` is not a power of two or an index is not
/// below `dim`.
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
    if twist_cross_ratio(dim, i, j, k, l) != 1 {
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
///
/// # Panics
///
/// Panics in builds with debug assertions when `dim` is not a power of two.
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

/// Failure of a checked twisted-tower construction or product.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TwistedTowerError {
    /// The dimension is not a power of two in 1..=64.
    InvalidDimension(usize),
    /// The modulus is not a prime.
    InvalidModulus(u32),
    /// An i64 coordinate product or sum left the i64 range.
    Overflow,
}

impl std::fmt::Display for TwistedTowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidDimension(dim) => {
                write!(f, "dimension {dim} is not a power of two in 1..=64")
            }
            Self::InvalidModulus(p) => write!(f, "modulus {p} is not prime"),
            Self::Overflow => write!(f, "integer coordinate product left the i64 range"),
        }
    }
}

impl std::error::Error for TwistedTowerError {}

/// The support mask holds 64 coordinates and the sign recursion needs a power of two.
const fn check_dimension(dim: usize) -> Result<(), TwistedTowerError> {
    if dim.is_power_of_two() && dim <= 64 {
        Ok(())
    } else {
        Err(TwistedTowerError::InvalidDimension(dim))
    }
}

/// Deterministic trial division; the largest u32 divisor bound is 65535.
const fn is_prime_u32(n: u32) -> bool {
    if n < 2 {
        return false;
    }
    if n.is_multiple_of(2) {
        return n == 2;
    }
    let n = n as u64;
    let mut d = 3u64;
    while d * d <= n {
        if n.is_multiple_of(d) {
            return false;
        }
        d += 2;
    }
    true
}

/// Sized integral Cayley-Dickson element over i64 coordinates.
///
/// The dimension `D` is a power of two in 1..=64, checked by every constructor; the coordinates
/// are private so no element of another shape exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IntegralCdElement<const D: usize> {
    coords: [i64; D],
}

impl<const D: usize> IntegralCdElement<D> {
    /// Build an element from its coordinates.
    ///
    /// # Errors
    ///
    /// Returns `InvalidDimension` when `D` is not a power of two in 1..=64.
    pub const fn new(coords: [i64; D]) -> Result<Self, TwistedTowerError> {
        match check_dimension(D) {
            Ok(()) => Ok(Self { coords }),
            Err(e) => Err(e),
        }
    }

    /// The zero element.
    ///
    /// # Errors
    ///
    /// Returns `InvalidDimension` when `D` is not a power of two in 1..=64.
    pub const fn zero() -> Result<Self, TwistedTowerError> {
        Self::new([0; D])
    }

    /// The element `scale * e_index`.
    ///
    /// # Errors
    ///
    /// Returns `InvalidDimension` when `D` is not a power of two in 1..=64.
    ///
    /// # Panics
    ///
    /// Panics when `index >= D`.
    pub fn basis(index: usize, scale: i64) -> Result<Self, TwistedTowerError> {
        check_dimension(D)?;
        assert!(index < D, "basis index exceeds dimension");
        let mut coords = [0; D];
        coords[index] = scale;
        Ok(Self { coords })
    }

    /// The coordinates in basis order.
    pub const fn coords(&self) -> &[i64; D] {
        &self.coords
    }

    /// Multiply two integral elements with the discrete sign table. Every coordinate product and
    /// every running sum is checked, so an `Ok` result is the exact product in Z^D.
    ///
    /// # Errors
    ///
    /// Returns `Overflow` when a coordinate product or sum leaves the i64 range.
    pub fn mul_exact(&self, other: &Self) -> Result<Self, TwistedTowerError> {
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
                let sign = i64::from(cd_basis_mul_sign_iter(D, p, q));
                let term = ap
                    .checked_mul(bq)
                    .and_then(|t| t.checked_mul(sign))
                    .ok_or(TwistedTowerError::Overflow)?;
                out[p ^ q] = out[p ^ q]
                    .checked_add(term)
                    .ok_or(TwistedTowerError::Overflow)?;
            }
        }
        Ok(Self { coords: out })
    }

    /// Exact associator [a, b, c] = (a * b) * c - a * (b * c).
    ///
    /// # Errors
    ///
    /// Returns `Overflow` when a product or the final difference leaves the i64 range.
    pub fn associator(&self, b: &Self, c: &Self) -> Result<Self, TwistedTowerError> {
        let ab = self.mul_exact(b)?;
        let abc_left = ab.mul_exact(c)?;
        let bc = b.mul_exact(c)?;
        let abc_right = self.mul_exact(&bc)?;

        let mut out = [0i64; D];
        for (i, item) in out.iter_mut().enumerate() {
            *item = abc_left.coords[i]
                .checked_sub(abc_right.coords[i])
                .ok_or(TwistedTowerError::Overflow)?;
        }
        Ok(Self { coords: out })
    }

    /// Whether this element is identically zero.
    pub fn is_zero(&self) -> bool {
        self.coords.iter().all(|&c| c == 0)
    }

    /// Bitmask of nonzero coordinate supports.
    pub fn support_mask(&self) -> BasisSupportMask {
        let mut mask = 0u64;
        for (i, &c) in self.coords.iter().enumerate() {
            if c != 0 {
                mask |= 1u64 << i;
            }
        }
        BasisSupportMask(mask)
    }
}

/// Sized exact modular Cayley-Dickson element over F_p (u32 residue in [0, p-1]).
///
/// The modulus is a prime, the dimension `D` is a power of two in 1..=64, and every residue is
/// reduced below p; the constructors establish these and the fields are private.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModularCdElement<const D: usize> {
    coords: [u32; D],
    prime: u32,
}

impl<const D: usize> ModularCdElement<D> {
    /// Build an element, reducing each coordinate modulo `prime`.
    ///
    /// # Errors
    ///
    /// Returns `InvalidDimension` when `D` is not a power of two in 1..=64 and `InvalidModulus`
    /// when `prime` is not prime.
    pub fn new(mut coords: [u32; D], prime: u32) -> Result<Self, TwistedTowerError> {
        check_dimension(D)?;
        if !is_prime_u32(prime) {
            return Err(TwistedTowerError::InvalidModulus(prime));
        }
        for c in &mut coords {
            *c %= prime;
        }
        Ok(Self { coords, prime })
    }

    /// The zero element.
    ///
    /// # Errors
    ///
    /// Same as [`Self::new`].
    pub fn zero(prime: u32) -> Result<Self, TwistedTowerError> {
        Self::new([0; D], prime)
    }

    /// The element `scale * e_index` with `scale` reduced modulo `prime`.
    ///
    /// # Errors
    ///
    /// Same as [`Self::new`].
    ///
    /// # Panics
    ///
    /// Panics when `index >= D`.
    pub fn basis(index: usize, scale: u32, prime: u32) -> Result<Self, TwistedTowerError> {
        let mut coords = [0; D];
        assert!(index < D, "basis index exceeds dimension");
        coords[index] = scale;
        Self::new(coords, prime)
    }

    /// The residues in basis order, each in [0, p-1].
    pub const fn coords(&self) -> &[u32; D] {
        &self.coords
    }

    /// The prime modulus.
    pub const fn prime(&self) -> u32 {
        self.prime
    }

    /// Multiply two modular elements over F_p.
    ///
    /// # Panics
    ///
    /// Panics when the two moduli differ.
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

    fn izero<const D: usize>() -> IntegralCdElement<D> {
        IntegralCdElement::zero().expect("valid dimension")
    }

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
                        let x = IntegralCdElement::<32>::basis(a, 1).expect("valid basis");
                        let y = IntegralCdElement::<32>::basis(b, 1).expect("valid basis");
                        let z = IntegralCdElement::<32>::basis(c, 1).expect("valid basis");
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
            let mut out = izero::<32>();
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
        let mut out = izero::<32>();
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
                let mut a = izero::<32>();
                a.coords[i] = 1;
                a.coords[j] = i64::from(t);
                let mut b = izero::<32>();
                b.coords[k] = 1;
                b.coords[l] = i64::from(s);
                let mut prod = izero::<32>();
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
        assert_eq!(twist_cross_ratio(16, 1, 10, 4, 15), 1);
    }

    /// Gauge-changed sign sigma'(p, q) = sigma(p, q) g(p) g(q) g(p ^ q).
    fn gauged_sign(dim: usize, g: &[i32], p: usize, q: usize) -> i32 {
        cd_basis_mul_sign_iter(dim, p, q) * g[p] * g[q] * g[p ^ q]
    }

    fn gauged_cross_ratio(dim: usize, g: &[i32], i: usize, j: usize, k: usize, l: usize) -> i32 {
        gauged_sign(dim, g, i, k)
            * gauged_sign(dim, g, j, l)
            * gauged_sign(dim, g, i, l)
            * gauged_sign(dim, g, j, k)
    }

    #[test]
    fn twist_cross_ratio_is_gauge_invariant_only_on_the_xor_skeleton() {
        let dim = 16usize;
        let mut state = 0x2545_f491_u32;
        for _ in 0..8 {
            let mut g = vec![1i32; dim];
            for slot in g.iter_mut().skip(1) {
                state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
                *slot = if state >> 31 == 1 { -1 } else { 1 };
            }
            for i in 1..dim {
                for j in 1..dim {
                    for k in 1..dim {
                        for l in 1..dim {
                            if i ^ j == k ^ l {
                                assert_eq!(
                                    gauged_cross_ratio(dim, &g, i, j, k, l),
                                    twist_cross_ratio(dim, i, j, k, l),
                                    "({i}, {j}; {k}, {l})"
                                );
                            }
                        }
                    }
                }
            }
        }
        // Off the skeleton (1 ^ 2 != 3 ^ 4) the gauge g(e1) = -1 flips chi.
        let mut g = vec![1i32; dim];
        g[1] = -1;
        assert_eq!(twist_cross_ratio(dim, 1, 2, 3, 4), -1);
        assert_eq!(gauged_cross_ratio(dim, &g, 1, 2, 3, 4), 1);
    }

    #[test]
    fn sedenion_zero_divisor_has_two_two_sided_inverses() {
        // x = e1 + e10 is a zero divisor: x (e4 - e15) = (e4 - e15) x = 0. With N(x) = 2,
        // x conj(x) = conj(x) x = 2, so conj(x) / 2 and conj(x) / 2 + (e4 - e15) are both
        // two-sided inverses; integer scaling by 2 keeps the check exact.
        let mut x = izero::<16>();
        x.coords[1] = 1;
        x.coords[10] = 1;
        let mut z = izero::<16>();
        z.coords[4] = 1;
        z.coords[15] = -1;
        let two = IntegralCdElement::<16>::basis(0, 2).expect("valid basis");
        let mut conj = izero::<16>();
        conj.coords[1] = -1;
        conj.coords[10] = -1;
        let mut other = conj.clone();
        other.coords[4] = 2;
        other.coords[15] = -2;
        assert!(x.mul_exact(&z).unwrap().is_zero() && z.mul_exact(&x).unwrap().is_zero());
        for y in [&conj, &other] {
            assert_eq!(x.mul_exact(y).unwrap(), two);
            assert_eq!(y.mul_exact(&x).unwrap(), two);
        }
        assert_ne!(conj, other);
    }

    #[test]
    fn modular_product_and_digit_split() {
        let p = 32009u32;
        let mut a = ModularCdElement::<32>::zero(p).expect("prime modulus");
        let mut b = ModularCdElement::<32>::zero(p).expect("prime modulus");
        a.coords[1] = 1;
        a.coords[10] = 1;
        b.coords[4] = 1;
        b.coords[15] = 1;
        let prod = a.mul_mod(&b);
        assert_eq!(prod.coords[5], 2);
        assert_eq!(prod.coords[14], p - 2);

        // Every residue of F_32009 splits into in-range digits that reconstruct it mod p.
        for start in (0..p).step_by(32) {
            let mut elem = ModularCdElement::<32>::zero(p).expect("prime modulus");
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
        let elem = ModularCdElement::<4>::zero(40_009).expect("prime modulus");
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

    #[test]
    fn integer_product_reports_overflow_instead_of_wrapping() {
        let big = IntegralCdElement::<1>::basis(0, i64::MAX).expect("valid basis");
        assert_eq!(big.mul_exact(&big), Err(TwistedTowerError::Overflow));
        // Each coordinate product fits in i64; the running sum x^2 + y^2 does not.
        let x = 2_500_000_000i64;
        let a = IntegralCdElement::<2>::new([x, x]).expect("valid dimension");
        let b = IntegralCdElement::<2>::new([x, -x]).expect("valid dimension");
        assert_eq!(a.mul_exact(&b), Err(TwistedTowerError::Overflow));
        let ok = IntegralCdElement::<2>::new([3, 4]).expect("valid dimension");
        let conj = IntegralCdElement::<2>::new([3, -4]).expect("valid dimension");
        assert_eq!(ok.mul_exact(&conj).expect("in range").coords(), &[25, 0]);
        let m = IntegralCdElement::<8>::basis(1, i64::MAX).expect("valid basis");
        let n = IntegralCdElement::<8>::basis(2, i64::MAX).expect("valid basis");
        assert_eq!(m.associator(&n, &m), Err(TwistedTowerError::Overflow));
    }

    #[test]
    fn modulus_must_be_prime_and_residues_are_reduced() {
        for bad in [0u32, 1, 4, 9, 32_011 * 3, u32::MAX] {
            assert_eq!(
                ModularCdElement::<4>::zero(bad),
                Err(TwistedTowerError::InvalidModulus(bad)),
                "modulus {bad}"
            );
        }
        for good in [2u32, 3, 32_009, 4_294_967_291] {
            assert!(ModularCdElement::<4>::zero(good).is_ok(), "modulus {good}");
        }
        let elem = ModularCdElement::<4>::new([5, 7, 0, u32::MAX], 3).expect("prime modulus");
        assert_eq!(elem.prime(), 3);
        assert_eq!(elem.coords(), &[2, 1, 0, 0]);
        let basis = ModularCdElement::<4>::basis(1, 10, 7).expect("prime modulus");
        assert_eq!(basis.coords(), &[0, 3, 0, 0]);
    }

    #[test]
    fn dimension_must_be_a_power_of_two_up_to_64() {
        assert_eq!(
            IntegralCdElement::<3>::zero(),
            Err(TwistedTowerError::InvalidDimension(3))
        );
        assert_eq!(
            IntegralCdElement::<0>::zero(),
            Err(TwistedTowerError::InvalidDimension(0))
        );
        assert_eq!(
            IntegralCdElement::<128>::zero(),
            Err(TwistedTowerError::InvalidDimension(128))
        );
        assert_eq!(
            ModularCdElement::<6>::zero(7),
            Err(TwistedTowerError::InvalidDimension(6))
        );
        assert_eq!(
            ModularCdElement::<128>::zero(7),
            Err(TwistedTowerError::InvalidDimension(128))
        );
        let top = IntegralCdElement::<64>::basis(63, 1).expect("valid basis");
        assert_eq!(top.support_mask(), BasisSupportMask::single(63));
        assert!(ModularCdElement::<64>::zero(7).is_ok());
    }
}
