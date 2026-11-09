//! Cayley-Dickson twisted tower architecture and exact representation mapping.
//!
//! This module formalizes the multi-tier twisted group algebra tower:
//!
//!     A_k = R^sigma[Z_2^k]
//!
//! with basis product e_p * e_q = sigma_k(p, q) * e_{p ^ q}, across exact integer
//! bit widths (Int4, Int8, Int16, Int32, Int64) and floating-point representations
//! (Float8 through Float64).
//!
//! # Epistemic Principles
//!
//! 1. The Cayley-Dickson tower is fundamentally integer-exact and combinatorial.
//!    Its structure is fully determined by the 2-cocycle twist sigma_k and the
//!    F_2 vector space skeleton (Z_2^k, ^).
//! 2. IEEE 754 floating-point representations introduce extrinsic non-associativity
//!    at the scalar level ((a + b) + c != a + (b + c)). Exact algebraic diagnostics
//!    must operate over discrete integer coordinates or verified modular fields F_p.
//! 3. Zero divisors (ZDs) vanish for D <= 8 (Hurwitz division theorem) and appear
//!    at D = 16 (sedenions) governed by the gauge-invariant cocycle cross-ratio:
//!    chi(i, j; k, l) = sigma(i, k) * sigma(j, l) * sigma(i, l) * sigma(j, k) = +1
//!    on the skeleton i ^ j = k ^ l.
//! 4. The associator tensor [e_a, e_b, e_c] = (e_a e_b) e_c - e_a (e_b e_c) is
//!    non-zero if and only if omega(a, b, c) = -1, yielding exactly
//!    N(D) = (D - 2)(D - 4)(D + 6) / 2 non-associating ordered triples of distinct
//!    imaginary units.

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

    /// Exact closed-form count of non-associating ordered triples of distinct imaginary units:
    /// N(D) = (D - 2)(D - 4)(D + 6) / 2
    pub const fn non_associating_triple_count(&self) -> usize {
        let d = self.dimension();
        if d <= 4 {
            0
        } else {
            (d - 2) * (d - 4) * (d + 6) / 2
        }
    }

    /// Theoretical algebraic normal form (ANF) degree of the associator truth table.
    /// For D = 2^n >= 16, degree is n - 2; for D = 8, degree is 1; for D <= 4, degree is 0.
    pub const fn associator_anf_degree(&self) -> u32 {
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

/// Enumerate all 336 signed two-blade zero divisor products in the sedenion algebra (D = 16).
/// These arise from 168 ordered pairs of index pairs with chi = +1, across 42 distinct
/// assessor pairs (84 signed two-blade elements).
/// Returns tuples (i, j, t, k, l, s) with 1 <= i < j <= 15, 1 <= k < l <= 15,
/// {i, j} disjoint from {k, l}, and (e_i + t e_j)(e_k + s e_l) = 0.
pub fn enumerate_sedenion_zero_divisors() -> Vec<(usize, usize, i32, usize, usize, i32)> {
    let dim = 16;
    let mut zds = Vec::with_capacity(84);
    for i in 1..dim {
        for j in (i + 1)..dim {
            for k in 1..dim {
                for l in (k + 1)..dim {
                    if let Some((t, s)) = find_two_blade_zero_divisor_signs(dim, i, j, k, l) {
                        zds.push((i, j, t, k, l, s));
                        // The opposite sign pair t = -1, -s is also a zero divisor
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

    /// Decompose each coordinate into signed base-256 digits (a = 256 * a1 + a0),
    /// matching the RTX 4070 Ti SM89 Layer 1 exact modular GEMM architecture:
    /// a0 in [-128, 127], a1 in [-64, 64].
    pub fn split_base256_digits(&self) -> ([i8; D], [i8; D]) {
        let mut digit0 = [0i8; D];
        let mut digit1 = [0i8; D];

        for (i, &coord) in self.coords.iter().enumerate() {
            let val = coord as i32;
            let mut a0 = val % 256;
            let mut a1 = val / 256;
            if a0 > 127 {
                a0 -= 256;
                a1 += 1;
            }
            digit0[i] = a0 as i8;
            digit1[i] = a1 as i8;
        }

        (digit0, digit1)
    }
}

/// Sized floating-point Cayley-Dickson element over f64 coordinates with exact sign routing.
#[derive(Clone, Debug, PartialEq)]
pub struct FloatingCdElement<const D: usize> {
    pub coords: [f64; D],
}

impl<const D: usize> FloatingCdElement<D> {
    pub const fn zero() -> Self {
        Self { coords: [0.0; D] }
    }

    pub fn basis(index: usize, scale: f64) -> Self {
        assert!(index < D, "basis index exceeds dimension");
        let mut coords = [0.0; D];
        coords[index] = scale;
        Self { coords }
    }

    /// Multiply two floating-point elements using exact discrete sign routing.
    pub fn mul_exact_signs(&self, other: &Self) -> Self {
        let mut out = [0.0; D];
        for p in 0..D {
            let ap = self.coords[p];
            if ap == 0.0 {
                continue;
            }
            for q in 0..D {
                let bq = other.coords[q];
                if bq == 0.0 {
                    continue;
                }
                let sign = cd_basis_mul_sign_iter(D, p, q) as f64;
                out[p ^ q] += sign * ap * bq;
            }
        }
        Self { coords: out }
    }

    /// Compute the associator [a, b, c] = (a * b) * c - a * (b * c).
    pub fn associator(&self, b: &Self, c: &Self) -> Self {
        let ab = self.mul_exact_signs(b);
        let abc_left = ab.mul_exact_signs(c);
        let bc = b.mul_exact_signs(c);
        let abc_right = self.mul_exact_signs(&bc);

        let mut out = [0.0; D];
        for (i, item) in out.iter_mut().enumerate() {
            *item = abc_left.coords[i] - abc_right.coords[i];
        }
        Self { coords: out }
    }

    /// Squared Euclidean norm.
    pub fn norm_sq(&self) -> f64 {
        self.coords.iter().map(|&x| x * x).sum()
    }

    /// Euclidean norm.
    pub fn norm(&self) -> f64 {
        self.norm_sq().sqrt()
    }
}

/// Hardware execution target for the Cayley-Dickson twisted tower operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum HardwarePlatform {
    /// Quandela Ascella: 12-mode Clements dual-rail integrated photonic processor.
    Ascella12Mode,
    /// Quandela Belenos: remote multi-mode photonic processor.
    Belenos,
    /// IBM Heron: 156-qubit superconducting heavy-hex lattice.
    IbmHeronHeavyHex,
    /// NVIDIA RTX 4070 Ti (SM89): Tensor core INT8/INT32 and FP8 modular GEMM.
    Rtx4070TiSm89,
    /// Quantum Inspire Tuna-17: 17-qubit spin / transmon processor.
    Tuna17,
}

impl HardwarePlatform {
    /// Supported maximum exact Cayley-Dickson dimension for single-shot kernel evaluation.
    pub const fn max_supported_dimension(&self) -> usize {
        match self {
            Self::Ascella12Mode => 32,      // 8-mode kernel slice + 4 sentinels
            Self::Belenos => 64,            // Scaled LOQC mesh
            Self::IbmHeronHeavyHex => 64,   // Parity network mapping up to 64D
            Self::Rtx4070TiSm89 => 65536,   // Exact GEMM up to n = 32768+ via HMM
            Self::Tuna17 => 32,             // Parity blocks for A_5
        }
    }

    /// Dominant execution precision for algebraic operations.
    pub const fn primary_precision(&self) -> &'static str {
        match self {
            Self::Ascella12Mode => "Discrete single-photon clicks (optical Haar unitary)",
            Self::Belenos => "Discrete single-photon clicks (scaled linear optical)",
            Self::IbmHeronHeavyHex => "Binary parity syndromes (Z_2^k XOR bitstrings)",
            Self::Rtx4070TiSm89 => "INT8 tensor core GEMM with INT32 accumulation (exact F_p)",
            Self::Tuna17 => "Transmon microwave parity syndromes",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tower_level_properties() {
        let real = TwistedTowerLevel::Real;
        assert_eq!(real.dimension(), 1);
        assert!(real.is_commutative());
        assert!(real.is_associative());
        assert!(!real.has_zero_divisors());

        let oct = TwistedTowerLevel::Octonion;
        assert_eq!(oct.dimension(), 8);
        assert!(!oct.is_commutative());
        assert!(!oct.is_associative());
        assert!(oct.is_alternative());
        assert!(!oct.has_zero_divisors());
        assert_eq!(oct.non_associating_triple_count(), 168);
        assert_eq!(oct.associator_anf_degree(), 1);

        let sed = TwistedTowerLevel::Sedenion;
        assert_eq!(sed.dimension(), 16);
        assert!(!sed.is_alternative());
        assert!(sed.has_zero_divisors());
        assert_eq!(sed.non_associating_triple_count(), 1848);
        assert_eq!(sed.associator_anf_degree(), 2);

        let path = TwistedTowerLevel::Trigintaduonion;
        assert_eq!(path.dimension(), 32);
        assert!(path.has_zero_divisors());
        assert_eq!(path.non_associating_triple_count(), 15960);
        assert_eq!(path.associator_anf_degree(), 3);
    }

    #[test]
    fn test_octonion_fano_lines_and_associators() {
        let dim = 8;
        // Lines in the standard Fano plane (e1..e7) associate: omega = +1
        // Standard Fano triples: {1, 2, 3}, {1, 4, 5}, {1, 7, 6}, {2, 4, 6}, {2, 5, 7}, {3, 4, 7}, {3, 6, 5}
        let fano_triples = [
            (1, 2, 3),
            (1, 4, 5),
            (1, 7, 6),
            (2, 4, 6),
            (2, 5, 7),
            (3, 4, 7),
            (3, 6, 5),
        ];

        for &(a, b, c) in &fano_triples {
            assert_eq!(
                basis_associator_sign(dim, a, b, c),
                1,
                "Fano line ({a}, {b}, {c}) must associate"
            );
        }

        // Count total non-associating ordered triples of distinct imaginary units
        let mut non_assoc = 0;
        let mut assoc = 0;
        for a in 1..dim {
            for b in 1..dim {
                if b == a {
                    continue;
                }
                for c in 1..dim {
                    if c == a || c == b {
                        continue;
                    }
                    if basis_associator_sign(dim, a, b, c) == -1 {
                        non_assoc += 1;
                    } else {
                        assoc += 1;
                    }
                }
            }
        }

        // 7 * 6 * 5 = 210 distinct imaginary triples.
        // N(8) = 168 non-associating triples.
        // 210 - 168 = 42 associating triples (7 Fano lines * 6 permutations).
        assert_eq!(non_assoc, 168);
        assert_eq!(assoc, 42);
        assert_eq!(non_assoc + assoc, 210);
    }

    #[test]
    fn test_sedenion_zero_divisors_cross_ratio() {
        let dim = 16;
        // Known de Marrais assessor zero divisor: (e1 + e10)(e4 - e15) = 0
        // i=1, j=10, k=4, l=15.
        // Skeleton condition: 1 ^ 10 = 11, 4 ^ 15 = 11. Match!
        assert_eq!(1 ^ 10, 4 ^ 15);
        let chi = cocycle_cross_ratio(dim, 1, 10, 4, 15);
        assert_eq!(chi, 1, "Gauge-invariant cross-ratio must be +1 for zero divisor");

        let zds = enumerate_sedenion_zero_divisors();
        // Sedenions contain exactly 336 signed two-blade zero divisor products
        assert_eq!(zds.len(), 336);

        // Verify that there are exactly 42 distinct assessor pairs {i, j} and 84 signed elements
        let mut distinct_pairs = std::collections::BTreeSet::new();
        let mut distinct_elements = std::collections::BTreeSet::new();
        for &(i, j, t, _, _, _) in &zds {
            distinct_pairs.insert((i, j));
            distinct_elements.insert((i, j, t));
        }
        assert_eq!(distinct_pairs.len(), 42);
        assert_eq!(distinct_elements.len(), 84);

        // Verify every enumerated zero divisor algebraically with IntegralCdElement
        for &(i, j, t, k, l, s) in &zds {
            let mut a = IntegralCdElement::<16>::zero();
            a.coords[i] = 1;
            a.coords[j] = t as i64;

            let mut b = IntegralCdElement::<16>::zero();
            b.coords[k] = 1;
            b.coords[l] = s as i64;

            let prod = a.mul_exact(&b);
            assert!(
                prod.is_zero(),
                "Candidate ({i} + {t}*{j}) * ({k} + {s}*{l}) must vanish"
            );
        }
    }

    #[test]
    fn test_modular_exact_product_and_base256_split() {
        let p = 32009u32;
        let mut a = ModularCdElement::<32>::zero(p);
        let mut b = ModularCdElement::<32>::zero(p);

        // A_5 operands from Ascella kernel slice: (e1 + e10)(e4 + e15) = 2*(e5 - e14)
        a.coords[1] = 1;
        a.coords[10] = 1;
        b.coords[4] = 1;
        b.coords[15] = 1;

        let prod = a.mul_mod(&b);
        assert_eq!(prod.coords[5], 2);
        assert_eq!(prod.coords[14], p - 2); // -2 mod p

        // Test base-256 signed digit splitting
        let mut elem = ModularCdElement::<32>::zero(p);
        elem.coords[0] = 300; // 300 = 256 * 1 + 44
        elem.coords[1] = 32000; // near p
        let (d0, d1) = elem.split_base256_digits();
        assert_eq!(d0[0], 44);
        assert_eq!(d1[0], 1);
    }

    #[test]
    fn test_floating_associator_quads() {
        // In H (D=4), associator must vanish identically
        let a = FloatingCdElement::<4>::basis(1, 1.0);
        let b = FloatingCdElement::<4>::basis(2, 1.0);
        let c = FloatingCdElement::<4>::basis(3, 1.0);
        let assoc = a.associator(&b, &c);
        assert!(assoc.norm() < 1e-12);

        // In O (D=8), non-Fano triple (1, 2, 4) has non-zero associator
        let a8 = FloatingCdElement::<8>::basis(1, 1.0);
        let b8 = FloatingCdElement::<8>::basis(2, 1.0);
        let c8 = FloatingCdElement::<8>::basis(4, 1.0);
        let assoc8 = a8.associator(&b8, &c8);
        assert!(assoc8.norm() > 1.99); // norm is exactly 2.0
    }
}
