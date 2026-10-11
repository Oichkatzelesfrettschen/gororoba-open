//! Sedenion annihilator analysis via SVD nullspace computation.
//!
//! For a sedenion element `a`, the left multiplication matrix L_a has
//! L_a * b = a * b for all b. Its nullspace is the left annihilator of `a`.
//! Similarly, the right multiplication matrix R_a has R_a * b = b * a.
//!
//! A nonzero element is a zero divisor when its multiplication matrix has a
//! nontrivial kernel. SVD tolerance measures numerical proximity to singularity;
//! `crate::exact_annihilator` supplies exact certificates for rational input.
//! Reggiani (2024) defines ZD(S) as the submanifold of
//! sedenions with squared norm 2 and nontrivial annihilators.
//!
//! # Literature
//! - Reggiani (2024): Geometry of sedenion zero divisors

use cd_kernel::cayley_dickson::cd_multiply;
use nalgebra::{DMatrix, SVD};

/// Dimensions of left and right annihilator subspaces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnnihilatorInfo {
    pub left_nullity: usize,
    pub right_nullity: usize,
}

/// Build the dim x dim left multiplication matrix L_a: L_a * b = a * b.
pub fn left_multiplication_matrix(a: &[f64], dim: usize) -> DMatrix<f64> {
    assert_eq!(a.len(), dim);
    assert!(
        dim.is_power_of_two(),
        "dimension must be a positive power of two"
    );
    assert!(
        a.iter().all(|coordinate| coordinate.is_finite()),
        "coordinates must be finite"
    );
    let mut mat = DMatrix::zeros(dim, dim);
    for i in 0..dim {
        let mut e = vec![0.0; dim];
        e[i] = 1.0;
        let col = cd_multiply(a, &e);
        for (r, &val) in col.iter().enumerate() {
            mat[(r, i)] = val;
        }
    }
    mat
}

/// Build the dim x dim right multiplication matrix R_a: R_a * b = b * a.
pub fn right_multiplication_matrix(a: &[f64], dim: usize) -> DMatrix<f64> {
    assert_eq!(a.len(), dim);
    assert!(
        dim.is_power_of_two(),
        "dimension must be a positive power of two"
    );
    assert!(
        a.iter().all(|coordinate| coordinate.is_finite()),
        "coordinates must be finite"
    );
    let mut mat = DMatrix::zeros(dim, dim);
    for i in 0..dim {
        let mut e = vec![0.0; dim];
        e[i] = 1.0;
        let col = cd_multiply(&e, a);
        for (r, &val) in col.iter().enumerate() {
            mat[(r, i)] = val;
        }
    }
    mat
}

/// Compute an orthonormal basis for the right nullspace of `mat` using SVD.
///
/// Returns a matrix of shape (n, k) where k = dim(nullspace).
/// Singular values at most `atol` are treated as zero.
pub fn nullspace_basis(mat: &DMatrix<f64>, atol: f64) -> DMatrix<f64> {
    assert!(
        atol.is_finite() && atol > 0.0,
        "tolerance must be finite and positive"
    );
    assert!(
        mat.iter().all(|entry| entry.is_finite()),
        "matrix entries must be finite"
    );
    let n = mat.ncols();
    if n == 0 {
        return DMatrix::zeros(0, 0);
    }
    if mat.nrows() == 0 {
        return DMatrix::identity(n, n);
    }
    // Zero rows retain the kernel and make nalgebra's thin V^T contain all
    // right singular vectors when the input has more columns than rows.
    let padded = DMatrix::from_fn(mat.nrows().max(n), n, |row, column| {
        if row < mat.nrows() {
            mat[(row, column)]
        } else {
            0.0
        }
    });
    let svd = SVD::new(padded, false, true);
    let singular = &svd.singular_values;

    let rank = singular.iter().filter(|&&s| s > atol).count();
    if rank == n {
        return DMatrix::zeros(n, 0);
    }

    // V^T rows rank..n-1 form the nullspace basis
    let vt = svd.v_t.expect("SVD should compute V^T");
    let nullity = n - rank;
    let mut basis = DMatrix::zeros(n, nullity);
    for col in 0..nullity {
        let row_idx = rank + col;
        for r in 0..n {
            basis[(r, col)] = vt[(row_idx, r)];
        }
    }
    basis
}

/// Compute annihilator dimensions for a Cayley-Dickson element.
pub fn annihilator_info(a: &[f64], dim: usize, atol: f64) -> AnnihilatorInfo {
    let la = left_multiplication_matrix(a, dim);
    let ra = right_multiplication_matrix(a, dim);
    let left_nullity = nullspace_basis(&la, atol).ncols();
    let right_nullity = nullspace_basis(&ra, atol).ncols();
    AnnihilatorInfo {
        left_nullity,
        right_nullity,
    }
}

/// Numerical singularity heuristic for nonzero finite Cayley-Dickson input.
/// `atol` is an absolute singular-value threshold, so rescaling the input can
/// change the answer. Use an exact certificate for a membership claim.
pub fn is_zero_divisor(a: &[f64], dim: usize, atol: f64) -> bool {
    if !valid_numerical_input(a, dim, atol) || a.iter().all(|&coordinate| coordinate == 0.0) {
        return false;
    }
    let info = annihilator_info(a, dim, atol);
    info.left_nullity > 0 || info.right_nullity > 0
}

/// Check membership in Reggiani's ZD(S): squared norm 2 and nontrivial annihilator.
///
/// This matches the diagonal-form zero divisors (e_i +/- e_j) which have
/// squared Euclidean norm 2.
pub fn is_reggiani_zd(a: &[f64], atol: f64) -> bool {
    if !valid_numerical_input(a, 16, atol) {
        return false;
    }
    let norm_sq: f64 = a.iter().map(|x| x * x).sum();
    if (norm_sq - 2.0).abs() > atol {
        return false;
    }
    is_zero_divisor(a, 16, atol)
}

/// Find a nonzero left annihilator b such that a*b = 0, if one exists.
pub fn find_left_annihilator_vector(a: &[f64], dim: usize, atol: f64) -> Option<Vec<f64>> {
    if !valid_numerical_input(a, dim, atol) {
        return None;
    }
    let la = left_multiplication_matrix(a, dim);
    let ns = nullspace_basis(&la, atol);
    if ns.ncols() == 0 {
        return None;
    }
    Some(ns.column(0).iter().copied().collect())
}

fn valid_numerical_input(coordinates: &[f64], dimension: usize, tolerance: f64) -> bool {
    coordinates.len() == dimension
        && dimension.is_power_of_two()
        && coordinates.iter().all(|coordinate| coordinate.is_finite())
        && tolerance.is_finite()
        && tolerance > 0.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numerical_membership_rejects_zero_and_invalid_domains() {
        assert!(!is_zero_divisor(&[0.0; 16], 16, 1e-12));
        assert!(!is_zero_divisor(&[1.0; 15], 15, 1e-12));
        assert!(!is_zero_divisor(&[1.0; 16], 8, 1e-12));
        for invalid in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            let mut input = [0.0; 16];
            input[1] = invalid;
            assert!(!is_zero_divisor(&input, 16, 1e-12));
            assert!(!is_reggiani_zd(&input, 1e-12));
            assert_eq!(find_left_annihilator_vector(&input, 16, 1e-12), None);
        }
        for tolerance in [0.0, -1.0, f64::NAN, f64::INFINITY] {
            assert!(!is_zero_divisor(&[1.0; 16], 16, tolerance));
            assert!(!is_reggiani_zd(&[1.0; 16], tolerance));
        }
    }

    #[test]
    fn rectangular_nullspace_retains_missing_right_singular_vectors() {
        let matrix = DMatrix::from_row_slice(1, 3, &[1.0, 0.0, 0.0]);
        let kernel = nullspace_basis(&matrix, 1e-12);
        assert_eq!(kernel.shape(), (3, 2));
        assert!((&matrix * &kernel).norm() < 1e-12);
        assert!((kernel.transpose() * kernel - DMatrix::identity(2, 2)).norm() < 1e-12);
        assert_eq!(
            nullspace_basis(&DMatrix::zeros(0, 3), 1e-12),
            DMatrix::identity(3, 3)
        );
        assert_eq!(
            nullspace_basis(&DMatrix::zeros(3, 0), 1e-12).shape(),
            (0, 0)
        );
    }

    #[test]
    fn test_known_zero_divisor_has_nontrivial_annihilator() {
        // (e1 + e10) * (e4 - e15) = 0 under our Cayley-Dickson convention
        let mut a = vec![0.0; 16];
        let mut b = vec![0.0; 16];
        a[1] = 1.0;
        a[10] = 1.0;
        b[4] = 1.0;
        b[15] = -1.0;

        let prod = cd_multiply(&a, &b);
        assert!(
            prod.iter().all(|&x| x.abs() < 1e-12),
            "Should be zero product"
        );

        let info = annihilator_info(&a, 16, 1e-12);
        assert!(info.left_nullity >= 1, "Left nullity should be >= 1");
        assert!(is_reggiani_zd(&a, 1e-12), "Should be in Reggiani ZD(S)");

        let found = find_left_annihilator_vector(&a, 16, 1e-12);
        assert!(found.is_some(), "Should find an annihilator");
        let ann = found.unwrap();
        let check = cd_multiply(&a, &ann);
        assert!(
            check.iter().all(|&x| x.abs() < 1e-10),
            "Annihilator should annihilate"
        );
    }

    #[test]
    fn test_basis_unit_is_not_zero_divisor() {
        // e_1 squares to -1, so it is invertible
        let mut e1 = vec![0.0; 16];
        e1[1] = 1.0;
        let info = annihilator_info(&e1, 16, 1e-12);
        assert_eq!(info.left_nullity, 0);
        assert_eq!(info.right_nullity, 0);
        assert!(!is_reggiani_zd(&e1, 1e-12));
    }

    #[test]
    fn test_unit_normalized_zd_not_in_reggiani() {
        // (e1 + e10) / sqrt(2) has norm 1, not 2 -- fails Reggiani criterion
        let mut a = vec![0.0; 16];
        a[1] = 1.0 / 2.0_f64.sqrt();
        a[10] = 1.0 / 2.0_f64.sqrt();
        let norm_sq: f64 = a.iter().map(|x| x * x).sum();
        assert!((norm_sq - 1.0).abs() < 1e-12);
        assert!(is_zero_divisor(&a, 16, 1e-12));
        assert!(!is_reggiani_zd(&a, 1e-12));
    }

    #[test]
    fn test_all_primitive_assessor_diagonals_have_nullity_4() {
        // The 84 standard zero-divisors (42 assessors * 2 signs) all have
        // left nullity 4 and right nullity 4
        use crate::boxkites::primitive_assessors;
        for a in &primitive_assessors() {
            for sign in [1.0_f64, -1.0] {
                let diag = a.diagonal(sign);
                let info = annihilator_info(&diag, 16, 1e-12);
                assert_eq!(
                    info.left_nullity, 4,
                    "Assessor ({},{}) sign={sign}: left nullity {} != 4",
                    a.low, a.high, info.left_nullity
                );
                assert_eq!(
                    info.right_nullity, 4,
                    "Assessor ({},{}) sign={sign}: right nullity {} != 4",
                    a.low, a.high, info.right_nullity
                );
            }
        }
    }
}
