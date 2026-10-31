// SPDX-License-Identifier: MIT
//! Synthetic identifiability experiment compiler; not physical evidence.
//!
//! For a target signature `t` and a nuisance design matrix `N`, the residual
//! `r = (I - P_N) t` is the part of `t` no nuisance combination reproduces.
//! `P_N` is built from the SVD pseudo-inverse of `N`, with singular values
//! below `f64::EPSILON * max(rows, cols) * sigma_max` truncated, so
//! rank-deficient nuisance families give a well-defined projector. Unpivoted
//! QR returns a wrong projector on such matrices.
//!
//! Usage: `identifiability-compiler`

use nalgebra::{DMatrix, DVector};

/// Diagnostics of a target against a nuisance family.
#[derive(Debug, Clone, Copy)]
pub struct Diagnostics {
    pub identifiable_fraction: f64,
    pub principal_angle_deg: f64,
    pub efficient_fisher_info: f64,
}

/// Residual of `target` after least-squares projection onto the column span
/// of `nuisance`, computed through the truncated SVD pseudo-inverse.
pub fn orth_residual(target: &DVector<f64>, nuisance: &DMatrix<f64>) -> DVector<f64> {
    let svd = nuisance.clone().svd(true, true);
    let sigma_max = svd.singular_values.max();
    let cutoff = f64::EPSILON * nuisance.nrows().max(nuisance.ncols()) as f64 * sigma_max;
    let coef = svd
        .solve(target, cutoff)
        .expect("SVD computed with both singular-vector factors");
    target - nuisance * coef
}

/// Identifiable fraction `|r| / |t|`, its principal angle, and the efficient
/// Fisher information `r.r / sigma^2`.
pub fn diagnostics(target: &DVector<f64>, nuisance: &DMatrix<f64>, sigma: f64) -> Diagnostics {
    let r = orth_residual(target, nuisance);
    let frac = r.norm() / target.norm();
    Diagnostics {
        identifiable_fraction: frac,
        principal_angle_deg: frac.clamp(0.0, 1.0).asin().to_degrees(),
        efficient_fisher_info: r.dot(&r) / (sigma * sigma),
    }
}

fn columns(cols: &[Vec<f64>]) -> DMatrix<f64> {
    DMatrix::from_fn(cols[0].len(), cols.len(), |i, j| cols[j][i])
}

/// Commutator design: target `q*a*b` against the declared nuisance family.
pub fn commutator_problem() -> (DVector<f64>, DMatrix<f64>) {
    let levels = [-1.0, -0.5, 0.5, 1.0];
    let (mut a, mut b, mut q, mut k) = (vec![], vec![], vec![], vec![]);
    for &ai in &levels {
        for &bi in &levels {
            for &qi in &[-1.0, 1.0] {
                for &ki in &[-1.0, 0.0, 1.0] {
                    a.push(ai);
                    b.push(bi);
                    q.push(qi);
                    k.push(ki);
                }
            }
        }
    }
    let f = |g: &dyn Fn(usize) -> f64| (0..a.len()).map(g).collect::<Vec<f64>>();
    let target = f(&|i| q[i] * a[i] * b[i]);
    let n = columns(&[
        f(&|_| 1.0),
        a.clone(),
        b.clone(),
        f(&|i| a[i] * b[i]),
        f(&|i| a[i] * a[i]),
        f(&|i| b[i] * b[i]),
        k.clone(),
        f(&|i| k[i] * k[i]),
        f(&|i| q[i] * a[i]),
        f(&|i| q[i] * b[i]),
        f(&|i| q[i] * (a[i] * a[i] - b[i] * b[i])),
        f(&|i| q[i] * k[i]),
        f(&|i| q[i] * a[i] * k[i]),
        f(&|i| q[i] * b[i] * k[i]),
    ]);
    (DVector::from_vec(target), n)
}

/// Boundary-differential design grid and its base nuisance matrix.
pub struct BoundaryProblem {
    pub d: Vec<f64>,
    pub z: Vec<f64>,
    pub s: Vec<f64>,
    pub c: Vec<f64>,
    pub target: DVector<f64>,
    pub nuisance: DMatrix<f64>,
}

pub fn boundary_problem() -> BoundaryProblem {
    let (mut d, mut z, mut v, mut s, mut c) = (vec![], vec![], vec![], vec![], vec![]);
    for step in 0..13 {
        let di = 100.0 + 25.0 * step as f64;
        for &vi in &[-0.15, -0.075, 0.0, 0.075, 0.15] {
            for &si in &[-1.0, 1.0] {
                for &ci in &[-1.0, 1.0] {
                    d.push(di);
                    z.push(200.0 / di);
                    v.push(vi);
                    s.push(si);
                    c.push(ci);
                }
            }
        }
    }
    let f = |g: &dyn Fn(usize) -> f64| (0..d.len()).map(g).collect::<Vec<f64>>();
    let shape = |i: usize| {
        z[i].powi(4)
            * (1.0 + 0.55 * (-((d[i] - 220.0) / 42.0).powi(2)).exp()
                - 0.25 * (-((d[i] - 135.0) / 30.0).powi(2)).exp())
    };
    let target = f(&|i| s[i] * c[i] * shape(i));
    let n = columns(&[
        f(&|_| 1.0),
        z.clone(),
        f(&|i| z[i] * z[i]),
        f(&|i| z[i].powi(4)),
        v.clone(),
        f(&|i| v[i] * v[i] * z[i] * z[i]),
        s.clone(),
        f(&|i| s[i] * z[i] * z[i]),
        f(&|i| s[i] * v[i] * z[i] * z[i]),
        f(&|i| s[i] * v[i] * v[i] * z[i] * z[i]),
        f(&|i| s[i] * z[i].powi(5)),
        f(&|i| s[i] * z[i].powi(6)),
        c.clone(),
        f(&|i| c[i] * z[i] * z[i]),
        f(&|i| c[i] * v[i] * z[i] * z[i]),
        f(&|i| s[i] * c[i]),
        f(&|i| s[i] * c[i] * z[i] * z[i]),
        f(&|i| s[i] * c[i] * v[i] * z[i] * z[i]),
    ]);
    BoundaryProblem {
        d,
        z,
        s,
        c,
        target: DVector::from_vec(target),
        nuisance: n,
    }
}

/// Boundary nuisance matrix expanded by three target-adjacent columns.
pub fn boundary_expanded(p: &BoundaryProblem) -> DMatrix<f64> {
    let m = p.d.len();
    let extra = [
        (0..m)
            .map(|i| p.s[i] * p.c[i] * p.z[i].powi(3))
            .collect::<Vec<_>>(),
        (0..m)
            .map(|i| p.s[i] * p.c[i] * p.z[i].powi(5))
            .collect::<Vec<_>>(),
        (0..m)
            .map(|i| p.s[i] * p.c[i] * (-((p.d[i] - 220.0) / 60.0).powi(2)).exp())
            .collect::<Vec<_>>(),
    ];
    let base = &p.nuisance;
    DMatrix::from_fn(m, base.ncols() + 3, |i, j| {
        if j < base.ncols() {
            base[(i, j)]
        } else {
            extra[j - base.ncols()][i]
        }
    })
}

fn append_column(n: &DMatrix<f64>, col: &DVector<f64>) -> DMatrix<f64> {
    let mut out = n.clone().insert_column(n.ncols(), 0.0);
    out.column_mut(n.ncols()).copy_from(col);
    out
}

fn report(label: &str, d: &Diagnostics) {
    println!(
        "{label} {{'identifiable_fraction': {:?}, 'principal_angle_deg': {:?}, 'efficient_fisher_info': {:?}}}",
        d.identifiable_fraction, d.principal_angle_deg, d.efficient_fisher_info
    );
}

fn main() {
    let (t, n) = commutator_problem();
    report("commutator", &diagnostics(&t, &n, 0.08));
    report(
        "commutator_adversarial",
        &diagnostics(&t, &append_column(&n, &t), 0.08),
    );
    let p = boundary_problem();
    report("boundary", &diagnostics(&p.target, &p.nuisance, 0.12));
    report(
        "boundary_expanded",
        &diagnostics(&p.target, &boundary_expanded(&p), 0.12),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_target_nuisance_collapses_identifiability() {
        let (t, n) = commutator_problem();
        let d = diagnostics(&t, &append_column(&n, &t), 0.08);
        assert!(d.identifiable_fraction < 1e-10, "{d:?}");
    }

    #[test]
    fn commutator_target_is_distinct_from_declared_nuisances() {
        let (t, n) = commutator_problem();
        let d = diagnostics(&t, &n, 0.08);
        assert!(d.identifiable_fraction > 0.9, "{d:?}");
        assert!(d.principal_angle_deg > 60.0, "{d:?}");
    }

    /// The grid draws no random numbers, so base and expanded fractions are
    /// fixed at 0.264486 and 0.027178, a collapse of 9.73 times.
    #[test]
    fn boundary_full_grid_loses_most_information_under_adversarial_expansion() {
        let p = boundary_problem();
        let base = diagnostics(&p.target, &p.nuisance, 0.12).identifiable_fraction;
        let expanded = diagnostics(&p.target, &boundary_expanded(&p), 0.12).identifiable_fraction;
        assert!((base - 0.264486).abs() < 1e-6, "{base}");
        assert!((expanded - 0.027178).abs() < 1e-6, "{expanded}");
        assert!(expanded < 0.11 * base);
    }

    #[test]
    fn rank_deficient_nuisance_projects_onto_column_span() {
        let n = DMatrix::from_row_slice(4, 2, &[1.0, 2.0, 1.0, 2.0, 1.0, 2.0, 1.0, 2.0]);
        let t = DVector::from_vec(vec![1.0, 2.0, 3.0, 4.0]);
        let r = orth_residual(&t, &n);
        assert!((r.sum()).abs() < 1e-12);
        assert!((r.norm() - (5.0f64).sqrt()).abs() < 1e-12);
    }
}
