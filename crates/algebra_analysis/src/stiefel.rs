//! Imaginary-octonion frame checks for sedenion zero-divisor elements.
//!
//! A nonzero sedenion z = (a,b) is a zero divisor when both octonion
//! scalar parts vanish, the imaginary halves have equal norms, and their
//! inner product vanishes. At fixed nonzero norm, independently normalizing
//! the halves gives V_2(R^7), the orthonormal two-frames in imaginary
//! octonions. Full R^8 half balance and orthogonality omit the scalar
//! constraints: e0+e9 satisfies those two conditions and is invertible.
//!
//! Numerical residuals establish proximity to the component constraints.
//! The finite assessor census retains exact zero-product witnesses; neither
//! computation supplies a proof of the global manifold identification.
//! The transport functions separately operate on generic R^8 frames.

/// Result of finite sedenion frame checks.
#[derive(Debug, Clone)]
pub struct StiefelVerification {
    /// Ambient CD dimension (16 for sedenions).
    pub dim: usize,
    /// Candidate evaluations, including repeated zero-product factors.
    /// Random candidates satisfy a numerical singular-value threshold.
    pub n_samples: usize,
    /// Candidates satisfying scalar purity and the imaginary-frame tolerance.
    pub n_stiefel: usize,
    /// Maximum normalized imaginary-half inner product in absolute value.
    /// An inadmissible frame contributes infinity.
    pub max_ortho_violation: f64,
    /// Maximum absolute imaginary-half norm difference before rescaling.
    /// Admission divides the absolute difference by the sum of half norms.
    /// An inadmissible frame contributes infinity.
    pub max_norm_violation: f64,
    /// Fraction of evaluated candidates satisfying the frame tolerance.
    /// An empty candidate set returns zero and establishes an empty sample.
    pub stiefel_fraction: f64,
}

/// Numerical singularity of left multiplication at a fixed tolerance.
fn is_zero_divisor(coordinates: &[f64]) -> bool {
    if coordinates.len() != 16
        || coordinates.iter().any(|coordinate| !coordinate.is_finite())
        || coordinates.iter().all(|coordinate| *coordinate == 0.0)
    {
        return false;
    }
    let matrix = crate::annihilator::left_multiplication_matrix(coordinates, 16);
    let decomposition = nalgebra::linalg::SVD::new(matrix, false, false);
    decomposition
        .singular_values
        .iter()
        .any(|value| *value < 1e-8)
}

/// Decompose a sedenion into its octonion halves.
fn decompose_halves(coordinates: &[f64]) -> (&[f64], &[f64]) {
    assert_eq!(coordinates.len(), 16);
    (&coordinates[..8], &coordinates[8..])
}

/// Euclidean inner product.
fn inner_product(first: &[f64], second: &[f64]) -> f64 {
    first
        .iter()
        .zip(second)
        .map(|(left, right)| left * right)
        .sum()
}

/// Euclidean norm of a bounded vector.
fn vec_norm(coordinates: &[f64]) -> f64 {
    inner_product(coordinates, coordinates).sqrt()
}

/// Normalize finite nonzero coordinates after removing their common scale.
fn normalized_vector(coordinates: &[f64]) -> Option<Vec<f64>> {
    if coordinates.iter().any(|coordinate| !coordinate.is_finite()) {
        return None;
    }
    let scale = coordinates
        .iter()
        .map(|coordinate| coordinate.abs())
        .fold(0.0, f64::max);
    if scale == 0.0 {
        return None;
    }
    let mut normalized: Vec<_> = coordinates
        .iter()
        .map(|coordinate| coordinate / scale)
        .collect();
    let norm = vec_norm(&normalized);
    for coordinate in &mut normalized {
        *coordinate /= norm;
    }
    Some(normalized)
}

#[derive(Debug, Clone, Copy, PartialEq)]
struct StiefelFrameResiduals {
    absolute_norm_balance: f64,
    relative_norm_balance: f64,
    orthogonality: f64,
}

/// Residuals of a finite, doubly-pure sedenion with nonzero imaginary halves.
/// Scaling before squaring keeps the checks meaningful at extreme magnitudes.
/// Admission uses ||a|-|b||/(|a|+|b|); the absolute difference remains a report.
fn stiefel_frame_residuals(coordinates: &[f64]) -> Option<StiefelFrameResiduals> {
    if coordinates.len() != 16
        || coordinates.iter().any(|coordinate| !coordinate.is_finite())
        || coordinates[0] != 0.0
        || coordinates[8] != 0.0
    {
        return None;
    }
    let scale = coordinates
        .iter()
        .map(|coordinate| coordinate.abs())
        .fold(0.0, f64::max);
    if scale == 0.0 {
        return None;
    }
    let first: Vec<_> = coordinates[1..8]
        .iter()
        .map(|coordinate| coordinate / scale)
        .collect();
    let second: Vec<_> = coordinates[9..16]
        .iter()
        .map(|coordinate| coordinate / scale)
        .collect();
    let first_norm = vec_norm(&first);
    let second_norm = vec_norm(&second);
    if first_norm == 0.0 || second_norm == 0.0 {
        return None;
    }
    let scaled_norm_difference = (first_norm - second_norm).abs();
    let absolute_norm_balance = scaled_norm_difference * scale;
    let relative_norm_balance = scaled_norm_difference / (first_norm + second_norm);
    let orthogonality = first
        .iter()
        .zip(&second)
        .map(|(left, right)| (left / first_norm) * (right / second_norm))
        .sum::<f64>()
        .abs();
    Some(StiefelFrameResiduals {
        absolute_norm_balance,
        relative_norm_balance,
        orthogonality,
    })
}

fn record_stiefel_candidate(result: &mut StiefelVerification, coordinates: &[f64], tolerance: f64) {
    result.n_samples += 1;
    let Some(residuals) = stiefel_frame_residuals(coordinates) else {
        result.max_norm_violation = f64::INFINITY;
        result.max_ortho_violation = f64::INFINITY;
        return;
    };
    result.max_norm_violation = result
        .max_norm_violation
        .max(residuals.absolute_norm_balance);
    result.max_ortho_violation = result.max_ortho_violation.max(residuals.orthogonality);
    if residuals.relative_norm_balance < tolerance && residuals.orthogonality < tolerance {
        result.n_stiefel += 1;
    }
}

fn empty_stiefel_verification() -> StiefelVerification {
    StiefelVerification {
        dim: 16,
        n_samples: 0,
        n_stiefel: 0,
        max_ortho_violation: 0.0,
        max_norm_violation: 0.0,
        stiefel_fraction: 0.0,
    }
}

/// Construct a unit sedenion from two seeded imaginary-octonion directions.
fn random_stiefel_candidate(rng: &mut impl rand::Rng) -> Option<[f64; 16]> {
    use rand::RngExt;

    let mut first_direction = [0.0; 7];
    let mut second_direction = [0.0; 7];
    for coordinate in &mut first_direction {
        *coordinate = rng.random_range(-1.0..1.0);
    }
    for coordinate in &mut second_direction {
        *coordinate = rng.random_range(-1.0..1.0);
    }
    let first = normalized_vector(&first_direction)?;
    let mut second = normalized_vector(&second_direction)?;
    // Reorthogonalization removes cancellation left by the first projection.
    for _ in 0..2 {
        let projection = inner_product(&first, &second);
        for (second_coordinate, first_coordinate) in second.iter_mut().zip(&first) {
            *second_coordinate -= projection * first_coordinate;
        }
    }
    if vec_norm(&second) < 1e-12 {
        return None;
    }
    let second = normalized_vector(&second)?;
    let mut coordinates = [0.0; 16];
    for (coordinate, direction) in coordinates[1..8].iter_mut().zip(first) {
        *coordinate = std::f64::consts::FRAC_1_SQRT_2 * direction;
    }
    for (coordinate, direction) in coordinates[9..16].iter_mut().zip(second) {
        *coordinate = std::f64::consts::FRAC_1_SQRT_2 * direction;
    }
    Some(coordinates)
}

/// Check a seeded, constrained finite sample of V_2(R^7) imaginary frames.
/// Normalized cube draws supply the directions; Gram-Schmidt projection and
/// equal half scaling construct unit 16D candidates with scalar parts zero.
/// Relative balance and normalized orthogonality require tolerance 1e-10.
/// Each recorded candidate also passes a left-multiplication SVD threshold
/// of 1e-8. The SVD check is a floating diagnostic, rather than an exact
/// zero-product certificate or a proof of the global geometric identification.
/// A zero request returns the empty report; every successful nonzero request
/// returns exactly the requested count.
///
/// # Panics
/// Panics if the requested count overflows the attempt budget or if 100
/// attempts per requested candidate exhaust before the complete sample passes
/// both numerical checks.
pub fn verify_stiefel_condition(n_samples: usize, seed: u64) -> StiefelVerification {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let mut result = empty_stiefel_verification();
    let max_attempts = n_samples
        .checked_mul(100)
        .expect("requested Stiefel sample count exceeds finite attempt budget");
    let mut attempts = 0;
    while result.n_samples < n_samples && attempts < max_attempts {
        attempts += 1;
        let Some(coordinates) = random_stiefel_candidate(&mut rng) else {
            continue;
        };
        let Some(residuals) = stiefel_frame_residuals(&coordinates) else {
            continue;
        };
        if residuals.relative_norm_balance >= 1e-10 || residuals.orthogonality >= 1e-10 {
            continue;
        }
        if is_zero_divisor(&coordinates) {
            record_stiefel_candidate(&mut result, &coordinates, 1e-10);
        }
    }
    assert_eq!(
        result.n_samples, n_samples,
        "Stiefel sample exhausted {max_attempts} attempts before collecting {n_samples} candidates"
    );
    if result.n_samples > 0 {
        result.stiefel_fraction = result.n_stiefel as f64 / result.n_samples as f64;
    }
    result
}

/// Check the finite diagonal factors supplied by exact zero-product witnesses.
/// The first factor is evaluated once per returned solution and unordered
/// partner pair, so the count includes repetitions. The frame checks require zero scalar parts,
/// nonzero imaginary halves, and relative balance/orthogonality below 1e-10.
pub fn verify_stiefel_algebraic() -> StiefelVerification {
    use crate::boxkites::{cross_assessors, diagonal_zero_products_exact};

    let pairs = cross_assessors(16);
    let mut result = empty_stiefel_verification();
    for (pair_index, &first_pair) in pairs.iter().enumerate() {
        for &second_pair in &pairs[(pair_index + 1)..] {
            for &(first_sign, _) in &diagonal_zero_products_exact(16, first_pair, second_pair) {
                let mut coordinates = [0.0f64; 16];
                coordinates[first_pair.0] = 1.0;
                coordinates[first_pair.1] = f64::from(first_sign);
                record_stiefel_candidate(&mut result, &coordinates, 1e-10);
            }
        }
    }
    if result.n_samples > 0 {
        result.stiefel_fraction = result.n_stiefel as f64 / result.n_samples as f64;
    }
    result
}

// ---------------------------------------------------------------------------
// Frame transport in R^8 and G_2 calibration
// ---------------------------------------------------------------------------

/// Comparison of a transported tangent vector with a second frame vector.
/// The legacy field names describe an endpoint comparison along one sphere
/// geodesic. A closed transport loop requires a separately specified path.
#[derive(Debug, Clone, Copy)]
pub struct HolonomyResult {
    /// Geodesic distance on S^7 between u1 and u2 (in radians).
    pub geodesic_distance: f64,
    /// Endpoint angle between the transported first and second frame vectors
    /// (in radians, range [0, pi]).
    pub holonomy_angle: f64,
    /// Inner product of the transported first and normalized second tangent vector.
    pub projected_inner_product: f64,
}

/// Compare parallel transport between generic orthonormal R^8 two-frames.
/// Each input contains two finite, nonzero eight-coordinate vectors. The
/// normalized halves must be orthogonal within 1e-10. Scalar purity and norm
/// balance are separate sedenion constraints and are outside this geometric
/// domain. Antipodal endpoints have an ambiguous geodesic and return None.
/// Sphere transport alone supplies neither zero-divisor membership nor an
/// algebraic nonassociativity witness.
pub fn holonomy_between(z1: &[f64], z2: &[f64]) -> Option<HolonomyResult> {
    if z1.len() != 16 || z2.len() != 16 {
        return None;
    }
    let (a1, b1) = decompose_halves(z1);
    let (a2, b2) = decompose_halves(z2);
    let u1 = normalized_vector(a1)?;
    let v1 = normalized_vector(b1)?;
    let u2 = normalized_vector(a2)?;
    let v2 = normalized_vector(b2)?;
    if inner_product(&u1, &v1).abs() >= 1e-10 || inner_product(&u2, &v2).abs() >= 1e-10 {
        return None;
    }

    let cos_d = inner_product(&u1, &u2).clamp(-1.0, 1.0);
    let geodesic_distance = cos_d.acos();

    // Parallel transport v1 along the geodesic from u1 to u2 on S^7.
    // For a great circle parameterised by gamma(t) = cos(t)*u1 + sin(t)*e,
    // where e = (u2 - cos_d*u1) / sin_d  is the unit tangent,
    // the parallel transport of v along gamma is:
    //   v(t) = v - <v,u1>*u1 - <v,e>*e
    //        + [<v,u1>*cos(t) - <v,e>*sin(t)] * gamma(t)/|gamma|
    //        + [<v,u1>*sin(t) + <v,e>*cos(t)] * gamma'(t)/|gamma'|
    //
    // Simplified Schild's ladder approach for the sphere:
    //   P_transport(v1) = v1 - (<v1,u1> + <v1,u2>)/(1 + cos_d) * (u1 + u2)
    //                      + 2*<v1,u1> * u2
    // (valid when cos_d > -1, i.e. u1 != -u2)

    // Distinguish near-identical (d ~ 0) from near-antipodal (d ~ pi).
    // sin(0) = sin(pi) = 0, so we must check geodesic_distance directly.
    let near_zero_tol = 1e-12;
    let near_pi_tol = 1e-12;

    let v1_transported = if geodesic_distance < near_zero_tol {
        // u1 ~ u2: parallel transport is identity
        v1.clone()
    } else if (std::f64::consts::PI - geodesic_distance) < near_pi_tol {
        // u1 ~ -u2 (antipodal): geodesic is non-unique and parallel
        // transport is path-dependent.  No single deterministic holonomy
        // angle exists, so we return None.
        return None;
    } else {
        // Rodrigues-type parallel transport formula on S^n:
        // PT(v) = v - (<v,u1>+<v,u2>)/(1+cos_d) * (u1+u2) + 2<v,u1>*u2
        let vu1 = inner_product(&v1, &u1);
        let vu2 = inner_product(&v1, &u2);
        let coeff = (vu1 + vu2) / (1.0 + cos_d);
        let mut pt = vec![0.0_f64; 8];
        for k in 0..8 {
            pt[k] = v1[k] - coeff * (u1[k] + u2[k]) + 2.0 * vu1 * u2[k];
        }
        // Project out u2 component to stay in tangent space at u2
        let pt_u2 = inner_product(&pt, &u2);
        for k in 0..8 {
            pt[k] -= pt_u2 * u2[k];
        }
        // Re-normalise
        let pt_norm = vec_norm(&pt);
        if pt_norm > 1e-14 {
            for x in &mut pt {
                *x /= pt_norm;
            }
        }
        pt
    };

    // Project v2 orthogonal to u2 (it should already be, but ensure numerical cleanliness)
    let v2u2 = inner_product(&v2, &u2);
    let mut v2_orth: Vec<f64> = v2
        .iter()
        .zip(u2.iter())
        .map(|(&vi, &ui)| vi - v2u2 * ui)
        .collect();
    let v2_orth_norm = vec_norm(&v2_orth);
    if v2_orth_norm > 1e-14 {
        for x in &mut v2_orth {
            *x /= v2_orth_norm;
        }
    }

    let proj_ip = inner_product(&v1_transported, &v2_orth).clamp(-1.0, 1.0);
    let holonomy_angle = proj_ip.acos();

    Some(HolonomyResult {
        geodesic_distance,
        holonomy_angle,
        projected_inner_product: proj_ip,
    })
}

/// G_2-orbit invariant: the octonion triple cross-product of three
/// unit vectors in R^7 (imaginary octonions).
///
/// For u, v, w  in  Im(O) ~ R^7, the G_2-invariant quantity
///   phi(u,v,w) = <u, v x w>_O
/// where x is the octonion cross product, is the calibration 3-form
/// of G_2.  This is invariant under the G_2 automorphism group of the
/// octonions.
///
/// # Literature
/// - Harvey & Lawson (1982): Calibrated geometries
/// - Bryant (1987): Metrics with holonomy G_2
pub fn g2_calibration_form(u: &[f64; 7], v: &[f64; 7], w: &[f64; 7]) -> f64 {
    // Octonion multiplication table for imaginary units e1..e7:
    // We embed u,v as imaginary octonions (0, u1..u7) and compute
    // the imaginary part of the product, then take the inner product.
    //
    // The calibration form phi(u,v,w) = <u, vxw> where
    //   (vxw)_i = eps_{ijk} v_j w_k
    // with eps_{ijk} the octonion structure constants.
    //
    // Standard octonion Fano-plane structure constants:
    // Positive triples (i,j,k) with e_i*e_j = e_k:
    //   (1,2,3), (1,4,5), (1,7,6), (2,4,6), (2,5,7), (3,4,7), (3,6,5)
    // Using 0-indexed: subtract 1 from each index above.
    let triples: [(usize, usize, usize); 7] = [
        (0, 1, 2), // e1*e2 = e3
        (0, 3, 4), // e1*e4 = e5
        (0, 6, 5), // e1*e7 = e6
        (1, 3, 5), // e2*e4 = e6
        (1, 4, 6), // e2*e5 = e7
        (2, 3, 6), // e3*e4 = e7
        (2, 5, 4), // e3*e6 = e5
    ];

    // Iterate over the 7 Fano-plane triples and for each accumulate
    // the three cyclic permutations (i,j,k), (j,k,i), (k,i,j) of
    // the totally-antisymmetric 3-form:
    // phi(u,v,w) = Sum_{(i,j,k)} [u_i (v_j w_k - v_k w_j)
    //                          + u_j (v_k w_i - v_i w_k)
    //                          + u_k (v_i w_j - v_j w_i)]
    let mut phi = 0.0_f64;
    for &(i, j, k) in &triples {
        phi += u[i] * (v[j] * w[k] - v[k] * w[j]);
        phi += u[j] * (v[k] * w[i] - v[i] * w[k]);
        phi += u[k] * (v[i] * w[j] - v[j] * w[i]);
    }
    phi
}

/// Evaluate the G_2 form on lower imaginary halves of admitted sedenions.
/// Each input requires 16 finite coordinates, zero scalar parts, nonzero
/// imaginary halves, and relative balance/orthogonality below 1e-10. Admission
/// is a numerical constraint check; the returned form is a floating result.
pub fn g2_calibration_from_zds(z1: &[f64], z2: &[f64], z3: &[f64]) -> Option<f64> {
    let extract_im = |coordinates: &[f64]| -> Option<[f64; 7]> {
        let residuals = stiefel_frame_residuals(coordinates)?;
        if residuals.relative_norm_balance >= 1e-10 || residuals.orthogonality >= 1e-10 {
            return None;
        }
        let normalized = normalized_vector(&coordinates[1..8])?;
        normalized.try_into().ok()
    };
    let first = extract_im(z1)?;
    let second = extract_im(z2)?;
    let third = extract_im(z3)?;
    Some(g2_calibration_form(&first, &second, &third))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frame_and_calibration_admission_is_invariant_under_scalar_rescaling() {
        for scale in [-1e300_f64, -1.0, -1e-20, 1e-20, 1.0, 1e300] {
            let mut equal = [0.0; 16];
            equal[1] = scale;
            equal[10] = scale;
            let mut unequal = equal;
            unequal[10] = 2.0 * scale;
            let residuals = stiefel_frame_residuals(&unequal).unwrap();
            assert_eq!(residuals.relative_norm_balance, 1.0 / 3.0);
            let mut second = [0.0; 16];
            second[2] = scale;
            second[11] = scale;
            let mut third = [0.0; 16];
            third[3] = scale;
            third[12] = scale;
            assert!(g2_calibration_from_zds(&unequal, &second, &third).is_none());
            assert!(g2_calibration_from_zds(&equal, &unequal, &third).is_none());
            assert!(g2_calibration_from_zds(&equal, &second, &unequal).is_none());
            assert_eq!(
                g2_calibration_from_zds(&equal, &second, &third),
                Some(scale.signum())
            );
            for tolerance in [0.01, 1e-10] {
                let mut rejected = empty_stiefel_verification();
                record_stiefel_candidate(&mut rejected, &unequal, tolerance);
                assert_eq!(rejected.n_stiefel, 0);
                assert_eq!(rejected.max_norm_violation, scale.abs());
                let mut admitted = empty_stiefel_verification();
                record_stiefel_candidate(&mut admitted, &equal, tolerance);
                assert_eq!(admitted.n_stiefel, 1);
                assert_eq!(admitted.max_norm_violation, 0.0);
            }
        }
    }

    #[test]
    fn imaginary_frame_domain_requires_scalar_purity_and_nonzero_halves() {
        let mut scalar_half = [0.0; 16];
        scalar_half[0] = 1.0;
        scalar_half[9] = 1.0;
        assert!(stiefel_frame_residuals(&scalar_half).is_none());
        let mut valid = [0.0; 16];
        valid[1] = 1.0;
        valid[10] = 1.0;
        let mut parallel = [0.0; 16];
        parallel[1] = 1.0;
        parallel[9] = 1.0;
        assert_eq!(
            stiefel_frame_residuals(&parallel),
            Some(StiefelFrameResiduals {
                absolute_norm_balance: 0.0,
                relative_norm_balance: 0.0,
                orthogonality: 1.0
            })
        );
        for scale in [1e-300, 1.0, 1e300] {
            let scaled = valid.map(|coordinate| coordinate * scale);
            assert_eq!(
                stiefel_frame_residuals(&scaled),
                Some(StiefelFrameResiduals {
                    absolute_norm_balance: 0.0,
                    relative_norm_balance: 0.0,
                    orthogonality: 0.0
                })
            );
        }
        valid[8] = 1.0;
        assert!(stiefel_frame_residuals(&valid).is_none());
        assert!(stiefel_frame_residuals(&[0.0; 16]).is_none());
        let mut empty_half = [0.0; 16];
        empty_half[1] = 1.0;
        assert!(stiefel_frame_residuals(&empty_half).is_none());
        assert!(stiefel_frame_residuals(&parallel[..15]).is_none());
        parallel[1] = f64::INFINITY;
        assert!(stiefel_frame_residuals(&parallel).is_none());
    }

    #[test]
    fn frame_report_uses_normalized_orthogonality_and_rejects_invalid_controls() {
        let mut candidate = [0.0; 16];
        candidate[1] = 2.0;
        candidate[9] = 1.0;
        candidate[10] = 3.0f64.sqrt();
        let mut result = empty_stiefel_verification();
        record_stiefel_candidate(&mut result, &candidate, 1e-10);
        assert_eq!(result.n_samples, 1);
        assert_eq!(result.n_stiefel, 0);
        assert!((result.max_ortho_violation - 0.5).abs() < 1e-14);
        for first_basis in [0, 1] {
            let mut invalid = [0.0; 16];
            invalid[first_basis] = 1.0;
            invalid[9] = 1.0;
            let mut report = empty_stiefel_verification();
            record_stiefel_candidate(&mut report, &invalid, 1e-10);
            assert_eq!(report.n_samples, 1);
            assert_eq!(report.n_stiefel, 0);
        }
        candidate.fill(0.0);
        candidate[1] = 1.0;
        candidate[10] = 1.0;
        let mut report = empty_stiefel_verification();
        record_stiefel_candidate(&mut report, &candidate, 1e-10);
        assert_eq!(report.n_samples, 1);
        assert_eq!(report.n_stiefel, 1);
    }

    #[test]
    fn generic_frame_transport_admits_scalar_components_and_unequal_half_norms() {
        let mut frame = [0.0; 16];
        frame[0] = 2.0;
        frame[9] = 3.0;
        let result = holonomy_between(&frame, &frame).unwrap();
        assert_eq!(result.geodesic_distance, 0.0);
        assert_eq!(result.holonomy_angle, 0.0);
        assert_eq!(result.projected_inner_product, 1.0);
    }

    #[test]
    fn holonomy_rejects_parallel_and_nonfinite_frames() {
        let mut frame = [0.0; 16];
        frame[1] = 1.0;
        frame[10] = 1.0;
        let mut parallel = frame;
        parallel[10] = 0.0;
        parallel[9] = 1.0;
        assert!(holonomy_between(&parallel, &frame).is_none());
        for coordinate in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            let mut invalid = frame;
            invalid[1] = coordinate;
            assert!(holonomy_between(&invalid, &frame).is_none());
            assert!(holonomy_between(&frame, &invalid).is_none());
        }
        assert!(holonomy_between(&frame[..15], &frame).is_none());
        assert!(holonomy_between(&[0.0; 16], &frame).is_none());
    }

    #[test]
    fn calibration_rejects_invalid_sedenion_frames() {
        let mut first = [0.0; 16];
        first[1] = 1.0;
        first[10] = 1.0;
        let mut second = [0.0; 16];
        second[2] = 1.0;
        second[11] = 1.0;
        let mut third = [0.0; 16];
        third[3] = 1.0;
        third[12] = 1.0;
        for first_basis in [0, 1] {
            let mut invalid = [0.0; 16];
            invalid[first_basis] = 1.0;
            invalid[9] = 1.0;
            assert!(g2_calibration_from_zds(&invalid, &second, &third).is_none());
        }
        assert!(g2_calibration_from_zds(&first[..8], &second, &third).is_none());
        assert!(g2_calibration_from_zds(&[0.0; 16], &second, &third).is_none());
        let mut nonfinite = first;
        nonfinite[1] = f64::NAN;
        assert!(g2_calibration_from_zds(&nonfinite, &second, &third).is_none());
    }

    #[test]
    fn test_stiefel_algebraic_cross_assessors() {
        let result = verify_stiefel_algebraic();
        assert!(result.n_samples > 0);
        assert_eq!(result.n_stiefel, result.n_samples);
        assert_eq!(result.stiefel_fraction, 1.0);
        assert_eq!(result.max_norm_violation, 0.0);
        assert_eq!(result.max_ortho_violation, 0.0);
    }

    #[test]
    fn test_stiefel_random_sample() {
        let result = verify_stiefel_condition(20, 42);
        assert_eq!(result.n_samples, 20);
        assert_eq!(result.n_stiefel, 20);
        assert_eq!(result.stiefel_fraction, 1.0);
        assert!(result.max_norm_violation < 1e-12);
        assert!(result.max_ortho_violation < 1e-12);
    }

    #[test]
    fn constrained_random_candidates_are_seeded_unit_imaginary_frames() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;

        let mut first_rng = ChaCha8Rng::seed_from_u64(42);
        let mut replay_rng = ChaCha8Rng::seed_from_u64(42);
        let first = random_stiefel_candidate(&mut first_rng).unwrap();
        let replay = random_stiefel_candidate(&mut replay_rng).unwrap();
        assert_eq!(first, replay);
        let mut other_rng = ChaCha8Rng::seed_from_u64(43);
        assert_ne!(first, random_stiefel_candidate(&mut other_rng).unwrap());

        for seed in [0, 42, u64::MAX] {
            let mut rng = ChaCha8Rng::seed_from_u64(seed);
            for _ in 0..20 {
                let coordinates = random_stiefel_candidate(&mut rng).unwrap();
                assert_eq!(coordinates[0], 0.0);
                assert_eq!(coordinates[8], 0.0);
                assert!((vec_norm(&coordinates) - 1.0).abs() < 1e-12);
                let first_norm = vec_norm(&coordinates[1..8]);
                let second_norm = vec_norm(&coordinates[9..16]);
                assert!((first_norm - std::f64::consts::FRAC_1_SQRT_2).abs() < 1e-12);
                assert!((second_norm - std::f64::consts::FRAC_1_SQRT_2).abs() < 1e-12);
                let residuals = stiefel_frame_residuals(&coordinates).unwrap();
                assert!(residuals.relative_norm_balance < 1e-12);
                assert!(residuals.orthogonality < 1e-12);
                let matrix = crate::annihilator::left_multiplication_matrix(&coordinates, 16);
                let singular_values = matrix.svd(false, false).singular_values;
                assert!(singular_values.min() < 1e-8);
            }
            let result = verify_stiefel_condition(20, seed);
            assert_eq!(result.n_samples, 20);
            assert_eq!(result.n_stiefel, 20);
            assert_eq!(result.stiefel_fraction, 1.0);
            assert!(result.max_norm_violation < 1e-12);
            assert!(result.max_ortho_violation < 1e-12);
            let replay = verify_stiefel_condition(20, seed);
            assert_eq!(result.max_norm_violation, replay.max_norm_violation);
            assert_eq!(result.max_ortho_violation, replay.max_ortho_violation);
        }
    }

    #[test]
    fn zero_stiefel_sample_request_returns_empty_report() {
        let result = verify_stiefel_condition(0, 42);
        assert_eq!(result.dim, 16);
        assert_eq!(result.n_samples, 0);
        assert_eq!(result.n_stiefel, 0);
        assert_eq!(result.stiefel_fraction, 0.0);
        assert_eq!(result.max_norm_violation, 0.0);
        assert_eq!(result.max_ortho_violation, 0.0);
    }

    #[test]
    #[should_panic(expected = "requested Stiefel sample count exceeds finite attempt budget")]
    fn oversized_stiefel_sample_request_fails_explicitly() {
        verify_stiefel_condition(usize::MAX, 42);
    }

    #[test]
    fn test_basis_zd_stiefel() {
        // Find a confirmed zero-divisor from the box-kite zero-product structure.
        // Not every e_lo + e_hi is a ZD; only those pairs (a, b) where
        // diagonal_zero_products_exact returns non-empty solutions.
        use crate::boxkites::{cross_assessors, diagonal_zero_products_exact};

        let pairs = cross_assessors(16);
        let mut found_zd = false;

        for (i, &a_pair) in pairs.iter().enumerate() {
            for &b_pair in &pairs[(i + 1)..] {
                let solutions = diagonal_zero_products_exact(16, a_pair, b_pair);
                if solutions.is_empty() {
                    continue;
                }

                // We have a confirmed ZD: z = e_{a.0} + s*e_{a.1}
                let (s, _t) = solutions[0];
                let mut z = [0.0f64; 16];
                z[a_pair.0] = 1.0;
                z[a_pair.1] = s as f64;

                // Verify it's actually a ZD via SVD
                assert!(is_zero_divisor(&z), "confirmed ZD should pass SVD check");

                assert_eq!(
                    stiefel_frame_residuals(&z),
                    Some(StiefelFrameResiduals {
                        absolute_norm_balance: 0.0,
                        relative_norm_balance: 0.0,
                        orthogonality: 0.0
                    })
                );

                // Verify the imaginary-frame condition.
                let (a, b) = decompose_halves(&z);
                let norm_a = vec_norm(a);
                let norm_b = vec_norm(b);
                let dot = inner_product(a, b);

                // Cross-assessor pair has lo < 8 and hi >= 8,
                // so a and b occupy different R^8 components.
                // Norm balance: |a| = |b| = 1 (single basis element each)
                assert!(
                    (norm_a - norm_b).abs() < 1e-12,
                    "norm balance for ({}, {})",
                    a_pair.0,
                    a_pair.1
                );

                // Orthogonality: <a, b> = 0 when lo != hi - 8
                if a_pair.0 != a_pair.1 - 8 {
                    assert!(
                        dot.abs() < 1e-12,
                        "<a,b> should be 0 for ({}, {})",
                        a_pair.0,
                        a_pair.1
                    );
                }

                eprintln!(
                    "Confirmed ZD e_{} + {}*e_{}: |a|={:.6}, |b|={:.6}, <a,b>={:.2e}",
                    a_pair.0, s, a_pair.1, norm_a, norm_b, dot
                );
                found_zd = true;
                break;
            }
            if found_zd {
                break;
            }
        }
        assert!(found_zd, "should find at least one confirmed ZD pair");
    }

    #[test]
    fn test_verified_zd_count() {
        // Check the imaginary-frame constraints on exact diagonal witnesses.
        // The census counts factor occurrences, including repeated factors.
        use crate::boxkites::{cross_assessors, diagonal_zero_products_exact};

        let pairs = cross_assessors(16);
        let mut n_zd = 0;
        let mut n_stiefel = 0;
        let mut n_ortho_fail = 0;

        for (i, &a_pair) in pairs.iter().enumerate() {
            for &b_pair in &pairs[(i + 1)..] {
                let solutions = diagonal_zero_products_exact(16, a_pair, b_pair);
                for &(s, _t) in &solutions {
                    let mut z = [0.0f64; 16];
                    z[a_pair.0] = 1.0;
                    z[a_pair.1] = s as f64;

                    n_zd += 1;
                    let residuals =
                        stiefel_frame_residuals(&z).expect("exact witness has pure nonzero halves");
                    let norm_ok = residuals.relative_norm_balance < 1e-10;
                    let ortho_ok = residuals.orthogonality < 1e-10;
                    if norm_ok && ortho_ok {
                        n_stiefel += 1;
                    }
                    if !ortho_ok {
                        n_ortho_fail += 1;
                    }
                }
            }
        }

        eprintln!("Verified ZD Stiefel census:");
        eprintln!("  total confirmed ZDs: {}", n_zd);
        eprintln!("  V_2(R^7) satisfied: {}", n_stiefel);
        eprintln!("  orthogonality failures: {}", n_ortho_fail);
        if n_zd > 0 {
            eprintln!("  fraction: {:.4}", n_stiefel as f64 / n_zd as f64);
        }

        assert!(
            n_zd > 0,
            "must find at least one exact zero-product witness"
        );
        assert_eq!(n_stiefel, n_zd);
        assert_eq!(n_ortho_fail, 0);
    }

    #[test]
    fn test_holonomy_self_is_zero() {
        // Identical orthonormal frames have zero distance and endpoint angle.
        let mut z = [0.0f64; 16];
        z[1] = 1.0; // e_1 in lower half
        z[10] = 1.0; // e_2 in upper half (different R^8 component)
        let result = holonomy_between(&z, &z).expect("should compute holonomy");
        assert!(
            result.geodesic_distance.abs() < 1e-10,
            "self-distance should be 0, got {}",
            result.geodesic_distance
        );
        assert!(
            result.holonomy_angle.abs() < 1e-10,
            "self-holonomy should be 0, got {}",
            result.holonomy_angle
        );
    }

    #[test]
    fn test_holonomy_between_distinct_zds() {
        // Two generic R^8 frames with orthogonal u,v components:
        // z1: a=(e_1), b=(e_2) => u1=e_1, v1=e_2 (orthogonal ok)
        // z2: a=(e_3), b=(e_4) => u2=e_3, v2=e_4 (orthogonal ok)
        let mut z1 = [0.0f64; 16];
        z1[1] = 1.0; // a = e_1
        z1[10] = 1.0; // b = e_2 (in upper half)
        let mut z2 = [0.0f64; 16];
        z2[3] = 1.0; // a = e_3
        z2[12] = 1.0; // b = e_4 (in upper half)
        let result = holonomy_between(&z1, &z2).expect("should compute holonomy");
        // u1 = e_1, u2 = e_3 in R^8 => <u1,u2> = 0 => geodesic distance = pi/2
        assert!(
            (result.geodesic_distance - std::f64::consts::FRAC_PI_2).abs() < 1e-10,
            "expected pi/2 geodesic distance, got {}",
            result.geodesic_distance
        );
        // The holonomy angle should be well-defined and finite
        assert!(result.holonomy_angle.is_finite());
    }

    #[test]
    fn test_holonomy_antipodal_returns_none() {
        // u1 ~ -u2 (antipodal on S^7): geodesic is non-unique,
        // parallel transport is path-dependent => returns None.
        let mut z1 = [0.0f64; 16];
        z1[1] = 1.0; // a = +e_1
        z1[10] = 1.0; // b = e_2 (in upper half)
        let mut z2 = [0.0f64; 16];
        z2[1] = -1.0; // a = -e_1  (antipodal to z1's a-half)
        z2[10] = 1.0; // b = e_2
        let result = holonomy_between(&z1, &z2);
        assert!(
            result.is_none(),
            "antipodal u-vectors should return None, got {:?}",
            result
        );
    }

    #[test]
    fn test_g2_calibration_antisymmetric() {
        // The G_2 3-form is totally antisymmetric
        let u = [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        let v = [0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0];
        let w = [0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0];

        let phi_uvw = g2_calibration_form(&u, &v, &w);
        let phi_vuw = g2_calibration_form(&v, &u, &w);
        let phi_uwv = g2_calibration_form(&u, &w, &v);

        assert!(
            (phi_uvw + phi_vuw).abs() < 1e-12,
            "phi(u,v,w) should be -phi(v,u,w)"
        );
        assert!(
            (phi_uvw + phi_uwv).abs() < 1e-12,
            "phi(u,v,w) should be -phi(u,w,v)"
        );
    }

    #[test]
    fn test_g2_calibration_nonzero_for_fano_triple() {
        // (e1, e2, e3) is a Fano-plane triple => phi should be +/-1
        let u = [1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]; // e1
        let v = [0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0]; // e2
        let w = [0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0]; // e3

        let phi = g2_calibration_form(&u, &v, &w);
        // For (0,1,2) triple: contribution is u[0]*(v[1]*w[2] - v[2]*w[1])
        // = 1*(1*1 - 0*0) = 1
        assert!(
            (phi.abs() - 1.0).abs() < 1e-12,
            "phi(e1,e2,e3) should be +/-1 for Fano triple, got {}",
            phi
        );
    }

    #[test]
    fn test_g2_calibration_from_zds_works() {
        // Use three distinct standard ZDs
        let mut z1 = vec![0.0; 16];
        z1[1] = 1.0;
        z1[10] = 1.0;
        let mut z2 = vec![0.0; 16];
        z2[2] = 1.0;
        z2[11] = 1.0;
        let mut z3 = vec![0.0; 16];
        z3[3] = 1.0;
        z3[12] = 1.0;

        let result = g2_calibration_from_zds(&z1, &z2, &z3);
        assert_eq!(result, Some(1.0));
    }
}
