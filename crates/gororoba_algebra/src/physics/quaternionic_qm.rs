//! Quaternionic interference and its faithful two-channel complex encoding.
//!
//! Matched encodings preserve probabilities. Projecting away quaternion
//! components changes the inputs and supplies a separate diagnostic.
//!
//! # References
//! - Adler, S. L. (1995). Quaternionic Quantum Mechanics and Quantum Fields.

use cd_kernel::cayley_dickson::{cd_multiply, cd_norm_sq};

/// Return unnormalized intensities after component projection and full multiplication.
///
/// Projection discards the j and k coefficients and can turn a unit phase
/// into zero. The resulting difference tests projection, not scalar-field physics.
pub fn projected_interference_intensities(
    psi1: &[f64],
    psi2: &[f64],
    phase1: &[f64],
    phase2: &[f64],
) -> (f64, f64) {
    // Standard Complex QM (using the first 2 components: real + i)
    let c_psi1 = vec![psi1[0], psi1[1]];
    let c_psi2 = vec![psi2[0], psi2[1]];
    let c_phase1 = vec![phase1[0], phase1[1]];
    let c_phase2 = vec![phase2[0], phase2[1]];

    // state = phase1 * psi1 + phase2 * psi2
    let c_term1 = cd_multiply(&c_phase1, &c_psi1);
    let c_term2 = cd_multiply(&c_phase2, &c_psi2);
    let c_state = vec![c_term1[0] + c_term2[0], c_term1[1] + c_term2[1]];
    let complex_probability = cd_norm_sq(&c_state);

    // Quaternionic QM (using 4 components: real + i + j + k)
    let h_psi1 = vec![psi1[0], psi1[1], psi1[2], psi1[3]];
    let h_psi2 = vec![psi2[0], psi2[1], psi2[2], psi2[3]];
    let h_phase1 = vec![phase1[0], phase1[1], phase1[2], phase1[3]];
    let h_phase2 = vec![phase2[0], phase2[1], phase2[2], phase2[3]];

    // state = phase1 * psi1 + phase2 * psi2
    let h_term1 = cd_multiply(&h_phase1, &h_psi1);
    let h_term2 = cd_multiply(&h_phase2, &h_psi2);
    let h_state = vec![
        h_term1[0] + h_term2[0],
        h_term1[1] + h_term2[1],
        h_term1[2] + h_term2[2],
        h_term1[3] + h_term2[3],
    ];
    let quaternionic_probability = cd_norm_sq(&h_state);

    (complex_probability, quaternionic_probability)
}

/// Return the same balanced-port probability in complex and quaternion coordinates.
///
/// Each arm has a unit quaternion state and unit left phase. Splitting and
/// recombination give amplitude `(phase1*psi1 + phase2*psi2)/2`. The complex
/// encoding uses both channels of `chi(z+w*j)=[[z,w],[-conj(w),conj(z)]]`.
///
/// # Panics
///
/// Panics when an input has a length other than four, nonfinite coefficients,
/// or squared norm differing from one by more than 1e-12.
pub fn evaluate_interference(
    psi1: &[f64],
    psi2: &[f64],
    phase1: &[f64],
    phase2: &[f64],
) -> (f64, f64) {
    for input in [psi1, psi2, phase1, phase2] {
        assert_eq!(input.len(), 4, "a quaternion has four real coefficients");
        assert!(input.iter().all(|value| value.is_finite()));
        assert!((cd_norm_sq(input) - 1.0).abs() <= 1e-12);
    }
    let encode_product = |phase: &[f64], state: &[f64]| {
        use num_complex::Complex64;
        let diagonal = Complex64::new(phase[0], phase[1]);
        let off_diagonal = Complex64::new(phase[2], phase[3]);
        let first = Complex64::new(state[0], state[1]);
        let second = Complex64::new(-state[2], state[3]);
        [
            diagonal * first + off_diagonal * second,
            -off_diagonal.conj() * first + diagonal.conj() * second,
        ]
    };
    let first_encoded = encode_product(phase1, psi1);
    let second_encoded = encode_product(phase2, psi2);
    let complex_probability = first_encoded
        .iter()
        .zip(second_encoded)
        .map(|(first, second)| (*first + second).norm_sqr())
        .sum::<f64>()
        / 4.0;
    let first_product = cd_multiply(phase1, psi1);
    let second_product = cd_multiply(phase2, psi2);
    let sum: Vec<f64> = first_product
        .iter()
        .zip(second_product)
        .map(|(first, second)| first + second)
        .collect();
    (complex_probability, cd_norm_sq(&sum) / 4.0)
}

/// Computes the commutator `[A, B]` = A*B - B*A.
/// In standard QM (complex numbers), scalar phases commute: `[A, B]` = 0.
/// In Quaternionic QM, scalar phases (if they involve j, k) do not commute.
pub fn phase_commutator(a: &[f64], b: &[f64]) -> Vec<f64> {
    let dim = a.len();
    let ab = cd_multiply(a, b);
    let ba = cd_multiply(b, a);

    let mut commutator = vec![0.0; dim];
    for i in 0..dim {
        commutator[i] = ab[i] - ba[i];
    }
    commutator
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn faithful_complex_encoding_preserves_balanced_probability() {
        let state = [1.0, 0.0, 0.0, 0.0];
        let phase_i = [0.0, 1.0, 0.0, 0.0];
        let phase_j = [0.0, 0.0, 1.0, 0.0];
        let (encoded, quaternionic) = evaluate_interference(&state, &state, &phase_i, &phase_j);
        assert!((encoded - 0.5).abs() < 1e-12);
        assert!((quaternionic - 0.5).abs() < 1e-12);
    }

    #[test]
    fn component_projection_changes_the_interference_inputs() {
        let psi1 = vec![1.0, 0.0, 0.0, 0.0]; // Real state 1
        let psi2 = vec![0.0, 1.0, 0.0, 0.0]; // "i" state 1

        // Complex phase (real + i)
        let phase1 = vec![0.0, 1.0, 0.0, 0.0];
        // Quaternionic phase (real + j)
        let phase2 = vec![0.0, 0.0, 1.0, 0.0];

        let (c_prob, h_prob) = projected_interference_intensities(&psi1, &psi2, &phase1, &phase2);

        // Since phase2 is purely 'j', in the complex projection it appears as 0,
        // altering the interference sum and its normalization.
        assert!((c_prob - h_prob).abs() > 1e-10);
    }

    #[test]
    fn quaternion_ray_representatives_preserve_probability() {
        let real = [1.0, 0.0, 0.0, 0.0];
        let phase_i = [0.0, 1.0, 0.0, 0.0];
        let phase_j = [0.0, 0.0, 1.0, 0.0];
        assert_eq!(
            evaluate_interference(&real, &real, &phase_i, &phase_j),
            evaluate_interference(&phase_j, &phase_j, &phase_i, &phase_j),
        );
    }

    #[test]
    #[should_panic(expected = "four real coefficients")]
    fn invalid_quaternion_width_is_rejected() {
        let unit = [1.0, 0.0, 0.0, 0.0];
        evaluate_interference(&unit[..2], &unit, &unit, &unit);
    }

    #[test]
    fn test_phase_commutativity() {
        // Complex phases commute
        let c1 = vec![0.0, 1.0];
        let c2 = vec![0.5, 0.5];
        let c_comm = phase_commutator(&c1, &c2);
        assert!(cd_norm_sq(&c_comm) < 1e-10);

        // Quaternionic phases do not commute
        let h1 = vec![0.0, 1.0, 0.0, 0.0]; // i
        let h2 = vec![0.0, 0.0, 1.0, 0.0]; // j
        let h_comm = phase_commutator(&h1, &h2);

        // [i, j] = ij - ji = k - (-k) = 2k
        assert!(cd_norm_sq(&h_comm) > 1e-10);
    }
}
