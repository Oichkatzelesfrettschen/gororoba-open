// SPDX-License-Identifier: MIT

//! Terminal Pauli readout of a teleportation byproduct, modulo global phase.
//!
//! Bennett et al. (1993), teleportation protocol: the Bell record `(a, b)`
//! leaves the receiver in the frame `X^b Z^a`. A terminal measurement in X,
//! Y or Z can absorb that frame by relabelling its classical outcome. This
//! does not apply a physical gate and does not assert a surviving output.
//!
//! These types discard global phase. They must not represent a coherently
//! controlled Pauli operator, where a branch-relative phase is observable.

/// Pauli observable measured at the receiver; bit zero is eigenvalue +1.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MeasurementBasis {
    X,
    Y,
    Z,
}

/// Pauli byproduct `X^x Z^z`, with only physically irrelevant global phase omitted.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PauliFrame {
    pub x: bool,
    pub z: bool,
}

impl PauliFrame {
    /// Construct the byproduct from the input Bell bit `a` and partner bit `b`.
    pub const fn from_bell_record(a: bool, b: bool) -> Self {
        Self { x: b, z: a }
    }

    /// True exactly when this frame anticommutes with the measured observable.
    pub const fn flips(self, basis: MeasurementBasis) -> bool {
        match basis {
            MeasurementBasis::X => self.z,
            MeasurementBasis::Y => self.x ^ self.z,
            MeasurementBasis::Z => self.x,
        }
    }

    /// Decode a terminal bit. There is no constant inversion in the Y basis.
    pub const fn decode(self, basis: MeasurementBasis, raw: bool) -> bool {
        raw ^ self.flips(basis)
    }

    /// Compose two Pauli frames, modulo global phase.
    pub const fn then(self, next: Self) -> Self {
        Self {
            x: self.x ^ next.x,
            z: self.z ^ next.z,
        }
    }

    /// Conjugate the frame through H: X and Z exchange roles.
    pub const fn through_h(self) -> Self {
        Self {
            x: self.z,
            z: self.x,
        }
    }

    /// Conjugate through S, modulo global phase. S-dagger has the same frame map.
    pub const fn through_s(self) -> Self {
        Self {
            x: self.x,
            z: self.z ^ self.x,
        }
    }

    /// Conjugate through S-dagger; the discarded sign never flips a terminal bit.
    pub const fn through_s_dagger(self) -> Self {
        self.through_s()
    }

    /// Conjugate through the readout alignment (I, H, or S-dagger then H).
    pub const fn aligned(self, basis: MeasurementBasis) -> Self {
        match basis {
            MeasurementBasis::Z => self,
            MeasurementBasis::X => self.through_h(),
            MeasurementBasis::Y => self.through_s_dagger().through_h(),
        }
    }
}

/// Propagate independent frames through a CNOT, returning (control, target).
pub const fn through_cnot(control: PauliFrame, target: PauliFrame) -> (PauliFrame, PauliFrame) {
    (
        PauliFrame {
            x: control.x,
            z: control.z ^ target.z,
        },
        PauliFrame {
            x: target.x ^ control.x,
            z: target.z,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::{MeasurementBasis, PauliFrame, through_cnot};

    // Exact Gaussian-integer matrix arithmetic supplies an independent oracle.
    // Unnormalized H introduces an explicit factor of two, not a float tolerance.
    type Complex = (i32, i32);
    type Matrix = [[Complex; 2]; 2];
    const ZERO: Complex = (0, 0);
    const ONE: Complex = (1, 0);
    const I: Matrix = [[ONE, ZERO], [ZERO, ONE]];
    const X: Matrix = [[ZERO, ONE], [ONE, ZERO]];
    const Y: Matrix = [[ZERO, (0, -1)], [(0, 1), ZERO]];
    const Z: Matrix = [[ONE, ZERO], [ZERO, (-1, 0)]];
    const H: Matrix = [[ONE, ONE], [ONE, (-1, 0)]];
    const S: Matrix = [[ONE, ZERO], [ZERO, (0, 1)]];
    const SD: Matrix = [[ONE, ZERO], [ZERO, (0, -1)]];
    const FRAMES: [PauliFrame; 4] = [
        PauliFrame { x: false, z: false },
        PauliFrame { x: true, z: false },
        PauliFrame { x: false, z: true },
        PauliFrame { x: true, z: true },
    ];

    fn add(a: Complex, b: Complex) -> Complex {
        (a.0 + b.0, a.1 + b.1)
    }

    fn mul(a: Complex, b: Complex) -> Complex {
        (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0)
    }

    fn product(a: Matrix, b: Matrix) -> Matrix {
        let mut out = [[ZERO; 2]; 2];
        for (r, row) in out.iter_mut().enumerate() {
            for (c, value) in row.iter_mut().enumerate() {
                *value = add(mul(a[r][0], b[0][c]), mul(a[r][1], b[1][c]));
            }
        }
        out
    }

    fn scaled(a: Matrix, scale: Complex) -> Matrix {
        a.map(|row| row.map(|value| mul(scale, value)))
    }

    fn matrix(frame: PauliFrame) -> Matrix {
        product(if frame.x { X } else { I }, if frame.z { Z } else { I })
    }

    fn equal_mod_phase(a: Matrix, b: Matrix, scale: i32) -> bool {
        [(scale, 0), (-scale, 0), (0, scale), (0, -scale)]
            .into_iter()
            .any(|phase| a == scaled(b, phase))
    }

    #[test]
    fn decode_agrees_with_exact_anticommutation() {
        for frame in FRAMES {
            for (basis, observable) in [
                (MeasurementBasis::X, X),
                (MeasurementBasis::Y, Y),
                (MeasurementBasis::Z, Z),
            ] {
                let left = product(observable, matrix(frame));
                let right = product(matrix(frame), observable);
                let flip = left == scaled(right, (-1, 0));
                assert!(left == right || flip);
                assert_eq!(frame.flips(basis), flip);
                for raw in [false, true] {
                    assert_eq!(frame.decode(basis, raw), raw ^ flip);
                }
                assert_eq!(frame.aligned(basis).x, flip);
            }
        }
    }

    #[test]
    fn conjugation_matches_exact_matrices_modulo_phase() {
        for frame in FRAMES {
            assert!(equal_mod_phase(product(product(H, matrix(frame)), H), matrix(frame.through_h()), 2));
            assert!(equal_mod_phase(product(product(S, matrix(frame)), SD), matrix(frame.through_s()), 1));
            assert!(equal_mod_phase(product(product(SD, matrix(frame)), S), matrix(frame.through_s_dagger()), 1));
        }
    }

    #[test]
    fn composition_matches_matrix_product_modulo_phase() {
        for before in FRAMES {
            for after in FRAMES {
                assert!(equal_mod_phase(product(matrix(after), matrix(before)), matrix(before.then(after)), 1));
            }
            assert_eq!(before.then(before), PauliFrame::default());
        }
    }

    #[test]
    fn bell_record_roles_and_y_parity_are_unambiguous() {
        for a in [false, true] {
            for b in [false, true] {
                let frame = PauliFrame::from_bell_record(a, b);
                assert!(!frame.decode(MeasurementBasis::Z, b));
                assert!(frame.decode(MeasurementBasis::Z, !b));
                assert!(!frame.decode(MeasurementBasis::X, a));
                assert!(!frame.decode(MeasurementBasis::Y, a ^ b));
                assert!(frame.decode(MeasurementBasis::Y, !(a ^ b)));
            }
        }
    }

    #[test]
    fn cnot_propagation_matches_exact_tensor_conjugation() {
        // Computational order |control,target>; CNOT swaps basis indices 2,3.
        let permutation = [0, 1, 3, 2];
        for control in FRAMES {
            for target in FRAMES {
                let (next_c, next_t) = through_cnot(control, target);
                let (c, t) = (matrix(control), matrix(target));
                let (nc, nt) = (matrix(next_c), matrix(next_t));
                let mut matches = false;
                for phase in [ONE, (-1, 0), (0, 1), (0, -1)] {
                    let mut equal = true;
                    for (r, &pr) in permutation.iter().enumerate() {
                        for (col, &pc) in permutation.iter().enumerate() {
                            let left = mul(c[pr / 2][pc / 2], t[pr % 2][pc % 2]);
                            let right = mul(phase, mul(nc[r / 2][col / 2], nt[r % 2][col % 2]));
                            equal &= left == right;
                        }
                    }
                    matches |= equal;
                }
                assert!(matches);
                assert_eq!(through_cnot(next_c, next_t), (control, target));
            }
        }
    }
}
