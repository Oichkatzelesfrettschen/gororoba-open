//! Fixed-norm Cayley-Dickson commutator perturbation of a relaxed vector.
//!
//! The 16 components are algebraic coordinates. Interpreting the coordinates
//! as populations changes their sum and permits negative entries, as the
//! basis-vector counterexamples demonstrate. A D3Q19 velocity map, conservative
//! collision construction, and quantum fluctuation model remain required for
//! a physical fluid interpretation. The ZPE API name supplies compatibility,
//! rather than evidence for quantum vacuum dynamics.

use cd_kernel::cayley_dickson::cd_multiply;
#[cfg(test)]
use cd_kernel::cayley_dickson::cd_norm_sq;

/// A 16-component algebraic vector, with an unconstrained population sum.
pub type LbmNode = [f64; 16];

/// Relax toward `equilibrium`, then normalize a nonzero commutator to norm 1e-4.
///
/// `omega` is dimensionless. `vacuum_field` supplies an algebraic operand;
/// normalization removes its positive magnitude when the squared norm and
/// normalization arithmetic remain representable and nonzero.
/// The function defines neither SI energy nor a
/// stochastic bath. Population conservation and positivity fail on basis inputs.
pub fn zpe_bgk_collision(
    node: &mut LbmNode,
    equilibrium: &LbmNode,
    omega: f64,
    vacuum_field: &LbmNode,
) {
    let mut relaxation = [0.0; 16];
    for i in 0..16 {
        relaxation[i] = node[i] - omega * (node[i] - equilibrium[i]);
    }

    let nv: [f64; 16] = cd_multiply(&relaxation, vacuum_field).try_into().unwrap();
    let vn: [f64; 16] = cd_multiply(vacuum_field, &relaxation).try_into().unwrap();

    let mut commutator = [0.0; 16];
    let mut zpe_energy: f64 = 0.0;
    for i in 0..16 {
        commutator[i] = nv[i] - vn[i];
        zpe_energy += commutator[i].powi(2);
    }

    // Fixed normalization controls vector distance, rather than physical energy.
    let scale = if zpe_energy > 0.0 {
        1e-4 / zpe_energy.sqrt()
    } else {
        0.0
    };

    for i in 0..16 {
        node[i] = relaxation[i] + commutator[i] * scale;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basis_commutator_changes_population_sum() {
        let mut node = [0.0; 16];
        node[1] = 1.0;
        let equilibrium = node;
        let mut field = [0.0; 16];
        field[2] = 1.0;
        zpe_bgk_collision(&mut node, &equilibrium, 1.0, &field);
        assert!((node[3] - 1e-4).abs() < 1e-15);
        assert!((node.iter().sum::<f64>() - 1.0001).abs() < 1e-12);
    }

    #[test]
    fn reversed_operand_creates_negative_population() {
        let mut node = [0.0; 16];
        node[1] = 1.0;
        let equilibrium = node;
        let mut field = [0.0; 16];
        field[2] = -1.0;
        zpe_bgk_collision(&mut node, &equilibrium, 1.0, &field);
        assert!((node[3] + 1e-4).abs() < 1e-15);
        assert!(node[3] < 0.0);
    }

    #[test]
    fn normalization_removes_operand_magnitude() {
        let mut unit_field_node = [0.0; 16];
        unit_field_node[1] = 1.0;
        let equilibrium = unit_field_node;
        let mut tiny_field_node = unit_field_node;
        let mut field = [0.0; 16];
        field[2] = 1.0;
        zpe_bgk_collision(&mut unit_field_node, &equilibrium, 1.0, &field);
        field[2] = 1e-12;
        zpe_bgk_collision(&mut tiny_field_node, &equilibrium, 1.0, &field);
        for (unit_value, tiny_value) in unit_field_node.iter().zip(tiny_field_node) {
            assert!((unit_value - tiny_value).abs() < 1e-15);
        }
    }

    #[test]
    fn test_zpe_injection() {
        let mut node = [0.0; 16];
        node[3] = 1.0; // Specific directional momentum

        let mut eq = [0.0; 16];
        eq[3] = 0.5; // Relaxing towards smaller momentum

        let mut vacuum = [0.0; 16];
        vacuum[1] = 1.0;
        vacuum[2] = 1.0; // e1 and e2 do not commute with e3

        zpe_bgk_collision(&mut node, &eq, 1.0, &vacuum);

        let final_dist = cd_norm_sq(&node).sqrt();

        assert!(
            (final_dist - 0.5).abs() > 1e-9,
            "the normalized commutator should perturb the vector norm"
        );
    }
}
