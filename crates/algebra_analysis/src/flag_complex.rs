//! Finite graph flag complexes with exact rational homology.
//!
//! An edge states the supplied graph relation. The resulting homology belongs
//! to its clique complex. A continuous zero-divisor space requires a proved
//! bridge before these graph invariants can describe that space.

use crate::{
    boxkites::Assessor,
    exact_annihilator::{ExactMatrix, exact_rank, valid_rational_matrix},
};
use cd_kernel::cayley_dickson::cd_basis_mul_sign;
use num_rational::BigRational;
use num_traits::Zero;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FlagComplexError {
    InvalidEdge(usize, usize),
    DuplicateEdge(usize, usize),
    SimplexBudgetExceeded(usize),
    InvalidAssessorXorKey(usize),
}

impl std::fmt::Display for FlagComplexError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for FlagComplexError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlagComplex {
    /// Increasing vertex lists, grouped by dimension and ordered lexically.
    simplices: Vec<Vec<Vec<usize>>>,
}

impl FlagComplex {
    /// Enumerate every clique, returning an error if the declared finite
    /// budget is insufficient. A budget error never returns a truncated complex.
    pub fn from_edges(
        vertex_count: usize,
        edges: &[(usize, usize)],
        simplex_budget: usize,
    ) -> Result<Self, FlagComplexError> {
        if vertex_count > simplex_budget {
            return Err(FlagComplexError::SimplexBudgetExceeded(simplex_budget));
        }
        let mut adjacency = vec![BTreeSet::new(); vertex_count];
        for &(left, right) in edges {
            if left >= vertex_count || right >= vertex_count || left == right {
                return Err(FlagComplexError::InvalidEdge(left, right));
            }
            if !adjacency[left].insert(right) {
                return Err(FlagComplexError::DuplicateEdge(left, right));
            }
            adjacency[right].insert(left);
        }
        let mut simplices = Vec::<Vec<Vec<usize>>>::new();
        let mut frontier: Vec<Vec<usize>> = (0..vertex_count).map(|vertex| vec![vertex]).collect();
        let mut count = vertex_count;
        while !frontier.is_empty() {
            let mut next = Vec::new();
            for simplex in &frontier {
                for &candidate in adjacency[*simplex.last().expect("nonempty simplex")]
                    .range(simplex.last().expect("nonempty simplex") + 1..)
                {
                    if simplex
                        .iter()
                        .all(|&vertex| adjacency[vertex].contains(&candidate))
                    {
                        if count == simplex_budget {
                            return Err(FlagComplexError::SimplexBudgetExceeded(simplex_budget));
                        }
                        let mut extension = simplex.clone();
                        extension.push(candidate);
                        next.push(extension);
                        count += 1;
                    }
                }
            }
            simplices.push(frontier);
            frontier = next;
        }
        Ok(Self { simplices })
    }

    pub fn simplices(&self) -> &[Vec<Vec<usize>>] {
        &self.simplices
    }

    /// The unaugmented boundary has oriented coefficients `(-1)^face_index`.
    pub fn boundary_maps(&self) -> Vec<ExactMatrix> {
        self.simplices
            .iter()
            .enumerate()
            .map(|(dimension, simplices)| {
                if dimension == 0 {
                    return ExactMatrix::zeros(0, simplices.len());
                }
                let faces = &self.simplices[dimension - 1];
                let face_indices: BTreeMap<_, _> = faces
                    .iter()
                    .enumerate()
                    .map(|(index, face)| (face.clone(), index))
                    .collect();
                let mut boundary = ExactMatrix::zeros(faces.len(), simplices.len());
                for (column, simplex) in simplices.iter().enumerate() {
                    for omitted in 0..simplex.len() {
                        let mut face = simplex.clone();
                        face.remove(omitted);
                        let coefficient = if omitted % 2 == 0 { 1 } else { -1 };
                        boundary[(face_indices[&face], column)] =
                            BigRational::from_integer(coefficient.into());
                    }
                }
                boundary
            })
            .collect()
    }

    /// Compute ordinary Betti numbers over Q. Rational homology records free
    /// ranks and leaves integral torsion outside the certificate's domain.
    pub fn rational_homology(&self) -> RationalHomologyCertificate {
        let boundaries = self.boundary_maps();
        let boundary_ranks: Vec<_> = boundaries.iter().map(exact_rank).collect();
        let betti_numbers = self
            .simplices
            .iter()
            .enumerate()
            .map(|(dimension, cells)| {
                cells.len()
                    - boundary_ranks[dimension]
                    - boundary_ranks.get(dimension + 1).copied().unwrap_or(0)
            })
            .collect();
        RationalHomologyCertificate {
            boundaries,
            boundary_ranks,
            betti_numbers,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RationalHomologyCertificate {
    pub boundaries: Vec<ExactMatrix>,
    pub boundary_ranks: Vec<usize>,
    pub betti_numbers: Vec<usize>,
}

impl RationalHomologyCertificate {
    /// Reconstruct signed boundaries, check `d d = 0`, and recompute ranks.
    pub fn verify(&self, complex: &FlagComplex) -> bool {
        if self
            .boundaries
            .iter()
            .any(|matrix| !valid_rational_matrix(matrix))
            || self.boundaries != complex.boundary_maps()
        {
            return false;
        }
        if self
            .boundaries
            .windows(2)
            .any(|pair| (&pair[0] * &pair[1]).iter().any(|entry| !entry.is_zero()))
        {
            return false;
        }
        *self == complex.rational_homology()
    }
}

#[derive(Debug, Clone)]
pub struct AssessorFlagComplex {
    pub assessors: Vec<Assessor>,
    /// `(left_vertex, right_vertex, left_sign, right_sign)` certifies the
    /// zero product of the two signed assessor diagonals.
    pub edge_witnesses: Vec<(usize, usize, i32, i32)>,
    pub complex: FlagComplex,
}

fn exact_diagonal_zero_product(left: Assessor, right: Assessor) -> Option<(i32, i32)> {
    for left_sign in [-1, 1] {
        for right_sign in [-1, 1] {
            let mut product = [0; 16];
            for (left_basis, left_coefficient) in [(left.low, 1), (left.high, left_sign)] {
                for (right_basis, right_coefficient) in [(right.low, 1), (right.high, right_sign)] {
                    product[left_basis ^ right_basis] += left_coefficient
                        * right_coefficient
                        * cd_basis_mul_sign(16, left_basis, right_basis);
                }
            }
            if product.iter().all(|&coefficient| coefficient == 0) {
                return Some((left_sign, right_sign));
            }
        }
    }
    None
}

/// Build the six-vertex assessor graph with `low XOR high = xor_key`.
/// Every edge carries an exact zero-product witness. All four sign choices
/// are exhausted before a pair is excluded. The admitted keys are 9..=15.
pub fn assessor_flag_complex(
    xor_key: usize,
    simplex_budget: usize,
) -> Result<AssessorFlagComplex, FlagComplexError> {
    if !(9..=15).contains(&xor_key) {
        return Err(FlagComplexError::InvalidAssessorXorKey(xor_key));
    }
    let assessors: Vec<_> = crate::boxkites::primitive_assessors()
        .into_iter()
        .filter(|assessor| assessor.low ^ assessor.high == xor_key)
        .collect();
    let mut edge_witnesses = Vec::new();
    for left in 0..assessors.len() {
        for right in left + 1..assessors.len() {
            if let Some((left_sign, right_sign)) =
                exact_diagonal_zero_product(assessors[left], assessors[right])
            {
                edge_witnesses.push((left, right, left_sign, right_sign));
            }
        }
    }
    let edges: Vec<_> = edge_witnesses
        .iter()
        .map(|&(left, right, _, _)| (left, right))
        .collect();
    let complex = FlagComplex::from_edges(assessors.len(), &edges, simplex_budget)?;
    Ok(AssessorFlagComplex {
        assessors,
        edge_witnesses,
        complex,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use cd_kernel::cayley_dickson::cd_multiply;
    use num_traits::One;

    #[test]
    fn assessor_flag_complex_has_verified_sphere_betti_numbers() {
        let graph = assessor_flag_complex(11, 26).unwrap();
        let labels: Vec<_> = graph
            .assessors
            .iter()
            .map(|assessor| (assessor.low, assessor.high))
            .collect();
        assert_eq!(
            labels,
            [(1, 10), (2, 9), (4, 15), (5, 14), (6, 13), (7, 12)]
        );
        assert_eq!(graph.edge_witnesses.len(), 12);
        for &(left, right, left_sign, right_sign) in &graph.edge_witnesses {
            let product = cd_multiply(
                &graph.assessors[left].diagonal(f64::from(left_sign)),
                &graph.assessors[right].diagonal(f64::from(right_sign)),
            );
            assert!(product.iter().all(|&coordinate| coordinate == 0.0));
        }
        let cell_counts: Vec<_> = graph.complex.simplices().iter().map(Vec::len).collect();
        assert_eq!(cell_counts, [6, 12, 8]);
        let certificate = graph.complex.rational_homology();
        assert_eq!(certificate.boundary_ranks, [0, 5, 7]);
        assert_eq!(certificate.betti_numbers, [1, 0, 1]);
        assert!(certificate.verify(&graph.complex));
        let mut damaged = certificate;
        damaged.boundaries[1][(0, 0)] += BigRational::one();
        assert!(!damaged.verify(&graph.complex));
        damaged.boundaries[1][(0, 0)] = BigRational::new_raw(1.into(), 0.into());
        assert!(!damaged.verify(&graph.complex));
    }

    #[test]
    fn simplex_filling_changes_cycle_homology() {
        let cycle = FlagComplex::from_edges(4, &[(0, 1), (1, 2), (2, 3), (3, 0)], 8).unwrap();
        assert_eq!(cycle.rational_homology().betti_numbers, [1, 1]);
        let filled =
            FlagComplex::from_edges(4, &[(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)], 11).unwrap();
        let certificate = filled.rational_homology();
        assert_eq!(certificate.betti_numbers, [1, 0, 0]);
        assert!(certificate.verify(&filled));
    }

    #[test]
    fn graph_domain_and_budget_fail_explicitly() {
        assert_eq!(
            FlagComplex::from_edges(2, &[(0, 2)], 8),
            Err(FlagComplexError::InvalidEdge(0, 2))
        );
        assert_eq!(
            FlagComplex::from_edges(2, &[(1, 1)], 8),
            Err(FlagComplexError::InvalidEdge(1, 1))
        );
        assert_eq!(
            FlagComplex::from_edges(2, &[(0, 1), (1, 0)], 8),
            Err(FlagComplexError::DuplicateEdge(1, 0))
        );
        assert!(matches!(
            assessor_flag_complex(11, 25),
            Err(FlagComplexError::SimplexBudgetExceeded(25))
        ));
        let empty = FlagComplex::from_edges(0, &[], 0).unwrap();
        assert!(empty.rational_homology().verify(&empty));
        let isolated = FlagComplex::from_edges(3, &[], 3).unwrap();
        assert_eq!(isolated.rational_homology().betti_numbers, [3]);
    }
}
