# Selected-center nullity-twelve locus evidence

The [proof note](../../notes/nullity_twelve_local_geometry.md) proves the
complete real quadratic-compatible velocity set at `e1+e18`. The
[production certificate](../../../gororoba_quantum/nullity_twelve_locus.py)
retains every equation coefficient and verifies the two sum-of-squares
identities reducing the set to `A15 union B17`, with intersection dimension
13. Formal second-order solvability describes the certificate's API domain.
The proof note separately attributes the known smooth `B17` realization.
The [curve module](../../../gororoba_quantum/nullity_twelve_curves.py)
constructs an exact rational slice and certifies the rank-preserving actions
that realize every `A15` direction. Together those results identify the
complete selected-center tangent cone.

Run from the repository root with the pinned dependencies:

```sh
PYTHON="${PYTHON:-$(command -v python3)}"
GOROROBA_WORKERS=4 PYTHONDONTWRITEBYTECODE=1 \
  "$PYTHON" -W error docs/evidence/nullity_twelve_locus/replay.py --check
GOROROBA_WORKERS=1 PYTHONDONTWRITEBYTECODE=1 \
  "$PYTHON" -O -W error docs/evidence/nullity_twelve_locus/replay.py --check
(cd docs/evidence/nullity_twelve_locus && sha256sum -c SHA256SUMS)
```

The replay independently reconstructs the 32-dimensional multiplication
operators from `cd_sign`, the `66 x 30` derivative map, the complete
`30 x 21` first-order sphere kernel and the complete `66 x 58` cokernel.
It extracts all 231 quadratic coefficients, verifies a nonzero rank-eight
minor, and checks two full reconstruction matrices. Polynomial identities
and both coordinate-plane substitutions certify equality over all real
coefficients. Finite fixtures compare dense rational members of each piece
and two excluded directions against the separate direct acceleration solver.

The independent [curve proof](curve_proof.py) derives the four-parameter
slice through a separate route: a seed Schur identity, coefficient-complete
outer rotation, quaternion automorphism, isotropy and phase similarities.
It checks all 256 internal multiplication signs, all 1,344 octonion
derivation basis pairs, all 14,336 ordered basis pairs for their dimension-32
extensions, orbit rank eleven and completed slice/orbit rank
fifteen with image exactly `A15`. The production certificate instead
uses a direct three-variable polynomial kernel and pivot witness. Exact
rational point fixtures cross-check the two formulas and rank certificates.
An additional rational `e8` curve has a positive pivot determinant and
zero Schur residual for every real finite parameter.

The production module's command-line audit uses a separate quadratic-form
expansion for certificate verification and rejects corrupted matrices,
frames, minors, sum-of-squares data, plane definitions and input domains.
Normal and optimized Python executions retain active verification checks.
The independent replay binds the module, proof note and transitive source
inputs to source hashes, verifies imported module locations, and checks
those hashes again after execution.

`result.json` stores sparse exact matrices, monomial order, symbolic forms,
rank witnesses, real-locus identities, curve identities, and runtime
versions. Sparse records specify their matrix shape and encode
every omitted entry as zero. `SHA256SUMS` binds the README, replay, independent curve proof and result.
Source or dependency changes require reviewed regeneration; `--check`
carries the retained Python patch release when major.minor agree (gate
core-609).

The calculations use exact CPU algebra and submit zero QPU jobs. The
complete local rank locus, its attachments and global topological invariants
require further proofs beyond the quadratic certificate.
