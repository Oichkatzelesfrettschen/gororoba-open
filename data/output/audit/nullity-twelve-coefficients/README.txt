Complete selected-center coefficient table
=========================================

The retained source has 58 projected equations in 231 ordered monomials.
A pinned standalone Rust program rejects malformed sparse input, checks every
entry of the 58 by 231 reconstruction and the eight reduced pivot columns,
and emits a Rocq source. Rocq independently checks the integer reconstruction,
canonical square-first monomial order, all real row identities, inverse
generator recovery, and equality with the selected A15 union B17 zero set.

The table is retained evidence. Equality between the table and the actual
Schur expansion of the recursive dimension-32 multiplication operator remains
a separate proof obligation. Curve realization, exact operator rank, tangent
limits and global geometry require their named subsequent certificates.
The checkpoint has source_only qualification outside the canonical inventory.

Run from the isolated repository root, with every path resolved there:

CARGO_TARGET_DIR="$PWD/.cache/exp-nullity-coefficients-target" NULLITY_SOURCE="$PWD/data/output/audit/nullity-twelve-coefficients/frozen/docs/evidence/nullity_twelve_locus/result.json" cargo test --locked --offline --manifest-path data/output/audit/nullity-twelve-coefficients/Cargo.toml
CARGO_TARGET_DIR="$PWD/.cache/exp-nullity-coefficients-target" cargo clippy --locked --offline --manifest-path data/output/audit/nullity-twelve-coefficients/Cargo.toml --all-targets -- -D warnings
CARGO_TARGET_DIR="$PWD/.cache/exp-nullity-coefficients-target" cargo run --locked --offline --manifest-path data/output/audit/nullity-twelve-coefficients/Cargo.toml -- data/output/audit/nullity-twelve-coefficients/frozen/docs/evidence/nullity_twelve_locus/result.json /tmp/NullityTwelveCoefficientCertificate.v
cmp /tmp/NullityTwelveCoefficientCertificate.v proofs/checkpoints/schur-geometry/NullityTwelveCoefficientCertificate.v
opam exec --switch=rocq-9.3 -- rocq compile -q -w @default -Q proofs/theories OpenGororoba -Q proofs/checkpoints/schur-geometry OpenGororobaCheckpoint proofs/checkpoints/schur-geometry/NullityTwelveCoefficientCertificate.v
opam exec --switch=rocq-9.3 -- rocq check -silent -o -Q proofs/theories OpenGororoba -Q proofs/checkpoints/schur-geometry OpenGororobaCheckpoint OpenGororobaCheckpoint.NullityTwelveCoefficientCertificate

Compile the unchanged dependency theories/NullityTwelveQuadraticLocus.v first
on a fresh checkout. The full corpus build supplies that dependency at admission.
Frozen .py files preserve external producer bytes; Rust supplies new tooling.
IBMQuantum remains read-only and quantum submissions remain prohibited.

Replay source identities and the negative controls from the same repository root:

sha256sum -c data/output/audit/nullity-twelve-coefficients/SHA256SUMS
rustc --edition=2024 -D warnings data/output/audit/nullity-twelve-coefficients/mutate_coefficients.rs -o /tmp/nullity-coefficient-mutations
/tmp/nullity-coefficient-mutations "$PWD" /tmp/nullity-coefficient-mutation-results
opam exec --switch=rocq-9.3 -- rocq top -quiet -Q proofs/theories OpenGororoba -Q proofs/checkpoints/schur-geometry OpenGororobaCheckpoint < data/output/audit/nullity-twelve-coefficients/exported-assumptions.v

The mutation runner compiles the unchanged positive control, then requires
coefficient, reconstruction, monomial-order and generator-sign rejection at
the mathematical checks. The retained stdout/stderr files record those verdicts.
