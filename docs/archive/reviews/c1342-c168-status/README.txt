Review record: registry transitions of C-1342 (Superseded) and C-168 (Refuted)

Scope. C-1342 states the motif component count formulas as verified to D=4096 "analytically"; the
test motif_exact_rank enumerates 16D to 256D and records the extension as unproved. Transition
event 240 marks C-1342 Superseded (verdict Inconclusive) and registers C-1795 as a Provisional
successor (relation narrows) that states the enumerated range. C-168 infers sparser zero divisors
at 128D from a first-100 sample; the exact two-term nullity censuses show nonzero nullity for 930
of 961 pairs at level 6 (64D) and for 27768 of 31500 two-term elements at 128D. Transition event 241
marks C-168 Refuted (verdict Falsifies), with no successor. data/output/audit/c1342-c168-status
holds the source map and the two specifications.

Review. No local reviewer round ran for this record: the owner chooses the local reviewers per pull
request, and the parent session runs them before the hosted review. The coordinator's read-only
check required three wording corrections before the commit, applied before the apply: the 930 of 961
figure names level 6 (64D); the C-168 text states that the first-100 sample was not recomputed; the
C-1342 text cites the existing test motif_exact_rank in place of a function name that no repository
file holds.

Result. The committed specifications equal the applied ones: their sha256 equal
transition_spec_sha256 of events 240 and 241 in registry/claim_transitions.toml. Evidence classes:
the C-1342 component counts (7, 15, 31, 63, 127 at 16D to 256D) are a measured run of
motif_exact_rank on this commit; the C-168 counts are read from the gororoba-math tower census
(inputs identified by sha256 in the source map) and were not recomputed. The component count D/2 - 1
is read from the report the test writes and is not an assertion of the test.

Validation (a compute host, on the commit of this record): cargo test --profile validation -p
algebra_analysis --test motif_exact_rank (1 passed); gororoba-db artifact register-local; gororoba-db
claim transition plan and apply for each specification in order, each checking the claim's
source-state digest and the claim-id maximum (1794, 1795); make registry-export-markdown, make
registry-integrity and make registry-verify-mirrors (exit 0). No Rocq or Lean ran. Hosted CI is the
validation authority.
