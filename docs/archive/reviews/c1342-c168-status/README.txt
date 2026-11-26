Review record: registry transitions of C-1342 and C-168 (both Superseded)

Scope. C-1342 states the motif component count formulas as verified to D=4096 "analytically"; the
test motif_exact_rank enumerates 16D to 256D and records the extension as unproved. Transition
event 240 marks C-1342 Superseded (verdict Inconclusive); the enumerated finite statement is the
existing Provisional claim C-1715. C-168 infers sparser zero divisors at 128D from a first-100
sample. Transition event 241 marks C-168 Superseded (verdict Falsifies) and registers three
Provisional successors by narrows: C-1795 (6,942 of 7,875 unordered pairs e_i + e_j have nonzero
nullity at 128D, the continuation of the series that C-156 holds through 64D) and C-1796 (a zero
divisor has zero coordinates at e_0 and e_(D/2), cited to gororoba-math by path and theorem name). data/output/audit/c1342-c168-status
holds the source map, the two specifications and the census files. This record replaces two earlier
branches whose applied transitions (C-1342 with a new claim, C-168 Refuted; then C-168 with three
successors) the append-only database could not amend.

Reviewers. codex (gpt-daybreak-blue), agy gemini-4-neon-medium (red team) and agy
gemini-4-neon-low (decomposition of C-168), each read-only. The Advisor reviewed the three-successor round last; its overlap finding is item 0.

Findings.
0. Advisor: the C-168 successor by dimension repeats claims that hold the figures (the by-dimension
   counts are C-156; the 64D cross-half figure is C-1715). Fixed: C-168 registers exactly two
   successors. C-156 (Verified) holds 84, 588 and 3,036 zero divisors at 16D to 64D, equal to twice
   42, 294 and 1,518 pairs, and the fractions are context citing C-156; C-1795 states the 128D count
   (grep of registry/claims.toml: 6942, 13884 and 27768 have 0 hits). The 930 nonzero-nullity
   cross-half operands equal, as a set, the 930 motif nodes (31 x 30) of C-1715 (measured against
   the node lists of the motif_exact_rank report at 64D), so the figure lives in the rationale.
   The grep for "doubly pure" hits only the A5 statement (32D) and e_(D/2) has no hit, so the
   theorem successor is not a duplicate.
1. codex: Refuted on the whole of C-168 overreaches, because the 0-of-100 observation and the
   index-pair alternative are untouched. Fixed: C-168 is Superseded with narrowed successors, and the
   transition names the sparsity alternative as the falsified clause.
2. codex: the source map names commit 3c04c2eb for the run and the review names the pull-request
   head. Fixed: both name the tree of commit 3c04c2eb (base); the two implementation files carry
   their sha256, and the rerun report equals the retained report.
3. codex: report_sha256 lacks its path. Fixed: the retained report is an input of the source map.
4. neon-medium: C-1795 duplicates C-1715. Fixed: no duplicate is created. Boundary: the transition
   tool relates a predecessor only to a claim it creates, so C-1342 carries no relation row to
   C-1715 and the rationale names it; an existing-claim relation needs a tool change or an owner
   decision. The number C-1795 now denotes the 128D density successor.
5. neon-medium: (D/2 - 1)(D/2 - 2) overstates cross_assessors(D). Fixed: the text speaks of active
   motif nodes and states that cross_assessors(D) returns (D/2 - 1)(D/2) pairs.
6. neon-medium: the component count D/2 - 1 is not asserted by the test. Boundary: the source map
   says the count is read from the report; the test is unchanged.
7. neon-medium: the 64D figure 930 of 961 is cross-half, not the full census. Fixed: the rationale keeps
   the two domains apart and relates the figure to C-1715, and the cross-half counts were recomputed (nullities 28, 20, 12, 4, 0 on
   342, 168, 168, 252, 31 pairs; recount.json agrees).
8. neon-medium: the census omits e_0 and e_64. Fixed: C-1796 states the theorem; recount.json shows
   nullity 0 on every e_0 +- e_j and e_(D/2) +- e_j pair at 16D to 128D.
9. neon-medium: the sign classes of 27,768 of 31,500. Fixed: the successors count unordered pairs
   (6,942 of 7,875); the minus-sign pairs are the same pairs.
10. neon-medium: inputs under gororoba-math local/ are unretrievable. Fixed: census.json,
    tower_census.py.txt (the program under a .txt name, since the repository tracks no .py file),
    recount.json and recount.py.txt are copied unchanged with their sha256, and the dependency on
    cd_sign of gororoba-quantum is named by repository and path.
11. neon-medium: the review record must follow the local passes. Fixed: this record; the Advisor
    pass remains.
12. neon-medium: registry/markdown_export mirrors still read C-168 and C-1342 as Verified.
    Boundary: the drift predates this change (the preceding registry commit left them too) and no
    generator in the documented flow rewrites them.
13. neon-low: clauses 1a to 1e of C-168. Fixed: 1a is stated untested (the script and its JSON are
    absent from the history), 1b falsified, 1c consistent; the ordering is computed for two
    named orderings, the original ordering stays unknown, and the e_0 start is marked hypothesis.
14. neon-low: Superseded with Falsifies and narrows successors. Fixed as recommended.
15. neon-low: successor 2 as Verified. Boundary: Provisional, because the compile and kernel check
    of the cited sources are those of gororoba-math workflows. The file does not exist at the commit
    of ci/gororoba_math.pin (0c818156); at the cited commit 796aa5c1 the lean run 45587924245 and
    the rocq schedule run 45589354987 on main succeeded (the rocq push run was cancelled).
16. neon-low: the zero-divisor-is-doubly-pure row is T018. Refuted: the row is T017 (data row 17,
    file line 18 of tower-matrix.tsv); T018 is the kernel swap.
17. neon-low: C-144 (Verified) conflicts with census.json at 64D. Boundary: C-144 is not
    transitioned here; the owner decides on follow-up claims. C-156 needs no change.

Result. The committed specifications equal the applied ones: their sha256 equal
transition_spec_sha256 of events 240 and 241 in registry/claim_transitions.toml. Evidence classes:
the component counts (7, 15, 31, 63, 127 at 16D to 256D) are a measured run of motif_exact_rank
on the base tree; the census counts are retained outputs of two implementations with different
sign tables, which agree on every count and were not rerun here. Computed on the orderings of the
128D pairs e_i + e_j: (0,1) to (0,100) all have nullity 0; of (1,2) to (1,101), 86 have nonzero
nullity and 14 have nullity 0. The transition timestamps equal the apply time.

Validation (a compute host, under the shared lease): cargo test --profile validation -p
algebra_analysis --test motif_exact_rank (1 passed; report sha256 equals the retained report);
gororoba-db artifact register-local; gororoba-db claim transition plan and apply for each
specification (source-state digests and the claim-id maximum 1794 checked); make
registry-export-markdown, make registry-integrity and make registry-verify-mirrors (exit 0). No
Rocq or Lean ran. Hosted CI is the validation authority.
