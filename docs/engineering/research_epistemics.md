---
description: Evidence layers, interpretive depth, matched controls, and falsifier rules for registered claims
last_verified: 2026-10-30
status: active
---

# Research epistemics

Scope: every claim, insight, and experiment that enters the registry.
The "Registry mutation workflow" in `registry/AGENTS.md` governs how a write
happens; this section governs what earns an ID.

Each rule below cites the repository's own record as its authority. A
rule with no claim ID behind it is a convention; a rule with one is a
finding, and the finding outranks the preference.

### Evidence layers

`docs/engineering/claim-theorem-identity-frontier-2026_08_04.md` fixes
three layers and one invariant: evidence at one layer never promotes a
claim at another.

| Layer                      | Records                                                          | Decisive evidence                                       |
| -------------------------- | ---------------------------------------------------------------- | ------------------------------------------------------- |
| Source proposition         | What a paper, theorem, or cited equation asserts                 | The primary source, cited by name and section           |
| Implementation conformance | Whether code implements that proposition                         | A passing test, a Rocq `Qed.`, a reproducible run       |
| Phenomenological mapping   | Whether parameters or observables support the physical reading   | A preregistered comparison against matched controls     |

Implementation correctness is decisive for its own layer and carries
no weight at the layer above. The `hypothesis_class` distribution
makes the asymmetry measurable: count `verified_claim` against
`falsifiable_thesis` rows in `registry/claims_atoms.toml`. Reading the first count as a scoreboard for the
second is the error the invariant forbids.

Belief, coherence, analogy, and cross-domain recurrence generate
hypotheses. Recurrence becomes evidence only when the recurring
domains share no analysis pipeline, no normalization, and no lift;
recurrence through a shared pipeline measures the pipeline.

### Interpretive depth

Lifts, wavenumber selections, embeddings, normalizations, and
parameter fits stand between an algebraic structure and an observable.
Their count is itself a measurement, and the record shows it dominates
the result.

| Depth | Protocol                                     | Outcome in this repository                                                                                                                              |
| ----- | -------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 0     | Associator applied directly to a signal      | Structure-specific: scrambling the CD sign table at identical 1848-term support collapses ROC-AUC 0.8274 to 0.4750 (C-1632)                             |
| 1     | Algebraically-selected wavenumbers, stacked  | Degenerate null: CD-ZD, G2 Aut(O) and Albert J3(O) each return SNR 0.29 and sl(2) returns 0.23 (C-1372); D=16 through 262144 return identical RMS (C-1366) |
| 2     | 42 assessors -> Herm_3 -> mixing angles      | Fitted agreement at four free parameters through a lift proved non-S_3-equivariant, hence underivable from the algebra (C-1502, C-1489, C-1492)         |

Rules:

- A scientific claim MUST enumerate its intervening maps and declare
  the count.
- A signal MUST NOT be attributed to an algebraic structure until it
  is shown specific to that structure: it survives substitution of a
  different algebra, randomization of the structure at fixed support,
  and removal of each map in turn.
- A result identical across algebras or across dimensions measures the
  pipeline, not the algebra. C-1366 names the mechanism in its own
  case (the `assessor_fraction=0.5` identity).
- A lift that cannot be derived from the structure it expresses MUST
  be recorded as a construction with its free-parameter count, and
  MUST NOT be cited as evidence for that structure. C-1476 is the
  obstruction (rank-2 Jacobian lock on the 42D->3D family), C-1478 the
  construction that breaks it, C-1489 the concession that it is
  project-specific.

`ClaimEvidenceSpec` in `provenance_store::claim_evidence` records maps by
branch and kind, fitted parameter counts, and interpretive depth. A declared
`lift_depth` equals the maximum number of interpretive maps along any branch;
computational maps remain separately enumerated. `depth_status = "not_assessed"`
requires an omitted `lift_depth` and an explicit rationale. An enumerated
computational pipeline therefore does not establish physical interpretive depth.
C-1740, C-1741, and C-1743 carry typed contracts; their physical depth remains unassessed.

### Matched controls

A control MUST preserve support, dimensionality, free-parameter count,
temporal receptive field, and measurement procedure, and destroy only
the proposed causal structure.

- Temporal receptive field is a confound in its own right. I-212
  records the case: an advantage over a one-step baseline partly
  measured temporal asymmetry, and at matched six-sample support the
  ranking reversed, with maximum stepwise rotation at 0.8383 over the
  associator at 0.8274 (C-1633).
- A single control draw is an anecdote. C-1632 states its own limit --
  one ChaCha8 scramble at seed 42 -- and leaves the ensemble open. A
  dominance claim SHOULD report a null distribution, not one
  comparison.

### Falsifiers

`what_would_verify_refute` is a typed outcome table in the C-1740, C-1741, and C-1743
contracts, with separate verification, revision, abandonment, and inconclusive
outcomes. Each contract names decisive experiments and a protocol artifact.
`gororoba-db claim set-evidence` validates the declaration and appends its full
previous and new values before compatibility export. A registered falsifier
defines an adjudication rule; experiment evidence determines the claim outcome.

- A `falsifiable_thesis` or `research_claim` MUST state what would
  refute it, which experiment adjudicates, and which outcome forces
  abandonment. C-1498 is the worked example: a predicted delta_CP near
  93 deg against a measured 195 +/- 25 deg, "Testable by DUNE and
  Hyper-Kamiokande".
- A `verified_claim` at the implementation layer needs no separate
  falsifier, because the test is the falsifier.
- Identify the cheapest DECISIVE falsifier and run it before extending
  a theory. When no cheap test is decisive, record the theory as
  untested; a cheap indecisive proxy manufactures confidence and is
  worse than silence.

- Separate effect evidence, declared target attainment, mechanism specificity
  and practical utility. An investigator-chosen discrimination target needs an
  application-based justification before anyone calls it a usefulness threshold.
  C-1743 and C-1754 retain positive effects below the historical 0.005 ROC-AUC
  target; their practical utility remains unassessed. Preserve historical targets
  and outcomes while correcting active interpretations through canonical revisions.
  Target attainment alone supplies no general scientific pass/fail gate.

### Refuted structures as controls

Refutations are retained permanently and their closure reason is typed
(`Closed/Negative-Result`, `Closed/Obstructed`,
`Closed/Methodology-Insufficient`, `Closed/Analogy`, and the rest of
the vocabulary).

- C-020 is the standing specimen: a 16D zero-divisor adjacency matrix
  that "does NOT represent valid algebra. Found to be
  noise/hallucination when verified against commutator/parity
  matrices." Generated structure that survives visual inspection is
  the characteristic failure mode of LLM-assisted work here, and the
  defense is a mechanical cross-check, not a closer reading.
- A claim reusing a refuted claim's pipeline, lift, or normalization
  inherits that refutation as a prior and MUST state what differs
  before registration.
- Structural analogy raises the evidentiary burden and never lowers
  it. C-036, C-037, C-038, C-040 and C-041 are five refutations of one
  shape: algebraically motivated, numerically near, empirically false.
  An attractive analogy is registered as a conjecture carrying a
  discriminating prediction, and is promoted only when that prediction
  survives.

### Instruments over essays

An interpretive argument left in prose is unfalsifiable by
construction. Convert it into a schema field, a provenance record, an
executable query, or a preregistered comparison.

`registry/scorecard.toml` is the model: `parameter_count` is declared
per observable and the bins are defined by it, with the bin-1 entries
at `parameter_count = 0` (count them in the scorecard) against a bin-2 PMNS fit at four. The
quantity such a scorecard measures is the derivative of agreement with
respect to parameter count, not agreement.

Tracked axes: free-parameter count, interpretive depth, symmetry
obligations discharged or waived, null-model performance, and the
falsification criterion.

Mathematics determines the invariants and the admissible
transformations. Experiment determines whether an invariant reaches an
observable. State each claim at the layer its evidence supports and no
higher; when the decisive experiment has not run, say so plainly and
run it next.
