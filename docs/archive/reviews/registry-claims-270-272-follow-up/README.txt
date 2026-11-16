Registry claims 270/272 follow-up: review record

Subject: pull request 290, "registry: narrow the warp-interior and
spectral-dimension claims to their evidence". The branch narrows C-869,
C-874 and C-922 to the evidence that decides them (status Verified to
Partial by recorded claim transitions), splits the scalar worldline Monte
Carlo diagnostic from C-871 into C-1785 (Provisional, relation
implementation_split), retains the version 2 spectral census, and
regenerates registry/experiment_lineage.toml.

Reviewers (owner selection of 2026-11-16): the Advisor only. No other local
reviewer ran. Each round names the head it read.

Rounds:
- Round 1 read d9cf9862 (second-pass predecessor of the owner-decision
  mutation pass).
- Round 2 read 9c96b611 (head after the owner-decision mutation pass).

Read-only verification pass: before round 1 closed, a read-only pass
re-derived the numbers behind the statements from the retained curve rows,
the test sources and the pin sweep. Its measurements are quoted in
reconciliation.txt where a finding depends on them.

Claim text of record: the Statements section of the pull request body holds
the exact stored text of every changed row; registry/claims.toml and
registry/experiments.toml hold the exported rows.

Files:
- reconciliation.txt: each finding of each round, its disposition and the
  commit that resolved it.
