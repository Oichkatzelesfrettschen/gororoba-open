Review record: quantum_core: partial-qubit compatibility without inventing Z tomography

Pull request: gororoba-open #273, branch quantum/partial-qubit-compatibility, merged 2026-11-16T05:29:11Z (GitHub mergedAt), squash commit f81aba2b4e9f18fef4ac751422972bf1d8f3a764 (one parent).

This record was written after the merge from the pull request itself (title, body, commits, reviews, issue comments and inline review comments as GitHub returns them). This record is a post-merge backfill, so no brief exists. Its scope is the pull request's own threads and the private orchestration record of the session that ran the Advisor and worker rounds below, which this repository does not retain; a step with no source in either reads "not recorded". Reviewer verdicts below are the threads' own; no later judgment is added.

Reviewers that ran:
- Hosted Codex (requested by an "@Codex review" comment, 2026-11-16T05:16Z): review of 1c986b25 completed; no findings, receipt "Didn't find any major issues".
- CodeRabbit: automatic review skipped (auto reviews are disabled on the repository); no findings.
- Further rounds recovered from the orchestration record (what ran, on which head, disposition): see "Rounds beyond the pull request" below.
- Local codex, grok and red-team rounds: not recorded.

Findings: hosted Codex raised none; the Advisor and worker findings are listed in the orchestration-record table of reconciliation.txt.

Rounds beyond the pull request
- Advisor, adopted-draft pass (2026-11-16, before the hosted round): confirmed 273. The orchestrator's note that the alpha == 0.0 clause is redundant was falsified: the interval 0.0..1.0 contains 0, and the clause is the only alpha = 0 rejection.
