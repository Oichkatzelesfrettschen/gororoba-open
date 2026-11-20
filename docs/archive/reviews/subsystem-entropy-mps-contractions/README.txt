Review record: quantum_core: checked subsystem entropy and two-sided MPS contractions

Commit references: every commit named in this record is a full 40-hex hash. Each branch commit is reachable from refs/pull/271/head and each squash or merge commit from the default branch (git merge-base --is-ancestor, 2026-11-19).

Pull request: gororoba-open #271, branch quantum/checked-subsystem-entropy, merged 2026-11-16T12:14:29Z (GitHub mergedAt), squash commit 2848ae506b1b46e7e8f26763635062b4f4864984 (one parent).

This record was written after the merge from the pull request itself (title, body, commits, reviews, issue comments and inline review comments as GitHub returns them). This record is a post-merge backfill, so no brief exists. Its scope is the pull request's own threads and the private orchestration record of the session that ran the Advisor and worker rounds below, which this repository does not retain; a step with no source in either reads "not recorded". Reviewer verdicts below are the threads' own; no later judgment is added.

Reviewers that ran:
- Hosted Codex (requested 2026-11-16T08:39Z): review of eb362102ecf9c7cd4aa0a57e6dc5a51b0cb263a7 completed with two P2 inline findings (C1, C2).
- GitHub Copilot: one review at 8153dacf1300400207323c1134e633b32a89af2c with four inline findings (R1 to R4); it ran before the 2026-11-17 owner ruling that forbids Copilot rounds.
- CodeRabbit: automatic review skipped (auto reviews are disabled on the repository); no findings.
- Further rounds recovered from the orchestration record (what ran, on which head, disposition): see "Rounds beyond the pull request" below.
- Local codex, grok and red-team rounds: not recorded.

Findings: 6 inline finding(s); see reconciliation.txt

Rounds beyond the pull request
- Advisor, partial read (28 of 32 thousand characters): confirmed the MPS two-sided Schmidt spectrum, named-site semantics and the product test. Gaps: the diff tail unread (measure_entropy left-Gram path), MPS dense-fallback bit order untested, estimate_memory_bytes overflow-panic callers, the body must name the panic class. A Sonnet worker closed these; the MPS measure_entropy external caller is only a benchmark with a valid MPS, and TensorNetworkState::measure_entropy is a separate method.
- Hosted rounds: Codex at eb362102ecf9c7cd4aa0a57e6dc5a51b0cb263a7 (C1, C2) and Copilot at 8153dacf1300400207323c1134e633b32a89af2c (R1 to R4); fixes landed in 8153dacf1300400207323c1134e633b32a89af2c and dfd2bd0e1b9fba4c2308736af7badcb754fcffe6, threads replied and resolved; no further hosted round ran before the merge on green CI.
