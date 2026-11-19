Review record: quantum_core: checked subsystem entropy and two-sided MPS contractions

Pull request: gororoba-open #271, branch quantum/checked-subsystem-entropy, merged 2026-11-16T12:14:29Z, merge commit 2848ae506b1b46e7e8f26763635062b4f4864984.

This record was written after the merge from the pull request itself (title, body, commits, reviews, issue comments and inline review comments as GitHub returns them). The orchestration board of the same session supplies the Advisor and worker rounds below; a step with no source in either reads "not recorded". Reviewer verdicts below are the threads' own; no later judgment is added.

Reviewers that ran:
- Hosted Codex (requested 2026-11-16T08:39Z): review of eb362102 completed with two P2 inline findings (C1, C2).
- GitHub Copilot: one review at 8153dacf with four inline findings (R1 to R4); it ran before the 2026-11-17 owner ruling that forbids Copilot rounds.
- CodeRabbit: automatic review skipped (auto reviews are disabled on the repository); no findings.
- Further rounds recovered from the orchestration record (what ran, on which head, disposition): see "Rounds beyond the pull request" below.
- Local codex, grok and red-team rounds: not recorded.

Findings: 6 inline finding(s); see reconciliation.txt

Rounds beyond the pull request
- Advisor, partial read (28 of 32 thousand characters): confirmed the MPS two-sided Schmidt spectrum, named-site semantics and the product test. Gaps: the diff tail unread (measure_entropy left-Gram path), MPS dense-fallback bit order untested, estimate_memory_bytes overflow-panic callers, the body must name the panic class. A Sonnet worker closed these; the MPS measure_entropy external caller is only a benchmark with a valid MPS, and TensorNetworkState::measure_entropy is a separate method.
- Hosted rounds: Codex at eb362102 (C1, C2) and Copilot at 8153dacf (R1 to R4); fixes landed in 8153dacf and dfd2bd0e, threads replied and resolved; no further hosted round ran before the merge on green CI.
