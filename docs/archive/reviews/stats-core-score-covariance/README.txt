Review record: stats_core: retain full multinomial score covariance

Pull request: gororoba-open #269, branch stats_core/measurement-scores, merged 2026-11-16T08:33:58Z, merge commit 76fa9bb1805d6c825128c41525fbb184a3a6e094.

This record was written after the merge from the pull request itself (title, body, commits, reviews, issue comments and inline review comments as GitHub returns them). The orchestration board of the same session supplies the Advisor and worker rounds below; a step with no source in either reads "not recorded". Reviewer verdicts below are the threads' own; no later judgment is added.

Reviewers that ran:
- Hosted Codex (requested 2026-11-16T05:16Z): review of 1b7ee1db completed with one P2 inline finding (C1).
- GitHub Copilot: one review at 3823d7d6 with one inline finding (R1); it ran before the 2026-11-17 owner ruling that forbids Copilot rounds.
- CodeRabbit: automatic review skipped (auto reviews are disabled on the repository); no findings.
- Further rounds recovered from the orchestration record (what ran, on which head, disposition): see "Rounds beyond the pull request" below.
- Local codex, grok and red-team rounds: not recorded.

Findings: 2 inline finding(s); see reconciliation.txt

Rounds beyond the pull request
- Advisor, adopted-draft pass (2026-11-16, before the hosted rounds): confirmed 269; no commits followed.
- Implementing worker (Opus) rework at the head after c8f67c94 (centering by TwoSum pairs, exact weights n/2^K, Dot2 mean and covariance; Ogita, Rump and Oishi 2005, Algorithms 3.1, 3.5, 5.3): new tests for mixed scale (all six column orders), counts [3,7,10] and a reversed rare outcome; the earlier code fails the mixed-scale tests; compute-host validation 294 tests, clippy with denied warnings and rustfmt on the file clean. The worker's own advisor call timed out, so the covariance bound derivation had no second review; the module doc marks the bound a hypothesis (f2ef3f22), on the Advisor's note that it is derived and unreviewed.
- Advisor, owner-requested pass on e53f8f01 (exact_scale, fail-closed rescale): confirmed. A subnormal scales back up exactly, so the round trip matches only for an exact down-scale; the doc sentence is accurate. Disposition: the PR body states the refusal contract, including rows whose earlier result was correct ([1e200, 1e-150] with [2, 1]), and that this head had no hosted round.
- Hosted rounds: Codex at 1b7ee1db (C1) and Copilot at 3823d7d6 (R1); after e53f8f01 no hosted round ran.
