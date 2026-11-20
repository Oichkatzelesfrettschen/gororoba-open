Review record: casimir_core: audit Casimir stress against complete gravitational source tensors

Commit references: every commit named in this record is a full 40-hex hash. Each branch commit is reachable from refs/pull/270/head and each squash or merge commit from the default branch (git merge-base --is-ancestor, 2026-11-19).

Pull request: gororoba-open #270, branch casimir-warp-evidence, merged 2026-11-16T09:10:17Z (GitHub mergedAt), squash commit 14f63a201e4426bc5dc7354a19570b52f2684d15 (one parent).

This record was written after the merge from the pull request itself (title, body, commits, reviews, issue comments and inline review comments as GitHub returns them). This record is a post-merge backfill, so no brief exists. Its scope is the pull request's own threads and the private orchestration record of the session that ran the Advisor and worker rounds below, which this repository does not retain; a step with no source in either reads "not recorded". Reviewer verdicts below are the threads' own; no later judgment is added.

Reviewers that ran:
- Hosted Codex (requested by an "@Codex review" comment, 2026-11-16T09:06Z): review of 954120c17bcbd13a92bda64d9f05e5e6baad149d completed; no findings, receipt "Didn't find any major issues".
- CodeRabbit: automatic review skipped (auto reviews are disabled on the repository); no findings.
- Further rounds recovered from the orchestration record (what ran, on which head, disposition): see "Rounds beyond the pull request" below.
- Local codex, grok and red-team rounds: not recorded.

Findings: hosted Codex raised none; the Advisor and worker findings are listed in the orchestration-record table of reconciliation.txt.

Rounds beyond the pull request
- Advisor, partial read (about 21k of 63k characters of the diff): confirmed the Brown-Maclay tensor, the null contraction, the planar-shift Einstein tensor (independent ADM check), the zz residual of -2 and the licenses (casimir_core GPL-2.0-or-later, gr_core MIT). Blocking items: the warp_metric.rs diff unread (an off-center expansion-sign test needed), the audit binary tail and the audit report unread. Non-blocking: scalar versus electromagnetic constant, report bytes produced on a compute host, registry statements are owner-read, dispatch the audit validation after merge.
- Follow-up check by a Sonnet worker, head 954120c17bcbd13a92bda64d9f05e5e6baad149d (hosted run: 30 pass, 7 skipped): off-center expansion-sign tests already exist (Alcubierre closed form at (+-1.2, 1.0, 0.7), ADM York time, mirror check); the constant is electromagnetic (-4.33375e-4 J/m^3 and -1.30013e-3 Pa at 1e-6 m) and stress_energy reaches it through electromagnetic_unit_gap_energy_per_area_si (cbc28bce484e3e51edb186e13f93cc2d21bbc0bf); report bytes rewritten to the binary's exact output; body gains the registry follow-up and the post-merge audit dispatch. Disposition of the blocking items: closed by those checks.
- Hosted Codex on 954120c17bcbd13a92bda64d9f05e5e6baad149d: no findings; squash-merged afterwards.
