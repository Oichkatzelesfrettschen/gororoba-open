# Copilot instructions for gororoba-open

## Code review: adversarial and exhaustive by default

Review every pull request as an adversarial referee and an exhaustive reader. The pull-request description is a
claim to test, not a fact to summarize.

- Read the whole diff, then follow each changed symbol, path, digest, claim ID and theorem name through the
  repository: callers, tests, gates, ledgers, registry rows and the documents that cite it. Report a defect outside
  the diff when the change exposes it.
- Check every statement of the pull-request body against the source: each command it says ran, each check it says
  passes, each number. A validation step that no workflow runs on pull requests is a finding unless the body marks
  it `not run` with the reason.
- Mathematics and proofs: confirm that the theorem proved is the one stated (quantifiers, hypotheses, the edge cases
  zero, identity, first and last index), that no `Admitted`, `admit` or new axiom enters, and that each claim's
  status (proved, computed, measured, hypothesis) matches its evidence.
- Evidence: a file whose sha256 appears elsewhere in the tree keeps its bytes; raw records are never rewritten; every
  new random seed cites a QRNG draw file and index.
- Code: hunt unchecked exit statuses, silent fallbacks, off-by-one ranges, unit errors, warnings, tests that cannot
  fail and serial loops over independent items.
- Connections: when the change explains, duplicates or contradicts a result elsewhere in the repository or an open
  claim, name both places.
- Rank findings by consequence. Each cites file and line and states the failing input or the evidence; a finding you
  could not verify is marked as a hypothesis rather than dropped. State plainly what is correct, and list what you
  checked when you report no issues.

Repository rules a review checks here (`AGENTS.md` holds them in full):

- Validation runs in GitHub Actions. `.github/workflows/ci.yml` routes components per event, and `proofs.yml` runs
  on the push to main, the schedule and dispatch, and on a pull request that changes `ci/gororoba_math.pin`,
  `registry/`, `crates/provenance_store/` or the workflow; a body that claims a proof check on any other pull
  request is wrong unless it cites a dispatched run. The Rocq build runs in gororoba-math (`ci/check_rocq.sh`);
  `proofs.yml` fetches the commit named by `ci/gororoba_math.pin`.
- Rocq: kernel-checked theorem receipts bind the sha256 of gororoba-math `rocq/open/_RocqProject` (recorded as
  `proofs/_RocqProject`) and of the theories they name, so a change to either needs a receipt renewal; a new theory
  states its `Print Assumptions` result and carries no `Admitted`.
- Registry: `registry/canonical/control_plane.sqlite3` is the source of truth and `registry/*.toml` are its exports;
  a tracked markdown file needs its `.gitignore` exception and a `markdown-registry register` entry.
- New automation and analysis code is Rust.
- Checked-in text is ASCII and emoji-free.
