<!-- AUTO-GENERATED: DO NOT EDIT -->
<!-- Source of truth: registry/requirements.toml; registry/requirements_narrative.toml -->

# Requirements: Rocq Proof Checking

The Rocq proof tree lives in gororoba-math under `rocq/open`. This repository
runs no Rocq: no workflow, make target, command or binary here installs or
invokes the Rocq toolchain.

gororoba-math compiles every proof source and kernel-checks the result with
`sh ci/check_rocq.sh` under Rocq 9.3.0; its toolchain and proof commands are
in `rocq/open/README.md` there. Its producer `ci/kernel_replay_evidence.py`
writes the replay evidence file for one proof source.

This repository ingests that file:

```bash
gororoba-db theorem identity record-kernel-evidence --spec SPEC --evidence FILE
```

Notes:

- Ingest binds the sources, the project file, the proof object and the
  retained logs to the witness and the proof tree, and checks the argument
  vectors and the compilation order of the evidence file. It trusts the
  producer for the fact that Rocq ran; no process attestation exists.
- Flocq object digests are recorded as the producer reports them and are
  compared with no bytes in this repository.
- `GOROROBA_MATH` names a gororoba-math checkout for the checks that read the
  proof tree; `ci/gororoba_math.pin` names the commit that hosted CI fetches.
