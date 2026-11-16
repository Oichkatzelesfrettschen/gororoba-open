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
- Flocq object digests must equal the entry of the producer that the evidence
  names in `flocq_producer`, in the committed copy of the gororoba-math Flocq
  manifest (`crates/provenance_store/fixtures/flocq_manifest/rocq-9.3.json`),
  when a new event key is admitted; this repository holds no Flocq object
  bytes. The object bytes depend on the install prefix and the native
  toolchain of the producer (measured: a hosted runner that built the same
  export produced different Flocq object bytes, first at `Calc/Bracket.vo`),
  so the manifest holds one entry per producer, and evidence that names no
  entry, an unknown entry or another producer's digests is rejected.
- The statement inventories under `curated/01_theory_frameworks/`
  (`ConfineModel.v` and `confine_theorems_512.v`, `confine_theorems_1024.v`,
  `confine_theorems_2048.v`) are statements without proofs here.
  gororoba-math `rocq/delegation` holds them with proofs under a defined
  delegation model; no make target here compiles them.
- `GOROROBA_MATH` names a gororoba-math checkout for the checks that read the
  proof tree; `ci/gororoba_math.pin` names the commit that hosted CI fetches.
