---
description: Comment voice, citation forms, finding-doc rules, markdown style, and text-hygiene gate details
last_verified: 2026-10-30
status: active
---

# Comment and commit style

Banned comment patterns (task numbers, PR numbers, phase labels, session dates,
deictic terms) live in the user-level guide; this document carries the
repository-specific forms.

## Text hygiene gates

`ansi-check` and `terminology-gate` are the two text gates. `ansi-check` is an
anti-emoji gate, not an ASCII gate: in `--check` mode it fails a file
only on an emoji or on a control character other than tab, newline or
carriage return. Smart quotes, en/em dashes, arrows, Greek letters,
box-drawing and accented characters all pass it. Writing ASCII
remains the house convention and `--fix` rewrites the typographic
substitutes through `CHARACTER_POLICY_REPLACEMENTS`, NFKD
normalization and combining-mark removal, but the gate does not
enforce it, so a reviewer catches what the hook does not.
The emoji predicate covers six ranges -- Emoticons, Miscellaneous
Symbols and Pictographs, Transport and Map, Supplemental Symbols and
Pictographs, regional-indicator Flags, Variation Selectors -- and
omits Miscellaneous Symbols (U+2600..U+26FF), Dingbats
(U+2700..U+27BF) and Symbols and Pictographs Extended-A
(U+1FA70..U+1FAFF), so a warning sign, check mark or cross mark
passes. A green `ansi-check` is not proof that a file is emoji-free.
The check skips binary and build-artifact extensions, everything
under `data/external/papers`, files over 10 MB, and files that are
not valid UTF-8. `terminology-gate` is a separate check over the
eight banned legacy terms in `registry/terminology_standards.toml`
and has nothing to say about encoding.

### Source code MUST contain (when domain-specific)

- Absolute identifiers (crate name + module path) for any
  cross-crate citation, so the reader can navigate without context:

| Subject                               | Canonical form                                                     |
| ------------------------------------- | ------------------------------------------------------------------ |
| Cayley-Dickson dimension              | "8D (octonions)", "16D (sedenions)", "32D (pathions)"              |
| LBM lattice                           | "D3Q19 BGK", "D3Q27 MRT"                                           |
| Backend                               | "Vulkan (ash)", "cubecl-wgpu", "CUDA (cudarc)"                     |
| Precision tier                        | "FP32", "FP16", "BF16", "FP8 e4m3", "INT8 SoA"                     |
| Claim / Insight / Experiment / Binary | `C-1234`, `I-0042`, `E-201`, `B-bin_name` (matches registry IDs)   |
| Rocq theorem                          | `Brown1972ChapterIII::brown_3_1_trace`, `Moreno1997::theorem_1_16` |

- Bit-field / SoA layout commentary
  (`SoA: f[channel * n_cells + cell_idx]`).
- Empirical numerical behaviour (`f32 GPU vs f64 CPU drifts ~1e-4
  relative per D3Q19 step at low Mach`).
- Mathematical invariants and non-obvious workaround rationale.
- Reference citation by name + chapter/section, not by line number
  or internal-repo path:

| WRONG (internal)                                    | RIGHT (public)                                                                                                      |
| --------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------- |
| `// per data/sources/moreno_1997_zd_paper.txt:1572` | `// per Moreno (1997), "Zero divisors of the Cayley-Dickson algebras over the reals", J. Algebra 196, Theorem 1.16` |
| `// see audit_2026_04_30.csv row 12`                | `// see DEBT-DUPLICATION class in plans/repo_debt_roadmap_2026_04_11.toml`                                          |

### Markdown finding-doc rules

Markdown bodies MAY carry chronology (every finding-doc has dated
frontmatter -- `last_verified`, `evidence_class`, dated filename,
ordered predecessors). That is intentional.

PR# / task# references MUST triangulate with a durable identifier:

| WRONG (PR# alone)           | RIGHT (durable primary + PR# cross-link)                                                                                                                           |
| --------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `the fix landed via PR #38` | `landed in commit f79a37fa (cd_kernel/turboquant/cuda migration to gpu_cuda); PR #38 / branch session/wave-c2-cd-kernel-turboquant-cuda-2026-05-15 for cross-link` |
| `see issue #157`            | `see CLAIMS.md row C-1234 (issue #157 if still open)`                                                                                                              |

### Commenting voice

Adopted from steinmarder/AGENTS.md "Commenting voice"; adapted to
Rust:

- A short paragraph opens with the claim the rest of the block rests on
  ("PUSH-scheme writes are race-free because dst = src + c_i is a
  bijection on cells for each fixed i.").
- Then the primary-source citation, by name -- the function
  (`LbmSolver3D::phase2_streaming`), the paper section, the type
  (`StoragePrecision::Fp32`) -- not an internal-repo file extract.
- Then the consequence in one or two lines, with a fragment of
  code inlined when that is clearer than prose.
- A test name or benchmark reference when the comment exists to
  explain a regression being fixed.
- Env knobs / feature flags described together at the bottom of the
  block when relevant.

The distillate -- subtle shifts on top of the existing voice:

- Default short. One-line trailing comments on the decisive line
  beat a function-header paragraph, unless the function as a whole
  encodes a non-obvious invariant.
- One thought per comment; stack them when steps are distinct,
  rather than fusing into a multi-clause sentence.
- Do not paraphrase the next line of code. The comment is about
  WHY the code is shaped that way -- the numerical constraint, the
  paper section, the measurement -- not what it does.
- When the code is mechanical, no comment. Comments earn their
  place by carrying information that does not survive in the code
  itself.
- Anchor citations by name (paper title + section, Rocq theorem
  identifier, registry C-/I-/E-/B- ID) rather than by line number
  or repo-internal path.
- Multi-paragraph blocks are reserved for the genuine
  numerical-quirk WHYs -- the kind of finding that took a long
  bench measurement or a Rocq proof to land.

Three prose-level leans -- subtle, but they are what makes a comment
feel like everything just makes sense:

- State mechanism in the active voice ("the GPU reads f_in and
  writes the periodic-neighbor cell"), not in the passive
  ("f_in is combined with the offset").
- Let sequence be the explanation. "X. Then Y. Then Z." -- one
  sentence per step, each doing one thing -- beats one sentence
  with three clauses.
- Chain each WHY by what the next step needs, so the comment moves
  forward instead of cataloguing in parallel.
  ("...so the descriptor write can resolve the relocation" tells
  the reader where the explanation is heading.)

Example shape:

> The PUSH-scheme kernel reads 19 own-cell f values. It computes
> rho, u, f_eq, applies BGK collision in registers, then writes
> each post-collision f_i to the periodic-neighbor destination cell.
> For any fixed direction i, src -> src + c_i is a bijection on the
> periodic lattice, so the 19 scattered writes per thread are
> race-free without atomics.

This composes with the comment-hygiene rules above (no task #, no
PR #, no Phase X.Y, no deictic refs). Together: short, active,
sequenced, primary-source-grounded, time-invariant.

### LLM-readable markdown style

For files an LLM agent might slice-load (AGENTS.md, CLAUDE.md,
finding-docs, memory entries):

- MUST use heading depth <= 3 levels.
- MUST use exactly one H1 per file (the document title).
- MUST include frontmatter on programmatically-loaded files.
- MUST use language tags on code fences (`bash`, `rust`, `toml`,
  `wgsl`).
- SHOULD prefer tables over bullet lists for 3+ comparable items.
- MUST NOT use emoji, ASCII boxes, banner dividers in rules text.
  `ansi-check` blocks the emoji; the boxes and dividers are on the
  author.
- MUST name the exact section or path instead of using relative
  position phrases; the file may be slice-loaded.
- MUST use MUST / MUST NOT / SHOULD imperative voice in rules.
