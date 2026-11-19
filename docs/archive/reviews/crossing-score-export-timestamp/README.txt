# Brief: review of gororoba-open PR 295 at head caa952ef, the timestamp_us column of themis-staples-score-export

Read first: the workspace guide (AGENTS.md in the workspace root), then AGENTS.md and crates/AGENTS.md. Work read-only: change no file (the launcher captures your final answer); never commit, push, stash or start a job; spawn no subagents.
Binding host rule: this host runs no computation. Read files with cat, sed, head or git show on a named path and git diff on named paths. Run no cargo, no tests, no repository-wide grep. A check you would have run goes into your report as a fenced block `SCRIPT-n` with the output you expect.

Material: worktree the worktree of the branch, branch crossing-score-export-timestamp, head caa952ef (frozen). The change is `git diff origin/main...HEAD -- crates/gororoba_cli_physics/src/bin/themis_staples_score_export.rs` (80 inserted, 5 deleted). Consumer: a confirmatory benchmark joins this column against sorted day rows by timestamp and checks a float64 port of the associator against the exported values; it binds the export by digest, so a wrong time on any row silently misaligns its labels.

## Claims under review (justify or falsify each)
1. Each output row's `timestamp_us` is the UTC time, in integer microseconds since the Unix epoch, of the sample four rows after the window's first row, the same alignment the labels use. Falsifier: an off-by-one between the window index and the timestamp index, a different offset than the label code uses (cite both lines), or a time parse that loses sub-second precision or applies a time zone.
2. The finite-score filter drops the timestamp with its window, so row k carries its own time after any dropped window. Falsifier: a code path where scores and timestamps are filtered by separate predicates or iterated at different lengths.
3. The three readers named in the PR body (staples-roc-cluster-bootstrap by column name, staples-incremental-information by leading index with at least 10 fields, staples-roc-block-bootstrap by leading fields after file_id) ignore a trailing column. Falsifier: a reader that checks the field count exactly or reads the last field (cite file:line; read those binaries by path under crates/gororoba_cli_physics/src/bin/).
4. The unit test catches a wrong alignment: name a mutation of the offset (3 or 5 instead of 4) and say whether the test fails; name a mutation it misses.
5. Integer conversion: microseconds from the parsed time cannot overflow or round for 2007 to 2017 timestamps at 3 s cadence; a fractional-second input keeps its microseconds.
6. Defects, with file:line; and whether the header line names the column.

Report ranked by consequence, every claim tied to a file:line or a SCRIPT-n block, each marked proved, computed or hypothesis. Print it as your answer, under 150 lines.
