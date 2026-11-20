Review record: cosmology_core: scope the Jacobi iteration cap to the x87 lane

Pull request: gororoba-open #300, branch slit-projection-cfg-scoped-max-iter, head under review f00ab18828587b83557f7645b627a9227962d93c. Closes issue 292.

Reviewers chosen by the owner (question tool, 2026-11-19): local reviewers None; the Advisor reviews last; then hosted Codex.

Scope: the one-file diff of crates/cosmology_core/src/slit_projection.rs (the max_iter binding moves inside the x86_64 cfg block), the commit message and the pull-request body.
