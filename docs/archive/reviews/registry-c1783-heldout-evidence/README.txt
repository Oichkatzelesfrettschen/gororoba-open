Review record: registry: C-1783 carries its held-out P13d evaluation (gororoba-open pull request 303)

Scope. The pull request appends the held-out result of the preregistered rule
P13d to claim C-1783 through the audited correct-content mutation (status stays
Provisional) and names the three P13d records in where_stated.

Review. One local round on head 24562919, chosen by the owner for gororoba-quantum
pull requests 982 to 984 and this one: codex (gpt-daybreak-blue, high) and grok
as reviewers, agy (gemini-4-neon-high) and opencode (opencode-go/deepseek-v4-pro)
as red-teamers, the Advisor last. All four read one brief; raw reports stay
outside the tree.

Findings and dispositions.

1. codex, agy, grok, opencode. The mutation re-exported registry/claims.toml
   only; claims_atoms.toml, claims_evidence_edges.toml, knowledge/claim_atoms.toml,
   knowledge/derivation_steps.toml, knowledge/proof_skeletons.toml and the Rust
   claims mirror kept the old statement and where_stated, and the pull-request
   checks do not compare the Rust mirror. Fixed in 096960a7: the mutation was
   rerun from main's database and make registry-export-markdown regenerated the
   whole surface; the regeneration also refreshes the sha256 that
   registry/knowledge_sources.toml records for the agents and entrypoint
   documents, which was stale on main.

2. agy, grok. The appended sentence said "on configurations held out of those
   runs", which points at the Gaussian-peak runs of the claim, while P13d holds
   out six 64x64x4 shear-layer runs from the development runs of P13a to P13c
   (lbm-late-failure-heldout-registration.txt). Fixed in 096960a7: the sentence
   names the shear-layer runs, their grid and relaxation times, and that the 12
   decided pairs come from the three runs that give pairs.

3. codex, grok, opencode. The counts (0 of 12 decided pairs, none skipped, the
   0.95 orbit quantile, the 0.02 margin) match p13d_rule_applied in
   lbm-late-failure-heldout-null.json. Confirmed; no change.

4. agy. Two of the 12 pairs sit within 0.02 of the ceiling
   (lbm-late-failure-heldout-attainability.txt), and three of the six held-out
   runs give no pair. Boundary: the attainability record states both and is in
   where_stated; the sentence now states the three-run count.
