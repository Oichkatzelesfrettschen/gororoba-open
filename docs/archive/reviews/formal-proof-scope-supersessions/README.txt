Review record: registry supersession of C-029, C-1130, C-1141, C-1233 and C-1236 by the statements their Rocq files prove (gororoba-open pull request replacing 304)

Scope. Five claims read Verified on the strength of kernel-checked gororoba-math
files that prove less than the claims state. Transition events 232 to 236 mark
them Superseded with verdict MethodologyInvalid and register C-1786 to C-1791 as
Provisional successors: for C-029, the proved classification of 15
coordinate-hyperplane subalgebras of the sedenions (supersedes) and the literature
proposition attributed to Gillard and Gresnigt (source_split); for the other four,
the statement each cited file proves (narrows).
data/output/audit/formal-proof-scope holds the source map and the five
specifications.

Review. One local round: codex (gpt-daybreak-blue-latest, high effort,
read-only) on commit 50d7069c of the first branch, then the Advisor last on the
revised specifications and the applied database. codex returned seven findings;
reconciliation.txt lists each with its check and resolution. Three changed the
specifications, so the transitions were applied again on a fresh branch from
main a5fbea4d, at commit c45ecf60; the first pull request (304) closes unmerged,
so its database blob never enters main.

Result. All eight gororoba-math file digests in the source map equal
gororoba-math main. The verdict of C-029 is MethodologyInvalid, and its
literature proposition survives as its own Provisional successor. Successor
statements hold only what the cited theorems state; computations and
implementation evidence sit in the boundaries, labeled by layer. Two
generator defects found by the review exist on main and are left to a follow-up
(reconciliation.txt, findings 1 and 3).

Validation (a compute host, on c45ecf60): gororoba-db claim transition apply for
each specification in order, each checking the claim's source-state digest and
the claim-id maximum; provenance export-control-plane; make registry-integrity;
make registry-export-markdown (23 of 23 mirrors emitted); make
registry-verify-mirrors (mirror immutability and claim-ticket mirrors OK).
Hosted CI is the validation authority.
