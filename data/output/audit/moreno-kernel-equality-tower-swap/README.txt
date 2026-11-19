Receipt renewal for the proof project that lists the tower kernel swap.

proofs/_RocqProject gains CDTowerKernelSwap.v, MorenoTowerInstance.v and
MorenoSwapIndependence.v and hashes to
ee514ff423105d4faa4530e8a4e915d277631c3009ae5b460b175e3a16238c06. Kernel-checked
theorem receipts bind the project digest, so the control-plane invariant
"kernel_checked theorem ... lacks a valid source-bound execution receipt" failed
for THM-LEGACY-BooleanANFDegree and every other kernel-checked theorem
(control-plane-before.txt).

renew_receipts.sh, run with the gororoba-db executable built from this tree,
appends one inventory event (inventory.toml, inventory.log: 350 modules) and
then, for each of the 54 receipts of
data/output/audit/vacuum-composition/main-integration/receipts, writes a
specification that differs from it in the event key, actor, reason, timestamp
and project digest alone and passes it to
"gororoba-db theorem identity record-kernel-evidence". The command compiles
the exact source closure with the pinned Rocq 9.3.0 / OCaml 5.5.1 switch and
checks the object, the kernel result and the declaration assumptions before it
admits the event. replay.log lists the 54 exits (all 0); receipts/NAME.log is
the output of each admission. No receipt names a source this change edits.

The canonical database keeps every earlier event and gains 55. The three new
modules enter the inventory as source_only: no kernel receipt is recorded for
them here. Claims C-1539 and C-1721 are untouched; their transition is
gororoba-open issue 277.

After the renewal "provenance export-control-plane" regenerates docs/THEOREMS.md
and docs/generated/THEOREMS_REGISTRY_MIRROR.md (350 proof files), "make
registry-integrity" leaves its two files unchanged, and "make
validate-registry-control-plane" exits 0 (control-plane-after.txt).

Reproduction: build gororoba-db (cargo build --release -p gororoba_db --bin
gororoba-db), then sh renew_receipts.sh PATH/TO/gororoba-db from the checkout.
A rerun keeps the specifications, so stored events replay exactly.
