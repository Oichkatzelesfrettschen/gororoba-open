#!/bin/sh
# Renew the kernel-checked theorem receipts after a change of proofs/_RocqProject: synchronize the proof
# inventory at the new project digest, then replay every receipt of the previous renewal against it.
# Usage: renew_receipts.sh GOROROBA_DB, run from any directory of the checkout; GOROROBA_DB is the built
# gororoba-db executable. A rerun keeps existing specifications, so stored events replay exactly.
set -eu

if [ "$#" -ne 1 ]; then
    printf '%s\n' 'usage: renew_receipts.sh GOROROBA_DB' >&2
    exit 2
fi
db=$1
root=$(git rev-parse --show-toplevel)
cd "$root"
audit=data/output/audit/moreno-kernel-equality-tower-swap
previous=data/output/audit/vacuum-composition/main-integration/receipts
database=registry/canonical/control_plane.sqlite3
actor=claude-code
project=$(sha256sum proofs/_RocqProject | cut -d' ' -f1)
short=$(printf '%s' "$project" | cut -c1-12)
mkdir -p "$audit/receipts"

if [ ! -f "$audit/inventory.toml" ]; then
    applied=$(date -u +%Y-%m-%dT%H:%M:%SZ)
    {
        printf 'sync_key = "moreno-kernel-swap-inventory-%s"\n' "$project"
        printf 'actor = "%s"\n' "$actor"
        printf 'reason = "Admit CDTowerKernelSwap, MorenoTowerInstance and MorenoSwapIndependence to the proof inventory and preserve append-only canonical history."\n'
        printf 'applied_at = "%s"\n' "$applied"
        printf 'project_sha256 = "%s"\n' "$project"
    } > "$audit/inventory.toml"
fi
applied=$(sed -n 's/^applied_at = "\(.*\)"$/\1/p' "$audit/inventory.toml")
"$db" theorem identity sync-inventory --spec "$audit/inventory.toml" --regen-toml false > "$audit/inventory.log"

total=0
failed=0
for historical in "$previous"/*.receipt.toml; do
    name=$(basename "$historical" .receipt.toml)
    case $name in
    *[!A-Za-z0-9_]*)
        printf 'unexpected receipt name %s\n' "$name" >&2
        exit 1
        ;;
    esac
    total=$((total + 1))
    spec="$audit/receipts/$name.receipt.toml"
    if [ ! -f "$spec" ]; then
        prestate=$(sqlite3 -readonly "$database" \
            "SELECT hex(kernel_result) FROM theorem_identities WHERE stable_id='THM-LEGACY-$name'" |
            xxd -r -p | sha256sum | cut -d' ' -f1)
        {
            printf 'evidence_key = "moreno-kernel-swap-replay-%s-%s"\n' "$name" "$short"
            printf 'actor = "%s"\n' "$actor"
            printf 'reason = "Replay retained source, objects and declaration assumptions against the proof project that lists the tower kernel swap."\n'
            printf 'applied_at = "%s"\n' "$applied"
            printf 'expected_kernel_result_sha256 = "%s"\n' "$prestate"
            printf 'expected_status = "source_only"\n\n'
            sed -n '/^\[witness\]$/,$p' "$historical" |
                sed "s/^project_sha256 = .*/project_sha256 = \"$project\"/"
        } > "$spec"
    fi
    status=0
    opam exec --switch=rocq-9.3 -- "$db" theorem identity record-kernel-evidence --spec "$spec" \
        --regen-toml false > "$audit/receipts/$name.log" 2>&1 || status=$?
    printf '%s/%s %s exit %s\n' "$total" "$(find "$previous" -name '*.receipt.toml' | wc -l)" "$name" "$status"
    if [ "$status" -ne 0 ]; then
        failed=$((failed + 1))
    fi
done
printf 'receipts=%s failed=%s project=%s\n' "$total" "$failed" "$project"
[ "$failed" -eq 0 ]
