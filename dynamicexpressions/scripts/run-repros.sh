#!/usr/bin/env bash
# Run the Julia reproducer of every refuted registry entry, after scripts/audit.sh
# has written .lake/audit.out.
#
#   JULIA=/path/to/julia scripts/run-repros.sh      (default: julia on PATH)
#
# Convention: repro/<id>.jl prints the line `REPRODUCED <id>` when the bug shows
# on the DynamicExpressions.jl source pinned in repro/Project.toml, and anything
# else otherwise.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
JULIA=${JULIA:-julia}

AUDIT_OUT=.lake/audit.out
test -s "$AUDIT_OUT" || { echo "FAIL missing $AUDIT_OUT; run scripts/audit.sh first"; exit 1; }

"$JULIA" --project=repro -e 'using Pkg; Pkg.instantiate(); using DynamicExpressions' >/dev/null

failures=0
count=0
while read -r id; do
    count=$((count + 1))
    script="repro/$id.jl"
    if [[ ! -f "$script" ]]; then
        echo "FAIL $id: missing $script"
        failures=$((failures + 1))
        continue
    fi
    out="$("$JULIA" --project=repro "$script" </dev/null 2>&1 || true)"
    if grep -qx "REPRODUCED $id" <<<"$out"; then
        echo "OK $id"
    else
        echo "FAIL $id: reproducer did not print 'REPRODUCED $id'"
        sed 's/^/    /' <<<"$out" | tail -20
        failures=$((failures + 1))
    fi
done < <(sed -n 's/^REFUTED //p' "$AUDIT_OUT")

echo "REPROS $count FAILURES $failures"
[[ $failures -eq 0 ]]
