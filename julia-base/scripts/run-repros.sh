#!/usr/bin/env bash
# Run the reproducer of every refuted registry entry with one Julia binary.
#
#   JULIA=/path/to/julia scripts/run-repros.sh      (default: julia on PATH)
#
# Reads the `REFUTED <id>` lines that scripts/audit.sh writes to .lake/audit.out,
# runs repro/<id>.jl for each, and prints `<id> REPRODUCED` when the output
# contains the line `REPRODUCED <id>`, else `<id> not-reproduced`. Ends with
# `REPROS <n> FAILURES <k>` and exits nonzero when any reproducer failed.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
JULIA=${JULIA:-julia}

if [[ ! -s .lake/audit.out ]]; then
    echo "FAIL missing .lake/audit.out; run scripts/audit.sh first" >&2
    exit 1
fi

count=0 failures=0
while read -r id; do
    count=$((count + 1))
    if [[ -f repro/$id.jl ]] &&
        grep -qx "REPRODUCED $id" <<<"$("$JULIA" --startup-file=no --history-file=no "repro/$id.jl" </dev/null 2>&1)"; then
        echo "$id REPRODUCED"
    else
        echo "$id not-reproduced"
        failures=$((failures + 1))
    fi
done < <(sed -n 's/^REFUTED //p' .lake/audit.out)

echo "REPROS $count FAILURES $failures"
[[ $failures -eq 0 ]]
