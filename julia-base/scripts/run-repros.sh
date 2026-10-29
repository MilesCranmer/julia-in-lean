#!/usr/bin/env bash
# Run the reproducer of every refuted registry entry with one Julia binary.
#
#   JULIA=/path/to/julia scripts/run-repros.sh      (default: julia on PATH)
#
# Reads the `REFUTED <id>` lines that scripts/audit.sh writes to .lake/audit.out,
# runs repro/<target>.jl for each, where scripts/repro-target.sh names the target
# (the id itself, or the bug whose `covers` list names it), and prints
# `<id> REPRODUCED` when the output contains the line `REPRODUCED <target>`, else
# `<id> not-reproduced`. Ends with `REPROS <n> FAILURES <k>` and exits nonzero
# when any reproducer failed.
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
    if target=$(bash scripts/repro-target.sh "$id") &&
        grep -qx "REPRODUCED $target" <<<"$("$JULIA" --startup-file=no --history-file=no "repro/$target.jl" </dev/null 2>&1)"; then
        echo "$id REPRODUCED"
    else
        echo "$id not-reproduced"
        failures=$((failures + 1))
    fi
done < <(sed -n 's/^REFUTED //p' .lake/audit.out)

echo "REPROS $count FAILURES $failures"
[[ $failures -eq 0 ]]
