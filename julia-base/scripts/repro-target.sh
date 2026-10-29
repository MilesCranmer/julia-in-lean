#!/usr/bin/env bash
# Print the reproducer that confirms refuted registry entry ID, relative to the
# repository root in the current directory:
#
#   scripts/repro-target.sh ID
#
# Prints ID when repro/ID.jl exists. Otherwise prints BUG when bugs/BUG.yaml is
# the one bug file whose `covers` list names ID and repro/BUG.jl exists. The
# caller runs repro/<printed>.jl and requires the line `REPRODUCED <printed>`.
# Exits 1 with a message when no reproducer, or more than one covering bug, exists.
set -euo pipefail
id=${1:?usage: repro-target.sh ID}

if [[ -f repro/$id.jl ]]; then
    echo "$id"
    exit 0
fi

covering=()
for bug in bugs/*.yaml; do
    [[ -f $bug ]] || continue
    # `covers:` holds a flow list (`[a, b]`, possibly over several lines) or a block list.
    if awk -v id="$id" '
        function check(s,   n, a, i) {
            gsub(/[][,"]/, " ", s); gsub(/\047/, " ", s)
            n = split(s, a, /[ \t]+/)
            for (i = 1; i <= n; i++) if (a[i] == id) hit = 1
        }
        mode == "flow" { check($0); if ($0 ~ /\]/) mode = ""; next }
        mode == "block" {
            if ($0 ~ /^[ \t]*-[ \t]/) { s = $0; sub(/^[ \t]*-[ \t]*/, "", s); check(s); next }
            mode = ""
        }
        /^covers:/ {
            s = $0; sub(/^covers:[ \t]*/, "", s); sub(/[ \t]*#.*$/, "", s)
            if (s == "") mode = "block"
            else { check(s); if (s ~ /^\[/ && s !~ /\]/) mode = "flow" }
        }
        END { exit !hit }' "$bug"; then
        covering+=("$(basename "$bug" .yaml)")
    fi
done

if ((${#covering[@]} == 0)); then
    echo "missing reproducer repro/$id.jl and no bugs/*.yaml covers $id" >&2
    exit 1
fi
if ((${#covering[@]} > 1)); then
    echo "$id is covered by more than one bug: ${covering[*]}" >&2
    exit 1
fi
if [[ ! -f repro/${covering[0]}.jl ]]; then
    echo "$id is covered by ${covering[0]}, which has no repro/${covering[0]}.jl" >&2
    exit 1
fi
echo "${covering[0]}"
