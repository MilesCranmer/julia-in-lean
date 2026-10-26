#!/usr/bin/env bash
# Build the Lean project, reject forbidden proof escapes, and audit the registry.
# Run from the package root. Writes .lake/audit.out.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

lake build

if grep -rnwE 'sorry|admit|native_decide|bv_decide|ofReduceBool' --include='*.lean' JuliaLean JuliaLean.lean; then
    echo "FAIL forbidden proof escape found (see lines above)"
    exit 1
fi

lake env lean Audit.lean | tee .lake/audit.out
