#!/usr/bin/env bash
# Build the Lean project, reject forbidden proof escapes, and audit the C runtime
# and Base registries.
# Run from the package root. Writes .lake/audit.out.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

python3 scripts/check-hoist.py

LEAN_NUM_THREADS=2 lake build JuliaLean JuliaLean.Registry.Audit

python3 scripts/check-proof-escapes.py

lake env lean CRuntimeAudit.lean
lake env lean Audit.lean | tee .lake/audit.out
