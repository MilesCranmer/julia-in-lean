#!/bin/bash
# Validate bugs/*.yaml (runs on the Mac; plain Python, no Julia or Lean).
exec uv run --no-project --quiet --with pyyaml python "$(dirname "${BASH_SOURCE[0]}")/check_bugs.py" "$@"
