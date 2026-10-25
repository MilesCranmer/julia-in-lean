#!/bin/bash
# Validate bugs/*.yaml (plain Python with PyYAML via uv; needs neither Julia nor Lean).
exec uv run --no-project --quiet --with pyyaml python "$(dirname "${BASH_SOURCE[0]}")/check_bugs.py"
