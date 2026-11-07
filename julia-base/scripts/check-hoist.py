#!/usr/bin/env python3
"""Reject model lines that put a monadic action to the right of `&&` or `||`.

Lean's do-notation runs every nested `(← e)` before the statement that contains it,
so in `if guard && (← f x) then` the call `f x` runs even when `guard` is false.
Julia's `&&`/`||` short-circuit, so the model must use `<&&>`/`<||>` instead.

Lines already in scripts/hoist-baseline.txt are known defects awaiting a fix; the
check fails on any other occurrence, and on baseline entries that no longer occur
(delete them from the baseline once fixed).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BASELINE = ROOT / "scripts" / "hoist-baseline.txt"
PATTERN = re.compile(r"(?<!<)(&&|\|\|)(?!>)[^-]*\(← ")


def occurrences() -> set[str]:
    found = set()
    for top in ("JuliaLean/base", "JuliaLean/stdlib"):
        for path in sorted((ROOT / top).rglob("*.lean")):
            name = path.relative_to(ROOT).as_posix()
            for line in path.read_text().splitlines():
                code = line.split("--", 1)[0]
                if PATTERN.search(code):
                    found.add(f"{name}\t{line.strip()}")
    return found


def main() -> int:
    baseline = set(BASELINE.read_text().splitlines()) if BASELINE.exists() else set()
    found = occurrences()
    new = sorted(found - baseline)
    fixed = sorted(baseline - found)
    for entry in new:
        print("HOIST", entry.replace("\t", ": ", 1))
    for entry in fixed:
        print("HOIST-FIXED (remove from baseline)", entry.replace("\t", ": ", 1))
    print(f"HOIST {len(found)} known {len(baseline)} new {len(new)} stale {len(fixed)}")
    return 1 if new or fixed else 0


if __name__ == "__main__":
    sys.exit(main())
