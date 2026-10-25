"""Validate bugs/*.yaml against the schema in ARCHITECTURE.md.

Also checks that every refuted id in registry.tsv (when present) has a bug file
and a reproducer. Prints one line per problem and exits nonzero on any.
"""

import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
PRIORITIES = {"P0", "P1", "P2", "P3"}
KINDS = {"wrong-result", "wrong-exception", "missing-error", "crash", "hang", "documentation"}
TEXT = ["title", "area", "summary", "likelihood", "maybe_intended", "reproducer",
        "expected", "promised_by", "cause", "possible_fix"]


def check(path: Path) -> list[str]:
    try:
        bug = yaml.safe_load(path.read_text())
    except yaml.YAMLError as err:
        return [f"{path.name}: invalid YAML: {err}"]
    if not isinstance(bug, dict):
        return [f"{path.name}: top level is not a mapping"]
    problems = []

    def need(cond: bool, msg: str) -> None:
        if not cond:
            problems.append(f"{path.name}: {msg}")

    need(bug.get("id") == path.stem, f"id {bug.get('id')!r} does not match the file name")
    need(bug.get("priority") in PRIORITIES, f"priority {bug.get('priority')!r} not in {sorted(PRIORITIES)}")
    need(bug.get("kind") in KINDS, f"kind {bug.get('kind')!r} not in {sorted(KINDS)}")
    for key in TEXT:
        need(isinstance(bug.get(key), str), f"{key} missing or not a string")
    for key in ["files", "functions"]:
        need(isinstance(bug.get(key), list) and bug[key], f"{key} missing or empty list")
    output, reproduced = bug.get("output"), bug.get("reproduced")
    for version in ["release", "nightly"]:
        need(isinstance(output, dict) and isinstance(output.get(version), str),
             f"output.{version} missing")
        need(isinstance(reproduced, dict) and isinstance(reproduced.get(version), bool),
             f"reproduced.{version} missing or not a bool")
    dups = bug.get("duplicates")
    need(isinstance(dups, dict) and isinstance(dups.get("issues"), list)
         and isinstance(dups.get("queries"), list) and dups["queries"],
         "duplicates needs issues (list) and non-empty queries (list)")
    if isinstance(dups, dict):
        for issue in dups.get("issues") or []:
            need(isinstance(issue, dict) and isinstance(issue.get("number"), int)
                 and issue.get("relation") in {"duplicate", "related"},
                 f"bad duplicates.issues entry {issue!r}")
    lean = bug.get("lean")
    need(isinstance(lean, dict) and isinstance(lean.get("property"), str)
         and isinstance(lean.get("theorem"), str), "lean.property and lean.theorem required")
    unknown = set(bug) - set(TEXT) - {"id", "priority", "kind", "files", "functions",
                                      "output", "reproduced", "duplicates", "lean"}
    need(not unknown, f"unknown keys {sorted(unknown)}")
    need((ROOT / "repro" / f"{path.stem}.jl").exists(), f"missing repro/{path.stem}.jl")
    return problems


def main() -> int:
    files = sorted((ROOT / "bugs").glob("*.yaml"))
    problems = [p for f in files for p in check(f)]
    registry = ROOT / "registry.tsv"
    if registry.exists():
        have = {f.stem for f in files}
        for line in registry.read_text().splitlines():
            cols = line.split("\t")
            if len(cols) > 1 and cols[1] == "refuted" and cols[0] not in have:
                problems.append(f"{cols[0]}: refuted in registry.tsv but no bugs/{cols[0]}.yaml")
    for p in problems:
        print(p)
    print(f"BUGS {len(files)} PROBLEMS {len(problems)}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
