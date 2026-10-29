"""Validate bugs/*.yaml against the schema in ARCHITECTURE.md.

Also checks that every refuted id in registry.tsv (when present) has a bug file
and a reproducer. Prints one line per problem and exits nonzero on any.
"""

import argparse
import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
PRIORITIES = {"P0", "P1", "P2", "P3"}
KINDS = {"wrong-result", "wrong-exception", "missing-error", "crash", "hang", "documentation", "model-counterexample"}
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
    if bug.get("kind") == "model-counterexample":
        need(isinstance(reproduced, dict) and reproduced.get("release") is False
             and reproduced.get("nightly") is False,
             "model-counterexample requires reproduced.release and reproduced.nightly to be false")
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
    covers = bug.get("covers", [])
    need(isinstance(covers, list) and all(isinstance(c, str) for c in covers),
         "covers must be a list of registry ids")
    if "current" in bug:
        current = bug["current"]
        need(isinstance(current, dict), "current must be a mapping")
        if isinstance(current, dict):
            need(bool(re.fullmatch(r"[0-9a-f]{40}", current.get("commit", "") if isinstance(current.get("commit"), str) else "")),
                 "current.commit must be a full lowercase commit SHA")
            need(isinstance(current.get("reproduced"), bool), "current.reproduced must be a bool")
            need(isinstance(current.get("output"), str), "current.output must be a string")
            if current.get("reproduced") is False:
                need(isinstance(current.get("proof"), str) and bool(current["proof"].strip()),
                     "current.proof required when not reproduced")
            if "proof" in current:
                need(isinstance(current["proof"], str) and bool(current["proof"].strip()),
                     "current.proof must be a nonempty string")
            need(not (set(current) - {"commit", "reproduced", "output", "proof"}),
                 "current has unknown keys")
    unknown = set(bug) - set(TEXT) - {"id", "priority", "kind", "files", "functions",
                                      "output", "reproduced", "duplicates", "lean", "covers", "current"}
    need(not unknown, f"unknown keys {sorted(unknown)}")
    need((ROOT / "repro" / f"{path.stem}.jl").exists(), f"missing repro/{path.stem}.jl")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cruntime-refuted-id", action="append", default=[], metavar="ID")
    args = parser.parse_args()

    files = sorted((ROOT / "bugs").glob("*.yaml"))
    problems = [p for f in files for p in check(f)]
    for bug_id in args.cruntime_refuted_id:
        if not (ROOT / "bugs" / f"{bug_id}.yaml").is_file():
            problems.append(f"{bug_id}: missing bugs/{bug_id}.yaml")
        if not (ROOT / "repro" / f"{bug_id}.jl").is_file():
            problems.append(f"{bug_id}: missing repro/{bug_id}.jl")
    registry = ROOT / "registry.tsv"
    if registry.exists():
        have = {f.stem for f in files}
        for f in files:
            covers = (yaml.safe_load(f.read_text()) or {}).get("covers") or []
            have.update(c for c in covers if isinstance(c, str))
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
