"""Validate bugs/*.yaml and check that each bug has a reproducer."""

import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
PRIORITIES = {"P0", "P1", "P2", "P3"}
KINDS = {"wrong-result", "wrong-exception", "missing-error", "crash", "hang", "documentation", "model-counterexample"}
TEXT = ["title", "area", "summary", "likelihood", "maybe_intended", "reproducer",
        "expected", "promised_by", "cause", "possible_fix"]


def declared_theorems() -> set[str]:
    decl = re.compile(r"^\s*(?:private\s+|protected\s+)?theorem\s+([^\s:({\[]+)", re.M)
    return {name.rsplit(".", 1)[-1]
            for f in (ROOT / "JuliaLean").rglob("*.lean")
            for name in decl.findall(f.read_text(errors="ignore"))}


def registered_todo_properties() -> set[tuple[str, str]]:
    registry = (ROOT / "JuliaLean/Registry.lean").read_text()
    groups = re.findall(r"\+\+\s+(JuliaLean\.[\w.]+)", registry)
    imports = re.findall(r"^import\s+([\w.]+)", registry, re.M)
    pending = set()
    for module in imports:
        path = ROOT / (module.replace(".", "/") + ".lean")
        if not path.exists():
            continue
        text = path.read_text()
        namespaces = set(re.findall(r"^namespace\s+([\w.]+)\s*$", text, re.M))
        for group in groups:
            namespace, name = group.rsplit(".", 1)
            if namespace not in namespaces:
                continue
            scope = re.search(rf"^namespace\s+{re.escape(namespace)}\s*$\n(.*?)^end\s+{re.escape(namespace)}\s*$",
                              text, re.M | re.S)
            if scope is None:
                continue
            declaration = re.search(
                rf"\bdef\s+{re.escape(name)}\s*:\s*List\s+(?:JuliaLean\.Registry\.)?Entry\s*:=\s*\[(.*?)^\]",
                scope[1], re.M | re.S)
            if declaration is None:
                continue
            for entry in re.split(r"\n\s*(?=\{\s*id\s*:=)", declaration[1]):
                identifier = re.search(r'\bid\s*:=\s*"([^"]+)"', entry)
                prop = re.search(r"\bprop\s*:=\s*``(JuliaLean\.[\w.]+)", entry)
                if identifier and prop and re.search(r"\bstatus\s*:=\s*\.todo\b", entry):
                    pending.add((identifier[1], prop[1]))
    return pending

def check(path: Path, theorems: set[str], warnings: list[str],
          pending: set[tuple[str, str]]) -> list[str]:
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
    pending_proof = (isinstance(lean, dict) and lean.get("theorem") == ""
                     and isinstance(lean.get("property"), str)
                     and (path.stem, lean.get("property")) in pending
                     and isinstance(lean.get("notes"), str) and bool(lean["notes"].strip()))
    if (bug.get("kind") != "model-counterexample"
            and isinstance(reproduced, dict) and reproduced.get("nightly") is True
            and isinstance(lean, dict) and isinstance(lean.get("theorem"), str)
            and lean["theorem"].rsplit(".", 1)[-1] not in theorems and not pending_proof):
        warnings.append(f"{path.name}: lean.theorem {lean['theorem']} is not declared in JuliaLean")
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
    files = sorted((ROOT / "bugs").glob("*.yaml"))
    theorems = declared_theorems()
    pending = registered_todo_properties()
    warnings = []
    problems = [p for f in files for p in check(f, theorems, warnings, pending)]
    for p in problems:
        print(p)
    for warning in warnings:
        print(f"WARNING {warning}")
    print(f"BUGS {len(files)} PROBLEMS {len(problems)}")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
