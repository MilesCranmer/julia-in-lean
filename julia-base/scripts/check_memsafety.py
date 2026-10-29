"""Validate the pinned unchecked-access inventory against source and registry."""

import argparse
import csv
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE_COMMIT = "f755f49a9e41380d7da126b3c1db9fe7f83dd027"
KEYWORDS = ("@inbounds", "@boundscheck", "unsafe_load", "unsafe_store!",
            "unsafe_copyto!", "unsafe_wrap", "memoryref")
PROOF_STATUSES = {"proven", "refuted"}
NOTE_STATUSES = {"user-contract", "not-unchecked"}


def row_problems(row, registry, reviews=None):
    status = row["status"]
    if status in PROOF_STATUSES:
        entries = [e for e in row["entry"].split(",") if e]
        if not entries:
            return [f"{row['site']}: {status} without entry"]
        problems = [f"{row['site']}: entry {e} is {registry.get(e, 'missing')} in registry.tsv, not {status}"
                    for e in entries if registry.get(e) != status]
        if status == "proven" and reviews is not None:
            problems += [f"{row['site']}: entry {e} lacks FAITHFUL review"
                         for e in entries if reviews.get((row["group"], e)) != "FAITHFUL"]
        return problems
    if status in NOTE_STATUSES:
        return [] if row["note"].strip() else [f"{row['site']}: {status} without note"]
    if status == "todo":
        return [] if not row["entry"] else [f"{row['site']}: todo with entry"]
    return [f"{row['site']}: unknown status {status!r}"]


def source_sites(repo, commit):
    pattern = "|".join(re.escape(keyword) for keyword in KEYWORDS)
    result = subprocess.run(["git", "grep", "-n", "-E", pattern, commit, "--", "base/*.jl"],
                            cwd=repo, text=True, capture_output=True)
    if result.returncode not in (0, 1):
        raise ValueError(f"cannot scan pinned Julia source: {result.stderr.strip()}")
    sites = {}
    for line in result.stdout.splitlines():
        match = re.match(r"^[^:]+:(base/.*\.jl):(\d+):(.*)$", line)
        if not match:
            raise ValueError(f"invalid git grep output: {line}")
        file, number, code = match.groups()
        if code.lstrip().startswith("#"):
            continue
        code = code.strip()
        sites[(file, number)] = ("+".join(k for k in KEYWORDS if k in code), code)
    return sites


def inventory_problems(rows, source):
    problems = []
    seen = set()
    for row in rows:
        key = (row["file"], row["line"])
        if key in seen:
            problems.append(f"{row['site']}: duplicate source location")
        seen.add(key)
        expected_id = row["file"].removeprefix("base/").removesuffix(".jl").replace("/", ".") + ":" + row["line"]
        if row["site"] != expected_id:
            problems.append(f"{row['site']}: incorrect site id")
        actual = source.get(key)
        if actual is None:
            problems.append(f"{row['site']}: absent from pinned source scan")
        elif (row["kind"], row["code"]) != actual:
            problems.append(f"{row['site']}: kind or code differs from pinned source")
    for file, line in sorted(source.keys() - seen):
        problems.append(f"{file}:{line}: missing from inventory")
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT.parent / "julia",
                        help="Julia Git repository containing the pinned source commit")
    args = parser.parse_args()
    pin = ROOT / "memsafety" / "SOURCE_COMMIT"
    if not pin.is_file() or pin.read_text().strip() != SOURCE_COMMIT:
        print("PROBLEM missing or incorrect memsafety/SOURCE_COMMIT")
        return 1
    registry = {}
    for line in (ROOT / "registry.tsv").read_text().splitlines():
        fields = line.split("\t")
        if len(fields) >= 2:
            registry[fields[0]] = fields[1]
    rows = []
    reviews = {}
    for path in sorted((ROOT / "memsafety").glob("sites-*.tsv")):
        group = path.stem.removeprefix("sites-")
        with path.open(newline="") as stream:
            for row in csv.DictReader(stream, delimiter="\t"):
                if row["group"] != group:
                    print(f"PROBLEM {row['site']}: wrong group")
                    return 1
                rows.append(row)
        review = path.with_name(f"review-{group}.tsv")
        if review.exists():
            with review.open(newline="") as stream:
                for row in csv.DictReader(stream, delimiter="\t"):
                    reviews[(group, row["entry"])] = row["verdict"]
    try:
        source = source_sites(args.repo, SOURCE_COMMIT)
    except (OSError, ValueError) as error:
        print(f"PROBLEM {error}")
        return 1
    problems = inventory_problems(rows, source)
    problems += [p for row in rows for p in row_problems(row, registry, reviews)]
    counts = Counter(row["status"] for row in rows)
    for problem in problems:
        print(problem)
    for group in sorted({row["group"] for row in rows}):
        group_counts = Counter(row["status"] for row in rows if row["group"] == group)
        print(f"GROUP {group} " + " ".join(f"{k}={v}" for k, v in sorted(group_counts.items())))
    print(f"SITES {len(rows)} " + " ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    print(f"PROBLEMS {len(problems)}")
    return 1 if problems or counts["todo"] else 0


if __name__ == "__main__":
    sys.exit(main())
