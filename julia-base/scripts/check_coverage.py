"""Validate coverage/methods/*.tsv against registry.tsv; exit 1 while todo remains.

Use --prefill <metadata.tsv> with tab-separated id, file, and function rows to
settle only unique same-file name/signature matches. Ambiguous entries remain
as candidates in their notes.
"""

import argparse
import csv
import functools
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIELDS = ["file", "line", "endline", "name", "signature", "status", "entry", "note"]
EXCLUSION_REASONS = ("no-behaviour:", "deprecated:", "internal-bootstrap:", "platform:")


def read_registry(path):
    """Entries from registry.tsv."""
    registry = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        fields = line.split("\t")
        if len(fields) < 4 or fields[0] in registry:
            raise ValueError(f"{path}:{number}: malformed or duplicate registry entry")
        registry[fields[0]] = {"status": fields[1], "file": fields[3]}
    return registry


def row_problems(row, registry):
    problems = []
    try:
        if not 1 <= int(row["line"]) <= int(row["endline"]):
            raise ValueError()
    except ValueError:
        problems.append("invalid line span")
    if not row["file"].startswith("base/") or not row["file"].endswith(".jl"):
        problems.append("invalid Base source path")
    if not row["name"].strip() or not row["signature"].strip():
        problems.append("empty name or signature")
    if any("\n" in value or "\r" in value for value in row.values()):
        problems.append("multiline field")
    status = row["status"]
    entries = row["entry"].split(",") if row["entry"] else []
    if status == "modelled":
        if not entries:
            problems.append("modelled without entry")
        if len(set(entries)) != len(entries):
            problems.append("duplicate entry id")
        for entry in entries:
            registered = registry.get(entry)
            if registered is None:
                problems.append(f"missing registry id {entry}")
            elif registered["status"] not in {"proven", "refuted"}:
                problems.append(f"registry id {entry} is {registered['status']}")
            elif registered["file"] != row["file"]:
                problems.append(f"registry id {entry} belongs to {registered['file']}")
    elif status == "excluded":
        if not any(row["note"].startswith(reason) and row["note"][len(reason):].strip()
                   for reason in EXCLUSION_REASONS):
            problems.append("excluded without allowed reason and justification")
        if entries:
            problems.append("excluded with entry")
    elif status == "todo":
        if entries:
            problems.append("todo with entry")
    else:
        problems.append(f"unknown status {status!r}")
    return problems


def plain_name(name):
    name = re.sub(r"\s+", "", name)
    name = re.sub(r"(?:\b\w+\.)+", "", name)
    return name.removeprefix(":").strip("()")


def signature_types(signature):
    # Keep complete nested type expressions; partial names could settle the wrong method.
    types = []
    for annotation in re.finditer(r"::\s*", signature):
        start = annotation.end()
        end = start
        depth = 0
        quoted = False
        escaped = False
        while end < len(signature):
            char = signature[end]
            if quoted:
                if char == '"' and not escaped:
                    quoted = False
                escaped = char == "\\" and not escaped
            elif char == '"':
                quoted = True
            elif char in "{([":
                depth += 1
            elif char in "})]":
                if depth == 0:
                    break
                depth -= 1
            elif depth == 0 and not (char.isalnum() or char in "_.@"):
                break
            end += 1
        types.append(re.sub(r"\s+", "", signature[start:end]))
    return types


def prefill(rows, metadata, registry):
    by_name = defaultdict(list)
    for row in rows:
        by_name[row["file"], plain_name(row["name"])].append(row)
    settled = defaultdict(set)
    candidates = defaultdict(set)
    for entry, file, fn in metadata:
        registered = registry.get(entry)
        if not registered or registered["status"] not in {"proven", "refuted"} or registered["file"] != file:
            continue
        name = plain_name(fn.split("(", 1)[0])
        matching = by_name.get((file, name), [])
        if "(" in fn and len(matching) > 1:
            types = signature_types(fn)
            matching = [row for row in matching
                        if signature_types(row["signature"]) == types]
        if len(matching) == 1:
            settled[id(matching[0])].add(entry)
        elif matching:
            for row in matching:
                candidates[id(row)].add(entry)
    for row in rows:
        if row["status"] != "todo":
            continue
        if settled[id(row)]:
            row["status"] = "modelled"
            row["entry"] = ",".join(sorted(settled[id(row)]))
        elif candidates[id(row)]:
            note = "candidates:" + ",".join(sorted(candidates[id(row)]))
            row["note"] = "; ".join(filter(None, [row["note"], note]))


def manifest_name(file):
    if (not file.startswith("base/") or not file.endswith(".jl") or
            any(part in {"", ".", ".."} for part in file.split("/")) or "\\" in file):
        raise ValueError(f"invalid Base source path {file!r}")
    return file[5:-3].replace("/", "__") + ".tsv"


def load_review(path):
    """Verdicts from coverage/review/<file>.tsv, written by the fixed REVIEW_PROMPT.md reviewer."""
    review = path.parent.parent / "review" / path.name
    if not review.exists():
        return {}
    with review.open(newline="") as fh:
        return {(r["line"], r["name"]): (r["verdict"], r["reason"]) for r in csv.DictReader(fh, delimiter="\t")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", help="Base paths to check; default: every manifest")
    parser.add_argument("--manifest-dir", type=Path, default=ROOT / "coverage/methods")
    parser.add_argument("--registry", type=Path, default=ROOT / "registry.tsv")
    parser.add_argument("--prefill", type=Path)
    args = parser.parse_args()
    try:
        registry = read_registry(args.registry)
        paths = ([args.manifest_dir / manifest_name(file) for file in sorted(set(args.files))]
                 if args.files else sorted(args.manifest_dir.glob("*.tsv")))
        if not paths:
            raise ValueError(f"{args.manifest_dir}: no coverage manifests")
        manifests = {}
        located_rows = []
        malformed = []
        for path in paths:
            with path.open(newline="") as fh:
                reader = csv.DictReader(fh, delimiter="\t")
                if reader.fieldnames != FIELDS:
                    raise ValueError(f"{path}: expected columns {FIELDS}")
                file_rows = list(reader)
            manifests[path] = file_rows
            for number, row in enumerate(file_rows, 2):
                if None in row or any(v is None for v in row.values()):
                    malformed.append(f"{path}:{number}: malformed row (expected {len(FIELDS)} tab-separated fields)")
                else:
                    located_rows.append((path, number, row))
        rows = [row for _, _, row in located_rows]
        if args.prefill:
            with args.prefill.open(newline="") as fh:
                metadata = list(csv.reader(fh, delimiter="\t"))
            if any(len(row) != 3 for row in metadata):
                raise ValueError("prefill metadata must have id, file, function columns")
            prefill(rows, metadata, registry)
            for path, file_rows in manifests.items():
                with path.open("w", newline="") as fh:
                    writer = csv.DictWriter(fh, FIELDS, delimiter="\t", lineterminator="\n")
                    writer.writeheader()
                    writer.writerows(file_rows)
            print(f"PREFILLED {sum(row['status'] == 'modelled' for row in rows)}")
        problems = list(malformed)
        seen = set()
        per_file = defaultdict(Counter)
        for path in paths:
            per_file["base/" + path.stem.replace("__", "/") + ".jl"]
        weighted = Counter()
        review_counts = Counter()
        reviews = functools.cache(load_review)
        for path, number, row in located_rows:
            row_errors = row_problems(row, registry)
            if manifest_name(row["file"]) != path.name:
                row_errors.append("definition belongs in a different manifest")
            key = tuple(row[field] for field in FIELDS[:5])
            if key in seen:
                row_errors.append("duplicate definition")
            seen.add(key)
            problems.extend(f"{path}:{number}: {problem}" for problem in row_errors)
            per_file[row["file"]][row["status"]] += 1
            span = int(row["endline"]) - int(row["line"]) + 1
            weighted["all"] += span
            if row_errors or row["status"] == "todo":
                continue
            verdict, reason = reviews(path).get((row["line"], row["name"]), ("unreviewed", ""))
            if verdict == "HOLLOW":
                problems.append(f"{path}:{number}: review HOLLOW: {reason}")
                continue
            review_counts[verdict] += 1
            if verdict == "FAITHFUL":
                weighted[row["status"]] += span
        for problem in problems:
            print(problem)
        for file, counts in sorted(per_file.items()):
            print(file + " " + " ".join(f"{s}={counts[s]}" for s in ("modelled", "excluded", "todo")))
        counts = Counter(row["status"] for row in rows)
        print(f"METHODS {len(rows)} modelled={counts['modelled']} excluded={counts['excluded']} todo={counts['todo']}")
        print(f"REVIEWED faithful={review_counts['FAITHFUL']} unreviewed={review_counts['unreviewed']}")
        share = weighted["modelled"] / weighted["all"] if weighted["all"] else 0
        print(f"LINE COVERAGE {weighted['modelled']}/{weighted['all']} = {share:.4%} modelled and reviewed FAITHFUL (definition-span weighted; overlapping definitions counted separately)")
        print(f"PROBLEMS {len(problems)}")
        return int(bool(problems or counts["todo"] or review_counts["unreviewed"]))
    except (OSError, ValueError, csv.Error) as error:
        print(error, file=sys.stderr)
        print("PROBLEMS 1")
        return 1


if __name__ == "__main__":
    sys.exit(main())
