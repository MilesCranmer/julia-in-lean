"""Validate memsafety/sites-*.tsv against registry.tsv.

Every unchecked-access site in base/ has one row. A row is settled when its
status is `proven` or `refuted` and `entry` names registry entries with that
status, or when its status is `user-contract` or `not-unchecked` and `note`
says why. Prints one line per problem, then a summary, and exits nonzero if
any row is unsettled or inconsistent.
"""

import csv
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROOF_STATUSES = {"proven", "refuted"}
NOTE_STATUSES = {"user-contract", "not-unchecked"}


def row_problems(row: dict, registry: dict) -> list[str]:
    status = row["status"]
    if status in PROOF_STATUSES:
        entries = [e for e in row["entry"].split(",") if e]
        if not entries:
            return [f"{row['site']}: {status} without entry"]
        return [
            f"{row['site']}: entry {e} is {registry.get(e, 'missing')} in registry.tsv, not {status}"
            for e in entries
            if registry.get(e) != status
        ]
    if status in NOTE_STATUSES:
        return [] if row["note"].strip() else [f"{row['site']}: {status} without note"]
    if status == "todo":
        return []
    return [f"{row['site']}: unknown status {status!r}"]


def main() -> int:
    registry = {}
    for line in (ROOT / "registry.tsv").read_text().splitlines():
        fields = line.split("\t")
        if len(fields) >= 2:
            registry[fields[0]] = fields[1]
    rows = []
    for path in sorted((ROOT / "memsafety").glob("sites-*.tsv")):
        with open(path, newline="") as fh:
            rows.extend(csv.DictReader(fh, delimiter="\t"))
    problems = [p for row in rows for p in row_problems(row, registry)]
    counts = Counter(row["status"] for row in rows)
    todo_by_group = Counter(row["group"] for row in rows if row["status"] == "todo")
    for p in problems:
        print(p)
    todo = ", ".join(f"group {g}: {n}" for g, n in sorted(todo_by_group.items()))
    print(f"SITES {len(rows)} " + " ".join(f"{k}={v}" for k, v in sorted(counts.items())) + (f" (todo {todo})" if todo else ""))
    print(f"PROBLEMS {len(problems)}")
    return 1 if problems or counts["todo"] else 0


if __name__ == "__main__":
    sys.exit(main())
