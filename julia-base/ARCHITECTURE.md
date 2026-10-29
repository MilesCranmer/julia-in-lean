# Lean formalization of Julia Base

Goal: find bugs in Julia by modelling parts of Base in Lean 4, stating the
properties its documentation or obvious invariants promise, and settling each
one as proven or refuted. Every refuted Base property is confirmed by a
minimal pure-Julia reproducer run against the pinned release and master.

## Pinned sources

| Name | Version | Commit |
|---|---|---|
| release | Julia 1.13.2 | `45b6d15e34b` |
| previous nightly | Julia 1.15.0-DEV.126 (master) | `bbfa0ce4150ea33f2532198cabcf319a49399360` |
| target master | Julia 1.15.0-DEV (master) | `f755f49a9e41380d7da126b3c1db9fe7f83dd027` |

The Lean model is being migrated from the previous nightly to the target master
(`git -C <julia-source-root> show f755f49a9e41380d7da126b3c1db9fe7f83dd027:base/<file>`).
The previous nightly remains the source of historical bug evidence.
Where 1.13.2 differs in a modelled function, note it in the entry's `notes`.

## Layout

- `JuliaLean/Core.lean`: shared primitives: `JlError`, `Jl α = Except JlError α`,
  the ten `BitInteger` types (`IntTy`, `JInt t`), wrapping arithmetic, the
  checked `div`/`rem` intrinsics, `convert`.
- `JuliaLean/base/<path>.lean`: the source-mirrored model of `base/<path>.jl`,
  one file per Base file, with the verbatim Julia source in comments.
- `JuliaLean/Proofs/base/<path>.lean`: the properties and proofs for that Base
  file. Each defines `JuliaLean.Proofs.base.<path>.entries`.
- `JuliaLean/<Area>.lean` and `JuliaLean/<Area>/*.lean`: the older area modules
  (`Ranges`, `IntArith`, `Sort`, ...), each defining `JuliaLean.<Area>.entries`.
  An area entry leaves its list once a proofs file keeps, replaces or retires it.
- `JuliaLean/Registry.lean`: `all` concatenates every area's and every proofs
  file's `entries`. Unsettled properties stay registered with status `todo`.
- `JuliaLean/CRuntime.lean`, `JuliaLean/CRuntime/`: C runtime protocol models.
  `JuliaLean.CRuntime.entries` is not part of `Registry.all`; `CRuntimeAudit.lean`
  audits it. `JuliaLean/src/<file>_c.lean` mirrors runtime C sources.
- `JuliaLean/Runtime/Axioms.lean`: the only place axioms may be declared.
- `Audit.lean`, `Report.lean`: registry audit and TSV report (`registry.tsv`).
  The audit prints each open entry as `TODO <id>` and counts it without failing.
- `repro/<id>.jl`: pure-Julia confirmation harness for each refuted entry;
  prints `REPRODUCED <id>` only for the qualifying outcome, anything else
  otherwise. Model counterexamples may remain non-claiming harnesses. Reproducers
  use only Julia's standard library.
  A refuted id without its own harness is confirmed by `repro/<bug>.jl` printing
  `REPRODUCED <bug>` when `bugs/<bug>.yaml` lists the id in `covers`;
  `scripts/repro-target.sh <id>` names the harness to run.
- `bugs/<id>.yaml`: one structured write-up per refuted entry (see below);
  `scripts/check-bugs.sh` validates them.
- `scripts/source_comments.py`: seed a source-only model with `seed <source> <revision>`,
  check its exact source comments with `validate <source>`, and report source changes
  with `compare <source> <revision>` (`--repo <julia-source-root>`). Seeds and
  untranslated blocks have no coverage.
- `scripts/gc/`: `build.sh` builds assertion and GC-verification builds of the
  previous nightly; `stress.sh` and `run-campaign.sh` run the seeded GC stress
  workloads in `repro/gc-stress-runtime.jl` and `repro/gc-foreign-thread.c`.

## Modelling rules

- Mirror the Julia source line by line: same branches, same order of checks,
  same intermediate types. Cite `base/<file>.jl:<line>` (master) in the
  docstring of each mirrored definition.
- A Julia exception is `.error e` in `Jl`. Model which exception type is
  thrown; message text only when a property is about it.
- Integer values are `JInt t`; wrapping happens exactly where Julia wraps.
  Use `JuliaLean.JInt` operations, never unbounded `Int` arithmetic, for
  Julia integer operations.
- Extend `Core.lean` only with Julia primitives several areas need; otherwise
  keep definitions in the area's own files.
- A property's `prop` must quantify over inputs (the audit rejects single
  worked examples). State the property as Julia promises it, with only the
  preconditions the documentation states or that are obviously required.
- A property that only restates its model (the statement is the model's own
  body, or one model set equal to another) cannot find a bug. `Restating.lean`
  lists proven entries whose conjuncts hold by definitional unfolding
  (`DEFEQ <id>`, `PARTIAL <id> k/n`, with `SAME-AREA-DEFEQ` when a model is
  equated to a model or body from the same area); run it with
  `lake env lean Restating.lean`. The list is a review aid; reviewers decide by
  reading whether the statement states a promise independently of the model;
  definitional equality alone never rejects a property.
- Refutations are theorems `¬ prop` built from a concrete counterexample,
  checked by `decide` (or `rfl`/`simp` on the concrete instance).
- Forbidden: `sorry`, `admit`, `native_decide`, `bv_decide`, `ofReduceBool`,
  new axioms outside `Runtime/Axioms.lean`. No Mathlib.

## Workflow

1. Model the functions; state the properties as registry entries (`todo`).
2. For a Base runtime candidate, write `repro/<id>.jl` and run
   `julia repro/<id>.jl` with each pinned Julia version. When it prints
   `REPRODUCED`, search JuliaLang/julia issues and PRs for a duplicate
   (`gh search issues --repo JuliaLang/julia ...`, `gh search prs ...`), write
   `bugs/<id>.yaml` (schema below), and check it with `scripts/check-bugs.sh`.
   Record the result before further modelling or proving. If the Lean
   refutation is not done yet, put its planned theorem name in `lean.theorem`.
3. Prove or refute every remaining property; for refuted entries, record
   duplicate searches in the entry's `issue` field (`"#12345"` or
   `"none found (queries: ...)"`). CRuntime model counterexamples use
   `modelCounterexample` evidence and a non-claiming Julia confirmation harness;
   they do not require a reproduced Julia outcome.
   When a contract is refuted only through an exotic input (offset axes,
   typemin/typemax, huge sizes, custom `AbstractArray` or `AbstractChar`
   types), keep that refutation and also state the same contract for the
   ordinary case (1-based `Array`s, small values, standard types) as a second
   entry, and prove or refute it. A bug on ordinary inputs is far more
   significant. The row's `entry` lists both ids. The full contract stays
   refuted and linked. A proven full contract already covers ordinary inputs
   and needs no second entry.
4. From the package root, run `bash scripts/audit.sh` (it runs `lake build`),
   then refresh the registry with
   `lake build JuliaLean.Registry.Print JuliaLean.Registry.Metadata`,
   `lake env lean Report.lean > registry.tsv` and
   `lake env lean scripts/coverage_metadata.lean > registry.tsv.metadata.jsonl`.
   Run all reproducers with `JULIA=... bash scripts/run-repros.sh`, setting
   `JULIA` to each pinned Julia executable in turn. Every audited Base
   refutation must print its reproduction marker on the target master. Release
   results are reported separately.

CRuntime entries describe source-level C behavior. A refutation may have
`runtime` evidence from a Julia reproducer or `modelCounterexample` evidence
from a counterexample in the source model. Model counterexamples do not claim
a Julia runtime manifestation. Keep a targeted non-claiming confirmation
harness, record `kind: model-counterexample`, and set both
`reproduced.release` and `reproduced.nightly` to `false`.
`CRuntimeAudit.lean` reports the evidence class for each refuted entry.

When the model disagrees with Julia's behaviour on a reproducer, the model is
wrong until shown otherwise: fix the model, never the reproducer.

## bugs/<id>.yaml

One YAML file per refuted entry, to sort, filter and decide what to
report upstream. Plain English in the text fields. Multi-line text uses `|`
blocks. `scripts/check-bugs.sh` validates every file against this schema and
checks that every refuted registry id has one.

```yaml
id: ranges-reverse-typemin            # = registry id = repro/<id>.jl; model harnesses may remain non-claiming
title: "reverse(r) overflows for ranges ending at typemin"   # as an upstream issue title
priority: P1                          # P0 | P1 | P2 | P3 (scale below)
kind: wrong-result                    # wrong-result | wrong-exception | missing-error | crash | hang | documentation | model-counterexample
area: Ranges                          # Ranges | IntArith | Sort | Float | GC | ...
files: [base/range.jl]
functions: ["reverse(::StepRange)"]
summary: |
  Two or three sentences: what goes wrong, for which inputs.
likelihood: |
  How likely real code is to hit it.
maybe_intended: |                     # empty string if clearly a bug
  Why someone could consider this intended, with the doc reference.
reproducer: |
  r = Int8(-127):Int8(-1):typemin(Int8)
  reverse(r)
output:                               # verbatim output from each Julia version
  release: |                          # Julia 1.13.2
    ...
  nightly: |                          # 1.15.0-DEV, master bbfa0ce4150
    ...
reproduced: {release: true, nightly: true}
expected: |
  The correct result.
promised_by: |
  Quoted docstring/manual sentence with base/<file>.jl:<line>, or the invariant.
cause: |
  Responsible source lines (base/<file>.jl:<line> on master) and why.
possible_fix: |
  One or two sentences, if obvious; else empty.
duplicates:
  issues:                             # may be empty
    - {number: 12345, state: open, relation: duplicate}   # duplicate | related
  queries: ["reverse range overflow", "StepRange typemin reverse"]
lean:
  property: JuliaLean.Ranges.reverseCorrect
  theorem: JuliaLean.Ranges.reverseCorrect_refuted
covers: []                           # optional: other refuted registry ids with this same root cause; the repro must exercise each
```

Historical `output`, `reproduced`, and `lean` fields retain their original
source evidence. An optional `current` mapping records evidence for another
source version: `commit` is the full 40-character commit, `reproduced` is a
boolean, and `output` is the verbatim runtime output. When `reproduced` is
false, `proof` names the theorem proving the same formerly refuted property.

Priority scale (be conservative; do not inflate):

- **P0**: crash, hang, memory unsafety, or a silently wrong result on inputs
  ordinary code produces (no extreme values needed).
- **P1**: silently wrong result, or a missing error where the docs promise
  one, on edge inputs real code can plausibly reach (typemin/typemax, empty
  collections, unsigned types, large ranges).
- **P2**: wrong exception type, inconsistent behaviour between methods, or
  silent wrong results only on contrived inputs.
- **P3**: documentation contradicts behaviour that is arguably correct, or
  a cosmetic problem.

## Memory safety of unchecked accesses

Goal: prove that no unchecked access in `base/` can go out of bounds, or find
the inputs that make it do so. `memsafety/sites-<group>.tsv` lists every site on
the target master (`@inbounds`, `@boundscheck`, `unsafe_load`, `unsafe_store!`,
`unsafe_copyto!`, `unsafe_wrap`, `memoryref`), one row each, in six files
(groups) split by Julia file.

- Model the enclosing function as usual, with the unchecked access written as an
  explicit bounds obligation (index in `1:length` of the memory or array it
  reads, or the pointer range it covers, after `@inbounds` removes the check).
- The property for the function quantifies over every input its signature and
  documented preconditions allow, including inputs from the public callers that
  reach it, and states that every unchecked access in it is in bounds. One
  registry entry may cover all sites of one function or of several small ones.
  Area `MemSafety`: group n registers its entries in `JuliaLean/MemSafety/G<n>.lean`
  (other files under `JuliaLean/MemSafety/G<n>/`), ids
  `memsafety-<file>-<function>`.
- Refuted: a counterexample input plus `repro/memsafety-*.jl`. The reproducer
  re-runs the trigger in a child `Base.julia_cmd()` with `--check-bounds=yes`,
  so the unchecked access becomes a `BoundsError` at that line instead of a
  silent read; it prints `REPRODUCED <id>` last when the child reports a
  `BoundsError` at the site (or crashes). Write the YAML as for any other bug.
- Each row's `status` becomes `proven` or `refuted` with `entry` set to the
  registry id (comma-separated if several), or `user-contract` (the docstring
  makes the caller responsible, e.g. `unsafe_load` of a caller's pointer;
  quote it in `note`) or `not-unchecked` (the line is not an unchecked access,
  e.g. a comment, a macro definition or a `@boundscheck` check itself; say so
  in `note`). A `proven` row also needs a FAITHFUL verdict for its entry in
  `memsafety/review-<group>.tsv`, written with the fixed
  `memsafety/REVIEW_PROMPT.md`.
- `python3 scripts/check_memsafety.py --repo <julia-source-root>` checks the
  inventory against a `git grep` of the pinned source and validates the rows
  against `registry.tsv` (refresh it as in the workflow above).

## Whole-Base coverage

Goal: account for every method definition in every `base/**/*.jl` file at master
`f755f49a9e41380d7da126b3c1db9fe7f83dd027` (`coverage/SOURCE_COMMIT`). Each
`coverage/methods/<path>.tsv` records source file, start/end
lines, name, source signature, status, registry ids and notes. `<path>` is the
path under `base/`, with `/` replaced by `__` and `.jl` dropped, for example
`coverage/methods/strings__string.tsv`. `scripts/list_base_methods.jl` parses
pinned sources with `julia scripts/list_base_methods.jl <julia-source-root>`
using the pinned master Julia executable; it never evaluates Base. Each syntactic definition in a
method-generating loop appears once, with the loop header in its note. Evaluated
quotes and method templates in macros or generator helpers are included once;
templates have `generated-macro:` or `generated-quote:` notes. Documentation
strings, comments and inert top-level quotes are not definitions.

- `todo`: no settled coverage claim.
- `modelled`: `entry` names proven or refuted registry ids with the same
  `juliaFile`. A registry entry may cover several rows of the same file.
- `excluded`: `note` starts with `no-behaviour:` (no observable behaviour to
  state), `deprecated:` (deprecation path), `internal-bootstrap:` (unreachable
  after Base loads), or `platform:` (only another operating system), followed
  by a one-line justification.

`python3 scripts/check_coverage.py` validates every TSV against `registry.tsv`,
prints per-file and total counts and definition-span-weighted line coverage of
FAITHFUL rows, and fails if any problems, `todo` rows or unreviewed rows remain.
Pass Base paths to check selected files, for example
`python3 scripts/check_coverage.py base/range.jl base/dict.jl`.

The checker accepts `modelled` rows only against a full registry export bound
to its inputs. Stage the pinned Base source under `coverage/src/` (ignored by
git) with
`mkdir -p coverage/src && git -C <julia-source-root> archive f755f49a9e41380d7da126b3c1db9fe7f83dd027 base | tar -x -C coverage/src`,
run `python3 scripts/coverage_evidence.py snapshot .lake/snapshot`, refresh
`registry.tsv` and `registry.tsv.metadata.jsonl` as in the workflow above, then
run `python3 scripts/coverage_evidence.py bind-registry .lake/snapshot registry.tsv`,
which writes `registry.tsv.evidence.json`. The binding covers the metadata, the
root registry import closure, the reproducers and the staged source.

A `modelled` or `excluded` row counts only after a reviewer running the fixed
`coverage/REVIEW_PROMPT.md` marks it FAITHFUL in `coverage/review/<path>.tsv`;
a HOLLOW verdict is a checker problem until the model is fixed and re-reviewed.
Before an independent review, run `python3 scripts/coverage_evidence.py
review-snapshot .lake/review-snapshot.json coverage/methods/<path>.tsv
coverage/review/<path>.tsv`. After the reviewer writes the review, run
`python3 scripts/coverage_evidence.py bind-review .lake/review-snapshot.json
coverage/methods/<path>.tsv coverage/review/<path>.tsv`. Binding requires
unchanged inputs and does not replace the independent review. Reviews without
bindings count as unreviewed. Review bindings cover the selected entries and
their model and proof dependencies, relevant source, reproducers, manifest and
review prompt. Missing or changed inputs invalidate the binding.
FAITHFUL needs a Lean function that mirrors that method's own body (not a
shared simplified model of several overloads) and a property over all allowed
inputs. An umbrella entry claiming many methods with one statement is HOLLOW.

Nested definitions contribute their own spans, so the line measure counts
overlapping spans separately.
An optional `--prefill <metadata.tsv>` file has three tab-separated columns:
registry id, Base source path, and Julia function name. Prefilling settles only
unique same-file name/signature matches; ambiguous matches stay `todo` with
`candidates:<ids>` in their notes. It does not infer Julia subtyping.
