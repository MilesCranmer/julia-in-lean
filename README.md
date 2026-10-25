# Formalizing Julia in Lean

Julia source code, modelled in Lean 4, with AI coding agents writing the models and the proofs and machine checks deciding what counts. Each Julia function is mirrored by a Lean definition that follows the source line by line. Each property of that function, taken from a docstring, the manual, or an obvious invariant, ends either proven (a Lean theorem) or refuted (a Lean theorem of the negation, built from a concrete counterexample). Every refutation is backed by a pure-Julia script that reproduces the problem on real Julia.

The repository holds two Lean packages. `julia-base/` models parts of Julia Base and several standard libraries: 910 registered properties, 510 proven and 400 refuted, with 401 bug write-ups and 75 issues filed on JuliaLang/julia. `dynamicexpressions/` models DynamicExpressions.jl, the expression-tree package behind SymbolicRegression.jl and PySR: 385 properties in the first pass (332 proven, 53 refuted), 38 fix pull requests merged upstream, and a current registry of 400 entries with 394 proven and 6 refuted.

The method is described in enough detail to repeat it for another package.

## Contents

1. [What a property looks like](#what-a-property-looks-like)
2. [The method](#the-method)
3. [Running it with agents](#running-it-with-agents)
4. [What went wrong, and the lessons](#what-went-wrong-and-the-lessons)
5. [Results](#results)
6. [Formalizing your own package](#formalizing-your-own-package)
7. [Repository layout and building](#repository-layout-and-building)
8. [Limits](#limits)

## What a property looks like

The example below is a real entry, `ranges-operations-reverse-typemin`, filed as JuliaLang/julia#64124. Every refuted entry has the same four pieces: a Lean definition mirroring the Julia source, a closed `Prop`, a theorem of its negation, and a reproducer script.

Julia reverses an ordinal range by rebuilding it with the negated step (`base/range.jl:1435`):

```julia
_reverse(r::OrdinalRange, ::Colon) = (:)(last(r), negate(step(r)), first(r))
```

The Lean mirror (`JuliaLean/Ranges/Operations.lean`) does the same, in Julia's `Jl` error monad and with Julia's fixed-width scalar arithmetic (`Num`):

```lean
/-- `base/range.jl:1435`: reversing ordinal ranges reconstructs with `negate(step)`. -/
def reverse (r : Rng) : Jl Rng := do
  let st ← Num.negate (step r)
  colon3 (last r) st (first r)
```

The property comes from the `reverse` documentation: reversing a range that Julia constructed keeps its number of elements. It quantifies over every start, step, stop and range:

```lean
/-- Reversing a successfully constructed ordinal range preserves its mathematical cardinality. -/
def reverseCardinalityProp : Prop :=
  ∀ (a st b : Num) (r : Rng), stepRange a st b = .ok r →
    match reverse r with
    | .ok out => trueCount out = trueCount r
    | .error _ => False
```

The refutation instantiates it at `Int8(0):typemin(Int8):typemin(Int8)`, a two-element range. Negating the step `-128` wraps back to `-128`, so the rebuilt range runs from `-128` down to `0` in steps of `-128` and is empty. `decide` checks both the construction and the element counts:

```lean
theorem reverseCardinalityRefuted : ¬ reverseCardinalityProp := by
  intro h
  let a := Num.lit (.bit .i8) 0
  let st := Num.lit (.bit .i8) (-128)
  let r : Rng := ⟨.step, a, st, st⟩
  have hr : stepRange a st st = .ok r := by decide
  have hp := h a st st r hr
  have hn : ¬ (match reverse r with
      | .ok out => trueCount out = trueCount r | .error _ => False) := by
    change ¬ ((0 : Int) = 2)
    decide
  exact hn hp
```

The registry entry records where the promise comes from, which Julia functions it covers, which theorem settles it, and the duplicate search:

```lean
{ id := "ranges-operations-reverse-typemin", juliaFile := "base/range.jl",
  juliaFns := ["reverse(::OrdinalRange)", "sort(::AbstractRange)"],
  statement := "Reversing a constructed range preserves its cardinality.",
  source := "reverse documentation, base/array.jl:2193-2197", status := .refuted,
  prop := ``reverseCardinalityProp, thm := some ``reverseCardinalityRefuted,
  issue := "none found (issues: reverse range typemin; PRs: reverse range typemin)", ... }
```

The reproducer `repro/ranges-operations-reverse-typemin.jl` is pure Julia. It prints `REPRODUCED <id>` as its last line only when the behaviour is observed, and it does on both the 1.13.2 release and master. It also shows the same bug reaching `sort`:

```julia
r = Int8(0):typemin(Int8):typemin(Int8)
s = reverse(r)
sortable = Int8(127):typemin(Int8):Int8(-1)
@assert length(sortable) == 2 && isempty(sort(sortable))
if length(r) == 2 && isempty(s) && reverse(collect(r)) == Int8[-128, 0]
    println("REPRODUCED ranges-operations-reverse-typemin")
else
    error("reverse typemin did not reproduce: $s")
end
```

A proven entry has the same first three pieces, with a theorem whose type is the property itself instead of its negation, and no reproducer.

## The method

### Modelling rules

Each Julia function becomes one Lean definition that follows the source: the same branches, the same order of checks, fixed-width integers with Julia's wraparound. Julia exceptions are values of `Except JlError α`, for example `.error (.argumentError msg)`, `.boundsError`, or `.inexactError`. Unchecked invalid memory access is modelled explicitly rather than hidden; the DynamicExpressions.jl model returns an `undefinedBehavior` value for it.

The model is hand-written, so it can be wrong. The checks below exist to catch that.

### Properties and generality

A property is a closed Lean `Prop`. Its statement comes from one of three places, recorded in the registry: a docstring, the manual, or an obvious invariant. Examples of properties:

- `tryparse` never throws.
- `reverse(reverse(r))` has the fields of `r`.
- Values that are `isequal` hash equally.
- With `early_exit=false`, evaluation of a non-constant tree returns the elementwise result.

Each property must quantify over inputs. An automated generality count unfolds definitions to a fixed depth and counts universally quantified data variables; statements that only check worked examples are rejected. A Printf entry that checked the 11 docstring examples was rejected by this check and kept only as a lemma.

### Proven or refuted

Every entry ends in one of two states.

| Status | Lean artefact | Julia artefact |
| --- | --- | --- |
| PROVEN | a theorem whose type is exactly the property | none |
| REFUTED | a theorem whose type is exactly the negation, built from a concrete counterexample and checked with `decide` | `repro/<id>.jl` prints `REPRODUCED <id>` as its last line |

A refutation counts only when the reproducer shows the behaviour on real Julia: the 1.13.2 release, Julia master (1.15.0-DEV, pinned to commit `bbfa0ce4150`), or both. A bug seen only on master is a regression candidate. DynamicExpressions.jl reproducers run against the package. A Lean counterexample without a reproducer is a model bug, not a Julia bug.

### Differential testing

Before any proof work, the Lean model is evaluated on many inputs and the results are compared with real Julia. Examples:

- The shared Int8/UInt8 integer core matched Julia master on an exhaustive 656,896-row table.
- The Float64 model matched on 236,954 operations for both Julia versions.
- The TOML parser model matched on about 15,000 test documents.

When the model and Julia disagree, the model is wrong until shown otherwise. The fix goes into the model, never into the reproducer.

### The audit

A registry (`Registry.lean`, exported to `registry.tsv`) lists every entry: id, status, Julia file, Julia function names, statement, preconditions, and a duplicate-issue field. `Audit.lean` fails the build if any of the following holds:

- an id is duplicated;
- any entry is unsettled;
- a theorem's type is not exactly the property or its negation;
- a theorem depends on an axiom other than Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`);
- a non-static property has no quantified data variable.

A source scan also rejects `sorry`, `admit`, `native_decide`, `bv_decide` and `ofReduceBool`, since each bypasses or weakens the kernel check. Coverage is enforced: every Julia file and function named in the model must have entries.

### Questions and rulings

Ambiguous semantics go to `QUESTIONS.md` (the DynamicExpressions.jl package has Q1 to Q58). Each question gives the file and line, both readings, and the maintainer's ruling. When the ruling is "not a bug", the property is restated to match Julia's actual behaviour and proven, and the reproducer is deleted. Rulings of this kind included: repeated degree keys in `OperatorEnum` behave like a `Dict` (last wins); signed-zero hashing; constant trees may exit early.

### Flipping after upstream fixes

When a bug is fixed upstream, upstream is merged into the formalization branch and the model is updated to the new source. The same statement then flips from `_refuted` to `_holds` (proven). The statement is never edited to make it pass.

### Bug write-ups and priorities

Each confirmed bug gets a YAML file `bugs/<id>.yaml`, validated by `scripts/check-bugs.sh`, with these fields: id, title, priority, kind, area, files, functions, summary, likelihood, maybe_intended, reproducer, verbatim output for each Julia version, expected behaviour and the sentence that promises it, cause (source lines), possible fix, duplicates (issue numbers or the searches tried), and the Lean property and theorem names.

| Priority | Meaning |
| --- | --- |
| P0 | crash, hang, memory unsafety, or silent wrong result on ordinary inputs |
| P1 | silent wrong result or missing error where the docs promise one, on edge inputs real code can reach (typemin/typemax, empty collections, unsigned types) |
| P2 | wrong exception type, inconsistency between methods, or silent wrong results only on contrived inputs |
| P3 | documentation contradicts arguably correct behaviour, or cosmetic |

### Duplicate search

Before filing, each bug is searched for duplicates in JuliaLang/julia issues and pull requests, and the YAML records what was found or which searches were tried. Many findings were already known, for example [#58245](https://github.com/JuliaLang/julia/issues/58245) (`collect(typemin(Int):typemax(Int))` segfault), [#62906](https://github.com/JuliaLang/julia/issues/62906) (nested `SubArray` offset), and [#63399](https://github.com/JuliaLang/julia/issues/63399) (range search overflow, with an open PR that fixes it).

Filing is never automated. After the first two reports, the Julia community was asked how it preferred to receive findings in bulk, and the answer was individual issues. Each issue is drafted from its YAML, checked again for duplicates, and shown to a person, who approves it or sends it back before it is posted. Issues are posted from a separate bot account so they read as ordinary bug reports; each ends with a short italic note saying it was found through a Lean formalization and tagging the person responsible. Selection favours distinct bugs that are severe and that real code might hit, so most write-ups are never filed. Findings that may be security-relevant are held back and raised privately before anything is posted.

## Running it with agents

### Areas and ownership

One agent owns one area of the source, for example ranges, integer arithmetic, Dict/Set, UTF-8 strings, Printf, the TOML parser, or shell quoting. The area owns a fixed set of files:

```
JuliaLean/<Area>.lean
JuliaLean/<Area>/
repro/<area>-*.jl
bugs/<area>-*.yaml
```

A coordinator agent creates area stubs, registers them, broadcasts rule changes, and reviews results. An area took one agent between one and six hours. About 50 areas were covered in waves of 4 to 7 agents running in parallel; agents sometimes spawned sub-agents for independent parts of an area.

### Models and refusals

Models used: Claude Opus for most areas, GPT-6.1 Sol through Codex, Kimi K3, GLM-5.3, and OpenAI's Daybreak Blue model in Codex.

Several GPT-based runs were stopped by the provider's cybersecurity filter (`cyber_policy`) because the task described hunting for bugs and overflow in source code. Kimi and GLM sub-runs that fell back to GPT models hit the same filter. Those areas were re-run on Claude Opus, or on Daybreak Blue, which is intended for authorized security work and accepted the same task.

### Practical rules

- Agents write the YAML as soon as a reproducer confirms, not at the end of a run. Holding write-ups until the end delayed reports by hours.
- Agents share one working tree and commit with an explicit pathspec (`git commit -m ... -- <files>`), because a bare `git commit` also commits other agents' staged files.
- Rule changes are broadcast by the coordinator to every running agent.

## What went wrong, and the lessons

1. **Hollow proofs.** In the memory-safety phase, the first pass reported 130 sites proven in under an hour. A review with a fixed rubric (`memsafety/REVIEW_PROMPT.md`) asked three questions of each proof: does the Lean compute the index from the function's real inputs by following the Julia code? Are its hypotheses only type invariants or documented preconditions? Does it cover every caller? The review failed 128 of 130. The proofs assumed the conclusion, for example "if 1 ≤ i ≤ len then i is in bounds". All 128 were withdrawn. The general audit cannot detect this kind of proof, because it is a valid theorem of a vacuous statement; only a check against the source can.
2. **Reproducer harness false negatives.** A reproducer that printed more output after its `REPRODUCED` line was counted as failing, because the harness stopped reading early. Rule: `REPRODUCED <id>` is the last line.
3. **Internal-helper "bugs".** Three memory-safety findings broke internal functions only on inputs that no public caller can produce. They were withdrawn. A finding must be reachable from the public API or from a documented contract.
4. **Bounds-checked reproducers.** A finding that needs `--check-bounds=yes` to show an error is still real if the error proves that the default build reads out of bounds. Its priority depends on how ordinary code reaches it.
5. **Scope pressure.** A model under time pressure wants to stub a definition, narrow a statement, or test examples instead of quantifying. The audit and the generality check exist for this.

## Results

### Julia Base (`julia-base/`)

Lean 4.34.1 (`lean-toolchain`: `leanprover/lean4:v4.34.1`), no Mathlib.

| Count | |
| --- | --- |
| Registry entries | 910 |
| Proven | 510 |
| Refuted | 400 |
| Bug write-ups | 401 |

There is one write-up per refuted entry, plus one for a compiler bug (`compiler-isa-flag-loop`, [#64183](https://github.com/JuliaLang/julia/issues/64183)) found while checking Markdown; the compiler is outside the Lean model, so it has no registry entry. Bug write-ups by priority:

| Priority | Count |
| --- | --- |
| P0 | 4 |
| P1 | 47 |
| P2 | 223 |
| P3 | 127 |

Coverage: parts of about 90 files in `base/`, plus the stdlib packages Printf, Dates, Base64, UUIDs, CRC32c, TOML, Markdown, Sockets, Serialization, Artifacts, Random and Unicode.

After the first two reports (including [#64121](https://github.com/JuliaLang/julia/issues/64121)), 75 issues were filed on JuliaLang/julia ([full list](https://github.com/JuliaLang/julia/issues?q=is%3Aissue%20author%3AMilesCranmerBot)), numbered [#64123](https://github.com/JuliaLang/julia/issues/64123) to [#64207](https://github.com/JuliaLang/julia/issues/64207). A few numbers in that range come from a separate C-runtime/GC project that is not in this repository. Selected filed issues, all open:

- [#64183](https://github.com/JuliaLang/julia/issues/64183): 1.14 regression. A stale `isa` refinement across loop iterations miscompiles code: inference folds `w && el isa String` to false when `w = el isa C` was set in the previous iteration. Found because `Markdown.rst` printed wrong output on master.
- [#64147](https://github.com/JuliaLang/julia/issues/64147): BitArrays. Resizing `vec(M)` or `reshape(M, n)` corrupts the original `BitArray` (memory unsafe).
- [#64175](https://github.com/JuliaLang/julia/issues/64175): `selectdim` with a `CartesianIndex` can create an out-of-bounds view.
- [#64185](https://github.com/JuliaLang/julia/issues/64185): Printf. A large `BigFloat` after preceding output can write past the buffer.
- [#64202](https://github.com/JuliaLang/julia/issues/64202): Printf. Negative dynamic precision writes integer digits out of bounds.
- [#64204](https://github.com/JuliaLang/julia/issues/64204): Printf. Exact-fit `BigFloat` conversion replaces the last character with NUL.
- [#64193](https://github.com/JuliaLang/julia/issues/64193): Artifacts. Slash lookup allows paths outside the artifact directory.
- [#64131](https://github.com/JuliaLang/julia/issues/64131): 1.14 regression. `intersect` can return values absent from an input.
- [#64123](https://github.com/JuliaLang/julia/issues/64123): `intersect` can omit shared values.
- [#64143](https://github.com/JuliaLang/julia/issues/64143): `first(s, typemax(Int))` returns empty for non-ASCII strings.
- [#64136](https://github.com/JuliaLang/julia/issues/64136): `range` can miss a tiny nonzero endpoint (`last(range(1.0, 1e-300; length=24))`).
- [#64142](https://github.com/JuliaLang/julia/issues/64142): `round(floatmax(); sigdigits=1)` returns `0.0`; `sigdigits` turns large finite values into zero.
- [#64170](https://github.com/JuliaLang/julia/issues/64170): TOML. A later value can silently overwrite an existing table.
- [#64200](https://github.com/JuliaLang/julia/issues/64200): `uuid5` unescapes the name before hashing.
- [#64192](https://github.com/JuliaLang/julia/issues/64192): shell. Line continuation can drop characters after non-ASCII text.

Some confirmed bugs are held back from this repository until they have been reported.

### Memory safety

The memory-safety phase lists every unchecked access in `base/` on master: `@inbounds`, `@boundscheck`-elided paths, `unsafe_load`, `unsafe_store!`, `unsafe_copyto!`, `memoryref`, and similar. The list, `memsafety/sites-<group>.tsv`, has 1,152 sites in about 90 files, split into six groups. Each site must end in one of four states:

| State | Requirement |
| --- | --- |
| proven | a faithful in-bounds proof that passes the review rubric |
| refuted | a reproducer, run under `--check-bounds=yes` so the access throws instead of silently reading |
| user-contract | the docstring makes the caller responsible; the sentence is quoted in the note |
| not-unchecked | the site is not actually an unchecked access |

`scripts/check_memsafety.py` fails while any site is unsettled. Current state: 242 sites are not unchecked accesses, 159 are the caller's responsibility by contract, 20 are refuted, and 731 are not yet settled. This phase is unfinished.

### DynamicExpressions.jl (`dynamicexpressions/`)

DynamicExpressions.jl provides trees of operator nodes, constants and features; an `OperatorEnum`; fast evaluation kernels (`eval_tree_array`, fused kernels, early exit on non-finite values); derivatives; simplification; string parsing and printing; `GraphNode` with shared subtrees; and parametric and structured expressions.

The Lean package `DynExpr` models:

- trees (`Model/Tree.lean`): constant, feature and operator-branch constructors, one-based features, and degree, operator and feature well-formedness;
- operators as total Lean functions on value lists (`Model/OperatorEnum.lean`);
- a denotation that evaluates left to right (`Model/Denote.lean`);
- the typed evaluator with fused kernels, early exits, constant-tree shortcuts and buffer slots (`Eval/Core.lean`).

Areas: Deriv, Eval, EvalCache, Expressions, Model, NoAlias, NodeBase, NodeUtils, ParamStruct, Plumbing, Simplify, StringsParse.

| | Entries | Proven | Refuted |
| --- | --- | --- | --- |
| First full pass | 385 | 332 | 53 |
| Current registry | 400 | 394 | 6 |

Maintainer rulings on ambiguous cases are in `QUESTIONS.md`.

The bugs were fixed upstream, one pull request per bug, with bugs that share a root cause fixed together. 38 Lean-derived fix PRs were merged into SymbolicML/DynamicExpressions.jl (numbers from [#221](https://github.com/SymbolicML/DynamicExpressions.jl/issues/221) onward), and each refutation flipped to proven as its fix landed. Examples of merged fixes:

- [#249](https://github.com/SymbolicML/DynamicExpressions.jl/issues/249): `is_valid_array` accepts finite arrays whose sum overflows.
- [#241](https://github.com/SymbolicML/DynamicExpressions.jl/issues/241): `GraphNode` equality must match shared nodes to each other.
- [#242](https://github.com/SymbolicML/DynamicExpressions.jl/issues/242): break sharing when converting `GraphNode` to `Node`.
- [#264](https://github.com/SymbolicML/DynamicExpressions.jl/issues/264): throw `BoundsError` for feature indices beyond the input rows.
- [#268](https://github.com/SymbolicML/DynamicExpressions.jl/issues/268): fused unary kernels apply the outer operator when early exit is off.
- [#270](https://github.com/SymbolicML/DynamicExpressions.jl/issues/270): the fused branch kernel checks constant subtrees like the unfused path.
- [#259](https://github.com/SymbolicML/DynamicExpressions.jl/issues/259): reject negative and non-finite `NodeSampler` weights.
- [#229](https://github.com/SymbolicML/DynamicExpressions.jl/issues/229): parse `NaN`, `Inf` and `-Inf` constants.
- [#228](https://github.com/SymbolicML/DynamicExpressions.jl/issues/228): parenthesize signed power bases when printing.

The remaining refutations include `eval-noearly-denote`: with `early_exit=false` and no fusion, `x1 + inv(inv(0.0))` still stops early.

Four further refutations concern an open performance PR, [#219](https://github.com/SymbolicML/DynamicExpressions.jl/issues/219), which adds a cache of unary operators applied to features. The formalization was extended with the cache before the PR was merged. It shows that cached and uncached evaluation differ in three situations: when the input array or the operators are mutated in place (`evalcache-mutate-x`, `evalcache-mutate-op`); when callers with different `early_exit` settings share a cache (`evalcache-shared-early-exit`); and when threads share one context (`evalcache-threads`). These are findings about the PR as it stands, recorded so the design can take them into account.

Downstream, a separate Lean formalization of SymbolicRegression.jl imports the DynamicExpressions.jl Lean package as a dependency. It led to three SymbolicRegression.jl fixes: [#786](https://github.com/MilesCranmer/SymbolicRegression.jl/issues/786) (count shared `GraphNode` subtrees once in weighted complexity), [#789](https://github.com/MilesCranmer/SymbolicRegression.jl/issues/789) (optimize a child in the optimize mutation instead of the parent) and [#790](https://github.com/MilesCranmer/SymbolicRegression.jl/issues/790) (keep NaN losses off the Pareto frontier). That formalization is not in this repository.

## Formalizing your own package

A checklist derived from the method above. The order matters: the checks that keep the agents honest must exist before the agents start proving things.

1. **Set up the model, the differential test, the audit and the registry first.**
   - Write the Lean mirror of one small, central module by hand or with one agent, following the source line by line. Use `Except JlError` for exceptions and fixed-width integer types for Julia integers.
   - Write a differential test that evaluates the model on many inputs and compares the results with the real package. Make it exhaustive where the input space allows (small integer types) and random elsewhere. Run it before any proof work, and rerun it whenever the model changes.
   - Write `Audit.lean` and the registry before the second module. The audit must fail the build on unsettled entries, mismatched theorem types, non-standard axioms, and `sorry`, `admit`, `native_decide`, `bv_decide` and `ofReduceBool`. Add the generality count so that example-checking statements are rejected.
   - Add the coverage rule: every file and function named in the model needs entries.
2. **Pick properties from written promises.** Take each property from a docstring, the manual, or an invariant that a maintainer would agree with, and record the source in the registry. Every property must quantify over inputs. A property that reads "this example returns that" is a lemma, not an entry.
3. **Require a reproducer for every refutation.** A Lean counterexample is a claim about the model. The pure-Julia script that prints `REPRODUCED <id>` as its last line is what makes it a claim about the package. Run reproducers on the versions that matter (the latest release and the development branch). When the model and the package disagree, fix the model.
4. **Keep an issue search in the loop.** Before writing a bug up, search the package's issues and pull requests, and record the result in the write-up.
5. **Ask the maintainers early.** When two readings of the source are both plausible, write both down in `QUESTIONS.md` with the file and line, and ask. A "not a bug" ruling becomes a restated, proven property. Do not leave ambiguous entries refuted.
6. **Write bugs up as they are confirmed.** A YAML per bug with the fields listed above, validated by a script, written the moment the reproducer passes.
7. **Review proofs against the source, not only against the audit.** Especially for memory-safety claims, use a fixed rubric: the proof must compute the index from the real inputs by following the code, its hypotheses must be type invariants or documented preconditions, and it must cover every caller.
8. **Keep reproducers and flip on fix.** When a fix is merged upstream, merge it into the formalization branch, update the model to the new source, and let the same statement flip from refuted to proven. Never edit the statement.
9. **Give each agent one area and a coordinator.** One area per agent, fixed file ownership, commits with an explicit pathspec, and a coordinator who creates stubs, broadcasts rule changes and reviews results.

## Repository layout and building

```
julia-base/
  lean-toolchain              leanprover/lean4:v4.34.1
  ARCHITECTURE.md             modelling rules, workflow, YAML schema, priority scale
  JuliaLean/<Area>.lean       registry entries of one area of Julia Base or a stdlib
  JuliaLean/<Area>/           models, properties, proofs, refutations, differential checks
  JuliaLean/Registry.lean     collects every area's entries
  Audit.lean, Report.lean     registry checks; export to registry.tsv
  registry.tsv                every entry with its status
  repro/<id>.jl               one pure-Julia reproducer per refuted entry
  bugs/<id>.yaml              one write-up per confirmed bug
  memsafety/sites-*.tsv       unchecked-access sites, six groups
  memsafety/REVIEW_PROMPT.md  rubric for reviewing in-bounds proofs
  scripts/audit.sh            lake build, forbidden-token scan, audit
  scripts/run-repros.sh       runs every reproducer on a given Julia
  scripts/check-bugs.sh       validates bugs/*.yaml
  scripts/check_memsafety.py  fails while any memory-safety site is unsettled
  NOTICE                      Julia's license, for the mirrored source

dynamicexpressions/
  README.md, ARCHITECTURE.md       modelled commit, rules, how to run
  QUESTIONS.md                     Q1 to Q58 with maintainer rulings
  DynExpr/Model/Tree.lean          trees and well-formedness
  DynExpr/Model/OperatorEnum.lean  operators as total functions on value lists
  DynExpr/Model/Denote.lean        left-to-right denotation
  DynExpr/Eval/Core.lean           typed evaluator: fused kernels, early exit, buffers
  DynExpr/<Area>/                  Deriv, Eval, EvalCache, Expressions, ... StringsParse
  DynExpr/Registry.lean, Audit.lean, Report.lean, registry.tsv
  repro/<id>.jl, repro/Project.toml
  scripts/audit.sh, scripts/run-repros.sh
```

Build and check a package:

```sh
cd julia-base                     # or dynamicexpressions
bash scripts/audit.sh             # lake build, forbidden-token scan, audit; ends with AUDIT OK
JULIA=/path/to/julia scripts/run-repros.sh   # runs the reproducer of every refuted entry
```

For `julia-base/`, run the reproducers against both the 1.13.2 release and Julia master; each refuted entry reproduces on at least one of them, and most on both. The DynamicExpressions.jl reproducers use `repro/Project.toml`, which pins the package at the modelled commit; the `evalcache-*` reproducers need the [PR #219](https://github.com/SymbolicML/DynamicExpressions.jl/issues/219) branch instead.

## Limits

**What "proven" means.** A proven entry is a theorem about the Lean model. The model mirrors the Julia source by hand and is checked against the real implementation by differential testing, not by a verified compiler or a verified semantics of Julia. A proof therefore says: if the model is faithful on the inputs the property quantifies over, the property holds. Differential testing raises confidence in faithfulness; it does not establish it. The refuted side is stronger, because every refutation is confirmed by a reproducer on the real implementation.

**Coverage is partial.** The Julia Base package covers parts of about 90 files in `base/` and a selection of stdlib packages. Within a covered file, only the functions named in the model have entries. The coverage rule guarantees that named functions have entries; it does not say anything about the rest of the file.

**The memory-safety phase is unfinished.** Of the 1,152 listed sites, the current state is 242 sites are not unchecked accesses, 159 are the caller's responsibility by contract, 20 are refuted, and 731 are not yet settled. The first-pass proofs were withdrawn after review (see the lessons above), and any new proof must pass the same review rubric before it counts.

**Priorities are judgment calls.** The agent that confirms a bug assigns its P0 to P3 priority from the scale above, and a person reviews it before anything is filed. Whether an input is "ordinary" or "contrived", and whether a documented sentence is a promise or a description, are decisions that another reader could make differently. The write-ups record the reasoning so the decision can be revisited.

**Properties are only as good as their sources.** A docstring can be wrong or vague. When the source of a property is an invariant rather than a written promise, the refutation is an argument for a change rather than evidence of a contradiction, and the write-up records that possibility in its `maybe_intended` field.
