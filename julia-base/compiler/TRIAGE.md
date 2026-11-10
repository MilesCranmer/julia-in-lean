# Triage of the inference-lattice findings (2026-11-09)

This is a skeptical pass over the refuted entries from the typelattice and typelimits lanes,
plus `compiler-isa-flag-loop`. Each reproducer was run on three builds:

- pinned 1.15.0-DEV.184 `f755f49a9e`
- `julia +1.13` 1.13.3 `67ac47b9cd`
- `julia +nightly` 1.15.0-DEV.304 `290d5bb5f5`, built 2026-10-31 13:36

The juliaup nightly is 9 days behind upstream master (`f840009913`, 2026-11-09). Where a
fix landed in that gap, the status comes from reading master's code, not from running it.
Duplicate searches were read-only and every query is recorded in the yaml's
`duplicates.queries`. The checker (`scripts/check_bugs.py`) reports 0 problems. It allows no
`triage` key, so each verdict is an appended `Triage 2026-11-09` paragraph in `likelihood`,
plus the top-level `priority`/`kind`.

## Surviving findings, ranked

| # | id | priority | summary | pinned / nightly / 1.13 | duplicate |
|---|----|----------|---------|-------------------------|-----------|
| 1 | `compiler-tl-sqsub-widenconst-upper` | **P0** (was P2), kind `hang` | `⊑(PartialTypeVar, T)` is true only for `T === TypeVar`. Two `@goto` merge blocks that each assign `TypeVar(:T)` make `infer_return_type` loop forever; the same shape with `h = 1` finishes in 10 ms. | yes / yes / yes (new repro `repro/compiler-tl-sqsub-widenconst-upper-hang.jl`) | none found. Same mechanism as the Conditional hang fixed by [#64441](https://github.com/JuliaLang/julia/pull/64441), which did not touch this rule. Master still has `b === TypeVar \|\| a === b` (typelattice.jl:560-561). |
| 2 | `compiler-isa-flag-loop` | P0 | A `Conditional` from the previous loop iteration refines the new loop variable, so `f(C(), "y")` returns `false`. A real miscompile. | yes / yes / no | **duplicate** of [#64183](https://github.com/JuliaLang/julia/issues/64183) (open, same reproducer, cause [#55601](https://github.com/JuliaLang/julia/pull/55601)). No fix on master. |
| 3 | `typelimits-tmerge-conditional-idempotent` | P2 | `tmerge(c, c)` on an `@isdefined` Conditional returns `Bool`, or drops `isdefined`. `f` loses `nothrow` and gains an `UndefVarError` path; the merge-free `g` does not. | yes / yes / lattice yes, effect no (1.13 is still nothrow) | none found |
| 4 | `typelimits-tmerge-limited-upper-bound` | P2 | `merge_causes` takes the union for equal-size cause sets, so the merge result is `⊑` both inputs instead of above them. | yes / yes / yes | **duplicate** of [#48376](https://github.com/JuliaLang/julia/issues/48376) (open since 2023, "tmerge for LimitedAccuracy is not convergent") |
| 5 | `compiler-tl-sqsub-bottom-least-optimizer` | P3 (was P2) | On `optimizer_lattice`, `Union{} ⋢ Const(1)` and `Union{} ⋢ PartialStruct`. | yes / yes / yes | none found |
| 6 | `compiler-al-is-valid-lattice-types` | P3 | `is_valid_lattice` uses `&&` where `\|\|` is needed, so it is false for every element above `JLTypeLattice`. It is dead code. | yes / yes / yes | none. [#62057](https://github.com/JuliaLang/julia/issues/62057) was listed as related; it is not, removed. |

Notes per finding:

1. **PartialTypeVar hang.** The lane's probe (`loopy`) converged, but it used an ordinary
   `for` loop. There, the back edge passes through a block with one predecessor, whose state
   widens to `TypeVar` after two visits, so the cascade stops. The hang needs a block that is
   both a merge point and the assigner, which lowering produces through `@goto`. That is the
   same precondition as #64441's `condgoto`. A 120 s run on each build was killed after about
   2e9 allocations, with the backtrace in `typeinf_local`. Contrived code, but a hang, so P0
   by the playbook, and #64441 shows upstream fixes this class. The fix is one line: for a
   type `b`, return `⊑(widenlattice(lattice), TypeVar, b)`. Upstream's new
   `Compiler/test/lattice.jl` has no PartialTypeVar elements, so it is a natural place for
   the test.
2. **isa-flag-loop.** Do not file again. It can be cited as context.
3. **isdefined merge.** Shown to be causal on the pinned build. With
   `Base.REFLECTION_COMPILER[] = Base.Compiler`, I redefined `tmerge(::ConditionalsLattice)`
   so that it keeps `isdefined` for two same-slot isdefined Conditionals. That flips
   `infer_exception_type(f)` from `UndefVarError` to `Union{}`; the unpatched control stays
   `UndefVarError`. The element is the one `@isdefined` itself builds
   (abstractinterpretation.jl:3715). This is a regression from 1.13.3, which has the same
   tmerge result but keeps `nothrow`. Code reading says master is unchanged. Not covered by
   `Compiler/test/lattice.jl`, whose Conditionals are not isdefined ones.
4. **LimitedAccuracy causes.** The return path cannot reach it: `frame.limitations` only
   grows, so `⊑` holds before any merge. Slot states can reach it: ssavaluetypes get
   `LimitedAccuracy(rt, pclimitations)` at abstractinterpretation.jl:4423, and assignments
   carry that into a VarState. No hang or wrong type was built. The yaml can be offered as a
   concrete example on #48376 if someone works on that issue.
5. **Optimizer Bottom.** Every `⊑(𝕃ₒ, …)` in the optimizer compares against a plain type.
   The only lattice-element right side is ssair/passes.jl:1552, and there the result would
   be a sound widening of code that already throws.
6. **is_valid_lattice.** No caller in the tree. The fix is to delete it, next to
   [5fdc91d4e3](https://github.com/JuliaLang/julia/commit/5fdc91d4e3) ("Compiler: remove
   more unused functions"). Registered-package callers were not checked.

## Withdrawn

| id | reason |
|----|--------|
| `compiler-tl-sqsub-transitive` | **Fixed upstream** by [#64441](https://github.com/JuliaLang/julia/pull/64441) (merged 2026-10-31, `42dcc4dea3`). That PR found the same `Const(::Bool) ⊑ Conditional` mismatch hanging inference, so it was effectively P0. The fix is not in the juliaup nightly (`290d5bb5f5` is not a descendant), which is why nightly still reproduces. It is covered by the new transitivity check in `Compiler/test/lattice.jl`. |
| `compiler-tl-widenconditional-extract` | Inference never builds `Conditional(x, Union{}, Union{})`: abstractinterpretation.jl:590-591 returns `Bottom` instead, and the other formers take branch types from a reachable slot's type. Even if it did appear, both answers are sound for unreachable code. |
| `compiler-tl-sqsub-any-top-optimizer` | Has no yaml of its own: it is the same line (typelattice.jl:561-562) as finding 1, which `covers` it. No optimizer call asks `⊑(𝕃ₒ, x, Any)`, so on its own it has no effect. |

## Perf leads, ranked, with how to measure

The PERF_LEADS.md claims were checked against how `stupdate!`/`schanged`/`smerge` actually
gate merges. A missed `⊑` re-queues only the block whose entry changed, and that block
cascades only if its outputs change its successors' entries.

| rank | lead | verdict | measurement plan |
|------|------|---------|------------------|
| 1 | `tmerge` on `JLTypeLattice` is not associative (5/300 smoke cases; 124/1306 on typeinf) | Real on generated inputs; the caching effect is unproven. Within one `typeinf_local` the visiting order is fixed (lowest block first), so any variation would have to come from const-prop, IRInterp, or edits elsewhere. | Precompile one package twice in fresh depots with different dependency load orders. Diff the rettypes of the external code instances in the two caches (`pkgimg`). Count differences in methods with merges of three or more tuple or union types. |
| 2 | `tmerge(::ConditionalsLattice)` has no `typea === typeb` shortcut | Precision part confirmed (finding 3). The frequency guess was too high: `smerge` already short-circuits `===` VarStates, and `schanged` skips the merge when `new ⊑ old`. | Count calls with `typea === typeb` in a counting wrapper `AbstractInterpreter` over a package workload. The fix is cheap either way, because it comes with the finding 3 fix. |
| 3 | `tname_intersect` never joins siblings, so unions can exceed `MAX_TYPEUNION_LENGTH` | Probably intended: it collapses members that share a TypeName, joining siblings would lose precision, and termination does not depend on it. | Count non-`issimpleenoughtype` results of `tmerge_types_slow` during real inference (same wrapper interpreter), and check whether they lead to union-splitting blowups downstream. Drop the lead if they are rare. |
| 4 | `limit_type_size` is not idempotent on `Type{…}` nestings | Documented as not required (commented assertion at typelimits.jl:29-31). Reaches a fixed point in two steps. | First rerun the smoke check on a build with [#64503](https://github.com/JuliaLang/julia/pull/64503) (`c7738544ad`, which changes `Type{}` levels), since it postdates the pin. |
| 5 | `tmerge_field` always returns `nothing` on the default layers | Probably constant-folded. | `code_typed` the `PartialsLattice` merge with the concrete lattice type and look for a remaining call. Drop the lead if none. |

Withdrawn leads:

- **PartialTypeVar ⊑**: promoted to the P0 bug above.
- **`Const(true) ⊑ Conditional`**: fixed by #64441.
- **Optimizer `Any`/`Union{}` fast paths**: no `⊑(𝕃ₒ, x, Any)` callers. The "extra work" is
  three `isa` checks.
- **`is_valid_lattice`**: no runtime cost.
- **`usep` always true** (typelimits.jl:889-904) and **unreachable `issimplertype` branch**
  (line 350): both confirmed by reading the code, and both produce the same output either
  way. They are cleanups.

## Caveats

- The upstream-master status of findings 1, 3, 4, 5 and 6 comes from reading the code at
  `f840009913`. Nothing was run on a master build.
- The lane's statement in PERF_LEADS.md that PartialTypeVar "is not a hang" was wrong. Its
  triage note now says so.
- I did not edit `difftest/compiler/run_repros.sh`, which is outside this task's files. The
  new hang reproducer needs adding there, and it takes about 2 minutes per Julia, since it
  waits out a 60 s limit.
