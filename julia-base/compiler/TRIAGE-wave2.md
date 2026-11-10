# Triage of the wave-2 compiler findings (2026-11-10)

This is a skeptical pass over every `bugs/compiler-<area>-*.yaml` from the five wave-2 lanes
(tfuncs, effects, reinfer with cicache, domtree, unionsplit) and the area sections of their
`compiler/PERF_LEADS.md`. Each reproducer was run on the build machine,
under `-t 2`, on three builds:

- pinned 1.15.0-DEV.184 `f755f49a9e`
- `julia +nightly` 1.15.0-DEV.304 `290d5bb5f5` (juliaup, built 2026-10-31)
- `julia +1.13` 1.13.3 `67ac47b9cd`

Upstream master is `eb844b8ebd` (2026-11-10). For each finding I checked whether its code
changed between the pin and master by reading the diff, since the juliaup nightly is 10 days
behind master. Duplicate searches were read-only, and every query is recorded in each yaml's
`duplicates.queries`. The first two batches of searches were invalid. Under zsh, `gh` got
each multi-word query as a single phrase, and some searches hit the search rate limit and
returned nothing. All of them were run again as unquoted words, with retries on rate-limit
errors. The verdicts are a
`Triage 2026-11-10 (wave 2)` paragraph at the top of each yaml's `likelihood` (the schema
allows no `triage` key), plus the top-level `priority`/`kind`. The yaml, repro and
PERF_LEADS changes are committed in each worktree as "Compiler: Triage <area> findings":
tfuncs f9f2bef, effects fff4089, reinfer 172faf1, domtree c0bdb02, unionsplit e678a0d (none
pushed). `scripts/check_bugs.py` gives 0 problems in each worktree; the only warnings are the
existing empty `lean.theorem` ones. If the lanes ran their own searches from zsh, they may have
hit the same phrase problem, so their recorded queries may have matched less than they
appear to.

## Surviving findings, ranked

| # | area | id | priority | summary | pinned / nightly / 1.13 | duplicate |
|---|------|----|----------|---------|-------------------------|-----------|
| 1 | tfuncs | `compiler-tfuncs-vararg-optional-arg-bottom` | **P0**, kind now `crash` | builtin_tfunction pads a trailing Vararg up to the builtin's maximum arity, so `getfield(x, 1, false, v...)` is checked only as the 4-argument form and inferred `Union{}`. With `v = Bool[]` the compiled code reaches `unreachable` and the process dies (SIGILL). | yes / yes / yes | none. Related: [#57292](https://github.com/JuliaLang/julia/issues/57292), fixed by [#57293](https://github.com/JuliaLang/julia/pull/57293) for a Vararg in the order/boundscheck slot itself, not for a fixed argument shifted into it |
| 2 | unionsplit | `compiler-unionsplit-immutable-typevar-member` | **P0** | `is_immutable_type(Union{Nothing, T} where T)` is true because the bare TypeVar member counts as immutable. A field load through such a value is marked consistent, and the call is concrete-evaluated: `w()` keeps returning a field value that was later mutated. | yes / yes / yes | none |
| 3 | tfuncs | `compiler-tfuncs-tuple-vararg-type` | **P0** | tuple_tfunc rewrites `Type{T}` parameters for fixed arguments but not for a trailing `Vararg{Type{T}}`. `tuple(v...)` for `v::Vector{Type{Int}}` is inferred `Tuple{Vararg{Type{Int}}}`, which no value has, and `tuple(v...) isa Tuple{Vararg{Type{Int}}}` folds to `true`. | yes / yes / yes | none. Related: [#44705](https://github.com/JuliaLang/julia/issues/44705)/[#44725](https://github.com/JuliaLang/julia/pull/44725) (the Union case, fixed) |
| 4 | tfuncs | `compiler-tfuncs-subtype-bottom-lhs` | **P0**, low likelihood | subtype_tfunc folds `a <: b` to false from `!hasintersect(a, b)` when `a` may be `Union{}` at run time. `s.t <: String` for a field `t::Type{<:Integer}` holding `Union{}` returns `false`. | yes / yes / yes | none |
| 5 | unionsplit | `compiler-unionsplit-typesubtract-unionall-diagonal` | **P0**, low likelihood | typesubtract splits `Union{A, B} where T` into separately rewrapped members, which makes `T` diagonal in `Tuple{T,T} where T`. The else branch of `y isa AR` loses `(Int8(1), 2)`, so `kr` takes the wrong branch. | yes / yes / yes | none. Related class: [#63345](https://github.com/JuliaLang/julia/issues/63345) (typeintersect drops a diagonal typevar from a union) |
| 6 | reinfer | `compiler-reinfer-stale-min-world` | **P1** | verify_method checks a loaded code instance's edges in `codeinst.min_world`, and the interference fast path then returns `typemax`. A method defined on another thread between image activation and `insert_backedges` is missed, and after a real `using` the image's code keeps calling the old method. | yes / yes / **no** | none. [#63178](https://github.com/JuliaLang/julia/issues/63178) (GC corruption from a concurrent `require`, closed) and [#57904](https://github.com/JuliaLang/julia/issues/57904) (missing invalidation records, closed) are different bugs |
| 7 | effects | `compiler-effects-is-better-order` | P2 | is_better_effects checks only the lowest condition bit of `consistent`, so two conditional states are each "better" than the other, and a weaker one can replace a stronger one after const-prop. Precision only; no visible case built. | yes / yes / yes | none |
| 8 | effects | `compiler-effects-c-foldable-sync` | P3 (was P2), kind now `documentation` | `effects_foldable` in staticdata.c is not in sync with `is_foldable(e, true)` (noub, nortcall), as its comment promises. Since [#62359](https://github.com/JuliaLang/julia/pull/62359) nothing reads the code this clause keeps, so the mismatch has no effect; see perf lead 3. | yes / yes / no (1.13 drops both) | none |
| 9 | effects | `compiler-effects-effect-free-globally-collision` | P3, latent | `EFFECT_FREE_GLOBALLY == ALWAYS_FALSE \| EFFECT_FREE_IF_INACCESSIBLEMEMONLY`, so the bit test reads it as the conditional state, and every `GC.@preserve` statement gets `IR_FLAG_EFIIMO`. No reader acts on it today. | yes / yes / yes | none |
| 10 | unionsplit | `compiler-unionsplit-split-count-exceeds-limit` | P3, `documentation` | The InferenceParams docstring says `max_union_splitting` bounds the number of split signatures; the cost formula (intended since [#37378](https://github.com/JuliaLang/julia/pull/37378)) lets one 20-member union split 20 ways. | yes / yes / yes | none |

Notes per finding:

1. **getfield Vararg padding.** The new user-visible repro: `f(x, v::Vector{Bool}) =
   (getfield(x, 1, false, v...); :reached)` compiles to `_apply_iterate(...)` followed by
   `unreachable`, and `f((1,), Bool[])` prints "Unreachable reached" and dies on all three
   builds. The repro now runs this in a child process. The padding (tfuncs.jl:3306-3322) is
   unchanged on master. The fix in the yaml (tmerge over each possible argument count) is
   local to builtin_tfunction. isdefined, setfield! and the other builtins with optional
   trailing arguments probably have the same shape and should be checked in the same PR.
2. **TypeVar member immutable.** The most plausible input among the P0s: `Union{Nothing, T}
   where T` is an easy mistake for an optional parametric field. The one-line fix is
   `isa(ty, TypeVar) && return false` in `_is_immutable_type` (or test the TypeVar's upper
   bound).
3. **tuple_tfunc Vararg.** [#44725](https://github.com/JuliaLang/julia/pull/44725) fixed the Union case of the same rewrite, and its comment
   (tfuncs.jl:2334-2337) states the rule this breaks. The fix applies the same rewrite to
   `unwrapva(x)` and rewraps.
4. **subtype with Union{}.** The case most likely to be intended. instanceof_tfunc's Union rule
   says it assumes `isexact` "only cares about the answers where there's actually a Type",
   which covers the `Union{Type{Int}, Core.TypeofBottom}` variant. The `Type{<:Integer}`
   variant is not covered, and the true branch's `a === Bottom` test shows the code knows
   Union{} is below everything. The code has had this shape since 2018. Expect a reviewer to
   weigh it against the cost of losing `Const(false)` for every `Type{<:T}` argument.
5. **typesubtract diagonal.** Also the root of the withdrawn `switchtupleunion` finding. Legal
   but unusual types.
6. **Stale code after a concurrent load.** Both parts reproduce on the pinned build and on
   nightly; the yaml also records 1.14.0-alpha2. 1.13.3 caps the range at `min_world` and
   re-infers, so this is a 1.14-line regression, likely from the complete interference sets
   of [#62396](https://github.com/JuliaLang/julia/pull/62396)/[#63469](https://github.com/JuliaLang/julia/pull/63469) (809d9319c5), not bisected. The repro's helper thread takes
   `require_lock` only to hit the window reliably. Any concurrent method definition in the
   window gives the same result, including a second task's `using B` while `using A` has
   dropped `require_lock` around its restore (loading.jl:1495). That variant was not run.
   It is a race, so P1 and not P0, but the result is stale code that is never invalidated,
   and it is the one finding that should be considered for a 1.14 backport.
7. **is_better_effects.** It could be meant as a loose "something improved" test, but its one
   caller uses it to pick between two sound effects, so the wrong order can only cost
   precision. The yaml's cause citation was wrong (effects.jl:174-179 are the bit constants)
   and is now 228-240.
8. **effects_foldable.** Downgraded. Semi-concrete evaluation runs only on a
   LocalInferenceResult (abstractinterpretation.jl:1404). lookup_cached_edge builds one from a
   cached CodeInstance only when it loads inlineable source (typeinfer.jl:1255-1259). So the
   non-inlineable code that this clause keeps "for irinterp" is never used by irinterp after a
   load.
9. **EFFECT_FREE_GLOBALLY.** The only test for the state itself (inferencestate.jl:1409) uses
   `===`, so nothing goes wrong today. Worth the one-line fix when someone touches the flags.
10. **max_union_splitting docstring.** A docstring-only PR.

## Withdrawn

| area | id | reason |
|------|----|--------|
| effects | `compiler-effects-adjust-consistent-overlay` | Not reachable from any public macro: `@assume_effects` has no consistent_overlay setting, and `Base.Experimental.@consistent_overlay` always defines an overlay method, whose inference already starts at CONSISTENT_OVERLAY. Only a hand-built `Expr(:purity, ...)` reproduces it. |
| reinfer | `compiler-cicache-union-hull` | Compilation never produces the input. The one caller, `binding_access_range`, passes touching, non-nested ranges with `min_world >= 1` (proven as UnionCallSite). A trap for a future caller only. |
| domtree | `compiler-domtree-delete-stale-idom` | **Fixed upstream** by [#64518](https://github.com/JuliaLang/julia/pull/64518) (merge 0ae93c3a14, 2026-11-06, in master). Nightly 290d5bb5f5 still reproduces because it was built before the merge. Even before the fix, the stale tree claimed less dominance, never more, and its only caller reads only `bb_unreachable`. |
| domtree | `compiler-domtree-on-semi-path-miss` | Same cause and fix as above: [#64518](https://github.com/JuliaLang/julia/pull/64518) removes `on_semidominator_path`. |
| domtree | `compiler-domtree-rename-keep-unreachable` | **Fixed upstream** by [#64518](https://github.com/JuliaLang/julia/pull/64518) (c13e8ba8d6). The function has no callers, before or after. |
| domtree | `compiler-domtree-naive-only-virtual-pred` | `naive_idoms` is a test-only reference implementation, never called by compilation, and the existing tests do not build this CFG. Unchanged on master; mention it in any PR that adds fuzzed CFGs with catch blocks. |
| unionsplit | `compiler-unionsplit-switchtupleunion-unionall` | Its one call site (typeutils.jl:132) is inside `elseif a isa DataType`, so the method never sees a UnionAll. Same mechanism as surviving finding 5, which a fix can guard in both places. |
| unionsplit | `compiler-unionsplit-cost-subtype-monotone` | Both choices are sound, and counting members is how the cost was designed (comment at typeutils.jl:285-290). Kept as perf lead 9. |

## Perf and caching leads, ranked, with how to measure

Only the area sections were triaged; the lattice sections that every PERF_LEADS.md shares
were triaged in TRIAGE.md. Each entry's full verdict is a "Triage 2026-11-10" bullet under
the lead in that worktree's PERF_LEADS.md.

| rank | area | lead | verdict | measurement plan |
|------|------|------|---------|------------------|
| 1 | reinfer | The binding-edge check (reinfer.jl:307-319) walks `binding_access_range_at` for every binding edge, though `binding_changed_since_require_world`'s fast path already shows the edge cannot narrow the range. | Real: inference pushes one `Core.Binding` edge per `GlobalAccessInfo` (stmtinfo.jl:795-797), and [#62452](https://github.com/JuliaLang/julia/pull/62452) multiplied them about 11x. The skip is sound under `LeafRangePromise` (proven, difftest-checked). Unknown: whether the walk is expensive on an unchanged leaf. | Count binding edges, and time the binding branch of `verify_method`, during `using OrdinaryDiffEq` and `using Plots` on a local master build (temporary counter, or a Tracy zone next to `CC: INSERT_BACKEDGES`). If that is more than about 5% of INSERT_BACKEDGES, add the fast path and compare `@time_imports` ABBA with 10 or more runs. Then confirm on the PR CI TTFX job (load phase). |
| 2 | domtree | ADCE builds a full `DomTree` for every compaction with CFG transforms (ir.jl:819-821) and updates it on every deleted edge, but only ever asks `bb_unreachable` (ir.jl:1485-1494). | Confirmed by reading, and wider than the original lead: the up-front `construct_domtree` runs on every `adce_pass!`, even when no edge is deleted. `CFGReachability` (tarjan.jl) answers the one question. | Sampling profile (`Profile.@profile`, `C=true`) of precompiling one large package on nightly. Sum samples under `CFGTransformState!` -> `construct_domtree` and `kill_edge_terminator!` -> `domtree_delete_edge!`, as a share of `optimize`. If over about 1%, swap in `CFGReachability` and compare precompile time and the sysimage build's `Base.Compiler` timing, then the PR CI TTFX job. |
| 3 | effects | The `effects_foldable` clause in staticdata.c (master 657-664, used at 965) keeps non-inlineable foldable IR in package images "for irinterp". | Real by reading: since [#62359](https://github.com/JuliaLang/julia/pull/62359) nothing reads that code after a load (finding 8), and the clause only applies when native code exists, so codegen does not need it either. Unmeasured image size. | With the `pkgimg` tool, count CodeInstances in the OrdinaryDiffEq and Plots images that have `String` inferred, inlining cost `UINT16_MAX` and foldable effects, and sum their sizes. If over about 1% of the `.ji`, delete the clause, compare `.ji`/`.so` sizes and `@time using` ABBA, and run `Compiler/test/irinterp.jl` and `test/precompile.jl`. |
| 4 | domtree | [#64518](https://github.com/JuliaLang/julia/pull/64518) now runs the delete update for every forward edge (domtree.jl:528 on master). | Plausible, unmeasured; folds into lead 2 if that one lands. | Existing data first: perf.julialang.org TTFX and Nanosoldier compile-time results for master builds either side of 0ae93c3a14, and [#64518](https://github.com/JuliaLang/julia/pull/64518)'s own PR TTFX job. |
| 5 | unionsplit | One long union splits into many signatures; `max_union_splitting` bounds a cost, not the count. | Intended ([#37378](https://github.com/JuliaLang/julia/pull/37378)); the remaining question is time. | Wrapper `AbstractInterpreter`, or a temporary counter in `abstract_call_gf_by_type`, recording `length(split_argtypes)` and call time while precompiling DataFrames or CSV (wide `Union{Missing, ...}`). Act only if the calls with more than 4 signatures take a visible share of inference time. |
| 6 | unionsplit | A `UnionAll` around a `Union` is never split. | Precision lead. Corrected: splitting is sound unless a member would become diagonal on its own. More common than guessed, since `AbstractVecOrMat` and `StridedVecOrMat` have this shape. | Count call sites with such argument types while precompiling StaticArrays or Optim. For a sample, compare inferred return types with and without splitting. |
| 7 | reinfer | The lookup memo in verify_call is an IdDict, so `==`-but-not-`===` signatures miss it. | Unproven and possibly empty, since the serializer deduplicates types through the type cache. | In `verify_call`, record misses by `hash(sig)` during `using OrdinaryDiffEq`, and count misses that are `==` to an earlier key. Drop the lead under 1% of lookups. |
| 8 | effects | is_better_effects can keep the weaker consistent state (finding 7). | Precision only. | Counting wrapper over is_better_effects, comparing each answer with the merge order, while precompiling StaticArrays and DataFrames. Close the lead if the count is near zero. |
| 9 | unionsplit | More precise argument types can turn splitting off. | It is how the cost was designed; the yaml was withdrawn as a bug. | For calls that are not split only because the cost is above the limit, also infer the split version, and count calls where it is strictly better (`⊏`). |
| 10 | tfuncs | tuple_tfunc repeats builtin_tfunction's `is_all_const_arg`. | Real, probably too small to see: the loop stops at the first non-constant argument. | Share of profile samples in that call while precompiling a large package. Drop under 0.1% of inference samples. |
| 11 | reinfer | A method with `did_scan_source & 0x4` still checks every edge. | Real but rare: the code instance is rejected anyway, and this only makes the rejection slower. | Only matters under Revise. Count code instances that take that branch during a `using` after a Revise edit. |
| 12 | reinfer | Edge checks in `min_world` also lose `max_world` and METHOD_SIG_LATEST_ONLY when the counter moved after activation. | Real only with concurrent loading: in a single-task `using` the two worlds are equal. | Count `verify_method` calls with `codeinst.min_world != validation_world` for a single-task load (expect 0) and for two packages loaded from two tasks. Fix it with finding 6. |

Dropped as leads (nothing to measure): `builtin_nothrow` depending on `rt` (an API fragility
for external interpreters, not redundant work); "the word `0` means two things" (master's
`effects_ipo_reset_safe` documents 0 as deliberately conservative; the `decode_effects(0)`
half needs a code reading, not a measurement); `EFFECT_FREE_GLOBALLY` (it is finding 9);
`adjust_effects` weakening `nonoverlayed` (withdrawn); `rename_nodes!(::DomTree)` (dead code,
a cleanup for the next "remove unused functions" commit); "no order dependence in the split
decision" (a negative result, kept as documentation).

## Suggested next steps

- File, or fix directly, findings 1-3 first: each has a small local fix and a user-visible
  repro. Finding 1 crashes, and finding 2 returns a stale value.
- Finding 6 needs a design choice (check in `validation_world`, or cap the range at the world
  the lookups saw) from whoever owns reinfer.jl, and a 1.14 backport label.
- Leads 1-3 are the only ones worth an instrumented build. All three can be measured from
  one `using OrdinaryDiffEq` session plus a precompile profile.
