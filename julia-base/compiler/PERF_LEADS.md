# Optimization leads in the inference lattice

Hypotheses for a human to measure, never claims of speedup (see `PLAYBOOK.md`, "Bugs and
leads"). One section per lead:

- **Source:** `Compiler/src/<file>.jl:<lines>` at `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
- **What:** the precision lost without need, the work whose result is provably fixed, or the
  fast path that never (or always) fires.
- **Lean statement:** the registry id and theorem that show it.
- **How often real inference hits it:** a guess, labelled as one.

## Lattice order and widening (abstractlattice.jl, typelattice.jl), from the property pass

### PartialTypeVar is only below `TypeVar` itself

- **Source:** `Compiler/src/typelattice.jl:561-562` (`b === TypeVar || a === b`).
- **What:** `PartialTypeVar ⊑ T` is false for every type `T` other than `TypeVar`, for example
  `Union{Nothing, TypeVar}`, the `tmerge` of a `PartialTypeVar` and `nothing`. When a slot's state
  is that union and a new `PartialTypeVar` arrives, `schanged` (`typelattice.jl:777-778`) reports a
  change although `smerge` gives back the old type, so `stupdate!` marks the block changed and it
  is inferred again. The same comparison on `optimizer_lattice` fails even against `Any`.
- **Lean statement:** `compiler-tl-sqsub-widenconst-upper`
  (`JuliaLean.Proofs.Compiler.src.typelattice.sqsubWidenconstUpperTypeinf_refuted`) and
  `compiler-tl-sqsub-any-top-optimizer` (`sqsubAnyTopOptimizer_refuted`).
- **How often real inference hits it (guess):** rare; only code that builds `TypeVar`s from
  constant arguments and merges them with another type. A loop probe
  (`difftest/compiler/typelattice_probe.jl`) still converged in 0.02 s, so the cost is a few
  extra block visits, not a hang.
- **Triage (2026-11-09): promoted to a P0 bug; it is a hang, not a perf lead.** When two
  `@goto` merge blocks each assign a PartialTypeVar, inference never terminates on pinned,
  1.13.3 and nightly (`repro/compiler-tl-sqsub-widenconst-upper-hang.jl`). In ordinary loops
  the extra visits stop after two rounds, because a single-predecessor block widens to
  `TypeVar`. Tracked in `bugs/compiler-tl-sqsub-widenconst-upper.yaml`.

### `Const(true)` is not below a `Conditional` whose else branch is inhabited

- **Source:** `Compiler/src/typelattice.jl:434-442`.
- **What:** `Const(true) ⊑ Conditional(x, Any, E)` is true only for `E === Union{}`, although a
  constant `true` never takes the else branch. A missed `⊑` makes `schanged` report a change and
  `tmerge` run where the old state already covers the new one; it also breaks transitivity, so
  whether two states compare as equal can depend on the order in which they were merged.
- **Lean statement:** `compiler-tl-sqsub-transitive`
  (`JuliaLean.Proofs.Compiler.src.typelattice.sqsubTransitiveTypeinf_refuted`).
- **How often real inference hits it (guess):** low; needs a branch condition that folds to a
  constant on one path and is a `Conditional` with `thentype === Any` on another.
- **Triage (2026-11-09): fixed upstream, withdrawn.** JuliaLang/julia#64441 (merged
  2026-10-31, 42dcc4dea3) rewrote this rule after the same mismatch hung inference on a
  `@goto` loop. The juliaup nightly 290d5bb5f5 predates it. In plain `while` loops the cost
  was one extra header revisit, since an unchanged block entry stops the cascade.

### No `Any`/`Union{}` fast paths on the optimizer lattice

- **Source:** `Compiler/src/typelattice.jl:421-425` (the only fast paths, in the conditional
  layers), `460-567` (`PartialsLattice`, `ConstsLattice`).
- **What:** `optimizer_lattice` is `PartialsLattice(ConstsLattice())`, so `⊑(𝕃ₒ, a, Any)` runs
  the `PartialStruct`/`PartialOpaque`/`PartialTask`/`Const` tests before `a <: Any`, and
  `⊑(𝕃ₒ, Union{}, b)` is wrongly false for a `Const` or `PartialStruct` `b`. Adding the two
  fast paths to the outermost layer would fix the order and skip that work.
- **Lean statement:** `compiler-tl-sqsub-bottom-least-optimizer`
  (`sqsubBottomLeastOptimizer_refuted`); the typeinf versions with the fast paths are proven
  (`compiler-tl-sqsub-any-top-typeinf`, `compiler-tl-sqsub-bottom-least-typeinf`).
- **How often real inference hits it (guess):** the wrong answer, rarely (an unreachable statement
  compared with a constant, e.g. `Compiler/src/ssair/passes.jl:1552`); the extra tests, on every
  optimizer `⊑` whose right side is `Any`, frequency unknown.
- **Triage (2026-11-09): perf part withdrawn.** No `⊑(𝕃ₒ, x, Any)` call exists in
  optimize.jl, ssair/passes.jl or ssair/inlining.jl. The right side is always a specific type
  (Bool, Tuple, Type, Method, Task, Builtin, a field type) or a lifted `result_t`. The
  "extra tests" are three `isa` checks before `<:`. There is nothing to measure. The
  correctness part stays as `compiler-tl-sqsub-bottom-least-optimizer` (P3).

### `is_valid_lattice` is dead code that always returns false

- **Source:** `Compiler/src/abstractlattice.jl:281-283`.
- **What:** for every lattice but `JLTypeLattice` the result is `false` for every element; no
  caller in `Compiler/src`. Deleting it, or fixing `&&` to `||`, has no runtime cost either way.
- **Lean statement:** `compiler-al-is-valid-lattice-only-jltype`
  (`isValidLatticeOnlyJLType_proven`), `compiler-al-is-valid-lattice-types` (refuted).
- **How often real inference hits it (guess):** never in the native interpreter.
- **Triage (2026-11-09): not a perf lead.** No runtime cost. It is cleanup, tracked as the
  P3 bug `compiler-al-is-valid-lattice-types`.

### `tmerge_field` is `nothing` on every default layer

- **Source:** `Compiler/src/abstractlattice.jl:139-142`, called per field at
  `Compiler/src/typelimits.jl:649`.
- **What:** on the native lattices the call always returns `nothing` after walking the layers.
  With a concrete lattice type this is likely folded at compile time, so this is only worth
  checking if `tmerge(::PartialsLattice, ...)` is compiled with a non-concrete lattice.
- **Lean statement:** `compiler-al-tmerge-field-nothing` (`tmergeFieldNothing_proven`).
- **How often real inference hits it (guess):** every `PartialStruct` field merge; the cost is
  probably zero after inlining (unmeasured).
- **Triage (2026-11-09): unverified, probably zero.** To check, run
  `code_typed(Compiler.tmerge_partial_struct, ...)` (or the `tmerge(::PartialsLattice)` method)
  with the concrete `typeinf_lattice` type and look for a remaining `tmerge_field` call. If
  it is folded to `nothing`, drop the lead.

## `Compiler/src/typelimits.jl` (tmerge and the type-size limits)

Smoke-test counts are from `difftest/compiler/typelimits_props.jl` on the pinned Julia
(1.15.0-DEV.184, f755f49a9e), seeds 1 and 2, 300 and 1500 rounds.

### Merging two identical `Conditional`s does the full merge and loses `isdefined`

- **Source:** `Compiler/src/typelimits.jl:509-538`.
- **What:** `tmerge(::ConditionalsLattice)` has no `typea === typeb` shortcut, so merging a
  `Conditional` with itself merges both field types (two recursive `tmerge`s) and then rebuilds
  the element, dropping `isdefined` (or returning `Bool` when the then and else types are equal,
  which is always the case for `@isdefined`). Work whose result is known, plus a precision loss
  that shows up as lost `nothrow` (see `bugs/typelimits-tmerge-conditional-idempotent.yaml`).
- **Lean statement:** `typelimits-tmerge-conditional-idempotent`,
  `tmergeIdempotentTypeinf_refuted`.
- **How often real inference hits it:** guess: rare for `isdefined` conditionals; the missing
  `===` shortcut is hit at every control-flow merge of an unchanged `Conditional` slot, which is
  common in loops over flags.
- **Triage (2026-11-09): precision part confirmed, the frequency guess was too high.**
  `smerge` returns early when the two VarStates are `===`, and `schanged` skips the merge when
  `new ⊑ old`. So `tmerge(c, c)` runs only when the VarStates differ in `ssadef` or
  `undef` but carry the same `Conditional`. That is a merge, not "every merge of an unchanged
  slot". The precision loss is real and causal: patching the method to keep `isdefined`
  restores `nothrow` for `f` on the pinned build (see the bug yaml). For the cost of the
  missing shortcut, count calls to `tmerge(::ConditionalsLattice)` with `typea === typeb`
  while inferring a package workload (for example a counting wrapper interpreter over the
  Base test suite or OmniPackage), before calling it a lead.

### `tname_intersect` never joins siblings

- **Source:** `Compiler/src/typelimits.jl:791-816`, called at 855.
- **What:** `tname_intersect(a, b)` only answers `a` or `b`, so two type names under a shared
  abstract parent (`Signed` and `Float64` under `Real`) are never merged by `tmerge_types_slow`.
  The union then keeps both, and the result can exceed `MAX_TYPEUNION_LENGTH`: in the smoke test
  25 of 300 `tmerge_types_slow` results were not `issimpleenoughtype`. Precision is kept, union
  size is not bounded by the limit.
- **Lean statement:** `typelimits-tname-intersect-arg`, `tnameIntersectArg_proven` (first
  conjunct).
- **How often real inference hits it:** guess: whenever abstract-typed struct families or numeric
  types of different branches meet at a merge; common in generic numeric code.
- **Triage (2026-11-09): likely intended, weak lead.** `tmerge_types_slow` is written to
  collapse union members that share a TypeName (comment at typelimits.jl:846-848). The
  ancestor case is an extension of that. Joining siblings to their common supertype
  (Signed and Float64 to Real) would lose precision to save union length. Termination does not
  depend on it: the number of TypeNames is finite, and concrete types form unions freely by
  design (`tmerge(::JLTypeLattice)`, "it's always ok to form a Union of two concrete types").
  The smoke-test elements that are not `issimpleenoughtype` are generated inputs. Before
  keeping this, measure how often `tmerge_types_slow` returns a non-simple union during real
  inference (a counter in a wrapper `AbstractInterpreter` over a package load), and whether
  those unions cause later union-splitting blowups.

### `tmerge` on `JLTypeLattice` is commutative but not associative

- **Source:** `Compiler/src/typelimits.jl:775-789` with `tmerge_types_slow` and `tuplemerge`
  (818-1022).
- **What:** on the smoke test `tmerge(JLT, a, b) == tmerge(JLT, b, a)` held in 1800 of 1800 cases,
  but `tmerge(tmerge(a, b), c) == tmerge(a, tmerge(b, c))` failed in 5 of 300 (tuples near the
  length and union limits, e.g. `Tuple{T,T} where T`, `Union{Tuple{}, CA, Tuple{Float64, Missing,
  Float64, Bool}}`, `Type{Tuple{Signed, Missing, Vararg{Bool}}}`). On `typeinf_lattice` the
  lattice-equality version failed in 124 of 1306. The order inference visits predecessors in then
  decides the inferred type, so the same method can get different code instances in different
  sessions or package load orders.
- **Lean statement:** none. A concrete Lean refutation goes through `jl_type_union` and
  `tuplemerge`, whose model uses `jl_egal` and `Std.Range` loops, both defined by well-founded
  recursion; neither `rfl` nor the kernel reduces them.
- **How often real inference hits it:** guess: only for merges of three or more large tuple or
  union types, e.g. loops that grow a tuple; rare, but each hit is a possible cache mismatch.
- **Triage (2026-11-09): real on generated inputs; the caching consequence is a hypothesis.**
  The playbook says associativity is not promised, so this matters only if the visiting
  order of predecessors differs between runs on the same code. Within one `typeinf_local`
  the order is fixed by the worklist (lowest block first), so the order cannot change for
  one method. The open question is across const-prop and IRInterp, or after an edit
  elsewhere. The measurement plan is the strongest test of the lead: precompile a package
  twice in fresh depots with different load orders of its dependencies, and diff the
  inferred return types of the external code instances in the two caches (the `pkgimg`
  tool lists code instances and rettypes). Any difference whose method has a merge of three
  or more tuple types is a hit.

### `limit_type_size` is not idempotent

- **Source:** `Compiler/src/typelimits.jl:14-33` and `_limit_type_size` 88-192.
- **What:** `limit_type_size(r, c, ...)` with `r = limit_type_size(t, c, ...)` differs from `r` in
  86 of 1500 smoke cases, all `Type{...}` nestings: `Type{Type{String}}` against `Type{String}`
  gives `Type{<:Type}`, which limits again to `Type`, a fixed point after two steps. The commented
  assertion at lines 29-31 says this stronger property is not required. Applying the limit once
  per inference round can then produce two different signatures for one call site.
- **Lean statement:** none (`typelimits-limit-type-size-self` proves only `limit(t, t) = t`).
- **How often real inference hits it:** guess: recursion on `Type{...}` arguments, uncommon.
- **Triage (2026-11-09): documented as not required.** The commented-out assertion at
  typelimits.jl:29-31 says so. The fixed point arrives after two steps, so this cannot cause
  non-termination. Note that c7738544ad (#64503, "count `Type{}` as a level in
  `is_derived_type`", 2026-10-31) changed this area after the pin. Rerun the smoke check
  on a build with that commit before doing anything else.

### Code-reading notes without a Lean statement

- `Compiler/src/typelimits.jl:889-904` (`tmerge_types_slow`): `usep` starts `true` and is only
  ever set to `true`, so `simplify[j] = !usep` is always `false` and the `if usep` branch always
  runs. A widened non-`Tuple` element is never re-checked by `issimpleenoughtype`. Since such an
  element is a `DataType` or `UnionAll` (union complexity 0 outside tuples), this only matters for
  wrappers whose type-variable bounds are big unions; probably equivalent in practice.
- `Compiler/src/typelimits.jl:350` (`issimplertype`): the `elseif typeb isa PartialStruct` branch
  is unreachable (the branch before it takes every `PartialStruct`), so the per-field `undefs`
  assertion never runs. Cosmetic.
- Triage (2026-11-09): both notes are confirmed by reading the code. With `usep` always true,
  `widen` for a pair with no shared parameters is `wr{wrapper params...}`, which is the
  wrapper. With `usep` starting false, the result would also be the wrapper (simplify then
  sees a simple wrapper and keeps it). So the output is the same, and only the dead variable
  goes. The `usep` lines come from a61d1b47a6 (2023-09). Both are cleanups, not perf leads.

## effects

Leads from the `Compiler/src/effects.jl` property pass (entries `compiler-effects-*` in
`JuliaLean/Proofs/Compiler/src/effects.lean`). Sources at `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.

### Package images drop inferred code that `is_foldable` would accept (caching)

- **Source:** `src/staticdata.c:645-652` (`effects_foldable`), used at `src/staticdata.c:946-953`.
- **What:** the serializer keeps a non-inlineable `CodeInstance`'s inferred code only when
  `effects_foldable` says it may be folded. That test requires `noub == ALWAYS_TRUE`, while
  `is_foldable(e, true)` (the test concrete and semi-concrete evaluation use,
  `Compiler/src/abstractinterpretation.jl:1071`) also accepts `NOUB_IF_NOINBOUNDS`; and it ignores
  `nortcall`. So foldable `NOUB_IF_NOINBOUNDS` code is dropped from the image, and code that calls
  `return_type` (never folded) is kept. For non-inlineable cached code, `lookup_cached_edge`
  (`Compiler/src/typeinfer.jl:1237-1265`) does not pass the source to semi-concrete evaluation in
  either case, so whether the kept code is ever used after loading is the open question; if it
  is not, the whole `effects_foldable` clause only costs image size.
- **Lean statement:** `compiler-effects-c-foldable-sync` (`cFoldableSync_refuted`,
  `cFoldable_nortcall_counterexample`); what the C test reads is `compiler-effects-c-readers`.
- **How often real inference hits it (guess):** `NOUB_IF_NOINBOUNDS` with a non-inlineable method
  is uncommon (most such methods are small `@propagate_inbounds` accessors that are inlineable and
  keep their code anyway). Measuring: count `CodeInstance`s in a large package image whose decoded
  effects have `noub == NOUB_IF_NOINBOUNDS` or `!nortcall` and are otherwise foldable.
- **Triage 2026-11-10:** the open question has a reading-based answer, and it turns this into a
  lead about image size. Since #62359 (311f373e01, first in 1.14), semi-concrete evaluation runs
  only on a `LocalInferenceResult` (`Compiler/src/abstractinterpretation.jl:1404`).
  `lookup_cached_edge` builds one from a cached `CodeInstance` only when it loads the source,
  which it does only for inlineable code (`Compiler/src/typeinfer.jl:1255-1259`). The
  `effects_foldable` clause only keeps non-inlineable code, so after a load nothing in inference
  reads what it keeps. Codegen does not need it either, because the clause only applies when
  native code exists (`native_functions`). So the lead is: delete the clause, and every
  non-inlineable foldable `CodeInstance` drops its compressed IR from the image. This is not
  measured. How to measure: (1) with the `pkgimg` tool, count the CodeInstances in the
  OrdinaryDiffEq and Plots images (current nightly) that have a `String` `inferred`, inlining cost
  `UINT16_MAX` and foldable effects, and sum their `sizeof`. (2) If the sum is more than about 1%
  of the `.ji` size, build with the clause removed and compare the `.ji`/`.so` sizes and
  `@time using` (ABBA, `timing-comparisons`). Also run `Compiler/test/irinterp.jl` and
  `test/precompile.jl` to confirm no test relies on the kept code. The clause is unchanged on
  master eb844b8ebd (`src/staticdata.c:657-664`, used at 965).

### `is_better_effects` can pick the weaker `consistent` state

- **Source:** `Compiler/src/effects.jl:226-302` (the consistent part at 228-240; earlier cited
  as 174-179, which are the bit constants), used at `Compiler/src/abstractinterpretation.jl:233`.
- **What:** when a const-prop result's return type is not better than the regular one, its
  effects are kept if `is_better_effects` says so. For `consistent` that test only checks the
  lowest condition bit, so it calls the union of both conditions better than
  `CONSISTENT_IF_INACCESSIBLEMEMONLY` (it is weaker) and misses that `CONSISTENT_IF_NOTRETURNED`
  is better than the union. Picking the weaker state can stop `adjust_effects(sv)` from refining
  `consistent` to `ALWAYS_TRUE`, which blocks concrete evaluation of callers.
- **Lean statement:** `compiler-effects-is-better-order` (`isBetterEffectsOrder_refuted`,
  `isBetterEffects_more_counterexamples`).
- **How often real inference hits it (guess):** rare; needs const-prop and regular inference to
  disagree both on the return type and on which `consistent` condition they carry.
- **Triage 2026-11-10:** the precision loss is real by construction, but no compiled code that
  shows it was found. How to measure: wrap `is_better_effects` in a counting
  `AbstractInterpreter` (or temporarily patch it with `Base.REFLECTION_COMPILER[] =
  Base.Compiler`) that records each call where its answer differs from the order "new != old and
  merge_effects(new, old) == old". Run it over a package test workload (e.g. precompiling
  StaticArrays and DataFrames). If the count is zero or a handful, close the lead and fix the
  function only for clarity.

### The word `0` means two things

- **Source:** `src/codegen.cpp:2516-2525` (`effects_ipo_reset_safe`), `Compiler/src/effects.jl:371-397`.
- **What:** codegen treats `ipo_purity_bits == 0` as "no recorded effects", but `0` is also
  `encode_effects` of a real `Effects` (all `UInt8` fields `ALWAYS_TRUE`, all `Bool` fields
  false), which is effect-free and reset-safe. Such a callee is not marked `julia.reset_safe`.
  The other way round, Julia's `decode_effects(0)` reads a `CodeInstance` that never recorded
  effects as consistent, effect-free, inaccessiblememonly, noub and nonoverlayed; it is worth
  checking that no reader decodes the bits of a `CodeInstance` that was not inferred.
- **Lean statement:** `cResetSafe_zero_word` (in `compiler-effects-c-readers`).
- **How often real inference hits it (guess):** the first case needs `nothrow`, `terminates`,
  `notaskstate` and `nortcall` all false with everything else proven; rare.
- **Triage 2026-11-10:** the codegen half is intended. Master's `effects_ipo_reset_safe`
  (`src/codegen.cpp:2524-2532` at eb844b8ebd) has the comment "0 means 'no recorded effects' and
  is treated conservatively", so the missed `julia.reset_safe` mark is a deliberate trade, and the
  case is rare. The `decode_effects(0)` half is a question for a code reading (list every reader
  of `ipo_purity_bits`/`purity_bits` and check that each one first tests that the CodeInstance
  was inferred), not a measurement. Low rank.

### `EFFECT_FREE_GLOBALLY` reads as the conditional state

- **Source:** `Compiler/src/effects.jl:176-183`, `Compiler/src/optimize.jl:86-90`.
- **What:** `EFFECT_FREE_GLOBALLY` is `ALWAYS_FALSE | EFFECT_FREE_IF_INACCESSIBLEMEMONLY`, so every
  `GC.@preserve` begin/end, `:leave`, `:pop_exception` and `:aliasscope` statement gets
  `IR_FLAG_EFIIMO`, and merging it with `EFFECT_FREE_IF_INACCESSIBLEMEMONLY` loses the condition.
  No consumer acts on it today (the flag is only read together with
  `IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM`); it is a correctness trap, not a speedup.
- **Lean statement:** `compiler-effects-effect-free-globally-collision`
  (`effectFreeIfIamoNamedStates_refuted`, `globally_merge_drops_condition`).
- **How often real inference hits it (guess):** the flag, on every `GC.@preserve`; a wrong
  result, never today.
- **Triage 2026-11-10:** not a perf lead; it stays as the P3 latent bug
  `compiler-effects-effect-free-globally-collision`. Nothing to measure.

### `adjust_effects` can weaken `nonoverlayed`

- **Source:** `Compiler/src/typeinfer.jl:659-661`.
- **What:** the `consistent_overlay` override sets `CONSISTENT_OVERLAY` without checking for
  `ALWAYS_TRUE`. Only a hand-written `Expr(:purity)` on a non-overlay method reaches it.
- **Lean statement:** `compiler-effects-adjust-consistent-overlay` (`adjustEffectsStrengthens_refuted`);
  the guarded version is `compiler-effects-adjust-spec`.
- **How often real inference hits it (guess):** never through the public macros.
- **Triage 2026-11-10:** withdrawn. No public macro reaches it (see the yaml), and overlay
  methods already start at `CONSISTENT_OVERLAY`. Nothing to measure.

## domtree

Leads from the property pass over `Compiler/src/ssair/domtree.jl` and the CFG edits in
`Compiler/src/ssair/ir.jl`. Source lines are at `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.

### ADCE keeps a full dominator tree only to answer `bb_unreachable`

- **Source:** `Compiler/src/ssair/ir.jl:815-821` (`CFGTransformState!` builds a `DomTree` when CFG
  transforms are allowed), `ir.jl:1483-1500` (`kill_edge_terminator!` updates it with
  `domtree_delete_edge!` and reads it only through `bb_unreachable`), `passes.jl:2167`
  (`adce_pass!` compacts with `IncrementalCompact(ir, true)`).
- **What:** every deleted edge pays a DSNCA update (a rebuild when the edge is a DFS-tree edge,
  else a partial `SNCA!` plus the O(n) idom pass and `compute_domtree_nodes!`), but the only
  question asked is whether the target block became unreachable. Reachability alone (for
  example `CFGReachability` in `tarjan.jl`, or a DFS numbering without SNCA state) would answer
  it. The stale-idom bug below shows that nothing reads the dominance relation of this tree.
- **Lean statement:** `compiler-domtree-delete-sound-small` (reachability stays exact) and
  `compiler-domtree-delete-stale-idom` (the dominance part can be stale with no effect).
- **How often real inference hits it (guess):** every `adce_pass!` that folds a constant branch;
  cost grows with blocks times folded branches, so large generated functions pay most.
- **Triage 2026-11-10:** confirmed by reading, and wider than stated. Nothing else reads
  `compact.cfg_transform.domtree`: `kill_edge_terminator!` (`ir.jl:1485-1494`) is the only
  user, and it asks only `bb_unreachable`. Also, `CFGTransformState!` builds the tree up front
  (`ir.jl:819-821`) for every compaction with CFG transforms enabled, that is every
  `adce_pass!`, even when no edge is ever deleted. So the cost is one `construct_domtree` per ADCE
  run, plus one update per deleted edge. A reachability check (for example `CFGReachability` from
  `tarjan.jl`, which already supports edge deletion) would answer the one question. How to
  measure, without a heavy local run first: (1) take a sampling profile (`Profile.@profile`,
  `C=true`) of precompiling one large package (e.g. OrdinaryDiffEq) on nightly. Sum the samples
  under `CFGTransformState!` -> `construct_domtree` and under `kill_edge_terminator!` ->
  `domtree_delete_edge!`, as a share of samples in `optimize`. (2) If that is more than about 1%
  of optimizer time, swap in `CFGReachability` in a branch and compare precompile time and
  sysimage build time (`Base.Compiler` timing in the `make` log). Then confirm on the PR CI TTFX
  job.

### Upstream fix #64518 makes nearly every edge deletion recompute

- **Source:** current master `Compiler/src/ssair/domtree.jl:528`, which replaced
  `on_semidominator_path` with `!dominates(domtree, to, from)`.
- **What:** the update is now skipped only for back edges (`to` dominates `from`); before, it was
  skipped whenever `from` was not on a semidominator path of `to`, which was cheaper but missed
  cases (`compiler-domtree-delete-stale-idom`). Combined with the lead above, each folded forward
  branch in ADCE now runs a partial `SNCA!` and a full `compute_domtree_nodes!`. Worth
  measuring ADCE time on functions with many constant branches before and after #64518.
- **Lean statement:** `compiler-domtree-delete-stale-idom`
  (`deleteEdgeMatchesRebuild_refuted`) shows why the old test was not exact.
- **How often real inference hits it (guess):** as above.
- **Triage 2026-11-10:** plausible, not measured. Check existing data first: perf.julialang.org
  TTFX and the Nanosoldier compile-time benchmarks for master builds on either side of 0ae93c3a14
  (merged 2026-11-06), and the PR CI TTFX job of #64518 itself. If those show nothing above noise,
  this lead folds into the one above: replacing the tree with reachability removes both costs.
  Do not optimize the delete test on its own, since the stale-idom bug shows how easy it is to
  get wrong.

### `rename_nodes!(::DomTree)` shares children vectors, and has no callers

- **Source:** `Compiler/src/ssair/domtree.jl:579-603`.
- **What:** `old_nodes = copy(domtree.nodes)` is shallow, so when `rename_bb` leaves a slot at most
  `max_new_bb` unwritten, two slots hold the same children vector and the later `map!` and
  `compute_domtree_nodes!` act on both. It also threw on kept unreachable blocks until #64518
  (`compiler-domtree-rename-keep-unreachable`). Nothing in `Compiler/src` calls it. The
  `TODO: This could be done by just renaming the domtree` at `ir.jl:820` would not save work
  as written, since only a `DFS` of the original CFG exists there, not a dominator tree; it
  pays only where a caller already holds the tree of the CFG before unreachable blocks are
  dropped. `compiler-domtree-rename-small` shows that renaming which drops unreachable blocks
  gives the same tree as a rebuild, so such a caller could use it once the sharing is fixed.
- **How often real inference hits it (guess):** never at this commit (dead code); a cleanup lead.
- **Triage 2026-11-10:** not a perf lead. It is dead code, and master eb844b8ebd still has no
  caller, after #64518 fixed it rather than removing it. Nothing to measure. It could join the
  next "remove unused functions" cleanup, like 5fdc91d4e3, unless the TODO at `ir.jl:820` is
  taken up.

## tfuncs

### `tuple_tfunc` repeats the all-constant check `builtin_tfunction` just made

- **Source:** `Compiler/src/tfuncs.jl:2315` (`is_all_const_arg`, commented "repeated from
  builtin_tfunction for the benefit of callers that use this tfunc directly") after 3259-3277.
- **What:** `tuple` is a `_PURE_BUILTINS` member, so `builtin_tfunction` has already run
  `is_all_const_arg` on the same argument types and found them not all constant before it calls
  `tuple_tfunc`. The repeat can only succeed when the dropped trailing `Vararg{Union{}}` was the one
  non-constant argument. Every non-constant `tuple(...)` call pays a second walk with an
  `issingletontype` per argument.
- **Lean statement:** `compiler-tfuncs-builtin-fold` (`builtinFoldSpec_proven`: the fold falls
  through only when `isAllConstArg` returned `false`) and `compiler-tfuncs-builtin-tfunction`
  (`builtinTfunctionSpec_proven`: then `tuple` goes to `tupleTfunc` on the same argument types).
- **How often real inference hits it (guess):** on every non-constant `tuple` call, which is very
  common; the cost per call is small (one loop over the arguments).
- **Triage 2026-11-10:** real, but probably too small to see. Every tuple literal lowers to
  `Core.tuple`, so the repeat runs often. Each run is one `is_const_argtype` per argument, and
  it stops at the first non-constant one, which is usually the first argument. Measure before
  touching it: in a sampling profile (`Profile.@profile` with `C=true`) of precompiling a large
  package (e.g. OrdinaryDiffEq) on the pinned build, take the share of samples in
  `tuple_tfunc` that are in its `is_all_const_arg` call. Drop the lead if that share is below
  0.1% of inference samples. The code is unchanged on master eb844b8ebd.

### `builtin_nothrow` for the pure builtins depends on `rt` to reject a wrong argument count

- **Source:** `Compiler/src/tfuncs.jl:3243-3253`.
- **What:** not a speedup but a fragility that matters for callers that pass their own `rt`:
  `===`, `typeof`, `has_free_typevars` and `nfields` are reported nothrow for any argument count
  once `rt !== Union{}`. Only `rt` from `builtin_tfunction` makes this sound.
- **Lean statement:** `compiler-tfuncs-builtin-nothrow-dispatch` (clause 4 of
  `builtinNothrowSpec_proven`) and `compiler-tfuncs-pure-nothrow-sound`
  (`pureNothrowSound_proven`, which needs `compiler-tfuncs-arity-bottom`).
- **How often real inference hits it (guess):** never on the normal path, which passes the
  tfunc result; a lead only for external `AbstractInterpreter`s.
- **Triage 2026-11-10:** not a perf lead; drop it from the ranking. Nothing is redundant and no
  precision is lost on the normal path. It is an API fragility, which belongs in a comment on
  `builtin_nothrow` if anywhere.

## reinfer

Edge verification at package load (`Compiler/src/reinfer.jl`, `bindinginvalidations.jl`,
`cicache.jl`), from the property pass. Lines are at `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.

### Edge checks run in `codeinst.min_world`, not the validation world

- **Source:** `Compiler/src/reinfer.jl:235` (`world = initial.codeinst.min_world`), passed to
  `verify_call` and `verify_invokesig` at `reinfer.jl:298, 304, 334`; the interference cutoff at
  `reinfer.jl:814`; `promote_mi_to_current(mi, minworld, world)` at `reinfer.jl:777, 889`.
- **What:** soundness first: this is `compiler-reinfer-stale-min-world` (stale code kept when a
  method is defined between activation and verification). For load time: when the counter moved
  after activation, the full lookup runs in the old world, so its `max_world` stops at the next
  method that merely intersects the signature, the code instance is not valid in the current
  world and is recompiled although its matches are unchanged; and `jl_promote_mi_to_current`
  never sets `METHOD_SIG_LATEST_ONLY`, because it requires the counter to equal `world`.
  Checking in `validation_world` fixes both.
- **Lean statement:** `compiler-reinfer-stale-min-world`
  (`JuliaLean.Proofs.Compiler.src.reinfer.verifyMethodSound_refuted`), and
  `compiler-reinfer-promote-mi` (`PromoteMiEffect`: promotion needs the counter to equal `world`).
- **How often real loads hit it (guess):** rare; only loads that run while another task defines
  methods or loads packages.
- **Triage 2026-11-10:** the soundness half survives as `compiler-reinfer-stale-min-world` (P1).
  The load-time half is real only when the world counter moves between a package's activation
  and its `insert_backedges`. In a single-task `using`, nothing runs in that window, so the two
  worlds are equal and nothing is lost. How to measure: in a local build, count `verify_method`
  calls with `codeinst.min_world != validation_world` and how many of those end with `maxworld <
  validation_world`. Do it for `using OrdinaryDiffEq` alone, and for two packages loaded from two
  tasks at once. Expect zero for the first. Fix it with the soundness bug, not on its own.

### A method with `did_scan_source & 0x4` still checks all of its edges

- **Source:** `Compiler/src/reinfer.jl:268-269` sets `maxworld = 0`; the guard at `reinfer.jl:277`
  (`maxworld != get_require_world()`) does not skip the edge loop for 0, and the loop breaks only
  after an edge itself returns `max_valid2 == 0` (`reinfer.jl:348`).
- **What:** every lookup of such a code instance is done although the result is already a
  rejection. Testing `maxworld != 0` too (or breaking at the top of the loop) skips them; the
  code-instance children still have to be visited for the cycle bookkeeping.
- **Lean statement:** none proven; it is a reading of the mirrored model
  (`initAndProcessCallees`), and `compiler-reinfer-range-bounded` (open) is the related property.
- **How often real loads hit it (guess):** rare; needs a binding the method's source reads to
  have been replaced since the require world.
- **Triage 2026-11-10:** real, but rare. The bit is set only when a global that the image's
  code reads was redefined after the require world. Then the whole code instance is rejected
  anyway, and the extra lookups only make that rejection slower. Measure only with a workload
  that redefines globals (Revise sessions): count code instances that take the
  `did_scan_source & 0x4` branch during a `using` after a Revise edit. Low rank.

### The binding-edge check has no fast path

- **Source:** `Compiler/src/reinfer.jl:307-319` calls `binding_access_range_at` for every binding
  edge; `binding_changed_since_require_world` (`reinfer.jl:110-113`) skips the walk when the latest
  partition starts by the require world and is a leaf.
- **What:** with that fast path the edge's range is the latest partition's, which starts at or
  before `require_world` (the starting `minworld`) and runs to `typemax`, so the edge cannot
  narrow the result and the walk can be skipped. Ian's note on #62452 measured 11x more binding
  edges validated at load after that PR.
- **Lean statement:** `compiler-reinfer-binding-queries` (`BindingQueriesBoth`). Its second half,
  `BindingFastPathAgrees`, proves that the fast path's answer is the walk's, given the promise
  `LeafRangePromise` of `binding_access_range` (the access range for a newest leaf partition starts
  no later than the partition), which the difftest checks on every case. So the same skip is sound
  for the binding-edge check: when the fast path holds, the walk would return a range that starts
  at or before `require_world`.
- **How often real loads hit it (guess):** common; every image code instance that reads a global
  has one binding edge per global read.
- **Triage 2026-11-10:** the strongest load-time lead of this wave. Inference pushes a
  `Core.Binding` edge for every `GlobalAccessInfo` (`Compiler/src/stmtinfo.jl:795-797`), so the
  count is real. The skip is sound given `LeafRangePromise`, which the difftest checks and which
  `binding_changed_since_require_world` already relies on. What is not known is how much time
  the walk costs, since `binding_access_range_at` on an unchanged leaf partition may already be
  cheap. How to measure: (1) count binding edges, and time the binding branch of
  `verify_method`, during `using OrdinaryDiffEq` and `using Plots` on a local master build. Use a
  temporary counter and `time_ns` around the `binding_access_range_at` call, or a Tracy zone
  next to the existing `CC: INSERT_BACKEDGES` one. (2) If that branch is more than about 5% of
  INSERT_BACKEDGES, add the fast-path check before the walk and compare `@time_imports` for
  those packages, ABBA with 10 or more runs each (`timing-comparisons`). Then confirm on the PR
  CI TTFX job (load phase). The code is unchanged on master eb844b8ebd.

### Lookup memo keyed by object identity

- **Source:** `Compiler/src/reinfer.jl:705-725` (`workspace.lookups::IdDict`).
- **What:** two edges with equal but distinct signature objects (`==` types built separately)
  miss the memo and repeat `_methods_by_ftype`. Whether images share these objects is not known.
- **Lean statement:** `compiler-reinfer-lookup-memo` (`VerifyCallLookupMemo`: a hit needs the same
  signature object id).
- **How often real loads hit it (guess):** unknown; measure the hit rate (the difftest saw 48 hits
  in 17000 cases, on synthetic edges).
- **Triage 2026-11-10:** unproven, and possibly empty. The serializer deduplicates types through
  the type cache, so equal signatures in one image may already be the same object. How to
  measure: in `verify_call`, record each miss together with the `hash` of `sig`. During `using
  OrdinaryDiffEq`, count misses whose hash, and then `==`, matches an earlier key. If that is
  under 1% of lookups, drop the lead. An `==`-keyed memo costs a type comparison per lookup, so it
  only pays if many misses are equal.

## unionsplit

From the property pass over `Compiler/src/typeutils.jl` (union splitting) and
`is_union_split_eligible` (`Compiler/src/abstractinterpretation.jl:395-397`). Two soundness bugs
found in the same pass are in `bugs/compiler-unionsplit-typesubtract-unionall-diagonal.yaml` and
`bugs/compiler-unionsplit-immutable-typevar-member.yaml`; they are not perf leads.

### The split limit does not bound the number of method lookups

- **Source:** `Compiler/src/typeutils.jl:291-316` (cost), `Compiler/src/abstractinterpretation.jl:395-411`
  (one `findall` per split signature), docstring `Compiler/src/types.jl:295-297`.
- **What:** the cost is `2 * prod(lengths) / max(2, largest length)`, so the largest union counts
  as 2 whatever its size. With the default `max_union_splitting = 4`, one 20-member union argument
  costs 2 and is split into 20 signatures, each with its own method-table lookup and its own
  inference; a 3-member and a 2-member union cost 4 and give 6. The docstring says the limit is
  the number of union-tuples expanded. A bound on `prod(lengths)` (or a docstring that describes
  the cost) would make the limit mean what it says.
- **Lean statement:** `compiler-unionsplit-cost-spec` (`unionsplitcostSpec_proven`, the closed
  form) and `compiler-unionsplit-split-count-exceeds-limit` (`splitCountWithinLimit_refuted`).
- **How often real inference hits it (guess):** any call whose argument is a long union, mostly
  from declared field or argument types (inferred unions are limited to 3 members by
  `MAX_TYPEUNION_LENGTH`); unmeasured.
- **Triage 2026-11-10:** the extra lookups are intended. #37378 ("remove union-split limit for
  linear signatures") made one long union always split, and the comment at
  `Compiler/src/typeutils.jl:285-290` explains the cost. So the lead is a docstring fix
  (`compiler-unionsplit-split-count-exceeds-limit`, P3) plus a question to measure: do the
  6-or-more-signature splits that the cost allows cost noticeable inference time? How to
  measure: in a wrapper `AbstractInterpreter` (or a temporary counter in
  `abstract_call_gf_by_type`), record `length(split_argtypes)` and the time of each split call
  while precompiling a package with wide declared unions (e.g. DataFrames, or CSV with its
  `Union{Missing, ...}` columns). Then look at the tail above 4. Act only if signatures past
  `max_union_splitting` account for a visible share of inference time.

### More precise argument types can turn splitting off

- **Source:** `Compiler/src/typeutils.jl:291-316`.
- **What:** the cost counts members, so narrowing `Union{Integer,Nothing}` to
  `Union{Int8,Int16,Nothing}` raises it (4 to 6 for two such arguments) and the call is no longer
  split. The split decision is monotone in the member counts (proven) but not in the type order.
  Inference results for the narrower call can be less precise than for the wider one.
- **Lean statement:** `compiler-unionsplit-cost-subtype-monotone`
  (`unionsplitEligibleSubtypeMonotone_refuted`); the member-count version is
  `compiler-unionsplit-cost-monotone` (`unionsplitcostMonotone_proven`).
- **How often real inference hits it (guess):** rare; needs two or more union arguments near the
  limit.
- **Triage 2026-11-10:** real, but it is how the cost was designed, so the yaml was withdrawn as
  a bug. Whether it costs precision depends on the callee, and no case was built where the
  narrower call infers a worse return type. How to measure: in the same wrapper interpreter,
  for each call that is not split only because the cost is above the limit, also infer the
  split version, and count the calls where the split result is strictly better (`⊏`). If that
  is rare, close the lead.

### A `UnionAll` around a `Union` is never split

- **Source:** `Compiler/src/typeutils.jl:306` and `:360` (`isa(ti, Union)`).
- **What:** an argument such as `Union{Vector{T}, Set{T}} where T` counts 1 in the cost and is
  never split, though splitting it into its rewrapped members would be sound when the variable
  occurs in one member only. Splitting it when the variable is diagonal in a member would be
  unsound (the same mechanism as `compiler-unionsplit-typesubtract-unionall-diagonal`), so a fix
  needs that check.
- **Lean statement:** `compiler-unionsplit-cost-spec` and `compiler-unionsplit-switchtupleunion-lattice`
  (`unionLenOf`/`partsPure` read only a top-level `Union`).
- **How often real inference hits it (guess):** rare; such types come from declarations, not from
  `tmerge`.
- **Triage 2026-11-10:** one correction to the soundness condition. The example has `T` in both
  members, and splitting it is still sound. Splitting a union under a `where` is
  set-theoretically exact. What breaks it is only Julia's diagonal rule: a member in which the
  variable becomes diagonal on its own (two covariant uses, while the whole type also has an
  invariant one) changes meaning. Such types are less rare than the guess says, because
  `AbstractVecOrMat` and `StridedVecOrMat` are `UnionAll`s over a `Union`, and declared fields of
  those types are common. How to measure: count call sites whose argument types include a
  `UnionAll` with a `Union` body during a package workload (e.g. precompiling LinearAlgebra-heavy
  code such as StaticArrays or Optim). For a sample of them, compare the inferred return type
  with and without splitting.

### No order dependence in the split decision

- **Source:** `Compiler/src/typeutils.jl:291-316`, `:326-392`.
- **What:** not a lead but a negative result: the cost, and so `is_union_split_eligible`, is the
  same for every permutation of the arguments, and `switchtupleunion` emits the cartesian product
  in a fixed order (last argument slowest). Argument order cannot change whether a call is split.
- **Lean statement:** `compiler-unionsplit-cost-order-independent`
  (`unionsplitcostOrderIndependent_proven`), `compiler-unionsplit-switchtupleunion-lattice`.
- **How often real inference hits it (guess):** n/a.

## Code loading: cache-file selection (base/loading.jl), from the loading difftest

Source lines are `base/loading.jl` at `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. No Lean
property is registered for these yet; the evidence is the source and the model in
`JuliaLean/base/loading.lean`, checked by `difftest/base/loading.jl`.

### Candidates with equal mtimes are tried in directory-listing order

- **Source:** `base/loading.jl:1384` (`readdir(dir, sort = false)`) and `1401-1415`
  (`sortperm(...; lt=sort_lt, rev=true)`, stable).
- **What:** candidates are ordered by (has pkgimage, mtime), newest first. The sort is stable and
  `rev=true` keeps the input order among equal keys, so caches of one package with the same mtime
  (a depot unpacked from a tarball or container layer, a copied depot, a file system with coarse
  timestamps) are tried in the order the file system enumerates the directory. Which one is
  checked first, and which one `compilecache_freshest_path` returns when several are valid,
  depends on that order. Sorting ties by file name would make the choice reproducible across
  machines.
- **Lean statement:** none registered. The model's `sort_cachefile_candidates!` takes the
  listing from `readdir_unsorted`, and the difftest feeds it Julia's own listing order.
- **How often real inference hits it (guess):** only in depots whose cache files share mtimes;
  the cost is extra stale checks (a header parse each), not a wrong load, since every candidate
  is validated before use.

### `compilecache_freshest_path` and `require` can pick caches from different depots

- **Source:** `base/loading.jl:1452-1461` (`find_all_in_cache_path` sorts all depots' candidates
  together by mtime) versus `1447-1450` (`lazy_cachefile_candidates`, used by
  `_require_search_from_serialized` at `2425-2427`, goes depot by depot).
- **What:** when two depots hold a valid cache for the same package, `isprecompiled` and the
  precompile driver look at the newest one across depots, while `using` loads the first valid one
  in `DEPOT_PATH` order. Both are valid, so nothing wrong is loaded, but the driver may validate
  (and `touch`) a file that loading never reads.
- **Lean statement:** none registered.
- **How often real inference hits it (guess):** shared or stacked depots (a system depot plus a
  user depot, CI caches) with the same package compiled in both.

### `cachepath_cache` is read but never filled by `compilecache_freshest_path`

- **Source:** `base/loading.jl:2210` and `2250` use `get(() -> find_all_in_cache_path(...),
  cachepath_cache, key)`, which does not store the listing.
- **What:** a caller that passes an empty `cachepath_cache` (for example repeated `isprecompiled`
  calls) lists and stats every dependency's cache directories again on each call. The precompile
  driver fills the dictionary itself (`base/precompilation.jl:2685-2687`), so it is not affected.
- **Lean statement:** none; the model now mirrors the `get` (it used to store the listing).
- **How often real inference hits it (guess):** callers outside the driver that check many
  packages; a few `readdir`/`stat` calls per dependency per call.

## loading

Leads from the proof pass over the cache-file checks (`JuliaLean/Proofs/base/loading/cachefile.lean`).
Source lines are `base/loading.jl` at `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.

### A directory include goes stale when its `st_size` changes but its listing does not

- **Source:** `base/loading.jl:2700-2702` records `UInt64(filesize(path))` for a content-tracked
  directory, and `4837-4842` compares it before the `join(readdir(path))` hash.
- **What:** the docstring (`2766-2772`) defines a directory's content as its listing, but the
  check also compares the directory's `st_size`. ext4 and XFS never shrink a directory, and
  sizes differ between file systems, so the same listing is rejected with `:fsize_changed`: a
  needless recompile, and a relocated depot on another file system is never fresh although
  `isrelocatable` says yes. Skipping the size for directories fixes both.
- **Lean statement:** `DirectoryIncludeContentOnly` refuted by
  `directoryIncludeContentOnly_refuted`; `AnyIncludesStalePrecise` (proven) shows that the size
  is the only extra input. Reproduced: `repro/compiler-loading-dir-include-size.jl`
  (`bugs/compiler-loading-dir-include-size.yaml`).
- **How often real inference hits it (guess):** packages with `include_dependency(dir)` whose
  directory once held more files, or relocated depots; rare, but each hit is a full recompile.

### Precision of the include check is otherwise exact

- **Source:** `base/loading.jl:4802-4851`.
- **What:** `AnyIncludesStalePrecise` proves that unchanged includes (same recorded mtime, or
  same size and hash) are never rejected, including the `trunc(digits=6)` and `1e-6` mtime
  tolerances (an exact mtime match is never stale). No needless recompile comes from this
  function beyond the directory case above.
- **Lean statement:** `AnyIncludesStalePrecise`, `mtime_not_stale_self`.

### Triage 2026-11-10 (cache-file selection and loading leads)

Skeptical pass; master source read at eb844b8ebd, reproducers run on master 4c0e39dde6.

- **Directory include size** (`compiler-loading-dir-include-size`, P2): survives. Reproduces on
  pinned, nightly, 1.13.3 and master. Measurement plan: count registered packages that pass a
  directory to `include_dependency` (julia-code-search for `include_dependency(` with
  `@__DIR__`/`joinpath` and no file extension, then check by hand); for one of them, copy a
  precompiled depot from ext4 to tmpfs and count `:fsize_changed` reasons with
  `Base.isprecompiled(pkg)` plus a `reasons` dict, before and after a patch that skips the
  size for directories.
- **Depot shadowing** (`compiler-loading-depot-shadow-recompile`, P2): survives, niche (only
  manifest `path =` entries). Measurement plan: the reproducer already counts one recompile per
  session; time `using` of a mid-size dev'd package in sessions 2 and 3, with and without a
  patch that prefers the depot holding `modspec.path`.
- **Equal mtimes tried in listing order**: plausible, small cost. Each extra candidate is one
  header parse. Measurement plan: unpack a depot from a tarball (equal mtimes), run
  `JULIA_DEBUG=loading julia -e 'using Pkg'` and count "Rejecting" lines and `stale_cachefile`
  calls, then repeat with ties sorted by file name. Expect a few header parses per package
  at most; drop the lead if under 1 ms per `using`.
- **`compilecache_freshest_path` and `require` choose by different rules**: no wrong load
  (both validate). Measurement plan: with two stacked depots that both hold valid caches, run
  `Pkg.precompile()` as a no-op and use `strace -f -e trace=openat,utimensat` to count files the
  driver opens or touches that `using` never reads. Low priority.
- **`cachepath_cache` not filled**: real (the `get` does not store). Measurement plan: time 100
  calls of `Base.isprecompiled` over every package in a 300-package manifest with an empty dict
  against one dict reused across the calls, and count `stat` calls with strace. Callers outside
  the precompile driver are rare, so expect a small total.

## escape

`Compiler/src/ssair/EscapeAnalysis.jl` at f755f49a9e41. The escape queries are proven monotone
along `⊔ₑ` and `⊑ₑ` (`compiler-escape-has-*-monotone`), so none of the leads below is a
soundness problem; they are about work the analysis does.

### `getaliases` scans every index and finds only direct children of the root

- **Source:** `Compiler/src/ssair/EscapeAnalysis.jl:474-490`, called from every
  `propagate_escape_change!` (lines 720-732).
- **What:** each escape change on a value in a non-singleton alias set scans the whole
  `parents` vector (nargs + nstmts entries) and keeps only the indices whose parent is the root.
  After `union!` joins two sets of rank 1 or more, members two levels down are missed until a
  later `find_root!` on them compresses the path. The change still reaches them: in the last
  pass every alias statement calls `isaliased` (path compression) and pushes `x ⊔ₑ y` to both
  ends, so a missed member is updated and the pass reports a change. That costs extra passes.
  Keeping a member list per root (or compressing every path once per pass) would make the
  lookup proportional to the set size and avoid the extra passes.
- **Lean statement:** none yet; the model reproduces the behaviour (difftest compares the
  union-find state and `getaliases` of every index). The soundness half is the
  `compiler-escape-has-*-monotone` entries.
- **How often real inference hits it (guess):** only when EA runs (`refine_effects!` with
  pending mutable allocations, and finalizer inlining), on IR with phi or pi chains over
  allocations. The scan is O(n) per change, so O(n²) per pass on large functions.

### `⊑ₑ` slow path is dead in the analysis

- **Source:** `Compiler/src/ssair/EscapeAnalysis.jl:246-300`; its only caller in the
  analysis is `has_all_escape(x) = ⊤ ⊑ₑ x` (line 156).
- **What:** `⊤ ⊑ₑ x` always returns at the first two fast-path tests, so `has_all_escape(x)` is
  exactly `x === ⊤` (`compiler-escape-has-all-escape-monotone`, first conjunct). Writing it as
  `x === ⊤` states that directly. The slow path has the bugs in
  `bugs/compiler-escape-sqsub-transitive.yaml` and `bugs/compiler-escape-sqsub-respects-eq.yaml`,
  which matter only to external callers.
- **Lean statement:** `JuliaLean.Proofs.Compiler.src.ssair.EscapeAnalysis.hasAllEscape_iff`.
- **How often real inference hits it (guess):** no runtime cost to speak of; a clarity lead.

### Shared `Liveness` sets are mutated in place

- **Source:** `propagate_liveness_change!`, lines 746-763; `⊔ₑ` (lines 344-352) and the
  keyword `EscapeInfo` constructors share one `BitSet` between several values.
- **What:** a liveness push on one value also marks every value that shares its set as live
  at that pc. This is conservative, but the result depends on the order in which sets were
  shared, and finalizer inlining reads `Liveness` (`passes.jl:1853-1857`) to place the
  finalizer call, so extra live points can move the inlined finalizer later or block it.
- **Lean statement:** none; the model reproduces it through its heap of `Liveness` sets.
- **How often real inference hits it (guess):** whenever a value with `BOT_LIVENESS` is joined
  with another value's information, for example a field value receiving its object's
  information in `escape_new!` (line 1201): the field then shares the object's set, and the
  field's own liveness pushes land in the object's set. Common, but the extra points are
  usually places the object is live anyway.

### Triage 2026-11-10 (escape leads)

- **`getaliases` scans every index**: plausible, the strongest of the three. EA runs only for
  `refine_effects!` with mutable allocations and for finalizer inlining, so total cost is
  bounded by how often EA runs at all. Measurement plan: run `Compiler/test/EscapeAnalysis.jl`
  and a few large functions with many allocations through phi or pi chains (for example a
  generated function with 500 `Ref`s merged through a loop) under `Profile`, and report the
  share of samples in `getaliases` and the number of EA passes until convergence, with and
  without a per-root member list.
- **`⊑ₑ` slow path is dead in the analysis**: confirmed by code reading on master (only
  `has_all_escape` calls it, and it returns at the fast path). A clarity change, not a speedup.
  No measurement needed.
- **Shared `Liveness` sets mutated in place**: unproven effect. Measurement plan: patch
  `propagate_liveness_change!` to copy a set before writing to a shared one, then diff the IR
  that finalizer inlining gives for the finalizer tests in `Compiler/test/inline.jl` and for
  `code_typed` of a sample of Base functions with finalizers. If no IR changes, drop the lead.

## slot2ssa

### Linear `in` on vectors in `compute_live_ins` and `iterated_dominance_frontier`

- **Source:** `Compiler/src/ssair/slot2ssa.jl:520, 524-526` (`p in bb_defs` for every
  predecessor, `elem in bb_uses` for every worklist entry) and line 272 (`succ in defs`, with
  `defs = liveness.def_bbs` a `Vector{Int}`).
- **What:** each test scans a vector, so for one slot the liveness walk costs about
  (predecessor edges) × (def blocks + use blocks), and the IDF about (edges visited) × (def
  blocks). `construct_ssa!` runs both once per slot with uses, so a large function with many
  locals that are assigned in many blocks pays a quadratic factor. A `BitSet` (as already used
  for `processed`, `visited` and `extra_liveins`) would make each test constant time. The
  results cannot change: `compiler-slot2ssa-pruned-small` pins `def_bbs`, `live_in_bbs` and the
  phi blocks as sets, independent of how membership is tested.
- **Lean statement:** `compiler-slot2ssa-pruned-small` (`prunedPhisSmall_proven`) for what the
  results must be; the cost is from reading the model (`livePreds`, `liveWorklist`,
  `idfSuccLoop` use `Array.contains`).
- **How often real inference hits it (guess):** every function that reaches the optimizer;
  noticeable only for generated or very long functions (hundreds of blocks and slots).

### `first_insert_for_bb` rescans the block for every inserted node

- **Source:** `Compiler/src/ssair/slot2ssa.jl:614, 645, 654, 728, 742` call
  `first_insert_for_bb(code, cfg, block)` (`Compiler/src/ssair/ir.jl:160-177`, a scan from the
  block start) for each PhiC, phi, undef phi, π node and upsilon.
- **What:** the result for a block is the same at every call (the new nodes go to
  `ir.new_nodes`, not `code`, the phis in `code` are only edited in place, and the calls for a
  block happen before the renaming rewrites its own statements), so it could be computed once
  per block. The cost is (nodes inserted into a block) × (leading phi statements
  of the block), small unless lowered code has many phis, which it normally does not.
- **Lean statement:** none; from reading the model (`phicLoop`, `phiInsertLoop`, `renameVisit`).
- **How often real inference hits it (guess):** every phi insertion, but each scan usually stops
  at the first statement; likely not measurable.

### Value phis for slots read only by `@isdefined`

- **Source:** `Compiler/src/ssair/slot2ssa.jl:119-126` (`fixemup!` renames `@isdefined(x)` to
  the undef part only) with lines 637-657 (a value phi is inserted for every IDF block).
- **What:** `scan_entry!` counts `@isdefined(x)` as a use of `x`, so a slot whose only reads are
  `@isdefined` gets live-in blocks and value phis that nothing reads; `compact!` deletes them
  later. This is why the refuted `compiler-slot2ssa-catch-loop-header` statement excludes
  `@isdefined`. Counting such reads as uses of the undef part only would avoid building and then
  deleting these phis.
- **Lean statement:** none (an exclusion in `PhisUsed`).
- **How often real inference hits it (guess):** rare; `@isdefined` on locals is uncommon outside
  macro-generated code.

### Triage 2026-11-10 (slot2ssa leads)

- **Linear `in` in `compute_live_ins` and the IDF**: plausible only for very large functions.
  Measurement plan: build generated functions with N blocks and M slots that are assigned in
  most blocks (N, M in 100, 300, 1000), time `construct_ssa!` inside `code_ircode` with
  `@timed` over repeated runs, and compare with a patch that uses `BitSet` for `bb_defs`,
  `bb_uses` and `def_bbs`. Also profile the optimizer on one real large method (a big
  JuMP or ModelingToolkit generated function) to see whether `construct_ssa!` is over 1% of
  optimizer time. Drop it if not.
- **`first_insert_for_bb` rescans**: very likely not measurable (each scan usually stops at
  the first statement). No measurement planned unless the profile above shows it.
- **Value phis for `@isdefined`-only slots**: rare, and `compact!` deletes them. No
  measurement planned.
- Not a lead but worth noting: the P0 `compiler-slot2ssa-catch-loop-header` is a correctness
  bug, not a perf lead. The fix may add a block or a phi operand per catch block that is also
  a loop header; when fixing it, check that the IR of catch blocks without loops does not change.

## cacheresult (inferenceresult.jl and the caching decisions of typeinfer.jl)

From the model and proof passes (`JuliaLean/Compiler/src/inferenceresult.lean`,
`JuliaLean/Proofs/Compiler/src/inferenceresult.lean`, difftest `difftest/compiler/cacheresult.jl`).

### A const-prop result whose key ends in `Vararg` is never reused

- **Source:** `Compiler/src/abstractinterpretation.jl:1517-1522` (the `overridden_by_const`
  flags) and `Compiler/src/inferenceresult.jl:245-248` (the lookup's match loop).
- **What:** `const_prop_call` marks position `i` as overridden when
  `argtypes[i] !== argtype_by_index(cache_argtypes, i)`. When the call's argument types end in
  `Vararg{T}` (a splat of unknown length), `pick_const_args!` puts a `Vararg{...}` at the end of
  the key, while `argtype_by_index` returns the unwrapped element type there, so the last flag
  is always `true`. On the next lookup with the same arguments, the query's last element is the
  same `Vararg`, which is not forwardable, so `is_argtype_match(..., overridden_by_const = true)`
  is `false` and the entry is skipped. Every call site with the same constant arguments and a
  splatted tail runs constant propagation again within one inference session. The same flag
  also keeps `!any(overridden_by_const)` from ever bailing out for such keys (code reading only,
  not observed). A possible fix is to compare the tail with `unwrapva` on both sides when
  computing the flag, or to compare `Vararg` elements with `is_lattice_equal` in the lookup;
  either needs a check that the cached result stays valid for the query.
- **Lean statement:** `ConstpropKeyRehits`, refuted by `constpropKeyRehits_refuted`
  (registry `compiler-cacheresult-va-tail-miss`, `bugs/compiler-cacheresult-va-tail-miss.yaml`):
  for cache argument types `[Int64, Vararg{Int64}]` the key is the same list, its flags are
  `[false, true]` (`overriddenByConstFlags` models abstractinterpretation.jl:1517-1522), and the
  lookup of that key in a cache holding only its entry returns `nothing`. The difftest op
  `cr.rehit` runs the same chain (key, flags, lookup) against the pinned Julia: 51000/51000 cases
  agree over seeds 1-3, and about 46% of the keys with a flag set are not found again (676 of
  1464). In a separate check (20000 random calls of four small methods, not kept), every miss had
  either a `Vararg` tail (1208) or a `Union{}` key position (4399); the latter come from
  `PartialStruct` arguments disjoint from the method's signature, which a real call cannot
  produce. Upstream master eb844b8ebd
  (2026-11-10) has the same lines.
- **Evidence:** `repro/compiler-cacheresult-va-tail-miss.jl`: three calls `g(1, v...)` in one
  caller leave three identical const-prop entries `[Const(g), Const(1), Vararg{Int64}]` with
  flags `[0, 1, 1]`, while three calls `h(1, v, v)` of a fixed-arity method leave one. Prints
  `REPRODUCED` on the pinned Julia (1.15.0-DEV.184 f755f49a9e), on nightly (1.15.0-DEV.304
  290d5bb5f5) and on 1.13.3. GitHub search (read-only, 2026-11-10) found no report; queries:
  "constprop_cache_lookup Vararg", "overridden_by_const", "constprop cache vararg",
  "const-prop varargs cache", "matching_cache_argtypes vararg", "pick_const_args" (issues and
  PRs). Related but different: #61953 / #61989 (length mismatch assertion for varargs `mi`).
- **How often real inference hits it (guess):** common in code that splats a collection into a
  varargs method with a constant leading argument (formatting, `tuple`/`vcat`-style helpers);
  the cost is one extra const-prop inference per such call site in a method, so it matters
  for large methods with many identical splat calls rather than per call.

### `maybe_compress_codeinfo`'s drop branch never fires for optimized sources

- **Source:** `Compiler/src/typeinfer.jl:562-580` (`transform_result_for_cache`) and
  `typeinfer.jl:595-610` (`maybe_compress_codeinfo`), called from `finish!` at
  `typeinfer.jl:151-169`.
- **What:** for an optimized result, `transform_result_for_cache` first calls
  `discard_optimized_result` with the inlining cost and returns `nothing` when it says so; only
  otherwise does it build the `CodeInfo` and store that same cost in it. `maybe_compress_codeinfo`
  then drops a `CodeInfo` that is not inlineable (`inlining_cost == MAX_INLINE_COST`) under the
  same conditions. `DiscardMatchesCompress` (proven, `compiler-cacheresult-discard-compress-agree`)
  shows the two decisions agree for the same cost, so on this path the second test is decided
  already and its `return nothing` is dead; it only acts on sources that were never optimized.
  Not a speedup (two boolean tests), but a simplification, and the two copies of the rule can
  drift apart.
- **How often (guess):** every `CodeInstance` that reaches the global cache passes the tests once.

### `is_result_constabi_eligible` runs twice per finished result

- **Source:** `Compiler/src/typeinfer.jl:120` and `typeinfer.jl:148` in `finish!`.
- **What:** `const_flag = is_result_constabi_eligible(result)` is computed at line 120 and again,
  with nothing changed in between, at line 148. For a `Const` result with foldable effects each
  call walks the constant with `count_const_size`, which for a struct constant visits up to 256
  bytes of fields. Removing the second call saves one walk per such result. Code reading only;
  the cost of one walk was not measured.
- **How often (guess):** once per inferred method whose result is a foldable `Const`; small next
  to inference itself.

### The local cache keeps optimized source that the global cache drops

- **Source:** `Compiler/src/typeinfer.jl:548-560` (`transform_result_for_local_cache`, with the
  comment "this must perform the exact same operations as transform_result_for_cache to avoid
  introducing soundness bugs") and `typeinfer.jl:562-588`.
- **What:** both drop the source of a constant-ABI result (`may_discard_trees` and
  `is_result_constabi_eligible`), but only the global path also drops optimized source that is
  not inlineable (`discard_optimized_result`). So the local cache holds on to the
  `OptimizationState` of every non-inlineable result for the rest of the inference session. This
  is not a soundness issue (keeping more source never changes a result), and it contradicts the
  comment only in that direction. Code reading only; not modelled (`transform_result_for_local_cache`
  reads the `OptimizationState`).
- **How often (guess):** every const-prop result of a non-inlineable method; the memory is
  released when the `InferenceCache` is.

### Triage 2026-11-10 (cacheresult leads)

- **Vararg-tail const-prop key never reused** (`compiler-cacheresult-va-tail-miss`, now P3):
  measured, and small on Base. `typeinf_frame` with a fresh `NativeInterpreter` on 40000 Base
  method instances (pinned Julia) made 39775 const-prop entries; 66 had a Vararg tail and 16
  repeated an earlier Vararg-tail key (0.04%). The "common" guess above was too high. Next
  measurement, if anyone wants it: the same count over the method instances in a package
  image (for example the `precompile` workload of a string-formatting heavy package), and time
  inference with and without the fix. Drop the lead if duplicates stay under 1%.
- **`maybe_compress_codeinfo` drop branch**: a simplification, no speedup to measure.
- **`is_result_constabi_eligible` twice**: real by reading (the two calls are still on master).
  Expected cost is tiny. Measurement plan: count the calls during a sysimage build and time
  `count_const_size` on its largest constants; drop if total is under 10 ms.
- **Local cache keeps optimized source**: memory, not time. Measurement plan: after
  `typeinf_frame` of a large method, compare `Base.summarysize` of the inference cache with a
  patch that applies `discard_optimized_result` in the local path too. Must also confirm the
  kept source is never read back (inlining of a local const-prop result reads it), or the patch
  changes inlining.

## inlining

From the model and property passes of `Compiler/src/optimize.jl`, `Compiler/src/ssair/inlining.jl`
and the threshold logic of `Compiler/src/typeinfer.jl` (models `JuliaLean/Compiler/src/optimize.lean`,
`JuliaLean/Compiler/src/ssair/inlining.lean`; properties `JuliaLean/Proofs/Compiler/src/optimize.lean`,
`optimize/Cost.lean`, `optimize/Encoding.lean`, `ssair/inlining.lean`). Three leads are also
registry refutations with reproducers; the others are hypotheses only.

### Large thresholds wrap and make methods uninlineable (refuted, P2)

- **Source:** `Compiler/src/typeinfer.jl:531-541` (`cost_threshold += params.inline_tupleret_bonus`,
  `+= 19*default`, `+= 4*default`).
- **What:** with `inline_cost_threshold = typemax(Int)`, which GPUCompiler sets to force inlining
  (JuliaLang/julia#60121, closed unmerged), the threshold of a method returning a non-concrete
  `Tuple` becomes `typemax(Int) + 250 < 0`, and that of an `@inline` method `-20`. A negative
  threshold returns `MAX_INLINE_COST` after the first statement, so exactly the methods the setting
  should inline are never inlined. `repro/compiler-inlining-threshold-overflow.jl` shows a two-line
  callee inlined with default parameters and kept as a call with `typemax(Int)`, on the pinned
  Julia, nightly and 1.13.3.
- **Lean statement:** `ThresholdAtLeastDefault`, refuted by `thresholdAtLeastDefault_refuted`; the
  ordinary range is `InlineCostModelDeclared` (proven for parameters up to 2^56), and
  `threshold_wraps` shows `2^59` already wraps.
- **How often real inference hits it (guess):** every method with a Union-of-tuples or abstract
  `Tuple` return, and every `@inline` method without a dispatch-tuple signature, under GPUCompiler
  or another interpreter with a typemax threshold. Never with the default parameters.

### `inline_cost_clamp` maps finite costs above 3968 to "not inlineable" (refuted, P2)

- **Source:** `Compiler/src/optimize.jl:131-137`, `src/ircode.c:1234-1264`.
- **What:** the 8-bit encoding tops out at 3968 (byte `0xfe`); every cost from 3969 to 65534
  encodes to `0xff`, which decodes to `MAX_INLINE_COST`. So with any `inline_cost_threshold` above
  3968 the effective threshold is 3968, silently. The "use a couple billion instead of typemax"
  workaround suggested on #60121 runs into this: `repro/compiler-inlining-clamp-finite-to-max.jl`
  with a threshold of `10^9` inlines a callee of cost 3000 but not one of cost 5000. Since
  `discard_optimized_result` drops the IR of `MAX_INLINE_COST` methods, a call-site `@inline` may
  then find no source either.
- **Lean statement:** `ClampFiniteStaysFinite`, refuted by `clampFiniteStaysFinite_refuted`.
  `InlineCostClampSpec` (proven) gives the rest of the clamp's contract, from the exhaustive facts
  in `optimize/Encoding.lean` (rounding up by at most 1/32 below 3969, monotone, exact below 64,
  `enc(dec(b)) == b`).
- **How often real inference hits it (guess):** never with default parameters; for raised
  thresholds, every callee costing more than about four dynamic calls.

### `llvmcall` always costs `UNKNOWN_CALL_COST`, and its guard is dead (refuted, P3)

- **Source:** `Compiler/src/optimize.jl:1816-1823` with `Compiler/src/tfuncs.jl:52,329`.
- **What:** `maxarg` of `llvmcall` is `INT_INF = typemax(Int)`, so `nargs <= maxarg + 1` compares
  with the wrapped `typemin(Int)` and is false. Every `llvmcall` gets cost 20 instead of 10, and
  the `f === Intrinsics.llvmcall` test is never reached. Intrinsics are the only callees there
  with `INT_INF`; builtins with it go through `find_tfunc`.
- **Lean statement:** `LlvmcallTableCost`, refuted by `llvmcallTableCost_refuted`;
  `repro/compiler-inlining-llvmcall-cost.jl`.
- **How often real inference hits it (guess):** every `llvmcall`; matters only near the threshold.

### `ifelse(c, x, x)` with a global constant is not folded

- **Source:** `Compiler/src/ssair/inlining.jl:1807-1808` (`stmt.args[3] === stmt.args[4]`).
- **What:** the "identical branches" rewrite compares the two operands by identity, but at the
  inlining pass two reads of the same global are two SSA values (`%3 = Main.T1; %4 = Main.T1`), so
  `Core.ifelse(c, T1, T1)` with a non-inlineable constant `T1` (a 100-element tuple) is never
  rewritten, and the final code still contains the `ifelse` (pinned Julia, `code_typed`). The same
  call on an argument (`ifelse(c, x, x)`) is folded. The decision depends on how the operand is
  spelled, not on its value.
- **Lean statement:** `EarlyInlineSpecialCaseSpec` (proven) shows the rewrite fires exactly when
  `args34Egal` holds; the SSA-renaming effect is outside the model (checked on the pinned Julia
  only).
- **How often real inference hits it (guess):** rare; needs the same global (or two equal
  non-inlineable constants) on both sides.

### A `Const` result with a non-inlineable value skips the special-case rewrites

- **Source:** `Compiler/src/ssair/inlining.jl:1772-1773` (`is_inlineable_constant(val) || return
  nothing` inside `if isa(type, Const)`).
- **What:** when the inferred type is a `Const` whose value is not an inlineable constant,
  `early_inline_special_case` returns `nothing` before the `compilerbarrier`, `ifelse` and
  `task_result_type` rewrites, which do not need the constant at all. Proven in the model
  (`EarlyInlineSpecialCaseSpec`, second clause). Not shown in Julia: in the cases tried, inference
  widened such globals to their type, so the inferred type was not a `Const`.
- **Lean statement:** `EarlyInlineSpecialCaseSpec`.
- **How often real inference hits it (guess):** unknown; a hypothesis.

### Cost-model facts that hold (no lead)

- The `IR_FLAG_*` constants are distinct single bits, the bits below `NUM_IR_FLAGS` are the three
  call-site flags, and the C definitions match (`IrFlagsDistinct`); only the bit-15 comment is
  stale (`compiler-inlining-rsiimo-reserved-comment`, P3).
- `inline_cost_model(ir, ...)` equals `MAX_INLINE_COST` above the threshold and
  `inline_cost_clamp(sum of statement_costs!)` otherwise (`CostModelClosedForm`), so it is
  independent of statement order for branch-free bodies (`CostModelOrderIndependent`), never
  decreases when statements are appended (`CostModelAppendMonotone`, no sign assumption), and is
  `MAX_INLINE_COST` for any body with a `try` (`EnterNeverInlineable`).
- Order dependence through errors: with the one-argument `typeassert` bug
  (`compiler-inlining-typeassert-one-arg`), an expensive statement before the bad one hides the
  `BoundsError` behind the early exit, so whether inference fails depends on statement order.
- `statement_cost` of a global store `p = val` (a `BindingPartition` `p`, from the global-write
  reformulation, `optimize.jl:1446-1447`) is 3; its right side is never an `Expr`, so the
  `3 + statement_cost(rhs)` sum that would wrap for `inline_nonleaf_penalty = typemax(Int)`
  (`statementCost_global_assign_wraps`) is not reached.

### Triage 2026-11-10 (inlining leads)

- **Clamp maps finite costs above 3968 to never-inline** (`compiler-inlining-clamp-finite-to-max`,
  P2): the most important of these now. GPUCompiler sets `inline_cost_threshold =
  Int(MAX_INLINE_COST)` for `always_inline = true` (JuliaGPU/GPUCompiler.jl#741), and the
  reproducer shows a cost-5000 callee stays a call at that threshold. Measurement plan: compile
  the kernels of GPUCompiler's test suite and a few KernelAbstractions kernels through a
  `GPUInterpreter` with `always_inline = true` (code_typed only, no GPU needed), and count
  `:invoke` statements left, with and without a clamp that saturates finite costs at 3968.
- **Threshold wraps at typemax(Int)** (P3): known, #60121 closed unmerged, and GPUCompiler no
  longer passes typemax. Fix it with saturating additions together with the clamp. No
  measurement needed.
- **`llvmcall` charged 20, not 10** (P3): effect only near the threshold. Measurement plan:
  count methods in a package that uses `llvmcall` (SIMD.jl, VectorizationBase) whose cost is
  within 10 per llvmcall of the threshold. Expect few.
- **`ifelse(c, x, x)` on a global not folded** and **`Const` with non-inlineable value skips
  rewrites**: hypotheses with no shown effect on real code. Measurement plan for both: a
  sysimage-wide count of the shapes in optimized IR (`Core.ifelse` with two identical
  GlobalRef operands; calls whose inferred type is a non-inlineable `Const`). Drop if fewer
  than a handful.
