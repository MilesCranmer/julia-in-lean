# Response to the review of Compiler/src/ssair/inlining.jl

Each HOLLOW row now has a new entry that states every outcome of the function as an `iff`, so the
ordinary case and the branches the review found missing are pinned. The statements are in the
"Exact decisions" section of `JuliaLean/Proofs/Compiler/src/ssair/inlining.lean` and are
registered in that file's `entries`. The row's earlier entries are kept. The model did not change.

All 5 new entries are proven, and `scripts/audit.sh` ends with `AUDIT OK`.
`early_inline_special_case`, `handle_cases!` and `inline_const_if_inlineable!` are in the model
difftest (`difftest/compiler/inlining.jl`). It was re-run after this change and agreed on every case
(see the header). `resolveTodoDecision` and `semiconcreteDecision` are still not in the driver: they
need a call result and an inlining state. Their `@inline`/`@noinline` docstring examples were run
end to end on the pinned Julia earlier (header of `difftest/compiler/inlining.jl`).

| line | function | new entry | what is now pinned |
|---|---|---|---|
| 860 | resolve_todo | `compiler-inlining-resolve-todo-exact` | There are three iffs. `ConstantCase` exactly when there is a local result and it is a constant, so returning compileable instead now fails. Inline exactly when there is a non-constant local result, inlining is on, the call site is not `@noinline` and `src_inlining_policy` accepts the source. Without a local result, always compileable. The ordinary case is also stated directly. With no call-site annotation and a generator that can run (or none), a `CodeInfo` is inlined exactly when its cost is not `MAX_INLINE_COST`, a compressed source exactly when its byte is not `0xff`, and an `IRCode` always. So "inline only at `@inline` call sites" now fails. The edge bookkeeping and the returned `InliningTodo` IR are still not modelled. The row keeps its "decision only" note. |
| 1517 | semiconcrete_result_item | `compiler-inlining-semiconcrete-exact` | Inline exactly when inlining is on, the call site is not `@noinline`, the method is not declared `@noinline` unless the call site is `@inline`, and the generator can run. Otherwise it uses a compileable specialization, and never a constant. The ordinary case (unannotated call, method not `@noinline`) is stated as inlining. |
| 1578 | handle_cases! | `compiler-inlining-handle-cases-exact` | Each outcome outside the single-case branch is now an iff. It pushes `UnionSplit(handled_all_cases, fully_covered, ...)` exactly when there is a case or all cases are handled and `atype` and every signature are `DataType`s. It gives up exactly when one of those is not a `DataType`. It adds `flag \| flags_for_effects(joint_effects)` exactly when there is no case and not all cases are handled. A function that always gives up on several cases now fails the first clause. |
| 1699 | inline_const_if_inlineable! | `compiler-inlining-const-if-inlineable-exact` | The result is an equation: `(true, flag)` for a `Const` with an inlineable value, else `(false, flag \| IR_FLAGS_REMOVABLE)`. Also, for every mask disjoint from `IR_FLAGS_REMOVABLE`, the new flag agrees with the old one on it. So setting `IR_FLAG_INBOUNDS` or `IR_FLAG_NOINLINE` now fails. |
| 1766 | early_inline_special_case | `compiler-inlining-early-special-case-exact` | The `compilerbarrier`, `ifelse` and `task_result_type` rewrites are now iffs. Their precondition `EarlyPre` says three things: inlining is on, the result is not a `Const` whose value cannot be inlined, and the constant case does not apply. This is what the body checks before it reaches them (inlining.jl:1779-1795). So a function that never performs a rewrite now fails, and the registry's "exactly" now holds for these clauses too. |
