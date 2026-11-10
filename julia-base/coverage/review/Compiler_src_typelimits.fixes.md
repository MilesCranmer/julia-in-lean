# Response to the review of Compiler/src/typelimits.jl

Each HOLLOW row now has a new entry that states the method's answer on each of its branches.
The statements are in `JuliaLean/Proofs/Compiler/src/typelimits/Spec.lean`, `Layers.lean` and
`Branches.lean`, and they are registered in `typelimits.lean`. The row's earlier entries are kept.

The new statements use one pattern. `Gives m v` means "every run of `m` that returns, returns `v`".
Hypotheses of this form fix what each call inside the method answers. The conclusion then fixes
what the method answers on that branch. `Via m m'` means every result of `m` is a result of `m'`,
so a layer hands its arguments to `m'` unchanged. None of the new statements assumes
`EgalReflexive`, `SubReflexive`, `SubAnyTop` or `SubStateFree`, so the reviewer's caveat about
those hypotheses does not apply to them.

All 16 entries are proven. `#print axioms` lists only propext, Classical.choice and Quot.sound.
`scripts/audit.sh` ends with `AUDIT OK`. The model was not changed, so
the model difftest (59988/59988) still stands. New Julia-side checks of the main claims are in
`difftest/compiler/typelimits_props.jl` (seed 3, 1500 rounds, pinned Julia). None of them found a
violation.

| line | function | new entry | what is now pinned |
|---|---|---|---|
| 17 | limit_type_size | `typelimits-limit-type-size-exact` | All four results: `t` when `type_more_complex` is false, the `_limit_type_size` result `r` when `t <: r`, the result limited against `Any` when that is a supertype, else `Any`. A version that always returns `t` or `Any` fails the second and third clauses. Julia check "limit_type_size exact": 1500/1500. |
| 37 | is_derived_type | `typelimits-is-derived-type-branches` | The `t === c` case for any `===` answer, plus the Union, UnionAll (bound or body), `Type{T}`, DataType (supertype chain, or any parameter at `mindepth - 1`) and fall-through branches, with `Vararg` unwrapped. A version that returns false after the first two checks fails the Union clause. Julia check "is_derived_type Union branch": 1378/1378. |
| 228 | type_more_complex | `typelimits-type-more-complex-branches` | The TypeVar rules (lower bound, upper-bound recursion), Union against Union (or) and against a non-Union (and), the Int rule, `Type{T}` (nested, tuple depth 0 gives true, against `Union{}`), and DataType (different names, fewer parameters, the depth-1 false case, and the parameter loop: true exactly when some `tP[i]` is more complex than `cP[i + ntail]`). The bound that `limit_type_size` relies on (its result is not more complex than `compare`) is still not stated. Julia smoke test only: "limit_type_size result not more complex" holds. |
| 315 | union_count_abstract | `typelimits-union-count-abstract-exact` | The count of union members that are not dispatch elements, given what `isdispatchelem` answers. `unionlen` no longer satisfies it. Julia check: 1500/1500. |
| 316 | union_count_abstract | `typelimits-union-count-abstract-exact` | For a non-Union, 0 when `isdispatchelem` is true and 1 otherwise. The constant 1 fails. |
| 318 | issimpleenoughtype | `typelimits-issimpleenoughtype-exact` | The wrapper case (line 320) gives true whatever the union counts are. Otherwise the answer is exactly `max(unionlen, union_count_abstract + 1) ≤ 3 && unioncomplexity ≤ 3`. A version without line 320 fails the first clause. Julia check "issimpleenoughtype exact": 1500/1500. |
| 342 | issimplertype | `typelimits-issimplertype-branches`, `typelimits-issimplertype-partialstruct` | The Conditional, InterConditional, MustAlias, InterMustAlias, PartialOpaque and PartialTask branches. For a PartialStruct, the field loop: the answer is true exactly when every field is lattice-equal to its declared type, to its type name's wrapper, or to `getfield_tfunc(b, i)`. A version that skips the field checks fails. |
| 413 | tmerge_fast_path | `typelimits-tmerge-fast-path-exact` | The exact answer for every combination of `===`, the two `⊑` and the two `issimplertype` answers. A version that always answers `nothing`, or answers b without asking `issimplertype`, fails. Julia check "tmerge_fast_path exact" on typeinf, ipo and optimizer: no violations (1018-1067 cases each). |
| 427 | union_causes | `typelimits-union-causes-exact` | The result is b itself when a ⊆ b, else a itself when b ⊆ a, else a fresh set. In every case its members are exactly those of a and b. Always returning the union, or adding causes, now fails. No Julia check: the `IdSet{InferenceState}` arguments are not built by the driver. |
| 501 | tmerge(::InferenceLattice) | `typelimits-tmerge-inference-dispatch` | Two non-LimitedAccuracy elements are handed to the layer below unchanged. LimitedAccuracy(T, causes) against an incomparable b that is not `Union{}` gives LimitedAccuracy(tmerge(T, b), causes). Returning Any fails both. |
| 549 | tmerge(::InterConditionalsLattice) | `typelimits-tmerge-interconditionals` | Same-slot merge into `InterConditional(slot, then, else)`, different slots giving `Const(v)` or `Bool`, widening against other elements, and pass-through. Returning Bool fails the same-slot clause. |
| 589 | tmerge(::AnyMustAliasesLattice) | `typelimits-tmerge-mustaliases` | Same alias with `===` widened vartyps keeps the alias through `update_mustalias` with merged vartyp and fldtyp, on both alias lattices. Plus widening against a non-alias, and pass-through. |
| 702 | tmerge(::PartialsLattice) | `typelimits-tmerge-partials` | PartialStruct/Const pairs give the `tmerge_partial_struct` answer. The PartialOpaque merge covers same and different source or parent. The PartialTask merge gives `Task` when the merged fetch type is Any. Other pairs are handed down unchanged. |
| 763 | tmerge(::ConstsLattice) | `typelimits-tmerge-consts-dispatch` | Two different Consts (or PartialTypeVars) are widened and merged by JLTypeLattice. Single ones are widened, and other arguments pass through. Returning Any for two Consts fails. Julia check: 1470/1470. On the PartialTypeVar/Const(1) failure: it is caused by ⊑ in typelattice.jl:561-562, which is already filed as `compiler-tl-sqsub-widenconst-upper` (refuted, with repro). That rule puts PartialTypeVar ⊑ b only for b === TypeVar (or b === a), so no result of any join can be ⊒ both PartialTypeVar and Const(1). A second refutation through tmerge would file the same bug again. It would also need a terminating evaluation of `jl_type_union` in Lean, and the model's well-founded definitions block that. So `typelimits-tmerge-upper-bound` stays todo, and its note now names the filed bug. |
| 775 | tmerge(::JLTypeLattice) | `typelimits-tmerge-jltype-exact` | Equal concrete types give a. Concrete or `Type{T}` pairs give `Union{a, b}`. Otherwise the answer is the fast-path answer, else `tmerge_types_slow`. The upper bound of `tmerge_types_slow` itself is still todo (`typelimits-tmerge-types-slow-upper`), on its own todo row. |
| 791 | tname_intersect | `typelimits-tname-intersect-exact` | For different names, given the abstractness and height-walk answers: `nothing` when neither wrapper is abstract; `a` when the walk up from b meets a; `b` when a's ancestor at b's height is b; else `nothing`. A version that answers `nothing` past `(a, a)` and `(Any, b)` fails the ancestor clause. Julia check "tname_intersect exact": 1404/1404. |

The FAITHFUL rows (79, 330, 334, 437, 450, 509) were not changed.
