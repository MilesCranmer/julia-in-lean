# Fixes for the review of Compiler/src/abstractlattice.jl

Response to `Compiler_src_abstractlattice.tsv` (FAITHFUL 40, HOLLOW 20). The review file is
unchanged. Proofs: `JuliaLean/Proofs/Compiler/src/abstractlattice.lean`. All entries below are
proven; the build and `scripts/audit.sh` ran on the build machine.

| line | name | fix |
|---|---|---|
| 13, 22, 33, 44, 55, 66, 77, 96 | `is_valid_lattice_norec` | New entry `compiler-al-norec-owner` (`NorecOwner`): `is_valid_lattice_norec(𝕃, x)` holds exactly when `eltOwner x = some (layerKind 𝕃)`. `eltOwner` is a table written from the layer docstrings (`abstractlattice.jl:6-91`), not from the method bodies: types to JLTypeLattice, Const/PartialTypeVar to ConstsLattice, and so on. `fun _ _ => false` now fails, for example on `Int` with JLTypeLattice. Rows now list `compiler-al-norec-disjoint,compiler-al-norec-owner`. |
| 32, 43, 54, 65, 76, 95 | `widenlattice` | Strengthened `compiler-al-widenlattice-terminates`. The result `L'` must also satisfy `layers L = L :: layers L'`, where `layers` lists the layer stack through each struct's `parent` field. A version that returns `JLTypeLattice()` instead of `𝕃.parent` fails, e.g. on `PartialsLattice(ConstsLattice())`. |
| 153 | `⊑(::JLTypeLattice)` | Strengthened `compiler-al-sqsub-jltype-preorder` with an unconditional clause: on two types, `sqsubJLType n E (.ty x) (.ty y) = issub n E x y`, the same computation as `a <: b`. This is the docstring's "equivalent to subtyping" (`abstractlattice.jl:149`). An always-true `⊑` fails. The preorder part still assumes SubReflexive/SubTransitive, and the entry's note now says that known corner cases break transitivity. |
| 161 | `⊏` | New entry `compiler-al-strict-part` (`SqsubStrictPart`). If `a ⋢ b`, `a ⊏ b` returns false from the same state without asking `b ⊑ a`. If `a ⊑ b`, it returns `!(b ⊑ a)` from the state that `a ⊑ b` left. An always-false `⊏` fails the second clause. The row lists `compiler-al-strict-irreflexive,compiler-al-strict-part`. |
| 189 | `has_nontrivial_extended_info` (generic) | Strengthened `compiler-al-nontrivial-extended-info` with a fifth clause: for every slot wrapper and every LimitedAccuracy, the result is `false` on every lattice, with the state unchanged. Returning true for them now fails. The docstring and note give the callers: abstractinterpretation.jl:1263 widens first, and tfuncs.jl:2322, typelimits.jl:693 and abstractinterpretation.jl:3507 use the answer to decide whether to keep a PartialStruct field. |
| 215 | `is_const_prop_profitable_arg` (generic) | Strengthened `compiler-al-const-prop-profitable` with the same clause: slot wrappers and LimitedAccuracy give `false` on every lattice. |
| 232 | `is_const_prop_profitable_arg(::ConstsLattice)` | Mirror: the model now has the `isa(val, Method)` and `isa(val, CodeInstance)` tests, as `typeOf val == Core.Method` / `Core.CodeInstance` (both concrete with no subtypes; the objects are `Val.mutableRef`). Property: the clause for mutable values now pins the result to `hasConstfields E v` instead of covering only the false case, so returning false for a mutable Const with const fields fails. The always-profitable clause covers Symbol, Type, Method and CodeInstance. The difftest generator gained a Const of a Method and of a CodeInstance (seed 1: 7 `isConstPropProfitableArg` cases on them), and the rerun is 100% (see below). The "not representable" notes are removed from rows 215-242. |
| 283 | `is_valid_lattice(::JLTypeLattice)` | Strengthened `compiler-al-is-valid-lattice-only-jltype`: on JLTypeLattice the result is `true` for every type and `false` for every non-type. A version that returns false for `Int` on JLTypeLattice fails. |

Difftest after the model change (pinned Julia 1.15.0-DEV.184 f755f49a9e, 20000 cases each):
seed 1 AGREE 19959/19959 (41 unmodelled), seed 2 19951/19951 (49), seed 3 19947/19947 (53). All
unmodelled cases are `tmeet` cases, with the same counts as the run before the change.

Reproducer `compiler-al-is-valid-lattice-types` was rerun and printed REPRODUCED on pinned
f755f49, 1.13.3 and nightly 290d5bb5f5.
