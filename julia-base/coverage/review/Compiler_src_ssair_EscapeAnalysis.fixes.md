# Response to the review of Compiler/src/ssair/EscapeAnalysis.jl

Every HOLLOW row is fixed by strengthening its registered statement. No statement was weakened,
and no row was moved to todo. The model (`JuliaLean/Compiler/src/ssair/EscapeAnalysis.lean`) did
not change. All the work is in `JuliaLean/Proofs/Compiler/src/ssair/EscapeAnalysis.lean`. The
existing entry ids are kept, and two entries are new: `compiler-escape-join-exact` and
`compiler-escape-eq-sets`. The four former todo entries are now proven:
`compiler-escape-join-commutative`, `-join-idempotent`, `-join-absorbs` and
`-join-upper-bound-nonempty`.

The fixes use three shared descriptions:

- `AliasExact xa ya r`: the exact result of `merge_alias_info`, given as sets. `true` wins. A
  `false` argument gives back the other argument. Two `IndexableFields` give `max(xn, yn)`
  fields, where field `i` holds exactly the union of field `i` of each argument. Every other
  case gives an `Unindexable` holding exactly the union of all the sets. Neither the constant
  `true` nor a merge that adds elements satisfies it.
- `JoinExact h x y j h'`: what `x ⊔ₑ y` computes, field by field. `Analyzed` and `ReturnEscape`
  are or-ed. `ThrownEscape` and `Liveness` are `TOP` exactly when an argument's set is `TOP`,
  and otherwise hold exactly the union. `AliasInfo` satisfies `AliasExact`. No existing heap set
  changes. The result's `Liveness` is allocated when the arguments' sets are. This covers the
  `⊤`/`⊥` fast paths too.
- `eqE_iff`: `x == y` holds exactly when both have the same flags, both or neither field is
  `TOP`, and the remaining fields hold the same sets.

`scripts/audit.sh` (run through `../scripts/r`) ends with `AUDIT OK`. The escape entries are now
22 proven, 4 refuted and 0 todo. The Julia-side checks are in
`difftest/compiler/escape_props.jl`: seed 5, 20000 rounds, on the pinned 1.15.0-DEV.184
f755f49a9e. No property was violated. The only exceptions were 103 `⊏ₑ` cases that threw the
known `⊑ₑ` BoundsError.

| line | function | entry | response |
|---|---|---|---|
| 150 | has_no_escape | `compiler-escape-has-no-escape-monotone` | Three conjuncts are added. (1) `has_no_escape(x ⊔ₑ y) == has_no_escape(x) && has_no_escape(y)`, as an equation. (2) `has_no_escape(x) == !has_return_escape(x) && !has_thrown_escape(x) && !has_arg_escape(x)`. (3) Its value on all seven constructors: true on `NoEscape()` and `⊥`, false on `ArgEscape()`, `ReturnEscape(p)`, `AllReturnEscape()`, `ThrownEscape(p)` and `⊤`. The constant `false` fails on `NoEscape()`, and the constant `true` fails on `⊤`. Through (2), the value on every `x` is fixed by the three queries below. Julia check: "query join laws", "query values on constructors". |
| 151 | has_arg_escape | `compiler-escape-has-arg-escape-monotone` | Added: the exact join law (`||`). Added: the effect of `push!(x.Liveness, p)` on a non-constant set: the query becomes `has_arg_escape(x) \|\| p == 0`. Added: the values on the seven constructors, including true on `AllReturnEscape()` (`TOP_LIVENESS` holds 0) and `p == 0` on `ReturnEscape(p)`. The constant `true` fails on `NoEscape()`. Together with `compiler-escape-ignore-argescape` (removing 0 gives false), this fixes the query as `0 ∈ Liveness` on every set the analysis builds. |
| 152 | has_return_escape | `compiler-escape-has-return-escape-monotone` | Added: `has_return_escape(x ⊔ₑ y) == has_return_escape(x) \|\| has_return_escape(y)`, and the values on the seven constructors (false on `NoEscape()`, `⊥`, `ArgEscape()` and `ThrownEscape(p)`). The constant `true` fails. |
| 153 | has_return_escape(x, pc) | `compiler-escape-has-return-escape-at-monotone` | Added: the query implies `has_return_escape(x)`. Added: after `push!(x.Liveness, pc)` on a non-constant set, `has_return_escape(x, pc) == has_return_escape(x)`. Added: the constructor values. On `ReturnEscape(p)` it is `p == -1 \|\| p == pc`. It is true for every `pc` on `AllReturnEscape()` and `⊤`, and false on `ArgEscape()` at every `pc`, including `pc = 0`. The constant `true` fails. A version without the `ReturnEscape` test fails on `ArgEscape()` at 0. A version without the `-1` test fails on `AllReturnEscape()` at `pc = 5`. A version without the `pc` test fails on `ReturnEscape(p)` at `pc = p`. The join stays only an upper bound for this query, because it really is only one: `x` returned but not live at `pc`, joined with a `y` live at `pc` and not returned, gives true. |
| 154 | has_thrown_escape | `compiler-escape-has-thrown-escape-monotone` | Added: the exact join law, and the constructor values (true only on `ThrownEscape(p)` and `⊤`). The constant `true` fails on `NoEscape()`. |
| 155 | has_thrown_escape(x, pc) | `compiler-escape-has-thrown-escape-at-monotone` | Added: the exact join law `has_thrown_escape(x ⊔ₑ y, pc) == ... \|\| ...`, and that the query implies `has_thrown_escape(x)`. Added: the constructor values. On `ThrownEscape(p)` it is `p == -1 \|\| p == pc`, it is true on `⊤` at every `pc`, and false elsewhere. A version without the `-1` test fails on `⊤` at `pc = 5`, because `TOP_THROWN_ESCAPE` is `BitSet(-1)`. A version without the `pc` test fails on `ThrownEscape(p)` at `p`. |
| 159 | ignore_argescape | `compiler-escape-ignore-argescape` | Added what the reviewer asked for. Every existing heap set (`x.Liveness` included) is unchanged: `∀ r, RefOk h r → get r` is the same. The result's `Liveness` is a newly allocated set (`¬ RefOk h result.Liveness`), so nothing shares it. Also added: its elements are exactly those of `x.Liveness` other than 0, and `Analyzed`, `ReturnEscape`, `ThrownEscape` and `AliasInfo` are kept. An in-place `delete!` without `copy` breaks the first conjunct whenever 0 was in the set. Julia check: "ignore_argescape exact, x.Liveness unchanged". |
| 161 | ignore_aliasinfo | `compiler-escape-ignore-aliasinfo` | Added: the result's `AliasInfo` is the identity of `merge_alias_info` on both sides, for every `AliasInfo a`. A version that uses `Unindexable()` or an empty `IndexableFields` fails, for example on `a = IndexableFields([{LocalUse(1)}])`. Also added: `Analyzed`, `ReturnEscape` and `ThrownEscape` are kept, and so is the same `Liveness` object. Julia check: "ignore_aliasinfo merge identity". |
| 162 | ignore_liveness | `compiler-escape-ignore-liveness` | Added: the result's `Liveness` holds no element in any heap, which covers every later `push!` as well. Also added: `Analyzed`, `ReturnEscape`, `ThrownEscape` and `AliasInfo` are kept. A version that only deletes 0 fails on any `x` with another live pc. |
| 177 | merge_to_unindexable(Unindexable, IndexableFields) | `compiler-escape-merge-alias-covers` | The registered statement now includes `AliasExact xa ya (merge_alias_info(xa, ya))`. In the Unindexable/IndexableFields case (both orders), that is: the result is an `Unindexable` holding exactly `info` ∪ every field. A version that adds elements fails, and so does one that answers `true`. |
| 179 | merge_to_unindexable(info, infos) | `compiler-escape-merge-alias-covers` | The iff lemma `mem_mergeToUnindexable` is now a registered conjunct: `k ∈ merge_to_unindexable(info, infos) ↔ k ∈ info ∨ ∃ s ∈ infos, k ∈ s`. Julia check: "merge_to_unindexable exact". |
| 308 | ⊏ₑ | `compiler-escape-sqsub-strict` | Both directions are added, for each answer. `x ⊏ₑ y` returns true exactly when `x ⊑ₑ y` returns true and `y ⊑ₑ x` returns false. It returns false exactly when `x ⊑ₑ y` returns false, or both directions return true. The constant `false` fails the first iff. |
| 323 | ⊔ₑ | `compiler-escape-join-exact` (new), `-join-commutative`, `-join-idempotent`, `-join-absorbs`, `-join-upper-bound-nonempty` | `JoinExact` fixes every field of the result as described above, so the constant `⊤` fails (for example `NoEscape() ⊔ₑ NoEscape()` must not be returned). The four former todo laws are proven from it and from `eqE_iff`. Commutativity, idempotence and absorption hold up to `==` for `EscapeInfo`s whose `Liveness` sets are allocated. The ordinary-case upper bound also holds: `x ⊑ₑ x ⊔ₑ y` and `y ⊑ₑ x ⊔ₑ y` whenever neither `AliasInfo` is an `IndexableFields` with zero fields. Its proof goes through a sufficient condition for `⊑ₑ` (`sqsub_of`) that follows the body branch by branch, including the single `xinfos[length(xinfos)]` check. So the refuted `compiler-escape-join-upper-bound` really does fail only through the `⊑ₑ` BoundsError, as the reviewer said. The ordinary case is now settled as proven. Julia checks: "join exact", "join commutative/idempotent/absorbs (==)", "join upper bound, no zero-field object" (18427 cases). |
| 362 | merge_alias_info | `compiler-escape-merge-alias-covers` | `AliasExact` is registered, as at line 177. On two `IndexableFields` the result must have exactly `max(xn, yn)` fields with exactly the unions, so `true` and extra elements both fail. Julia check: covered by "join exact". |
| 1032 | from_interprocedural | `compiler-escape-interprocedural` | Added, for every non-`⊤` `x`. `ThrownEscape` holds `k` exactly when `has_thrown_escape(x)` and `k == pc`, so it is empty when `x` has no thrown escape. `Analyzed` is true. `Liveness` is a newly allocated set, and no existing set changes. Versions that always set `ThrownEscape = BitSet(pc)`, or set `Analyzed = false`, fail. Julia check: "from_interprocedural exact". |

The `==` row (line 188) was todo. It is now modelled by `compiler-escape-eq-sets` (`eqE_iff`),
which states both directions. The disjoint_set.jl review file has no rows, and no row there
changed.
