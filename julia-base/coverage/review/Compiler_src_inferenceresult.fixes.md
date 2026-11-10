# Response to the review of Compiler/src/inferenceresult.jl

Each HOLLOW row now has a new entry that states what the method returns, position by position or
branch by branch. The statements and proofs are in
`JuliaLean/Proofs/Compiler/src/inferenceresult/Exact.lean` (registered as `exactEntries`). The
earlier entries are kept unchanged. No statement was weakened, and the model was not changed.

The new statements use three forms. `Gives m v` means every run of `m` that returns, returns `v`; a
hypothesis of that form fixes what a call inside the method answers. `Res m x` means `x` is a
result of some run of `m`; a conclusion of that form says a position holds what the named call
returns. `Via m m'` means every result of `m` is a result of `m'`.

All new entries are proven. `scripts/audit.sh` ends with `AUDIT OK` (8998 entries). The model
difftest was re-run after this pass (results in the summary of this commit).

| line | function | new entry | what is now pinned |
|---|---|---|---|
| 3 | matching_cache_argtypes(𝕃, mi) | `compiler-cacheresult-most-general-exact` | The body is `most_general_argtypes`, and the entry is stated for `matching_cache_argtypes(𝕃, mi)` itself. Every position is pinned (see line 162). A version returning `Any`s fails it. |
| 38 | matching_cache_argtypes (simple argtypes) | `compiler-cacheresult-matching-simple-via`, `compiler-cacheresult-pick-const-args-exact` | Its result is a result of `pick_const_args!` on a list that matches the argument types position by position, with `widenslotwrapper` applied: a `Conditional` widened by `widenconditional`, a `MustAlias` by `widenmustalias`, anything else kept. With the `pick_const_args!` entry, each key position is a `pick_const_arg` result on the right pair. Skipping `widenslotwrapper`, or returning `Any`s, fails it. |
| 49 | pick_const_arg | `compiler-cacheresult-pick-const-arg-prefers-given` | The branches that the earlier entry left open. For a forwardable given type that is not lattice-equal to the cache type: the result is the given type itself, except that a `PartialStruct` against a cache `Type` gives the given type when it is strictly below that type (`⊏` true), and otherwise a result of `tmeet(𝕃, given, cache)`. A version that always returns `cache_argtype` fails the first clause. |
| 64 | pick_const_args! | `compiler-cacheresult-pick-const-args-exact` | Each fixed key position `j` holds a result of `pick_const_arg` on the given type there (the given `Vararg`'s element type at and after the given `Vararg`) and on `argtype_by_index(cache_argtypes, j)`. When both lists end in `Vararg`, the last position holds `Vararg{x}` with `x` a result of `pick_const_arg(unwrapva(given_va), unwrapva(cache_va))`. Filling the key with `Any` or with the cache types fails it. |
| 100 | is_argtype_match | `compiler-cacheresult-is-argtype-match-exact`, `compiler-cacheresult-argtypes-match-exact` | For a type that is not forwardable it equals `pure (!overridden_by_const)`, so `overridden_by_const = false` gives `true`. For a forwardable type it runs exactly `is_lattice_equal(𝕃, given, cache)`, from every state. An always-false version fails the first clause. The lookup's position loop is stated as the conjunction of these answers. |
| 111 | va_process_argtypes | `compiler-cacheresult-va-process-exact` | (1) Without `isva` and without a trailing `Vararg`, the result is the argument list unchanged. (2) Each fixed position `i ≤ nargs - isva` holds `argtype_by_index(given, i)`, then the `Conditional` step and then the `MustAlias` step: a wrapper on a slot past the fixed arguments is widened when the method is varargs and the lattice has the wrapper, and is kept otherwise. (3) For a varargs method, position `nargs` holds `tuple_tfunc` of a list `ws` with `length(given) + 1 - vaLast` elements, each the matching trailing argument type after the same two widening steps. `vaLast` is the given `Vararg`'s position when fewer than `nargs` argument types end in one, and `nargs` otherwise (lines 130-133). Returning `nargs` copies of `Any` fails all three. |
| 162 | most_general_argtypes | `compiler-cacheresult-most-general-exact` | Each parameter other than a trailing `Vararg` becomes its conversion `MgConv`. The conversion takes the `unwraptv` result `a`. If `issingletontype(a)` holds, it gives `Const(singletonInstance(a))`. If `a` is a constant `Type{T}`, it gives `Const(type_parameter(a))`. Otherwise it gives `elim_free_typevars(rewrap_unionall(a, specTypes))`. A trailing `Vararg{T}` gives the conversion `e` of `T` at its own position and at every padded position up to `method.nargs`. The last position then holds `Vararg{widenconst(e)}`, as `jlVararg` builds it. With `compiler-cacheresult-most-general-length` this pins every position. |
| 209 | elim_free_typevars | `compiler-cacheresult-elim-free-typevars-choice` | A type with free type variables gives `Type` (the model's `typeTypeVal`, `Type{T} where T`) when `isType` holds, and `Any` otherwise. The entry also proves `Type ≠ Any`, so returning `Any` (or `Union{}`) for every such type fails it. |
| 217 | constprop_cache_lookup | `compiler-cacheresult-lookup-exact`, `compiler-cacheresult-argtypes-match-exact` | The answer, given what the position loop answers for each entry that reaches it (`m c`). The lookup returns the 1-based position of the first entry, in cache order, that passes every test and is not a tombstone. The tests are the same `MethodInstance`, the query's world, valid there, the query's length, `overridden_by_const` set, and the loop answering true. Failing that, it returns `missing` when a passing entry is a tombstone, and `nothing` otherwise. So a hit is pinned: an always-`nothing` lookup fails it on a one-entry cache whose entry passes. With the two `is_argtype_match` entries, an entry whose key is lattice-equal at forwardable positions and not overridden elsewhere passes the loop. |

On the reviewer's note about row 217's refutation (`compiler-cacheresult-va-tail-miss`): the review
agrees it is genuine. The `ownEntry` of the refutation is a raw `InferenceResult` rather than the
`LocalInferenceResult` that `const_prop_call` stores. As the review says, that changes only which
world range is read (`proof_worlds(cached.proof)` against `valid_worlds`), not the argument match
that fails. This was not changed.

On the caveat for the FAITHFUL row 11 (`get_nospecializeinfer_argtypes`): the caveat is correct. A
bare `@nospecialize` stores the mask `-1`, and the model takes the mask as a `Nat`. The two agree on
every bit below 32, so they differ only for methods with more than 33 arguments. Fixing it means
changing the model's mask to an `Int32` encoding and re-running the difftest. That is a model change
on a row the review accepted, so it is left for a later pass and noted here.
