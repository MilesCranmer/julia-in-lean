# Response to the review of Compiler/src/utilities.jl

The HOLLOW row now has two new entries. The statements and proofs are in
`JuliaLean/Proofs/Compiler/src/inferenceresult/Exact.lean` (registered as `exactUtilityEntries`).
The earlier entry `compiler-cacheresult-count-const-size-bound` is kept unchanged. The model was not
changed. Both new entries are proven, and `scripts/audit.sh` ends with `AUDIT OK`.

The statements give the answers of the calls `count_const_size` makes as hypotheses of the form
`Gives m v` ("every run of `m` that returns, returns `v`"). These calls are `ismutable(x)`, the
layout facts of `typeof(x)`, the fields of `x`, the layout facts of each inline field value, and the
recursive counts.

| line | function | new entry | what is now pinned |
|---|---|---|---|
| 37 | count_const_size | `compiler-cacheresult-count-const-size-exact` | Every branch. A `Type`, `TypeName` or `Symbol` counts 0. A mutable `GenericMemory`, `String` or `SimpleVector` is too large (`MAX_INLINE_CONST_SIZE + 1`). A `Module`, `Method` or `CodeInstance` counts 8 (`sizeof(Ptr{Cvoid})`). Any other mutable object with a non-`const` field is too large. An `isbits` value counts its size. Every other object counts `capSize(base + Σ fieldAdd)`. Here `base` is `sizeof(typeof(x))` when `count_self` and 0 otherwise. A field adds 0 when it is undefined or an inline pointer-free value, and its recursive count otherwise. `capSize(t)` is `t` up to the limit and `MAX_INLINE_CONST_SIZE + 1` above it. The proof shows that the loop's early exit at the first partial sum over the limit gives the same answer as capping the total. A version that always returns 0 fails the `isbits`, `Module` and sum clauses. |
| 37 | count_const_size | `compiler-cacheresult-count-const-size-self-mono` | Monotonicity in `count_self`, which the review noted was unstated. With the same answers from the calls it makes, every result of `count_const_size(x, false)` is at most every result of `count_const_size(x, true)`. |

The FAITHFUL row 77 (`is_inlineable_constant`) was not changed.
