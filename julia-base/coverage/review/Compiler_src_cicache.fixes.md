# Fixes for the review of `Compiler/src/cicache.jl`

Responses to the HOLLOW rows of `Compiler_src_cicache.tsv` (review commit 1416952).

## cicache.jl:22, `union`

The review's premise was wrong, and so was our earlier note: something does call `union` on a
`WorldRange`. `binding_access_range` calls `union(total_validity, this_partition_validity)` at
`Compiler/src/abstractinterpretation.jl:4269`. We fixed the note and the bug's `likelihood`, and
replaced the entry that rested on hypotheses no source gave:

- `compiler-cicache-union-ordered` now states `UnionCallSite`. Its hypotheses are the shape of that
  call. `this` is the validity range of the partition at `lookup_world = min_world(total) - 1`
  (`:4256`, `:4279`), so `this.max_world + 1 == total.min_world`. On every such pair
  `union(total, this)` does not throw and returns exactly the worlds of both ranges. This is
  proven (`unionCallSite_proven`). The old `UnionOrdered` is still proven but has no entry now.
- `compiler-cicache-union-hull` stays refuted. Its notes and `bugs/compiler-cicache-union-hull.yaml`
  now say it is latent: the one caller only passes touching ranges, where `union` is right. It
  stays P3.

## cicache.jl:40, `InternalCodeCache(owner, wr::WorldRange)`

Excluded as `no-behaviour:`, as the review suggested. It is `new(owner, wr)`: it only stores its
two arguments.

## cicache.jl:41, `InternalCodeCache(owner, args...)`

Now modelled as `InternalCodeCache.ofArgs` over `WorldRangeArgs` (none, one `UInt`, a `UnitRange`,
or the two fields), and `WorldRange.ofArgs` mirrors `WorldRange(args...)`. The new entry
`compiler-cicache-args-ctor` (`CacheArgsCtor`, proven) states that the view's lookups ask
`jl_rettype_inferred` for exactly the worlds of `WorldRange(args...)` in each case. The difftest's
`r.icc` cases now build the cache with each constructor form and compare `haskey`, `get` and
`getindex`.

## cicache.jl:44, `setindex!`

`jl_mi_cache_insert` is now modelled (`jlMiCacheInsert`, after `src/gf.c:803-857`). The walk
stops at `ci` itself or before the first entry that `ci` should precede (invoke, inferred, or a
smaller `max_world` when `ci` has no `next`). It links `ci` in there and unlinks an older place
of `ci`. `setindex` now returns the new chain. `compiler-cicache-setindex-owner` now states
`SetindexInserts` (proven): with matching owners, afterwards `ci` is in the chain, every other
entry is still there, and every view of the cache's owner over worlds inside `ci`'s range finds
code when `ci` has `inferred`. A `setindex!` that never inserts fails this.

There is a new difftest op, `r.iccSet`. It calls the pinned `setindex!` on fresh code instances
and on ones already in the chain, then compares the resulting chain order. Gap: the fake code
instances always have `inferred` set and no `invoke`, so the invoke and inferred stop
conditions are not exercised. `jl_push_newly_inferred` does nothing outside precompilation, so the
pushed flag is not observed.
