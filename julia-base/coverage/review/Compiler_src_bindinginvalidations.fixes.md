# Fixes for the review of `Compiler/src/bindinginvalidations.jl`

Responses to the HOLLOW rows of `Compiler_src_bindinginvalidations.tsv` (review commit 1416952).

## bindinginvalidations.jl:10, `foreachgr`

The model no longer uses a precomputed visit list. `MethodR.source` holds the statements
(`Stmt`): a statement's own binding when it is a `GlobalRef`, and the values its `userefs`
yield. `foreachgr` mirrors both loops, as recursion over the statements and over their uses. The
first part of `GlobalrefScan` states it: `foreachgr visit src = (grVisits src).forM visit` in any
lawful monad (the visits in order). The difftest now sends the statements and their `userefs`
values, built with the pinned `Compiler.userefs`.

## bindinginvalidations.jl:22, `anygr`

`anygr` mirrors its body: it stops at the first `true`, and a `GlobalRef` statement skips its
`userefs` (`continue`). The proposition is no longer a definition:

- `anygr visit src = (anyVisits src).any visit`, where `anyVisits` asks only about the statement
  itself for a `GlobalRef` statement.
- Under `GRStmtsHaveNoUses`, `anyVisits src = grVisits src`. That premise holds because `userefs`
  treats a `GlobalRef` as irrelevant (`Compiler/src/ssair/ir.jl:722-726, 738-739`). So the early
  `continue` loses nothing, and `anygr` agrees with `foreachgr`.

The difftest tallies any `GlobalRef` statement with uses (`stmt:globalref-with-uses`). None
appeared.

## bindinginvalidations.jl:40, `isgr(g)`

Excluded as `no-behaviour:`, as the review suggested. `anygr` only calls `visit` on values that
passed an `isa(…, GlobalRef)` check (lines 49 and 55), so this fallback is never reached.

## bindinginvalidations.jl:91, `invalidate_code_for_globalref!(b::Core.Binding, …)`

Marked todo. Only the no-change path is proven. A positive statement would say that when the
access key changes, every `CodeInstance` backedge is invalidated and the result is true. That
needs invariants across its three loops and the recursion through queued bindings: the effects
of `invalidate_method_for_globalref!` and `jl_maybe_reresolve_implicit` only lower `max_world`
and add events. Not done.

## bindinginvalidations.jl:167, `invalidate_code_for_globalref!(gr::GlobalRef, …)`

`convert(Core.Binding, gr)` is now modelled (`convertBinding`, after
`base/runtime_internals.jl:293-299`): the cached `gr.binding`, else the module's binding of that
name (`Heap.moduleBindings`). The wrapper is `invalidateCodeForGlobalrefGR`. The entry now states
`NoChangeAndForwards`: the no-change no-op, plus `GlobalRefForwards`, which says the wrapper runs
exactly the `Binding` method on the converted binding. Its strength still comes from the
`Binding` method's properties, and those are only the no-change path (see :91).

## bindinginvalidations.jl:175, `scan_new_method!`

Added `ScanMarksScanned` (proven). For a method with a source that is not skipped, the method
ends with bit `0x1` of `did_scan_source` set, so a no-op fails it. Still open, with no entry:
that bit `0x4` is set exactly when a visited binding changed since the require world. This needs
a loop invariant that the body's heap changes keep partitions and the require world. It is
noted on the entry.

## bindinginvalidations.jl:196, `scan_new_methods!`

Added `ScanMethodsEach` (proven). Unless it takes the incremental-precompile skip, it runs
`scan_new_method!` on exactly the `Method` items, in order (`forM` over the filtered list). The
model's loop is now a recursion over the items (`scanNewMethods.scanEach`), with the same
behaviour.
