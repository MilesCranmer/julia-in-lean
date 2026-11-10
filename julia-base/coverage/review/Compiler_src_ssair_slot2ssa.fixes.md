# Response to the review of Compiler/src/ssair/slot2ssa.jl

Both HOLLOW rows now have entries that pin the method's behaviour, and the side note on
`construct_ssa!` (that `ssaPropsOK` alone pins little) is answered by the same new entry. Writing
the stronger statement found a new miscompile, `compiler-slot2ssa-arg-entry-loop`, and showed
that the earlier `compiler-slot2ssa-pruned-small` hides it. Both are described below.

Model changes, in `JuliaLean/Compiler/src/ssair/slot2ssa.lean`:

* `fixemup!` now takes the slot filter and the renaming as parameters, as the Julia method does.
  `rename_uses!` passes "every slot" and `renames[slot_id(x)]`, so its behaviour is unchanged.
* New `fixupUses!`, which mirrors `fixup_uses!` (Compiler/src/ssair/slot2ssa.jl:151-155).
* `constructSsa!` is split into `constructSsaBody!` (everything before line 880) and the final
  `domsort_ssa!` call, so that the checks can see the IR `domsort_ssa!` gets. The composition is
  the old definition; `slot2regParts_snd` states it.

No other area's files changed, except `CompilerDiff.lean` (new `fixup` op).

| line | function | new entry | what is now pinned |
|---|---|---|---|
| 335 | domsort_ssa! | `compiler-slot2ssa-sem-small` | `Sem.lean` defines what an IR does: it runs the IR on symbolic values, logs each call as a term built from its arguments, and lets an oracle decide each `Main.c` branch. On every input of `ssa-small` (about 15800) and every oracle of three outcomes, the IR `domsort_ssa!` gets and the IR it returns make the same calls in the same order and end the same way, and neither gets stuck. A run is stuck on an unknown node, on an SSA value read before its definition ran, on a phi with no edge for the block control came from, on a phi that is not at the start of its block, and on falling off the last block. `domsort_ssa!` must also keep every new node. A `domsort_ssa!` that returns `return 0` fails on every input whose code makes a call. One that sends a goto, a fall-through or a phi edge to the wrong block fails on the inputs whose blocks make different calls (the patterns give each block its own calls). The reviewer asked for "a block permutation with the same statements". This statement is about behaviour instead, which is what the permutation is for; it does not check statement identity block by block. |
| 151 | fixup_uses! | `compiler-slot2ssa-fixup-uses-small` (proven), `compiler-slot2ssa-fixup-uses-isdefined` (refuted) | Now modelled (`fixupUses!`), not excluded. It is checked exhaustively on every pair of 37 lowered statements over two slots, both `IR_FLAG_NOTHROW` flags and three new values (16428 inputs, `Fixup.lean`). For a value other than `UNDEF_TOKEN`: no node is inserted, each use statement becomes `substReads` of itself (a definition written from the meaning: every read of the slot replaced by the value, and `@isdefined` of the slot becomes `true`), every other statement is unchanged, and afterwards `scan_slot_def_use` finds no use of the slot, with the other defs and uses unchanged. For `UNDEF_TOKEN`: only `throw_undef_if_not(:x, false)` nodes are inserted, one before each use. The refuted entry: with `UNDEF_TOKEN`, a use `@isdefined(x)` becomes `true`, because line 153 always passes `ssa => true`. That is P3, because the only caller is the disabled branch. Reproducer: `repro/compiler-slot2ssa-fixup-uses-isdefined.jl`. The difftest has a new `fixup` op that calls `Compiler.fixup_uses!` on generated statements, CFGs, flags, static parameters and use lists. |

Rows the review marked FAITHFUL, with what changed:

* 550 `construct_ssa!`: the reviewer noted that `ssa-small` alone pins little. `sem-small` checks,
  on the same inputs, that the lowered code (with slots) and the IR `construct_ssa!` hands to
  `domsort_ssa!` do the same thing. A renaming that turns slot reads into constants now fails.
  This part has a condition: x is a local, or no block jumps back to block 1. Without that
  condition it is false, which gives the new bug below. `fixemup!` and `fixup_slot!` are now
  `modelled` rows with these entries.
* 494 `compute_live_ins` (and through it `compiler-slot2ssa-pruned-small`): **the earlier spec had
  the same mistake as the code.** `Spec.blockOfStmt 0 = 1` counts the argument def as a def at
  the top of block 1, before every use. That is right only when block 1 has no predecessor
  except the virtual 0. When a back edge enters block 1, a use in block 1 is reached from that
  edge before any def, so block 1 is live-in. `compute_live_ins` leaves it out, and so did the
  spec, so the proof passed. I did not change the spec. Its statement text and note now say
  which convention it uses and point to the bug. A reviewer may want this row downgraded: the
  proof shows agreement with a convention, and the convention is wrong in the case that
  matters.

New finding, `compiler-slot2ssa-arg-entry-loop` (refuted, P2, wrong result):
`constructSemAll_refuted` gives the counterexample. When block 1 is a loop header and the loop
assigns an argument, block 1 gets no phi. Every iteration then reads `Argument(n)`. Lowering
avoids this shape for source code, because it copies an assigned argument into a new slot at
statement 1. A generator that returns a `CodeInfo` can make it:
`repro/compiler-slot2ssa-arg-entry-loop.jl` returns 1 instead of 4 (4 with `--compile=min`) on the
pinned Julia, nightly and 1.13. No duplicate was found; the queries are in the bug yaml.

`ssa-small` and the IDF, heap and renumber entries are unchanged.

The bounded `IdfSmall` and `PrunedPhisSmall` range over `cfgsUpTo3`: the 564 CFGs of 1 to 3 blocks plus the domtree area's lowering-shaped 3-block CFGs (`lower3`). The domtree area's `branchCFGs` (4 to 9 blocks) are not kernel-checked here, because of cost. Measured at one Lean thread under a 12 GB cap: `idfOK` takes 12 s and 3.2 GB on a 6-block CFG and runs out of memory after 41 s on the 7-block chain; on the 9-block `compiler-domtree-delete-stale-idom` CFG, 1/1024 of `prunedOK` (512 runs) and 504 of the 986410 `idfOK` orderings each run out of memory, about 0.1 s and 25 MB per run, so that CFG alone would take tens of hours.
