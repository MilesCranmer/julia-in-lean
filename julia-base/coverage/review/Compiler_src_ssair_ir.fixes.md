# Fixes for the review of Compiler_src_ssair_ir

| line | name | response |
|---|---|---|
| 14 | cfg_insert_edge! | Fixed with a general proof. `compiler-domtree-cfg-insert-edge` (`CfgInsertSpec` in `domtree/General.lean`) covers every array of blocks and all integers `f`, `t`. It states the `BoundsError` when either is not a block. Otherwise `t` is appended to the successors of `f` and `f` to the predecessors of `t`, both when `f == t`, and nothing else changes. The row lists only that entry. The todo `compiler-domtree-cfg-edit` is removed, since this entry and the next replace it. |
| 21 | cfg_delete_edge! | Fixed with a general proof. `compiler-domtree-cfg-delete-edge` (`CfgDeleteSpec`) states three outcomes: the `BoundsError` for a non-block; the `TypeError` from the `::Int` assertion when `f` is not a predecessor of `t`, or `t` is not a successor of `f`; otherwise the removal of the first occurrence of each, with nothing else changed. |
| 1453 | kill_edge! | Still bounded; general `compiler-domtree-kill-edge` stays todo. The family now includes two chains, where the recursion goes five and three levels deep, and 25 more CFGs of 4 to 9 blocks. That raises the depth cap but does not remove it. |

Checks: as in `Compiler_src_ssair_domtree.fixes.md` (build, AUDIT OK, difftest 60000/60000).
