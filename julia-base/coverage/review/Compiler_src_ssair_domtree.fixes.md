# Fixes for the review of Compiler_src_ssair_domtree

Responses to the 30 HOLLOW rows of `Compiler_src_ssair_domtree.tsv`, one per row. "Bounded
family" below is `smallCFGs` in `JuliaLean/Proofs/Compiler/src/ssair/domtree/Checks.lean`. It
grew from 564 to 639 CFGs: 48 more 3-block CFGs in `compute_basic_blocks` order (`lower3`,
block 1 `[3, 2]`, with and without a catch block), and 27 CFGs of 4 to 9 blocks (`branchCFGs`).
Every `-small` entry now ranges over it, so each bounded statement got stronger, and none got
weaker. Rows whose only evidence is still bounded stay HOLLOW under the review's rule, and their
general statements stay `todo`. I did not try to prove Semi-NCA, DSNCA or the DFS in general
here.

General proofs added in `domtree/General.lean`: `CfgInsertSpec`, `CfgDeleteSpec`,
`DominatesWalkSpec`, `NCDSpec`, `BBUnreachableSpec`, `IsParentSpec`, `DFSWorklistSpec`.
`domtree/Basic.lean` gained `DomTreeCacheSpec` and stronger ctor, copy and resize specs.

| line | name | response |
|---|---|---|
| 89 | DFSTree | Mirror fixed. The model now has the `_worklist` field (`DFSTree.worklist`), and `DFS!` uses it as its stack, as Julia does. `compiler-domtree-dfstree-ctor` now also states `DFSTree(n)._worklist == []`. The new general entry `compiler-domtree-dfs-worklist` proves that `DFS!` leaves it empty whenever it returns, so "always starts empty" holds on every later call. Row entries: dfstree-ctor, dfs-worklist. |
| 98 | copy | Mirror fixed. `DFSTree.copy` is now `DFSTree.mk D.toPre D.fromPre D.toPost D.fromPost D.toParentPre D.worklist`, the positional constructor in the order of the Julia call. `D.copy = D` is proved by `cases D; rfl`, so swapping two arguments would break it. |
| 113 | resize! | Mirror fixed. `DFSTree.resize` returns the pair of the tree and the method's value, which is the resized `to_parent_pre` (its last call). The statement now says `(D.resize n).2 = (D.resize n).1.toParentPre`, and that `_worklist` is kept. |
| 123 | DFS! | Partly fixed; still bounded. `lower3` adds the `[3, 2]` order a forward `GotoIfNot` gives, so that order now drives the DFS. `branchCFGs` adds more such blocks (`[5, 3]`, `[4, 2]`, ...). The DFS correctness (preorder, parents, reachability) is still checked only on the bounded family, through `construct-small` and `postdom-small`. The new general `dfs-worklist` covers the stack. No general DFS proof. |
| 200 | DFS | Fixed. The row now lists `compiler-domtree-dfs-worklist`, whose statement covers `DFS(blocks, post) = DFS!(DFSTree(0), blocks, post)`. That is the whole method (line 200), and the property calls `DFS!` through it. In the model `DFS` is defined as exactly that call. |
| 257 | DomTreeCache | Fixed. It is now modelled (`DomTreeCache.new`) and no longer excluded. `compiler-domtree-dom-tree-cache` states the three empty buffers. The functions that take `cache` still use fresh values (module docstring). |
| 259 | construct_domtree | Still bounded; general `compiler-domtree-construct` stays todo. The family is stronger, as above. The point about predecessors in sorted order stands: the general statement uses `mkBlocks`, which sorts them. The insert check does build CFGs with appended predecessors, through `cfg_insert_edge!`. |
| 263 | construct_postdomtree | Still bounded; `compiler-domtree-postdom` stays todo. `branchPostRec` (6 CFGs) reaches the recursive call of `snca_compress!` in post-dominance, so two-level compression is now tested. `difftest/compiler/domtree_branches.jl` prints (update, recursion) counts of (2,1) and (3,2) for these. |
| 267 | update_domtree! | Still bounded. The partial path (`recompute_dfs = false`, `max_pre = to_pre`) is now also checked on the 27 CFGs of 4 to 9 blocks, through `insert-small`. The 9-block delete counterexample is in the family, so the partial path runs there (`delete-sound-small`). Still far from a general statement. |
| 283 | compute_domtree_nodes! | Still bounded. Children and levels are now also checked after every deletion (`delete-sound-small` got the structural clauses). |
| 318 | update_level! | Still bounded. Its output is the precondition `LevelOK` of the new general `dominates-walk` and `ncd`, so those two no longer depend on depth. The fact that `update_level!` establishes `LevelOK` is still bounded. |
| 331 | dom_edges | Fixed. The row now lists only `compiler-domtree-dom-edges`, which states the exact result for every index in general. |
| 333 | dom_edges | Fixed, as for line 331. |
| 342 | SNCA! | Still bounded; general todo. The objection is answered within the bound. `branchFwdUpd` and `branchFwdRec` (12 CFGs) take the forward update branch of `snca_compress!`, and `branchFwdRec` also takes its recursive call. `domtree_branches.jl` prints forward (update, recursion) = (1,0) and (2,1) for these. |
| 450 | snca_compress! | Still bounded; the objection is answered within the bound. The 12 forward and 12 post-dominance CFGs above reach lines 454-459. Six of each reach the recursion (`u >= last_linked` twice). So "compress only one level" or "never compress forward" now fails `construct-small` / `postdom-small` / `compress-worklist-small` on them. I did not mutate the model to confirm that each variant fails. |
| 464 | snca_compress_worklist! | Still bounded. The push branch (lines 476-479) runs exactly when `snca_compress!` recurses, and `branchFwdRec`/`branchPostRec` do recurse, so `compress-worklist-small` now covers it. The other half of the objection stands: the check still forces the variant through `sncaSemisWith` instead of `length(ancestors) <= 32`, because that test needs more than 32 reachable blocks. The model difftest covers up to 72 blocks, where Julia itself takes the worklist branch (60000/60000). |
| 490 | domtree_insert_edge! | Still bounded; `compiler-domtree-insert` stays todo. The family is stronger (`insert-small` on 27 larger CFGs, split into six kernel checks to stay under the memory cap). |
| 516 | domtree_delete_edge! | Strengthened, and the counterexample replaced. `delete-sound-small` now also states that children and levels match the idoms, and that every reachable block other than 1 has a non-zero idom that is a strict dominator by definition. An update that zeroes every idom fails this. A random search of 451511 deletions on `compute_basic_blocks`-shaped CFGs found no failure. "Keeps every old dominance" is false for Julia's update (two cases in 225899 random deletions in an earlier probe run), so it is not in the statement. The refutation `delete-stale-idom` now uses a 9-block CFG in `compute_basic_blocks` shape: fall-through from block 1, `[dest, next]` branches, catch blocks 5 and 9 with the virtual predecessor. Deleting 9 -> 6 keeps idom(6) = 2 where a rebuild gives 5. It reproduces on pinned, 1.13.3 and nightly 290d5bb5f5. The 14-block case is kept as `deleteCex14_stale`. Still true: the only caller reads `bb_unreachable` only, and no Julia function reaching this CFG was found. Still bounded overall. |
| 544 | is_parent | Fixed. The new general `compiler-domtree-is-parent` states the result for every DFS tree and pair of blocks. It is whether `to_pre[x]` is the recorded parent `to_parent_pre[to_pre[y]]`, with a `BoundsError` when `y` is unreachable. The row lists only that entry. |
| 554 | on_semidominator_path | Fixed with a direct refutation. The new `compiler-domtree-on-semi-path-miss` states the docstring promise in the direction the update needs: "true whenever x is on a semidominator path from semi(y) to y ending with x -> y". The semidominator and the path are by definition (`sdomDef`, `onSdomPathDef`). The refutation is on the 9-block CFG, edge 9 -> 6. semi(6) = 4 both in the model and by definition, 4 -> 7 -> 8 -> 9 -> 6 is such a path, and the function returns false. It has a reproducer and a bug yaml, and is fixed upstream by #64518. |
| 579 | rename_nodes! (DomTree) | Mirror improved; still bounded. The model now mirrors the in-place `map!` on a kept block's own slot that nothing overwrites, which is the visible effect of the shallow copy within the call. The module docstring says what a value model still cannot show: two slots sharing one vector after the call. The model difftest now also uses injective maps that leave slots unwritten (30% of rename cases), at 60000/60000. The "cannot arise in real compilation" point stands (no callers in Compiler/src), and the bug stays P3. |
| 609 | rename_nodes! (DFSTree) | Unchanged: bounded, reached only through the uncalled DomTree method. General `compiler-domtree-rename` stays todo. |
| 645 | dominates | Fixed with a general proof. `dominates` is `_dominates(domtree, bb1, bb2)` (lines 645-646), and `compiler-domtree-dominates-walk` proves for every tree with consistent levels, any depth, that it returns and is true exactly when bb1 is bb2 or an ancestor of bb2. Agreement with dominance by definition is then construct_domtree's property, which stays bounded (construct-small). |
| 656 | postdominates | Fixed, as for line 645 (lines 656-657 call the same `_dominates`). |
| 659 | _dominates | Fixed: `dominates-walk` is the general statement of the level walk. It is proved by induction over the walk, with no depth bound. |
| 670 | bb_unreachable | Fixed for the method. `compiler-domtree-bb-unreachable` states the whole one-line body for every tree and integer, including the `BoundsError`. Exactness with respect to reachability needs DFS correctness, which stays bounded. |
| 679 | dominated | Still bounded; no general statement. It needs a proof that the worklist walk over `children` visits each node of the subtree once. |
| 685 | iterate | Still bounded, as for line 679. |
| 699 | nearest_common_dominator | Fixed with a general proof. `compiler-domtree-ncd` covers every tree with consistent levels no deeper than its number of nodes, and `a`, `b` each a node or 0. It returns (the `@assert` holds), it returns 0 when `a == 0` or `b == 0`, and the result is the nearest common ancestor or 0 when there is none. That covers unreachable blocks and roots of different post-dominator trees. The depth bound only makes the model's fuel enough. The smoke test also checks the 0 and unreachable inputs on Julia over the family. |
| 721 | naive_idoms | Unchanged: bounded and test-only. The "returns" refutation stays, and its input does arise in compilation, as the reviewer says. |

## Checks run

- `lake build JuliaLean.Proofs.Compiler.src.ssair.domtree` on the build machine: OK. The largest
  modules are BoundedInsert (256 s), BoundedMisc (116 s) and BoundedDelete (105 s).
- `scripts/audit.sh` on the build machine: AUDIT OK, ENTRIES 8914.
- Model difftest `difftest/compiler/domtree.jl` after the model changes, seeds 1-3 with 20000
  cases each: AGREE 60000/60000 on pinned f755f49a9e.
- `difftest/compiler/domtree_smoke.jl` (Julia's functions on the 639-CFG family, with the
  stronger delete checks): no failures on pinned f755f49a9e or on nightly 290d5bb5f5. The only
  entry is the expected `delete-rebuild(info)` from the 9-block CFG.
- `difftest/compiler/domtree_branches.jl`: confirms the branch counts of all 24 compression CFGs.
- All four domtree reproducers print REPRODUCED on pinned, 1.13.3 and nightly 290d5bb5f5.
