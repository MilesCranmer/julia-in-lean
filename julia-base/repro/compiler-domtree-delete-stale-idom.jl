# domtree_delete_edge! can leave the dominator tree different from a rebuild from scratch.
# On_semidominator_path (Compiler/src/ssair/domtree.jl:554-573) follows the semidominators of
# `from` and misses a semidominator path through it, so the update is skipped.
# The CFG has the shape compute_basic_blocks gives: block 1 falls through, the two-successor
# blocks are `GotoIfNot` or `:enter` branches `[dest, next]`, and 5 and 9 are catch blocks with
# the virtual predecessor 0.
const CC = Base.Compiler
id = "compiler-domtree-delete-stale-idom"
succs = [[2], [5, 3], [5, 4], [7, 5], [9, 6], [7], [5, 8], [8, 9], [6]]
zp = [1, 9, 5]
n = length(succs)
preds = [i in zp ? [0] : Int[] for i in 1:n]
for j in 1:n, s in succs[j]
    push!(preds[s], j)
end
blocks = [CC.BasicBlock(CC.StmtRange(i, i), preds[i], copy(succs[i])) for i in 1:n]
cfg = CC.CFG(blocks, Int[])
domtree = CC.construct_domtree(blocks)
println("is_parent(9, 6) = ", CC.is_parent(domtree.dfs_tree, 9, 6),
        ", on_semidominator_path(9, 6) = ", CC.on_semidominator_path(domtree, 9, 6))
CC.cfg_delete_edge!(cfg, 9, 6)
CC.domtree_delete_edge!(domtree, blocks, 9, 6)
fresh = CC.construct_domtree(blocks)
println("preds of block 6 after deleting 9 -> 6: ", blocks[6].preds)
println("updated idom(6) = ", domtree.idoms_bb[6], ", rebuilt idom(6) = ", fresh.idoms_bb[6])
println("updated dominates(5, 6) = ", CC.dominates(domtree, 5, 6),
        ", rebuilt dominates(5, 6) = ", CC.dominates(fresh, 5, 6))
println(domtree.idoms_bb[6] == 2 && fresh.idoms_bb[6] == 5 ? "REPRODUCED $id" : "NOT REPRODUCED $id")
