# rename_nodes!(::DomTree, rename_bb) throws a BoundsError when it keeps an unreachable block:
# Compiler/src/ssair/domtree.jl:621-623 index from_pre and from_post with the block's preorder
# number 0, and lines 590-591 index rename_bb with its idom 0.
const CC = Base.Compiler
id = "compiler-domtree-rename-keep-unreachable"
# Block 2 has no predecessors, so it is unreachable; the identity renaming keeps it.
blocks = [CC.BasicBlock(CC.StmtRange(1, 1), [0], Int[]),
          CC.BasicBlock(CC.StmtRange(2, 2), Int[], Int[])]
domtree = CC.construct_domtree(blocks)
println("idoms_bb = ", domtree.idoms_bb, ", to_pre = ", domtree.dfs_tree.to_pre)
err = try
    CC.rename_nodes!(domtree, [1, 2])
    nothing
catch e
    e
end
println("rename_nodes!(domtree, [1, 2]): ", err === nothing ? "returned" : typeof(err))
println(err isa BoundsError ? "REPRODUCED $id" : "NOT REPRODUCED $id")
