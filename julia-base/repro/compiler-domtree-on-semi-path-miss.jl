# on_semidominator_path(domtree, x, y) answers false although x lies on a semidominator path
# from semi(y) to y (Compiler/src/ssair/domtree.jl:550-573). Same CFG as
# compiler-domtree-delete-stale-idom; the DFS preorder is the identity.
const CC = Base.Compiler
id = "compiler-domtree-on-semi-path-miss"
succs = [[2], [5, 3], [5, 4], [7, 5], [9, 6], [7], [5, 8], [8, 9], [6]]
zp = [1, 9, 5]
n = length(succs)
preds = [i in zp ? [0] : Int[] for i in 1:n]
for j in 1:n, s in succs[j]
    push!(preds[s], j)
end
blocks = [CC.BasicBlock(CC.StmtRange(i, i), preds[i], copy(succs[i])) for i in 1:n]
domtree = CC.construct_domtree(blocks)
D = domtree.dfs_tree
pre(b) = D.to_pre[b]
semi(b) = domtree.snca_state[pre(b)].semi
println("to_pre = ", D.to_pre, ", semi by block = ", [b == 1 ? 0 : semi(b) for b in 1:n])
# The path 4 -> 7 -> 8 -> 9 -> 6: its inner blocks 7, 8, 9 all have preorder numbers above pre(6).
path = [4, 7, 8, 9, 6]
onpath = all(i -> path[i+1] in blocks[path[i]].succs, 1:length(path)-1) &&
         all(b -> pre(b) > pre(6), path[2:end-1]) && pre(4) == semi(6)
println("4 -> 7 -> 8 -> 9 -> 6 is a semidominator path from semi(6): ", onpath)
res = CC.on_semidominator_path(domtree, 9, 6)
println("on_semidominator_path(9, 6) = ", res)
println(onpath && res == false ? "REPRODUCED $id" : "NOT REPRODUCED $id")
