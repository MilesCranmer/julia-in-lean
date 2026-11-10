# naive_idoms throws a TypeError when a block other than the entry has only the virtual
# predecessor 0: Compiler/src/ssair/domtree.jl:737 peels the first non-zero predecessor and
# asserts that there is one.
const CC = Base.Compiler
id = "compiler-domtree-naive-only-virtual-pred"
# Block 2 is a catch block whose `:enter` edge is gone: its only predecessor is the virtual 0.
blocks = [CC.BasicBlock(CC.StmtRange(1, 1), [0], Int[]),
          CC.BasicBlock(CC.StmtRange(2, 2), [0], Int[])]
println("construct_domtree idoms_bb = ", CC.construct_domtree(blocks).idoms_bb)
err = try
    CC.naive_idoms(blocks)
    nothing
catch e
    e
end
println("naive_idoms: ", err === nothing ? "returned" : typeof(err))
println(err isa TypeError ? "REPRODUCED $id" : "NOT REPRODUCED $id")
