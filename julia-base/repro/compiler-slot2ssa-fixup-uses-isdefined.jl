# fixup_uses! (Compiler/src/ssair/slot2ssa.jl:151-155) renames every use of a slot to `ssa` and
# always says the slot is defined (`ssa => true`), also when `ssa` is UNDEF_TOKEN. A use
# `@isdefined(x)` then becomes `true` for a slot with no value. Every other read of x gets a
# `throw_undef_if_not(:x, false)`. The function's only caller is the disabled `if false` branch
# of construct_ssa!, so no compiled code is affected today.
const CC = Base.Compiler
id = "compiler-slot2ssa-fixup-uses-isdefined"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)

g(x, y) = x
ci = copy(first(code_lowered(g, (Any, Any))))
code = Any[nothing, Expr(:isdefined, Core.SlotNumber(2))]
stmts = CC.InstructionStream(2)
for i in 1:2
    stmts.stmt[i] = code[i]; stmts.type[i] = Any; stmts.flag[i] = CC.IR_FLAG_NULL
end
cfg = CC.CFG([CC.BasicBlock(CC.StmtRange(1, 2), Int[0], Int[])], Int[])
ir = CC.IRCode(stmts, cfg, CC.DebugInfoStream(stmts.line), Any[], Expr[], CC.VarState[])
CC.fixup_uses!(ir, ci, ir.stmts.stmt, [2], 2, CC.UNDEF_TOKEN)
println("@isdefined(x) after fixup_uses! with UNDEF_TOKEN: ", repr(ir.stmts.stmt[2]), " (expected false)")
println("new nodes: ", ir.new_nodes.stmts.stmt)

println(ir.stmts.stmt[2] === true ? "REPRODUCED $id" : "NOT REPRODUCED $id")
