# `statement_cost` (Compiler/src/optimize.jl:1812-1822) tests `minarg + 1 <= nargs <= maxarg + 1`
# for an intrinsic. llvmcall's arity is `3:INT_INF` with `INT_INF = typemax(Int)`
# (Compiler/src/tfuncs.jl:52, 329), so `maxarg + 1` wraps to typemin(Int), the test fails, and the
# call is charged UNKNOWN_CALL_COST (20) instead of its table cost 10. The
# `f === Intrinsics.llvmcall` branch meant for it is never reached.
const CC = Base.Compiler
id = "compiler-inlining-llvmcall-cost"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
fl(x::Int32) = Base.llvmcall("%r = add i32 %0, 1\nret i32 %r", Int32, Tuple{Int32}, x)
ir, = only(Base.code_ircode(fl, (Int32,)))
iidx = Int(reinterpret(Int32, Core.Intrinsics.llvmcall)) + 1
minarg, maxarg = CC.T_IFUNC[iidx]
println("T_IFUNC arity: ", minarg, ":", maxarg, ", maxarg + 1 = ", maxarg + 1, ", T_IFUNC_COST = ", CC.T_IFUNC_COST[iidx])
cost = nothing
for (i, st) in enumerate(ir.stmts.stmt)
    if Meta.isexpr(st, :call) && CC.singleton_type(CC.argextype(st.args[1], ir)) === Core.Intrinsics.llvmcall
        global cost = CC.statement_cost(st, i, ir, ir.sptypes, CC.OptimizationParams())
        println("statement ", i, " (", length(st.args), " args): statement_cost = ", cost)
    end
end
ok = cost == 20 && CC.T_IFUNC_COST[iidx] == 10 && maxarg + 1 < 0
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
