# `statement_cost` reads `ex.args[3]` of every `typeassert` call (Compiler/src/optimize.jl:1861),
# but unlike the memoryref cases it does not check `length(ex.args) >= 3` first. A call
# `Core.typeassert(x)` with one argument stays in the IR (inferred `Union{}`), so computing the
# inlining cost of any function containing it throws a BoundsError. `code_typed` fails, and a
# call of the function prints "Internal error: during type inference" and runs uninferred.
const CC = Base.Compiler
id = "compiler-inlining-typeassert-one-arg"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
g(x, c) = c ? Core.typeassert(x) : 1
ir, = only(Base.code_ircode(g, (Int, Bool)))
i = findfirst(st -> Meta.isexpr(st, :call) && length(st.args) == 2 &&
                    CC.singleton_type(CC.argextype(st.args[1], ir)) === Core.typeassert,
              ir.stmts.stmt)
println("statement ", i, ": ", ir.stmts.stmt[i])
direct = try
    CC.statement_or_branch_cost(ir.stmts.stmt[i], i, ir, ir.sptypes, CC.OptimizationParams())
    "no error"
catch e
    sprint(showerror, e)
end
println("statement_or_branch_cost: ", first(direct, 120))
typed = try
    code_typed(g, (Int, Bool))
    "no error"
catch e
    sprint(showerror, e)
end
println("code_typed(g, (Int, Bool)): ", first(typed, 120))
ok = startswith(direct, "BoundsError") && startswith(typed, "BoundsError")
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
