# widenconditional and maybe_extract_const_bool disagree on a Conditional whose two branch types
# are both Union{}: the first returns Const(false), the second nothing
# (Compiler/src/typelattice.jl:242-255 and 288-292).
const CC = Base.Compiler
# Julia 1.13 has no `ssadef` field: `Conditional(slot, thentype, elsetype)`.
mkcond(slot, t, e) = hasfield(CC.Conditional, :ssadef) ? CC.Conditional(slot, 0, t, e) : CC.Conditional(slot, t, e)
id = "compiler-tl-widenconditional-extract"
c = mkcond(1, Union{}, Union{})
w = CC.widenconditional(c)
m = CC.maybe_extract_const_bool(c)
println("widenconditional = ", w, ", maybe_extract_const_bool = ", repr(m))
println(w == Core.Const(false) && m === nothing ? "REPRODUCED $id" : "NOT REPRODUCED $id")
