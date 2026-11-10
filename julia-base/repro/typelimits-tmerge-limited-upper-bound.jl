# tmerge(typeinf_lattice, a, b) of two lattice-equal LimitedAccuracy elements with different
# causes of the same size returns a result that is ⊑ both arguments, not ⊒ them.
const CC = Base.Compiler
println("VERSION = ", VERSION, ", commit ", Base.GIT_VERSION_INFO.commit)
L = CC.typeinf_lattice(CC.NativeInterpreter())
IS = CC.InferenceState isa UnionAll ? CC.InferenceState{CC.NativeInterpreter} : CC.InferenceState
s1 = ccall(:jl_new_struct_uninit, Any, (Any,), IS)
s2 = ccall(:jl_new_struct_uninit, Any, (Any,), IS)
S = fieldtype(CC.LimitedAccuracy, :causes)
c1 = S(); push!(c1, s1)
c2 = S(); push!(c2, s2)
a = CC.LimitedAccuracy(Int, c1)
b = CC.LimitedAccuracy(Int, c2)
r = CC.tmerge(L, a, b)
println("r = tmerge(a, b) = ", r, " with ", length(r.causes), " causes")
println("a ⊑ r: ", CC.:⊑(L, a, r), ";  b ⊑ r: ", CC.:⊑(L, b, r), ";  r ⊑ a: ", CC.:⊑(L, r, a))
if !CC.:⊑(L, a, r) && !CC.:⊑(L, b, r)
    println("REPRODUCED typelimits-tmerge-limited-upper-bound")
end
