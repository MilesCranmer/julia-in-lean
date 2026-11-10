# tmerge(typeinf_lattice, c, c) is not ⊑ c for the Conditional that `@isdefined x` produces, so
# merging two copies of the same `@isdefined` result loses the "x is defined" refinement.
const CC = Base.Compiler
println("VERSION = ", VERSION, ", commit ", Base.GIT_VERSION_INFO.commit)
L = CC.typeinf_lattice(CC.NativeInterpreter())
# Julia 1.13 has no `ssadef` field.
mkcond(t, e) = hasfield(CC.Conditional, :ssadef) ? CC.Conditional(1, 0, t, e; isdefined=true) :
                                                   CC.Conditional(1, t, e; isdefined=true)
c = mkcond(Int, Int)     # `@isdefined x` for a slot x::Int
r = CC.tmerge(L, c, c)
println("tmerge(c, c) = ", r, ";  ⊑(r, c) = ", CC.:⊑(L, r, c))
c2 = mkcond(Int, Nothing)
r2 = CC.tmerge(L, c2, c2)
println("tmerge(c2, c2) = ", r2, ";  ⊑(r2, c2) = ", CC.:⊑(L, r2, c2))

# User-visible effect: `f` merges two identical `@isdefined(x)` results at the phi of `c`.
function f(b1::Bool, b2::Bool)
    if b1
        x = 1
    end
    c = b2 ? @isdefined(x) : @isdefined(x)
    c && return x
    return 0
end
function g(b1::Bool, b2::Bool)
    if b1
        x = 1
    end
    c = @isdefined(x)
    c && return x
    return 0
end
ef = Base.infer_exception_type(f, (Bool, Bool))
eg = Base.infer_exception_type(g, (Bool, Bool))
println("infer_exception_type(f) = ", ef, ";  infer_exception_type(g) = ", eg)
println("infer_effects(f) = ", Base.infer_effects(f, (Bool, Bool)), ";  infer_effects(g) = ",
        Base.infer_effects(g, (Bool, Bool)))
if !CC.:⊑(L, r, c) && !CC.:⊑(L, r2, c2) && ef === UndefVarError && eg === Union{}
    println("REPRODUCED typelimits-tmerge-conditional-idempotent")
end
