# switchtupleunion(ty) promises `Union{return...} == ty` (Compiler/src/typeutils.jl:318-320), but
# for a UnionAll whose variable also occurs inside a Union it rewraps each split tuple on its own.
# `T` then becomes diagonal in `Tuple{T,T} where T`, so `(Int8(1), 2)`, an instance of `B`, is in
# none of the results. The only caller at this commit, typesubtract, passes a DataType.
const C = Base.Compiler
id = "compiler-unionsplit-switchtupleunion-unionall"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
abstract type AR end
abstract type R{T} <: AR end
const B = Tuple{Union{T, R{T}}, T} where T
x = (Int8(1), 2)
rs = C.switchtupleunion(B)
println("switchtupleunion(B) = ", rs)
println("x isa B = ", x isa B, ", x isa Union{rs...} = ", x isa Union{rs...})
println("B <: Union{rs...} = ", B <: Union{rs...})
println(x isa B && !(x isa Union{rs...}) ? "REPRODUCED $id" : "NOT REPRODUCED $id")
