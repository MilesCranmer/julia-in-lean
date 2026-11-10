# typesubtract(a, b, n) drops values of `a` when `a` is a UnionAll over a Union.
# Compiler/src/typeutils.jl:122-126 rewraps each Union member in its own UnionAll. In `A` the
# variable `T` also occurs inside `R{T}`, so the diagonal rule does not apply and `A` contains
# `(Int8(1), 2)`. Alone, `Tuple{T,T} where T` is diagonal and does not contain it.
const C = Base.Compiler
id = "compiler-unionsplit-typesubtract-unionall-diagonal"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
abstract type AR end
abstract type R{T} <: AR end
const A = Union{Tuple{T,T}, R{T}} where T
const D = Tuple{T,T} where T
x = (Int8(1), 2)
r = C.typesubtract(A, AR, 4)
println("x isa A = ", x isa A, ", x isa AR = ", x isa AR)
println("typesubtract(A, AR, 4) = ", r, ", x isa it = ", x isa r)
println("A <: Union{typesubtract(A, AR, 4), AR} = ", A <: Union{r, AR})
# User-visible effect: the else branch of `y isa AR` gets that type, so `y isa D` folds to true.
# `k(x)` must return 2.
function k(y)
    y isa AR && return 0
    y isa D && return 1
    return 2
end
kr(ref) = k(ref[])
got = kr(Ref{A}(x))
println("k(x) through a Ref{A} = ", got, " (called directly: ", k(x), ")")
println(x isa A && !(x isa AR) && !(x isa r) && got != 2 ? "REPRODUCED $id" : "NOT REPRODUCED $id")
