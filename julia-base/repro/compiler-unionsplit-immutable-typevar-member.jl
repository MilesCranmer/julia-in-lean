# is_immutable_argtype(Union{Nothing, T} where T) is true, though that type is `Any` and contains
# mutable objects. _is_immutable_type (Compiler/src/typeutils.jl:463-469) treats the bare
# TypeVar member `T` as immutable: it is not `Type{...}`, not abstract and not a mutable DataType.
# getfield_effects then marks a field load through such a value `:consistent`, so a call that
# reads a mutable object's field is constant-folded and returns a stale value.
const C = Base.Compiler
id = "compiler-unionsplit-immutable-typevar-member"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
const U = Union{Nothing, T} where T
mutable struct M; a::Int; end
struct S; f::U; end
const m = M(1)
println("U == Any = ", U == Any, ", is_immutable_argtype(U) = ", C.is_immutable_argtype(U))
@noinline q(x::S) = getfield(getfield(x, :f), :a)
println("infer_effects(q, (S,)) = ", Base.infer_effects(q, (S,)))
w() = q(S(m))
m.a = 2
first = w()
m.a = 3
second = w()
println("w() after m.a = 2: ", first, "; after m.a = 3: ", second, " (must be 3)")
println(C.is_immutable_argtype(U) && second != 3 ? "REPRODUCED $id" : "NOT REPRODUCED $id")
