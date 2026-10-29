mutable struct UnitAxisVector <: AbstractVector{Int}
    value::Int
end
Base.size(::UnitAxisVector) = (1,)
Base.axes(::UnitAxisVector) = (3:3,)
Base.IndexStyle(::Type{UnitAxisVector}) = IndexLinear()
function Base.getindex(A::UnitAxisVector, i::Int)
    i == 3 || throw(BoundsError(A, i))
    A.value
end
function Base.setindex!(A::UnitAxisVector, v, i::Int)
    i == 3 || throw(BoundsError(A, i))
    A.value = v
    A
end
outcome(f) = try
    (:ok, f())
catch e
    (:error, typeof(e))
end
A = UnitAxisVector(7)
println("axes = ", axes(A))
println("A[3] = ", A[3])
println("first(LinearIndices(A)) = ", first(LinearIndices(A)))
r = outcome(() -> A[])
g = outcome(() -> get(A, (), 0))
s = outcome(() -> setindex!(A, 8))
println("A[] = ", r)
println("get(A, (), 0) = ", g)
println("setindex!(A, 8) = ", s)
if r == g == s == (:error, BoundsError) && A.value == 7
    println("REPRODUCED abstractarrayspecs-linear-zero-unitrange")
else
    println("NOT REPRODUCED")
end
