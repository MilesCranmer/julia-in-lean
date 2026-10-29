# A[] on an IndexCartesian array whose axes are all of length 1 but do not
# start at 1 calls the canonical getindex with indices (1, 1) instead of
# (first(axes(A, 1)), first(axes(A, 2))). checkbounds(Bool, A) is true, so
# get(A, (), default) throws instead of returning the element.
struct C2 <: AbstractMatrix{Int}   # 1×1 matrix with axes (5:5, 5:5), IndexCartesian
    x::Base.RefValue{Int}
end
Base.size(::C2) = (1, 1)
Base.axes(::C2) = (Base.IdentityUnitRange(5:5), Base.IdentityUnitRange(5:5))
Base.getindex(A::C2, i::Int, j::Int) = (checkbounds(A, i, j); A.x[])
Base.setindex!(A::C2, v, i::Int, j::Int) = (checkbounds(A, i, j); A.x[] = v)

A = C2(Ref(7))
show_outcome(f) = try
    r = f(); println(repr(r)); r
catch e
    println("THROWS ", typeof(e)); e
end
show_outcome(() -> checkbounds(Bool, A))   # true: A[] is a valid index
show_outcome(() -> A[5, 5])                # 7
show_outcome(() -> first(A))               # 7
r1 = show_outcome(() -> A[])               # expected 7
r2 = show_outcome(() -> get(A, (), 0))     # expected 7
r3 = show_outcome(() -> (A[] = 8; A.x[]))  # expected 8
if r1 isa BoundsError && r2 isa BoundsError
    println("REPRODUCED abstractarrayspecs-zero-index-offset")
else
    println("NOT REPRODUCED")
end
