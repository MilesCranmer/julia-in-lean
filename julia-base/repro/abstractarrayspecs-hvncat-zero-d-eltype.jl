# Typed concatenation should keep the explicitly requested element type.
scalar = Base._typed_hvncat(Any, Val(0), "a")
number = Base._typed_hvncat(Any, Val(0), 1)
public_dim = Base.typed_hvncat(Any, 0, 1)
public_shape = Base.typed_hvncat(Any, (), false, 1)
println("scalar requested Any, got ", eltype(scalar), ", size ", size(scalar))
println("number requested Any, got ", eltype(number), ", size ", size(number))
println("typed_hvncat(Any, 0, 1) eltype => ", eltype(public_dim))
println("typed_hvncat(Any, (), false, 1) eltype => ", eltype(public_shape))
if size(scalar) == size(number) == () && scalar[] == "a" && number[] == 1 &&
        eltype(scalar) == String && eltype(number) == Int &&
        eltype(public_dim) == Int && eltype(public_shape) == Int
    println("REPRODUCED abstractarrayspecs-hvncat-zero-d-eltype")
else
    error("zero-dimensional concatenation type narrowing did not reproduce")
end
