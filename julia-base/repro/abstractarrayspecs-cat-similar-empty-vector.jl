# A shape vector and its tuple form must describe the same allocation shape.
a = 1:3
by_tuple = Base.cat_similar(a, Float64, ())
by_vector = Base.cat_similar(a, Float64, Int[])
array_tuple = Base.cat_similar(collect(a), Float64, ())
array_vector = Base.cat_similar(collect(a), Float64, Int[])
println("AbstractArray tuple shape => ", size(by_tuple))
println("AbstractArray vector shape => ", size(by_vector))
println("Array tuple shape => ", size(array_tuple))
println("Array vector shape => ", size(array_vector))
if size(by_tuple) == () && size(by_vector) == (3,) &&
        size(array_tuple) == () && size(array_vector) == ()
    println("REPRODUCED abstractarrayspecs-cat-similar-empty-vector")
else
    error("empty shape vector discrepancy did not reproduce")
end
