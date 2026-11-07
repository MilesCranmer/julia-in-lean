# length(::CartesianIndices) is prod(size) in wrapping Int arithmetic, so large index
# ranges report a wrong length; isempty is true for a nonempty CartesianIndices and
# linear indexing (which checks against 1:length) rejects every index.
R = CartesianIndices((2^32, 2^32))
r = iterate(R)
lin = try R[2] catch e; e end
println("length = ", length(R), ", isempty = ", isempty(R), ", first iterate = ", r === nothing ? nothing : r[1],
        ", R[2, 1] = ", R[2, 1], ", R[2] = ", repr(lin))
L = length(CartesianIndices((typemax(Int), 2)))
println("length(CartesianIndices((typemax(Int), 2))) = ", L)
if isempty(R) && r !== nothing && lin isa BoundsError && L < 0
    println("REPRODUCED multidim-cartesianindices-length-overflow")
end

let region = CartesianIndices((axes(0:typemax(Int), 1),)), index = 1
    @assert length(region) == typemin(Int)
    @assert !(index in axes(region, 1)) && region[index] == CartesianIndex(1)
    println("declared axes = ", axes(region), "; region[1] = ", region[index])
    println("REPRODUCED multidimensional-region-scalar-declared-axes")
end
let axis = axes(0:typemax(Int), 1)
    region = CartesianIndices((axis, 1:1:1))
    result = LinearIndices(region)
    @assert size(region) == (typemin(Int), 1) && size(result) == (0, 1)
    println("size(region) = ", size(region), "; size(LinearIndices(region)) = ", size(result))
    println("REPRODUCED multidimensional-linearindices-general-constructor")
end
let left = CartesianIndices((typemin(Int):typemax(Int),)), right = CartesianIndices((0:0,))
    point = CartesianIndex(typemin(Int))
    @assert length(left) == 0 && issubset(left, right)
    @assert point in left && !(point in right)
    println("subset length = ", length(left), "; issubset = true; missing point = ", point)
    println("REPRODUCED multidimensional-region-subset-geometry")
end
