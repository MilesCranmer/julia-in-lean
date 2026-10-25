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
