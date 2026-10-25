# copyto!(dest, Rdest, src, Rsrc) skips the size check when Rdest is empty.
dest = zeros(Int, 2)
src = [1, 2, 3]
r1 = try copyto!(dest, CartesianIndices((1:0,)), src, CartesianIndices((1:3,))) catch e; e end
r2 = try copyto!(dest, CartesianIndices((1:1,)), src, CartesianIndices((1:3,))) catch e; e end
r3 = try copyto!(dest, CartesianIndices((1:2,)), src, CartesianIndices((1:0,))) catch e; e end
println(repr(r1), " ", repr(r2), " ", repr(r3))
if r1 === dest && r2 isa ArgumentError && r3 isa ArgumentError
    println("REPRODUCED multidim-copyto-empty-size")
end
