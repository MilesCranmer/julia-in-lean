m = Memory{Int}(undef, 3)
a = Base.wrap(Array, m, -1)
b = Base.wrap(Array, memoryref(m), (-5,))
c = try Base.wrap(Array, m, (-1, -1)); "no error" catch e; typeof(e) end
d = try Vector{Int}(undef, -1); "no error" catch e; typeof(e) end
println("wrap(Array, m, -1): size ", size(a), ", length ", length(a))
println("wrap(Array, memoryref(m), (-5,)): size ", size(b), ", length ", length(b))
println("wrap(Array, m, (-1, -1)) throws ", c, "; Vector{Int}(undef, -1) throws ", d)
if size(a) == (-1,) && length(b) == -5 && c == ArgumentError && d == ArgumentError
    println("REPRODUCED multidimcov-wrap-negative-length")
else
    println("NOT REPRODUCED multidimcov-wrap-negative-length")
end
