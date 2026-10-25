# Dict(d), merge and merge! consume an ImmutableDict in its iteration order,
# most recent pair first, so the oldest shadowed value wins.
const ID = Base.ImmutableDict
d = ID(:a => 1, :a => 2)               # d[:a] == 2
D = Dict(d)
M = merge(d, Dict(:b => 3))
println("d[:a] = ", d[:a], "; collect(d) = ", collect(d))
println("Dict(d) = ", D, "; merge(d, Dict(:b => 3)) = ", M)
io = IOContext(IOContext(IOBuffer(), :compact => false), :compact => true)
println("io[:compact] = ", io[:compact], "; Dict(io.dict)[:compact] = ", Dict(io.dict)[:compact])
if d[:a] == 2 && D[:a] == 1 && M[:a] == 1
    println("REPRODUCED dicts-immutabledict-to-dict")
end
