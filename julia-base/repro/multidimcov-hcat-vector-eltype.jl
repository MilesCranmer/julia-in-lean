a = hcat(Any[1], Any[2])
b = cat(Any[1], Any[2]; dims=2)
c = vcat(Any[1], Any[2])
d = hcat(Union{Int,Float64}[1, 2], Union{Int,Float64}[3, 4])
println("hcat(Any[1], Any[2]) isa ", typeof(a))
println("cat(Any[1], Any[2]; dims=2) isa ", typeof(b))
println("vcat(Any[1], Any[2]) isa ", typeof(c))
println("hcat of two Vector{Union{Int,Float64}} isa ", typeof(d))
stored = try a[1] = "x"; "ok" catch e; typeof(e) end
println("a[1] = \"x\": ", stored)
if typeof(a) == Matrix{Int} && typeof(b) == Matrix{Any} && typeof(d) == Matrix{Int}
    println("REPRODUCED multidimcov-hcat-vector-eltype")
else
    println("NOT REPRODUCED multidimcov-hcat-vector-eltype")
end
