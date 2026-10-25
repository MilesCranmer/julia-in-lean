# replace!(f, ::Dict) and replace!(f, ::Set) collect replacement pairs in a
# Vector{Pair{K,V}}, which converts the new key without the isequal check that
# setindex!/push! perform, so 0.1 is stored as 0.1f0 and is then not a key.
d = replace!(p -> 0.1 => 2, Dict{Float32,Int}(1f0 => 1))
println("replace!(p -> 0.1 => 2, Dict{Float32,Int}(1f0 => 1)) = ", d, "; haskey(d, 0.1) = ", haskey(d, 0.1))
s = replace!(x -> 0.1, Set{Float32}([1f0]))
println("replace!(x -> 0.1, Set{Float32}([1f0])) = ", s, "; 0.1 in s = ", 0.1 in s)
e = try; push!(Set{Float32}(), 0.1); "no error"; catch err; sprint(showerror, err); end
println("push!(Set{Float32}(), 0.1) throws: ", e)
if !haskey(d, 0.1) && !(0.1 in s) && startswith(e, "TypeError")
    println("REPRODUCED dicts-replace-lossy-key")
end
