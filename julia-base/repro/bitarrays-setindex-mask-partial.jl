B = falses(4)
V = fill(false, 4)
eb = try; B[trues(4)] = trues(5); nothing; catch e; typeof(e); end
ev = try; V[trues(4)] = trues(5); nothing; catch e; typeof(e); end
println(eb, " ", Array(B), " | ", ev, " ", V)
if eb === DimensionMismatch && ev === DimensionMismatch && all(B) && !any(V)
    println("REPRODUCED bitarrays-setindex-mask-partial")
end
