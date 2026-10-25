# trunc(Int, 1//0) throws DivideError, while the docstring promises InexactError (as for Inf)
e1 = try trunc(Int, 1//0) catch e; e end
e2 = try trunc(Int, Inf) catch e; e end
e3 = try round(Int, -1//0) catch e; e end
println("trunc(Int, 1//0) -> ", typeof(e1), "; trunc(Int, Inf) -> ", typeof(e2), "; round(Int, -1//0) -> ", typeof(e3))
if e1 isa DivideError && e2 isa InexactError
    println("REPRODUCED promotion-trunc-rational-infinite-error")
end
