a = ["a", "b", "c"]
err = try
    splice!(a, 2:1, Any["x", 1])
    nothing
catch e
    e
end
println(typeof(err))
println("length = ", length(a), ", assigned = ", [isassigned(a, i) for i in eachindex(a)])
println(repr(try a[3] catch e; e end))
if err isa MethodError && !all(i -> isassigned(a, i), eachindex(a))
    println("REPRODUCED arrayops-splice-convert-undef")
end
