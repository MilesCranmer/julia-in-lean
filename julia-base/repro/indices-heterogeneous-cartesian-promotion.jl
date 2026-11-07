# Both regions contain the same four ordinary Cartesian coordinates.
a = CartesianIndices((1:2, Base.OneTo(2)))
b = CartesianIndices((1:2, 1:2))
@assert size(a) == size(b) == (2, 2)
@assert collect(a) == collect(b)
println("left type = ", typeof(a))
println("right type = ", typeof(b))

failures = Bool[]
for (label, operation) in (("promote", () -> promote(a, b)),
                            ("vector literal", () -> [a, b]))
    try
        result = operation()
        println(label, " returned ", typeof(result))
        push!(failures, false)
    catch err
        err isa MethodError || rethrow()
        println(label, " threw MethodError in ", err.f)
        push!(failures, err.f === Base.indices_promote_type)
    end
end
if all(failures)
    println("REPRODUCED indices-heterogeneous-cartesian-promotion")
else
    println("NOT REPRODUCED indices-heterogeneous-cartesian-promotion")
end
