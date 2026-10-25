println(partialsort(collect(259:-1:1), 4:3))
err = try
    partialsort(collect(260:-1:1), 4:3)
    nothing
catch e
    e
end
println(err)
if err isa ArgumentError
    println("REPRODUCED sort-partialsort-empty-range")
end
