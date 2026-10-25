println(repr(partialsortperm(zeros(127), Int8(3))))
err = try
    partialsortperm(zeros(128), Int8(3))
    nothing
catch e
    e
end
println(err)
if err isa InexactError
    println("REPRODUCED sort-partialsortperm-index-type")
end
