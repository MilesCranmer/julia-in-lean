r = -10:2:-1
expected = collect(r)[UInt(1)]
got = try r[UInt(1)] catch e; e end
println("collect(-10:2:-1)[UInt(1)] = ", expected)
println("(-10:2:-1)[UInt(1)] = ", repr(got))
println("(-10:2:-1)[1] = ", r[1])
if expected == -10 && r[1] == -10 && got isa InexactError
    println("REPRODUCED multidimcov-range-getindex-unsigned")
else
    println("NOT REPRODUCED multidimcov-range-getindex-unsigned")
end
