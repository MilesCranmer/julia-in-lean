r = try
    isapprox(1, 2; rtol=-1)
catch err
    err
end
println("isapprox(1, 2; rtol=-1) = ", r)
println("isapprox(1, 2; rtol=-1.0) = ", isapprox(1, 2; rtol=-1.0))
s = try
    isapprox(Int8(1), Int8(2); rtol=Int8(-2))
catch err
    err
end
println("isapprox(Int8(1), Int8(2); rtol=Int8(-2)) = ", s)
if r isa InexactError
    println("REPRODUCED floatfuncs-isapprox-int-negative-rtol")
end
