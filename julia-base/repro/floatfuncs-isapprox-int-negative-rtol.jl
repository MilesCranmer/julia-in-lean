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

let x = typemin(Int64), y = Int64(0), atol = Int64(0), rtol = Int64(-1)
    expected = x == y || abs(big(x) - big(y)) <=
        max(big(atol), big(rtol) * max(abs(big(x)), abs(big(y))))
    outcome = try
        isapprox(x, y; atol=atol, rtol=rtol, norm=abs)
    catch err
        err
    end
    println("typemin case = ", repr(outcome))
    println("exact formula = ", expected)
    @assert expected === false
    @assert outcome === true || outcome isa InexactError
    println("REPRODUCED floatfuncs-isapprox-int-negative-rtol-v2")
end
