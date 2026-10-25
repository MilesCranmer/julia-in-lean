q = typemax(Int64) // 2^62
e = exponent(q)
println("q = ", q, " < 2: ", q < 2)
println("exponent(q) = ", e)
println("2^e <= abs(q): ", (big(2) // 1)^e <= abs(q))
if !((big(2) // 1)^e <= abs(q) < (big(2) // 1)^(e + 1))
    println("REPRODUCED mathfuncs-exponent-rational")
end
