a, b, c = Int8(0), Int8(64), Int8(3)
@assert lcm(b, a, c) === Int8(0)
@assert lcm(b, c, a) === Int8(0)
println("lcm(64, 0, 3) = ", lcm(b, a, c))
println("lcm(64, 3, 0) = ", lcm(b, c, a))
try
    result = lcm(a, b, c)
    error("Expected the zero-first overflow, received ", result)
catch err
    err isa OverflowError || rethrow()
    println("lcm(0, 64, 3) = ", sprint(showerror, err))
    println("REPRODUCED intfuncs-lcm-nary-zero")
end
