xs = Rational{Int8}[64//1, 3//1, 0//1]
result = try
    lcm(xs)
catch err
    err
end
println("intfuncs-lcm-array-real = ", result isa Exception ? sprint(showerror, result) : repr(result))
@assert result isa OverflowError
println("REPRODUCED intfuncs-lcm-array-real")
