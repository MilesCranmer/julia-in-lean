x = 9.526624812270413e-145
y = round(x; sigdigits=1)
z = round(y; sigdigits=1)
println("round(9.526624812270413e-145; sigdigits=1) = ", y)
println("round(", y, "; sigdigits=1) = ", z)
println("round(1.0e-144; sigdigits=1) = ", round(1.0e-144; sigdigits=1))
println("10.0^144 == big(10)^144: ", 10.0^144 == big(10)^144)
if y == 1.0e-144 && z != y
    println("REPRODUCED floatfuncs-sigdigits-idempotent")
end
