x = -nextfloat(0.0)
y = 1.0
r = rem(x, y, RoundDown)
println("rem(-5.0e-324, 1.0, RoundDown) = ", repr(r))
println("0.0 <= r < 1.0 = ", 0.0 <= r < 1.0)
if r == y
    println("REPRODUCED float-rem-down-bound")
end
