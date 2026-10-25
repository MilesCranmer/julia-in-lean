a, b = Int8(2), Int8(2)
d, u, v = gcdx(a, b)
println("gcdx(Int8(2), Int8(2)) = ", (d, u, v))
println("abs(v) < abs(a ÷ d) = ", abs(v) < abs(a ÷ d))
if d == 2 && Int(u)*Int(a) + Int(v)*Int(b) == Int(d) && !(abs(u) < abs(b ÷ d) && abs(v) < abs(a ÷ d))
    println("REPRODUCED intarith-number-gcdx-strict-bounds")
else
    error("gcdx coefficient-bound counterexample did not reproduce")
end
