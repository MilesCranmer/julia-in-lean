a, b = UInt16(1), typemin(Int8)
forward = try
    lcm(a, b)
catch e
    e
end
reverse = lcm(b, a)
println("lcm(UInt16(1), typemin(Int8)) = ", forward isa Exception ? nameof(typeof(forward)) : forward)
println("lcm(typemin(Int8), UInt16(1)) = ", Int(reverse))
if forward isa InexactError && reverse == UInt16(128)
    println("REPRODUCED intarith-number-lcm-mixed-typemin")
else
    error("mixed lcm counterexample did not reproduce")
end
