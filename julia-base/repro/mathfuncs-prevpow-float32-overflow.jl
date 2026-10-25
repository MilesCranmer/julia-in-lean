a = 2.0f0
x = 1.0e39
p = prevpow(a, x)
println("prevpow(2.0f0, 1.0e39) = ", repr(p), "; p <= x: ", p <= x)
println("prevpow(2.5f0, 1.0e40) = ", repr(prevpow(2.5f0, 1.0e40)))
println("largest Float32 power of 2 <= x: ", repr(2.0f0^127))
if !(p <= x)
    println("REPRODUCED mathfuncs-prevpow-float32-overflow")
end
