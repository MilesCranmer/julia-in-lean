# Rational{Int32}(2f0^31) overflows Int32 and returns 2147483647//1 on nightly instead of throwing InexactError
x = 2f0^31
s = try Rational{Int32}(x) catch e; e end
println("Rational{Int32}(2f0^31) = ", s)
if s isa Rational && s != Int64(x)
    println("REPRODUCED promotion-rational-from-float-exact")
end
