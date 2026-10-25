# Rational{T}(x::AbstractFloat) returns a value that is not equal to x instead of throwing InexactError
function exact(x::AbstractFloat)   # the exact value of x, from its integer decomposition
    n, p, d = Base.decompose(x)
    p >= 0 ? big(n) * big(2)^p // d : big(n) // (d * big(2)^(-p))
end
r = Rational{Int8}(0.1)
println("Rational{Int8}(0.1) = ", r, ", r == 0.1: ", r == 0.1, ", exact 0.1 = ", exact(0.1))
s = try Rational{Int32}(2f0^31) catch e; e end
println("Rational{Int32}(2f0^31) = ", s)
bad1 = r != 0.1
bad2 = s isa Rational && s != 2f0^31
if bad1
    println("REPRODUCED promotion-rational-from-float-exact")
end
