res(f) = try f() catch e; nameof(typeof(e)) end
a, b = typemin(Int), UInt(2)
g1 = res(() -> gcd(a, b))
g2 = res(() -> gcd(b, a))
l1 = res(() -> lcm(a, UInt(1)))
x1 = res(() -> gcdx(a, b))
println("gcd(typemin(Int), UInt(2)) = ", g1)
println("gcd(UInt(2), typemin(Int)) = ", g2)
println("lcm(typemin(Int), UInt(1)) = ", l1)
println("gcdx(typemin(Int), UInt(2)) = ", x1)
println("gcd(typemin(Int), 2) = ", gcd(typemin(Int), 2))
println("gcd(typemin(Int64), UInt32(2)) = ", gcd(typemin(Int64), UInt32(2)))
if g1 === :InexactError && g2 === :InexactError && l1 === :InexactError && x1 === :InexactError
    println("REPRODUCED intfuncscov-gcd-mixed-typemin")
else
    println("not reproduced")
end
