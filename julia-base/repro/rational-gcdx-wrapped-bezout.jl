x = Int8(100) // Int8(1)
y = Int8(7) // Int8(3)
g, u, v = gcdx(x, y)

big_rational(q) = BigInt(numerator(q)) // BigInt(denominator(q))
lhs = BigInt(u) * big_rational(x) + BigInt(v) * big_rational(y)
expected = big_rational(g)

if lhs != expected
    println("REPRODUCED rational-gcdx-wrapped-bezout")
    println("REPRODUCED rational-gcdx-bezout")
    println("gcdx = ($g, $u, $v)")
    println("exact Bezout left-hand side = $lhs; gcd = $expected")
else
    error("gcdx rational Bezout identity held: $lhs")
end
