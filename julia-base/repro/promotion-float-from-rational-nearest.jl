# Float64(::Rational{Int64}) does not return the closest Float64, as convert promises
q = 9007199254740995 // 3            # exact value 3002399751580331.666...
f = Float64(q)
exact = big(q.num) // big(q.den)
function ex(x)
    n, p, d = Base.decompose(x)
    p >= 0 ? big(n) * big(2)^p // d : big(n) // (d * big(2)^(-p))
end
d(y) = abs(ex(y) - exact)
println("Float64(", q, ") = ", f)
println("prevfloat = ", prevfloat(f), " is closer: ", d(prevfloat(f)) < d(f))
g = Float16(Int16(6322) // Int16(8583))   # exact value 0.73657229...
e2 = 6322 // 8583
d2(y) = abs(ex(y) - e2)
println("Float16(6322//8583) = ", g, ", nextfloat = ", nextfloat(g), " is closer: ", d2(nextfloat(g)) < d2(g))
if d(prevfloat(f)) < d(f) || d2(nextfloat(g)) < d2(g)
    println("REPRODUCED promotion-float-from-rational-nearest")
end
