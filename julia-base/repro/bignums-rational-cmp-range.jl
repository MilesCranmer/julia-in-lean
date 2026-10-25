# cmp must return -1, 0 or 1. cmp(::Rational{BigInt}, ::Rational{BigInt}) returns
# GMP's mpq_cmp result unchanged, which is any int with the right sign.
a = big(0) // 1
b = big(2)^200 // 1
c = big(2)^100 // 3
d = big(5) // 7
println("cmp(0//1, 2^200//1)           = ", cmp(a, b))
println("cmp(2^200//1, 0//1)           = ", cmp(b, a))
println("cmp(2^100//3, 5//7)           = ", cmp(c, d))
println("cmp(Rational{Int128} values)  = ", cmp(Rational{Int128}(c), Rational{Int128}(d)))
println("cmp(BigInt(0), big(2)^200)    = ", cmp(big(0), big(2)^200))
vals = [b, d, c, a]
println("sort(vals; lt=(x, y) -> cmp(x, y) == -1) = ", sort(vals; lt=(x, y) -> cmp(x, y) == -1))
println("sort(vals)                               = ", sort(vals))
if !(cmp(a, b) in (-1, 0, 1)) && !(cmp(b, a) in (-1, 0, 1))
    println("REPRODUCED bignums-rational-cmp-range")
end
