a = Int64(9007199254740993)
b = Int64(9007199254740996)
q = a // b
@assert gcd(a, b) == 3
@assert q == 3002399751580331 // 3002399751580332

rational = float(q)
quotient = a / b
println("a=$a b=$b q=$q")
println("float(q)=$rational a/b=$quotient isequal=$(isequal(rational, quotient))")
if !isequal(rational, quotient)
    println("REPRODUCED rational-manual-float-identity")
else
    error("the documented identity held")
end
