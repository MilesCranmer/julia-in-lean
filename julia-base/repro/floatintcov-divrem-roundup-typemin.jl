id = "floatintcov-divrem-roundup-typemin"

x = Int8(-127)
y = typemin(Int8)
q = div(x, y, RoundUp)
r = rem(x, y, RoundUp)
qr = divrem(x, y, RoundUp)

println("VERSION = ", VERSION)
println("x = ", x, ", y = ", y)
println("div(x, y, RoundUp) = ", q)
println("rem(x, y, RoundUp) = ", r)
println("divrem(x, y, RoundUp) = ", qr)
println("q*y+r = ", Int(q) * Int(y) + Int(r))
println("divrem == (div, rem) = ", qr == (q, r))

if qr != (q, r)
    println("REPRODUCED ", id)
else
    println("NOT REPRODUCED ", id)
end
