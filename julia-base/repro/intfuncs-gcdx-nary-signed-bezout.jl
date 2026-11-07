a, b, c = Int8.((30, 34, 35))
result = gcdx(a, b, c)
d, u, v, w = result
exact_lhs = Int(a)*Int(u) + Int(b)*Int(v) + Int(c)*Int(w)
native_lhs = a*u + b*v + c*w
@show (a, b, c) result exact_lhs native_lhs d
@assert d == 1
@assert exact_lhs != Int(d)
println("REPRODUCED intfuncs-gcdx-nary-signed-bezout")
