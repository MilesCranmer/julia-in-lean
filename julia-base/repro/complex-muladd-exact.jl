z = complex(2.0^30, 2.0^30)
x = complex(1.0, 0.0)
m = muladd(z, z, x)
s = z * z + x
println("muladd(z, z, x) = ", m)
println("z * z + x       = ", s)
if m != s && s == complex(1.0, 2.0^61)
    println("REPRODUCED complex-muladd-exact")
end
