x = prevfloat(1000.0)                # 999.9999999999999
println("x = ", x, ",  log10(x) = ", log10(x), ",  Base.hidigit(x, 10) = ", Base.hidigit(x, 10))
a = floor(x; sigdigits=1)
b = trunc(x; sigdigits=1)
c = round(x; sigdigits=16)
d = round(x; sigdigits=17)
println("floor(x; sigdigits=1)  = ", a)
println("trunc(x; sigdigits=1)  = ", b)
println("round(x; sigdigits=16) = ", c)
println("round(x; sigdigits=17) = ", d)
println("floor(prevfloat(100.0); sigdigits=1) = ", floor(prevfloat(100.0); sigdigits=1))
println("floor(Float16(99.94); sigdigits=1) = ", floor(Float16(99.94); sigdigits=1))
println("floor(999.9999f0; sigdigits=1) = ", floor(999.9999f0; sigdigits=1))
if a == 0 && b == 0
    println("REPRODUCED floatfuncs-sigdigits-hidigit")
end
