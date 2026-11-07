tryval(f) = try
    f()
catch err
    err
end
c = reinterpret(Char, 0xc0000000)  # a lone 0xc0 lead byte, no continuation
ov = Base.isoverlong(c)
m = Base.ismalformed(c)
println("isoverlong=", ov, " ismalformed=", m, " ncodeunits=", ncodeunits(c))
if ov && ncodeunits(c) == 1
    println("REPRODUCED char-overlong-encoding")
end
