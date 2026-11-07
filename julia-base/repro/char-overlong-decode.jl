tryval(f) = try
    f()
catch err
    err
end
c = reinterpret(Char, 0xc0000000)
ov = Base.isoverlong(c)
d = tryval(() -> Base.decode_overlong(c))
println("isoverlong=", ov, " decode_overlong=", repr(d))
if ov && !(d isa Integer)
    println("REPRODUCED char-overlong-decode")
end
