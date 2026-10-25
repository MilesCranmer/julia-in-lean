f(g) = try repr(g()) catch e; "THROWS " * first(split(sprint(showerror, e), '\n')) end
for u in (0xe9a9a5bf, 0xc2808080, 0x00800000, 0x41800000)
    c = reinterpret(Char, u)
    println(repr(u), ": ismalformed = ", Base.ismalformed(c), ", isoverlong = ", Base.isoverlong(c),
            ", isvalid = ", isvalid(c), ", codepoint = ", f(() -> codepoint(c)),
            ", Char(codepoint(c)) == c: ", f(() -> Char(codepoint(c)) == c))
end
println("isvalid(String(UInt8[0xe9, 0xa9, 0xa5, 0xbf])) = ", isvalid(String(UInt8[0xe9, 0xa9, 0xa5, 0xbf])))
c = reinterpret(Char, 0xe9a9a5bf)
d = reinterpret(Char, 0x00800000)
isvalid(c) && codepoint(c) > 0x10ffff && isvalid(d) && d != '\0' && codepoint(d) == 0 &&
    println("REPRODUCED missingchar-isvalid-overlength")
