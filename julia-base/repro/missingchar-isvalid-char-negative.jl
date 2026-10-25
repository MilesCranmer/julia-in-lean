f(g) = try repr(g()) catch e; "THROWS " * first(split(sprint(showerror, e), '\n')) end
r1 = f(() -> isvalid(Char, -1))
r2 = f(() -> isvalid(Char, Int8(-1)))
println("isvalid(Char, 0x110000) = ", f(() -> isvalid(Char, 0x110000)))
println("isvalid(Char, 2^40)     = ", f(() -> isvalid(Char, 2^40)))
println("isvalid(Char, -1)       = ", r1)
println("isvalid(Char, Int8(-1)) = ", r2)
startswith(r1, "THROWS InexactError") && println("REPRODUCED missingchar-isvalid-char-negative")
