c = Char(0x110000)
s = repr(c)
println("c = Char(0x110000): ismalformed = ", Base.ismalformed(c), ", codepoint = ", repr(codepoint(c)))
println("repr(c) = ", s)
r = try repr(eval(Meta.parse(s))) catch e; "THROWS " * first(split(sprint(showerror, e), '\n')) end
println("eval(Meta.parse(repr(c))) = ", r)
println("Meta.parse(\"'\\\\xf4\\\\x90\\\\x80\\\\x80'\") == c: ", eval(Meta.parse("'\\xf4\\x90\\x80\\x80'")) == c)
startswith(r, "THROWS") && println("REPRODUCED missingchar-show-char-roundtrip")
