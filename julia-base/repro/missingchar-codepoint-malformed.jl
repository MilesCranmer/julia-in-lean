c = reinterpret(Char, 0x61620000)   # the bytes "ab" packed into one Char
println("c = ", repr(c), ", ismalformed(c) = ", Base.ismalformed(c), ", isvalid(c) = ", isvalid(c))
r = try repr(codepoint(c)) catch e; "THROWS " * sprint(showerror, e) end
println("codepoint(c) = ", r)
println("Int(c) = ", Int(c), ", c + 1 = ", repr(c + 1), ", c == 'a' = ", c == 'a')
d = reinterpret(Char, 0xc3000000)   # a truncated two-byte sequence
println("codepoint(", repr(d), ") = ", try repr(codepoint(d)) catch e; "THROWS " * sprint(showerror, e) end)
Base.ismalformed(c) && r == "0x00000061" && println("REPRODUCED missingchar-codepoint-malformed")
