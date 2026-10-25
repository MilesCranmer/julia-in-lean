# isvalid(Char, x) throws InexactError for negative integers instead of returning false.
r = try isvalid(Char, -1) catch e; e end
println("isvalid(Char, -1) -> ", r isa Exception ? sprint(showerror, r) : r)
println("isvalid(Char, typemax(Int)) -> ", isvalid(Char, typemax(Int)))
r isa InexactError && println("REPRODUCED regexunicode-isvalid-char-negative")
