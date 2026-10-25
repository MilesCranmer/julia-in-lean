# r^n with negative n builds a regex that matches the literal text "{n}".
n = -1
r = r"a"^n
println("r\"a\"^", n, " = ", r)
println("match(r, \"a{-1}\") = ", match(r, "a{-1}"))
println("\"a\"^-1 throws: ", try "a"^n; "no" catch e; typeof(e) end)
match(r, "a{-1}") !== nothing && println("REPRODUCED regexunicode-regex-pow-negative")
