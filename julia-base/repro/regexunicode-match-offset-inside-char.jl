# match/findnext started at an index inside a character return that index as a match start.
s = "éa"                        # 'é' occupies code units 1:2
m = match(r"", s, 2)
f = findnext(r"", s, 2)
println("isvalid(s, 2) = ", isvalid(s, 2))
println("match(r\"\", s, 2).offset = ", m.offset)
println("findnext(r\"\", s, 2) = ", f)
println("findnext(\"\", s, 2) -> ", try repr(findnext("", s, 2)) catch e; sprint(showerror, e) end)
!isvalid(s, m.offset) && println("REPRODUCED regexunicode-match-offset-inside-char")
