# On a string with a truncated UTF-8 sequence, eachmatch/findfirst/replace place an empty
# match inside that (malformed) character.
s = "a\xe2\x82"                 # 'a' at 1, the malformed character "\xe2\x82" at 2:3
r = r"(?<!a)(?!a)"
offs = [m.offset for m in eachmatch(r, s)]
println("collect(eachindex(s)) = ", collect(eachindex(s)))
println("eachmatch offsets = ", offs)
println("findfirst = ", findfirst(r, s))
println("replace(s, r => \"-\") = ", repr(replace(s, r => "-")))
any(o -> o <= ncodeunits(s) && !isvalid(s, o), offs) && println("REPRODUCED regexunicode-eachmatch-offset-inside-malformed")
