# After an empty match, findall/count restart one character later and miss a
# non-empty match that starts at the same position; eachmatch reports it.
s, r = "b", r"|b"
ms = [(m.offset, m.match) for m in eachmatch(r, s)]
fa = findall(r, s)
println("eachmatch: ", ms)
println("findall:   ", fa)
println("count:     ", count(r, s))
length(fa) < length(ms) && any(m -> m[2] == "b", ms) && !any(x -> x == 1:1, fa) &&
    println("REPRODUCED regexunicode-findall-skips-nonempty")
