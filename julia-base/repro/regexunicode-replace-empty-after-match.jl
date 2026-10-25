# replace skips an empty match that directly follows a non-empty match;
# eachmatch, findall and count all report it.
s, r = "abxd", r"x*"
ms = [(m.offset, m.match) for m in eachmatch(r, s)]
println("eachmatch: ", ms)
println("findall:   ", findall(r, s))
println("count:     ", count(r, s))
got = replace(s, r => "-")
io = IOBuffer(); pos = 1
for (o, t) in ms
    write(io, SubString(s, pos, o - 1), "-"); global pos = o + ncodeunits(t)
end
write(io, SubString(s, pos))
want = String(take!(io))
println("replace:   ", repr(got), "   (", count(==('-'), got), " replacements)")
println("assembled from eachmatch: ", repr(want))
got != want && count(==('-'), got) < count(r, s) && println("REPRODUCED regexunicode-replace-empty-after-match")
