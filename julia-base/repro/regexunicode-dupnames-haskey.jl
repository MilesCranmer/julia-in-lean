# With (?J) duplicate group names, keys(m) lists a name that haskey/getindex reject.
m = match(r"(?J)(?<x>a)|(?<x>b)", "b")
k = keys(m)
h = haskey(m, "x")
g = try repr(m["x"]) catch e; sprint(showerror, e) end
println("keys(m) = ", k)
println("haskey(m, \"x\") = ", h)
println("m[\"x\"] -> ", g)
("x" in k) && !h && println("REPRODUCED regexunicode-dupnames-haskey")
