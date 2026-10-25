println("startswith(IOBuffer(\"\"), \"a\") = ", startswith(IOBuffer(""), "a"))
io = IOBuffer("")
r = try startswith(io, 'a') catch e e end
println("startswith(IOBuffer(\"\"), 'a') = ", r isa Exception ? sprint(showerror, r) : r, ", ismarked(io) = ", ismarked(io))
println("startswith(\"\", 'a') = ", startswith("", 'a'))
r isa EOFError && ismarked(io) && println("REPRODUCED stringutil-startswith-io-eof")
