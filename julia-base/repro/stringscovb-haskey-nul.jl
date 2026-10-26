m = match(r"(?<a>x)", "x")
println("haskey(m, \"zz\") -> ", haskey(m, "zz"))
r = try haskey(m, "a\0b") catch e e end
println("haskey(m, \"a\\0b\") -> ", repr(r))
r isa ArgumentError && println("REPRODUCED stringscovb-haskey-nul")
