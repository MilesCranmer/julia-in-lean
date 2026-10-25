s = "é"   # bytes c3 a9
# raw_substring is new in Julia 1.14; 1.13 builds the same SubString with Val(:noshift).
ss = isdefined(Base, :raw_substring) ? Base.raw_substring(s, 1, 1) : SubString(s, 0, 1, Val(:noshift))
println("ncodeunits(ss) = ", ncodeunits(ss), ", length(ss) = ", length(ss))
println("iterate(ss) = ", repr(iterate(ss)))
r = try
    collect(ss)
catch e
    e
end
println("collect(ss) = ", r isa Exception ? sprint(showerror, r) : repr(r))
r isa BoundsError && println("REPRODUCED strings-raw-substring-iterate")
