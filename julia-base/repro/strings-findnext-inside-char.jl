s = "éx"            # bytes c3 a9 78
t = "\xa9x"         # bytes a9 78
r = findfirst(t, s)
println("findfirst(\"\\xa9x\", \"éx\") = ", repr(r))
println("occursin(\"\\xa9\", \"éx\") = ", occursin("\xa9", s))
g = try
    s[r]
catch e
    e
end
println("s[r] = ", g isa Exception ? sprint(showerror, g) : repr(g))
r == 2:3 && g isa StringIndexError && println("REPRODUCED strings-findnext-inside-char")
