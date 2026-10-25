using Printf
bad = String[]
for s in ["%1", "%5", "%*"]
    e = try Printf.Format(s); nothing catch e; e end
    println("Format(", repr(s), ") => ", typeof(e))
    e isa BoundsError && push!(bad, s)
end
length(bad) == 3 && println("REPRODUCED printf-incomplete-bounds")
