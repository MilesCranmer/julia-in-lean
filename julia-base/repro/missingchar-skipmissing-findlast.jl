x = [2, missing, 3, 4]
s = skipmissing(x)
f(g) = try repr(g()) catch e; "THROWS " * first(split(sprint(showerror, e), '\n')) end
println("collect(keys(s))         = ", collect(keys(s)))
println("findfirst(isodd, s)      = ", f(() -> findfirst(isodd, s)))
println("findall(iseven, s)       = ", f(() -> findall(iseven, s)))
r1 = f(() -> findlast(iseven, s))
r2 = f(() -> findnext(isodd, s, 1))
r3 = f(() -> findprev(isodd, s, 4))
println("findlast(iseven, s)      = ", r1)
println("findnext(isodd, s, 1)    = ", r2)
println("findprev(isodd, s, 4)   = ", r3)
println("findnext(isodd, s, 2)    = ", f(() -> findnext(isodd, s, 2)))
startswith(r1, "THROWS") && startswith(r2, "THROWS") && startswith(r3, "THROWS") &&
    println("REPRODUCED missingchar-skipmissing-findlast")
