x = [1, missing, 3]
s = skipmissing(x)
f(g) = try repr(g()) catch e; "THROWS " * first(split(sprint(showerror, e), '\n')) end
println("s[2]   = ", f(() -> s[2]))
println("s[1:2] = ", f(() -> s[1:2]))
println("s[[2]] = ", f(() -> s[[2]]))
v = s[1:2]
any(ismissing, v) && startswith(f(() -> s[2]), "THROWS MissingException") &&
    println("REPRODUCED missingchar-skipmissing-getindex-nonscalar")
