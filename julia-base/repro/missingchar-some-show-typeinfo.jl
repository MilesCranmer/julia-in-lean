v = [Some(1), Some(2)]
s = repr(v)
println("repr(v) = ", s)
r = try repr(eval(Meta.parse(s))) catch e; "THROWS " * first(split(sprint(showerror, e), '\n')) end
println("eval(Meta.parse(repr(v))) = ", r)
w = [Some(nothing)]
println("repr([Some(nothing)]) = ", repr(w))
startswith(r, "THROWS") && println("REPRODUCED missingchar-some-show-typeinfo")
