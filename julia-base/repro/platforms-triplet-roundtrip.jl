using Base.BinaryPlatforms
p = Platform("x86_64", "linux"; foo = "", validate_strict = true)
println("p = ", repr(p))
t = triplet(p)
println("triplet(p) = ", repr(t))
r = try
    parse(Platform, t)
catch e
    e
end
println("parse(Platform, triplet(p)) => ", r isa Exception ? sprint(showerror, r) : repr(r))
if r isa ArgumentError
    println("REPRODUCED platforms-triplet-roundtrip")
end
