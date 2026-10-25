using Base.BinaryPlatforms
p = Platform("x86_64", "linux"; julia_version = "foo", validate_strict = true)
println("accepted with validate_strict=true: ", repr(p))
r = try
    platforms_match(p, p)
catch e
    e
end
println("platforms_match(p, p) => ", r isa Exception ? sprint(showerror, r) : repr(r))
if r !== true
    println("REPRODUCED platforms-match-reflexive")
end
