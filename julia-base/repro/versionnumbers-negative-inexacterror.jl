# VersionNumber with a negative component throws InexactError, not the intended ArgumentError
function err(f)
    try
        f()
        return nothing
    catch e
        return e
    end
end
e1 = err(() -> VersionNumber(-1))
e2 = err(() -> VersionNumber(1, -2, 0))
e3 = err(() -> VersionNumber(1, 0, 0, (-1,)))
e4 = err(() -> VersionNumber(1, 0, 0, (), (-1,)))
for (name, e) in (("VersionNumber(-1)", e1), ("VersionNumber(1, -2, 0)", e2), ("VersionNumber(1, 0, 0, (-1,))", e3), ("VersionNumber(1, 0, 0, (), (-1,))", e4))
    println(name, " throws ", typeof(e), ": ", sprint(showerror, e))
end
if all(e -> e isa InexactError, (e1, e2, e3, e4))
    println("REPRODUCED versionnumbers-negative-inexacterror")
end
