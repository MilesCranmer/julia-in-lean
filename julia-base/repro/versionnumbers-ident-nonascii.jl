# VersionNumber identifiers accept the non-ASCII letters U+017F and U+212A
v = VersionNumber("1.0.0-\u017f")
w = VersionNumber("1.0.0-\u212a.x+\u212a")
u = VersionNumber(1, 0, 0, ("\u017f",))
println("VersionNumber(\"1.0.0-\\u017f\").prerelease = ", repr(v.prerelease))
println("VersionNumber(\"1.0.0-\\u212a.x+\\u212a\") = ", repr(w))
println("VersionNumber(1, 0, 0, (\"\\u017f\",)) = ", repr(u))
r = try VersionNumber("1.0.0-\u00e9"); "accepted" catch e; "throws " * sprint(showerror, e) end
println("VersionNumber(\"1.0.0-\\u00e9\") ", r)
if v.prerelease == ("\u017f",) && w.build == ("\u212a",) && u.prerelease == ("\u017f",) && !all(isascii, v.prerelease[1])
    println("REPRODUCED versionnumbers-ident-nonascii")
end
