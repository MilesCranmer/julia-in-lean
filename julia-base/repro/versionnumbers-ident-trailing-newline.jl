# VersionNumber accepts identifiers ending in "\n", and string/parse do not round-trip
v = VersionNumber(1, 0, 0, ("a\n",))
s = string(v)
w = parse(VersionNumber, s)
println("v = VersionNumber(1, 0, 0, (\"a\\n\",)): prerelease = ", repr(v.prerelease))
println("string(v) = ", repr(s))
println("parse(VersionNumber, string(v)).prerelease = ", repr(w.prerelease), ", equal to v: ", w == v)
u = VersionNumber(1, 0, 0, ("\n", "b"))
println("VersionNumber(1, 0, 0, (\"\\n\", \"b\")) = ", repr(string(u)))
x = parse(VersionNumber, "1.2.3\n")
println("parse(VersionNumber, \"1.2.3\\n\") = ", repr(x))
if w != v && v.prerelease == ("a\n",) && x == v"1.2.3"
    println("REPRODUCED versionnumbers-ident-trailing-newline")
end
