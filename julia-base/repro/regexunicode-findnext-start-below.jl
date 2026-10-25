# findnext/match with a Regex and a start index outside 1:ncodeunits(s)+1.
function attempt(f)
    try
        repr(f())
    catch e
        string(typeof(e), ": ", sprint(showerror, e)[1:min(end, 60)])
    end
end
s = "abc"
a = attempt(() -> findnext(r"a", s, 0))
b = attempt(() -> findnext("a", s, 0))
c = attempt(() -> findnext(r"a", s, 5))
d = attempt(() -> match(r"a", s, 0))
e = attempt(() -> match(r"a", s, 5))
println("findnext(r\"a\", \"abc\", 0) -> ", a)
println("findnext(\"a\", \"abc\", 0)  -> ", b)
println("findnext(r\"a\", \"abc\", 5) -> ", c)
println("match(r\"a\", \"abc\", 0)    -> ", d)
println("match(r\"a\", \"abc\", 5)    -> ", e)
println("occursin(r\"a\", \"abc\"; offset=-1) -> ", attempt(() -> occursin(r"a", s; offset = -1)))
println("occursin(r\"a\", \"abc\"; offset=10) -> ", attempt(() -> occursin(r"a", s; offset = 10)))
startswith(a, "InexactError") && startswith(b, "BoundsError") && startswith(c, "BoundsError") &&
    println("REPRODUCED regexunicode-findnext-start-below")
