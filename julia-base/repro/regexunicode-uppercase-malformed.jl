# uppercase/lowercase throw on strings containing invalid UTF-8; titlecase does not.
s = "a\xffb"
function attempt(f)
    try
        repr(f())
    catch e
        string(typeof(e), ": ", sprint(showerror, e))
    end
end
u = attempt(() -> uppercase(s))
l = attempt(() -> lowercase(s))
t = attempt(() -> titlecase(s))
c = attempt(() -> uppercasefirst("\xffab"))
println("uppercase(\"a\\xffb\") -> ", u)
println("lowercase(\"a\\xffb\") -> ", l)
println("titlecase(\"a\\xffb\") -> ", t)
println("uppercasefirst(\"\\xffab\") -> ", c)
startswith(u, "Base.InvalidCharError") && startswith(l, "Base.InvalidCharError") && !startswith(t, "Base") &&
    println("REPRODUCED regexunicode-uppercase-malformed")
