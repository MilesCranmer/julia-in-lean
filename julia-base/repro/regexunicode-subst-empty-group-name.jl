# s"\g<>" (empty group name) throws ArgumentError from parse instead of "Bad replacement string".
function attempt(sub)
    try
        replace("ab", r"(a)" => sub)
    catch e
        string(typeof(e), ": ", sprint(showerror, e))
    end
end
x = attempt(s"\g<>")
y = attempt(s"\g<")
z = attempt(s"\g<x>")
println("s\"\\g<>\"  -> ", x)
println("s\"\\g<\"   -> ", y)
println("s\"\\g<x>\" -> ", z)
startswith(x, "ArgumentError") && startswith(y, "ErrorException: Bad replacement string") &&
    println("REPRODUCED regexunicode-subst-empty-group-name")
