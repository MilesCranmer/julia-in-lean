# tryparse(VersionNumber, s) throws instead of returning nothing for some invalid strings
function outcome(s)
    try
        r = tryparse(VersionNumber, s)
        return r === nothing ? "nothing" : repr(r)
    catch e
        return "throws " * sprint(showerror, e)
    end
end
cases = ["4294967296", "1.2.99999999999", "1.0.0-18446744073709551616", "1+18446744073709551616", "\u0661.0"]
results = [outcome(s) for s in cases]
for (s, r) in zip(cases, results)
    println("tryparse(VersionNumber, ", repr(s), ") => ", r)
end
if all(startswith("throws"), results)
    println("REPRODUCED versionnumbers-tryparse-throws")
end
