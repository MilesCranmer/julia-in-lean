# tryparse returns nothing for strings that do not parse; for BigFloat a string with an
# embedded NUL throws ArgumentError from the Cstring conversion instead.
s = "1\0"
f = try repr(tryparse(Float64, s)) catch e; "throws " * string(typeof(e)) end
i = try repr(tryparse(BigInt, s)) catch e; "throws " * string(typeof(e)) end
b = try repr(tryparse(BigFloat, s)) catch e; "throws " * string(typeof(e)) end
println("tryparse(Float64, \"1\\0\")  -> ", f)
println("tryparse(BigInt, \"1\\0\")   -> ", i)
println("tryparse(BigFloat, \"1\\0\") -> ", b)
if f == "nothing" && b == "throws ArgumentError"
    println("REPRODUCED bignums-tryparse-nul")
end
