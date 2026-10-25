# parse(BigInt, s) must reject internal whitespace like parse(Int, s); GMP's
# mpz_set_str skips whitespace anywhere in the digits.
function res(f)
    try
        return repr(f())
    catch e
        return "throws " * string(typeof(e))
    end
end
a = res(() -> parse(Int, "100 10"))
b = res(() -> parse(BigInt, "100 10"))
c = res(() -> parse(BigInt, "1\t2"))
println("parse(Int, \"100 10\")    -> ", a)
println("parse(BigInt, \"100 10\") -> ", b)
println("parse(BigInt, \"1\\t2\")   -> ", c)
if startswith(a, "throws") && b == "10010"
    println("REPRODUCED bignums-parse-bigint-whitespace")
end
