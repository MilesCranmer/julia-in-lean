# parse(BigInt, s) must reject what parse(Int, s) rejects. Julia strips one sign and
# hands the rest to GMP's mpz_set_str, which accepts a second '-' and ignores
# whitespace, so "--5" parses as 5 (the sign is flipped twice) and "+-5" as -5.
function res(f)
    try
        return repr(f())
    catch e
        return "throws " * string(typeof(e))
    end
end
for s in ("--5", "+-5", "-+5", "1 2", "-0x-5")
    println(rpad(repr(s), 8), " Int: ", rpad(res(() -> parse(Int, s)), 22), " BigInt: ", res(() -> parse(BigInt, s)))
end
if res(() -> parse(BigInt, "--5")) == "5" && startswith(res(() -> parse(Int, "--5")), "throws")
    println("REPRODUCED bignums-parse-bigint-sign")
end
