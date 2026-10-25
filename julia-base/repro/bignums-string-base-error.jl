# string(n; base) with an unsupported base throws DomainError for machine integers but
# ArgumentError for BigInt.
function res(f)
    try
        return repr(f())
    catch e
        return "throws " * string(typeof(e))
    end
end
for b in (1, 63, 100)
    println("base=", b, ": Int ", res(() -> string(7; base=b)), ", BigInt ", res(() -> string(big(7); base=b)))
end
if res(() -> string(7; base=63)) == "throws DomainError" && res(() -> string(big(7); base=63)) == "throws ArgumentError"
    println("REPRODUCED bignums-string-base-error")
end
