# Base.Parsers.parsevalue(T, bytes) (base/parsers/Parsers.jl:55-89) parses an integer
# type "or return[s] a ParseFailure instead of throwing". For T = Bool (an Integer type)
# every call with digits throws InexactError, because the generic parseint
# (base/parsers/ints.jl:161-173) computes T(base).
for (s, kw) in (("1", 10), ("0", 10), ("1", 2))
    r = try Base.Parsers.parsevalue(Bool, codeunits(s); base = kw) catch e; e end
    println("parsevalue(Bool, codeunits(\"$s\"); base = $kw) => ", r isa Exception ? sprint(showerror, r) : repr(r))
end
println("parse(Bool, \"1\") => ", parse(Bool, "1"))
r = try Base.Parsers.parsevalue(Bool, codeunits("1")) catch e; e end
if r isa InexactError
    println("REPRODUCED misccov-parsers-parsevalue-bool")
end
