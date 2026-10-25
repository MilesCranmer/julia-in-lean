b = Int128(1) << 63
@assert b > 1
threw = try
    ndigits(1, base=b)
    false
catch e
    println("actual exception = ", typeof(e))
    e isa InexactError
end
@assert threw
println("REPRODUCED intarith-powers-large-base")
