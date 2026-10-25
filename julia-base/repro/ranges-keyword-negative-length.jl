r = range(1; length=-1)
println("range(1; length=-1) = ", repr(r), ", length = ", length(r))
unsigned_rejects = try
    range(UInt(1); length=-1)
    false
catch e
    println("range(UInt(1); length=-1) throws ", sprint(showerror, e))
    e isa ArgumentError
end
println("expected = ArgumentError for a negative element count in both calls")
length(r) == 0 && unsigned_rejects && println("REPRODUCED ranges-keyword-negative-length")
