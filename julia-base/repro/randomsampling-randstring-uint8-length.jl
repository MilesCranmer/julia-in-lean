using Random

mutable struct AlternatingWords <: AbstractRNG
    n::Int
end
Random.rng_native_52(::AlternatingWords) = UInt64
function Random.rand(rng::AlternatingWords, ::Random.SamplerType{UInt64})
    rng.n += 1
    isodd(rng.n) ? UInt64(0) : typemax(UInt64)
end
s = randstring(AlternatingWords(0), UInt8[0xc3, 0xa9], 2)
println("randstring = ", repr(s))
println("requested length = 2; length = ", length(s), "; ncodeunits = ", ncodeunits(s))
if length(s) != 2
    println("REPRODUCED randomsampling-randstring-uint8-length")
else
    error("NOT REPRODUCED randomsampling-randstring-uint8-length")
end
