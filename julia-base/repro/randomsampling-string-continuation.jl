using Random

struct DrawLimit <: Exception end
mutable struct CountWords <: AbstractRNG
    calls::Int
end
Random.rng_native_52(::CountWords) = UInt64
function Random.rand(rng::CountWords, ::Random.SamplerType{UInt64})
    rng.calls += 1
    rng.calls > 100 && throw(DrawLimit())
    UInt64(0)
end

s = String(UInt8[0x80])
println("string = ", repr(s), "; length = ", length(s), "; collect = ", repr(collect(s)))
println("isvalid(s, 1) = ", isvalid(s, 1), "; acceptance at its only byte = ", Random.isvalid_unsafe(s, 1))
m = String(UInt8[0x61, 0x80])
rng = Xoshiro(1)
counts = Dict{Char,Int}()
for _ in 1:10_000
    c = rand(rng, m)
    counts[c] = get(counts, c, 0) + 1
end
println("mixed string = ", repr(m), "; collect = ", repr(collect(m)), "; counts over 10000 draws = ", sort(collect(counts)))
rng = CountWords(0)
try
    println("rand = ", repr(rand(rng, s)))
    println("NOT REPRODUCED randomsampling-string-continuation")
catch e
    e isa DrawLimit || rethrow()
    println("rand rejected 100 draws from the singleton index range before the RNG stopped it")
    println("collected sampler = ", repr(rand(Xoshiro(1), Random.Sampler(Xoshiro, s, Val(Inf)))))
    println("REPRODUCED randomsampling-string-continuation")
end
