using Random

struct ZeroWords <: AbstractRNG end
Random.rng_native_52(::ZeroWords) = UInt64
Random.rand(::ZeroWords, ::Random.SamplerType{UInt64}) = UInt64(0)

println("randexp = ", randexp(ZeroWords()))
try
    println(randsubseq(ZeroWords(), [10, 20, 30], 0.1))
    println("NOT REPRODUCED randomsampling-randsubseq-zero")
catch e
    println(typeof(e), ": ", sprint(showerror, e))
    if e isa BoundsError && e.i == (0,)
        println("REPRODUCED randomsampling-randsubseq-zero")
    else
        rethrow()
    end
end
