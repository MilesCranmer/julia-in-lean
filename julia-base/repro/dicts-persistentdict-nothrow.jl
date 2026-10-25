# KeyValue.set(dict::PersistentDict{K,V}, key::K, val::V) is declared
# @assume_effects :nothrow but throws "Perfect hash collision", so a try/catch
# around it in compiled code is removed and the exception escapes.
# Colliding keys as in repro/dicts-persistentdict-objectid-collision.jl.
function int64hash(k::UInt64)
    k = ~k + (k << 21); k ⊻= k >> 24; k = k + (k << 3) + (k << 8)
    k ⊻= k >> 14; k = k + (k << 2) + (k << 4); k ⊻= k >> 28; k + (k << 31)
end
unxorshift(k, s) = (r = k; t = k >> s; while t != 0; r ⊻= t; t >>= s; end; r)
inv64(a) = invmod(UInt128(a), UInt128(1) << 64) % UInt64
function int64hash_inv(k::UInt64)
    k *= inv64(1 + (UInt128(1) << 31)); k = unxorshift(k, 28); k *= inv64(21)
    k = unxorshift(k, 14); k *= inv64(265); k = unxorshift(k, 24)
    (k + 1) * inv64((UInt128(1) << 21) - 1)
end
cI = objectid(0) ⊻ int64hash(UInt64(0))
y = UInt64(1)
x = reinterpret(Int64, int64hash_inv(objectid(y) ⊻ cI))
p = Base.PersistentDict{Any,Int}(x => 1)

function guarded(p, k)
    try
        return Base.PersistentDict(p, k, 2)
    catch
        return :caught
    end
end

println("Base.infer_effects(Base.PersistentDict, (typeof(p), Any, Int)) = ",
        Base.infer_effects(Base.PersistentDict, (typeof(p), Any, Int)))
# The top-level try is interpreted, so it sees what escapes the compiled one.
r = try
    guarded(p, y)
catch e
    e
end
println("guarded(p, y) = ", r)
r isa ErrorException && println("REPRODUCED dicts-persistentdict-nothrow")
