# PersistentDict hashes keys with objectid and throws "Perfect hash collision"
# for two distinct keys with the same objectid; IdDict stores both.
# objectid(::Int64) and objectid(::UInt64) are int64hash(bits) xor a per-type
# constant (src/builtins.c, src/support/hashing.c), so such a pair can be built.
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
println("x = ", x, ", y = ", repr(y), ", x === y: ", x === y, ", objectid(x) == objectid(y): ", objectid(x) == objectid(y))
r = try; Base.PersistentDict{Any,Int}(x => 1, y => 2); catch e; e; end
println("PersistentDict{Any,Int}(x => 1, y => 2) = ", r)
id = IdDict{Any,Int}(x => 1, y => 2)
println("IdDict{Any,Int}(x => 1, y => 2) has ", length(id), " entries")
if objectid(x) == objectid(y) && x !== y && r isa ErrorException && length(id) == 2
    println("REPRODUCED dicts-persistentdict-objectid-collision")
end
