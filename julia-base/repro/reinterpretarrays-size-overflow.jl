# size(reinterpret(T, A)) computes size(A, 1) * sizeof(eltype(A)) in Int and wraps
r = reinterpret(Int32, 1:2^61)          # 2^64 bytes, i.e. 2^62 Int32 values
println("size(reinterpret(Int32, 1:2^61)) = ", size(r))
s = reinterpret(UInt8, 1:2^60)
println("size(reinterpret(UInt8, 1:2^60)) = ", size(s))
t = try size(reinterpret(NTuple{3,UInt8}, 1:2^61)) catch e typeof(e) end
println("reinterpret(NTuple{3,UInt8}, 1:2^61) -> ", t, "   (2^64 bytes are not a multiple of 3)")
if size(r) == (0,) && size(s, 1) < 0 && t == (0,)
    println("REPRODUCED reinterpretarrays-size-overflow")
end
