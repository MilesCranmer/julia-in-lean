# reinterpret(reshape, T, reinterpret(reshape, S, a)) uses the shape of a instead of the shape of the inner array
a = UInt32[0x04030201, 0x08070605, 0x0c0b0a09]
b = reinterpret(reshape, UInt16, a)               # 2×3
c = reinterpret(reshape, UInt8, b)
println("size(b) = ", size(b))
println("size(reinterpret(reshape, UInt8, b)) = ", size(c))
println("size(reinterpret(reshape, UInt8, collect(b))) = ", size(reinterpret(reshape, UInt8, collect(b))))
m = UInt32[1 2 3; 4 5 6]
bm = reinterpret(reshape, UInt16, m)              # 2×2×3, first axis has length 2, not 4
d = try size(reinterpret(reshape, UInt64, bm)) catch e typeof(e) end
dc = try size(reinterpret(reshape, UInt64, collect(bm))) catch e typeof(e) end
println("reinterpret(reshape, UInt64, bm) -> ", d, "; on collect(bm) -> ", dc)
if size(c) == (4, 3) && d == (3,) && dc == ArgumentError
    println("REPRODUCED reinterpretarrays-rr-nested-size")
end
