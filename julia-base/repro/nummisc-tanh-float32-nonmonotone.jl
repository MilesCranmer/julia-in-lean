x = 0.49214557f0
y = nextfloat(x)
tx = tanh(x)
ty = tanh(y)
rx, ry = setprecision(BigFloat, 256) do
    Float32(tanh(BigFloat(x))), Float32(tanh(BigFloat(y)))
end
println("x = ", x, ", bits = 0x", string(reinterpret(UInt32, x), base=16))
println("y = ", y, ", bits = 0x", string(reinterpret(UInt32, y), base=16))
println("tanh(x) = ", tx, ", bits = 0x", string(reinterpret(UInt32, tx), base=16))
println("tanh(y) = ", ty, ", bits = 0x", string(reinterpret(UInt32, ty), base=16))
println("reference Float32 tanh(x), tanh(y) = ", (rx, ry))
if x < y && tx > ty
    println("REPRODUCED nummisc-tanh-float32-nonmonotone")
end
