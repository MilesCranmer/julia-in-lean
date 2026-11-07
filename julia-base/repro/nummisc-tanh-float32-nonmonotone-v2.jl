# Adjacent Float32 inputs, constructed directly from their public bit patterns.
id = "nummisc-tanh-float32-nonmonotone-v2"
x = reinterpret(Float32, UInt32(0x3dfff085))
y = reinterpret(Float32, UInt32(0x3dfff086))
matched = x < y && y == nextfloat(x) && tanh(x) > tanh(y)
println((matched ? "REPRODUCED " : "NOT_REPRODUCED ") * id)
