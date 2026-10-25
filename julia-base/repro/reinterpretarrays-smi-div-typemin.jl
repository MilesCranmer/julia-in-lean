# div(typemin(Int), SignedMultiplicativeInverse(-1)) returns typemin(Int) instead of throwing like div(typemin(Int), -1)
using Base.MultiplicativeInverses: multiplicativeinverse
mi = multiplicativeinverse(-1)
q = try div(typemin(Int), mi) catch e typeof(e) end
d = try div(typemin(Int), -1) catch e typeof(e) end
qr = try divrem(typemin(Int8), multiplicativeinverse(Int8(-1))) catch e typeof(e) end
dr = try divrem(typemin(Int8), Int8(-1)) catch e typeof(e) end
println("div(typemin(Int), multiplicativeinverse(-1)) = ", q, "; div(typemin(Int), -1) -> ", d)
println("divrem(typemin(Int8), multiplicativeinverse(Int8(-1))) = ", qr, "; divrem(typemin(Int8), Int8(-1)) -> ", dr)
if q == typemin(Int) && d == DivideError && qr == (typemin(Int8), Int8(0)) && dr == DivideError
    println("REPRODUCED reinterpretarrays-smi-div-typemin")
end
