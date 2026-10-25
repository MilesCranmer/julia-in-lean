x = UInt8(0)
y = typemax(UInt8)
wx = widen(x)
wy = widen(y)
actual = wx - wy
expected = Int(x) - Int(y)

println("typeof(widen(UInt8(0))) = ", typeof(wx))
println("widen(UInt8(0)) - widen(typemax(UInt8)) = ", actual)
println("exact difference = ", expected)

if actual != expected && actual == UInt16(65281)
    println("REPRODUCED hashops-widen-unsigned-sub")
else
    println("NOT REPRODUCED")
end
