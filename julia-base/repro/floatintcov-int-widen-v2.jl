x = UInt8(0)
y = typemax(UInt8)
actual = widen(x) - widen(y)
expected = Int(x) - Int(y)

if actual != expected && actual == UInt16(65281)
    println("REPRODUCED floatintcov-int-widen-v2")
else
    println("NOT_REPRODUCED floatintcov-int-widen-v2")
end
