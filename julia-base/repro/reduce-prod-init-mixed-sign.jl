a = prod(Int8[-1]; init=0x01)
b = prod(Int8[16, 16]; init=0x01)
c = prod(Int8[16, 16])
s = sum(Int8[-1]; init=0x00)
println(repr(a), " ", repr(b), " ", repr(c), " ", repr(s))
if a === 0xff && b === 0x00 && c === 256
    println("REPRODUCED reduce-prod-init-mixed-sign")
end
