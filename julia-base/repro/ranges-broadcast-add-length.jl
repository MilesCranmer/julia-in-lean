r = Int8(126):Int8(127)
s = r .+ Int8(1)
expected = [x + Int8(1) for x in r]
println("(Int8(126):Int8(127)) .+ Int8(1) = ", repr(s))
println("length = ", length(s))
println("elementwise result = ", repr(expected))
length(s) == 0 && expected == Int8[127, -128] && println("REPRODUCED ranges-broadcast-add-length")
