u = Int8(-128):Int8(127)
s = Int8(-100):Int8(2):Int8(120)
a = findfirst(iszero, u)
b = findfirst(isone, u)
c = findlast(==(Int8(0)), u)
d = findlast(==(Int8(100)), s)
e = findlast(iszero, u)
expected = (findfirst(iszero, collect(u)), findfirst(isone, collect(u)),
    findlast(==(Int8(0)), collect(u)), findlast(==(Int8(100)), collect(s)))
if (a, b, c, d, e) == (-127, -126, -127, -27, -127) && expected == (129, 130, 129, 101)
    println("REPRODUCED array-range-target-search-overflow")
else
    error("range target search overflow did not reproduce: $((a, b, c, d, e)) vs $expected")
end
