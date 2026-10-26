# Docstring of Base.Ryu.decimallength (base/ryu/utils.jl:89-93): "The number of decimal
# digits of the integer `v`." The generic method stops at 17 and the UInt32 method at 9.
v64 = UInt64(10)^17
v32 = UInt32(10)^9
println("decimallength($v64) = ", Base.Ryu.decimallength(v64), ", ndigits = ", ndigits(v64))
println("decimallength($v32) = ", Base.Ryu.decimallength(v32), ", ndigits = ", ndigits(v32))
if Base.Ryu.decimallength(v64) != ndigits(v64) && Base.Ryu.decimallength(v32) != ndigits(v32)
    println("REPRODUCED misccov-ryu-decimallength-doc")
end
