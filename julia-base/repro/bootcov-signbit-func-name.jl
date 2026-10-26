# Core.check_sign_bit (base/boot.jl:1047-1053) names :convert only when the source
# and target widths match, but toUInt16(::Int8) etc. call it with a narrower signed
# source, so a widening conversion reports `trunc`.
function func_of(f)
    try
        f()
    catch e
        e isa InexactError || rethrow()
        return e.func
    end
    return nothing
end
a = func_of(() -> UInt16(Int16(-1)))
b = func_of(() -> UInt16(Int8(-1)))
c = func_of(() -> convert(UInt64, Int32(-5)))
println("UInt16(Int16(-1))          InexactError func = ", repr(a))
println("UInt16(Int8(-1))           InexactError func = ", repr(b))
println("convert(UInt64, Int32(-5)) InexactError func = ", repr(c))
if a === :convert && b === :trunc && c === :trunc
    println("REPRODUCED bootcov-signbit-func-name")
end
