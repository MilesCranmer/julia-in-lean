# Mixed-type integer arithmetic promotes: promote_type(UInt8, Int16) == Int16, so the
# truncated quotient of 0x0a by Int16(-3) is Int16(-3). div returns 0xfffd::UInt16.
x, y = 0x0a, Int16(-3)
println("promote_type(UInt8, Int16) = ", promote_type(UInt8, Int16))
for f in (div, rem, fld, cld, mod, divrem, fldmod)
    r = f(x, y)
    p = f(promote(x, y)...)
    println(rpad(string(f, "(0x0a, Int16(-3))"), 26), " = ", repr(r), " :: ", typeof(r),
            "   ", string(f, "(promote(...)...)"), " = ", repr(p))
end
println("div(0x0a, -3) = ", repr(div(0x0a, -3)), "   (0x0a - 3 = ", repr(0x0a - 3), ")")
q = div(x, y)
if q isa UInt16 && q == 0xfffd && div(promote(x, y)...) === Int16(-3)
    println("REPRODUCED int-div-unsigned-signed-promotes")
else
    println("NOT REPRODUCED int-div-unsigned-signed-promotes")
end
