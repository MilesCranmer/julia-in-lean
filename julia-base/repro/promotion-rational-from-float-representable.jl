# Rational{T}(x::AbstractFloat) throws InexactError although x is exactly a Rational{T}
a = try Rational{Int8}(-128.0) catch e; e end
println("Rational{Int8}(-128.0) = ", a, "  (Int8(-128.0) = ", Int8(-128.0), ")")
x = nextfloat(Float16(0.0))   # 2^-24
b = try Rational{Int32}(x) catch e; e end
println("Rational{Int32}(nextfloat(Float16(0.0))) = ", b, "  (x == 1//16777216: ", x == 1//16777216, ")")
if a isa InexactError || b isa InexactError
    println("REPRODUCED promotion-rational-from-float-representable")
end
