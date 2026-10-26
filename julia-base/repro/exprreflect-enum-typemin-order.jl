@enum OutOfOrderEnum::Int8 high=5 low=-2 top=9

actual = Int(typemin(OutOfOrderEnum))
expected = minimum(Int.(instances(OutOfOrderEnum)))
println("instances: ", Int.(instances(OutOfOrderEnum)))
println("Int(typemin(OutOfOrderEnum)): ", actual)
println("minimum instance value: ", expected)

if actual != expected
    println("REPRODUCED exprreflect-enum-typemin-order")
else
    println("NOT REPRODUCED exprreflect-enum-typemin-order")
end
