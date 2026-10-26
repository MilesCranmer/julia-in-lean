inputs = ("nan(foo)", "nan(_)", "nan(0x)")
values = tryparse.(Float64, inputs)
for (input, value) in zip(inputs, values)
    println("tryparse(Float64, ", repr(input), ") = ", repr(value))
end
if all(x -> x isa Float64 && isnan(x), values)
    println("REPRODUCED nummisc-float-nan-invalid-payload")
end
