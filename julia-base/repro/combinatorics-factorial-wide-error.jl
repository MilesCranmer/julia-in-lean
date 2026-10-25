inputs = Any[
    typemax(UInt64),
    typemax(Int128),
    typemax(UInt128),
    typemin(Int128),
    big(typemax(Culong)) + 1,
]
errors = DataType[]

for n in inputs
    try
        factorial(n)
        push!(errors, Nothing)
    catch err
        push!(errors, typeof(err))
        println("factorial(", repr(n), "::", typeof(n), "): ", nameof(typeof(err)))
    end
end

if all(==(InexactError), errors)
    println("REPRODUCED combinatorics-factorial-wide-error")
end
