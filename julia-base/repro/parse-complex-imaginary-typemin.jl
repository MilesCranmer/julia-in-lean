println("JULIA ", VERSION, " COMMIT ", Base.GIT_VERSION_INFO.commit)
@assert string(Base.GIT_VERSION_INFO.commit) in (
    "45b6d15e34bbd2003a31acce0b1847b63dad029c",
    "f755f49a9e41380d7da126b3c1db9fe7f83dd027",
)

let reproduced = true
for T in (Int8, Int64)
    minimum = typemin(T)
    pure = string(minimum, "im")
    mixed = string("0", minimum, "im")
    expected = Complex{T}(0, minimum)
    scalar = parse(T, string(minimum))
    pure_result = parse(Complex{T}, pure)
    try_result = tryparse(Complex{T}, mixed)
    parse_result = try
        parse(Complex{T}, mixed)
    catch err
        err
    end
    println(T, " scalar = ", scalar)
    println(T, " pure imaginary accepted = ", pure_result == expected)
    println(T, " mixed string = ", repr(mixed))
    println(T, " tryparse = ", repr(try_result))
    println(T, " parse = ", parse_result isa Exception ? sprint(showerror, parse_result) : repr(parse_result))
    reproduced &= scalar == minimum && pure_result == expected &&
        try_result === nothing && parse_result isa OverflowError
end

println(reproduced ? "REPRODUCED parse-complex-imaginary-typemin" : "NOT REPRODUCED parse-complex-imaginary-typemin")
end
