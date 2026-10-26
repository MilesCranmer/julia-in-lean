# parse(Complex{T}, s) ignores characters after the last 'm'/'i'/'j' of s.
# The parse docstring (base/parse.jl:5-13) says an error is raised if the string
# does not contain a valid number.
results = Any[]
for s in ("1+2imabc", "2imfoo", "1+2jxyz")
    r = try
        parse(ComplexF64, s)
    catch e
        e
    end
    println(repr(s), " => ", repr(r))
    push!(results, r)
end
t = tryparse(Complex{Int}, "1+2im!")
println("tryparse(Complex{Int}, \"1+2im!\") => ", repr(t))
if any(r -> r isa Complex, results) || t !== nothing
    println("REPRODUCED docssyntaxcov-parse-complex-trailing")
end
