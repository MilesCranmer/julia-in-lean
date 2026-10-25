# a:s:b with an infinite or NaN endpoint throws InexactError, while
# range(a, b; length=n) reports the same input as an ArgumentError.
for (a, s, b) in ((0.0, 1.0, Inf), (0.0, 1.0, NaN), (NaN, 1.0, 2.0))
    try
        println("$a:$s:$b = ", a:s:b)
    catch e
        println("$a:$s:$b throws ", sprint(showerror, e))
    end
end
try
    range(0.0, Inf; length=3)
catch e
    println("range(0.0, Inf; length=3) throws ", sprint(showerror, e))
end
try
    0.0:1.0:Inf
catch e
    e isa InexactError && println("REPRODUCED floatranges-colon-nonfinite-error")
end
