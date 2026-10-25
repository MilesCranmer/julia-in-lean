# splitprec(Float64, i), documented as exact for every Int64/UInt64, throws for
# i >= 2^63 - 512, so converting an integer range near typemax(Int) to a Float64
# StepRangeLen throws InexactError.
for f in (() -> Base.splitprec(Float64, typemax(Int) - 512),
          () -> Base.splitprec(Float64, typemax(UInt64)),
          () -> [typemax(Int)-1:typemax(Int), 0.5:1.0:1.5],
          () -> Base.splitprec(Float64, typemax(Int) - 511))
    try
        println(repr(f()))
    catch e
        println("throws ", sprint(showerror, e))
    end
end
try
    StepRangeLen{Float64}(typemax(Int)-1:typemax(Int))
catch e
    println("StepRangeLen{Float64}(typemax(Int)-1:typemax(Int)) throws ", sprint(showerror, e))
    e isa InexactError && println("REPRODUCED floatranges-splitprec-typemax")
end
