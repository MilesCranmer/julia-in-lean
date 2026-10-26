signed_zero = indexin([-0.0], [0.0])
nan = indexin([NaN], [NaN])

println("-0.0 in [0.0]: ", -0.0 in [0.0], "; indexin: ", signed_zero)
println("NaN in [NaN]: ", NaN in [NaN], "; indexin: ", nan)
println("Expected: [1] for signed zero and [nothing] for NaN")

if signed_zero == Union{Nothing,Int}[nothing] && nan == Union{Nothing,Int}[1]
    println("REPRODUCED arraycov-indexin-isequal")
else
    println("NOT REPRODUCED arraycov-indexin-isequal")
end
