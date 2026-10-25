r = Int8(-100):Int8(2):Int8(120)
i = findfirst(==(Int8(100)), r)
u = Int8(-128):Int8(127)
@assert findfirst(==(Int8(0)), u) == -127
@assert findfirst(==(Int8(127)), u) == 0
if i == -27 && findfirst(==(Int8(100)), collect(r)) == 101
    println("REPRODUCED ranges-operations-findfirst-overflow")
else
    error("findfirst overflow did not reproduce: $i")
end
