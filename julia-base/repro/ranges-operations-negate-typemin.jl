r = typemin(Int8):Int8(1):Int8(-126)
s = -r
wide = typemin(Int):3:typemin(Int)+20
@assert length(wide) == 7 && isempty(-wide)
if s[2] == -129 && (-collect(r))[2] == 127
    println("REPRODUCED ranges-operations-negate-typemin")
else
    error("range negation overflow did not reproduce: $s")
end
