r = Int8(-1):Int8(1)
@assert !isempty(r)
@assert r[1] == first(r) == -1
try
    r[UInt8(1)]
catch e
    if e isa BoundsError
        println("REPRODUCED ranges-ordinal-unsigned-index")
    else
        rethrow()
    end
end
