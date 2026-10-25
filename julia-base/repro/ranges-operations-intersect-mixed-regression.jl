r = UInt8(0):UInt8(255)
s = Int8(-100):Int8(7):Int8(117)
try
    t = intersect(r,s)
    if first(t) == 2 && last(t) == 114 && !(UInt8(2) in s)
        println("REPRODUCED ranges-operations-intersect-mixed-regression")
    else
        error("mixed intersection regression did not reproduce")
    end
catch e
    if e isa InexactError
        println("NOT REPRODUCED ranges-operations-intersect-mixed-regression: InexactError")
    else
        rethrow()
    end
end
