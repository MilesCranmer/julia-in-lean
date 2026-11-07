let
    x = UInt8(1) // UInt8(0)
    ok1 = try
        round(x, RoundNearest)
        false
    catch err
        err isa OverflowError
    end
    ok2 = try
        round(x)
        false
    catch err
        err isa OverflowError
    end
    if ok1 && ok2
        println("REPRODUCED intarith-round-unsigned-rational-infinity")
        println("REPRODUCED rational-default-rounding-selected")
    else
        println("NOT_REPRODUCED intarith-round-unsigned-rational-infinity")
    end
end
