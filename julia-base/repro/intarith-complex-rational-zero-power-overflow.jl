let
    z = complex(Int8(12) // Int8(1), Int8(0) // Int8(1))
    x = Int8(12) // Int8(1)
    n = Int8(0)
    ok1 = try
        ^(z, n)
        false
    catch err
        err isa OverflowError
    end
    ok2 = try
        ^(x, n)
        false
    catch err
        err isa OverflowError
    end
    if ok1 && ok2
        println("REPRODUCED intarith-complex-rational-zero-power-overflow")
        println("REPRODUCED rational-power-native-rational-integer")
    else
        println("NOT_REPRODUCED intarith-complex-rational-zero-power-overflow")
    end
end
