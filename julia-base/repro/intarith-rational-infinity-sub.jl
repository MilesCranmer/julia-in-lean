# Infinity minus a finite rational must preserve the infinity.
function main()
    x = UInt8(1) // UInt8(0)
    y = UInt8(1) // UInt8(1)
    observed = try
        x - y
    catch e
        e
    end
    if observed isa OverflowError
        println("actual: ", typeof(observed), "; expected: ", x)
        println("REPRODUCED intarith-rational-infinity-sub")
    else
        error("expected unsigned infinity subtraction OverflowError, got $(repr(observed))")
    end
end
main()
