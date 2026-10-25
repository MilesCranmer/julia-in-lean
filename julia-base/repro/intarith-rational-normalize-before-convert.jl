# Both normalized components fit Int8, but conversion precedes sign normalization.
function main()
    expected = Int8(-128) // Int8(1)
    observed = try
        Rational{Int8}(Int16(128), Int16(-1))
    catch e
        e
    end
    if observed isa InexactError && expected == -128
        println("actual: ", typeof(observed), "; expected: ", expected)
        println("REPRODUCED intarith-rational-normalize-before-convert")
    else
        error("expected premature InexactError, got $(repr(observed))")
    end
end
main()
