let
    r = UnitRange(Int8(5) // Int8(1), Int8(1) // Int8(0))
    c = Base.checked_length(r)
    if !isempty(r) && c === Int8(-3)
        println("REPRODUCED rational-checked-length-native-rational-range")
    else
        println("NOT_REPRODUCED rational-checked-length-native-rational-range: ", c)
    end
end
