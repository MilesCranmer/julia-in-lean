# Tuple conversion should consume the requested number of elements in iteration order.
function reproduce()
    a = reshape(UInt8.(1:32), 4, 8)
    expected = Tuple(vec(a))
    @assert NTuple{31,UInt8}(a) == expected[1:31]
    @assert NTuple{32,UInt8}(vec(a)) == expected
    result = try
        NTuple{32,UInt8}(a)
    catch err
        err
    end
    if result isa ArgumentError && occursin("non-integral first dimension", sprint(showerror, result))
        println("NTuple{32,UInt8}(4x8 Matrix) throws: ", sprint(showerror, result))
        println("REPRODUCED reinterpretarray-totuple")
    elseif result == expected
        println("NTuple{32,UInt8}(4x8 Matrix) returned all 32 values")
        println("NOT REPRODUCED reinterpretarray-totuple")
    else
        error("unexpected tuple conversion result: ", repr(result))
    end
end
reproduce()
