r = Int64(0):typemin(Int64):typemin(Int64)
@assert collect(r) == [Int64(0), typemin(Int64)]
@assert length(r) == 2
try
    Base.checked_length(r)
catch e
    if e isa InexactError
        println("REPRODUCED ranges-ordinal-typemin-checked-length")
    else
        rethrow()
    end
end
