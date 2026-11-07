# A 260-element input reaches BracketedSort's minimum/maximum of the empty target.
let
    id = "sort-partialsort-empty-range"
    reproduced = try
        partialsort!(fill(1, 260), 1:1:0)
        false
    catch error
        error isa ArgumentError
    end
    println((reproduced ? "REPRODUCED " : "NOT_REPRODUCED ") * id)
end
