# Public alias growth adds a true tail bit to a logically false 1x1 parent.
let reproduced = false
    try
        parent = falses(1, 1)
        grown = vec(parent)
        push!(grown, true)
        reproduced = size(parent) == (1, 1) && parent[1, 1] == false &&
            maximum(collect(parent)) == false && maximum(parent) == true &&
            length(grown) == 2 && collect(grown) == [false, true]
    catch
        reproduced = false
    end
    println(reproduced ? "REPRODUCED bitarray-scalar-extrema-values" :
                         "NOT_REPRODUCED bitarray-scalar-extrema-values")
end
