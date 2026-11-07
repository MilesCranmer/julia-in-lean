# Two distinct mutable objects with equal contents fit in an ordinary tiny IdSet.
# Use documented collection functions only; do not alter Julia internals.
let reproduced = false
    try
        left = [1]
        right = [1]
        values = Base.IdSet{Vector{Int}}([left, right])
        observed = collect(values)
        reproduced = length(values) == 2 && left !== right &&
            isequal(left, right) && allunique(values) &&
            !allunique(observed) && !allequal(values) && allequal(observed)
    catch
        reproduced = false
    end
    println(reproduced ? "REPRODUCED bitsetscov-allunique-idset" :
                         "NOT_REPRODUCED bitsetscov-allunique-idset")
end
