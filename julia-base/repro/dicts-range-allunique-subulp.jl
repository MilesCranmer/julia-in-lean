# A two-element Float64 range whose nonzero step is one quarter of the ULP at 1.
# Both stored observations round to 1.0; no large allocation is involved.
let reproduced = false
    try
        values = range(1.0; step=eps(1.0) / 4, length=2)
        observed = collect(values)
        reproduced = length(values) == 2 && !iszero(step(values)) &&
            isequal(observed[1], observed[2]) && allunique(values) &&
            !allunique(observed) && !allequal(values) && allequal(observed)
    catch
        reproduced = false
    end
    println(reproduced ? "REPRODUCED dicts-range-allunique-subulp" :
                         "NOT_REPRODUCED dicts-range-allunique-subulp")
end
