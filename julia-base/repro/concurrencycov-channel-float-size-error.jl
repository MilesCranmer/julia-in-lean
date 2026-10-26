# Channel(sz::Float64) only special-cases Inf; other invalid float sizes reach
# convert(Int, sz) and throw InexactError instead of the constructor's ArgumentError
# "Channel size must be either 0, a positive integer or Inf" (which Channel(-1.0) throws).
function thrown(sz)
    try
        Channel(sz)
        return nothing
    catch e
        return e
    end
end
results = [sz => thrown(sz) for sz in (-1.0, -Inf, NaN, 2.5)]
for (sz, e) in results
    println("Channel(", sz, ") throws ", typeof(e), e isa ArgumentError ? ": " * e.msg : "")
end
bad = [sz for (sz, e) in results if !(e isa ArgumentError)]
println(results[1][2] isa ArgumentError && !isempty(bad) ?
    "REPRODUCED concurrencycov-channel-float-size-error" :
    "NOT REPRODUCED concurrencycov-channel-float-size-error")
