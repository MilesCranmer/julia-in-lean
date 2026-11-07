# Step the iterator directly so no allocation trusts its incorrect length.
function check()
    emptycycle = Iterators.cycle(Int[])
    prefix = Iterators.take(emptycycle, 3)
    return length(prefix) == 3 && iterate(prefix) === nothing
end

reproduced = try
    check()
catch
    false
end
println((reproduced ? "REPRODUCED " : "NOT_REPRODUCED ") * "iterators-cycle-empty-length")
