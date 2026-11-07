function reproduced()
    items = [1, 1]
    actual = symdiff!(BitSet(), items)
    reference = symdiff!(Set{Int}(), items)
    return isempty(actual) && (1 in reference) && length(reference) == 1
end

ok = try
    reproduced()
catch
    false
end
println(ok ? "REPRODUCED bitarrays-bitset-symdiff-duplicates" :
             "NOT_REPRODUCED bitarrays-bitset-symdiff-duplicates")
