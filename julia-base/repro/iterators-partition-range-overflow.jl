# Only a one-element lazy range is constructed. Do not collect the partition.
function reproduced()
    Sys.WORD_SIZE == 64 || return false
    hi = typemax(Int)
    r = Base.IdentityUnitRange(hi:hi)
    p = Iterators.partition(r, 2)
    y = iterate(p)
    y === nothing && return false
    chunk, next = y
    return firstindex(r) == hi && lastindex(r) == hi &&
        isempty(chunk) && first(chunk) == hi && last(chunk) == hi - 1 &&
        next == typemin(Int) + 1
end
ok = try reproduced() catch; false end
println(ok ? "REPRODUCED iterators-partition-range-overflow" : "NOT_REPRODUCED iterators-partition-range-overflow")
