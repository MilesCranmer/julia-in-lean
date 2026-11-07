# The input is a three-element tuple and one scalar count. Julia rejects the
# requested internal buffer size before allocating it.
function reproduced()
    Sys.WORD_SIZE == 64 || return false
    p = Iterators.partition((1, 2, 3), Int(1) << 62)
    try
        iterate(p)
        return false
    catch e
        return e isa ArgumentError && occursin("invalid", sprint(showerror, e))
    end
end
ok = try reproduced() catch; false end
println(ok ? "REPRODUCED iterators-partition-generic-alloc" : "NOT_REPRODUCED iterators-partition-generic-alloc")
