function reproduced(n)
    v = Union{Missing,Int32}[Int32(mod(137*i,1000)*1_000_000) for i in 1:n]
    v[17] = missing
    scratch = Union{Missing,Int32}[missing for _ in 1:n]
    expected = sort(v)
    issorted(expected) || return false
    try
        sort!(copy(v); scratch=scratch)
        false
    catch e
        e isa ArgumentError && occursin("reinterpret", sprint(showerror, e))
    end
end
large = reproduced(1000)
small = reproduced(98)
println(large ? "1000-element case: REPRODUCED" : "1000-element case: NOT_REPRODUCED")
println(small ? "98-element case: REPRODUCED" : "98-element case: NOT_REPRODUCED")
println(large && small ? "REPRODUCED sorttuplescov-sort-missing-scratch" : "NOT_REPRODUCED sorttuplescov-sort-missing-scratch")
