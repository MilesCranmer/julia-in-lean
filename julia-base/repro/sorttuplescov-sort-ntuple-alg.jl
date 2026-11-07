function reproduced()
    x = (2, 1)
    sort(x) == (1, 2) || return false
    try
        sort(x; alg=Base.Sort.InsertionSort)
        false
    catch e
        e isa MethodError
    end
end
println(reproduced() ? "REPRODUCED sorttuplescov-sort-ntuple-alg" : "NOT_REPRODUCED sorttuplescov-sort-ntuple-alg")
