println(sort([3, 1, 2]; alg=QuickSort))
err = try
    sort((3, 1, 2); alg=QuickSort)
catch e
    e
end
println(typeof(err))
if err isa MethodError && err.f === Base.Sort._sort
    println("REPRODUCED sorttuplescov-sort-ntuple-alg")
end
