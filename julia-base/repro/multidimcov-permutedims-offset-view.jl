function main()
    A = reshape(collect(1:12), 4, 3)
    V = view(A, Base.IdentityUnitRange(2:3), :)
    expected = permutedims(collect(V), (2, 1))

    println("axes(V) = ", axes(V))
    println("expected = ", repr(expected))

    reproduced = false
    try
        actual = permutedims(V, (2, 1))
        println("actual = ", repr(actual))
    catch e
        println("threw = ", typeof(e), ": ", sprint(showerror, e))
        reproduced = e isa DimensionMismatch
    end

    println(reproduced ? "REPRODUCED multidimcov-permutedims-offset-view" :
                         "NOT REPRODUCED multidimcov-permutedims-offset-view")
end

main()
