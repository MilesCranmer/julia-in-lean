let A = [10, 20], I = 0:3, default = 99
    expected = [99, 10, 20, 99]
    outcome = try
        get(A, I, default)
    catch error
        error
    end
    println("A = ", A, ", I = ", I, ", default = ", default)
    println("expected = ", expected)
    if outcome isa Exception
        showerror(stdout, outcome)
        println()
    else
        println("actual = ", outcome)
    end
    @assert outcome != expected
    println("REPRODUCED abstractarrays-get-range-default")
end

let A = [10, 20], I = 1:2, default = 99
    outcome = try
        get(A, I, default)
    catch error
        error
    end
    println("A = ", A, ", I = ", I, ", default = ", default)
    println("expected = ", A)
    if outcome isa Exception
        showerror(stdout, outcome)
        println()
    else
        println("actual = ", outcome)
    end
    @assert outcome != A
    println("REPRODUCED abstractarrays-get-range-default-ordinary")
end
