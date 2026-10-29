let A = reshape([10, 20], 1, 2), I = [1, 5, 2], X = fill(-1, 3), default = 99
    expected = [10, 99, 20]
    result = Base.get!(X, A, I, default)
    println("A = ", A, ", I = ", I, ", default = ", default)
    println("expected = ", expected)
    println("actual = ", result)
    @assert result === X
    @assert result != expected
    println("REPRODUCED abstractarrays-get-scattered-default")
end
