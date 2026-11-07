A = Base.IdentityUnitRange(-2:2)
expected = A[firstindex(A)]

function observes_nth(A, n, expected)
    try
        actual = Iterators.nth(A, n)
        println("$(typeof(n)): returned $actual")
        return actual == expected
    catch err
        err isa BoundsError || rethrow()
        println("$(typeof(n)): BoundsError")
        return false
    end
end

println("expected first element: $expected")
u64_ok = observes_nth(A, UInt64(1), expected)
u128_ok = observes_nth(A, UInt128(1), expected)

if !u64_ok || !u128_ok
    println("REPRODUCED iterators-nth-unsigned-offset")
else
    println("NOT REPRODUCED iterators-nth-unsigned-offset")
end
