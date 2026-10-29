# Julia master f755f49a9e41380d7da126b3c1db9fe7f83dd027
using Test

@test accumulate(+, [1, 2]; dims=2, init=10) == [11, 12]
@test accumulate(+, [1 2; 3 4]; dims=3, init=10) == [11 12; 13 14]
@test foldr(+, [true]) === 1
@test foldr(*, ['a']) == "a"
@test foldr(hcat, [[1, 2]]) == reshape([1, 2], 2, 1)
v = [1, 2]
@test foldr(vcat, [v]) == v
@test foldr(vcat, [v]) !== v
@test sum(Iterators.flatten([Int[], Int[]])) === 0

s = Set([false])
@test_throws InexactError union!(s, Any[true, 2])
@test s == Set([false, true])


p = :first => :second
@test iterate(p) === (:first, 2)
@test iterate(p, 2) === (:second, 3)
@test iterate(p, 3) === nothing
@test_throws BoundsError iterate(p, 0)

for a in (Bool[], [false], [true], [false, true], [true, false], fill(false, 65), fill(true, 65)),
    b in (Bool[], [false], [true], [false, true], [true, false], fill(false, 65), fill(true, 65))
    @test cmp(BitVector(a), BitVector(b)) == cmp(a, b)
end
println("COLLECTIONS TARGET CHECKS PASSED")
