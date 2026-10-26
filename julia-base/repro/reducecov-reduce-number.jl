# reduce(op, x::Number) = x (base/reduce.jl:500) returns the number itself, while every
# other single-element reduction applies reduce_first(op, x): a Number iterates as a
# one-element collection, and mapreduce, foldl and reduce over (x,) all widen or wrap.
r1 = reduce(+, true)
m1 = mapreduce(identity, +, true)
t1 = reduce(+, (true,))
f1 = foldl(+, true)
r2 = reduce(hcat, 5)
t2 = reduce(hcat, (5,))
r3 = reduce(Base.add_sum, Int8(1))
s3 = sum(Int8(1))
println("reduce(+, true) = ", repr(r1), "; mapreduce(identity, +, true) = ", repr(m1),
        "; reduce(+, (true,)) = ", repr(t1), "; foldl(+, true) = ", repr(f1))
println("reduce(hcat, 5) = ", repr(r2), "; reduce(hcat, (5,)) = ", repr(t2))
println("reduce(Base.add_sum, Int8(1)) = ", repr(r3), "; sum(Int8(1)) = ", repr(s3))
if r1 === true && m1 === 1 && t1 === 1 && r2 === 5 && t2 isa Matrix
    println("REPRODUCED reducecov-reduce-number")
end
