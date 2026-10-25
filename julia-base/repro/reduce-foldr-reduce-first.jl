a = foldr(+, [true])
b = foldl(+, [true])
c = foldr(*, ['a'])
d = foldr(hcat, [[1, 2]])
v = [1, 2]
e = foldr(vcat, [v]) === v
println(repr(a), " ", repr(b), " ", repr(c), " ", typeof(d), " ", e)
if a === true && b === 1 && c === 'a' && d isa Vector && e
    println("REPRODUCED reduce-foldr-reduce-first")
end
