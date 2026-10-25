# in!(x, s) is documented as `in(x, s) ? true : (push!(s, x); false)`, but the
# Set method converts x to the element type without the isequal check that
# push! performs.
s1 = Set{Float32}()
r1 = in!(0.1, s1)
r2 = try
    push!(Set{Float32}(), 0.1)
    "no error"
catch e
    sprint(showerror, e)
end
println("in!(0.1, Set{Float32}()) = ", r1, "; set afterwards: ", s1)
println("push!(Set{Float32}(), 0.1) throws: ", r2)
s2 = Set{Float32}([0.1f0])
println("in(0.1, Set{Float32}([0.1f0])) = ", 0.1 in s2, ", in!(0.1, same set) = ", in!(0.1, s2))
if r1 == false && 0.1f0 in s1 && startswith(r2, "TypeError") && !(0.1 in Set{Float32}([0.1f0])) && in!(0.1, Set{Float32}([0.1f0]))
    println("REPRODUCED dicts-set-in-bang-convert")
end
