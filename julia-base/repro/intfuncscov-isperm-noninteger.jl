res(f) = try f() catch e; sprint(showerror, e) end
t = res(() -> isperm((2.0, 1.0)))
v = res(() -> isperm([2.0, 1.0]))
tb = res(() -> isperm((true,)))
vb = res(() -> isperm([true]))
it = res(() -> invperm((2.0, 1.0)))
iv = res(() -> invperm([2.0, 1.0]))
println("isperm((2.0, 1.0)) = ", t)
println("isperm([2.0, 1.0]) = ", v)
println("isperm((true,)) = ", tb)
println("isperm([true]) = ", vb)
println("invperm((2.0, 1.0)) = ", it)
println("invperm([2.0, 1.0]) = ", iv)
if t === true && v isa String && startswith(v, "ArgumentError") && tb === true && vb isa String
    println("REPRODUCED intfuncscov-isperm-noninteger")
else
    println("not reproduced")
end
