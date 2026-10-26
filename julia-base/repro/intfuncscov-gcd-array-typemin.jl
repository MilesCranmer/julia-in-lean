v = [typemin(Int), 2]
pairwise = gcd(v[1], v[2])
varargs = gcd(v...)
arr = try
    gcd(v)
catch e
    e
end
println("gcd(typemin(Int), 2) = ", pairwise)
println("gcd(typemin(Int), 2, 4) = ", gcd(typemin(Int), 2, 4))
println("gcd([typemin(Int), 2]) = ", arr isa Exception ? sprint(showerror, arr) : arr)
if pairwise == 2 && varargs == 2 && arr isa OverflowError
    println("REPRODUCED intfuncscov-gcd-array-typemin")
else
    println("not reproduced")
end
