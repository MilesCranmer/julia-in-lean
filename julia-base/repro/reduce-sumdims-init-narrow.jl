A = Int8[100; 100;;]
whole = sum(vec(A); init=Int8(0))
r = try
    sum(A; dims=1, init=Int8(0))
catch err
    err
end
println(repr(whole), " ", r isa Exception ? typeof(r) : repr(r))
if whole === 200 && r isa InexactError
    println("REPRODUCED reduce-sumdims-init-narrow")
end
