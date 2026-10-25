println("lpad(\"a\", -5) = ", repr(lpad("a", -5)))
r = try
    lpad("a", typemin(Int))
catch e
    e
end
println("lpad(\"a\", typemin(Int)) = ", r isa Exception ? sprint(showerror, r) : repr(r))
q = try
    rpad("a", typemin(Int))
catch e
    e
end
println("rpad(\"a\", typemin(Int)) = ", q isa Exception ? sprint(showerror, q) : repr(q))
r isa OutOfMemoryError && println("REPRODUCED strings-lpad-typemin")
