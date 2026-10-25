# stride(V, k) throws for a zero-dimensional view, while it returns 1 for a zero-dimensional Array.
A = zeros(3, 4)
V = view(A, 1, 2)                 # 0-dimensional SubArray, strides(V) == ()
r = try stride(V, 1) catch e; e end
println("strides(V) = ", strides(V))
println("stride(view(zeros(3, 4), 1, 2), 1) = ", r isa Exception ? sprint(showerror, r) : r)
println("stride(fill(0.0), 1) = ", stride(fill(0.0), 1))
println("stride(copy(V), 1) = ", stride(copy(V), 1))
if r isa Exception
    println("REPRODUCED broadcastviews-stride-zero-dim")
end
