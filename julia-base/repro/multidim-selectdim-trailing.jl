# selectdim(A, d, i) is documented as view(A, :, ..., :, i, :, ...) with i in position d,
# but for d > ndims(A) it throws for a valid index collection and drops dimensions.
A = [1 2 3; 4 5 6]
v1 = try size(view(A, :, :, 1:1)) catch e; e end
s1 = try size(selectdim(A, 3, 1:1)) catch e; e end
v2 = try size(view(A, :, :, :, 1)) catch e; e end
s2 = try size(selectdim(A, 4, 1)) catch e; e end
println("view(A,:,:,1:1) ", repr(v1), "  selectdim(A,3,1:1) ", repr(s1))
println("view(A,:,:,:,1) ", repr(v2), "  selectdim(A,4,1) ", repr(s2))
if v1 == (2, 3, 1) && s1 isa BoundsError && v2 == (2, 3, 1) && s2 == (2, 3)
    println("REPRODUCED multidim-selectdim-trailing")
end
