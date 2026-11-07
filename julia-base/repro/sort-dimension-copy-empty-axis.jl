# sort(A; dims) on a matrix whose sorted dimension has length 0 throws, although sort!(A; dims)
# and sort(A; dims) along the other (nonempty) dimension both return an empty array.
A = zeros(0, 3)
r = try
    sort(A; dims=1)
catch e
    e
end
println("sort(zeros(0, 3); dims=1) -> ", r isa Exception ? sprint(showerror, r) : summary(r))
inplace = sort!(copy(A); dims=1)
other = sort(A; dims=2)
println("sort!(copy(A); dims=1) -> ", summary(inplace), "; sort(A; dims=2) -> ", summary(other))
if r isa ArgumentError && size(inplace) == (0, 3) && size(other) == (0, 3)
    println("REPRODUCED sort-dimension-copy-empty-axis")
end
