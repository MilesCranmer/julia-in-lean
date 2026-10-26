# sort!(v; scratch) accepts scratch::Vector{eltype(v)}, but for v with eltype
# Union{Missing, T} the radix path reinterprets the scratch vector as T and throws.
v = Union{Missing, Int32}[Int32(i * 7919 % 100000) for i in 1:3000]
w = copy(v)
sort!(w)                       # sorts
err = try
    sort!(v; scratch = Union{Missing, Int32}[])
    nothing
catch e
    e
end
println(issorted(w), " ", err isa Exception ? typeof(err) : err)
if err isa ArgumentError
    println("REPRODUCED sorttuplescov-sort-missing-scratch")
end
