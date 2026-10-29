# eachindex(A, B) is documented to throw DimensionMismatch when the arrays have
# different sizes, but for two linear-indexing arrays of equal length it returns
# the common linear range.
A = zeros(2, 3)
B = zeros(3, 2)
r = try
    eachindex(A, B)
catch e
    e
end
println(repr(r))
println(repr(try eachindex(zeros(6), A) catch e e end))
if !(r isa DimensionMismatch)
    println("REPRODUCED abstractarrayspecs-eachindex-size-mismatch")
else
    println("NOT REPRODUCED")
end
