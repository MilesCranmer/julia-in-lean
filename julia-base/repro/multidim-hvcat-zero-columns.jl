# hvcat(nbc, values...) throws DivideError for nbc == 0 instead of ArgumentError.
r1 = try hvcat(0, 1, 2) catch e; e end
r2 = try hvcat(0) catch e; e end
r3 = try hvcat(3, 1, 2) catch e; e end     # count not a multiple of nbc: ArgumentError
r4 = try hvcat(-1, 1, 2) catch e; e end
println(repr(r1), "\n", repr(r2), "\n", repr(r3), "\n", repr(r4))
if r1 isa DivideError && r2 isa DivideError && r3 isa ArgumentError
    println("REPRODUCED multidim-hvcat-zero-columns")
end
