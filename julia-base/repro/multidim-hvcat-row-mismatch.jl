# hvcat with rows of different lengths throws ArgumentError when all values have the same
# Number type, but DimensionMismatch when the Number types differ (or for arrays).
r1 = try hvcat((2, 1), 1, 2, 3) catch e; e end        # same type
r2 = try hvcat((2, 1), 1, 2.0, 3) catch e; e end      # mixed types
r3 = try hvcat((1, 3), 1, 2, 3, 4) catch e; e end
r4 = try hvcat((1, 3), 1, 2.0, 3, 4) catch e; e end
r5 = try hvcat((2, 1), [1;;], [2;;], [3;;]) catch e; e end   # 1x1 arrays
println(repr(r1), "\n", repr(r2), "\n", repr(r3), "\n", repr(r4), "\n", repr(r5))
if r1 isa ArgumentError && r2 isa DimensionMismatch && r3 isa ArgumentError && r4 isa DimensionMismatch
    println("REPRODUCED multidim-hvcat-row-mismatch")
end
