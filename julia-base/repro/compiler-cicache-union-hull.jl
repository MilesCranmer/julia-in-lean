# union(a, b) on WorldRange is not the hull of two overlapping ranges.
# Compiler/src/cicache.jl:22-28 returns WorldRange(a.min_world, b.max_world) after ordering by
# min_world, which cuts off a range nested in the other, and its `b.min_world - 1` wraps when
# b.min_world is 0.
const CC = Base.Compiler
id = "compiler-cicache-union-hull"
r1 = CC.union(CC.WorldRange(UInt(1), UInt(10)), CC.WorldRange(UInt(2), UInt(5)))
println("union(WorldRange(1,10), WorldRange(2,5)) = WorldRange(", r1.min_world, ", ", r1.max_world, ")")
r2 = try
    CC.union(CC.WorldRange(UInt(0), UInt(5)), CC.WorldRange(UInt(0), UInt(5)))
catch e
    e
end
println("union(WorldRange(0,5), WorldRange(0,5)) = ", r2 isa Exception ? typeof(r2) : r2)
println(r1.max_world == 5 && r2 isa AssertionError ? "REPRODUCED $id" : "NOT REPRODUCED $id")
