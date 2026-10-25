# circcopy! throws DivideError when the arrays are empty and their axes differ.
src = zeros(Int, 2, 0)
dest = view(zeros(Int, 3, 0), Base.IdentityUnitRange(2:3), :)   # 2x0, axes (2:3, 1:0)
r1 = try circcopy!(dest, src); "ok" catch e; e end
src1 = zeros(Int, 0)
dest1 = view(zeros(Int, 3), Base.IdentityUnitRange(3:2))         # empty, axes 3:2
r2 = try circcopy!(dest1, src1); "ok" catch e; e end
# non-empty arrays with the same offset work, and so do empty arrays with equal axes
r3 = try circcopy!(view(zeros(Int, 3, 1), Base.IdentityUnitRange(2:3), :), [1 ; 2;;]); "ok" catch e; e end
r4 = try circcopy!(zeros(Int, 2, 0), zeros(Int, 2, 0)); "ok" catch e; e end
println(repr(r1), " ", repr(r2), " ", repr(r3), " ", repr(r4))
if r1 isa DivideError && r2 isa DivideError && r3 == "ok" && r4 == "ok"
    println("REPRODUCED multidim-circcopy-empty")
end
