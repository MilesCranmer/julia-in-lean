const P = Base.Precompilation
X, Y, Z, W = Base.PkgId("X"), Base.PkgId("Y"), Base.PkgId("Z"), Base.PkgId("W")
# Y <-> X is one cycle and Z <-> W another; X also depends on Z.
dmap = Dict(Y => [X], X => [Y, Z], Z => [W], W => [Z])
stack = Base.PkgId[]
could_be_cycle = Dict{Base.PkgId,Bool}()
cycles = Vector{Base.PkgId}[]
P.scan_pkg!(stack, could_be_cycle, cycles, Y, dmap)
println("cycles reported: ", [[p.name for p in c] for c in cycles])
io = IOContext{IO}(stdout, Base.ImmutableDict{Symbol,Any}())
msg = P.excluded_circular_deps_explanation(io, Dict{Base.PkgId,Base.PkgId}(), [Y, X, Z, W], cycles)
println(msg)
in_reported = Set(p for c in cycles for p in c)
if !(X in in_reported) || !(Y in in_reported)
    println("REPRODUCED runtimecov-scan-deps-unreported-cycle")
end
