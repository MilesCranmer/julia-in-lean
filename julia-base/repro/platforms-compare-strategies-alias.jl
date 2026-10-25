using Base.BinaryPlatforms
cs = Dict{String,Function}()
p1 = Platform("x86_64", "linux"; julia_version = "1.6.0", compare_strategies = cs)
println("caller's compare_strategies after constructing p1: ", collect(keys(cs)))
p2 = Platform("x86_64", "linux"; compare_strategies = cs)
p3 = Platform("x86_64", "linux")
println("tags(p2) == tags(p3): ", tags(p2) == tags(p3), "; p2 == p3: ", p2 == p3)
r = try
    Platform("x86_64", "linux"; julia_version = "1.6.0",
             compare_strategies = Dict("foo" => Base.BinaryPlatforms.compare_version_cap))
catch e
    e
end
println("concretely typed compare_strategies => ", r isa Exception ? typeof(r) : repr(r))
if !isempty(cs) && p2 != p3
    println("REPRODUCED platforms-compare-strategies-alias")
end
