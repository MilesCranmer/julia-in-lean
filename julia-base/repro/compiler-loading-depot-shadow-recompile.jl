# A package inside a later depot is recompiled on every `using` when an earlier depot holds a copy
# of its files at the same depot-relative path.
#
# The cache records the sources as `@depot/dev/TwoDepot/...`. parse_cache_header resolves the tag
# to the first depot on DEPOT_PATH that has all of them, the earlier copy, so stale_cachefile sees
# a source path different from the one the manifest locates and rejects the cache with
# :source_path_changed. The cache written by the recompile records the same tag, so the next
# session rejects it again. Prints REPRODUCED when the second and third sessions both recompile.

const ID = "compiler-loading-depot-shadow-recompile"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)
root = mktempdir()
d1 = joinpath(root, "d1"); d2 = joinpath(root, "d2")
for d in (d1, d2)
    p = joinpath(d, "dev", "TwoDepot")
    mkpath(joinpath(p, "src"))
    write(joinpath(p, "Project.toml"), "name = \"TwoDepot\"\nuuid = \"5d0c7a8e-2b9f-4f61-8a3e-0d1c2b3a4f55\"\nversion = \"0.1.0\"\n")
    write(joinpath(p, "src", "TwoDepot.jl"), "module TwoDepot\nf() = 1\nend\n")
end
envdir = joinpath(root, "env"); mkpath(envdir)
write(joinpath(envdir, "Project.toml"), "[deps]\nTwoDepot = \"5d0c7a8e-2b9f-4f61-8a3e-0d1c2b3a4f55\"\n")
write(joinpath(envdir, "Manifest.toml"), """
manifest_format = "2.0"
[[deps.TwoDepot]]
path = $(repr(joinpath(d1, "dev", "TwoDepot")))
uuid = "5d0c7a8e-2b9f-4f61-8a3e-0d1c2b3a4f55"
""")
env = Dict("JULIA_DEPOT_PATH" => "$d2:$d1:", "JULIA_LOAD_PATH" => "$envdir:@stdlib", "JULIA_PKG_PRECOMPILE_AUTO" => "0")
julia = Base.julia_cmd()
child = joinpath(root, "child.jl")
write(child, """
pkg = Base.PkgId(Base.UUID("5d0c7a8e-2b9f-4f61-8a3e-0d1c2b3a4f55"), "TwoDepot")
println("isprecompiled before: ", Base.isprecompiled(pkg))
reasons = Dict{Symbol,Int}()
try
    for p in Base.find_all_in_cache_path(pkg)
        Base.stale_cachefile(pkg, UInt128(0), Base.locate_package_load_spec(pkg), p; reasons)
    end
    println("reasons: ", reasons)
catch
end
using TwoDepot
println("loaded ", pathof(TwoDepot))
""")
outs = String[]
for i in 1:3
    out = read(pipeline(ignorestatus(addenv(`$julia --startup-file=no $child`, env)); stderr=devnull), String)
    println("--- session $i"); print(out)
    push!(outs, out)
end
recompiled(out) = occursin("isprecompiled before: false", out) && occursin("loaded ", out)
println(recompiled(outs[2]) && recompiled(outs[3]) ? "REPRODUCED $ID" : "NOT REPRODUCED $ID")
