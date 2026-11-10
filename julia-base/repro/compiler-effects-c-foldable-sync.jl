# src/staticdata.c:645-652 `effects_foldable` is meant to match `is_foldable(effects, true)`, but it
# requires noub == ALWAYS_TRUE, so a CodeInstance whose noub is NOUB_IF_NOINBOUNDS (foldable for
# the compiler) loses its non-inlineable inferred code when it is saved in a package image.
# `getnib` and `getub` differ only in noub; after loading the image, `getnib` keeps only an
# inlining-cost byte and `getub` keeps its compressed code.
const CC = Base.Compiler
id = "compiler-effects-c-foldable-sync"
dir = mktempdir()
pkg = joinpath(dir, "EffPkg"); mkpath(joinpath(pkg, "src"))
write(joinpath(pkg, "Project.toml"), "name = \"EffPkg\"\nuuid = \"8f1d6c1e-6f5e-4c55-9b3a-1c2d3e4f5a6b\"\n")
write(joinpath(pkg, "src", "EffPkg.jl"), """
module EffPkg
Base.@assume_effects :noub_if_noinbounds @noinline getnib(t::NTuple{4,Int}, i::Int) = @inbounds t[i]
@noinline getub(t::NTuple{4,Int}, i::Int) = t[i]
call(t, i) = (getnib(t, i), getub(t, i))
precompile(call, (NTuple{4,Int}, Int))
end
""")
depot = mktempdir()
code = """
pushfirst!(LOAD_PATH, $(repr(dir))); pushfirst!(DEPOT_PATH, $(repr(depot)))
using EffPkg
const CC = Base.Compiler
res = Dict{Symbol,Any}()
for f in (EffPkg.getnib, EffPkg.getub)
    mi = only(Base.specializations(only(methods(f))))
    ci = mi.cache
    e = CC.decode_effects(ci.ipo_purity_bits)
    println(rpad(nameof(f), 7), e, " is_foldable(e, true) = ", CC.is_foldable(e, true),
            ", inferred::", typeof(ci.inferred))
    res[nameof(f)] = (CC.is_foldable(e, true), e.noub, ci.inferred)
end
nib = res[:getnib]; ub = res[:getub]
ok = nib[1] && nib[2] == CC.NOUB_IF_NOINBOUNDS && !(nib[3] isa String) &&
     ub[1] && ub[2] == CC.ALWAYS_TRUE && ub[3] isa String
println(ok ? "REPRODUCED $id" : "NOT REPRODUCED $id")
"""
run(`$(Base.julia_cmd()) --startup-file=no -e $code`)
