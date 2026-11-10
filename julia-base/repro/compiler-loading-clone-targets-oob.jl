# A cache file whose clone-target bytes are damaged crashes `using` instead of being rejected.
#
# `stale_cachefile` passes the header's clone-target bytes to `check_clone_targets`, which hands
# only a pointer to `jl_check_pkgimage_clones`; the C side reads the lengths stored in the bytes
# without a bound. The whole-file checksum that would reject a damaged file is checked later
# (and `require` skips it on the first pass, `verify_checksums=false`).
#
# The script precompiles a tiny package into a temporary depot, grows the length of the CPU name
# inside the clone targets of its cache file, then runs `using` in a child process with that
# depot first. Prints REPRODUCED when the child dies from a signal.

const ID = "compiler-loading-clone-targets-oob"
println(VERSION, " ", Base.GIT_VERSION_INFO.commit)

depot = mktempdir()
pkgdir = joinpath(depot, "dev", "CloneOOB")
mkpath(joinpath(pkgdir, "src"))
write(joinpath(pkgdir, "Project.toml"),
    "name = \"CloneOOB\"\nuuid = \"8d5f3b1e-61a5-4c39-9a0e-3f2c6b7d9e01\"\nversion = \"0.1.0\"\n")
write(joinpath(pkgdir, "src", "CloneOOB.jl"), "module CloneOOB\nf() = 1\nend\n")
env = Dict("JULIA_DEPOT_PATH" => depot * ":", "JULIA_LOAD_PATH" => joinpath(depot, "dev") * ":@stdlib",
    "JULIA_PKG_PRECOMPILE_AUTO" => "0")
julia = Base.julia_cmd()
run(addenv(`$julia --startup-file=no -e "using CloneOOB"`, env))

cachefiles = [joinpath(d, f) for (d, _, fs) in walkdir(joinpath(depot, "compiled")) for f in fs if endswith(f, ".ji")]
length(cachefiles) == 1 || error("expected one cache file, found $cachefiles")
cachefile = only(cachefiles)
clone_targets = open(cachefile) do io
    Base.isvalid_cache_header(io) === nothing && error("invalid header")
    Base._parse_cache_header(io, cachefile)[6]
end
isempty(clone_targets) && error("the cache has no pkgimage; nothing to damage")
name = String(Base.parse_image_targets(clone_targets)[1].name)
println("cache file: ", cachefile)
println("image target: ", name)

bytes = read(cachefile)
needle = vcat(reinterpret(UInt8, [Int32(ncodeunits(name))]), codeunits(name))
i = findfirst(needle, bytes)
i === nothing && error("CPU name not found in the cache file")
bytes[first(i):first(i)+3] .= reinterpret(UInt8, [Int32(0x40000000)])
write(cachefile, bytes)

p = run(ignorestatus(addenv(`$julia --startup-file=no -e "using CloneOOB; println(\"loaded\")"`, env)))
println("child exit code ", p.exitcode, ", signal ", p.termsignal)
println(p.termsignal != 0 ? "REPRODUCED $ID" : "NOT REPRODUCED $ID")
