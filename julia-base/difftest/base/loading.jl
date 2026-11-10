# Differential test of the cache-file part of the `base/loading.jl` model
# (`JuliaLean/base/loading.lean`) against the pinned Julia, through `LoadingDiff.lean`.
#
# Usage, from julia-base:
#     $JULIA difftest/base/loading.jl --cases 17000 --seed 1
# Set LOADINGDIFF to a built `loadingdiff` executable to use it instead of
# `lake env lean --run LoadingDiff.lean`. Pass --keep to keep the temporary directory.
#
# The driver generates a few tiny packages (include()d files, include_dependency() files and
# directories tracked by content or by mtime, dependencies between them, compile-time
# preferences), places some inside a depot (relocatable), one in the depot's package store and
# some outside any depot, and precompiles them into a temporary depot that comes first on
# DEPOT_PATH, so the stdlib caches are reused (the same effect as `JULIA_DEPOT_PATH=<tmp>:`).
# It adds a second cache with other preferences, one with `--check-bounds=yes`, a cache of a
# dependent built against a newer version of a dependency that is already loaded, and a copy of
# the whole depot (relocation). Each case then changes one recorded input (a source file's
# content, size or mtime, an include_dependency mtime near the tolerated roundings, a directory
# listing, a preference, the requested flags, build id or package id, the file bytes, the depot
# order) and runs one function in the pinned Julia and in the model, in the same state.
#
# Functions: replace_depot_path, restore_depot_path, resolve_depot,
# normalize_depots_for_relocation, CacheFlags(::UInt8, cov), _cacheflag_to_uint8,
# parse_cache_header(file), _parse_cache_header, cache_dependencies, read_dependency_src,
# stale_cachefile, find_all_in_cache_path, compilecache_freshest_path, isrelocatable.
#
# Cases whose cache file has clone-target bytes no writer produced are skipped: Julia crashes on
# them (repro/compiler-loading-clone-targets-oob.jl). The model's callees are answered from
# tables Julia computes in the same state; see LoadingDiff.lean.
#
# Runs (pinned Julia 1.15.0-DEV.184, f755f49a9e41, on the build machine, 2026-11-10):
#   seed 1: 17000 / 17000 agree (59 s)
#   seed 2: 17000 / 17000 agree (63 s)
#   seed 3: 17000 / 17000 agree (66 s)
# Rerun after the review fixes (one UInt8 conversion in _cacheflag_to_uint8, last duplicate key of
# Dict(modules), the preloaded-dependency @assert, literal PkgId("")), same Julia, 2026-11-10:
#   seed 1, 2, 3: 17000 / 17000 agree each
# Each seed: ~2800 stale_cachefile cases: fresh, 17 rejection reasons and 4 exception classes
# in every seed; unresolved_depot and dep_loaded_incompatible in one seed; never julia_version,
# cpu_target, pkgimages_disabled, ocache_checksum_invalid or dep_buildid_mismatch. ~2500 header/deps/srctext cases on real and damaged files, ~1200
# find_all/freshest/isrelocatable, ~5000 depot-path and ~1400 CacheFlags cases.

using Random
import Base: PkgId, UUID, CacheFlags

const TOML = Base.TOML

function argval(name, default)
    i = findfirst(==(name), ARGS)
    return i === nothing ? default : ARGS[i+1]
end
const NCASES = parse(Int, argval("--cases", "2000"))
const SEED = parse(Int, argval("--seed", "1"))
const KEEP = "--keep" in ARGS
const rng = Xoshiro(SEED)

# ---------------------------------------------------------------------------------------------
# JSON

function jesc(s::AbstractString)
    io = IOBuffer()
    print(io, '"')
    for c in s
        if c == '"' || c == '\\'
            print(io, '\\', c)
        elseif c < ' '
            print(io, "\\u", string(UInt16(c), base=16, pad=4))
        else
            print(io, c)
        end
    end
    print(io, '"')
    return String(take!(io))
end
jbytes(s::AbstractString) = isvalid(String(s)) ? jesc(s) : "{\"hex\":\"" * bytes2hex(codeunits(String(s))) * "\"}"
jbool(b::Bool) = b ? "true" : "false"
jhex(x::Integer) = "\"" * string(x, base=16) * "\""
jarr(xs) = "[" * join(xs, ",") * "]"
jobj(pairs) = "{" * join((jesc(string(k)) * ":" * v for (k, v) in pairs), ",") * "}"
jfloat(x::Float64) = jhex(reinterpret(UInt64, x))
jpkg(p::PkgId) = jarr([p.uuid === nothing ? "null" : jhex(UInt128(p.uuid)), jbytes(p.name)])
jspec(s) = jarr([jbytes(s.path), string(s.julia_edition[1]), string(s.julia_edition[2])])
jflags(f::CacheFlags) = jarr([jbool(f.use_pkgimages), string(f.debug_level), string(f.check_bounds),
    jbool(f.inline), string(f.opt_level), string(f.coverage),
    f.coverage_path === nothing ? "null" : jbytes(f.coverage_path)])
jreasons(r) = r === nothing ? "null" : jobj(sort!([string(k) => string(v) for (k, v) in r]))

function errclass(e)
    e isa EOFError && return "EOFError"
    e isa InexactError && return "InexactError"
    e isa BoundsError && return "BoundsError"
    e isa ArgumentError && return "ArgumentError"
    e isa AssertionError && return "AssertionError"
    e isa TypeError && return "TypeError"
    (e isa Base.IOError || e isa SystemError) && return "IOError"
    e isa ErrorException && return "ErrorException"
    e isa KeyError && return "KeyError"
    e isa ConcurrencyViolationError && return "ConcurrencyViolationError"
    return "Other"
end
jerr(e) = jobj(["err" => jesc(errclass(e))])

function expected(f, enc)
    r = try
        f()
    catch e
        e isa InterruptException && rethrow()
        return jerr(e)
    end
    return enc(r)
end

jinclude(c) = jarr([jpkg(c.id), jbytes(c.filename), jhex(c.fsize), string(c.hash), jfloat(c.mtime),
    jarr(jbytes.(c.modpath))])
jmods(ms) = jarr([jarr([jpkg(p), jhex(b)]) for (p, b) in ms])
function jheader(h, full::Bool)
    modules, (includes, src, requires), required_modules, srctextpos, prefs_blob, clone_targets, flags, syntax = h
    srcinc = full ? jarr(jinclude.(src)) : jarr(jbytes.(sort!(collect(src))))
    return jobj(["modules" => jmods(modules), "includes" => jarr(jinclude.(includes)),
        "srcinc" => srcinc, "requires" => jarr([jarr([jpkg(a), jpkg(b)]) for (a, b) in requires]),
        "req" => jmods(required_modules), "srcpos" => string(srctextpos),
        "prefs" => jesc(bytes2hex(codeunits(prefs_blob))), "clone" => jesc(bytes2hex(clone_targets)),
        "flags" => jflags(flags), "syntax" => string(syntax)])
end
function jstale(r, reasons)
    r === true && return jobj(["stale" => "true", "reasons" => jreasons(reasons)])
    depmods, oc, id = r
    deps = [d isa Module ? jobj(["m" => jpkg(PkgId(d))]) :
            jobj(["k" => jpkg(d[2]), "b" => jhex(d[3]), "spec" => jspec(d[1])]) for d in depmods]
    return jobj(["stale" => "false", "reasons" => jreasons(reasons),
        "oc" => oc === nothing ? "null" : jbytes(oc), "id" => jhex(id), "deps" => jarr(deps)])
end

# TOML values of preferences, tagged so that `toml_egal` can be decided structurally.
function jtoml(v)
    v isa Bool && return jobj(["t" => "\"Bool\"", "v" => jbool(v)])
    v isa Int64 && return jobj(["t" => "\"Int64\"", "v" => string(v)])
    v isa Float64 && return jobj(["t" => "\"Float64\"", "v" => jfloat(v)])
    v isa String && return jobj(["t" => "\"String\"", "v" => jesc(v)])
    v isa AbstractVector && return jobj(["t" => "\"array\"", "v" => jarr(jtoml.(v))])
    v isa AbstractDict && return jobj(["t" => "\"dict\"",
        "v" => jarr([jarr([jesc(k), jtoml(x)]) for (k, x) in v])])
    return jobj(["t" => jesc(string(typeof(v))), "v" => jesc(repr(v))])
end
jprefs(d) = jarr([jarr([jbytes(k), jtoml(v)]) for (k, v) in d])

# ---------------------------------------------------------------------------------------------
# Callee answers

function fshash(p, st)
    try
        isfile(st) && return open(Base._crc32c, p, "r")
        isdir(st) && return Base._crc32c(join(readdir(p)))
    catch
    end
    return UInt32(0)
end
function fsent(p::String)
    st = try
        stat(p)
    catch e
        return jarr([jbytes(p), jesc(errclass(e))])
    end
    jarr([jbytes(p), jbool(ispath(st)), jbool(isfile(st)), jbool(isdir(st)),
        jbool(ispath(st) && isreadable(p)), string(filesize(st)), jfloat(mtime(st)),
        string(filemode(st)), jhex(st.device), jhex(st.inode), string(fshash(p, st))])
end

function verify(p)
    open(p, "r") do io
        flags = Ref{UInt32}(0)
        checksum = Ref{UInt32}(0)
        err = ccall(:jl_read_verify_header, Cint, (Ptr{Cvoid}, Ptr{UInt32}, Ptr{UInt32}, Ptr{Int64}, Ptr{Int64}),
            io.ios, flags, checksum, Ref{Int64}(), Ref{Int64}())
        (err, flags[], checksum[], position(io))
    end
end
crcbody(p) = (sz = filesize(p); sz >= 4 ? open(io -> Base._crc32c(io, sz - 4), p, "r") : UInt32(0))

mutable struct Out
    io::IO
    files::Dict{String, Vector{UInt8}}
    env::Dict{String, String}
    fixup::Set{String}
    clones::Set{String}
    blobs::Set{String}
    ncases::Int
end
emit(o::Out, s) = println(o.io, s)

function register!(o::Out, p::String)
    isfile(p) || return
    bytes = read(p)
    get(o.files, p, nothing) == bytes && return
    o.files[p] = bytes
    err, flags, checksum, pos = verify(p)
    emit(o, jobj(["F" => jobj(["p" => jbytes(p), "hex" => jesc(bytes2hex(bytes)),
        "verify" => jarr(string.([err, flags, checksum, pos])), "crc" => string(crcbody(p))])]))
end

function env!(o::Out, key::String, value::String)
    get(o.env, key, nothing) == value && return
    o.env[key] = value
    emit(o, jobj(["ENV" => jobj([key => value])]))
end

fs!(o::Out, paths) = isempty(paths) || emit(o, jobj(["FS" => jarr(fsent.(unique(paths)))]))
rd!(o::Out, dirs) = emit(o, jobj(["RD" => jarr([jarr([jbytes(d), jarr(jbytes.(readdir(d, sort=false)))])
    for d in unique(dirs) if isdir(d)])]))

restore(p, d) = Base.restore_depot_path(p, d)

function raw_header(p)
    try
        open(p, "r") do io
            Base.isvalid_cache_header(io) === nothing && return nothing
            Base._parse_cache_header(io, p)
        end
    catch
        nothing
    end
end

const DEPOT_TAG = "@depot" * Base.Filesystem.pathsep()

# The paths a check of `cachefile` may stat, and the callee answers it may need.
function prepare_cachefile!(o::Out, p::String; spec=nothing)
    register!(o, p)
    paths = String[p, Base.ocachefile_from_cachefile(p)]
    spec === nothing || push!(paths, spec.path)
    h = raw_header(p)
    h === nothing && return paths, h
    modules, (includes, srcfiles, requires), required_modules, _, prefs_blob, clone_targets, _, _ = h
    for f in vcat([inc.filename for inc in includes], collect(srcfiles))
        cands = [f]
        if startswith(f, "@depot")
            for d in DEPOT_PATH
                push!(cands, restore(f, d))
            end
        end
        for c in cands
            push!(paths, c)
            if !(c in o.fixup)
                push!(o.fixup, c)
                fx = Base.fixup_stdlib_path(c)
                emit(o, jobj(["ENV" => jobj(["fixup" => jarr([jarr([jbytes(c), jbytes(fx)])])])]))
                push!(paths, fx)
            end
        end
    end
    ct = bytes2hex(clone_targets)
    # `jl_check_pkgimage_clones` reads changed clone-target bytes out of bounds and can crash
    # (repro/compiler-loading-clone-targets-oob.jl), so only bytes a writer produced are checked.
    if ct in KNOWN_CLONES && !(ct in o.clones)
        push!(o.clones, ct)
        emit(o, jobj(["ENV" => jobj(["clones" =>
            jarr([jarr([jesc(ct), jbool(Base.check_clone_targets(clone_targets) !== nothing)])])])]))
    end
    if !isempty(prefs_blob)
        bh = bytes2hex(codeunits(prefs_blob))
        if !(bh in o.blobs)
            push!(o.blobs, bh)
            entry = try
                # a blob that `stale_prefs` cannot read is answered by the exception it throws
                Base.stale_prefs(prefs_blob)
                d = TOML.parse(TOML.Parser{nothing}(prefs_blob))
                observed = [jarr([jbytes(u), jprefs(v)]) for (u, v) in d if u != "unset"]
                unset = haskey(d, "unset") ?
                    jarr([jarr([jbytes(u), jarr(jbytes.(ks))]) for (u, ks) in d["unset"]]) : "null"
                jarr([jesc(bh), jarr(observed), unset])
            catch e
                jarr([jesc(bh), jesc(errclass(e))])
            end
            emit(o, jobj(["ENV" => jobj(["prefsParsed" => jarr([entry])])]))
        end
    end
    return paths, h
end

function uuids_of_blob(blob)
    isempty(blob) && return String[]
    try
        d = TOML.parse(TOML.Parser{nothing}(blob))
        us = vcat([u for u in keys(d) if u != "unset"], haskey(d, "unset") ? collect(keys(d["unset"])) : String[])
        return [u for u in us if tryparse(UUID, u) !== nothing]
    catch
        return String[]
    end
end

function jmod(M::Module)
    b = Base.module_build_id(M)
    jarr([jpkg(PkgId(M)), jhex(b >> 64), jhex(b % UInt64)])
end

# Session-wide answers whose inputs are the given headers.
function session_env!(o::Out, headers; extra_locate=PkgId[])
    env!(o, "depot_path", jarr(jesc.(DEPOT_PATH)))
    env!(o, "loaded", jarr([jmod(M) for (k, M) in Base.loaded_modules]))
    env!(o, "precomp", jarr([jarr([jpkg(k), jarr(jmod.(ms))]) for (k, ms) in Base.loaded_precompiles]))
    env!(o, "concrete", jarr([jarr([jpkg(k), jhex(b)]) for (k, b) in Base._concrete_dependencies]))
    idents = String[]
    identerrs = String[]
    locs = String[]
    locerrs = String[]
    insys = String[]
    uuids = Set{String}()
    function locate!(k)
        s = try
            Base.locate_package_load_spec(k)
        catch e
            push!(locerrs, jarr([jpkg(k), jesc(errclass(e))]))
            return
        end
        push!(locs, jarr([jpkg(k), s === nothing ? "null" : jspec(s)]))
    end
    foreach(locate!, extra_locate)
    for h in headers
        h === nothing && continue
        _, (_, _, requires), required_modules, _, prefs_blob, _, _, _ = h
        for (modkey, req) in requires
            r = try
                Base.identify_package(modkey, req.name)
            catch e
                push!(identerrs, jarr([jpkg(modkey), jbytes(req.name), jesc(errclass(e))]))
                continue
            end
            push!(idents, jarr([jpkg(modkey), jbytes(req.name), r === nothing ? "null" : jpkg(r)]))
        end
        for (k, _) in required_modules
            locate!(k)
            Base.in_sysimage(k) && push!(insys, jpkg(k))
        end
        union!(uuids, uuids_of_blob(prefs_blob))
    end
    env!(o, "identify", jarr(sort!(unique(idents))))
    env!(o, "identifyErr", jarr(sort!(unique(identerrs))))
    env!(o, "locate", jarr(sort!(unique(locs))))
    env!(o, "locateErr", jarr(sort!(unique(locerrs))))
    env!(o, "insys", jarr(sort!(unique(insys))))
    env!(o, "prefs", jarr(sort!([jarr([jhex(UInt128(UUID(u))), jprefs(Base.get_preferences(UUID(u)))])
        for u in uuids])))
end

# ---------------------------------------------------------------------------------------------
# Packages

struct GenPkg
    name::String
    uuid::UUID
    dir::String
    deps::Vector{Int}
    srcfiles::Vector{String}
    mtimedep::Union{Nothing, String}
    contentdep::Union{Nothing, String}
    dirdep::Union{Nothing, String}
    prefkeys::Vector{String}
end
pkgid(p::GenPkg) = PkgId(p.uuid, p.name)
mainfile(p::GenPkg) = joinpath(p.dir, "src", p.name * ".jl")

const ROOT = mktempdir(; cleanup=false)
const D1 = joinpath(ROOT, "depot1")
const D2 = joinpath(ROOT, "depot2")
const D3 = joinpath(ROOT, "depot3")
const ENVDIR = joinpath(ROOT, "env")
const RES = joinpath(ROOT, "res")
mkpath.([D1, D3, ENVDIR, joinpath(ROOT, "ext")])

randuuid() = UUID(rand(rng, UInt128))
pickvalue() = rand(rng, Any[1, 2, -7, 1.0, 2.5, true, false, "s", "t", Any[1, 2], Any["a"],
    Dict{String,Any}("x" => 1), Dict{String,Any}("x" => Any[1, 2])])

function gen_packages(n)
    pkgs = GenPkg[]
    for i in 1:n
        name = "LdPkg$(SEED)_$i"
        loc = i == n ? :store : rand(rng, [:depot, :depot, :ext])
        dir = loc === :depot ? joinpath(D1, "dev", name) :
              loc === :store ? joinpath(D1, "packages", name, "Ab1Cd") : joinpath(ROOT, "ext", name)
        mkpath(joinpath(dir, "src"))
        deps = i == 1 ? Int[] : sort!(unique(rand(rng, 1:i-1, rand(rng, 0:2))))
        srcfiles = [mainfile(GenPkg(name, UUID(0), dir, Int[], String[], nothing, nothing, nothing, String[]))]
        body = IOBuffer()
        println(body, "module $name")
        for d in deps
            println(body, "using LdPkg$(SEED)_$d")
        end
        for j in 1:rand(rng, 0:3)
            f = rand(rng, Bool) ? "inc$j.jl" : joinpath("sub", "inc$j.jl")
            mkpath(dirname(joinpath(dir, "src", f)))
            write(joinpath(dir, "src", f), "g$j() = $j # padding padding\n")
            println(body, "include($(repr(f)))")
            push!(srcfiles, joinpath(dir, "src", f))
        end
        mtimedep = contentdep = dirdep = nothing
        if rand(rng) < 0.6
            mtimedep = joinpath(dir, "data_mtime.txt")
            write(mtimedep, "mtime tracked\n")
            println(body, "include_dependency(joinpath(@__DIR__, \"..\", \"data_mtime.txt\"); track_content=false)")
        end
        if rand(rng) < 0.6
            contentdep = joinpath(dir, "data_content.txt")
            write(contentdep, "content tracked\n")
            println(body, "include_dependency(joinpath(@__DIR__, \"..\", \"data_content.txt\"))")
        end
        if rand(rng) < 0.4
            dirdep = joinpath(dir, "datadir")
            mkpath(dirdep)
            write(joinpath(dirdep, "a.txt"), "a")
            println(body, "include_dependency(joinpath(@__DIR__, \"..\", \"datadir\"))")
        end
        uuid = randuuid()
        prefkeys = String[]
        for k in 1:rand(rng, 0:2)
            key = "k$k"
            push!(prefkeys, key)
            println(body, "const P_$key = (Base.record_compiletime_preference(Base.UUID(\"$uuid\"), \"$key\"); ",
                "get(Base.get_preferences(Base.UUID(\"$uuid\")), \"$key\", nothing))")
        end
        println(body, "f() = $i")
        println(body, "end")
        write(srcfiles[1], take!(body))
        open(joinpath(dir, "Project.toml"), "w") do io
            println(io, "name = \"$name\"\nuuid = \"$uuid\"\nversion = \"0.1.0\"")
            if !isempty(deps)
                println(io, "[deps]")
                for d in deps
                    println(io, "$(pkgs[d].name) = \"$(pkgs[d].uuid)\"")
                end
            end
        end
        push!(pkgs, GenPkg(name, uuid, dir, deps, srcfiles, mtimedep, contentdep, dirdep, prefkeys))
    end
    return pkgs
end

function write_env(pkgs; prefs=Dict{String,Any}(), uuid_override=Dict{String,UUID}())
    open(joinpath(ENVDIR, "Project.toml"), "w") do io
        println(io, "[deps]")
        for p in pkgs
            println(io, "$(p.name) = \"$(get(uuid_override, p.name, p.uuid))\"")
        end
    end
    open(joinpath(ENVDIR, "Manifest.toml"), "w") do io
        println(io, "julia_version = \"$(VERSION)\"\nmanifest_format = \"2.0\"\n")
        for p in pkgs
            println(io, "[[deps.$(p.name)]]")
            println(io, "path = $(repr(p.dir))")
            println(io, "uuid = \"$(get(uuid_override, p.name, p.uuid))\"")
            isempty(p.deps) || println(io, "deps = [", join(("\"$(pkgs[d].name)\"" for d in p.deps), ", "), "]")
            println(io)
        end
    end
    open(joinpath(ENVDIR, "LocalPreferences.toml"), "w") do io
        TOML.Printer.print(io, prefs; sorted=true)
    end
    @lock Base.require_lock empty!(Base.TOML_CACHE.d)
end

# ---------------------------------------------------------------------------------------------
# Setup

pushfirst!(DEPOT_PATH, D1)
const BASE_DEPOT_PATH = copy(DEPOT_PATH)
empty!(LOAD_PATH); push!(LOAD_PATH, ENVDIR, "@stdlib")

const PKGS = gen_packages(rand(rng, 5:7))
const PREFS = Dict{String,Any}()
for p in PKGS, k in p.prefkeys
    rand(rng) < 0.7 && (get!(Dict{String,Any}, PREFS, p.name)[k] = pickvalue())
end
write_env(PKGS; prefs=PREFS)

println(stderr, "precompiling $(length(PKGS)) packages into $D1")
for p in PKGS
    Base.compilecache(pkgid(p), stderr, devnull)
end
# a second cache with other preferences
let i = findfirst(p -> !isempty(p.prefkeys), PKGS)
    if i !== nothing
        p = PKGS[i]
        alt = deepcopy(PREFS)
        get!(Dict{String,Any}, alt, p.name)[p.prefkeys[1]] = "other"
        write_env(PKGS; prefs=alt)
        Base.compilecache(pkgid(p), devnull, devnull)
        write_env(PKGS; prefs=PREFS)
    end
end
# a cache built with other flags
Base.compilecache(pkgid(PKGS[1]), devnull, devnull; flags=`--check-bounds=yes`,
    cacheflags=CacheFlags(; check_bounds=1))
# load the first package, then rebuild it and a dependent against the new version
Base.require(pkgid(PKGS[1]))
let dependent = findfirst(p -> 1 in p.deps, PKGS)
    write(mainfile(PKGS[1]), read(mainfile(PKGS[1]), String) * "# changed\n")
    Base.compilecache(pkgid(PKGS[1]), devnull, devnull)
    dependent === nothing || Base.compilecache(pkgid(PKGS[dependent]), devnull, devnull)
end
const KNOWN_CLONES = Set{String}()
for (dir, _, fs) in walkdir(joinpath(D1, "compiled")), f in fs
    endswith(f, ".ji") || continue
    h = open(joinpath(dir, f), "r") do io
        Base.isvalid_cache_header(io); Base._parse_cache_header(io, joinpath(dir, f))
    end
    push!(KNOWN_CLONES, bytes2hex(h[6]))
end
cp(D1, D2)                       # relocation copy; `cp` does not keep mtimes
mkpath(joinpath(RES, "d1", "a")); mkpath(joinpath(RES, "d2", "a", "b")); mkpath(joinpath(RES, "d3"))
write(joinpath(RES, "d1", "a", "x.jl"), "x"); write(joinpath(RES, "d2", "a", "x.jl"), "x")
write(joinpath(RES, "d2", "a", "b", "y.jl"), "y"); write(joinpath(RES, "d3", "z"), "z")

compiled_dirs(p::PkgId) = [joinpath(d, Base.cache_file_entry(p)[1]) for d in DEPOT_PATH]
cachefiles() = sort!([joinpath(dir, f) for d in (D1, D2) for (dir, _, fs) in walkdir(joinpath(d, "compiled"))
    for f in fs if endswith(f, ".ji")])

const DEPOT_VARIANTS = [BASE_DEPOT_PATH, [D2; BASE_DEPOT_PATH[2:end]], [D1; D2; BASE_DEPOT_PATH[2:end]],
    [D2; D1; BASE_DEPOT_PATH[2:end]], [D3; D1; BASE_DEPOT_PATH[2:end]]]
set_depots!(v) = (copy!(DEPOT_PATH, v); nothing)

# ---------------------------------------------------------------------------------------------
# Cases

function case!(o::Out, op, args, exp)
    o.ncases += 1
    emit(o, jobj(vcat(["id" => string(o.ncases), "op" => jesc(op)], args, ["exp" => exp])))
end

const SEGS = ["a", "b", "bc", "dev", "é", "@depot", "x.jl", ""]
randseg() = rand(rng, SEGS)
randpath() = "/" * join([randseg() for _ in 1:rand(rng, 0:3)], "/") * (rand(rng) < 0.2 ? "/" : "")

function case_replace!(o)
    depots = [rand(rng) < 0.15 ? rand(rng, ["", "/", "@depot"]) : randpath() for _ in 1:rand(rng, 0:3)]
    base = isempty(depots) || rand(rng) < 0.3 ? randpath() : rand(rng, depots)
    path = rand(rng, [base, base * "/" * randseg(), base * randseg(), base * "/", randpath()])
    case!(o, "replace", ["path" => jbytes(path), "depots" => jarr(jesc.(depots))],
        expected(() -> Base.replace_depot_path(path, depots), jbytes))
end

function case_replace_default!(o)
    set_depots!(rand(rng, DEPOT_VARIANTS))
    env!(o, "depot_path", jarr(jesc.(DEPOT_PATH)))
    fs!(o, copy(DEPOT_PATH))
    d = rand(rng, DEPOT_PATH)
    path = rand(rng, [d, d * "/dev/x.jl", d * "x/y", "/elsewhere/a", joinpath(D2, "dev")])
    case!(o, "replace", ["path" => jbytes(path), "depots" => "null"],
        expected(() -> Base.replace_depot_path(path), jbytes))
end

function case_restore!(o)
    path = rand(rng, ["@depot", "@depot/", "@depot/a/b.jl", "@depotx/a", "x@depot/a", "/a/@depot", "", randpath()])
    depot = rand(rng, ["", "/", "/d", "/d/", randpath()])
    case!(o, "restore", ["path" => jbytes(path), "depot" => jbytes(depot)],
        expected(() -> Base.restore_depot_path(path, depot), jbytes))
end

function case_resolve!(o)
    ds = [joinpath(RES, d) for d in ("d1", "d2", "d3", "missing")]
    v = shuffle(rng, ds)[1:rand(rng, 0:4)]
    set_depots!(v)
    env!(o, "depot_path", jarr(jesc.(DEPOT_PATH)))
    rel = rand(rng, ["a/x.jl", "a/b/y.jl", "z", "a", "nope.jl", "a/b"])
    inc = rand(rng, ["@depot/" * rel, "@depot" * rel, "/abs/" * rel, "@depot/"])
    hint = rand(rng) < 0.5 ? nothing : rand(rng, ds)
    paths = [restore(inc, d) for d in vcat(ds)]
    fs!(o, paths)
    r = expected(() -> Base.resolve_depot(inc, hint),
        r -> r isa Symbol ? jobj(["r" => jesc(string(r))]) : jobj(["d" => jbytes(r)]))
    case!(o, "resolve", ["inc" => jbytes(inc), "hint" => hint === nothing ? "null" : jbytes(hint)], r)
end

function case_normalize!(o)
    cands = [D1, D1 * "/", joinpath(D1, "dev") * "/./", D2 * "//", joinpath(ROOT, "missing"), "/",
        joinpath(ROOT, "env", "..", "depot3"), joinpath(D1, "compiled", "..")]
    set_depots!(shuffle(rng, cands)[1:rand(rng, 0:length(cands))])
    env!(o, "depot_path", jarr(jesc.(DEPOT_PATH)))
    fs!(o, copy(DEPOT_PATH))
    case!(o, "normalize", Pair{String,String}[],
        expected(Base.normalize_depots_for_relocation, ds -> jarr(jbytes.(ds))))
end

function case_flags!(o)
    if rand(rng, Bool)
        b = rand(rng, 0:255)
        cov = rand(rng, [0, 1, 2, 3, -1, 300])
        case!(o, "flags_from", ["byte" => string(b), "cov" => string(cov)], jflags(CacheFlags(UInt8(b), cov)))
    else
        f = CacheFlags(rand(rng, Bool), rand(rng, [0, 1, 2, 3, 4, -1]), rand(rng, [0, 1, 2, 3, 4]),
            rand(rng, Bool), rand(rng, [0, 1, 2, 3, 4, 5]), rand(rng, [0, 1, 2]), nothing)
        case!(o, "flags_to", ["flags" => jflags(f)],
            expected(() -> Base._cacheflag_to_uint8(f), b -> string(b)))
    end
end

# A mutated copy of a cache file: a changed byte, or truncated.
function mutated_copy(p)
    bytes = read(p)
    q = joinpath(ROOT, "mut", basename(dirname(p)), "m$(rand(rng, 1:4))_" * basename(p))
    mkpath(dirname(q))
    k = rand(rng, 1:3)
    hdr = raw_header(p)
    if k == 1
        n = rand(rng, 0:min(length(bytes), 600))
        bytes = bytes[1:n]
    elseif k == 2 && !isempty(bytes)
        i = rand(rng, 1:min(length(bytes), 400))
        bytes[i] = rand(rng, [0x00, 0xff, bytes[i] ⊻ 0x01, bytes[i] ⊻ 0x80])
    else
        isempty(bytes) || (i = rand(rng, 1:length(bytes)); bytes[i] ⊻= 0x10)
    end
    write(q, bytes)
    ocp = Base.ocachefile_from_cachefile(p)
    isfile(ocp) && cp(ocp, Base.ocachefile_from_cachefile(q); force=true)
    return q
end

function case_header!(o)
    set_depots!(rand(rng, DEPOT_VARIANTS))
    p = rand(rng, cachefiles())
    rand(rng) < 0.3 && (p = mutated_copy(p))
    paths, h = prepare_cachefile!(o, p)
    env!(o, "depot_path", jarr(jesc.(DEPOT_PATH)))
    fs!(o, paths)
    k = rand(rng, 1:4)
    if k <= 2
        full = k == 1
        f = full ? () -> Base.parse_cache_header(p) :
            () -> open(p, "r") do io
                Base.isvalid_cache_header(io) === nothing && throw(ArgumentError("Incompatible header"))
                Base._parse_cache_header(io, p)
            end
        case!(o, "header", ["file" => jbytes(p), "full" => jbool(full)], expected(f, h -> jheader(h, full)))
    elseif k == 3
        case!(o, "deps", ["file" => jbytes(p)], expected(() -> Base.cache_dependencies(p),
            r -> jarr([jmods(r[1]), jarr(jbytes.(r[2]))])))
    else
        names = String[]
        if h !== nothing
            for inc in h[2][1]
                push!(names, inc.filename)
                startswith(inc.filename, "@depot") && push!(names, restore(inc.filename, rand(rng, DEPOT_PATH)))
            end
        end
        push!(names, "/nonexistent.jl")
        name = rand(rng, names)
        case!(o, "srctext", ["file" => jbytes(p), "name" => jbytes(name)],
            expected(() -> Base.read_dependency_src(p, name), s -> jesc(bytes2hex(codeunits(s)))))
    end
end

function flagsvariant()
    r = rand(rng)
    r < 0.75 && return CacheFlags()
    r < 0.8 && return CacheFlags(CacheFlags(); check_bounds=rand(rng, 0:2))
    r < 0.9 && return CacheFlags(UInt8(rand(rng, 0:255)), 0)
    return CacheFlags(CacheFlags(); coverage=rand(rng, 1:2))
end

# One recorded input of a package's sources, changed in place; returns the undo.
function mutate_inputs!(p::GenPkg)
    k = rand(rng, 1:12)
    if k == 1 # touch a source file (content tracked)
        f = rand(rng, p.srcfiles)
        t = mtime(f)
        touch(f)
        return () -> nothing
    elseif k == 2 # same size, different content
        f = rand(rng, p.srcfiles)
        s = read(f)
        s2 = copy(s); s2[end-1] = s2[end-1] == UInt8('g') ? UInt8('h') : UInt8('g')
        write(f, s2)
        return () -> write(f, s)
    elseif k == 3 # size change
        f = rand(rng, p.srcfiles)
        s = read(f)
        write(f, vcat(s, UInt8[0x20]))
        return () -> write(f, s)
    elseif k == 4 # missing source
        f = rand(rng, p.srcfiles)
        mv(f, f * ".away")
        return () -> mv(f * ".away", f)
    elseif k in (5, 6) && p.mtimedep !== nothing # mtime near the tolerated roundings
        f = p.mtimedep
        t = mtime(f)
        t2 = rand(rng, [t + 1, t - 1, floor(t), ceil(t), trunc(t, digits=6), 1.0, t - 5e-7, t + 5e-7,
            t - 2e-6, t + 1e-9, prevfloat(t), nextfloat(t), 0.0])
        setmtime(f, t2)
        return () -> setmtime(f, t)
    elseif k == 7 && p.contentdep !== nothing
        f = p.contentdep
        s = read(f)
        write(f, rand(rng, Bool) ? vcat(s, UInt8[0x41]) : reverse(s))
        return () -> write(f, s)
    elseif k == 8 && p.dirdep !== nothing
        f = joinpath(p.dirdep, "b.txt")
        write(f, "b")
        return () -> rm(f)
    elseif k == 9 && !isempty(p.prefkeys)
        alt = deepcopy(PREFS)
        r = rand(rng, 1:3)
        if r == 1
            get!(Dict{String,Any}, alt, p.name)[rand(rng, p.prefkeys)] = pickvalue()
        elseif r == 2
            haskey(alt, p.name) && delete!(alt[p.name], rand(rng, p.prefkeys))
        else
            v = get(get(alt, p.name, Dict{String,Any}()), p.prefkeys[1], 1)
            get!(Dict{String,Any}, alt, p.name)[p.prefkeys[1]] = v isa Int ? Float64(v) : v
        end
        write_env(PKGS; prefs=alt)
        return () -> write_env(PKGS; prefs=PREFS)
    elseif k == 10 && !isempty(p.deps) # a dependency's uuid changes in the environment
        d = PKGS[rand(rng, p.deps)]
        write_env(PKGS; prefs=PREFS, uuid_override=Dict(d.name => randuuid()))
        return () -> write_env(PKGS; prefs=PREFS)
    elseif k == 11 # read-only source (matters in the package store)
        f = rand(rng, p.srcfiles)
        m = filemode(f)
        chmod(f, 0o444)
        s = read(f)
        if rand(rng, Bool)
            chmod(f, 0o644); s2 = copy(s); s2[end-1] = s2[end-1] == UInt8('g') ? UInt8('h') : UInt8('g')
            write(f, s2); chmod(f, 0o444)
        end
        return () -> (chmod(f, 0o644); write(f, s); chmod(f, m))
    elseif k == 12 # object file missing
        return nothing
    end
    return () -> nothing
end

function setmtime(f, t)
    file = Base.Filesystem.open(f, Base.Filesystem.JL_O_RDONLY)
    try
        Base.Filesystem.futime(file, t, t)
    finally
        close(file)
    end
end

pkg_of_cachefile(p) = (i = findfirst(g -> occursin("/" * g.name * "/", p), PKGS); i === nothing ? nothing : PKGS[i])

function case_stale!(o)
    set_depots!(rand(rng, DEPOT_VARIANTS[1:4]))
    p = rand(rng, cachefiles())
    g = pkg_of_cachefile(p)
    g === nothing && return
    undo = mutate_inputs!(g)
    ocundo = () -> nothing
    if undo === nothing
        oc = Base.ocachefile_from_cachefile(p)
        if isfile(oc)
            mv(oc, oc * ".away"); ocundo = () -> mv(oc * ".away", oc)
        end
        undo = () -> nothing
    end
    mutfile = rand(rng) < 0.1
    q = mutfile ? mutated_copy(p) : p
    try
        r = rand(rng)
        modkey = r < 0.7 ? pkgid(g) : r < 0.85 ? PkgId("") : pkgid(rand(rng, PKGS))
        h = raw_header(q)
        checksum = open(Base.isvalid_cache_header, q, "r")
        build = rand(rng) < 0.7 || h === nothing || isempty(h[1]) || checksum === nothing ? UInt128(0) :
            rand(rng, [rand(rng, UInt128), (UInt128(checksum) << 64) | (h[1][1][2] % UInt64)])
        specpath = startswith(p, D2) ? replace(mainfile(g), D1 => D2) : mainfile(g)
        rand(rng) < 0.05 && (specpath = mainfile(rand(rng, PKGS)))
        located = Base.locate_package_load_spec(pkgid(g))
        ed = rand(rng) < 0.1 || located === nothing ? (1, rand(rng, [10, 13, 14, 15, 16, 300])) :
            located.julia_edition
        spec = Base.PkgLoadSpec(specpath, ed)
        flags = flagsvariant()
        ignore_loaded = rand(rng) < 0.2
        stalecheck = rand(rng) < 0.85
        verify = rand(rng) < 0.7
        split = rand(rng) < 0.8
        withreasons = rand(rng) < 0.8
        paths, hh = prepare_cachefile!(o, q; spec)
        hh !== nothing && !isempty(hh[6]) && !(bytes2hex(hh[6]) in KNOWN_CLONES) && return
        session_env!(o, [hh])
        fs!(o, paths)
        reasons = withreasons ? Dict{Symbol,Int}() : nothing
        exp = expected(() -> Base.stale_cachefile(modkey, build, spec, q; ignore_loaded,
                requested_flags=flags, reasons, stalecheck, verify_checksums=verify, split_checksums=split),
            r -> jstale(r, reasons))
        case!(o, "stale", ["modkey" => jpkg(modkey), "build" => jhex(build), "spec" => jspec(spec),
            "file" => jbytes(q), "flags" => jflags(flags), "reasons" => jbool(withreasons),
            "ignore_loaded" => jbool(ignore_loaded), "stalecheck" => jbool(stalecheck),
            "verify" => jbool(verify), "split" => jbool(split)], exp)
    finally
        undo(); ocundo()
    end
end

# Everything a search over the caches of `pkg` and of its dependencies may read.
function prepare_search!(o, pkg::PkgId)
    paths = String[]
    headers = Any[]
    seen = Set{PkgId}()
    todo = [pkg]
    while !isempty(todo)
        k = pop!(todo)
        k in seen && continue
        push!(seen, k)
        dirs = compiled_dirs(k)
        append!(paths, dirs)
        rd!(o, dirs)
        for c in Base.find_all_in_cache_path(k)
            ps, h = prepare_cachefile!(o, c)
            append!(paths, ps)
            h === nothing && continue
            push!(headers, h)
            k == pkg && for (rk, _) in h[3]
                Base.in_sysimage(rk) || push!(todo, rk)
            end
        end
        s = Base.locate_package_load_spec(k)
        s === nothing || push!(paths, s.path)
    end
    session_env!(o, headers; extra_locate=collect(seen))
    fs!(o, paths)
end

function case_search!(o)
    set_depots!(rand(rng, DEPOT_VARIANTS[[1, 1, 3, 4]]))
    g = rand(rng, PKGS)
    undo = rand(rng) < 0.5 ? mutate_inputs!(g) : () -> nothing
    undo === nothing && (undo = () -> nothing)
    try
        prepare_search!(o, pkgid(g))
        k = rand(rng, 1:3)
        if k == 1
            case!(o, "findall", ["pkg" => jpkg(pkgid(g))],
                expected(() -> Base.find_all_in_cache_path(pkgid(g)), ps -> jarr(jbytes.(ps))))
        elseif k == 2
            flags = rand(rng) < 0.5 ? nothing : flagsvariant()
            ignore_loaded = rand(rng) < 0.3
            verify = rand(rng) < 0.5
            exp = expected(() -> flags === nothing ?
                    Base.compilecache_freshest_path(pkgid(g); ignore_loaded, verify_checksums=verify) :
                    Base.compilecache_freshest_path(pkgid(g); ignore_loaded, flags, verify_checksums=verify),
                r -> r === nothing ? "null" : jbytes(r))
            case!(o, "freshest", ["pkg" => jpkg(pkgid(g)), "flags" => flags === nothing ? "null" : jflags(flags),
                "ignore_loaded" => jbool(ignore_loaded), "verify" => jbool(verify)], exp)
        else
            case!(o, "relocatable", ["pkg" => jpkg(pkgid(g))],
                expected(() -> Base.isrelocatable(pkgid(g)), jbool))
        end
    finally
        undo()
    end
end

# ---------------------------------------------------------------------------------------------
# Main

# The largest position `seek` on an IOStream of the depot's file system accepts.
function max_seek()
    f = joinpath(D1, "seekprobe")
    write(f, "x")
    lo, hi = Int128(0), Int128(typemax(Int64))
    open(f, "r") do io
        while lo < hi
            mid = lo + (hi - lo + 1) ÷ 2
            ok = try
                seek(io, Int64(mid)); true
            catch
                false
            end
            ok ? (lo = mid) : (hi = mid - 1)
        end
    end
    rm(f)
    return lo
end

function global_env!(o::Out)
    emit(o, jobj(["MCF" => jarr([jarr([string(a), string(b),
        string(ccall(:jl_match_cache_flags, UInt8, (UInt8, UInt8), a, b))]) for a in 0x00:0xff for b in 0x00:0xff])]))
    emit(o, jobj(["MCC" => jarr([jarr([string(a), string(b),
        jbool(ccall(:jl_match_cache_coverage, Cint, (UInt8, UInt8), a, b) != 0)]) for a in 0x00:0x03 for b in 0x00:0xff])]))
    env!(o, "stdlib", jesc(Sys.STDLIB))
    env!(o, "dlext", jesc(Base.Libc.Libdl.dlext))
    emit(o, jobj(["ENV" => jobj(["vmajor" => jesc(string(VERSION.major)), "vminor" => jesc(string(VERSION.minor))])]))
    env!(o, "edition", jarr(string.(collect(Base.VERSION_EDITION))))
    env!(o, "imageCov", string(ccall(:jl_image_coverage_config, UInt8, ())))
    env!(o, "sysimageCov", string(ccall(:jl_sysimage_coverage_config, UInt8, ())))
    env!(o, "jlCacheFlags", string(ccall(:jl_cache_flags, UInt8, ())))
    env!(o, "usePkgimages", jbool(Base.JLOptions().use_pkgimages != 0))
    env!(o, "debugBuild", jbool(Base.isdebugbuild()))
    env!(o, "maxSeek", string(max_seek()))
    env!(o, "core", jmod(Core))
    env!(o, "uuidcrc", jarr([jarr([jhex(UInt128(p.uuid)), string(Base._crc32c(p.uuid))]) for p in PKGS]))
end

function main()
    infile = joinpath(ROOT, "cases.jsonl")
    o = Out(open(infile, "w"), Dict{String,Vector{UInt8}}(), Dict{String,String}(), Set{String}(),
        Set{String}(), Set{String}(), 0)
    global_env!(o)
    kinds = [(case_replace!, 10), (case_replace_default!, 4), (case_restore!, 8), (case_resolve!, 8),
        (case_normalize!, 4), (case_flags!, 8), (case_header!, 20), (case_stale!, 30), (case_search!, 8)]
    weights = cumsum(last.(kinds))
    while o.ncases < NCASES
        i = searchsortedfirst(weights, rand(rng, 1:weights[end]))
        first(kinds[i])(o)
    end
    set_depots!(BASE_DEPOT_PATH)
    close(o.io)
    outfile = joinpath(ROOT, "out.jsonl")
    lean = get(ENV, "LOADINGDIFF", "")
    cmd = isempty(lean) ? `lake env lean --run LoadingDiff.lean` : `$lean`
    println(stderr, "running $(o.ncases) cases through $cmd")
    run(pipeline(cmd; stdin=infile, stdout=outfile))
    agree = 0
    bad = String[]
    for line in eachline(outfile)
        if occursin("\"agree\":true", line)
            agree += 1
        else
            push!(bad, line)
        end
    end
    for l in bad[1:min(end, 20)]
        println(l)
    end
    println("seed $SEED: $agree / $(o.ncases) agree, $(length(bad)) other lines (VERSION $VERSION, ",
        Base.GIT_VERSION_INFO.commit, ")")
    KEEP ? println("kept $ROOT") : rm(ROOT; recursive=true, force=true)
    return isempty(bad) && agree == o.ncases
end

exit(main() ? 0 : 1)
