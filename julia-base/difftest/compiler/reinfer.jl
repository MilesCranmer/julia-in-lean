# Differential test of the Lean models of Compiler/src/reinfer.jl, bindinginvalidations.jl and
# cicache.jl against the pinned Julia (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA difftest/compiler/reinfer.jl \
#         --cases 17000 --seed 1
#
# Builds a method table and bindings in fresh modules: functions with 2-5 methods over a small
# argument-type grammar (abstract and concrete types, Unions, Type{...}, Vararg, where-bound
# vectors), recorded call edges (match lists, fully-covering flags, possibly-ambiguous flags) and
# invoke edges at world wA, then two rounds of changes (methods added, deleted with
# `Base.delete_method`, redefined with the same signature; consts rebound; `did_scan_source` bit
# 0x4 set) ending at worlds wB and wC. Then it calls the pinned verifier functions directly on
# graphs of fake CodeInstances (`Core.CodeInstance` with `max_world` the revalidation sentinel,
# edges set afterwards so they can form cycles and self-loops; min_world wA, wB or wC so lookups
# run in older worlds too), with edges that are often stale (expected lists with a method dropped,
# added or deleted, wrong fully-covers or possibly-ambiguous flags, invoke targets that are not
# the `invoke` match, rebound or recent bindings, MethodTable invoke callees). Every case sends the
# objects it reads; the answers of the C lookups (`_methods_by_ftype`, `_findsup`,
# `binding_access_range`, `typeintersect`, `<:`, `===`) go to the oracle tables as `R` lines.
#
# Package images: two small packages (RIDep, and RIPkg using it) are precompiled into a fresh
# depot and loaded; then `RIDep.g` gains a method that changes recorded matches and one that
# meets them only at the `Type{Union{}}` corner, and on odd seeds the image const `RIDep.L` is
# rebound (so `jl_first_image_replacement_world` is finite and method sources get scanned). The
# image cases reset loaded CodeInstances (and, at random, those they reach) to the revalidation
# sentinel, clear some dispatch-status bits as an image load would leave them, and re-run
# `verify_method` / `insert_backedges` on them with their real recorded edges; these reach the
# `sig_contributors_world` paths of `verify_call` and `verify_invokesig`, with
# `jl_sig_contributors_world` and `jl_linkage_blob_dep_world` answered by the pinned runtime.
#
# Not exercised: the `method_in_image_deps` skip in the interference scan (no run reached it),
# coverage or allocation logging, the invalidation debug log, and
# `invalidate_code_for_globalref!` (only the runtime calls it when a binding changes, and its
# oracle is not filled). `insert_backedges` runs only outside precompilation. The fake code
# instances of r.iccSet always have `inferred` and never `invoke`, so the invoke and inferred
# stop conditions of `jl_mi_cache_insert` are not reached.
#
# Ops: r.verifyMethod (verify_method on a graph root), r.insertBackedges (insert_backedges on a
# list of code instances and methods), r.bindingChanged (binding_changed_since_require_world),
# r.invalidateMethod (invalidate_method_for_globalref! on methods with fake cached code),
# r.exportFlags, r.wrNew/r.wrIn/r.wrIntersect/r.wrUnion (WorldRange), r.icc
# (InternalCodeCache haskey/get/getindex). The driver prints, per seed, how often each branch of
# the model was taken in agreeing cases (`path ...`, from markers the model emits) and how the
# pinned verifier decided.
#
# Runs (seed, cases, agreement):
#   2026-11-09, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 17000 cases: AGREE 17000/17000, 0 unmodelled
#   seed 2, 17000 cases: AGREE 17000/17000, 0 unmodelled
#   seed 3, 17000 cases: AGREE 17000/17000, 0 unmodelled
#   Seed 1 had 6290 r.verifyMethod (493 on image code), 2490 r.insertBackedges (1112 on image
#   code), 1505 r.invalidateMethod, 1199 r.bindingChanged; branches taken in agreeing cases
#   included call:dominates 4288, interference-ok 1448, removed-silently 295, not-silent 592,
#   contributors 243, lookup-ok 2313, lookup-reject 733, lookup-none 409, deleted 203,
#   invoke:contributors 338, findsup-other 167, method:cycle-back-edge 1875, group-accepted 96,
#   group-rejected 114, binding-reject 885, promote-mi 275, lookup:memo-hit 48.
#   2026-11-09, after `recursivePhase`'s `while` became a bounded `for` (for kernel reduction in
#   proofs), same pinned Julia: seeds 1, 2, 3 with 17000 cases each: AGREE 17000/17000 each,
#   0 unmodelled.
#   2026-11-10, after the review fixes (statements and their userefs values in place of a visit
#   list, jl_mi_cache_insert in setindex!, the InternalCodeCache(owner, args...) forms; new ops
#   r.iccSet and constructor kinds in r.icc), same pinned Julia: seeds 1, 2, 3 with 17000 cases
#   each: AGREE 17000/17000 each, 0 unmodelled (r.iccSet 409/404/390 cases). Checks of the
#   pinned Julia on the same runs, seeds 1/2/3: fastpath:agree 1138/1113/1180 with no
#   disagreement; leafpromise:holds 887/844/891, none broken; range:bounded 3978/4062/3991, none
#   violated; cycle:consistent 578/578/696, no split; no GlobalRef statement with userefs.

include(joinpath(@__DIR__, "common.jl"))
using .LatticeSer
using Random

const LS = LatticeSer
const RU = CC.ReinferUtils
const obj = LS.obj
const arr = LS.arr
const jbool = LS.jbool
const TM = typemax(UInt)

function parse_args(args)
    opts = Dict("cases" => "2000", "seed" => "1", "exe" => joinpath(@__DIR__, "..", "..",
                ".lake", "build", "bin", "compilerdiff"), "show" => "20")
    i = 1
    while i <= length(args)
        a = args[i]
        startswith(a, "--") || error("bad arg $a")
        opts[a[3:end]] = args[i+1]
        i += 2
    end
    return opts
end

id!(s, @nospecialize(x)) = LS.objid!(s, x)
jn(x::Integer) = string(x)

# ---------------------------------------------------------------- oracle tables

mutable struct Facts
    seen::Set{String}
    rows::Dict{String,Vector{String}}
    isect::IdDict{Any,IdDict{Any,Any}}
end
Facts() = Facts(Set{String}(), Dict{String,Vector{String}}(), IdDict{Any,IdDict{Any,Any}}())

function fact!(F::Facts, table::String, key::String, row::String)
    k = table * "|" * key
    k in F.seen && return
    push!(F.seen, k)
    push!(get!(F.rows, table, String[]), row)
end

function flush_facts(io, s, F::Facts)
    LS.flush_universe(io, s)
    isempty(F.rows) && return
    println(io, obj("R" => obj((k => arr(v) for (k, v) in F.rows)...)))
    empty!(F.rows)
end

function isect_memo(F::Facts, @nospecialize(a), @nospecialize(b))
    d = get!(() -> IdDict{Any,Any}(), F.isect, a)
    return get!(() -> typeintersect(a, b), d, b)
end

function fact_sub!(F, s, @nospecialize(a), @nospecialize(b))
    ea = sval(s, a); eb = sval(s, b)
    fact!(F, "sub", ea * eb, arr([ea, eb, jbool(a <: b)]))
end

function fact_isect!(F, s, @nospecialize(a), @nospecialize(b))
    ti = isect_memo(F, a, b)
    ea = sval(s, a); eb = sval(s, b)
    fact!(F, "isect", ea * eb, arr([ea, eb, sval(s, ti)]))
    return ti
end

function fact_egal!(F, s, @nospecialize(a), @nospecialize(b))
    ea = sval(s, a); eb = sval(s, b)
    fact!(F, "egal", ea * eb, arr([ea, eb, jbool(a === b)]))
end

function fact_mm!(F, s, @nospecialize(sig), lim::Int, world::UInt)
    es = sval(s, sig)
    key = es * "|$lim|$world"
    key in F.seen && return
    mn = Ref(UInt(1)); mx = Ref(typemax(UInt)); amb = Ref(Int32(0))
    r = Base._methods_by_ftype(sig, nothing, lim, world, false, mn, mx, amb)
    res = r === nothing ? "null" : arr([jn(id!(s, (m::Core.MethodMatch).method)) for m in r])
    fact!(F, "mm", key, arr([es, jn(lim), jn(world), res, jn(mn[]), jn(mx[]), jn(amb[])]))
    return r
end

function fact_fs!(F, s, @nospecialize(sig), world::UInt)
    es = sval(s, sig)
    key = es * "|$world"
    key in F.seen && return
    m, wr = CC._findsup(sig, nothing, world)
    fact!(F, "fs", key, arr([es, jn(world), m === nothing ? "null" : jn(id!(s, m.method)),
        jn(wr.min_world), jn(wr.max_world)]))
end

function fact_bar!(F, s, b::Core.Binding, world::UInt)
    world >= Base.get_require_world() || return
    key = "$(id!(s, b))|$world"
    key in F.seen && return
    wr = RU.binding_access_range_at(b, world)
    fact!(F, "bar", key, arr([jn(id!(s, b)), jn(world), jn(wr.min_world), jn(wr.max_world)]))
end

function fact_scw!(F, s, @nospecialize(sig), image::UInt)
    image == TM && return
    es = sval(s, sig)
    key = es * "|$image"
    key in F.seen && return
    w = ccall(:jl_sig_contributors_world, Csize_t, (Any, Any, Csize_t), sig, Core.methodtable, image)
    tally!(w == 0 ? "fact:scw-zero" : "fact:scw-nonzero")
    fact!(F, "scw", key, arr([es, jn(image), jn(w)]))
end

function fact_bdw!(F, s, image::UInt, blob::UInt)
    (image == TM || blob == TM) && return
    key = "$image|$blob"
    key in F.seen && return
    w = ccall(:jl_linkage_blob_dep_world, Csize_t, (Csize_t, Csize_t), image, blob)
    fact!(F, "bdw", key, arr([jn(image), jn(blob), jn(w)]))
end

# ---------------------------------------------------------------- encodings

function sedge(s, @nospecialize(x))
    x isa Core.CodeInstance && return obj("ci" => jn(id!(s, x)))
    x isa Core.MethodInstance && return obj("mi" => jn(id!(s, x)))
    x isa Method && return obj("m" => jn(id!(s, x)))
    x isa Int && return obj("int" => jn(x))
    x isa Core.Binding && return obj("b" => jn(id!(s, x)))
    x isa Core.PossiblyAmbiguous && return obj("pa" => "1")
    x isa Core.MethodTable && return obj("mt" => "1")
    x isa Type && return obj("ty" => obj("oid" => jn(id!(s, x)), "t" => sval(s, x)))
    error("unexpected edge $(typeof(x))")
end

function assigned_interferences(m::Method)
    out = Method[]
    intf = m.interferences
    for k in 1:length(intf)
        isassigned(intf, k) || break
        push!(out, intf[k]::Method)
    end
    return out
end

function smethod(s, m::Method; src=nothing, specs=Core.MethodInstance[])
    obj("uid" => jn(id!(s, m)), "sig" => sval(s, m.sig), "pw" => jn(m.primary_world),
        "ds" => jn(m.dispatch_status),
        "intf" => arr([jn(id!(s, x)) for x in assigned_interferences(m)]),
        "ilen" => jn(length(m.interferences)), "dss" => jn(m.did_scan_source),
        "blob" => jn(RU.external_blob_index(m)), "mt" => jbool(CC.get_methodtable(m) !== nothing),
        "src" => src === nothing ? "null" : arr([arr([g === nothing ? "null" : jn(id!(s, g)),
                                                      arr([u === nothing ? "null" : jn(id!(s, u)) for u in uses])])
                                                 for (g, uses) in src]),
        "igr" => jbool(CC.has_image_globalref(m)),
        "specs" => arr([jn(id!(s, mi)) for mi in specs]), "mod" => jn(id!(s, m.module)))
end

function cache_chain(mi::Core.MethodInstance)
    out = Core.CodeInstance[]
    isdefined(mi, :cache) || return out
    ci = mi.cache
    while true
        push!(out, ci)
        isdefined(ci, :next) || break
        ci = ci.next
    end
    return out
end

smi(s, mi::Core.MethodInstance; withcache=false) =
    obj("id" => jn(id!(s, mi)), "def" => jn(id!(s, mi.def)),
        "st" => obj("oid" => jn(id!(s, mi.specTypes)), "t" => sval(s, mi.specTypes)),
        "ds" => jn(mi.dispatch_status),
        "cache" => withcache ? arr([jn(id!(s, c)) for c in cache_chain(mi)]) : "[]")

sci(s, ci::Core.CodeInstance) =
    obj("id" => jn(id!(s, ci)), "mi" => jn(id!(s, CC.get_ci_mi(ci))), "on" => jbool(ci.owner === nothing),
        "min" => jn(ci.min_world), "max" => jn(ci.max_world), "flags" => jn(ci.flags),
        "edges" => isdefined(ci, :edges) ? arr([sedge(s, e) for e in ci.edges]) : "null",
        "blob" => jn(RU.external_blob_index(ci)))

function spartitions(s, b::Core.Binding)
    parts = String[]
    isdefined(b, :partitions) || return arr(parts)
    p = b.partitions
    while true
        k = UInt8(p.kind & 0x0f)
        r = "null"
        if Base.is_some_imported(k)
            rv = CC.partition_restriction(p)
            rv isa Core.Binding && (r = jn(id!(s, rv)))
        end
        push!(parts, obj("pid" => jn(id!(s, p)), "min" => jn(p.min_world), "max" => jn(p.max_world),
            "kind" => jn(p.kind), "r" => r))
        isdefined(p, :next) || break
        nx = p.next
        nx isa Core.BindingPartition || break
        p = nx
    end
    return arr(parts)
end

sbinding(s, b::Core.Binding) =
    obj("id" => jn(id!(s, b)), "parts" => spartitions(s, b), "flags" => jn(b.flags),
        "mod" => jn(id!(s, b.globalref.mod)))

function sheap(s; methods=Method[], mis=Core.MethodInstance[], cis=Core.CodeInstance[],
               bindings=Core.Binding[], srcs=IdDict{Method,Any}(), specs=IdDict{Method,Any}(),
               withcache=false)
    obj("wc" => jn(Base.get_world_counter()), "rw" => jn(Base.get_require_world()),
        "firw" => jn(unsafe_load(cglobal(:jl_first_image_replacement_world, UInt))),
        "methods" => arr([smethod(s, m; src=get(srcs, m, nothing), specs=get(specs, m, Core.MethodInstance[]))
                          for m in methods]),
        "mis" => arr([smi(s, mi; withcache) for mi in mis]),
        "cis" => arr([sci(s, c) for c in cis]),
        "bindings" => arr([sbinding(s, b) for b in bindings]))
end

state_json(cis, mis, methods, bindings) =
    obj("cis" => arr([arr([jn(id!(LSER[], c)), jn(c.min_world), jn(c.max_world)]) for c in cis]),
        "mis" => arr([arr([jn(id!(LSER[], m)), jn(m.dispatch_status)]) for m in mis]),
        "dss" => arr([arr([jn(id!(LSER[], m)), jn(m.did_scan_source)]) for m in methods]),
        "bf" => arr([arr([jn(id!(LSER[], b)), jn(b.flags)]) for b in bindings]))

const LSER = Ref{Any}(nothing)

errjson(e) = obj("err" => LS.jstr(string(nameof(typeof(e)))))

# ---------------------------------------------------------------- pool

const ARGTS = Any[Int, Integer, Signed, Real, Number, Any, Char, Union{Int,Char}, AbstractString,
                  String, Float64, AbstractFloat, Nothing, Int8, UInt8, Unsigned, Type{Int},
                  Type{<:Integer}, Vector{Int}, AbstractVector{<:Integer}, AbstractVector, Bool]
const CONCRETE = Any[Int, Char, String, Float64, Nothing, Int8, UInt8, Bool, Vector{Int}, Type{Int},
                     Type{Bool}]

struct CallT
    sig::Any
    matches::Vector{Method}
    fc::Bool
    amb::Bool
    mod::Int
end

# Modules 1-3 and the special ones are never changed at random; they make the edges of the
# "clean" graphs, which verification should accept unless a recorded lookup really changed.
const SLURP_MODS = (13, 14)
const WIDE_MOD = 15
isclean(k) = k <= 3 || k >= 13

mutable struct Pool
    mods::Vector{Module}
    fs::Vector{Any}
    wA::UInt
    wB::UInt
    wC::UInt
    calls::Vector{CallT}
    invokes::Vector{Tuple{Any,Method,Int}}
    mis::Vector{Core.MethodInstance}
    mimod::Vector{Int}
    bindings::Vector{Core.Binding}
    methods::Vector{Method}
end

randargt(rng) = rand(rng) < 0.6 ? rand(rng, ARGTS) : rand(rng, CONCRETE)

function method_expr(rng, k)
    nargs = rand(rng, (1, 1, 2, 2, 2, 3))
    args = Any[]
    for i in 1:nargs
        T = randargt(rng)
        push!(args, Expr(:(::), T))
    end
    r = rand(rng)
    if r < 0.12
        args[end] = Expr(:(::), :(Vararg{$(randargt(rng))}))
    elseif r < 0.2
        args[1] = Expr(:(::), :(AbstractVector{T}))
        return :(f($(args...)) where {T<:Integer} = $k)
    end
    return :(f($(args...)) = $k)
end

function def_method!(rng, mod, k)
    try
        Core.eval(mod, method_expr(rng, k))
    catch
    end
end

function randcallsig(rng, f)
    n = rand(rng, (1, 1, 2, 2, 2, 3))
    Tuple{typeof(f), (randargt(rng) for _ in 1:n)...}
end

function record_calls!(rng, P::Pool, f, k; sigs=nothing)
    for i in 1:(sigs === nothing ? 10 : length(sigs))
        sig = sigs === nothing ? randcallsig(rng, f) : sigs[i]
        amb = Ref(Int32(0))
        r = Base._methods_by_ftype(sig, nothing, -1, P.wA, false, Ref(UInt(1)), Ref(typemax(UInt)), amb)
        r === nothing && continue
        ms = Method[(m::Core.MethodMatch).method for m in r]
        fc = !isempty(ms) && sig <: Union{(m.sig for m in ms)...}
        push!(P.calls, CallT(sig, ms, fc, amb[] != 0, k))
        if length(r) == 1
            try
                push!(P.mis, Base.specialize_method(r[1])); push!(P.mimod, k)
            catch
            end
        end
        m, _ = CC._findsup(sig, nothing, P.wA)
        if m !== nothing
            push!(P.invokes, (sig, m.method, k))
        end
    end
    for m in methods(f)
        push!(P.invokes, (m.sig, m, k))
    end
end

function build_pool(rng)
    mods = Module[]; fs = Any[]
    P = Pool(mods, fs, 0, 0, 0, CallT[], Tuple{Any,Method,Int}[], Core.MethodInstance[], Int[],
             Core.Binding[], Method[])
    for k in 1:15
        mod = Module(Symbol("RP", k))
        Core.eval(mod, :(function f end))
        Core.eval(mod, :(const c1 = 1))
        Core.eval(mod, :(const c2 = 2))
        Core.eval(mod, :(global g1::Int = 1))
        Core.eval(mod, :(import Base: cos))
        if k in SLURP_MODS
            # the `Type{Union{}}` bottom slurp beats everything it meets
            Core.eval(mod, :(f(::Type{Union{}}) = 0))
            Core.eval(mod, :(f(::Type{<:Integer}) = 1))
            k == 14 && Core.eval(mod, :(f(::Type{<:Real}) = 2))
        elseif k == WIDE_MOD
            Core.eval(mod, :(f(::Any) = 0))
            for (j, T) in enumerate((Int8, Int16, Int32, Int64, UInt8, UInt16, UInt32, UInt64, Float16, Float32))
                Core.eval(mod, :(f(::$T) = $j))
            end
        else
            for j in 1:rand(rng, 2:5)
                def_method!(rng, mod, j)
            end
        end
        push!(mods, mod); push!(fs, Core.eval(mod, :f))
    end
    P.wA = Base.get_world_counter()
    for (k, f) in enumerate(fs)
        F = typeof(f)
        sigs = k in SLURP_MODS ?
            Any[Tuple{F, Type{<:Signed}}, Tuple{F, Type{<:Integer}}, Tuple{F, Type{Int}},
                Tuple{F, Type{<:Real}}, Tuple{F, Type{Union{}}}, Tuple{F, Type{<:Unsigned}}] :
            k == WIDE_MOD ? Any[Tuple{F, String}, Tuple{F, Char}, Tuple{F, Int8}, Tuple{F, Any},
                                Tuple{F, Symbol}, Tuple{F, Int}, Tuple{F, Integer}] : nothing
        record_calls!(rng, P, f, k; sigs)
    end
    for mod in mods
        for name in (:c1, :c2, :g1, :cos, :sqrt)
            push!(P.bindings, convert(Core.Binding, GlobalRef(mod, name)))
        end
    end
    for (m, n) in ((Base, :pi), (Base, :sin), (Core, :Int), (Base, :println), (Base, :+))
        push!(P.bindings, convert(Core.Binding, GlobalRef(m, n)))
    end
    function mutate!(round)
        for (k, mod) in enumerate(mods)
            if k in SLURP_MODS && round == 1
                # intersect the recorded signatures only at the `Type{Union{}}` corner
                Core.eval(mod, :(f(::Type{<:AbstractString}) = 7))
                Core.eval(mod, :(f(::Type{<:AbstractFloat}) = 8))
                k == 14 && Core.eval(mod, :(f(::Type{<:Unsigned}) = 9))
            elseif k == WIDE_MOD && round == 2
                Core.eval(mod, :(f(::Int128) = 20))
            end
            isclean(k) && continue
            f = fs[k]
            if rand(rng) < 0.5
                for j in 1:rand(rng, 1:2)
                    def_method!(rng, mod, 10 * round + j)
                end
            end
            ms = collect(methods(f))
            if rand(rng) < 0.3 && length(ms) > 1
                Base.delete_method(rand(rng, ms))
            end
            ms = collect(methods(f))
            if rand(rng) < 0.25 && !isempty(ms)
                m = rand(rng, ms)
                # redefine with the same signature: replaces the method
                try
                    sig = Base.unwrap_unionall(m.sig)
                    if !(m.sig isa UnionAll) && !Base.isvarargtype(sig.parameters[end])
                        args = [Expr(:(::), T) for T in sig.parameters[2:end]]
                        Core.eval(mod, :(f($(args...)) = $(100 + round)))
                    end
                catch
                end
            end
            if rand(rng) < 0.4
                Core.eval(mod, :(const c1 = $(1.5 * round)))
            end
        end
    end
    mutate!(1)
    P.wB = Base.get_world_counter()
    mutate!(2)
    for (k, mod) in enumerate(mods)
        if !isclean(k) && rand(rng) < 0.3
            ms = collect(methods(fs[k]))
            if !isempty(ms)
                mm = rand(rng, ms)
                @atomic mm.did_scan_source |= 0x4
            end
        end
    end
    for k in 1:60
        push!(INV_BATCHES, new_inv_batch(k))
        mod = Module(Symbol("RQ", k))
        Core.eval(mod, :(q(x) = x))
        f = Core.eval(mod, :q)
        m = first(methods(f))
        push!(ICC_BATCHES, [Base.specialize_method(m, Tuple{typeof(f), T}, Core.svec()) for T in (Int, Float64)])
    end
    P.wC = Base.get_world_counter()
    for f in fs
        for m in methods(f)
            push!(P.methods, m)
        end
    end
    # every method ever recorded (deleted ones too)
    for c in P.calls, m in c.matches
        m in P.methods || push!(P.methods, m)
    end
    return P
end

const TALLY = Dict{String,Int}()
tally!(k) = (TALLY[k] = get(TALLY, k, 0) + 1)

const INV_BATCHES = Any[]
const ICC_BATCHES = Any[]

# ---------------------------------------------------------------- verify cases

function pick_world(rng, P)
    r = rand(rng)
    r < 0.2 ? P.wA : r < 0.35 ? P.wB : r < 0.95 ? P.wC : rand(rng, P.wA:P.wC)
end

function mi_of_method(P, m::Method)
    for mi in P.mis
        mi.def === m && return mi
    end
    return nothing
end

function call_targets(rng, P, ms::Vector{Method}, cis)
    out = Any[]
    for m in ms
        r = rand(rng)
        mi = mi_of_method(P, m)
        if r < 0.3 && mi !== nothing
            push!(out, mi)
        elseif r < 0.4 && !isempty(cis)
            push!(out, rand(rng, cis))  # a CodeInstance target: its method stands in
        else
            push!(out, m)
        end
    end
    return out
end

function perturb(rng, P, ms::Vector{Method})
    ms = copy(ms)
    r = rand(rng)
    if r < 0.08 && !isempty(ms)
        deleteat!(ms, rand(rng, 1:length(ms)))
    elseif r < 0.16
        push!(ms, rand(rng, P.methods))
    elseif r < 0.2 && length(ms) > 1
        ms[1], ms[end] = ms[end], ms[1]
    end
    return ms
end

const BASE_BINDINGS = 5   # the last entries of `P.bindings` are old Base and Core bindings

function gen_edges(rng, P, cis, clean::Bool)
    items = Any[]
    calls = clean ? filter(c -> isclean(c.mod), P.calls) : P.calls
    mis = clean ? [mi for (mi, k) in zip(P.mis, P.mimod) if isclean(k)] : P.mis
    invokes = clean ? filter(x -> isclean(x[3]), P.invokes) : P.invokes
    for _ in 1:rand(rng, 0:5)
        r = rand(rng)
        pa = !clean && rand(rng) < 0.12
        if r < 0.22
            push!(items, rand(rng, cis))
        elseif r < 0.42 && !isempty(mis)
            pa && push!(items, Core.PossiblyAmbiguous())
            push!(items, rand(rng, mis))
        elseif r < 0.72 && !isempty(calls)
            c = rand(rng, calls)
            ms = clean ? c.matches : perturb(rng, P, c.matches)
            fc = clean || rand(rng) < 0.9 ? c.fc : !c.fc
            (pa || (c.amb && (clean || rand(rng) < 0.7))) && push!(items, Core.PossiblyAmbiguous())
            push!(items, fc ? length(ms) : -length(ms))
            push!(items, c.sig)
            append!(items, call_targets(rng, P, ms, cis))
        elseif r < 0.84 && !isempty(invokes)
            sig, m, _ = rand(rng, invokes)
            !clean && rand(rng) < 0.1 && (m = rand(rng, P.methods))
            push!(items, sig)
            t = rand(rng)
            mi = mi_of_method(P, m)
            push!(items, t < 0.1 ? Core.methodtable : (t < 0.35 && mi !== nothing) ? mi : m)
        else
            push!(items, clean ? P.bindings[end - rand(rng, 0:BASE_BINDINGS-1)] : rand(rng, P.bindings))
        end
    end
    !clean && rand(rng) < 0.003 && push!(items, rand(rng, P.methods))   # corrupt: a bare Method edge
    return items
end

edge_method(@nospecialize(x)) =
    x isa Method ? x : x isa Core.MethodInstance ? x.def :
    x isa Core.CodeInstance ? CC.get_ci_mi(x).def : nothing

function collect_heap(cis)
    methods = Method[]; mis = Core.MethodInstance[]; bindings = Core.Binding[]
    addm(m) = (m isa Method && !(m in methods)) && push!(methods, m)
    addmi(mi) = (mi in mis) || (push!(mis, mi); addm(mi.def))
    for c in cis
        addmi(CC.get_ci_mi(c))
        for e in c.edges
            if e isa Core.MethodInstance
                addmi(e)
            elseif e isa Method
                addm(e)
            elseif e isa Core.Binding
                e in bindings || push!(bindings, e)
            end
        end
    end
    # interference closure
    i = 1
    while i <= length(methods)
        for x in assigned_interferences(methods[i])
            addm(x)
        end
        i += 1
    end
    return methods, mis, bindings
end

# The sources of the methods `verify_method` may scan (`did_scan_source & 0x1 == 0`), and the
# bindings they read.
function scan_sources!(F, s, cis, methods, bindings, vw; extra=Method[])
    srcs = IdDict{Method,Any}()
    for m in Any[(CC.get_ci_mi(c).def for c in cis)..., extra...]
        m isa Method || continue
        (m.did_scan_source & 0x1) == 0 || continue
        haskey(srcs, m) && continue
        isdefined(m, :source) && m.source isa CC.MaybeCompressed || continue
        bs = src_bindings(m)
        srcs[m] = src_stmts(m)
        for b in bs
            b in bindings || push!(bindings, b)
            fact_bar!(F, s, b, vw)
        end
    end
    return srcs
end

function case_facts!(F, s, P, cis, methods, vw)
    worlds = unique!([c.min_world for c in cis])
    lims = Set{Int}([1])
    sigs = Any[]
    invsigs = Any[]
    for c in cis
        es = c.edges
        for (j, e) in enumerate(es)
            if e isa Int
                push!(lims, abs(e))
            elseif e isa Core.MethodInstance || e isa Core.CodeInstance
                mi = e isa Core.CodeInstance ? CC.get_ci_mi(e) : e
                push!(sigs, mi.specTypes)
            elseif e isa Type
                push!(sigs, e); push!(invsigs, e)
            elseif e isa Core.Binding
                fact_bar!(F, s, e, vw)
            end
        end
    end
    for sig in unique(sigs)
        for w in worlds, lim in lims
            fact_mm!(F, s, sig, lim, w)
        end
        for m in methods
            fact_sub!(F, s, sig, m.sig)
            ti = fact_isect!(F, s, sig, m.sig)
            if ti !== Union{}
                for m2 in methods
                    fact_sub!(F, s, ti, m2.sig)
                end
            end
        end
    end
    for sig in unique(invsigs)
        for w in worlds
            fact_fs!(F, s, sig, w)
        end
        for m in methods
            fact_egal!(F, s, sig, m.sig)
        end
    end
end

function new_ci(rng, P, mi, minw)
    r = rand(rng)
    maxw = r < 0.85 ? UInt(1) : r < 0.9 ? TM : r < 0.95 ? P.wC : UInt(0)
    owner = rand(rng) < 0.05 ? :other : nothing
    Core.CodeInstance(mi, owner, Any, Any, nothing, nothing, Int32(0), minw, maxw, UInt32(0),
                      nothing, nothing, Core.svec())
end

function gen_graph(rng, P)
    k = rand(rng, (1, 1, 2, 2, 3, 3, 4, 5, 6))
    clean = rand(rng) < 0.4
    pool = clean ? [mi for (mi, j) in zip(P.mis, P.mimod) if isclean(j)] : P.mis
    cis = [new_ci(rng, P, rand(rng, pool), clean && rand(rng) < 0.8 ? P.wC : pick_world(rng, P))
           for _ in 1:k]
    for c in cis
        @atomic c.edges = Core.svec(gen_edges(rng, P, cis, clean)...)
    end
    # a method instance loaded from an image may lack the dispatch-status bits computed here
    for c in cis, e in c.edges
        e isa Core.MethodInstance && rand(rng) < 0.1 && (@atomic e.dispatch_status = 0x00)
    end
    return cis
end

function pick_vw(rng, P)
    r = rand(rng)
    r < 0.85 ? P.wC : r < 0.93 ? P.wB : r < 0.995 ? P.wA : Base.get_require_world() - UInt(1)
end

# Empirical checks of the two verify_method properties left open in Lean (compiler-reinfer-range-bounded
# and compiler-reinfer-cycle-group): the returned range of a root awaiting verification stays inside
# [require_world, validation_world] unless rejected, and two members of one cycle of code instances
# awaiting verification are not left one valid in the validation world and one not.
function check_open_properties(root, cis, sentinel, vw, mn, mx)
    rw = Base.get_require_world()
    if root in sentinel && vw >= rw
        tally!(mx <= vw && (mx == 0 || mn >= rw) ? "range:bounded" : "range:VIOLATED")
    end
    # cycles through code instances that were already validated are not cycles the verifier walks
    succ(c) = [e for e in c.edges if e isa Core.CodeInstance && e in sentinel]
    function reach(a)
        seen = Any[a]; todo = Any[a]
        while !isempty(todo)
            x = pop!(todo)
            for y in succ(x)
                any(z -> z === y, seen) || (push!(seen, y); push!(todo, y))
            end
        end
        return seen
    end
    R = Dict{Any,Vector{Any}}(c => reach(c) for c in cis)
    for a in cis, b in cis
        a === b && continue
        (a in sentinel && b in sentinel) || continue
        (any(x -> x === b, R[a]) && any(x -> x === a, R[b])) || continue
        (a.max_world == UInt(1) || b.max_world == UInt(1)) && continue
        va = a.min_world <= vw <= a.max_world
        vb = b.min_world <= vw <= b.max_world
        if va == vb
            tally!("cycle:consistent")
        else
            tally!("cycle:SPLIT")
            println(stderr, "cycle:SPLIT vw=$vw a=[$(Int(a.min_world)),$(a.max_world)] b=[$(Int(b.min_world)),$(b.max_world)]",
                    " root=$(root === a ? "a" : root === b ? "b" : "other") root_ret=[$mn,$mx]")
            if get(ENV, "RI_DUMP_SPLIT", "") != ""
                idx(x) = findfirst(y -> y === x, cis)
                for (k, c) in enumerate(cis)
                    d = String[]
                    for e in c.edges
                        push!(d, e isa Core.CodeInstance ? "CI$(idx(e))" : e isa Core.MethodInstance ? "MI($(e.specTypes))" :
                                 e isa Core.Binding ? "B($(e.globalref))" : e isa Method ? "M($(e.sig))" : string(e))
                    end
                    println(stderr, "  CI$k$(c === a ? "(a)" : "")$(c === b ? "(b)" : "") mi=$(CC.get_ci_mi(c).specTypes) [$(Int(c.min_world)),$(c.max_world)] sentinel=$(c in sentinel) dss=$(CC.get_ci_mi(c).def.did_scan_source) edges=", join(d, " | "))
                end
            end
        end
    end
end

function gen_verify(rng, s, F, P, io, id)
    cis = gen_graph(rng, P)
    methods, mis, bindings = collect_heap(cis)
    vw = pick_vw(rng, P)
    case_facts!(F, s, P, cis, methods, vw)
    srcs = scan_sources!(F, s, cis, methods, bindings, vw)
    heap = sheap(s; methods, mis, cis, bindings, srcs)
    root = cis[1]
    sentinel = Set{Any}(c for c in cis if c.max_world == UInt(1))
    exp = try
        c, mn, mx = RU.verify_method(root, vw, RU.VerifyMethodWorkspace())
        tally!(mx == 0 ? "verify:rejected" : mx == TM ? "verify:accepted-open" : "verify:accepted-bounded")
        check_open_properties(root, cis, sentinel, vw, mn, mx)
        st = state_json(cis, mis, methods, bindings)
        obj("json" => "{" * "\"ret\":" * arr([jn(c), jn(mn), jn(mx)]) * "," * st[2:end])
    catch e
        tally!("verify:error-" * string(nameof(typeof(e))))
        errjson(e)
    end
    flush_facts(io, s, F)
    write_case(io, s, id, "r.verifyMethod", "typeinf", [heap, jn(id!(s, root)), jn(vw)], exp)
    return "r.verifyMethod"
end

function gen_insert(rng, s, F, P, io, id)
    cis = gen_graph(rng, P)
    methods, mis, bindings = collect_heap(cis)
    vw = Base.get_world_counter()
    case_facts!(F, s, P, cis, methods, vw)
    items = Any[]
    for c in shuffle(rng, cis)
        rand(rng) < 0.8 && push!(items, c)
    end
    rand(rng) < 0.3 && !isempty(methods) && insert!(items, 1, rand(rng, methods))
    rand(rng) < 0.1 && push!(items, nothing)
    srcs = scan_sources!(F, s, cis, methods, bindings, vw; extra=Method[x for x in items if x isa Method])
    heap = sheap(s; methods, mis, cis, bindings, srcs)
    sitems = arr([x isa Core.CodeInstance ? obj("ci" => jn(id!(s, x))) :
                  x isa Method ? obj("m" => jn(id!(s, x))) : "\"other\"" for x in items])
    exp = try
        RU.insert_backedges(Any[items...])
        for c in cis
            tally!(c.max_world == TM ? "insert:ci-promoted" : c.max_world == 0 ? "insert:ci-rejected" :
                   c.max_world == 1 ? "insert:ci-untouched" : "insert:ci-bounded")
        end
        obj("json" => state_json(cis, mis, methods, bindings))
    catch e
        errjson(e)
    end
    flush_facts(io, s, F)
    write_case(io, s, id, "r.insertBackedges", "typeinf", [heap, sitems], exp)
    return "r.insertBackedges"
end

# The Lean statement compiler-reinfer-binding-queries takes, as a promise of binding_access_range, that
# for a newest partition that is a leaf and contains `w` the access range starts no later than it. Check
# that promise and that the fast path agrees with the walk on every case.
function check_fastpath(b, w)
    rw = Base.get_require_world()
    w >= rw || return
    fast = RU.binding_changed_since_require_world(b, w)
    slow = CC.min_world(RU.binding_access_range_at(b, w)) > rw
    tally!(fast == slow ? "fastpath:agree" : "fastpath:DISAGREE")
    if isdefined(b, :partitions)
        p = b.partitions
        if CC.is_leaf_partition(p) && p.min_world <= w <= p.max_world
            tally!(CC.min_world(RU.binding_access_range_at(b, w)) <= p.min_world ? "leafpromise:holds" : "leafpromise:BROKEN")
        end
    end
end

function gen_bchanged(rng, s, F, P, io, id)
    b = rand(rng, P.bindings)
    w = rand(rng) < 0.7 ? P.wC : rand(rng) < 0.5 ? P.wB : rand(rng, (P.wA, Base.get_require_world(),
        Base.get_require_world() - UInt(1)))
    fact_bar!(F, s, b, w)
    heap = sheap(s; bindings=[b])
    exp = try
        obj("json" => jbool(RU.binding_changed_since_require_world(b, w)))
    catch e
        errjson(e)
    end
    check_fastpath(b, w)
    flush_facts(io, s, F)
    write_case(io, s, id, "r.bindingChanged", "typeinf", [heap, jn(id!(s, b)), jn(w)], exp)
    return "r.bindingChanged"
end

function gen_export(rng, s, F, P, io, id)
    b = rand(rng, P.bindings)
    parts = Core.BindingPartition[]
    if isdefined(b, :partitions)
        p = b.partitions
        while true
            push!(parts, p)
            isdefined(p, :next) && p.next isa Core.BindingPartition || break
            p = p.next
        end
    end
    isempty(parts) && return gen_bchanged(rng, s, F, P, io, id)
    p = rand(rng, parts)
    a, e, d = CC.ReinferUtils.export_affecting_partition_flags(p)
    k = UInt8(p.kind & 0x0f)
    r = "null"
    if Base.is_some_imported(k)
        rv = CC.partition_restriction(p)
        rv isa Core.Binding && (r = jn(id!(s, rv)))
    end
    sp = obj("pid" => jn(id!(s, p)), "min" => jn(p.min_world), "max" => jn(p.max_world),
             "kind" => jn(p.kind), "r" => r)
    flush_facts(io, s, F)
    write_case(io, s, id, "r.exportFlags", "typeinf", [sp], obj("json" => arr([jbool(a), jbool(e), jbool(d)])))
    return "r.exportFlags"
end

# ---------------------------------------------------------------- invalidate_method_for_globalref!

mutable struct InvBatch
    mod::Module
    methods::Vector{Method}
    mis::Vector{Core.MethodInstance}
    left::Int
end

function new_inv_batch(k)
    mod = Module(Symbol("RI", k))
    Core.eval(mod, quote
        const c1 = 1
        const c2 = 2
        h1() = c1 + 1
        h2(x) = x + c2
        h3() = 3
        h4(x) = (c1, c2, x)
    end)
    ms = Method[first(methods(Core.eval(mod, n))) for n in (:h1, :h2, :h3, :h4)]
    mis = Core.MethodInstance[]
    for m in ms
        for T in (m.nargs == 1 ? (Tuple{},) : (Tuple{Int}, Tuple{Float64}))
            tt = Tuple{typeof(Core.eval(mod, m.name)), T.parameters...}
            push!(mis, Base.specialize_method(m, tt, Core.svec()))
        end
    end
    InvBatch(mod, ms, mis, 40)
end

function src_bindings(m::Method)
    out = Core.Binding[]
    RU.foreachgr(CC._uncompressed_ir(m)) do gr::GlobalRef
        push!(out, convert(Core.Binding, gr))
    end
    return out
end

# The statements of `m`'s source as the GlobalRef scans read them: the binding of a statement
# that is a GlobalRef, and the values its userefs yield (a binding for a GlobalRef, else nothing).
function src_stmts(m::Method)
    out = Any[]
    for stmt in CC._uncompressed_ir(m).code
        g = stmt isa GlobalRef ? convert(Core.Binding, stmt) : nothing
        uses = Any[]
        for ur in CC.userefs(stmt)
            a = ur[]
            push!(uses, a isa GlobalRef ? convert(Core.Binding, a) : nothing)
        end
        (g !== nothing && !isempty(uses)) && tally!("stmt:globalref-with-uses")
        push!(out, (g, uses))
    end
    return out
end

function gen_invalidate(rng, s, F, P, io, id, B::Ref{Any}, nb::Ref{Int})
    if B[] === nothing || B[].left == 0
        nb[] += 1
        B[] = INV_BATCHES[mod1(nb[], length(INV_BATCHES))]
        B[].left = 40
    end
    b = B[]; b.left -= 1
    bc1 = convert(Core.Binding, GlobalRef(b.mod, :c1))
    bc2 = convert(Core.Binding, GlobalRef(b.mod, :c2))
    w = Base.get_world_counter()
    for mi in b.mis
        for _ in 1:rand(rng, 0:1)
            r = rand(rng)
            es = r < 0.3 ? Core.svec(bc1) : r < 0.5 ? Core.svec(bc2, mi) : r < 0.6 ? Core.svec(bc1, bc2) : Core.svec()
            maxw = rand(rng) < 0.8 ? TM : rand(rng, (w, w - UInt(1), UInt(5)))
            ci = Core.CodeInstance(mi, nothing, Any, Any, nothing, nothing, Int32(0), UInt(2), maxw,
                                   UInt32(0), nothing, nothing, es)
            ccall(:jl_mi_cache_insert, Cvoid, (Any, Any), mi, ci)
        end
    end
    m = rand(rng, b.methods)
    grn = rand(rng, (:c1, :c2))
    gb = grn === :c1 ? bc1 : bc2
    nmw = rand(rng) < 0.8 ? w : rand(rng, (UInt(1), w - UInt(3), TM - UInt(1)))
    specs = IdDict{Method,Any}(mm => collect(Core.MethodInstance, CC.specializations(mm)) for mm in b.methods)
    for (_, v) in specs, mi in v
        mi in b.mis || push!(b.mis, mi)
    end
    srcs = IdDict{Method,Any}(mm => src_stmts(mm) for mm in b.methods)
    cis = Core.CodeInstance[]
    for mi in b.mis
        append!(cis, cache_chain(mi))
    end
    heap = sheap(s; methods=b.methods, mis=b.mis, cis, bindings=[bc1, bc2], srcs, specs, withcache=true)
    exp = try
        r = RU.invalidate_method_for_globalref!(GlobalRef(b.mod, grn), m, gb.partitions, nmw)
        st = state_json(cis, b.mis, b.methods, [bc1, bc2])
        obj("json" => "{\"ret\":" * jbool(r) * "," * st[2:end])
    catch e
        errjson(e)
    end
    flush_facts(io, s, F)
    write_case(io, s, id, "r.invalidateMethod", "typeinf",
               [heap, jn(id!(s, gb)), jn(id!(s, m)), jn(nmw)], exp)
    return "r.invalidateMethod"
end

# ---------------------------------------------------------------- cicache

const WEDGE = UInt[0, 1, 2, 3, 100, typemax(UInt) - 1, typemax(UInt), typemax(UInt) - 2]
randw(rng) = rand(rng) < 0.5 ? rand(rng, WEDGE) : rand(rng) < 0.5 ? UInt(rand(rng, 0:12)) : rand(rng, UInt)

function randwr(rng)
    a = randw(rng)
    r = rand(rng)
    b = r < 0.3 ? a + UInt(rand(rng, 0:3)) : r < 0.4 ? a - UInt(1) : randw(rng)
    return (a, b)
end

function gen_wr(rng, s, F, P, io, id)
    r = rand(rng)
    if r < 0.15
        k = rand(rng, ("all", "single", "unit"))
        x, y = randwr(rng)
        wr = k == "all" ? CC.WorldRange() : k == "single" ? CC.WorldRange(x) : CC.WorldRange(x:y)
        exp = obj("json" => arr([jn(CC.first(wr)), jn(CC.last(wr)), jn(CC.min_world(wr)), jn(CC.max_world(wr))]))
        write_case(io, s, id, "r.wrNew", "typeinf", [LS.jstr(k), jn(x), jn(y)], exp)
        return "r.wrNew"
    elseif r < 0.3
        w = randw(rng); (a, b) = randwr(rng)
        rand(rng) < 0.3 && (w = rand(rng, (a, b, a - UInt(1), b + UInt(1))))
        write_case(io, s, id, "r.wrIn", "typeinf", [jn(w), arr([jn(a), jn(b)])],
                   obj("bool" => jbool(CC.in(w, CC.WorldRange(a, b)))))
        return "r.wrIn"
    end
    (a, b) = randwr(rng)
    (c, d) = rand(rng) < 0.5 ? randwr(rng) : (rand(rng, (a, b, b + UInt(1), b + UInt(2), a - UInt(1))), randw(rng))
    op = r < 0.65 ? "r.wrIntersect" : "r.wrUnion"
    exp = try
        x = op == "r.wrIntersect" ? CC.intersect(CC.WorldRange(a, b), CC.WorldRange(c, d)) :
                                    CC.union(CC.WorldRange(a, b), CC.WorldRange(c, d))
        obj("json" => arr([jn(x.min_world), jn(x.max_world)]))
    catch e
        errjson(e)
    end
    write_case(io, s, id, op, "typeinf", [arr([jn(a), jn(b)]), arr([jn(c), jn(d)])], exp)
    return op
end

const OWNERS = (nothing, :a, :b)
owner_class(@nospecialize(o)) = o === nothing ? 0 : o === :a ? 1 : 2

function gen_icc(rng, s, F, P, io, id, B::Ref{Any}, nb::Ref{Int})
    if B[] === nothing || B[][2] == 0
        nb[] += 1
        B[] = (ICC_BATCHES[mod1(nb[], length(ICC_BATCHES))], 30)
    end
    mis, left = B[]; B[] = (mis, left - 1)
    mi = rand(rng, mis)
    smallw() = UInt(rand(rng, (1, 2, 3, 5, 8, 10, 20)))
    for _ in 1:rand(rng, 0:2)
        mn = smallw(); mx = rand(rng) < 0.3 ? TM : mn + UInt(rand(rng, 0:10))
        ci = Core.CodeInstance(mi, rand(rng, OWNERS), Any, Any, nothing, nothing, Int32(0), mn, mx,
                               UInt32(0), nothing, nothing, Core.svec())
        ccall(:jl_mi_cache_insert, Cvoid, (Any, Any), mi, ci)
    end
    chain = cache_chain(mi)
    owner = rand(rng, OWNERS)
    a = smallw(); b = rand(rng) < 0.2 ? TM : a + UInt(rand(rng, 0:6))
    if rand(rng) < 0.3
        return gen_iccset(rng, s, io, id, mi, chain, owner)
    end
    kind = rand(rng, ("wr", "wr", "none", "single", "unit", "fields"))
    kind == "single" && (b = a)
    c = kind == "none" ? CC.InternalCodeCache(owner) :
        kind == "single" ? CC.InternalCodeCache(owner, a) :
        kind == "unit" ? CC.InternalCodeCache(owner, a:b) :
        kind == "fields" ? CC.InternalCodeCache(owner, a, b) : CC.InternalCodeCache(owner, CC.WorldRange(a, b))
    hk = CC.haskey(c, mi)
    g = CC.get(c, mi, nothing)
    gi = try
        jn(id!(s, CC.getindex(c, mi)))
    catch e
        e isa KeyError || rethrow()
        "\"KeyError\""
    end
    sc = arr([arr([jn(id!(s, x)), jn(x.min_world), jn(x.max_world), jn(owner_class(x.owner)),
                   jbool(isdefined(x, :inferred))]) for x in chain])
    exp = obj("json" => arr([jbool(hk), g === nothing ? "null" : jn(id!(s, g)), gi]))
    write_case(io, s, id, "r.icc", "typeinf", [jn(owner_class(owner)), arr([jn(a), jn(b)]), sc, LS.jstr(kind)], exp)
    return "r.icc"
end

has_invoke(x::Core.CodeInstance) = isdefined(x, :inferred) && x.invoke != C_NULL
centry(s, x::Core.CodeInstance) = arr([jn(id!(s, x)), jn(x.min_world), jn(x.max_world), jn(owner_class(x.owner)),
                                       jbool(isdefined(x, :inferred)), jbool(has_invoke(x))])

# setindex! on a fresh code instance, or on one already in the chain (which may move down it)
function gen_iccset(rng, s, io, id, mi, chain, owner)
    if !isempty(chain) && rand(rng) < 0.3
        ci = rand(rng, chain)
    else
        mn = UInt(rand(rng, (1, 2, 3, 5, 8, 10, 20))); mx = rand(rng) < 0.3 ? TM : mn + UInt(rand(rng, 0:10))
        ci = Core.CodeInstance(mi, rand(rng) < 0.7 ? owner : rand(rng, OWNERS), Any, Any, nothing, nothing,
                               Int32(0), mn, mx, UInt32(0), nothing, nothing, Core.svec())
    end
    sc = arr([centry(s, x) for x in chain])
    e = centry(s, ci)
    exp = try
        CC.setindex!(CC.InternalCodeCache(owner, CC.WorldRange()), ci, mi)
        obj("json" => arr([jbool(mi.def isa Method), arr([jn(id!(s, x)) for x in cache_chain(mi)])]))
    catch err
        err isa AssertionError || rethrow()
        errjson(err)
    end
    write_case(io, s, id, "r.iccSet", "typeinf", [jn(owner_class(owner)), sc, e, jbool(mi.def isa Method)], exp)
    return "r.iccSet"
end

# ---------------------------------------------------------------- package images

const RIDEP_SRC = """
module RIDep
g(x::Integer) = 1
g(x::AbstractString) = 2
g(x::Type{<:Integer}) = 3
g(::Type{Union{}}) = 0
const K = 3
const L = 4
h(x) = g(x) + K
k(x::Integer) = 1
k(x::Int) = 2
k(x::Signed) = 3
export g
end
"""

const RIPKG_SRC = """
module RIPkg
using RIDep
f1(x) = RIDep.g(x) + 1
f2(x::Int) = RIDep.h(x)
f3() = RIDep.K
f4() = RIDep.L
f5(x) = invoke(RIDep.g, Tuple{Integer}, x)
f6(x) = g(x)
f7(T) = RIDep.g(T)
f8(x) = f1(x) + f2(x)
f9(x) = x > 0 ? f9(x - 1) : f1(x)
f10(x) = x > 0 ? f11(x - 1) : f4()
f11(x) = x > 0 ? f10(x - 1) : f3()
f12(x) = string(f1(x))
f13(x) = RIDep.k(x)
f14(x) = invoke(RIDep.k, Tuple{Int8}, x)
precompile(f1, (Int,)); precompile(f1, (String,)); precompile(f1, (Int8,))
precompile(f2, (Int,)); precompile(f3, ()); precompile(f4, ()); precompile(f5, (Int,))
precompile(f6, (Int8,)); precompile(f6, (Int,)); precompile(f7, (Type{Int},))
precompile(f7, (Type{Union{}},)); precompile(f8, (Int,)); precompile(f9, (Int,))
precompile(f10, (Int,)); precompile(f12, (Int,))
precompile(f13, (Int8,)); precompile(f13, (Integer,)); precompile(f13, (Signed,)); precompile(f14, (Int8,))
end
"""

const IMG_CIS = Core.CodeInstance[]

# Precompile two small packages into a fresh depot, load them, then change what their edges
# recorded: methods added to `RIDep.g` (one that changes recorded matches, one that meets them
# only at the `Type{Union{}}` corner), and on odd seeds a rebound image const (which makes
# `jl_first_image_replacement_world` finite, so sources get scanned).
function setup_images!(seed)
    dir = mktempdir()
    for (name, src, deps) in (("RIDep", RIDEP_SRC, ""), ("RIPkg", RIPKG_SRC,
            "[deps]\nRIDep = \"6d4f0a2e-1111-4a5b-9c3d-000000000001\"\n"))
        mkpath(joinpath(dir, "pkgs", name, "src"))
        uuid = name == "RIDep" ? "6d4f0a2e-1111-4a5b-9c3d-000000000001" : "6d4f0a2e-1111-4a5b-9c3d-000000000002"
        write(joinpath(dir, "pkgs", name, "Project.toml"), "name = \"$name\"\nuuid = \"$uuid\"\n$deps")
        write(joinpath(dir, "pkgs", name, "src", "$name.jl"), src)
    end
    pushfirst!(DEPOT_PATH, joinpath(dir, "depot"))
    pushfirst!(LOAD_PATH, joinpath(dir, "pkgs"))
    @eval Main using RIPkg
    RIDep = Base.root_module(Base.PkgId(Base.UUID("6d4f0a2e-1111-4a5b-9c3d-000000000001"), "RIDep"))
    RIPkg = Base.root_module(Base.PkgId(Base.UUID("6d4f0a2e-1111-4a5b-9c3d-000000000002"), "RIPkg"))
    Core.eval(RIDep, :(g(x::Int8) = 9))
    Core.eval(RIDep, :(g(::Type{<:AbstractString}) = 7))
    isodd(seed) && Core.eval(RIDep, :(const L = 5))
    for mod in (RIPkg, RIDep)
        for name in names(mod; all=true)
            isdefined(mod, name) || continue
            f = getfield(mod, name)
            f isa Function || continue
            parentmodule(f) === mod || continue
            for m in methods(f), mi in CC.specializations(m), ci in cache_chain(mi)
                ci.owner === nothing && RU.external_blob_index(ci) != TM || continue
                # weight the code that reaches the image-provenance paths
                for _ in 1:(m.name in (:f13, :f14) ? 4 : 1)
                    push!(IMG_CIS, ci)
                end
            end
        end
    end
    return length(IMG_CIS)
end

function parse_edges(es)
    out = Any[]
    j = 1
    while j <= length(es)
        e = es[j]
        e isa Method && break
        if e isa Core.PossiblyAmbiguous
            j += 1
            j > length(es) && break
            e = es[j]
        end
        e isa Core.CodeInstance && (e = CC.get_ci_mi(e))
        if e isa Core.MethodInstance
            push!(out, (:call, e.specTypes, Method[e.def]))
            j += 1
        elseif e isa Int
            n = abs(e)
            E = Method[]
            for i in 1:n
                m = edge_method(es[j+1+i])
                m isa Method && push!(E, m)
            end
            push!(out, (:call, es[j+1], E))
            j += 2 + n
        elseif e isa Core.Binding
            push!(out, (:binding, e))
            j += 1
        else
            j + 1 <= length(es) || break
            callee = es[j+1]
            j += 2
            callee isa Core.MethodTable && continue
            m = edge_method(callee)
            m isa Method && push!(out, (:invoke, e, m))
        end
    end
    return out
end

function gen_image(rng, s, F, P, io, id)
    isempty(IMG_CIS) && return gen_wr(rng, s, F, P, io, id)
    roots = unique([rand(rng, IMG_CIS) for _ in 1:rand(rng, (1, 1, 2, 3))])
    w = Base.get_world_counter()
    for r in roots
        @atomic r.max_world = UInt(1)
        rand(rng) < 0.4 && (@atomic r.min_world = w)
    end
    # code instances reachable through edges, down to the first already-validated ones
    cis = Core.CodeInstance[]
    todo = copy(roots)
    while !isempty(todo)
        c = popfirst!(todo)
        c in cis && continue
        if !(c in roots) && RU.external_blob_index(c) != TM && c.max_world != UInt(1) && rand(rng) < 0.5
            @atomic c.max_world = UInt(1)
        end
        push!(cis, c)
        # `jl_promote_ci_to_current` also walks code instances valid up to exactly this world
        (c.max_world == UInt(1) || c.max_world == w) || continue
        for e in c.edges
            e isa Core.CodeInstance && push!(todo, e)
        end
    end
    length(cis) > 60 && (tally!("image:skipped-large"); return gen_wr(rng, s, F, P, io, id))
    # as loaded from an image, without the dispatch-status bits this process computed
    for c in cis
        c.max_world == UInt(1) || continue
        for e in c.edges
            mi = e isa Core.CodeInstance ? CC.get_ci_mi(e) : e
            mi isa Core.MethodInstance && rand(rng) < 0.3 && (@atomic mi.dispatch_status = 0x00)
        end
    end
    methods = Method[]; mis = Core.MethodInstance[]; bindings = Core.Binding[]
    addm(m) = (m isa Method && !(m in methods)) && push!(methods, m)
    addmi(mi) = (mi in mis) || (push!(mis, mi); addm(mi.def))
    vw = w
    for c in cis
        addmi(CC.get_ci_mi(c))
        c.max_world == UInt(1) || continue
        img = RU.external_blob_index(c)
        for e in c.edges
            e isa Core.MethodInstance && addmi(e)
            e isa Core.CodeInstance && addmi(CC.get_ci_mi(e))
            e isa Method && addm(e)
        end
        for p in parse_edges(c.edges)
            if p[1] === :call
                _, sig, E = p
                foreach(addm, E)
                D1 = Method[]
                for m in E, x in assigned_interferences(m)
                    x in D1 || push!(D1, x)
                end
                foreach(addm, D1)
                for x in D1, y in assigned_interferences(x)
                    addm(y)
                end
                for lim in unique([1, length(E)])
                    fact_mm!(F, s, sig, lim, c.min_world)
                end
                fact_scw!(F, s, sig, img)
                for m in E
                    fact_sub!(F, s, sig, m.sig)
                end
                for x in D1
                    fact_sub!(F, s, sig, x.sig)
                    fact_bdw!(F, s, img, RU.external_blob_index(x))
                    ti = fact_isect!(F, s, sig, x.sig)
                    if ti !== Union{}
                        for m2 in E
                            fact_sub!(F, s, ti, m2.sig)
                        end
                    end
                end
            elseif p[1] === :invoke
                _, sig, m = p
                addm(m)
                fact_egal!(F, s, sig, m.sig)
                fact_scw!(F, s, sig, img)
                fact_fs!(F, s, sig, c.min_world)
            else
                b = p[2]
                b in bindings || push!(bindings, b)
                fact_bar!(F, s, b, vw)
            end
        end
    end
    length(methods) > 400 && (tally!("image:skipped-methods"); return gen_wr(rng, s, F, P, io, id))
    srcs = scan_sources!(F, s, [c for c in cis if c.max_world == UInt(1)], methods, bindings, vw)
    heap = sheap(s; methods, mis, cis, bindings, srcs)
    single = length(roots) == 1 && rand(rng) < 0.6
    exp = try
        if single
            c, mn, mx = RU.verify_method(roots[1], vw, RU.VerifyMethodWorkspace())
            tally!(mx == 0 ? "image:rejected" : "image:accepted")
            st = state_json(cis, mis, methods, bindings)
            obj("json" => "{" * "\"ret\":" * arr([jn(c), jn(mn), jn(mx)]) * "," * st[2:end])
        else
            RU.insert_backedges(Any[roots...])
            for r in roots
                tally!(r.max_world == 0 ? "image:rejected" : "image:accepted")
            end
            obj("json" => state_json(cis, mis, methods, bindings))
        end
    catch e
        tally!("image:error-" * string(nameof(typeof(e))))
        errjson(e)
    end
    flush_facts(io, s, F)
    if single
        write_case(io, s, id, "r.verifyMethod", "typeinf", [heap, jn(id!(s, roots[1])), jn(vw)], exp)
    else
        write_case(io, s, id, "r.insertBackedges", "typeinf",
                   [heap, arr([obj("ci" => jn(id!(s, r))) for r in roots])], exp)
    end
    return single ? "r.verifyMethod(image)" : "r.insertBackedges(image)"
end

# ---------------------------------------------------------------- main

function main(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    s = Ser(); LSER[] = s
    F = Facts()
    nimg = setup_images!(seed)
    P = build_pool(rng)
    dir = mktempdir()
    casefile = joinpath(dir, "cases.jsonl")
    ops = Dict{Int,String}()
    ib = Ref{Any}(nothing); nib = Ref(0)
    qb = Ref{Any}(nothing); nqb = Ref(0)
    open(casefile, "w") do io
        for id in 1:n
            r = rand(rng)
            ops[id] = if r < 0.1
                gen_image(rng, s, F, P, io, id)
            elseif r < 0.38
                gen_verify(rng, s, F, P, io, id)
            elseif r < 0.46
                gen_insert(rng, s, F, P, io, id)
            elseif r < 0.53
                gen_bchanged(rng, s, F, P, io, id)
            elseif r < 0.55
                gen_export(rng, s, F, P, io, id)
            elseif r < 0.64
                gen_invalidate(rng, s, F, P, io, id, ib, nib)
            elseif r < 0.72
                gen_icc(rng, s, F, P, io, id, qb, nqb)
            else
                gen_wr(rng, s, F, P, io, id)
            end
        end
    end
    if haskey(opts, "dump")
        cp(casefile, opts["dump"]; force=true)
        println("WROTE $n cases to $(opts["dump"])")
        return 0
    end
    out = read(pipeline(`$(opts["exe"])`, stdin=casefile), String)
    agree = 0; unmodelled = 0; bad = String[]; seen = 0
    perop = Dict{String,Vector{Int}}()
    outcomes = Dict{String,Int}()
    for line in split(out, '\n'; keepempty=false)
        m = match(r"\"id\":(\d+)", line)
        if m === nothing
            push!(bad, line); continue
        end
        id = parse(Int, m[1]); seen += 1
        st = get!(perop, ops[id], [0, 0, 0])
        if occursin("\"agree\":true", line)
            agree += 1; st[1] += 1
            pm = match(r"\"paths\":\[([^\]]*)\]", line)
            if pm !== nothing
                for t in unique(split(pm[1], ','))
                    tally!("path " * strip(t, '"'))
                end
            end
        elseif occursin("\"unmodelled\":true", line)
            unmodelled += 1; st[2] += 1
        else
            push!(bad, line); st[3] += 1
        end
    end
    for (op, st) in sort(collect(perop))
        println(rpad(op, 28), " agree=", st[1], " unmodelled=", st[2], " disagree=", st[3])
    end
    for line in first(bad, parse(Int, opts["show"]))
        println("DISAGREE ", first(line, 3000))
    end
    for (k, v) in sort(collect(TALLY))
        println("  ", rpad(k, 40), v)
    end
    println("IMAGES $nimg code instances")
    println("POOL wA=$(P.wA) wB=$(P.wB) wC=$(P.wC) methods=$(length(P.methods)) calls=$(length(P.calls)) mis=$(length(P.mis))")
    println("SEED $seed CASES $n ANSWERED $seen UNMODELLED $unmodelled")
    println("AGREE $agree/$(seen - unmodelled)")
    rm(dir; recursive=true)
    return isempty(bad) && seen == n ? 0 : 1
end

exit(main())
