# Differential test of the Lean models of Compiler/src/inferenceresult.jl
# (JuliaLean/Compiler/src/inferenceresult.lean), of the result-caching decisions of
# Compiler/src/typeinfer.jl (JuliaLean/Compiler/src/typeinfer.lean) and of `count_const_size` /
# `is_inlineable_constant` (JuliaLean/Compiler/src/utilities.lean) against the pinned Julia
# (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA difftest/compiler/cacheresult.jl --cases 20000 --seed 1
#
# Ops (each calls the pinned Compiler function directly):
#   cr.mostGeneral          most_general_argtypes(method or nothing, specTypes)
#   cr.nospecInfer          get_nospecializeinfer_argtypes(argtypes, cache_argtypes, method)
#   cr.matchSimple          matching_cache_argtypes(𝕃, mi, SimpleArgtypes(argtypes), cache_argtypes)
#                           (so pick_const_args!, pick_const_arg, tmeet of PartialStructs)
#   cr.rehit                the key const_prop_call builds (matching_cache_argtypes), its
#                           overridden_by_const flags (abstractinterpretation.jl:1517-1522), and
#                           constprop_cache_lookup of that key in a cache holding only its entry
#   cr.isArgtypeMatch       is_argtype_match(𝕃, given, cache, overridden_by_const)
#   cr.vaProcess            va_process_argtypes(𝕃, given, nargs, isva, mi)
#   cr.lookup               constprop_cache_lookup(𝕃, mi, given, cache, world) on a real
#                           InferenceCache of LocalInferenceResult and raw InferenceResult entries
#   cr.countConstSize       count_const_size(x, count_self)
#   cr.isInlineableConstant is_inlineable_constant(x)
#   cr.constabi             is_result_constabi_eligible(result) / result_is_constabi(interp, result)
#   cr.discard              discard_optimized_result(interp, mi, inlining_cost)
#   cr.compress             maybe_compress_codeinfo(interp, mi, ci), compared by kind of result
# The interpreter hooks (`may_discard_trees`, `precompile_keep_ir`, `may_compress`) come from a
# small `AbstractInterpreter` whose answers are per case. `jl_generating_output()` is 0 in this
# process, so `keep_source_for_output` is always false here; the model's `true` branch is not
# exercised.
#
# Inputs are biased to the edge cases of the area: specTypes shorter or longer than
# `method.nargs`, with and without a `Vararg` tail, `Vararg{T,N}` with a free `N`, `UnionAll`
# wrappers whose variable occurs only in a `Vararg` or a `Type{T}`, singleton and constant-type
# parameters (`Const` replacement), `Tuple{}` and non-tuple specTypes; argument lists whose cache
# entry is lattice-equal but not `===` (rebuilt `PartialStruct`s, reordered `Union` tuples),
# `PartialStruct`s wider than the cache type (the `tmeet` branch), `Vararg` on either or both sides
# and lengths that differ, `Conditional`/`MustAlias` on slots past the varargs position, cache
# entries in other worlds, tombstones, `overridden_by_const === nothing` and short
# `overridden_by_const` vectors; constants at and around the 256-byte limit (NTuple{32,Int} vs
# NTuple{33,Int}), `String`/`Memory`/`svec` payloads, mutable structs with only `const` fields,
# inline union fields, and `Const` results with effects either side of `is_foldable_nothrow`.
#
# Prints `AGREE k/n`; cases the model reports as `unmodelled` are counted separately and are not
# agreement.
#
# Runs (seed, cases, agreement):
#   2026-11-10, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 17000 cases: AGREE 17000/17000, 0 unmodelled
#   seed 2, 17000 cases: AGREE 17000/17000, 0 unmodelled
#   seed 3, 17000 cases: AGREE 17000/17000, 0 unmodelled
#   Per op and seed: about 2900 mostGeneral, 3400 matchSimple, 2500 lookup, 2050 vaProcess,
#   1300 constabi, 1200 isArgtypeMatch, 1000 nospecInfer, 950 countConstSize, 600
#   isInlineableConstant, 500 discard, 500 compress. Expected results that are Julia exceptions:
#   about 18% of mostGeneral (mostly `UndefVarError` for `lastatype`), 40% of vaProcess, 8% of
#   matchSimple (`AssertionError`), 2% of lookup. Lookup outcomes over the three seeds: 625
#   found, 149 `missing` (a tombstone matched), 6663 `nothing`; count_const_size 92 at exactly
#   256, 911 over, 1837 under.
#   The first run found one model bug, in two places, now fixed: a `(← ...)` inside `&&` ran
#   its action even when the left side was false (a layout lookup in count_const_size, 98
#   cases reported unmodelled; `given[end]` in va_process_argtypes).
#   Sensitivity (5000 cases, seed 3): with MAX_INLINE_CONST_SIZE = 255, `min` for `max` in
#   pick_const_args!, tombstones ignored in the lookup, `≥` for `>` on the Conditional slot in
#   va_process_argtypes, no isconstType branch in most_general_argtypes and `is_foldable` for
#   `is_foldable_nothrow` in is_result_constabi_eligible, 267 cases disagreed (mostGeneral 98,
#   countConstSize 87, matchSimple 53, isInlineableConstant 10, constabi 8, lookup 8,
#   vaProcess 3).
#   2026-11-10, proof pass: the model's lookup loops rewritten as recursion
#   (constpropLookupLoop, argtypesMatch) and the cr.rehit op added (30% of the matchSimple
#   draws), pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 17000 cases: AGREE 17000/17000, 0 unmodelled (cr.rehit 1091)
#   seed 2, 17000 cases: AGREE 17000/17000, 0 unmodelled (cr.rehit 980)
#   seed 3, 17000 cases: AGREE 17000/17000, 0 unmodelled (cr.rehit 1062)
#   cr.rehit outcomes over the three seeds: 1417 keys with no flag set, 788 flagged and found
#   again, 676 flagged and missed; 252 were Julia exceptions (AssertionError).
#   2026-11-10, review-fix pass (branch statements in inferenceresult/Exact.lean; model
#   unchanged), pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 4, 17000 cases: AGREE 17000/17000, 0 unmodelled (cr.rehit 1069)

include(joinpath(@__DIR__, "common.jl"))
using .LatticeSer
using Random

abstract type AbsC end
struct CU <: AbsC end
mutable struct MU <: AbsC
    x::Int
end
mutable struct MC
    const a::Int
    const b::Any
end
mutable struct MC0 end
struct PU{T} <: AbsC
    x::T
end
struct Two
    a::Union{Int,Nothing}
    b::Any
end
struct Wrap
    s::Some{Any}
    k::Int
end
struct Half
    a::Int
    b::Any
    Half(a) = new(a)
end

function parse_args(args)
    opts = Dict("cases" => "2000", "seed" => "1", "exe" => joinpath(@__DIR__, "..", "..",
                ".lake", "build", "bin", "compilerdiff"), "show" => "20")
    i = 1
    while i <= length(args)
        startswith(args[i], "--") || error("unexpected argument $(args[i])")
        opts[args[i][3:end]] = args[i+1]
        i += 2
    end
    return opts
end

const LATTICES = [("typeinf", CC.typeinf_lattice(CC.NativeInterpreter())),
                  ("ipo", CC.ipo_lattice(CC.NativeInterpreter())),
                  ("opt", CC.optimizer_lattice(CC.NativeInterpreter())),
                  ("jltype", CC.JLTypeLattice())]
pick_lattice(rng) = rand(rng) < 0.6 ? LATTICES[1] : rand(rng, LATTICES)

# --- the interpreter hooks ---------------------------------------------------------------------

struct CRInterp <: CC.AbstractInterpreter
    discard::Bool
    keepir::Bool
    compress::Bool
end
CC.may_discard_trees(i::CRInterp) = i.discard
CC.precompile_keep_ir(i::CRInterp) = i.keepir
CC.may_compress(i::CRInterp) = i.compress

# --- methods and method instances --------------------------------------------------------------

f0() = 1
f1(a) = 1
f2(a, b) = 1
f3(a, b, c) = 1
f5(a, b, c, d, e) = 1
fv1(a...) = 1
fv2(a, b...) = 1
fv4(a, b, c, d...) = 1
const POOL_FUNCS = Any[f0, f1, f2, f3, f5, fv1, fv2, fv4]
const POOL_METHODS = Method[only(methods(f)) for f in POOL_FUNCS]

# Methods with every `@nospecialize` mask over up to 4 arguments, with and without
# `@nospecializeinfer`, and a varargs variant.
const NSI_METHODS = Method[]
for nargs in 1:4, mask in 0:(2^nargs - 1), infer in (false, true), va in (false, true)
    name = gensym(:nsi)
    args = Any[]
    for i in 1:nargs
        a = Symbol(:a, i)
        a = (va && i == nargs) ? Expr(:..., a) : a
        push!(args, (mask >> (i - 1)) & 1 == 1 ? :(@nospecialize($a)) : a)
    end
    def = :($name($(args...)) = 1)
    infer && (def = :(Base.@nospecializeinfer $def))
    Core.eval(@__MODULE__, def)
    push!(NSI_METHODS, Core.eval(@__MODULE__, :(only(methods($name)))))
end

const MI_VA = CC.specialize_method(only(methods(fv2)), Tuple{typeof(fv2), Int, Vararg{Any}}, Core.svec())
const MI_FIX = CC.specialize_method(only(methods(f2)), Tuple{typeof(f2), Int, Any}, Core.svec())
const MI_ANY = MI_FIX

# --- types --------------------------------------------------------------------------------------

const LEAF = Any[Int, Int8, Bool, Float64, Nothing, Missing, Symbol, String, Char, CU, MU, Tuple{},
                 Union{}, Two, PU{Int}, Vector{Int}, Some{Int}, typeof(sin), typeof(f2), Val{1}]
const ABSTRACT = Any[Any, Integer, Signed, Real, Number, AbsC, AbstractString, AbstractVector{Int},
                     Type, DataType, Function, Some, PU, Type{Int}, Core.TypeEgal{Int}, Type{Union{}},
                     Core.TypeEgal{Union{}}, Union, UnionAll, Core.TypeofBottom, Type{Nothing}]
leaftype(rng) = rand(rng) < 0.65 ? rand(rng, LEAF) : rand(rng, ABSTRACT)

function randunion(rng, k=rand(rng, 2:4))
    ts = Any[rand(rng) < 0.75 ? rand(rng, LEAF) : rand(rng, ABSTRACT) for _ in 1:k]
    return Union{ts...}
end

function randtype(rng, depth=2)
    r = rand(rng)
    if depth <= 0 || r < 0.45
        return leaftype(rng)
    elseif r < 0.6
        return randunion(rng)
    elseif r < 0.75
        return randtuple(rng, depth - 1)
    elseif r < 0.88
        t = randtype(rng, depth - 1)
        return try (rand(rng) < 0.6 ? Type{t} : Core.TypeEgal{t}) catch; Type end
    else
        return try rand(rng, (Some, Vector, PU, Ref)){randtype(rng, depth - 1)} catch; Some end
    end
end

function randtuple(rng, depth=1)
    k = rand(rng, 0:4)
    ps = Any[randtype(rng, depth - 1) for _ in 1:k]
    if k > 0 && rand(rng) < 0.25 && ps[end] !== Union{}
        ps[end] = rand(rng) < 0.7 ? Vararg{ps[end]} : Vararg{ps[end], rand(rng, 0:3)}
    end
    return try Tuple{ps...} catch; Tuple{Int,Union{Int,Nothing}} end
end

# specTypes-like signatures, many with free variables in odd places.
const SPEC_UA = Any[
    Tuple{typeof(f2), T, Vector{T}} where T, Tuple{typeof(f2), T, Type{T}} where T<:Integer,
    Tuple{typeof(fv2), Vararg{T}} where T, Tuple{typeof(fv2), Int, Vararg{T}} where T<:Real,
    Tuple{typeof(fv2), Vararg{Int, N}} where N, Tuple{typeof(fv2), T, Vararg{Any, N}} where {T, N},
    Tuple{typeof(fv4), Vararg{Type{T}}} where T, Tuple{typeof(f2), Type{T}, T} where T,
    Tuple{typeof(f2), Core.TypeEgal{Int}, T} where T, Tuple{typeof(f3), T, T, T} where T<:Signed,
    Tuple{typeof(fv1), Vararg{Union{T, Nothing}}} where T, Tuple{typeof(f1), Union{T, Int}} where T,
    Tuple{typeof(fv2), Some{T}, Vararg{Some{T}}} where T, Tuple{T} where T, Tuple{Vararg{T}} where T,
    Tuple{typeof(f2), Val{N}, NTuple{N, Int}} where N, Tuple{typeof(fv1), Type{<:Integer}},
    Tuple{typeof(f2), Type{Vector{T}} where T, Int}, Tuple{typeof(f2), Nothing, Missing},
    Tuple{typeof(fv2), Nothing, Vararg{Nothing}}, Tuple{typeof(fv2), Type{Int}, Vararg{Type{Int}}},
    Tuple{typeof(fv2), Core.TypeEgal{Int}, Vararg{Core.TypeEgal{Int}}}, Tuple{typeof(fv2), Type{Union{}}, Vararg{CU}}]

function randspec(rng)
    r = rand(rng)
    r < 0.35 && return rand(rng, SPEC_UA)
    if r < 0.4
        return rand(rng, (Tuple{}, Union{}, Int, Vector{Int}, Some{Int}, Tuple{Vararg{Any}}, Tuple))
    end
    F = rand(rng) < 0.8 ? typeof(rand(rng, POOL_FUNCS)) : leaftype(rng)
    k = rand(rng, 0:5)
    ps = Any[F]
    for _ in 1:k
        push!(ps, rand(rng) < 0.6 ? leaftype(rng) : randtype(rng, 1))
    end
    if rand(rng) < 0.4
        T = rand(rng) < 0.7 ? leaftype(rng) : randunion(rng, 2)
        T === Union{} || push!(ps, rand(rng) < 0.85 ? Vararg{T} : Vararg{T, rand(rng, 0:2)})
    end
    return try Tuple{ps...} catch; Tuple{typeof(f2), Int} end
end

randnargs(rng, spec) = rand(rng) < 0.15 ? nothing :
    (rand(rng) < 0.6 ? rand(rng, POOL_METHODS) : rand(rng, NSI_METHODS))

# --- lattice elements ---------------------------------------------------------------------------

const VALUES = Any[1, 0, true, false, nothing, :a, (), (1,), (1, :a), (nothing, 2.0), Some(1),
    1.5, 0x01, Int, Union{}, Any, Union{Int,Nothing}, Vector{Int}, Some{T} where T, Type{Int},
    "str", missing, CU(), PU(1), PU(:a), Two(1, 2), Two(nothing, :x), (a=1,), ((1, 2), 3),
    ('c', 1), (Int, 1), sin, f2, Val(1), Core.svec(), Some{Any}(1), Half(3)]

mutable struct Gen
    rng::Random.AbstractRNG
    causes::Any
end

function Gen(rng)
    IS = CC.InferenceState{CC.NativeInterpreter}
    st = ccall(:jl_new_struct_uninit, Any, (Any,), IS)
    S = fieldtype(CC.LimitedAccuracy, :causes)
    c = S(); push!(c, st)
    Gen(rng, c)
end

const FB = CC.fallback_lattice

function rand_ps(rng)
    r = rand(rng)
    try
        r < 0.2 && return Core.PartialStruct(FB, Tuple{Int,Any}, Any[Core.Const(1), Any])
        r < 0.35 && return Core.PartialStruct(FB, Tuple{Any,Int}, Any[Core.Const(rand(rng, 1:2)), Int])
        r < 0.45 && return Core.PartialStruct(FB, Two, Any[Core.Const(1), Union{Int,Nothing}])
        r < 0.55 && return Core.PartialStruct(FB, Some{Any}, Any[Union{Int,Nothing}])
        r < 0.65 && return Core.PartialStruct(FB, Tuple{Any,Any}, Any[Core.Const(nothing), Core.Const(:a)])
        r < 0.75 && return Core.PartialStruct(FB, Tuple{Integer,Vararg{Any}}, Any[Core.Const(1), Vararg{Any}])
        r < 0.85 && return Core.PartialStruct(FB, Tuple{Real,Real}, Any[Core.Const(1.5), Int])
        return Core.PartialStruct(FB, Half, Any[Core.Const(3)])
    catch
        return Tuple{Int,Int}
    end
end

function rand_arg(g::Gen; allow_va=true, nslots=5)
    rng = g.rng
    r = rand(rng)
    if r < 0.3
        return rand(rng) < 0.4 ? randunion(rng) : randtype(rng, 1)
    elseif r < 0.5
        return Core.Const(rand(rng, VALUES))
    elseif r < 0.62
        return rand_ps(rng)
    elseif r < 0.7
        f = rand(rng) < 0.6 ? randunion(rng, 2) : rand(rng, (Int, Core.Const(1), Any))
        v = rand(rng) < 0.5 ? Any : rand(rng, (Tuple{Any,Any}, Two, Some{Any}))
        return try CC.MustAlias(rand(rng, 1:nslots), rand(rng, 0:1), v, rand(rng, 1:2), f) catch; f end
    elseif r < 0.78
        return try CC.Conditional(rand(rng, 1:nslots), 0, rand(rng, (Int, Union{Int,Nothing}, Union{})),
                                  rand(rng, (Nothing, Union{Int,Missing}, Union{}))) catch; Bool end
    elseif r < 0.8
        return Core.InterConditional(rand(rng, 1:2), Int, Nothing)
    elseif r < 0.82
        return CC.LimitedAccuracy(rand(rng, (Int, Core.Const(1))), g.causes)
    elseif r < 0.84
        return Core.PartialTask(Int)
    elseif r < 0.9 || !allow_va
        return rand(rng, (Union{}, Any, Union{Int,Nothing}, Type{Int}, Core.Const(Int), Core.Const(nothing)))
    else
        T = rand(rng) < 0.6 ? randunion(rng, 2) : rand(rng, (Union{}, Int, Any))
        return rand(rng) < 0.85 ? Vararg{T} : Vararg{T, rand(rng, 0:2)}
    end
end

function rand_argtypes(g::Gen, k=rand(g.rng, 0:5); va=0.25)
    rng = g.rng
    ats = Any[rand_arg(g; allow_va=false) for _ in 1:k]
    if k >= 1 && rand(rng) < va
        T = rand(rng) < 0.5 ? leaftype(rng) : rand(rng, (Any, Union{Int,Nothing}, Union{}))
        ats[end] = Vararg{T}
    end
    return ats
end

# A lattice-equal copy that is often not `===` to `x`, or a near miss.
const UNION_TWINS = Any[(Tuple{Union{Int,Nothing}}, Union{Tuple{Int},Tuple{Nothing}}),
    (Tuple{Union{Int,Bool},Int}, Union{Tuple{Int,Int},Tuple{Bool,Int}}),
    (Union{Int,Nothing}, Union{Nothing,Int}), (Type{Int}, Type{Int}),
    (Vector{T} where T, Vector), (Tuple{Vararg{Int,2}}, Tuple{Int,Int})]
function twin(rng, @nospecialize(x))
    if x isa Core.PartialStruct
        fs = Any[rand(rng) < 0.9 ? twin(rng, f) : f for f in x.fields]
        return try Core.PartialStruct(FB, x.typ, copy(x.undefs), fs) catch; x end
    elseif x isa Core.Const
        rand(rng) < 0.1 && x.val isa Int && return Core.Const(x.val + 1)
        rand(rng) < 0.1 && return Core.typeof(x.val)
        return Core.Const(x.val)
    elseif x isa CC.Conditional
        return CC.Conditional(x.slot, x.ssadef, x.thentype, x.elsetype; isdefined=x.isdefined)
    elseif x isa Type
        for (a, b) in UNION_TWINS
            x === a && return b
            x === b && return a
        end
        rand(rng) < 0.08 && return Any
        return x
    end
    return x
end

# --- count_const_size tables ---------------------------------------------------------------------

const CONST_VALUES = Any[1, 1.5, 'c', 0x01, Int128(3), nothing, missing, :sym, "s", "", Int, Union{},
    Union{Int,Nothing}, Vector{T} where T, Vararg{Int}, Vararg, Vararg{Int,2}, TypeVar(:T),
    TypeVar(:S, Union{}, Integer), Int.name, Core.svec(), Core.svec(1), [1, 2], fill(1),
    Memory{Int}(undef, 2), Ref(1), MU(1), MC(1, :x), MC(1, "x"), MC(2, (1, 2)), MC0(), Main, Base,
    first(methods(sin)), (), (1,), (1, 2.0), ("a", 1), (:a, Int), Some(1), Some{Any}(1),
    Some{Any}("x"), Some(Some(1)), Two(1, 2), Two(nothing, "s"), Two(1, MC(1, 2)), PU(1), PU("x"),
    Wrap(Some{Any}(1), 2), Wrap(Some{Any}("x"), 1), Half(3), (a=1, b=:c), (a="s",), 1 => 2,
    1 => "s", ntuple(identity, 31), ntuple(identity, 32), ntuple(identity, 33), ntuple(identity, 40),
    (ntuple(identity, 30), 1), (ntuple(identity, 30), Some{Any}(1)), (ntuple(identity, 31), "s"),
    (Some{Any}(ntuple(identity, 31)),), Core.Const(1), Core.Const("x"), sin, CU(), Val(1),
    ((1, 2), (3, 4)), (Some{Any}(1), Some{Any}(2), Some{Any}(3)), (MC(1, 2), MC(3, 4)),
    (TypeVar(:T), 1), Some{Any}(TypeVar(:U)), (Main, 1)]

function rand_const(rng)
    r = rand(rng)
    r < 0.75 && return rand(rng, CONST_VALUES)
    # build a nested value
    a = rand(rng, CONST_VALUES); b = rand(rng, CONST_VALUES)
    r < 0.85 && return (a, b)
    r < 0.92 && return Some{Any}(a)
    r < 0.96 && return MC(rand(rng, 1:3), a)
    return Two(rand(rng, (1, nothing)), a)
end

function dt_row(s::Ser, @nospecialize(T::DataType))
    size = try sizeof(T) catch; return nothing end
    pf = try Base.datatype_pointerfree(T) catch; return nothing end
    nf = Int(CC.datatype_nfields(T))
    isptr = nf == 0 ? Bool[] : (try [CC.DataTypeFieldDesc(T)[i].isptr for i in 1:nf] catch; return nothing end)
    isc = [isconst(T, i) for i in 1:nf]
    jb(b) = b ? "true" : "false"
    return "[" * sval(s, T) * "," * string(size) * "," * jb(isbitstype(T)) * "," * jb(pf) * ",[" *
           join(jb.(isptr), ",") * "],[" * join(jb.(isc), ",") * "]]"
end

# Walk `x` and collect the layout facts of every type reached and the fields of every mutable
# object whose fields are all `const`.
function layout_json(s::Ser, @nospecialize(x))
    dts = IdDict{Any,String}(); heap = String[]; seen = IdDict{Any,Nothing}()
    function walk(@nospecialize(v), depth)
        depth > 6 && return
        T = typeof(v)
        if !haskey(dts, T)
            row = dt_row(s, T)
            row === nothing || (dts[T] = row)
        end
        v isa Type && return
        v isa Symbol && return
        v isa Module && return
        if ismutable(v)
            haskey(seen, v) && return
            seen[v] = nothing
            (v isa String || v isa Core.SimpleVector || v isa GenericMemory || v isa Method ||
             v isa Core.TypeName || v isa Core.CodeInstance) && return
            all(i -> isconst(T, i), 1:nfields(v)) || return
            fs = String[]
            for i in 1:nfields(v)
                if isdefined(v, i)
                    f = getfield(v, i)
                    push!(fs, sval(s, f)); walk(f, depth + 1)
                else
                    push!(fs, "null")
                end
            end
            v isa TypeVar || push!(heap, "[" * string(LatticeSer.objid!(s, v)) * ",[" * join(fs, ",") * "]]")
            return
        end
        for i in 1:nfields(v)
            isdefined(v, i) && walk(getfield(v, i), depth + 1)
        end
    end
    walk(x, 0)
    return "{\"dts\":[" * join(values(dts), ",") * "],\"heap\":[" * join(heap, ",") * "]}"
end

function rand_effects(rng)
    rand(rng) < 0.35 && return CC.EFFECTS_TOTAL
    r = rand(rng)
    if r < 0.4
        # one field away from total
        e = CC.EFFECTS_TOTAL
        k = rand(rng, 1:9)
        return k == 1 ? CC.Effects(e; consistent=rand(rng, (0x01, 0x02, 0x04))) :
               k == 2 ? CC.Effects(e; effect_free=rand(rng, (0x01, 0x02, 0x03))) :
               k == 3 ? CC.Effects(e; nothrow=false) :
               k == 4 ? CC.Effects(e; terminates=false) :
               k == 5 ? CC.Effects(e; noub=rand(rng, (0x01, 0x02))) :
               k == 6 ? CC.Effects(e; nortcall=false) :
               k == 7 ? CC.Effects(e; notaskstate=false) :
               k == 8 ? CC.Effects(e; inaccessiblememonly=rand(rng, (0x01, 0x02))) :
                        CC.Effects(e; nonoverlayed=rand(rng, (0x01, 0x02)))
    end
    return CC.Effects(; consistent=rand(rng, (0x00, 0x01, 0x02, 0x04, 0x06)),
        effect_free=rand(rng, (0x00, 0x01, 0x02, 0x03)), reset_safe=rand(rng, (0x00, 0x01, 0x02)),
        nothrow=rand(rng, Bool), terminates=rand(rng, Bool), notaskstate=rand(rng, Bool),
        inaccessiblememonly=rand(rng, (0x00, 0x01, 0x02)), noub=rand(rng, (0x00, 0x01, 0x02)),
        nonoverlayed=rand(rng, (0x00, 0x01, 0x02)), nortcall=rand(rng, Bool))
end

# --- encoders ------------------------------------------------------------------------------------

jb(b::Bool) = b ? "true" : "false"
selts(s, xs) = "[" * join([selt(s, x) for x in xs], ",") * "]"

# Fail on `#undef` slots the way reading them would.
function checked(v::Vector{Any})
    for i in eachindex(v)
        isassigned(v, i) || throw(UndefRefError())
    end
    return v
end

# --- the const-prop cache -------------------------------------------------------------------------

function wr_json(w::CC.WorldRange)
    return "[" * string(first(w)) * "," * string(last(w)) * "]"
end

function build_cache(g::Gen, s::Ser, W::UInt)
    rng = g.rng
    cache = CC.InferenceCache()
    entries = String[]
    keys_ = Vector{Any}[]
    worlds = UInt[]
    for _ in 1:rand(rng, 0:5)
        mi = rand(rng) < 0.8 ? MI_VA : MI_FIX
        at = rand(rng) < 0.5 ? CC.most_general_argtypes(mi.def, mi.specTypes) : rand_argtypes(g, rand(rng, 2:4); va=0.3)
        if !isempty(at) && rand(rng) < 0.7
            at = Any[rand(rng) < 0.5 ? rand_arg(g; allow_va=false) : a for a in at]
            at[end] isa Core.TypeofVararg || (rand(rng) < 0.2 && (at[end] = Vararg{Any}))
        end
        # A varargs `mi` is also const-propagated at fixed arities: expand the tail.
        if !isempty(at) && at[end] isa Core.TypeofVararg && rand(rng) < 0.6
            T = Base.unwrapva(at[end])
            at = Any[at[1:end-1]..., (rand(rng) < 0.5 ? Core.Const(1) : T for _ in 1:rand(rng, 0:2))...]
        end
        # Mostly the flags `const_prop_call` would compute (overridden where the key holds
        # forwardable information), sometimes random, sometimes `nothing` or one short.
        ov = rand(rng) < 0.12 ? nothing :
             rand(rng) < 0.6 ? BitVector([CC.is_forwardable_argtype(LATTICES[1][2], a) || a isa Core.TypeofVararg for a in at]) :
             BitVector([rand(rng) < 0.5 for _ in 1:(rand(rng) < 0.92 ? length(at) : max(length(at) - 1, 0))])
        res = CC.InferenceResult(mi, at, ov)
        loc = rand(rng) < 0.6
        pw = CC.WorldRange(UInt(0), UInt(0))
        if loc
            w = rand(rng, (W - 2):W)
            a = rand(rng, (W - 3):w); b = rand(rng, w:W)
            pw = CC.WorldRange(a, b)
            res.result = Int
            rand(rng) < 0.5 && (res.valid_worlds = CC.WorldRange(rand(rng, (W - 3):W), rand(rng, W:(W + 2))))
            entry = CC.LocalInferenceResult(res, CC.LocalInferenceProof(pw, Core.svec()), w)
        else
            res.tombstone = rand(rng) < 0.6
            res.cache_world = rand(rng, (UInt(0), W - 1, W, W))
            res.valid_worlds = rand(rng) < 0.3 ? CC.WorldRange() :
                               CC.WorldRange(rand(rng, (W - 3):W), rand(rng, (W - 1):(W + 2)))
            entry = res
        end
        push!(cache, entry)
        push!(keys_, at)
        push!(worlds, res.cache_world)
        push!(entries, "{\"mi\":" * string(mi === MI_VA ? 1 : 2) * ",\"loc\":" * jb(loc) *
              ",\"pw\":" * wr_json(pw) * ",\"cw\":" * string(res.cache_world) *
              ",\"rw\":" * wr_json(res.valid_worlds) * ",\"at\":" * selts(s, at) *
              ",\"ov\":" * (ov === nothing ? "null" : "[" * join(jb.(collect(ov)), ",") * "]") *
              ",\"tomb\":" * jb(res.tombstone) * "}")
    end
    return cache, entries, keys_, worlds
end

# --- cases ---------------------------------------------------------------------------------------

function gen_case(g::Gen, s::Ser, id::Int, io::IO, W::UInt)
    rng = g.rng
    r = rand(rng)
    lname = "typeinf"
    if r < 0.17
        op = "cr.mostGeneral"
        spec = randspec(rng)
        m = randnargs(rng, spec)
        args = [m === nothing ? "null" : string(Int(m.nargs)), sval(s, spec)]
        exp = expected(s, :elts, () -> checked(CC.most_general_argtypes(m, spec)))
    elseif r < 0.23
        op = "cr.nospecInfer"
        m = rand(rng, NSI_METHODS)
        c = rand_argtypes(g, rand(rng, 0:6))
        a = rand(rng) < 0.9 ? Any[rand(rng) < 0.5 ? twin(rng, x) : rand_arg(g) for x in c] : rand_argtypes(g)
        rand(rng) < 0.3 && length(a) < 7 && push!(a, rand_arg(g))
        args = [jb(m.nospecializeinfer), string(Int(m.nospecialize)), string(Int(m.nargs)),
                selts(s, a), selts(s, c)]
        exp = expected(s, :elts, () -> checked(CC.get_nospecializeinfer_argtypes(a, c, m)))
    elseif r < 0.43
        op = "cr.matchSimple"
        lname, L = pick_lattice(rng)
        c = rand(rng) < 0.6 ? (try CC.most_general_argtypes(rand(rng, POOL_METHODS), randspec(rng)) catch; Any[] end) :
            rand_argtypes(g)
        any(i -> !isassigned(c, i), eachindex(c)) && (c = Any[Int])
        k = length(c)
        rr = rand(rng)
        given = if rr < 0.55
            Any[rand(rng) < 0.5 ? twin(rng, x) : rand_arg(g; allow_va=false) for x in c]
        else
            rand_argtypes(g, max(0, k + rand(rng, -2:2)); va=0.35)
        end
        if !isempty(given) && rand(rng) < 0.2
            given[end] = Vararg{rand(rng, (Int, Any, Union{Int,Nothing}))}
        end
        if rand(rng) < 0.3
            # The key `const_prop_call` builds, its `overridden_by_const` flags, and a lookup of
            # that key in a cache holding only the result stored under it. The result is
            # `found + 2 * (flags as bits)`.
            op = "cr.rehit"
            args = [selts(s, given), selts(s, c), string(W)]
            exp = expected(s, :val, () -> begin
                key = checked(CC.matching_cache_argtypes(L, MI_ANY, CC.SimpleArgtypes(copy(given)), copy(c)))
                ov = BitVector([key[i] !== CC.argtype_by_index(c, i) for i in 1:length(key)])
                cache = CC.InferenceCache()
                res = CC.InferenceResult(MI_VA, key, ov)
                res.cache_world = W
                res.valid_worlds = CC.WorldRange(W, W)
                push!(cache, res)
                hit = CC.constprop_cache_lookup(L, MI_VA, key, cache, W)
                code = hit === nothing ? 0 : hit === missing ? 2 : hit === res ? 1 : 3
                code + 4 * sum((Int(ov[i]) << (i - 1) for i in eachindex(ov)); init=0)
            end)
        else
            args = [selts(s, given), selts(s, c)]
            exp = expected(s, :elts, () -> checked(CC.matching_cache_argtypes(L, MI_ANY,
                CC.SimpleArgtypes(copy(given)), copy(c))))
        end
    elseif r < 0.5
        op = "cr.isArgtypeMatch"
        lname, L = pick_lattice(rng)
        a = rand_arg(g)
        b = rand(rng) < 0.6 ? twin(rng, a) : rand_arg(g)
        o = rand(rng, Bool)
        args = [selt(s, a), selt(s, b), jb(o)]
        exp = expected(s, :bool, () -> CC.is_argtype_match(L, a, b, o))
    elseif r < 0.62
        op = "cr.vaProcess"
        lname, L = pick_lattice(rng)
        nargs = rand(rng, 0:5)
        isva = rand(rng) < 0.6
        given = rand_argtypes(g, rand(rng) < 0.7 ? max(0, nargs + rand(rng, -2:2)) : rand(rng, 0:6); va=0.3)
        args = [selts(s, given), string(nargs), jb(isva)]
        lastva = !isempty(given) && Base.isvarargtype(given[end])
        quiet = !(isva || lastva) && length(given) != nargs
        exp = expected(s, :elts, () -> checked(quiet ?
            redirect_stdout(() -> CC.va_process_argtypes(L, copy(given), UInt(nargs), isva, MI_ANY), devnull) :
            CC.va_process_argtypes(L, copy(given), UInt(nargs), isva, MI_ANY)))
    elseif r < 0.77
        op = "cr.lookup"
        lname, L = pick_lattice(rng)
        cache, entries, keys_, cws = build_cache(g, s, W)
        mi = rand(rng) < 0.85 ? MI_VA : MI_FIX
        # Mostly a near copy of one entry's key, asked at that entry's world.
        j = isempty(keys_) ? 0 : rand(rng, 1:length(keys_))
        given = if j > 0 && rand(rng) < 0.75
            Any[rand(rng) < 0.9 ? twin(rng, x) : rand_arg(g) for x in keys_[j]]
        else
            rand_argtypes(g, rand(rng, 1:4))
        end
        world = j > 0 && rand(rng) < 0.7 ? cws[j] :
                rand(rng) < 0.85 ? rand(rng, (W - 1, W, W)) : rand(rng, (UInt(0), W - 3, W + 1))
        args = [string(mi === MI_VA ? 1 : 2), jb(mi === MI_VA), selts(s, given),
                "[" * join(entries, ",") * "]", string(world)]
        # The entry's position in `cache.results`, 0 for `nothing`, -1 for `missing`.
        exp = expected(s, :val, () -> begin
            res = CC.constprop_cache_lookup(L, mi, given, cache, world)
            res === nothing ? 0 : res === missing ? -1 : findfirst(x -> x === res, cache.results)::Int
        end)
    elseif r < 0.86
        x = rand_const(rng)
        lay = layout_json(s, x)
        if rand(rng) < 0.6
            op = "cr.countConstSize"
            cs = rand(rng) < 0.8
            args = [sval(s, x), jb(cs), lay]
            exp = expected(s, :val, () -> CC.count_const_size(x, cs))
        else
            op = "cr.isInlineableConstant"
            args = [sval(s, x), lay]
            exp = expected(s, :bool, () -> CC.is_inlineable_constant(x))
        end
    elseif r < 0.94
        op = "cr.constabi"
        rt = rand(rng) < 0.75 ? Core.Const(rand_const(rng)) : rand_arg(g)
        rt isa Core.TypeofVararg && (rt = Int)
        eff = CC.decode_effects(CC.encode_effects(rand_effects(rng)))
        lay = rt isa Core.Const ? layout_json(s, rt.val) : "{\"dts\":[],\"heap\":[]}"
        md = rand(rng) < 0.5 ? nothing : rand(rng, Bool)
        args = [selt(s, rt), string(CC.encode_effects(eff)), lay, md === nothing ? "null" : jb(md)]
        res = CC.InferenceResult(MI_ANY, Any[], nothing)
        res.result = rt
        res.ipo_effects = eff
        exp = expected(s, :bool, () -> md === nothing ? CC.is_result_constabi_eligible(res) :
                                       CC.result_is_constabi(CRInterp(md, false, false), res))
    elseif r < 0.97
        op = "cr.discard"
        d, k = rand(rng, Bool), rand(rng) < 0.3
        cost = rand(rng) < 0.5 ? CC.MAX_INLINE_COST : rand(rng, (UInt16(0), UInt16(10), UInt16(100), CC.MAX_INLINE_COST - 0x1))
        mi = rand(rng, (MI_VA, MI_FIX))
        args = [jb(d), jb(k), "false", jb(CC.isa_compileable_sig(mi)), string(Int(cost))]
        exp = expected(s, :bool, () -> CC.discard_optimized_result(CRInterp(d, k, false), mi, cost))
    else
        op = "cr.compress"
        d, k, c = rand(rng, Bool), rand(rng) < 0.3, rand(rng, Bool)
        inl = rand(rng, Bool)
        mi = rand(rng, (MI_VA, MI_FIX))
        ci = copy(Base.code_lowered(mi.def === MI_VA.def ? fv2 : f2)[1])
        CC.set_inlineable!(ci, inl)
        args = [jb(mi.def isa Method), jb(d), jb(CC.is_inlineable(ci)), jb(k), "false", jb(c),
                jb(CC.isa_compileable_sig(mi))]
        exp = expected(s, :val, () -> begin
            out = CC.maybe_compress_codeinfo(CRInterp(d, k, c), mi, ci)
            out === nothing ? 0 : out === ci ? 1 : out isa String ? 2 : 3
        end)
    end
    write_case(io, s, id, op, lname, args, exp)
    return op
end

function main(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    g = Gen(rng); s = Ser()
    W = Base.get_world_counter()
    dir = mktempdir()
    casefile = joinpath(dir, "cases.jsonl")
    ops = Dict{Int,String}()
    open(casefile, "w") do io
        for id in 1:n
            ops[id] = gen_case(g, s, id, io, W)
        end
    end
    errs = Dict{String,Dict{String,Int}}()
    for line in eachline(casefile)
        m = match(r"^\{\"id\":\"?(\d+)\"?.*\"exp\":\{\"err\":\"(\w+)\"", line)
        m === nothing && continue
        d = get!(errs, ops[parse(Int, m[1])], Dict{String,Int}())
        d[m[2]] = get(d, m[2], 0) + 1
    end
    # Outcome spread of the cases whose result is a small code: lookup position (> 0 found,
    # 0 nothing, -1 missing) and count_const_size at, under or over the limit.
    spread = Dict{String,Int}()
    for line in eachline(casefile)
        m = match(r"\"op\":\"(cr\.lookup|cr\.countConstSize|cr\.rehit)\".*\"exp\":\{\"val\":\{\"long\":(-?\d+)\}", line)
        m === nothing && continue
        k = parse(Int, m[2])
        key = m[1] == "cr.lookup" ? (k > 0 ? "lookup:found" : k == 0 ? "lookup:nothing" : "lookup:missing") :
              m[1] == "cr.rehit" ? (k < 4 ? "rehit:no-flag" : k % 4 == 1 ? "rehit:flagged-found" : "rehit:flagged-missed") :
              (k > 256 ? "size:over" : k == 256 ? "size:at-limit" : "size:under")
        spread[key] = get(spread, key, 0) + 1
    end
    println("SPREAD ", sort(collect(spread)))
    if haskey(opts, "dump")
        cp(casefile, opts["dump"]; force=true)
        println("WROTE $n cases to $(opts["dump"])")
        return 0
    end
    out = read(pipeline(`$(opts["exe"])`, stdin=casefile), String)
    agree = 0; unmodelled = 0; bad = String[]; seen = 0; unm = String[]
    perop = Dict{String,Vector{Int}}()
    for line in split(out, '\n'; keepempty=false)
        m = match(r"\"id\":(\d+)", line)
        if m === nothing
            push!(bad, line); continue
        end
        id = parse(Int, m[1]); seen += 1
        st = get!(perop, ops[id], [0, 0, 0])
        if occursin("\"agree\":true", line)
            agree += 1; st[1] += 1
        elseif occursin("\"unmodelled\":true", line)
            unmodelled += 1; st[2] += 1; push!(unm, line)
        else
            push!(bad, line); st[3] += 1
        end
    end
    for (op, st) in sort(collect(perop))
        println(rpad(op, 26), " agree=", st[1], " unmodelled=", st[2], " disagree=", st[3],
                " julia-errors=", get(errs, op, Dict{String,Int}()))
    end
    for line in first(bad, parse(Int, opts["show"]))
        println("DISAGREE ", first(line, 1500))
    end
    for line in first(unm, 5)
        println("UNMODELLED ", first(line, 600))
    end
    println("SEED $seed CASES $n ANSWERED $seen UNMODELLED $unmodelled")
    println("AGREE $agree/$(seen - unmodelled)")
    rm(dir; recursive=true)
    return isempty(bad) && seen == n ? 0 : 1
end

exit(main())
