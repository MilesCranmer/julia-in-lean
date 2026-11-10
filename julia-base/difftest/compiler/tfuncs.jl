# Differential test of the Lean model of Compiler/src/tfuncs.jl (JuliaLean/Compiler/src/tfuncs.lean)
# against the pinned Julia (f755f49a9e41380d7da126b3c1db9fe7f83dd027), plus a soundness smoke test
# that calls the builtins on sampled values.
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA difftest/compiler/tfuncs.jl --cases 20000 --seed 1
#
# Each generated call picks a modelled builtin (`throw`, `Core.ifelse`, `===`, `isdefined`,
# `nfields`, `svec`, `typeof`, `has_free_typevars`, `typeassert`, `isa`, `<:`, `getfield`,
# `tuple`) and argument lattice elements, biased to the edge cases: `Union{}`, `Any`, `Type`,
# `Type{Union{}}`, `Core.TypeEgal{T}` vs `Type{T}`, `Type{<:T}`, kinds, `UnionAll`s, `Union`s,
# `Vararg` tails (so `builtin_tfunction` pads or drops arguments), wrong argument counts,
# `Const`s of types, modules and structs with undefined fields, `PartialStruct`s with undefined
# fields, `Conditional`, `MustAlias` and `LimitedAccuracy` wrappers, and field names that are
# out of range, of the wrong type, or not constant. It writes three kinds of case:
#   tf.builtin    Compiler.builtin_tfunction(NativeInterpreter(), f, argtypes, nothing)
#   tf.nothrow    Compiler.builtin_nothrow(𝕃, f, argtypes, rt) with rt the result above
#   tf.instanceof Compiler.instanceof_tfunc(t, astag)
# and compares each with `compilerdiff`. Prints `AGREE k/n`; cases the model reports as
# `unmodelled` are counted separately and are not agreement.
#
# Soundness smoke test (always on): for each tf.builtin case whose arguments it can sample, it
# draws concrete argument tuples from the concretization of the argument elements, calls the
# builtin, and checks that the call either throws or returns a value in the concretization of
# the result, that a `Union{}` result always throws, and that `builtin_nothrow = true` calls do
# not throw. Prints `SOUND checked=<k> violations=<v>` and the first violations.
#
# Comparison: results agree up to a renaming of TypeVars, with each UnionAll's variable scoped
# to its body (`agreeScoped` in CompilerDiff.lean). Compiled code sometimes returns a `Union`
# whose `Type` arm has a fresh copy of `Type`'s variable, where the interpreter (and the C model
# of `jl_type_union`) return `Type` itself; the two are the same type but not `===`.
#
# Runs (seed, cases, agreement), 2026-11-09, compilerdiff at this commit's model, pinned Julia
# 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 20000 cases: AGREE 19937/19937, 63 unmodelled; SOUND checked=11295 violations=13
#   seed 2, 20000 cases: AGREE 19936/19936, 64 unmodelled; SOUND checked=11271 violations=17
#   seed 3, 20000 cases: AGREE 19954/19954, 46 unmodelled; SOUND checked=11319 violations=9
#   Total 59827/59827 agreement on the 60000 cases; the 173 unmodelled cases are `Const`s
#   of type objects or mutable objects whose fields `Val` does not record (getfield,
#   isdefined), and one `Const(sv.name)` TypeName result.
#   Every soundness violation is one of three bugs: bugs/compiler-tfuncs-tuple-vararg-type,
#   bugs/compiler-tfuncs-vararg-optional-arg-bottom, bugs/compiler-tfuncs-subtype-bottom-lhs.
#   Rerun after the proof pass refactored builtin_tfunction (builtinFold, builtinArgs),
#   tuple_tfunc (tupleTfuncParams) and builtinRT (getfield on tuples): the same three seeds
#   give the same numbers, 59827/59827.
#   Rerun after the review fixes added the dispatch-only builtins (`TF_DISPATCH_ONLY`, about 3%
#   of cases) and factored the `Vararg{Union{}}` drop out of tuple_tfunc, which changes the
#   generated cases:
#   seed 1, 20000 cases: AGREE 19947/19947, 53 unmodelled; SOUND checked=10944 violations=11
#   seed 2, 20000 cases: AGREE 19933/19933, 67 unmodelled; SOUND checked=10995 violations=25
#   seed 3, 20000 cases: AGREE 19955/19955, 45 unmodelled; SOUND checked=11064 violations=7
#   Total 59835/59835; the unmodelled cases are the same kinds as above plus 6
#   `current_scope_tfunc` cases. The violations are again only the tuple-vararg-type and
#   subtype-bottom-lhs bugs.

include(joinpath(@__DIR__, "common.jl"))
using .LatticeSer
using Random

struct HalfInit          # an immutable struct whose second field may be left undefined
    a::Int
    b::Any
    HalfInit(a) = new(a)
    HalfInit(a, b) = new(a, b)
end

struct Pt{T}
    x::T
    y::T
end

mutable struct MC        # a mutable struct with a const field and a field that may be undefined
    const a::Int
    b::Any
    MC(a) = new(a)
    MC(a, b) = new(a, b)
end

mutable struct MB
    x::Int
end

struct Wrap{T<:Integer}
    v::T
end

const TF_FREE_T = TypeVar(:T, Integer)

const TF_TYPES = Any[
    Any, Union{}, Int, Int8, Bool, Float64, Nothing, Symbol, Integer, Real, Signed,
    Some{Int}, Some{Any}, Some{Union{Int,Nothing}}, Pair{Int,Symbol}, Complex{Int},
    Tuple{}, Tuple{Int}, Tuple{Int,Symbol}, Tuple{Vararg{Int}}, NTuple{2,Int}, Tuple{Int,Vararg{Any}},
    Tuple{Any}, Tuple{Bool,Bool}, Tuple{Nothing}, Tuple{Int,Vararg{Int,2}},
    Union{Int,Nothing}, Union{Int,Symbol}, Union{Bool,Nothing}, Union{Pt{Int},Some{Int}},
    Union{HalfInit,Tuple{Int}}, Union{Int,Type{Int}},
    Type, Type{Int}, Type{Union{}}, Core.TypeEgal{Int}, Core.TypeEgal{Any}, Type{<:Integer},
    Type{Vector{Int}}, Type{Tuple{Int}}, Type{Union{Int,Nothing}}, Core.TypeEgal{Union{}},
    Type{Some{T}} where T, Type{T} where T<:Integer, Core.TypeEgal{Pt{Int}}, Type{Pt},
    DataType, UnionAll, Union, TypeVar, Core.TypeofBottom, Core.TypeEq, Core.TypeEgal,
    Vector{Int}, Base.RefValue{Int}, Ref{Int}, Val{1}, Val{:a},
    Some{T} where T, Some{<:Integer}, Tuple{T,T} where T, Tuple{T,Vararg{T}} where T,
    NTuple{N,Int} where N, Tuple{Vararg{T,N}} where {T,N},
    Pt{T} where T, Pt{Int}, Pt{Any}, Pt{<:Real}, Wrap, Wrap{Int}, Wrap{T} where T<:Signed,
    HalfInit, MC, MB, Module, Task, Function, typeof(sin), Missing,
    TF_FREE_T, Pt{TF_FREE_T}, Type{TF_FREE_T},
]

const TF_VALUES = Any[
    1, 0, -1, 2, 3, true, false, nothing, :a, :b, :x, :y, :v, (), (1,), (1, :a), (nothing, true),
    (1, 2), (1, 2, 3), (Int, 1), (true,), Some(1), Some(nothing), Some(:a), Some(Int),
    Pair(1, :a), Complex(1, 2), Pt(1, 2), Pt{Any}(1, :a), Wrap(Int8(1)), Wrap(1),
    HalfInit(1), HalfInit(1, :x), HalfInit(2, nothing), MB(1), MC(1), MC(2, :b),
    Int, Union{}, Any, Bool, Nothing, Integer, Vector{Int}, Some{T} where T, Type{Int},
    Tuple{Int}, Union{Int,Nothing}, Pt, Pt{Int}, Tuple{Vararg{Int}}, NTuple{N,Any} where N,
    Core.TypeEgal{Int}, DataType, Core, Main, sin, missing, 1.5, 0x01, Int8(3), TypeVar(:Q),
    TF_FREE_T,
]

const TF_NAMES = Any[
    Core.Const(1), Core.Const(2), Core.Const(3), Core.Const(0), Core.Const(-1), Core.Const(4),
    Core.Const(:a), Core.Const(:b), Core.Const(:x), Core.Const(:y), Core.Const(:v), Core.Const(:z),
    Core.Const(:name), Core.Const(:super), Core.Const(:types), Core.Const(:parameters),
    Core.Const(true), Core.Const(1.0), Core.Const(Int8(1)), Core.Const(nothing),
    Int, Symbol, Bool, Union{Int,Symbol}, Any, Integer, Union{}, Int8,
]

const TF_BUILTINS = [
    (getfield, "getfield", 2, 4, 0.24), (isdefined, "isdefined", 2, 3, 0.09),
    (isa, "isa", 2, 2, 0.09), ((<:), "<:", 2, 2, 0.07), (typeassert, "typeassert", 2, 2, 0.08),
    ((===), "===", 2, 2, 0.08), (typeof, "typeof", 1, 1, 0.07), (nfields, "nfields", 1, 1, 0.05),
    (Core.ifelse, "ifelse", 3, 3, 0.05), (tuple, "tuple", 0, 4, 0.08),
    (Core.has_free_typevars, "has_free_typevars", 1, 1, 0.04), (Core.svec, "svec", 0, 3, 0.03),
    (throw, "throw", 1, 1, 0.03),
]

# Builtins whose `builtin_tfunction` dispatch is modelled but not their tfunc: those without an
# `add_tfunc` entry (`Any`), and `Core.current_scope` (its argument check). Only `tf.builtin`
# cases are written for them; they are never called.
const TF_DISPATCH_ONLY = Any[(getfield(Core, n), string(n)) for n in
    (:_abstracttype, :_apply_iterate, :_call_in_world, :_call_in_world_total, :_call_latest,
     :_compute_sparams, :_equiv_typedef, :_import, :_new_cancel_source, :_primitivetype,
     :_setsuper!, :_structtype, :_task, :_typebody!, :_using, :cancellation_point!,
     :declare_const, :declare_global, :define_method, :invoke, :invoke_in_world,
     :invokelatest, :isdefinedglobal, :current_scope)]

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

randtype(rng, depth=2) = begin
    r = rand(rng)
    if depth <= 0 || r < 0.6
        rand(rng, TF_TYPES)
    elseif r < 0.72
        a = randtype(rng, depth - 1); b = randtype(rng, depth - 1)
        try Union{a, b} catch; Any end
    elseif r < 0.84
        k = rand(rng, 0:3)
        ps = Any[randtype(rng, depth - 1) for _ in 1:k]
        if k > 0 && rand(rng) < 0.3
            ps[end] = rand(rng) < 0.7 ? Vararg{ps[end]} : Vararg{ps[end], rand(rng, 0:2)}
        end
        try Tuple{ps...} catch; Tuple{} end
    elseif r < 0.92
        t = randtype(rng, depth - 1)
        try (rand(rng) < 0.6 ? Type{t} : Core.TypeEgal{t}) catch; Type end
    else
        t = randtype(rng, depth - 1)
        try Some{t} catch; Some{Any} end
    end
end

mutable struct Gen
    rng::Random.AbstractRNG
    states::Vector{Any}
end

function Gen(rng)
    IS = CC.InferenceState{CC.NativeInterpreter}
    Gen(rng, Any[ccall(:jl_new_struct_uninit, Any, (Any,), IS) for _ in 1:2])
end

function fresh_causes(g::Gen)
    c = fieldtype(CC.LimitedAccuracy, :causes)()
    push!(c, rand(g.rng, g.states))
    c
end

function partial_struct(g::Gen, depth)
    rng = g.rng
    for _ in 1:10
        typ = rand(rng, (Some{Int}, Some{Any}, Pair{Int,Symbol}, Pair{Any,Any}, Pt{Int}, Pt{Any},
            HalfInit, MC, Tuple{Int,Symbol}, Tuple{Any,Any}, Tuple{Int,Vararg{Int}}, Tuple{Any},
            Tuple{Int,Int}, Tuple{Nothing,Any}, Tuple{Bool,Vararg{Any}}, Base.RefValue{Any},
            Wrap{Int}, Tuple{Type{Int},Any}))
        isva = Base.isvatuple(typ)
        n = isva ? length(typ.parameters) : fieldcount(typ)
        fields = Any[]
        for i in 1:n
            ft = isva && i == n ? typ.parameters[i] : fieldtype(typ, i)
            r = rand(rng)
            if isva && i == n
                push!(fields, ft)
            elseif r < 0.3
                push!(fields, ft)
            elseif r < 0.4
                push!(fields, Union{})
            else
                push!(fields, simple_elt(g, depth))
            end
        end
        try
            if rand(rng) < 0.75
                return Core.PartialStruct(CC.fallback_lattice, typ, fields)
            else
                undefs = Union{Nothing,Bool}[rand(rng, (nothing, true, false)) for _ in 1:n]
                isva && (undefs[end] = nothing)
                for i in 1:n
                    fields[i] === Union{} && (undefs[i] = true)
                end
                return Core._PartialStruct(typ, undefs, fields)
            end
        catch
        end
    end
    return Core.PartialStruct(CC.fallback_lattice, Tuple{Int,Int}, Any[Core.Const(1), Int])
end

function simple_elt(g::Gen, depth)
    rng = g.rng
    r = rand(rng)
    if depth <= 0 || r < 0.42
        return randtype(rng, depth)
    elseif r < 0.75
        return Core.Const(rand(rng, TF_VALUES))
    elseif r < 0.93
        return partial_struct(g, depth - 1)
    elseif r < 0.96
        return CC.PartialTypeVar(rand(rng, (TF_FREE_T, TypeVar(:R, Int))), rand(rng, Bool), rand(rng, Bool))
    else
        return Core.PartialTask(simple_elt(g, depth - 1))
    end
end

function rand_elt(g::Gen, depth=2)
    rng = g.rng
    r = rand(rng)
    if r < 0.8
        return simple_elt(g, depth)
    elseif r < 0.88
        return try
            CC.Conditional(rand(rng, 1:2), 0, simple_elt(g, depth - 1), simple_elt(g, depth - 1))
        catch; Bool end
    elseif r < 0.96
        return try
            CC.MustAlias(rand(rng, 1:2), 0, simple_elt(g, depth - 1), rand(rng, 1:2), simple_elt(g, depth - 1))
        catch; Any end
    else
        typ = simple_elt(g, depth - 1)
        return CC.LimitedAccuracy(typ, fresh_causes(g))
    end
end

# An argument suited to position `i` of builtin `name`, or a random element.
function arg_for(g::Gen, name, i)
    rng = g.rng
    rand(rng) < 0.25 && return rand_elt(g)
    if name in ("getfield", "isdefined") && i == 2
        return rand(rng) < 0.85 ? rand(rng, TF_NAMES) : rand_elt(g, 1)
    elseif name == "getfield" && i == 3
        return rand(rng, Any[Core.Const(true), Core.Const(false), Bool, Core.Const(:not_atomic),
                             Core.Const(:monotonic), Symbol, Any, Int, Core.Const(1)])
    elseif name == "getfield" && i == 4
        return rand(rng, Any[Core.Const(true), Core.Const(false), Bool, Any, Int, Symbol])
    elseif name == "isdefined" && i == 3
        return rand(rng, Any[Core.Const(:not_atomic), Core.Const(:unordered), Symbol, Int, Any])
    elseif name in ("isa", "typeassert") && i == 2
        r = rand(rng)
        return r < 0.4 ? Core.Const(rand(rng, TF_TYPES)) : r < 0.85 ? (try Type{randtype(rng, 1)} catch; Type end) :
               rand_elt(g, 1)
    elseif name == "<:"
        r = rand(rng)
        return r < 0.4 ? Core.Const(rand(rng, TF_TYPES)) : r < 0.85 ? (try Type{randtype(rng, 1)} catch; Type end) :
               rand_elt(g, 1)
    elseif name == "ifelse" && i == 1
        return rand(rng, Any[Bool, Core.Const(true), Core.Const(false), Any, Int, Core.Const(1),
                             Union{Bool,Nothing}, rand_elt(g, 1)])
    end
    return rand_elt(g)
end

function gen_call(g::Gen)
    rng = g.rng
    ws = cumsum([b[5] for b in TF_BUILTINS]); ws = ws ./ ws[end]
    k = findfirst(>=(rand(rng)), ws)
    f, name, lo, hi = TF_BUILTINS[k]
    r = rand(rng)
    na = r < 0.85 ? rand(rng, lo:hi) : max(0, rand(rng, (lo - 1, hi + 1)))
    args = Any[arg_for(g, name, i) for i in 1:na]
    if rand(rng) < 0.12
        T = rand(rng) < 0.5 ? (na >= 1 ? (try CC.widenconst(CC.ignorelimited(CC.widenslotwrapper(args[end]))) catch; Any end) : Any) :
            rand(rng, Any[Int, Any, Symbol, Bool, Union{}, Core.Const, Type{Int}, Core.TypeEgal{Int}, DataType])
        va = try
            rand(rng) < 0.75 ? Vararg{T} : Vararg{T, rand(rng, 0:2)}
        catch
            Vararg{Any}
        end
        na >= 1 && rand(rng) < 0.5 && pop!(args)
        push!(args, va)
    end
    return f, name, args
end

# --- universe extras: struct field types and type-name facts --------------------------------

mutable struct Extra
    structs_seen::IdDict{Any,Nothing}
    tns_seen::Set{String}
end
Extra() = Extra(IdDict{Any,Nothing}(), Set{String}())

const KIND_TYPES = Any[DataType, UnionAll, Union, Core.TypeofBottom, TypeVar, Core.TypeEq,
                       Core.TypeEgal, Module, Task, Core.TypeofVararg, Symbol]

function collect_types!(acc, @nospecialize(x), depth=0)
    depth > 4 && return
    if x isa Core.Const
        push!(acc, typeof(x.val))
        x.val isa Type && collect_types!(acc, x.val, depth + 1)
        if !(x.val isa Type) && !(x.val isa Module) && !ismutable(x.val)
            for i in 1:nfields(x.val)
                isdefined(x.val, i) && collect_types!(acc, Core.Const(getfield(x.val, i)), depth + 1)
            end
        end
    elseif x isa Core.PartialStruct
        collect_types!(acc, x.typ, depth + 1)
        foreach(f -> collect_types!(acc, f, depth + 1), x.fields)
    elseif x isa CC.Conditional || x isa Core.InterConditional
        collect_types!(acc, x.thentype, depth + 1); collect_types!(acc, x.elsetype, depth + 1)
    elseif x isa CC.MustAlias || x isa Core.InterMustAlias
        collect_types!(acc, x.vartyp, depth + 1); collect_types!(acc, x.fldtyp, depth + 1)
    elseif x isa CC.LimitedAccuracy
        collect_types!(acc, x.typ, depth + 1)
    elseif x isa Core.PartialTask
        push!(acc, Task); collect_types!(acc, x.fetch_type, depth + 1)
    elseif x isa CC.PartialTypeVar
        push!(acc, TypeVar)
    elseif x isa UnionAll
        collect_types!(acc, x.var.ub, depth + 1); collect_types!(acc, x.body, depth + 1)
    elseif x isa Union
        collect_types!(acc, x.a, depth + 1); collect_types!(acc, x.b, depth + 1)
    elseif x isa TypeVar
        collect_types!(acc, x.ub, depth + 1)
    elseif x isa Core.TypeofVararg
        isdefined(x, :T) && collect_types!(acc, x.T, depth + 1)
    elseif x isa Core.TypeEq || x isa Core.TypeEgal
        collect_types!(acc, getfield(x, :T), depth + 1)
    elseif x isa DataType
        push!(acc, x)
        foreach(p -> collect_types!(acc, p, depth + 1), x.parameters)
    end
end

function struct_rows!(s::Ser, ex::Extra, types)
    rows = String[]
    for T in types
        T isa DataType || continue
        haskey(ex.structs_seen, T) && continue
        ex.structs_seen[T] = nothing
        (isabstracttype(T) || T.name === Tuple.name || T.name === NamedTuple.body.body.name) && continue
        fts = try
            collect(Any, Base.datatype_fieldtypes(T))
        catch
            continue
        end
        push!(rows, "[" * sval(s, T) * ",[" * join([sval(s, ft) for ft in fts], ",") * "]," *
              string(Base.datatype_min_ninitialized(T)) * "]")
        for ft in fts
            ft isa DataType && isconcretetype(ft) && sval(s, ft)
        end
    end
    return rows
end

function tn_row(tn::Core.TypeName)
    body = Base.unwrap_unionall(tn.wrapper)
    names = body isa DataType && body.name === Tuple.name ? Symbol[] :
            body isa DataType && body.name === NamedTuple.body.body.name ? Symbol[] :
            collect(Symbol, tn.names)
    mut = Base.ismutabletypename(tn)
    cs = mut && tn.constfields != C_NULL ? [Base.isconst(body, i) for i in 1:length(names)] : Bool[]
    as = mut && tn.atomicfields != C_NULL ? [Base.isfieldatomic(body, i) for i in 1:length(names)] : Bool[]
    jb(b) = b ? "true" : "false"
    return "[" * jstr(LatticeSer.tnname(tn)) * ",[" * join(jstr.(names), ",") * "],[" *
           join(jb.(cs), ",") * "],[" * join(jb.(as), ",") * "]," * string(tn.n_uninitialized) * "]"
end

# Write the universe lines for everything `encoded` registered, before the case line.
function write_extras(io::IO, s::Ser, ex::Extra, elts)
    acc = Any[]
    foreach(e -> collect_types!(acc, e), elts)
    append!(acc, KIND_TYPES)
    rows = struct_rows!(s, ex, acc)
    # fieldtypes of the struct rows can register further structs; one more round is enough
    # for the depths the model reads.
    tns = String[]
    for tn in s.pending_names
        nm = LatticeSer.tnname(tn)
        nm in ex.tns_seen && continue
        push!(ex.tns_seen, nm)
        push!(tns, tn_row(tn))
    end
    if !isempty(rows)
        println(io, "{\"U\":{\"names\":[],\"layouts\":[],\"nfields\":[],\"instances\":[],",
                "\"constfields\":[],\"primitives\":[],\"structs\":[", join(rows, ","), "]}}")
    end
    isempty(tns) || println(io, "{\"TF\":{\"tns\":[", join(tns, ","), "]}}")
end

# --- soundness smoke test --------------------------------------------------------------------

const UNKNOWN = :unknown

# Is `v` in the concretization of lattice element `a`? `UNKNOWN` when the element's
# concretization depends on information the test does not track (slots, tasks, type variables).
function member(@nospecialize(v), @nospecialize(a))
    if a isa Core.Const
        return v === a.val
    elseif a isa Core.PartialStruct
        isa(v, a.typ) || return false
        for i in 1:length(a.fields)
            fi = a.fields[i]
            fi isa Core.TypeofVararg && break
            u = a.undefs[i]
            d = isdefined(v, i)
            u === true && d && return false
            u === false && !d && return false
            if d
                m = member(getfield(v, i), fi)
                m === UNKNOWN && return UNKNOWN
                m || return false
            end
        end
        return true
    elseif a isa CC.LimitedAccuracy
        return member(v, a.typ)
    elseif a isa Type
        return isa(v, a)
    end
    return UNKNOWN
end

function samples(g::Gen, @nospecialize(a))
    rng = g.rng
    a isa CC.LimitedAccuracy && (a = a.typ)
    a isa Core.Const && return Any[a.val]
    (a isa Type || a isa Core.PartialStruct) || return nothing
    pool = Any[]
    for v in TF_VALUES
        member(v, a) === true && push!(pool, v)
    end
    if a isa Core.PartialStruct && a.typ <: Tuple && !any(f -> f isa Core.TypeofVararg, a.fields)
        for _ in 1:3
            parts = Any[]
            for fi in a.fields
                ps = samples(g, fi)
                (ps === nothing || isempty(ps)) && (parts = nothing; break)
                push!(parts, rand(rng, ps))
            end
            parts === nothing && break
            t = tuple(parts...)
            member(t, a) === true && push!(pool, t)
        end
    end
    return pool
end

function check_sound(g::Gen, f, name, argtypes, rt, nothrow, bad)
    args = Any[]
    va = nothing
    for a in argtypes
        if a isa Core.TypeofVararg
            va = a
        else
            push!(args, a)
        end
    end
    pools = Any[samples(g, a) for a in args]
    any(p -> p === nothing || isempty(p), pools) && return 0
    vapool = nothing
    if va !== nothing
        vapool = isdefined(va, :T) ? samples(g, va.T) : samples(g, Any)
        vapool === nothing && return 0
    end
    checked = 0
    for _ in 1:3
        vals = Any[rand(g.rng, p) for p in pools]
        if vapool !== nothing && !isempty(vapool)
            nva = isdefined(va, :N) ? va.N : rand(g.rng, 0:2)
            nva isa Int || continue
            for _ in 1:nva
                push!(vals, rand(g.rng, vapool))
            end
        end
        threw = false
        res = try
            f(vals...)
        catch
            threw = true
        end
        checked += 1
        if threw
            nothrow && push!(bad, "nothrow but threw: $name($(repr(vals))) argtypes=$(repr(argtypes))")
            continue
        end
        rw = rt
        rw isa CC.Conditional && (rw = Bool)
        rw isa Core.InterConditional && (rw = Bool)
        rw === Union{} && (push!(bad, "Union{} but returned: $name($(repr(vals))) = $(repr(res)) argtypes=$(repr(argtypes))"); continue)
        m = member(res, rw)
        m === false && push!(bad, "result outside rt: $name($(repr(vals))) = $(repr(res)) rt=$(repr(rt)) argtypes=$(repr(argtypes))")
    end
    return checked
end

# --- driver ----------------------------------------------------------------------------------

function main(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    g = Gen(rng); s = Ser(); ex = Extra()
    interp = CC.NativeInterpreter()
    Li = CC.typeinf_lattice(interp)
    Lo = CC.optimizer_lattice(interp)
    dir = mktempdir()
    casefile = joinpath(dir, "cases.jsonl")
    ops = Dict{Int,String}()
    sound_checked = 0; sound_bad = String[]
    open(casefile, "w") do io
        id = 0
        while id < n
            r = rand(rng)
            if r < 0.08
                t = rand(rng) < 0.5 ? rand_elt(g) : randtype(rng, 3)
                astag = rand(rng, Bool)
                exp = expected(s, :val, () -> CC.instanceof_tfunc(t, astag)[1:4])
                a = [selt(s, t), astag ? "true" : "false"]
                write_extras(io, s, ex, Any[t])
                id += 1; ops[id] = "tf.instanceof"
                write_case(io, s, id, "tf.instanceof", "typeinf", a, exp)
                continue
            end
            if r < 0.11
                f, name = rand(rng, TF_DISPATCH_ONLY)
                na = name == "current_scope" ? rand(rng, 0:2) : rand(rng, 0:3)
                argtypes = Any[rand_elt(g) for _ in 1:na]
                rand(rng) < 0.3 && push!(argtypes, rand(rng, Any[Vararg{Any}, Vararg{Int}, Vararg{Int, 1}]))
                exp = expected(s, :elt, () -> CC.builtin_tfunction(interp, f, argtypes, nothing))
                enc = "[" * join([selt(s, a) for a in argtypes], ",") * "]"
                write_extras(io, s, ex, argtypes)
                id += 1; ops[id] = "tf.builtin:" * name
                write_case(io, s, id, "tf.builtin", "typeinf", [jstr(name), enc], exp)
                continue
            end
            f, name, argtypes = gen_call(g)
            name == "svec" && CC.is_all_const_arg(argtypes, 1) && continue
            rt = try
                CC.builtin_tfunction(interp, f, argtypes, nothing)
            catch e
                e
            end
            exp = expected(s, :elt, () -> CC.builtin_tfunction(interp, f, argtypes, nothing))
            enc = "[" * join([selt(s, a) for a in argtypes], ",") * "]"
            write_extras(io, s, ex, argtypes)
            id += 1; ops[id] = "tf.builtin:" * name
            (string(id) == get(opts, "trace", "") || string(id + 1) == get(opts, "trace", "")) && println("TRACE $id $name ", repr(argtypes), " => ", repr(rt))
            write_case(io, s, id, "tf.builtin", "typeinf", [jstr(name), enc], exp)
            rt isa Exception && continue
            id < n || break
            useL, lname = rand(rng) < 0.75 ? (Li, "typeinf") : (Lo, "opt")
            nt = try CC.builtin_nothrow(useL, f, argtypes, rt) catch e; e end
            exp2 = expected(s, :bool, () -> CC.builtin_nothrow(useL, f, argtypes, rt))
            id += 1; ops[id] = "tf.nothrow:" * name
            rtenc = selt(s, rt)
            write_extras(io, s, ex, Any[rt])
            write_case(io, s, id, "tf.nothrow", lname, [jstr(name), enc, rtenc], exp2)
            nt0 = try CC.builtin_nothrow(Li, f, argtypes, rt) catch; false end
            # `getfield(x, i, false)` asserts the index is in bounds (as `@inbounds` does), so
            # its `nothrow` is not a claim about out-of-bounds calls.
            name == "getfield" && (try CC.getfield_boundscheck(argtypes) catch; :unsafe end) === :off && (nt0 = false)
            sound_checked += check_sound(g, f, name, argtypes, rt, nt0 === true, sound_bad)
        end
    end
    println("SOUND checked=$sound_checked violations=$(length(sound_bad))")
    for line in first(unique(sound_bad), parse(Int, opts["show"]))
        println("UNSOUND ", line)
    end
    if haskey(opts, "dump")
        cp(casefile, opts["dump"]; force=true)
        println("WROTE $n cases to $(opts["dump"])")
        return 0
    end
    out = read(pipeline(`$(opts["exe"])`, stdin=casefile), String)
    agree = 0; unmodelled = 0; bad = String[]; seen = 0
    perop = Dict{String,Vector{Int}}()
    unm = Dict{String,Int}()
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
            unmodelled += 1; st[2] += 1
            mm = match(r"unmodelled: ((?:[^\"\\]|\\.)*)", line)
            k = mm === nothing ? "?" : first(mm[1], 300)
            unm[k] = get(unm, k, 0) + 1
        else
            push!(bad, line); st[3] += 1
        end
    end
    for (op, st) in sort(collect(perop))
        println(rpad(op, 32), " agree=", st[1], " unmodelled=", st[2], " disagree=", st[3])
    end
    for (k, c) in sort(collect(unm); by=last, rev=true)
        println("UNMODELLED ", c, " ", k)
    end
    for line in first(bad, parse(Int, opts["show"]))
        println("DISAGREE ", first(line, 3000))
    end
    println("SEED $seed CASES $n ANSWERED $seen UNMODELLED $unmodelled")
    println("AGREE $agree/$(seen - unmodelled)")
    rm(dir; recursive=true)
    return isempty(bad) && seen == n ? 0 : 1
end

exit(main())
