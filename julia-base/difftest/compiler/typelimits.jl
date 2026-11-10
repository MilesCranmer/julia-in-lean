# Differential test of the Lean model of Compiler/src/typelimits.jl against the pinned Julia
# (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA \
#         difftest/compiler/typelimits.jl --cases 20000 --seed 1
#
# Inputs are biased toward the widening limits: deep tuples and nested `Type{}`/`Some{}`, long
# unions, `Vararg` tails and `NTuple`s near `MAX_TYPEUNION_LENGTH`/`MAX_TYPEUNION_COMPLEXITY`,
# `limit_type_size` on a type one wrapper deeper than its comparison (as recursion limiting
# produces), and `tmerge` of `Const`/`PartialStruct` of one type. Prints `AGREE k/n`; cases the
# model reports as `unmodelled` are counted separately and are not agreement.
#
# Runs (seed, cases, agreement):
#   2026-11-09, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 20000 cases: AGREE 19997/19997, 3 unmodelled
#   seed 2, 20000 cases: AGREE 19996/19996, 4 unmodelled
#   seed 3, 20000 cases: AGREE 19995/19995, 5 unmodelled
#   The 12 unmodelled cases are `n_initialized` of a `Const` whose value is a type object
#   (`nfields` of a `DataType`/`Union{}` value is not in the universe) and `PartialStruct`s of
#   `typeof(Union{})`.
#   Sensitivity: with MAX_TYPEUNION_LENGTH = 4 in the model, 3000 cases (seed 1) gave 18
#   disagreements; with `t !== 2` for `t !== 1` in the Int rule of `type_more_complex`, 2.
#   An earlier generator (before the Int-parameter pairs) gave one name-only disagreement at
#   seed 3: `tuple_tail_elem` returned `Val`'s wrapper (variable `x`) where the model, and the
#   same call in a fresh process, keep the input's alpha-equivalent `Val{T} where T`. The
#   result depends on what earlier cases left in Julia's type caches; it is not modelled.

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

abstract type AbsA end
struct CA <: AbsA end
struct WA{T} <: AbsA
    x::T
end
abstract type AbsB{T} <: AbsA end
struct WB{T} <: AbsB{T}
    x::T
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
                  ("opt", CC.optimizer_lattice(CC.NativeInterpreter()))]
const JLT = CC.JLTypeLattice()
const PARTIALS = CC.PartialsLattice(CC.ConstsLattice())

const FREE_T = TypeVar(:T, Integer)

const LEAF = Any[Int, Int8, Bool, Float64, Nothing, Symbol, String, Missing, Char, UInt8, CA,
                 Tuple{}, Union{}]
const ABSTRACT = Any[Any, Integer, Real, Number, Signed, AbsA, AbstractVector{Int},
                     AbstractArray{Int}, AbstractString, AbsB{Int}, AbsB, Function, Type, DataType]
const WRAPS = Any[Some, Vector, Ref, Base.RefValue, Val, Pt, WA, WB, AbsB, Complex]

function leaftype(rng)
    rand(rng) < 0.75 ? rand(rng, LEAF) : rand(rng, ABSTRACT)
end

# A random type with structure near the limits: deep, long unions, Vararg tails, Type{}.
function randtype(rng, depth=3)
    r = rand(rng)
    if depth <= 0 || r < 0.3
        return leaftype(rng)
    elseif r < 0.45
        k = rand(rng, 2:6)
        ts = Any[randtype(rng, depth - 2) for _ in 1:k]
        return try Union{ts...} catch; Any end
    elseif r < 0.65
        k = rand(rng, 0:5)
        ps = Any[randtype(rng, depth - 1) for _ in 1:k]
        if k > 0 && rand(rng) < 0.3
            ps[end] = rand(rng) < 0.8 ? Vararg{ps[end]} : Vararg{ps[end], rand(rng, 1:3)}
        end
        return try Tuple{ps...} catch; Tuple{} end
    elseif r < 0.7
        return try NTuple{rand(rng, 1:6), randtype(rng, depth - 1)} catch; Tuple{Int} end
    elseif r < 0.8
        t = randtype(rng, depth - 1)
        return try (rand(rng) < 0.85 ? Type{t} : Core.TypeEgal{t}) catch; Type end
    elseif r < 0.88
        W = rand(rng, WRAPS)
        t = randtype(rng, depth - 1)
        return try (W === Val ? Val{rand(rng, (1, 2, :a, t))} : W === Pt || W === WA || W === WB ||
                    W === Some || W === Ref || W === Base.RefValue || W === Vector ||
                    W === AbsB ? W{t} : Complex{Int}) catch; W end
    elseif r < 0.95
        return rand(rng, (Vector{T} where T, Some{T} where T, Ref{T} where T<:Integer,
            Tuple{T,T} where T, Tuple{Vector{T},T} where T, Type{T} where T<:Integer,
            Pt{T} where T, AbsB{T} where T<:Number, Array{Int,N} where N, Tuple{Vararg{Int,N}} where N,
            Tuple{Int,Vararg{T}} where T, Val{T} where T, WB{T} where T<:Real, Complex))
    else
        return rand(rng, (Some{Some{Some{Int}}}, Tuple{Tuple{Tuple{Int}}}, Type{Type{Type{Int}}},
            Val{Val{Val{1}}}, Tuple{Tuple{Int,Int},Tuple{Int}}, Vector{Vector{Vector{Int}}},
            Type{Vector{Vector{Int}}}, Tuple{Type{Type{Int}}}, Union{Int,Tuple{Union{Int,Nothing}}}))
    end
end

# A type one level more complex than `c`, the shape recursion limiting compares.
function deeper(rng, @nospecialize(c))
    r = rand(rng)
    try
        r < 0.2 && return Tuple{c}
        r < 0.35 && return Tuple{c, randtype(rng, 1)}
        r < 0.5 && return Type{c}
        r < 0.6 && return Some{c}
        r < 0.7 && return Vector{c}
        r < 0.8 && return Union{c, randtype(rng, 1)}
        r < 0.9 && c isa DataType && c.name === Tuple.name && return Tuple{c.parameters..., randtype(rng, 1)}
        return Val{c}
    catch
        return Any
    end
end

const VALUES = Any[1, 0, -5, 7, true, false, nothing, :a, :b, (), (1,), (1, :a), (nothing, true),
    (1, 2), (2, 2), (1, (2, 3)), ((1,), :b), Some(1), Some(2), Some(nothing), Some(:a), Some(Int),
    Pair(1, :a), Pair(2, :a), Pair(1, :b), Complex(1, 2), Complex(1, 3), Pt(1, 2), Pt(1, 3), Pt(:a, :b),
    Int, Union{}, Any, Vector{Int}, Some{T} where T, Type{Int}, Val{1}(), Val{:a}(), sin, missing,
    1.5, 0x01, HalfInit(1), HalfInit(1, :x), HalfInit(2, nothing), HalfInit(1, 2), (Int, 1),
    CA(), WA(1), WA(:a), WB(1), WB(2.0)]

mutable struct Gen
    rng::Random.AbstractRNG
    causes::Vector{Any}
    states::Vector{Any}
    mis::Vector{Any}
    sources::Vector{Any}
end

function Gen(rng)
    IS = CC.InferenceState{CC.NativeInterpreter}
    states = Any[ccall(:jl_new_struct_uninit, Any, (Any,), IS) for _ in 1:3]
    S = fieldtype(CC.LimitedAccuracy, :causes)
    causes = Any[]
    for sub in ([1], [2], [1, 2], [1, 2, 3], [3])
        c = S(); foreach(i -> push!(c, states[i]), sub); push!(causes, c)
    end
    m1 = first(methods(sin, (Float64,))); m2 = first(methods(cos, (Float64,)))
    mis = Any[CC.specialize_method(m1, Tuple{typeof(sin),Float64}, Core.svec()),
              CC.specialize_method(m2, Tuple{typeof(cos),Float64}, Core.svec())]
    Gen(rng, causes, states, mis, Any[m1, m2])
end

const PS_TYPES = Any[Some{Int}, Some{Any}, Some{Union{Int,Nothing}}, Pair{Int,Symbol}, Pair{Any,Any},
    Complex{Int}, Pt{Int}, Pt{Any}, HalfInit, Tuple{Int,Symbol}, Tuple{Any,Any}, Tuple{Int,Vararg{Int}},
    Tuple{Any}, Tuple{Int,Int}, Tuple{Nothing,Any}, Tuple{Bool,Vararg{Any}}, WA{Any}, WB{Real},
    Tuple{Any,Tuple{Any,Any}}, Tuple{Integer,Integer}]

function simple_elt(g::Gen, depth)
    rng = g.rng
    r = rand(rng)
    if depth <= 0 || r < 0.35
        return randtype(rng, 2)
    elseif r < 0.6
        return Core.Const(rand(rng, VALUES))
    elseif r < 0.85
        return partial_struct(g, depth - 1)
    elseif r < 0.9
        return CC.PartialTypeVar(rand(rng, (FREE_T, TypeVar(:R, Int))), rand(rng, Bool), rand(rng, Bool))
    elseif r < 0.95
        return Core.PartialTask(simple_elt(g, depth - 1))
    else
        return Core.PartialOpaque(rand(rng, (Core.OpaqueClosure{Tuple{Int},Int},
                    Core.OpaqueClosure{Tuple{Int},Any})), simple_elt(g, depth - 1),
                    rand(rng, g.mis), rand(rng, g.sources))
    end
end

function field_elt(g::Gen, @nospecialize(ft), depth)
    rng = g.rng
    r = rand(rng)
    if r < 0.25
        return ft
    elseif r < 0.55
        vs = filter(v -> v isa ft, VALUES)
        isempty(vs) || return Core.Const(rand(rng, vs))
    elseif r < 0.7 && depth > 0
        ts = filter(t -> t <: ft && isconcretetype(t), PS_TYPES)
        isempty(ts) || return partial_struct(g, depth - 1, rand(rng, ts))
    elseif r < 0.85
        return try typeintersect(ft, randtype(rng, 1)) catch; ft end
    end
    return simple_elt(g, depth)
end

function partial_struct(g::Gen, depth, typ=nothing)
    rng = g.rng
    for _ in 1:10
        T = typ === nothing ? rand(rng, PS_TYPES) : typ
        isva = Base.isvatuple(T)
        n = isva ? length(T.parameters) : fieldcount(T)
        fields = Any[]
        for i in 1:n
            ft = isva && i == n ? T.parameters[i] : fieldtype(T, i)
            if isva && i == n
                push!(fields, ft)
            else
                push!(fields, rand(rng) < 0.1 ? Union{} : field_elt(g, ft, depth))
            end
        end
        try
            if rand(rng) < 0.85
                return Core.PartialStruct(CC.fallback_lattice, T, fields)
            else
                undefs = Union{Nothing,Bool}[rand(rng, (nothing, true, false)) for _ in 1:n]
                for i in 1:n
                    fields[i] === Union{} && (undefs[i] = true)
                end
                isva && (undefs[end] = nothing)
                return Core._PartialStruct(T, undefs, fields)
            end
        catch
        end
    end
    return Core.PartialStruct(CC.fallback_lattice, Tuple{Int,Int}, Any[Core.Const(1), Int])
end

function rand_elt(g::Gen, depth=2)
    rng = g.rng
    r = rand(rng)
    if r < 0.55
        simple_elt(g, depth)
    elseif r < 0.7
        try
            CC.Conditional(rand(rng, 1:2), rand(rng, 0:1), simple_elt(g, depth - 1),
                           simple_elt(g, depth - 1); isdefined=rand(rng, Bool))
        catch; Bool end
    elseif r < 0.76
        Core.InterConditional(rand(rng, 1:2), simple_elt(g, depth - 1), simple_elt(g, depth - 1))
    elseif r < 0.86
        try
            CC.MustAlias(rand(rng, 1:2), rand(rng, 0:1), simple_elt(g, depth - 1), rand(rng, 1:2),
                         simple_elt(g, depth - 1))
        catch; Any end
    elseif r < 0.9
        Core.InterMustAlias(rand(rng, 1:2), simple_elt(g, depth - 1), rand(rng, 1:2),
                            simple_elt(g, depth - 1))
    else
        typ = rand(rng) < 0.5 ? simple_elt(g, depth - 1) : rand_elt(g, depth - 1)
        typ isa CC.LimitedAccuracy && (typ = typ.typ)
        S = fieldtype(CC.LimitedAccuracy, :causes)
        c = rand(rng) < 0.6 ? rand(rng, g.causes) : (s = S(); foreach(st -> rand(rng) < 0.5 && push!(s, st), g.states); isempty(s) && push!(s, g.states[1]); s)
        CC.LimitedAccuracy(typ, c)
    end
end

# A second lattice element related to `a`: equal, wider, narrower, of the same type, or limited.
function related(g::Gen, @nospecialize(a))
    rng = g.rng
    r = rand(rng)
    try
        r < 0.1 && return a
        r < 0.25 && return CC.widenconst(CC.ignorelimited(a))
        if r < 0.45
            w = CC.widenconst(CC.ignorelimited(a))
            ts = filter(t -> t <: w && isconcretetype(t), PS_TYPES)
            vs = filter(v -> v isa w && !ismutable(v), VALUES)
            rand(rng) < 0.5 && !isempty(vs) && return Core.Const(rand(rng, vs))
            isconcretetype(w) && isstructtype(w) && return partial_struct(g, 1, w)
            isempty(ts) || return partial_struct(g, 1, rand(rng, ts))
        end
        r < 0.5 && return rand(rng, (Any, Union{}, Bool, Core.Const(true), Core.Const(false)))
        r < 0.6 && a isa CC.LimitedAccuracy && return a.typ
        r < 0.7 && return CC.LimitedAccuracy(CC.ignorelimited(a), rand(rng, g.causes))
    catch
    end
    return rand_elt(g)
end

# Field types and `datatype_min_ninitialized` of the struct types the model may ask about.
function struct_info(s::Ser)
    Ts = Any[]
    for T in Iterators.flatten((PS_TYPES, map(typeof, VALUES), LEAF))
        T isa DataType && isconcretetype(T) && !(T <: Tuple) && !(T in Ts) && push!(Ts, T)
    end
    rows = String[]
    for T in Ts
        fts = try Any[fieldtype(T, i) for i in 1:fieldcount(T)] catch; continue end
        push!(rows, "[" * sval(s, T) * ",[" * join([sval(s, f) for f in fts], ",") * "]," *
                    string(Base.datatype_min_ninitialized(T)) * "]")
    end
    return "{\"U\":{\"names\":[],\"layouts\":[],\"nfields\":[],\"instances\":[],\"constfields\":[]," *
           "\"primitives\":[],\"structs\":[" * join(rows, ",") * "]}}"
end

jbool(b::Bool) = b ? "true" : "false"
jint(i::Int) = string(i)
svals(s, ts) = "[" * join([sval(s, t) for t in ts], ",") * "]"

const SOURCES_POOL = Any[Any, Int, Tuple{Int}, Some{Int}, Type{Int}, Vector{Int}, Integer,
                         Tuple{Tuple{Int}}, Union{Int,Nothing}, Tuple{Int,Vararg{Int}}]

function gen_case(g::Gen, s::Ser, id::Int, io::IO)
    rng = g.rng
    r = rand(rng)
    lname = "typeinf"
    if r < 0.30
        op = "tmerge"
        lname, L = rand(rng) < 0.7 ? LATTICES[1] : rand(rng, LATTICES)
        a = rand(rng) < 0.3 ? partial_struct(g, 2) : rand_elt(g)
        b = related(g, a)
        rand(rng) < 0.5 && ((a, b) = (b, a))
        args = [selt(s, a), selt(s, b)]
        exp = expected(s, :elt, () -> CC.tmerge(L, a, b))
    elseif r < 0.42
        op = "tmerge"; lname = "jltype"
        a = randtype(rng); b = rand(rng) < 0.5 ? randtype(rng) : deeper(rng, a)
        args = [selt(s, a), selt(s, b)]
        exp = expected(s, :elt, () -> CC.tmerge(JLT, a, b))
    elseif r < 0.48
        op = rand(rng, ("tmergeFastPath", "issimplertype"))
        lname, L = rand(rng) < 0.7 ? LATTICES[1] : rand(rng, LATTICES)
        a = rand(rng) < 0.4 ? partial_struct(g, 2) : rand_elt(g)
        b = related(g, a)
        args = [selt(s, a), selt(s, b)]
        exp = op == "tmergeFastPath" ? expected(s, :nothing, () -> CC.tmerge_fast_path(L, a, b)) :
              expected(s, :bool, () -> CC.issimplertype(L, a, b))
    elseif r < 0.54
        op = "tmergePartialStruct"; lname = "partials"
        T = rand(rng, PS_TYPES)
        mk1() = begin
            vs = filter(v -> v isa T && !ismutable(v), VALUES)
            (!isempty(vs) && rand(rng) < 0.4) ? Core.Const(rand(rng, vs)) : partial_struct(g, 2, T)
        end
        a = mk1(); b = mk1()
        args = [selt(s, a), selt(s, b)]
        exp = expected(s, :nothing, () -> CC.tmerge_partial_struct(PARTIALS, a, b))
    elseif r < 0.62
        op = "tmergeTypesSlow"
        a = randtype(rng); b = rand(rng) < 0.5 ? randtype(rng) : deeper(rng, a)
        args = [sval(s, a), sval(s, b)]
        exp = expected(s, :val, () -> CC.tmerge_types_slow(a, b))
    elseif r < 0.68
        op = "tuplemerge"
        mk() = (t = randtype(rng, 3); t isa DataType && t.name === Tuple.name ? t :
                (try Tuple{Any[randtype(rng, 2) for _ in 1:rand(rng, 0:4)]...} catch; Tuple{} end))
        a = mk(); b = rand(rng) < 0.3 ? deeper(rng, a) : mk()
        b isa DataType && b.name === Tuple.name || (b = mk())
        args = [sval(s, a), sval(s, b)]
        exp = expected(s, :val, () -> CC.tuplemerge(a, b))
    elseif r < 0.74
        op = rand(rng, ("issimpleenoughtype", "unioncomplexity", "unionCountAbstract"))
        t = randtype(rng, 4)
        args = [sval(s, t)]
        exp = op == "issimpleenoughtype" ? expected(s, :bool, () -> CC.issimpleenoughtype(t)) :
              op == "unioncomplexity" ? expected(s, :val, () -> CC.unioncomplexity(t)) :
              expected(s, :val, () -> Int(CC.union_count_abstract(t)))
    elseif r < 0.84
        op = "limitTypeSize"
        c = randtype(rng, 3)
        t = rand(rng) < 0.8 ? deeper(rng, rand(rng) < 0.5 ? c : deeper(rng, c)) : randtype(rng, 4)
        src = rand(rng) < 0.5 ? rand(rng, SOURCES_POOL) : randtype(rng, 2)
        d = rand(rng, 0:3); l = rand(rng, 0:3)
        args = [sval(s, t), sval(s, c), sval(s, src), jint(d), jint(l)]
        exp = expected(s, :val, () -> CC.limit_type_size(t, c, src, d, l))
    elseif r < 0.9
        op = rand(rng, ("typeMoreComplex", "limitTypeSize_"))
        c = randtype(rng, 3)
        t = rand(rng) < 0.7 ? deeper(rng, c) : randtype(rng, 3)
        if rand(rng) < 0.25
            # integer parameters (the `isa(t, Int) && isa(c, Int)` rule): Val{i}, Vararg{_, i}
            i = rand(rng, -1:4); j = rand(rng, -1:4)
            (t, c) = rand(rng, ((Val{i}, Val{j}), (Some{Val{i}}, Some{Val{j}}),
                (Tuple{Val{i},Int}, Tuple{Val{j},Int}), (Tuple{Int,Vararg{Val{i},max(i,0)}}, Tuple{Int,Vararg{Val{j},max(j,0)}})))
        end
        ss = Any[Base.unwrap_unionall(rand(rng) < 0.5 ? rand(rng, SOURCES_POOL) : randtype(rng, 2)) for _ in 1:rand(rng, 1:2)]
        if op == "typeMoreComplex"
            d = rand(rng, 1:3); td = rand(rng, 0:3); l = rand(rng, 0:3)
            args = [sval(s, t), sval(s, c), svals(s, ss), jint(d), jint(td), jint(l)]
            exp = expected(s, :bool, () -> CC.type_more_complex(t, c, Core.svec(ss...), d, td, l))
        else
            d = rand(rng, 1:3); l = rand(rng, 0:3)
            args = [sval(s, t), sval(s, c), svals(s, ss), jint(d), jint(l)]
            exp = expected(s, :val, () -> CC._limit_type_size(t, c, Core.svec(ss...), d, l))
        end
    elseif r < 0.95
        op = "isDerivedType"
        c = randtype(rng, 3)
        t = rand(rng) < 0.6 ? (ps = Any[]; x = c; for _ in 1:4
                x = Base.unwrap_unionall(x); x isa DataType && !isempty(x.parameters) || break
                x = rand(rng, collect(Any, x.parameters)); Base.isvarargtype(x) && (x = Base.unwrapva(x)); push!(ps, x) end;
                isempty(ps) ? c : rand(rng, ps)) : randtype(rng, 2)
        md = rand(rng, -1:3)
        args = [sval(s, t), sval(s, c), jint(md)]
        exp = expected(s, :bool, () -> CC.is_derived_type(t, c, md))
    elseif r < 0.975
        op = "tnameIntersect"
        a = rand(rng, (Any, Integer, Int, Signed, Real, Number, AbsA, CA, WA, WB, AbsB, Some, Tuple,
                       Float64, AbstractArray, Vector, AbstractVector, DenseArray))
        b = rand(rng, (Any, Integer, Int, Signed, Real, Number, AbsA, CA, WA, WB, AbsB, Some, Tuple,
                       Float64, AbstractArray, Vector, AbstractVector, DenseArray))
        args = [sval(s, a), sval(s, b)]
        exp = expected(s, :val, () -> (r = CC.tname_intersect(Base.unwrap_unionall(a).name,
                                        Base.unwrap_unionall(b).name); r === nothing ? :none : r.wrapper))
    else
        op = "tupleTailElem"
        init = rand(rng) < 0.7 ? Union{} : randtype(rng, 1)
        ct = Any[randtype(rng, 2) for _ in 1:rand(rng, 1:4)]
        rand(rng) < 0.3 && (ct[end] = Vararg{ct[end]})
        args = [selt(s, init), svals(s, ct)]
        exp = expected(s, :val, () -> CC.tuple_tail_elem(CC.fallback_lattice, init, ct))
    end
    write_case(io, s, id, op, lname, args, exp)
    return op
end

function main(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    g = Gen(rng); s = Ser()
    dir = mktempdir()
    casefile = joinpath(dir, "cases.jsonl")
    ops = Dict{Int,String}()
    open(casefile, "w") do io
        println(io, struct_info(s))
        for id in 1:n
            ops[id] = gen_case(g, s, id, io)
        end
    end
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
        println(rpad(op, 28), " agree=", st[1], " unmodelled=", st[2], " disagree=", st[3])
    end
    for line in first(bad, parse(Int, opts["show"]))
        println("DISAGREE ", line)
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
