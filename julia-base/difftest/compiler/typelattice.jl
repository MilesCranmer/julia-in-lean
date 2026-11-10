# Differential test of the Lean model of Compiler/src/abstractlattice.jl and typelattice.jl
# against the pinned Julia (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA difftest/compiler/typelattice.jl \
#         --cases 50000 --seed 1
#
# Generates random lattice elements (edge-heavy: Union{}, Any, Type, Type{Union{}}, Vararg tails,
# Const of types, PartialStruct with undefined fields, Conditional/MustAlias on few slots,
# LimitedAccuracy with shared and distinct causes), runs each operation on the pinned Compiler
# with `typeinf_lattice(NativeInterpreter())` (and the ipo and optimizer lattices), and compares
# with `compilerdiff`. Prints `AGREE k/n`; cases the model reports as `unmodelled` are counted
# separately and are not agreement.
#
# Runs (seed, cases, agreement):
#   2026-11-09, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 20000 cases: AGREE 19959/19959, 41 unmodelled
#   seed 2, 20000 cases: AGREE 19951/19951, 49 unmodelled
#   seed 3, 20000 cases: AGREE 19947/19947, 53 unmodelled
#   All 143 unmodelled cases are `tmeet` of a Tuple `PartialStruct` that reaches the
#   `getfield_tfunc`/`tuple_tfunc` branch (Compiler/src/typelattice.jl:653-666).
#   2026-11-09, after `is_const_prop_profitable_arg` learned Method/CodeInstance constants and
#   VALUES gained a Method and a CodeInstance (seed 1 has 162 cases with a Method, 7 of them
#   `isConstPropProfitableArg` of a Method or CodeInstance), same pinned Julia:
#   seed 1, 20000 cases: AGREE 19959/19959, 41 unmodelled
#   seed 2, 20000 cases: AGREE 19951/19951, 49 unmodelled
#   seed 3, 20000 cases: AGREE 19947/19947, 53 unmodelled
#   All unmodelled cases are `tmeet` cases (same counts as the run above).

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

const FREE_T = TypeVar(:T, Integer)
const FREE_S = TypeVar(:S)

const BASE_TYPES = Any[
    Any, Union{}, Int, Int8, Bool, Float64, Nothing, Symbol, String, Integer, Real, Number, Signed,
    Some{Int}, Some{Any}, Some{Union{Int,Nothing}}, Some{Symbol}, Pair{Int,Symbol}, Complex{Int},
    Tuple{}, Tuple{Int}, Tuple{Int,Symbol}, Tuple{Vararg{Int}}, NTuple{2,Int}, Tuple{Int,Vararg{Any}},
    Tuple{Any}, Tuple{Bool,Bool}, Tuple{Nothing}, Tuple{Int,Int},
    Union{Int,Nothing}, Union{Int,Symbol,Nothing}, Union{Bool,Nothing},
    Type, Type{Int}, Type{Union{}}, Core.TypeEgal{Int}, Type{<:Integer}, Type{Vector{Int}},
    DataType, UnionAll, Union, TypeVar, Core.TypeofBottom, Core.TypeEq,
    Vector{Int}, Vector{Any}, Base.RefValue{Int}, Ref{Int}, Val{1}, Val{:a}, Val{true},
    Some{T} where T, Some{<:Integer}, Tuple{T,T} where T, Vector{T} where T<:Real,
    Type{T} where T<:Integer, Tuple{Type{T},T} where T, Pt{T} where T, Pt{Int}, Pt{Any},
    Task, Function, typeof(sin), Missing, HalfInit, Core.OpaqueClosure{Tuple{Int},Int},
    FREE_T, Vector{FREE_T}, Some{FREE_S}, Type{FREE_T},
]

const VALUES = Any[
    1, 0, -5, 7, true, false, nothing, :a, :b, (), (1,), (1, :a), (nothing, true), (1, 2),
    Some(1), Some(nothing), Some(:a), Some(Int), Pair(1, :a), Complex(1, 2), Pt(1, 2),
    Int, Union{}, Any, Bool, Nothing, Vector{Int}, Some{T} where T, Type{Int}, Tuple{Int},
    Union{Int,Nothing}, Vector{FREE_T}, Val{1}(), Val{:a}(), sin, missing, 1.5, 0x01,
    HalfInit(1), HalfInit(1, :x), HalfInit(2, nothing), (Int, 1), Core, Ref(1),
    TypeVar(:Q), FREE_T,
]
# A Method and a CodeInstance, which is_const_prop_profitable_arg treats as profitable constants.
let m = first(methods(sin, (Float64,)))
    push!(VALUES, m)
    mi = CC.specialize_method(m, Tuple{typeof(sin),Float64}, Core.svec())
    isdefined(mi, :cache) && mi.cache isa Core.CodeInstance && push!(VALUES, mi.cache)
end

randtype(rng, depth=2) = begin
    r = rand(rng)
    if depth <= 0 || r < 0.55
        rand(rng, BASE_TYPES)
    elseif r < 0.7
        a = randtype(rng, depth - 1); b = randtype(rng, depth - 1)
        try Union{a, b} catch; Any end
    elseif r < 0.82
        k = rand(rng, 0:3)
        ps = Any[randtype(rng, depth - 1) for _ in 1:k]
        if k > 0 && rand(rng) < 0.3
            ps[end] = Vararg{ps[end]}
        end
        try Tuple{ps...} catch; Tuple{} end
    elseif r < 0.9
        t = randtype(rng, depth - 1)
        try Type{t} catch; Type end
    else
        t = randtype(rng, depth - 1)
        try Some{t} catch; Some{Any} end
    end
end

mutable struct Gen
    rng::Random.AbstractRNG
    causes::Vector{Any}       # shared IdSets of fake InferenceStates
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

function fresh_causes(g::Gen)
    S = fieldtype(CC.LimitedAccuracy, :causes)
    c = S()
    for st in g.states
        rand(g.rng) < 0.5 && push!(c, st)
    end
    isempty(c) && push!(c, g.states[1])
    c
end

# A native lattice element: a type, or `Const`/`PartialStruct`/... of the simple lattice.
function simple_elt(g::Gen, depth)
    rng = g.rng
    r = rand(rng)
    if depth <= 0 || r < 0.35
        return randtype(rng, depth)
    elseif r < 0.6
        return Core.Const(rand(rng, VALUES))
    elseif r < 0.85
        return partial_struct(g, depth - 1)
    elseif r < 0.9
        return CC.PartialTypeVar(rand(rng, (FREE_T, FREE_S, TypeVar(:R, Int))), rand(rng, Bool), rand(rng, Bool))
    elseif r < 0.95
        return Core.PartialTask(simple_elt(g, depth - 1))
    else
        return Core.PartialOpaque(rand(rng, (Core.OpaqueClosure{Tuple{Int},Int},
                    Core.OpaqueClosure{Tuple{Int},Any}, Core.OpaqueClosure)),
                    simple_elt(g, depth - 1), rand(rng, g.mis), rand(rng, g.sources))
    end
end

function partial_struct(g::Gen, depth)
    rng = g.rng
    for _ in 1:10
        typ = rand(rng, (Some{Int}, Some{Any}, Some{Union{Int,Nothing}}, Pair{Int,Symbol},
            Pair{Any,Any}, Complex{Int}, Pt{Int}, Pt{Any}, HalfInit, Tuple{Int,Symbol},
            Tuple{Any,Any}, Tuple{Int,Vararg{Int}}, Tuple{Any}, Tuple{Int,Int}, Tuple{Nothing,Any},
            Tuple{Bool,Vararg{Any}}, Base.RefValue{Any}))
        typ isa DataType || continue
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
            elseif r < 0.45
                push!(fields, Union{})
            else
                push!(fields, simple_elt(g, depth))
            end
        end
        try
            if rand(rng) < 0.8
                return Core.PartialStruct(CC.fallback_lattice, typ, fields)
            else
                undefs = Union{Nothing,Bool}[rand(rng, (nothing, true, false)) for _ in 1:n]
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

function rand_elt(g::Gen, depth=2)
    rng = g.rng
    r = rand(rng)
    x = if r < 0.55
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
        CC.LimitedAccuracy(typ, rand(rng) < 0.6 ? rand(rng, g.causes) : fresh_causes(g))
    end
    return x
end

# A second argument related to `a`, so that orders and equalities are often true.
function related(g::Gen, @nospecialize(a))
    rng = g.rng
    r = rand(rng)
    if r < 0.2
        return a
    elseif r < 0.4
        try return CC.widenconst(CC.ignorelimited(a)) catch end
    elseif r < 0.5
        return rand(rng, (Any, Union{}, Bool, Core.Const(true), Core.Const(false)))
    elseif r < 0.6 && a isa CC.LimitedAccuracy
        return a.typ
    elseif r < 0.7
        try return CC.LimitedAccuracy(CC.ignorelimited(a), rand(rng, g.causes)) catch end
    end
    return rand_elt(g)
end

const BINARY = ["sqsub", "sqsubStrict", "sqsubStrictNe", "isLatticeEqual"]
const UNARY_L = ["hasNontrivialExtendedInfo", "isConstPropProfitableArg", "isForwardableArgtype",
                 "isValidLattice", "isLatticeBool", "widenlattice"]
const UNARY = ["widenconst", "widenconstSplit", "widenconditional", "widenwrappedconditional",
               "widenslotwrapper", "widenmustalias", "widenwrappedmustalias",
               "maybeExtractConstBool", "isalreadyconst"]

function gen_case(g::Gen, s::Ser, id::Int, io::IO)
    rng = g.rng
    lname, L = rand(rng) < 0.7 ? LATTICES[1] : rand(rng, LATTICES)
    r = rand(rng)
    if r < 0.45
        op = rand(rng, BINARY)
        a = rand_elt(g); b = related(g, a)
        f = op == "sqsub" ? (() -> CC.:⊑(L, a, b)) : op == "sqsubStrict" ? (() -> CC.:⊏(L, a, b)) :
            op == "sqsubStrictNe" ? (() -> CC.:⋤(L, a, b)) : (() -> CC.is_lattice_equal(L, a, b))
        args = [selt(s, a), selt(s, b)]
        exp = expected(s, :bool, f)
    elseif r < 0.6
        op = "tmeet"
        a = rand(rng) < 0.15 ? partial_struct(g, 1) : rand_elt(g)
        t = a isa Core.PartialStruct && rand(rng) < 0.5 ?
            rand(rng, (Tuple{Int,Int}, Tuple{Any,Symbol}, Tuple{Int,Vararg{Int}}, Some{Int},
                       Tuple{Integer,Any}, Pair{Int,Symbol}, Tuple{Bool,Nothing})) : randtype(rng)
        args = [selt(s, a), sval(s, t)]
        exp = expected(s, :elt, () -> CC.tmeet(L, a, t))
    elseif r < 0.75
        op = rand(rng, UNARY_L)
        a = rand_elt(g)
        args = [selt(s, a)]
        f = op == "hasNontrivialExtendedInfo" ? (() -> CC.has_nontrivial_extended_info(L, a)) :
            op == "isConstPropProfitableArg" ? (() -> CC.is_const_prop_profitable_arg(L, a)) :
            op == "isForwardableArgtype" ? (() -> CC.is_forwardable_argtype(L, a)) :
            op == "isValidLattice" ? (() -> CC.is_valid_lattice(L, a)) :
            op == "isLatticeBool" ? (() -> CC.is_lattice_bool(L, a)) :
            (() -> CC.widenlattice(L, a))
        exp = expected(s, op == "widenlattice" ? :elt : :bool, f)
    elseif r < 0.9
        op = rand(rng, UNARY)
        lname = "typeinf"
        a = rand_elt(g)
        args = [selt(s, a)]
        f = op == "widenconst" ? (() -> CC.widenconst(a)) :
            op == "widenconstSplit" ? (() -> CC.widenconst_split(a)) :
            op == "widenconditional" ? (() -> CC.widenconditional(a)) :
            op == "widenwrappedconditional" ? (() -> CC.widenwrappedconditional(a)) :
            op == "widenslotwrapper" ? (() -> CC.widenslotwrapper(a)) :
            op == "widenmustalias" ? (() -> CC.widenmustalias(a)) :
            op == "widenwrappedmustalias" ? (() -> CC.widenwrappedmustalias(a)) :
            op == "maybeExtractConstBool" ? (() -> CC.maybe_extract_const_bool(a)) :
            (() -> CC.isalreadyconst(a))
        kind = op in ("widenconst", "widenconstSplit") ? :val :
               op == "maybeExtractConstBool" ? :optbool : op == "isalreadyconst" ? :bool : :elt
        exp = expected(s, kind, f)
    elseif r < 0.95
        op = rand(rng, ("narrowMustalias", "narrowLimitedTyp"))
        a = rand_elt(g); b = rand(rng) < 0.5 ? related(g, a) : rand_elt(g)
        args = [selt(s, a), selt(s, b)]
        exp = expected(s, :elt, op == "narrowMustalias" ? (() -> CC.narrow_mustalias(L, a, b)) :
                                                          (() -> CC.narrow_limited_typ(a, b)))
    else
        op = rand(rng, ("validAsLattice", "isconstType"))
        lname = "typeinf"
        t = randtype(rng)
        astag = rand(rng, Bool)
        args = op == "validAsLattice" ? [sval(s, t), jbool(astag)] : [sval(s, t)]
        exp = expected(s, :bool, op == "validAsLattice" ? (() -> CC.valid_as_lattice(t, astag)) :
                                                          (() -> CC.isconstType(t)))
    end
    write_case(io, s, id, op, lname, args, exp)
    return op
end

jbool(b::Bool) = b ? "true" : "false"

function main(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    g = Gen(rng); s = Ser()
    dir = mktempdir()
    casefile = joinpath(dir, "cases.jsonl")
    ops = Dict{Int,String}()
    open(casefile, "w") do io
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
    agree = 0; unmodelled = 0; bad = String[]; seen = 0
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
            unmodelled += 1; st[2] += 1
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
    println("SEED $seed CASES $n ANSWERED $seen UNMODELLED $unmodelled")
    println("AGREE $agree/$(seen - unmodelled)")
    rm(dir; recursive=true)
    return isempty(bad) && seen == n ? 0 : 1
end

exit(main())
