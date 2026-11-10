# Differential test of the Lean model of Compiler/src/typeutils.jl (JuliaLean/Compiler/src/typeutils.lean
# and typeutils/lattice.lean) and of `is_union_split_eligible` (Compiler/src/abstractinterpretation.jl)
# against the pinned Julia (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA \
#         difftest/compiler/typeutils.jl --cases 20000 --seed 1
#
# Inputs are biased toward union splitting: argument lists with several unions of 2 to 6 members
# (so the cost lands on both sides of `max_union_splitting`), unions inside `Vararg` tails, `Const`s
# of `Union` types, `MustAlias` and `Conditional` elements whose widened type is a union, repeated
# `MustAlias` and `SlotNumber`/`SSAValue` arguments (alias groups, including chains that
# `merge_mustalias_groups!` re-points), `fargs` shorter than `argtypes`, tuples wrapped in
# `UnionAll`s whose variable occurs inside a union (the diagonal rule), `Vararg{Union{}}` and
# misplaced `Vararg`s for `argtypes_to_type`, and `typesubtract` of a tuple of unions minus a
# tuple of one member. Prints `AGREE k/n`; cases the model reports as `unmodelled` are counted
# separately and are not agreement.
#
# Runs (seed, cases, agreement):
#   2026-11-09, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 20000 cases: AGREE 20000/20000, 0 unmodelled
#   seed 2, 20000 cases: AGREE 20000/20000, 0 unmodelled
#   seed 3, 20000 cases: AGREE 20000/20000, 0 unmodelled
#   2026-11-10, same model and build, after the review fixes (no model change):
#   seed 4, 20000 cases: AGREE 20000/20000, 0 unmodelled
#   About 4% of the expected results are Julia exceptions (each op's share is printed); the rest
#   are values. Two disagreements on the first runs were harness gaps, now fixed: Julia shares one
#   `TypeVar` between two `UnionAll`s where the model makes two (the comparator now scopes binder
#   ids), and `Tuple{Union{}}` raised a C-model string instead of an `ErrorException`.
#   Sensitivity (3000 cases, seed 3): with `max = 3` in `unionsplitcost`, `uniontypes` reversed in
#   `_switchtupleunion` and `min(3, ...)` in `typesubtract`, 644 cases disagreed (unionsplitcost
#   209, switchtupleunion 182, switchtupleunionL 142, unionsplitcostSvec 76,
#   isUnionSplitEligible 22, typesubtract 13).

include(joinpath(@__DIR__, "common.jl"))
using .LatticeSer
using Random

abstract type AbsU end
struct CU <: AbsU end
mutable struct MU <: AbsU
    x::Int
end
struct PU{T} <: AbsU
    x::T
end
struct Two
    a::Union{Int,Nothing}
    b::Any
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

const JLT = CC.JLTypeLattice()
const LATTICES = [("typeinf", CC.typeinf_lattice(CC.NativeInterpreter())),
                  ("ipo", CC.ipo_lattice(CC.NativeInterpreter())),
                  ("opt", CC.optimizer_lattice(CC.NativeInterpreter())),
                  ("jltype", JLT)]
pick_lattice(rng) = rand(rng) < 0.55 ? LATTICES[1] : rand(rng, LATTICES)

const LEAF = Any[Int, Int8, Int16, Int32, UInt8, Bool, Float64, Nothing, Missing, Symbol, String,
                 Char, CU, MU, Tuple{}, Union{}, Two, PU{Int}, Vector{Int}, Some{Int}]
const ABSTRACT = Any[Any, Integer, Signed, Real, Number, AbsU, AbstractString, AbstractVector{Int},
                     Type, DataType, Function, Some, PU, Type{Int}, Core.TypeEgal{Int}, Type{Union{}},
                     Union, UnionAll, Core.TypeofBottom, Core.AnyType]
leaftype(rng) = rand(rng) < 0.7 ? rand(rng, LEAF) : rand(rng, ABSTRACT)

# A union of k members drawn from a mix of leaves, abstract types and small tuples.
function randunion(rng, k=rand(rng, 2:6))
    ts = Any[]
    for _ in 1:k
        r = rand(rng)
        push!(ts, r < 0.7 ? rand(rng, LEAF) : r < 0.85 ? rand(rng, ABSTRACT) :
                  r < 0.95 ? (try Tuple{rand(rng, LEAF), rand(rng, LEAF)} catch; Int end) :
                  rand(rng, (Vector{T} where T, Type{Int}, Type{Nothing}, Val{1}, Val{2})))
    end
    return Union{ts...}
end

function randtype(rng, depth=2)
    r = rand(rng)
    if depth <= 0 || r < 0.35
        return leaftype(rng)
    elseif r < 0.6
        return randunion(rng)
    elseif r < 0.8
        return randtuple(rng, depth - 1)
    elseif r < 0.88
        t = randtype(rng, depth - 1)
        return try (rand(rng) < 0.8 ? Type{t} : Core.TypeEgal{t}) catch; Type end
    elseif r < 0.94
        return try rand(rng, (Some, Vector, PU, Ref)){randtype(rng, depth - 1)} catch; Some end
    else
        return rand(rng, UNIONALLS)
    end
end

const UNIONALLS = Any[Tuple{Union{T,Vector{T}},T} where T, Tuple{Union{T,Int},T} where T,
    Tuple{Union{T,Nothing}} where T, Tuple{T,Union{Int,Nothing}} where T<:Integer,
    Tuple{Vector{T},Union{T,Missing}} where T, Tuple{Union{Int,Nothing},Vararg{T}} where T,
    Tuple{Union{Some{T},T}} where T, Tuple{Union{Int8,Int16},Union{T,Bool}} where T<:Real,
    Union{Tuple{T},Tuple{T,T}} where T, Vector{T} where T, Pair{Union{Int,Nothing},T} where T,
    Tuple{Union{Type{T},T}} where T, Tuple{T,T} where T, NTuple{N,Union{Int,Bool}} where N]

# A tuple type with several union parameters, sometimes a `Vararg` tail.
function randtuple(rng, depth=1)
    k = rand(rng, 0:5)
    ps = Any[]
    for _ in 1:k
        r = rand(rng)
        push!(ps, r < 0.45 ? randunion(rng, rand(rng, 2:4)) : r < 0.9 ? leaftype(rng) :
                  randtype(rng, depth - 1))
    end
    if k > 0 && rand(rng) < 0.25
        T = ps[end]
        ps[end] = rand(rng) < 0.7 ? Vararg{T} : Vararg{T, rand(rng, 0:3)}
    end
    return try Tuple{ps...} catch; Tuple{Int,Union{Int,Nothing}} end
end

const VALUES = Any[1, 0, true, false, nothing, :a, (), (1,), (1, :a), (nothing, 2.0), Some(1),
    1.5, 0x01, Int, Union{}, Any, Union{Int,Nothing}, Vector{Int}, Some{T} where T, Type{Int},
    "str", missing, CU(), PU(1), PU(:a), Two(1, 2), Two(nothing, :x), (a=1,), (a=1, b=:c),
    (a=(1, 2),), (a="s",), ((1, 2), 3), ('c', 1), (Int, 1), sin, Val(1), Core.svec()]

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

# A lattice element for an argument list; `slot` biases MustAlias slots so that aliases repeat.
function rand_arg(g::Gen; allow_va=false)
    rng = g.rng
    r = rand(rng)
    if r < 0.38
        return rand(rng) < 0.55 ? randunion(rng) : randtype(rng, 1)
    elseif r < 0.5
        return Core.Const(rand(rng, VALUES))
    elseif r < 0.7
        f = rand(rng) < 0.7 ? randunion(rng, rand(rng, 2:4)) : rand(rng, (Int, Core.Const(1), Any))
        v = rand(rng) < 0.5 ? Any : rand(rng, (Tuple{Any,Any}, Two, Some{Any}))
        return try CC.MustAlias(rand(rng, 1:2), rand(rng, 0:1), v, rand(rng, 1:2), f) catch; f end
    elseif r < 0.76
        return Core.InterMustAlias(rand(rng, 1:2), Any, rand(rng, 1:2), randunion(rng, 2))
    elseif r < 0.82
        return try CC.Conditional(rand(rng, 1:2), 0, rand(rng, (Int, Union{Int,Nothing})),
                                  rand(rng, (Nothing, Union{Int,Missing}))) catch; Bool end
    elseif r < 0.87
        return rand(rng, (Core.PartialStruct(CC.fallback_lattice, Tuple{Int,Any}, Any[Core.Const(1), Any]),
                          Core.PartialStruct(CC.fallback_lattice, Two, Any[Core.Const(1), Union{Int,Nothing}]),
                          Core.PartialStruct(CC.fallback_lattice, Some{Any}, Any[Union{Int,Nothing}])))
    elseif r < 0.89
        return CC.PartialTypeVar(TypeVar(:T, Integer), true, false)
    elseif r < 0.9
        return CC.LimitedAccuracy(randunion(rng, 2), g.causes)
    elseif r < 0.92
        return Core.PartialTask(Int)
    elseif r < 0.95 || !allow_va
        return rand(rng, (Union{}, Any, Union{Int,Nothing}, Union{Int,Nothing,Missing}, Type{Int}))
    else
        T = rand(rng) < 0.6 ? randunion(rng, 2) : rand(rng, (Union{}, Int, Any))
        return rand(rng) < 0.7 ? Vararg{T} : Vararg{T, rand(rng, 0:2)}
    end
end

function rand_argtypes(g::Gen)
    rng = g.rng
    k = rand(rng, 0:6)
    ats = Any[rand_arg(g) for _ in 1:k]
    # repeat a MustAlias, so that alias groups form
    if k >= 2 && rand(rng) < 0.35
        ma = findall(x -> x isa CC.MustAlias, ats)
        if !isempty(ma)
            for _ in 1:rand(rng, 1:2)
                ats[rand(rng, 1:k)] = ats[rand(rng, ma)]
            end
        end
    end
    if k >= 1 && rand(rng) < 0.15
        ats[end] = rand(rng) < 0.7 ? Vararg{randunion(rng, 2)} : Vararg{Union{}}
    end
    return ats
end

fargobj(rng) = (r = rand(rng); r < 0.45 ? Core.SlotNumber(rand(rng, 1:3)) :
                r < 0.8 ? Core.SSAValue(rand(rng, 1:3)) : rand(rng, (:x, 1, GlobalRef(Main, :y))))

function rand_fargs(rng, na)
    r = rand(rng)
    r < 0.35 && return nothing
    k = r < 0.95 ? na : max(na - 1, 0)
    return Any[fargobj(rng) for _ in 1:k]
end

function sfargs(fargs)
    fargs === nothing && return "null"
    return "[" * join([x isa Core.SlotNumber ? "{\"slot\":$(x.id)}" :
                       x isa Core.SSAValue ? "{\"ssa\":$(x.id)}" : "{\"other\":true}" for x in fargs], ",") * "]"
end

jint(i::Int) = string(i)
selts(s, xs) = "[" * join([selt(s, x) for x in xs], ",") * "]"
svals(s, ts) = "[" * join([sval(s, t) for t in ts], ",") * "]"

function typename_sym(@nospecialize(t))
    r = CC._typename(t)
    r === Union{} && return :bottom
    r === Core.TypeName && return :typename
    return Symbol(LatticeSer.tnname((r::Core.Const).val))
end

# `b` for `typesubtract(a, b)`: a member, a tuple of members, or something unrelated.
function subtrahend(rng, @nospecialize(a))
    r = rand(rng)
    try
        if a isa DataType && a.name === Tuple.name && !isempty(a.parameters) && r < 0.55
            ps = Any[]
            for p in a.parameters
                q = Base.unwrapva(p)
                m = q isa Union ? rand(rng, Base.uniontypes(q)) : q
                push!(ps, rand(rng) < 0.75 ? m : (rand(rng) < 0.5 ? Any : rand(rng, LEAF)))
            end
            Base.isvarargtype(a.parameters[end]) && rand(rng) < 0.5 && (ps[end] = Vararg{ps[end]})
            return Tuple{ps...}
        elseif a isa Union && r < 0.8
            return rand(rng, Base.uniontypes(a))
        elseif r < 0.7
            return rand(rng) < 0.5 ? randunion(rng, 2) : leaftype(rng)
        end
    catch
    end
    return rand(rng) < 0.5 ? randtype(rng, 2) : rand(rng, (Tuple{Any,Vararg{Any}}, Tuple{Vararg{Any}}, Type, Tuple{Union{Int,Nothing}}))
end

function gen_case(g::Gen, s::Ser, id::Int, io::IO)
    rng = g.rng
    r = rand(rng)
    lname = "typeinf"
    if r < 0.16
        op = "unionsplitcost"
        lname, L = pick_lattice(rng)
        ats = rand_argtypes(g); fa = rand_fargs(rng, length(ats))
        args = [selts(s, ats), sfargs(fa)]
        exp = expected(s, :val, () -> CC.unionsplitcost(L, ats; fargs=fa))
    elseif r < 0.22
        op = "unionsplitcostSvec"
        lname, L = rand(rng) < 0.7 ? LATTICES[4] : pick_lattice(rng)
        t = randtuple(rng, 1)
        ps = collect(Any, t.parameters)
        args = [svals(s, ps)]
        exp = expected(s, :val, () -> CC.unionsplitcost(L, Core.svec(ps...)))
    elseif r < 0.32
        op = "isUnionSplitEligible"
        lname, L = pick_lattice(rng)
        ats = rand_argtypes(g); fa = rand_fargs(rng, length(ats))
        m = rand(rng) < 0.9 ? rand(rng, 0:8) : rand(rng, (typemax(Int), -1, 64))
        args = [selts(s, ats), jint(m), sfargs(fa)]
        exp = expected(s, :bool, () -> CC.is_union_split_eligible(L, ats, m; fargs=fa))
    elseif r < 0.42
        op = "switchtupleunion"
        t = rand(rng) < 0.6 ? randtuple(rng, 1) : rand(rng) < 0.6 ? rand(rng, UNIONALLS) : randtype(rng, 2)
        args = [sval(s, t)]
        exp = expected(s, :vals, () -> CC.switchtupleunion(t))
    elseif r < 0.53
        op = "switchtupleunionL"
        lname, L = pick_lattice(rng)
        ats = rand_argtypes(g)
        length(ats) > 4 && (ats = ats[1:4])   # keep the cartesian product small
        fa = rand_fargs(rng, length(ats))
        args = [selts(s, ats), sfargs(fa)]
        exp = expected(s, :eltss, () -> CC.switchtupleunion(L, ats; fargs=fa))
    elseif r < 0.58
        op = "computeAliasGroups"
        ats = rand_argtypes(g); na = length(ats)
        fa = rand_fargs(rng, na)
        useat = rand(rng) < 0.8
        args = [jint(na), sfargs(fa), useat ? selts(s, ats) : "null"]
        exp = expected(s, :ints_or_nothing, () -> CC.compute_alias_groups(na, fa, useat ? ats : nothing))
    elseif r < 0.67
        op = "argtypesToType"
        ats = rand_argtypes(g)
        if !isempty(ats) && rand(rng) < 0.15
            ats[rand(rng, 1:length(ats))] = rand(rng) < 0.5 ? Vararg{Int} : Vararg{Union{}}
        end
        args = [selts(s, ats)]
        exp = expected(s, :val, () -> CC.argtypes_to_type(ats))
    elseif r < 0.79
        op = "typesubtract"
        a = rand(rng) < 0.6 ? randtuple(rng, 1) : randtype(rng, 2)
        b = subtrahend(rng, a)
        m = rand(rng, (0, 1, 2, 3, 4, 4, 4, 6, 8, 16))
        args = [sval(s, a), sval(s, b), jint(m)]
        exp = expected(s, :val, () -> CC.typesubtract(a, b, m))
    elseif r < 0.82
        op = "unioncomplexity"
        t = rand(rng) < 0.5 ? randtuple(rng, 1) : randtype(rng, 3)
        args = [sval(s, t)]
        exp = expected(s, :val, () -> CC.unioncomplexity(t))
    elseif r < 0.84
        op = "tupleTailElem"
        init = rand(rng) < 0.7 ? Union{} : randtype(rng, 1)
        ct = Any[rand(rng) < 0.5 ? randunion(rng, rand(rng, 2:3)) : randtype(rng, 1) for _ in 1:rand(rng, 1:4)]
        rand(rng) < 0.3 && (ct[end] = Vararg{ct[end]})
        args = [selt(s, init), svals(s, ct)]
        exp = expected(s, :val, () -> CC.tuple_tail_elem(CC.fallback_lattice, init, ct))
    else
        op = rand(rng, ("isnotbrokensubtype", "compatibleVatuple", "isknownlength", "isTypeDataType",
                        "hasExtendedInfo", "validTypeofTparam", "validTparam", "unionallDepth",
                        "unwraptvUb", "unwraptvLb", "typename", "isImmutableArgtype",
                        "hasConcreteSubtype"))
        if op == "isnotbrokensubtype"
            a = rand(rng) < 0.5 ? rand(rng, ABSTRACT) : randtype(rng, 1)
            b = rand(rng) < 0.5 ? rand(rng, ABSTRACT) : randtype(rng, 1)
            args = [sval(s, a), sval(s, b)]
            exp = expected(s, :bool, () -> CC.isnotbrokensubtype(a, b))
        elseif op == "compatibleVatuple"
            a = randtuple(rng); b = randtuple(rng)
            rand(rng) < 0.1 && (a = rand(rng, (Some{Int}, Tuple{}, Int)))
            args = [sval(s, a), sval(s, b)]
            exp = expected(s, :bool, () -> CC.compatible_vatuple(a, b))
        elseif op == "isknownlength"
            a = rand(rng) < 0.85 ? randtuple(rng) : randtype(rng, 1)
            rand(rng) < 0.2 && (a = rand(rng, (Tuple{Int,Vararg{Int,N}} where N, NTuple{N,Int} where N)))
            a = rand(rng) < 0.15 ? Base.unwrap_unionall(a) : a
            args = [sval(s, a)]
            exp = expected(s, :bool, () -> CC.isknownlength(a))
        elseif op == "isTypeDataType" || op == "unionallDepth" || op == "typename"
            t = rand(rng) < 0.3 ? rand(rng, ABSTRACT) : rand(rng) < 0.3 ? rand(rng, UNIONALLS) : randtype(rng, 2)
            rand(rng) < 0.1 && (t = TypeVar(:S, Integer))
            rand(rng) < 0.05 && (t = Vararg{Int})
            args = [sval(s, t)]
            exp = op == "isTypeDataType" ? expected(s, :bool, () -> CC.isTypeDataType(t)) :
                  op == "unionallDepth" ? expected(s, :val, () -> CC.unionall_depth(t)) :
                  expected(s, :val, () -> typename_sym(t))
        elseif op == "hasExtendedInfo" || op == "isImmutableArgtype"
            x = rand(rng) < 0.7 ? rand_arg(g; allow_va=true) : rand(rng, (TypeVar(:S, Int), Union{T,Int} where T,
                Union{Vector{T},Int} where T, MU, Union{MU,Int}, Union{CU,Nothing}, Type{Int}, Union{Int,Type{Int}}))
            args = [selt(s, x)]
            exp = op == "hasExtendedInfo" ? expected(s, :bool, () -> CC.has_extended_info(x)) :
                  expected(s, :bool, () -> CC.is_immutable_argtype(x))
        elseif op == "validTypeofTparam" || op == "hasConcreteSubtype"
            t = rand(rng) < 0.5 ? typeof(rand(rng, VALUES)) : randtype(rng, 1)
            args = [sval(s, t)]
            exp = op == "validTypeofTparam" ? expected(s, :bool, () -> CC.valid_typeof_tparam(t)) :
                  expected(s, :bool, () -> CC.has_concrete_subtype(t))
        elseif op == "validTparam"
            x = rand(rng, VALUES)
            args = [sval(s, x)]
            exp = expected(s, :bool, () -> CC.valid_tparam(x))
        else
            v = rand(rng) < 0.6 ? TypeVar(:S, rand(rng) < 0.5 ? Integer : TypeVar(:R, Real)) : randtype(rng, 1)
            v isa TypeVar && rand(rng) < 0.4 && (v = TypeVar(:Q, rand(rng, (Int, TypeVar(:P, Signed))), Any))
            args = [sval(s, v)]
            exp = op == "unwraptvUb" ? expected(s, :val, () -> CC.unwraptv_ub(v)) :
                  expected(s, :val, () -> CC.unwraptv_lb(v))
        end
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
        for id in 1:n
            ops[id] = gen_case(g, s, id, io)
        end
    end
    # How many expected results per op are Julia exceptions, and which.
    errs = Dict{String,Dict{String,Int}}()
    for line in eachline(casefile)
        m = match(r"^\{\"id\":\"?(\d+)\"?.*\"exp\":\{\"err\":\"(\w+)\"", line)
        m === nothing && continue
        d = get!(errs, ops[parse(Int, m[1])], Dict{String,Int}())
        d[m[2]] = get(d, m[2], 0) + 1
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
        println(rpad(op, 28), " agree=", st[1], " unmodelled=", st[2], " disagree=", st[3],
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
