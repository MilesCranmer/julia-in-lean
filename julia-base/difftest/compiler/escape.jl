# Differential test of the Lean model of Compiler/src/ssair/EscapeAnalysis.jl (and the union-find
# of Compiler/src/ssair/disjoint_set.jl) against the pinned Julia
# (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA difftest/compiler/escape.jl --cases 20000 --seed 1
#
# Three kinds of case:
#
#   lat   the lattice on generated `EscapeInfo`s: `==`, `⊑ₑ`, `⊏ₑ`, `⋤ₑ`, `⊔ₑ`,
#         `merge_alias_info`, the queries (`has_no_escape`, `has_arg_escape`,
#         `has_return_escape` with and without `pc`, `has_thrown_escape` with and without `pc`,
#         `has_all_escape`, `ArgEscapeInfo`, `has_no_escape ∘ ignore_argescape`), the four
#         `ignore_*` constructors, `from_interprocedural` and the `ArgEscapeInfo` queries.
#         Inputs are biased to the edges: `⊥`, `⊤` and its egal copies, an `EscapeInfo` equal to
#         `⊥` but not egal to it, the constant `BitSet`s and fresh sets with the same contents
#         (`BitSet(-1)`, `BitSet(-1:0)`, empty), `Liveness` objects shared between `x` and `y`,
#         `IndexableFields` with no fields against `Unindexable`, `y` built from `x` (`x` itself,
#         `x ⊔ₑ z`, one field raised) so that `⊑ₑ` holds often.
#   ir    `analyze_escapes` on generated `IRCode`: random statements of every kind the analysis
#         dispatches on (`:new`/`:splatnew` of 0- to 3-field structs, builtin calls with and
#         without handlers, intrinsics, generic calls, `:invoke` with a random escape cache
#         (`true`, `false`, or an `ArgEscapeCache` with aliased and escaping arguments, vararg
#         methods), `:foreigncall` well and badly formed, `:foreignglobal`,
#         `:gc_preserve_begin`/`_end`, `:throw_undef_if_not`, meta heads, unknown heads,
#         `EnterNode`s with catch blocks, `ReturnNode`, `PhiNode`/`PhiCNode` with undefined
#         values, `PiNode`, `UpsilonNode`, global loads, `GlobalRef` and literal operands), random
#         statement types (identity-free or not, `Const`, unions, `Module`) and nothrow flags.
#   real  `analyze_escapes` on `Base.code_ircode` of small functions (allocations, field
#         stores and loads, phis, `try`/`catch`, finalizers, `GC.@preserve`, `ccall`, closures),
#         after several optimizer passes, with the native or a random escape cache.
#
# For `ir` and `real` the whole final state is compared: every `EscapeInfo` (with the identity
# of the `Liveness`/`ThrownEscape` constants), the union-find `parents` and `ranks`, the alias
# partition, `getaliases` of every index in turn, and `ArgEscapeCache(estate)`. Errors are
# compared by exception type. The type-dependent queries the analysis makes are computed here
# with the pinned Compiler and passed to the model (see the model's docstring).
#
# Prints the agreement per kind (an `-err-<Exception>` suffix when the pinned analysis threw), and
# `AGREE k/n`. `--debug 1` also prints the IR of the first `--show` disagreements.
#
# Runs (seed, cases, agreement):
#   2026-11-10, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 20000 cases: AGREE 20000/20000 (lat 9054, ir 8622 of which 584 throw, real 2324
#                        of which 11 throw)
#   seed 2, 20000 cases: AGREE 20000/20000 (lat 9105, ir 8518 of which 578 throw, real 2377
#                        of which 18 throw)
#   seed 3, 20000 cases: AGREE 20000/20000 (lat 8973, ir 8574 of which 572 throw, real 2453
#                        of which 20 throw)
#   seed 6, 5000 cases (2026-11-10, after the proof-only review fixes; model unchanged):
#                        AGREE 5000/5000
#   The `real` cases that throw all throw `BoundsError`. The ones inspected are at
#   EscapeAnalysis.jl:1020: a random `ArgEscapeCache` for a vararg callee aliases the vararg
#   slot, and the `:invoke` passes fewer arguments than the method's `nargs` (a lead, not yet
#   shown with a cache the native interpreter makes).

include(joinpath(@__DIR__, "common.jl"))
using .CFGSer: ja, jo, errj
using .EscSer
using Random

const CC = Base.Compiler
const EA = CC.EscapeAnalysis

function parse_args(args)
    opts = Dict("cases" => "2000", "seed" => "1", "exe" => joinpath(@__DIR__, "..", "..",
                ".lake", "build", "bin", "compilerdiff"), "show" => "20")
    i = 1
    while i <= length(args)
        a = args[i]
        startswith(a, "--") || error("bad argument $a")
        opts[a[3:end]] = args[i+1]
        i += 2
    end
    return opts
end

jb(b::Bool) = b ? "true" : "false"
jints(xs) = ja(sort!(collect(Int, xs)))
jstr(s) = "\"" * s * "\""

function tryv(f)
    try
        return jo("v" => f())
    catch e
        e isa InterruptException && rethrow()
        return errj(e)
    end
end

## Lattice cases

mutable struct LatCtx
    hs::Vector{BitSet}
    ids::IdDict{BitSet,Int}
    pool::Vector{BitSet}
end
LatCtx() = LatCtx(BitSet[], IdDict{BitSet,Int}(), BitSet[])

function enc_in_live(c::LatCtx, l::BitSet)
    l === EA.TOP_LIVENESS && return "\"T\""
    l === EA.BOT_LIVENESS && return "\"B\""
    l === EA.ARG_LIVENESS && return "\"A\""
    k = get!(c.ids, l) do
        push!(c.hs, l)
        length(c.hs) - 1
    end
    return jo("h" => string(k))
end

enc_in_info(c::LatCtx, i::EA.EscapeInfo) =
    jo("a" => jb(i.Analyzed), "r" => jb(i.ReturnEscape), "t" => enc_thrown(i.ThrownEscape),
       "al" => enc_alias(i.AliasInfo), "l" => enc_in_live(c, i.Liveness))

function rand_ainfo(rng)
    s = EA.AInfo()
    for _ in 1:rand(rng, 0:3)
        push!(s, rand(rng, Bool) ? EA.LocalUse(rand(rng, 1:4)) : EA.LocalDef(rand(rng, 1:4)))
    end
    return s
end

function rand_alias(rng)
    r = rand(rng)
    r < 0.25 && return false
    r < 0.45 && return true
    r < 0.75 && return EA.IndexableFields(EA.AInfo[rand_ainfo(rng) for _ in 1:rand(rng, 0:3)])
    return EA.Unindexable(rand_ainfo(rng))
end

rand_subset(rng, r, p=0.35) = BitSet(filter(_ -> rand(rng) < p, collect(r)))

function rand_thrown(rng)
    r = rand(rng)
    r < 0.35 && return EA.BOT_THROWN_ESCAPE
    r < 0.50 && return EA.TOP_THROWN_ESCAPE
    r < 0.58 && return BitSet()
    r < 0.66 && return BitSet(-1)
    r < 0.70 && return union!(BitSet(-1), rand_subset(rng, 1:5))
    return rand_subset(rng, 1:5)
end

function rand_live(rng, c::LatCtx)
    r = rand(rng)
    r < 0.22 && return EA.BOT_LIVENESS
    r < 0.36 && return EA.TOP_LIVENESS
    r < 0.46 && return EA.ARG_LIVENESS
    r < 0.58 && !isempty(c.pool) && return rand(rng, c.pool)
    l = r < 0.63 ? BitSet(-1:0) : r < 0.68 ? BitSet() : r < 0.73 ? BitSet(0) :
        rand_subset(rng, 0:5)
    push!(c.pool, l)
    return l
end

function rand_info(rng, c::LatCtx)
    r = rand(rng)
    pc = rand(rng, 1:5)
    r < 0.07 && return EA.⊥
    r < 0.14 && return EA.⊤
    r < 0.18 && return EA.EscapeInfo(EA.⊤, true)
    r < 0.22 && return EA.NoEscape()
    r < 0.26 && return EA.ArgEscape()
    r < 0.30 && return (x = EA.ReturnEscape(pc); push!(c.pool, x.Liveness); x)
    r < 0.33 && return EA.AllReturnEscape()
    r < 0.37 && return EA.ThrownEscape(pc)
    r < 0.40 && return EA.EscapeInfo(false, false, BitSet(), false, BitSet())
    r < 0.42 && return EA.EscapeInfo(true, true, BitSet(-1), true, BitSet(-1:0))
    return EA.EscapeInfo(rand(rng) < 0.8, rand(rng, Bool), rand_thrown(rng), rand_alias(rng),
                         rand_live(rng, c))
end

function raise(rng, x::EA.EscapeInfo, c::LatCtx)
    r = rand(rng)
    r < 0.25 && return EA.EscapeInfo(x; ReturnEscape=true)
    r < 0.45 && return EA.EscapeInfo(x, rand_alias(rng))
    r < 0.65 && return EA.EscapeInfo(x; ThrownEscape=union(x.ThrownEscape, rand_subset(rng, 1:5)))
    r < 0.80 && return EA.EscapeInfo(x; Liveness=rand_live(rng, c))
    return EA.EscapeInfo(x; Analyzed=true)
end

const LAT_OPS = ["eq", "sq", "sq", "sqs", "ntsq", "join", "join", "q", "mai", "fi"]

function gen_lat(rng, id, io)
    c = LatCtx()
    x = rand_info(rng, c)
    r = rand(rng)
    y = r < 0.15 ? x : r < 0.30 ? EA.:⊔ₑ(x, rand_info(rng, c)) :
        r < 0.38 ? EA.:⊔ₑ(rand_info(rng, c), x) : r < 0.55 ? raise(rng, x, c) :
        rand_info(rng, c)
    if rand(rng) < 0.5
        x, y = y, x
    end
    op = rand(rng, LAT_OPS)
    pc = rand(rng, -1:6)
    bits = rand(rng, 0:7)
    xs = enc_in_info(c, x); ys = enc_in_info(c, y)
    hs = ja([jints(s) for s in c.hs])
    xl, yl = x.Liveness, y.Liveness
    exp = if op == "eq"
        jo("v" => jb(x == y))
    elseif op == "sq"
        tryv(() -> jb(EA.:⊑ₑ(x, y)))
    elseif op == "sqs"
        tryv(() -> jb(EA.:⊏ₑ(x, y)))
    elseif op == "ntsq"
        tryv(() -> jb(EA.:⋤ₑ(x, y)))
    elseif op == "join"
        jo("v" => enc_info(EA.:⊔ₑ(x, y), xl, yl))
    elseif op == "q"
        qs = [jb(EA.has_no_escape(x)), jb(EA.has_arg_escape(x)), jb(EA.has_return_escape(x)),
              jb(EA.has_return_escape(x, pc)), jb(EA.has_thrown_escape(x)),
              jb(EA.has_thrown_escape(x, pc)), tryv(() -> jb(EA.has_all_escape(x))),
              string(EA.ArgEscapeInfo(x).escape_bits),
              jb(EA.has_no_escape(EA.ignore_argescape(x)))]
        igs = [enc_info(EA.ignore_argescape(x), xl), enc_info(EA.ignore_thrownescapes(x), xl),
               enc_info(EA.ignore_aliasinfo(x), xl), enc_info(EA.ignore_liveness(x), xl)]
        jo("v" => ja(qs), "ig" => ja(igs))
    elseif op == "mai"
        jo("v" => enc_alias(EA.merge_alias_info(x.AliasInfo, y.AliasInfo)))
    else
        a = EA.ArgEscapeInfo(UInt8(bits))
        jo("v" => enc_info(EA.from_interprocedural(a, pc)),
           "b" => ja([jb(EA.has_no_escape(a)), jb(EA.has_all_escape(a)),
                      jb(EA.has_return_escape(a)), jb(EA.has_thrown_escape(a))]))
    end
    println(io, jo("id" => string(id), "ea" => "\"lat\"", "o" => jstr(op), "h" => hs, "x" => xs,
                   "y" => ys, "pc" => string(pc), "bits" => string(bits), "exp" => exp))
    return "lat-" * op
end

## IR cases

mutable struct M0 end
mutable struct M1; x; end
mutable struct M2; x::Any; y::Int; end
mutable struct M3; a; b; c; end
struct S0 end
struct S2; a; b; end
struct SP{T}; a::T; b::Any; end
const GXR = Ref{Any}(nothing)
global GX::Any = 1

@noinline fid(x) = x
@noinline fnone(x) = nothing
@noinline fesc(x) = (GXR[] = x; nothing)
@noinline fva(x, ys...) = ys
@noinline f2(x, y) = (x, y)

const STRUCTS = Any[M0, M1, M2, M3, S0, S2, SP{Int}, SP, Base.RefValue{Any}, Tuple{Any,Any}]
const TYPES = Any[Any, Any, Int, String, Symbol, Nothing, Bool, M0, M1, M1, M2, M3, S0, S2,
    SP{Int}, SP, Base.RefValue{Any}, Ref{Any}, Tuple{Any,Any}, Tuple{Int}, Tuple{}, Tuple,
    Tuple{Vararg{Any}}, NTuple{3,Any}, Union{M1,Nothing}, Union{M1,M2}, Union{S2,M2}, Module,
    Vector{Any}, Memory{Any}, CC.Const(1), CC.Const(true), CC.Const(false), CC.Const(nothing),
    CC.Const(Main), CC.Const(:x), Type{M1}, DataType, Union{}]

# The functions `escape_builtin!` has methods for. `EscapeAnalysis` is a `baremodule` that uses
# `Core`, so these are the `Core` objects (`Base.ifelse` is a different, generic function).
const BUILTIN_NAMES = IdDict{Any,String}(Core.isa => "isa", Core.typeof => "typeof",
    Core.sizeof => "sizeof", Core.:(===) => "===", Core.donotdelete => "donotdelete",
    Core.isdefined => "isdefined", Core.throw => "throw",
    Core.throw_methoderror => "throw_methoderror", Core.ifelse => "ifelse",
    Core.typeassert => "typeassert", Core.tuple => "tuple", Core.getfield => "getfield",
    Core.setfield! => "setfield!", Core.finalizer => "finalizer")

const CALLEES = Any[
    (GlobalRef(Core, :getfield), 8), (GlobalRef(Core, :setfield!), 6),
    (GlobalRef(Core, :tuple), 4), (GlobalRef(Core, :ifelse), 2),
    (GlobalRef(Core, :typeassert), 2), (GlobalRef(Core, :isa), 1),
    (GlobalRef(Core, :typeof), 1), (GlobalRef(Core, :(===)), 1),
    (GlobalRef(Core, :isdefined), 1), (GlobalRef(Core, :throw), 1),
    (GlobalRef(Core, :sizeof), 1), (GlobalRef(Core, :donotdelete), 1),
    (GlobalRef(Core, :finalizer), 2), (GlobalRef(Core, :throw_methoderror), 1),
    (GlobalRef(Core, :memoryrefnew), 1), (GlobalRef(Core, :_apply_iterate), 1),
    (GlobalRef(Core, :svec), 1), (GlobalRef(Core, :swapfield!), 1),
    (GlobalRef(Core.Intrinsics, :add_int), 1), (GlobalRef(Core.Intrinsics, :bitcast), 1),
    (GlobalRef(Base, :println), 1), (GlobalRef(Base, :+), 1), (:ssa, 1)]
const CALLEE_W = cumsum([w for (_, w) in CALLEES])
pick_callee(rng) = CALLEES[searchsortedfirst(CALLEE_W, rand(rng, 1:CALLEE_W[end]))][1]

const MIS = let
    mk(f, tt) = CC.specialize_method(which(f, tt), Tuple{typeof(f), tt...}, Core.svec())
    Any[(mk(fid, (Any,)), GlobalRef(Main, :fid)), (mk(fnone, (Any,)), GlobalRef(Main, :fnone)),
        (mk(fesc, (Any,)), GlobalRef(Main, :fesc)), (mk(fva, (Any, Any, Any)), GlobalRef(Main, :fva)),
        (mk(f2, (Any, Any)), GlobalRef(Main, :f2))]
end

function fake_cache(rng, nargs::Int)
    st = EA.EscapeState(nargs, 0)
    for i in 1:nargs
        r = rand(rng)
        st.escapes[i] = r < 0.2 ? EA.⊤ :
            EA.EscapeInfo(EA.ArgEscape(); ReturnEscape=rand(rng, Bool),
                          ThrownEscape=rand(rng, Bool) ? BitSet(3) : EA.BOT_THROWN_ESCAPE)
    end
    for _ in 1:rand(rng, 0:2)
        nargs ≥ 2 && union!(st.aliasset, rand(rng, 1:nargs), rand(rng, 1:nargs))
    end
    return EA.ArgEscapeCache(st)
end

# A memoised `get_escape_cache`: one random answer per callee per case.
struct RandCache
    rng::Random.Xoshiro
    native::Any
    memo::IdDict{Any,Any}
end
function (c::RandCache)(codeinst)
    get!(c.memo, codeinst) do
        mi = codeinst isa Core.MethodInstance ? codeinst : codeinst.def
        r = rand(c.rng)
        if r < 0.25
            true
        elseif r < 0.45
            false
        elseif r < 0.6 && c.native !== nothing
            c.native(codeinst)
        else
            fake_cache(c.rng, Int((mi.def::Method).nargs))
        end
    end
end

function gen_opnd(rng, nargs, n, allocs)
    r = rand(rng)
    if r < 0.30 && !isempty(allocs)
        return Core.SSAValue(rand(rng, allocs))
    elseif r < 0.55
        return Core.SSAValue(rand(rng, 1:n))
    elseif r < 0.78
        return Core.Argument(rand(rng, 1:nargs))
    elseif r < 0.86
        return GlobalRef(Main, :GX)
    else
        return rand(rng, Any[1, nothing, :x, QuoteNode(:y), "s", 2.0, true])
    end
end

function gen_fld(rng, nargs, n, allocs)
    r = rand(rng)
    r < 0.45 && return rand(rng, 1:3)
    r < 0.75 && return rand(rng, Any[:x, :y, :a, :b, :zz])
    r < 0.85 && return rand(rng, Any[QuoteNode(:x), 0, 5, 1.0])
    return gen_opnd(rng, nargs, n, allocs)
end

const KINDS = [(:new, 12), (:call, 30), (:invoke, 5), (:fc, 3), (:fg, 1), (:tu, 1), (:skip, 3),
    (:gpb, 2), (:gpe, 2), (:cons, 2), (:enter, 2), (:ret, 5), (:phi, 6), (:pi, 3), (:phic, 2),
    (:ups, 2), (:gl, 2), (:ssa, 3), (:arg, 2), (:goto, 2), (:splat, 1)]
const KIND_W = cumsum([w for (_, w) in KINDS])
pick_kind(rng) = KINDS[searchsortedfirst(KIND_W, rand(rng, 1:KIND_W[end]))][1]

function gen_ir(rng)
    nargs = rand(rng, 1:4)
    n = rand(rng, 2:18)
    kinds = [pick_kind(rng) for _ in 1:n]
    allocs = [i for i in 1:n if kinds[i] in (:new, :splat)]
    gpbs = [i for i in 1:n if kinds[i] === :gpb]
    # Basic blocks: a random partition of 1:n.
    cuts = sort!(unique!([1; [i for i in 2:n if rand(rng) < 0.25]]))
    ranges = [cuts[k]:(k < length(cuts) ? cuts[k+1] - 1 : n) for k in 1:length(cuts)]
    blocks = CC.BasicBlock[CC.BasicBlock(CC.StmtRange(first(r), last(r)), Int[], Int[]) for r in ranges]
    cfg = CC.CFG(blocks, Int[first(r) for r in ranges[2:end]])
    stmts = CC.InstructionStream(n)
    op() = gen_opnd(rng, nargs, n, allocs)
    ops(k) = Any[op() for _ in 1:k]
    for pc in 1:n
        k = kinds[pc]
        T = rand(rng, TYPES)
        st = if k === :new
            S = rand(rng, STRUCTS)
            rand(rng) < 0.8 && (T = S)
            Expr(:new, S, ops(rand(rng, 0:4))...)
        elseif k === :splat
            S = rand(rng, STRUCTS)
            rand(rng) < 0.8 && (T = S)
            Expr(:splatnew, S, op())
        elseif k === :call
            f = pick_callee(rng)
            f === :ssa && (f = Core.SSAValue(rand(rng, 1:n)))
            name = f isa GlobalRef ? f.name : :none
            args = if name === :getfield
                Any[op(), gen_fld(rng, nargs, n, allocs), ops(rand(rng) < 0.85 ? 0 : 1)...]
            elseif name === :setfield!
                Any[op(), gen_fld(rng, nargs, n, allocs), op(), ops(rand(rng) < 0.85 ? 0 : 1)...]
            elseif name === :ifelse
                Any[rand(rng) < 0.5 ? rand(rng, Bool) : op(), op(), op()]
            elseif name === :typeassert
                Any[op(), rand(rng, Any[M1, Any, Int])]
            elseif name === :finalizer
                Any[op(), op(), ops(rand(rng, 0:1))...]
            else
                ops(rand(rng, 0:3))
            end
            if rand(rng) < 0.05 && !isempty(args)
                pop!(args)
            end
            name === :tuple && rand(rng) < 0.7 && (T = Tuple{Any,Any})
            Expr(:call, f, args...)
        elseif k === :invoke
            mi, g = rand(rng, MIS)
            Expr(:invoke, mi, g, ops(rand(rng, 0:4))...)
        elseif k === :fc
            nat = rand(rng, 0:3)
            ats = Core.svec([rand(rng, Any[Any, Int, Ptr{Cvoid}]) for _ in 1:nat]...)
            name = rand(rng, Any[QuoteNode(:foo), Expr(:tuple, QuoteNode(:f), "lib"), op()])
            args = Any[name, Any, rand(rng) < 0.05 ? Any[Any] : ats, 0, QuoteNode(:ccall),
                       ops(nat)..., ops(rand(rng, 0:2))...]
            if rand(rng) < 0.08
                args = args[1:rand(rng, 1:min(5, length(args)))]
            elseif rand(rng) < 0.05 && length(args) > 6
                pop!(args)
            end
            Expr(:foreigncall, args...)
        elseif k === :fg
            Expr(:foreignglobal, ops(rand(rng) < 0.85 ? 1 : 2)...)
        elseif k === :tu
            Expr(:throw_undef_if_not, rand(rng) < 0.5 ? :x : op(), op())
        elseif k === :skip
            rand(rng, Any[Expr(:meta, :inline), Expr(:boundscheck), Expr(:loopinfo),
                Expr(:leave, op()), Expr(:the_exception), Expr(:pop_exception, op()),
                Expr(:static_parameter, 1), Expr(:copyast, QuoteNode(:x)), Expr(:isdefined, :x),
                nothing, 1])
        elseif k === :gpb
            Expr(:gc_preserve_begin, ops(rand(rng, 0:3))...)
        elseif k === :gpe
            r = rand(rng)
            if r < 0.9 && !isempty(gpbs)
                Expr(:gc_preserve_end, Core.SSAValue(rand(rng, gpbs)))
            elseif r < 0.9
                Expr(:gc_preserve_begin, ops(rand(rng, 0:3))...)
            elseif r < 0.94
                Expr(:gc_preserve_end, Core.SSAValue(rand(rng, 1:n)))
            elseif r < 0.97
                Expr(:gc_preserve_end, op(), op())
            else
                Expr(:gc_preserve_end, 1)
            end
        elseif k === :cons
            Expr(rand(rng, [:cfunction, :foo, :new_opaque_closure, :method]), ops(rand(rng, 0:3))...)
        elseif k === :enter
            Core.EnterNode(rand(rng) < 0.85 ? rand(rng, 1:length(blocks)) : 0)
        elseif k === :ret
            rand(rng) < 0.9 ? Core.ReturnNode(op()) : Core.ReturnNode()
        elseif k === :phi
            m = rand(rng, 1:3)
            vals = Vector{Any}(undef, m)
            for i in 1:m
                rand(rng) < 0.85 && (vals[i] = op())
            end
            Core.PhiNode(Int32[1:m;], vals)
        elseif k === :pi
            Core.PiNode(op(), rand(rng, TYPES))
        elseif k === :phic
            m = rand(rng, 1:3)
            vals = Vector{Any}(undef, m)
            for i in 1:m
                rand(rng) < 0.85 && (vals[i] = op())
            end
            Core.PhiCNode(vals)
        elseif k === :ups
            rand(rng) < 0.85 ? Core.UpsilonNode(op()) : Core.UpsilonNode()
        elseif k === :gl
            GlobalRef(Main, :GX)
        elseif k === :ssa
            Core.SSAValue(rand(rng, 1:n))
        elseif k === :arg
            Core.Argument(rand(rng, 1:nargs))
        else
            rand(rng) < 0.5 ? Core.GotoNode(1) : Core.GotoIfNot(op(), 1)
        end
        stmts.stmt[pc] = st
        stmts.type[pc] = T
        stmts.flag[pc] = rand(rng) < 0.5 ? CC.IR_FLAG_NOTHROW : CC.IR_FLAG_NULL
    end
    argtypes = Any[rand(rng, TYPES) for _ in 1:nargs]
    w = Base.get_world_counter()
    ir = CC.IRCode(stmts, cfg, CC.DebugInfoStream(stmts.line), argtypes, Expr[], CC.VarState[],
                   CC.WorldRange(w, w))
    return ir, nargs
end

opsj(v) = ja(map(enc_opnd, v))

function enc_cache(c)
    c isa Bool && return jb(c)
    c = c::EA.ArgEscapeCache
    return jo("e" => ja([string(a.escape_bits) for a in c.argescapes]),
              "al" => ja([ja([a.aidx, a.bidx]) for a in c.argaliases]))
end

function enc_stmt(ir, pc, 𝕃ₒ, cachef)
    stmt = ir[Core.SSAValue(pc)][:stmt]
    if stmt isa Expr
        h = stmt.head; a = stmt.args
        if h === :call
            f = CC.singleton_type(CC.argextype(a[1], ir))
            fk = f isa Core.IntrinsicFunction ? "i" :
                 f isa Core.Builtin ? get(BUILTIN_NAMES, f, "other") : "o"
            mi = length(a) ≥ 2 && Base.hasintersect(CC.argextype_widened(a[2], ir), Module)
            of = "null"; ox = "null"
            if length(a) ≥ 3
                typ = CC.argextype_widened(a[2], ir)
                nf = CC.fieldcount_noerror(typ)
                nf === nothing || (of = string(nf))
                if typ isa DataType
                    fx = CC.try_compute_fieldidx(typ, CC.try_compute_field(ir, a[3]))
                    fx === nothing || (ox = string(fx))
                end
            end
            sn = fk == "setfield!" && length(a) == 4 &&
                CC.setfield!_nothrow(𝕃ₒ, CC.argextype(a[2], ir), CC.argextype(a[3], ir),
                                     CC.argextype(a[4], ir))
            cc = "null"
            if length(a) ≥ 2
                ct = CC.argextype(a[2], ir)
                ct isa CC.Const && ct.val isa Bool && (cc = jb(ct.val))
            end
            return jo("k" => "\"call\"", "a" => opsj(a), "fk" => jstr(fk), "mi" => jb(mi),
                      "of" => of, "ox" => ox, "sn" => jb(sn), "cc" => cc)
        elseif h === :invoke
            ci = a[1]
            m = ci isa Core.MethodInstance ? ci : ci.def
            c = cachef(ci)
            mn = c isa EA.ArgEscapeCache ? Int((m.def::Method).nargs) : 0
            return jo("k" => "\"inv\"", "a" => opsj(a), "c" => enc_cache(c), "mn" => string(mn))
        elseif h === :new || h === :splatnew
            return jo("k" => "\"new\"", "a" => opsj(a))
        elseif h === :foreigncall
            aa = length(a) ≥ 3 && a[3] isa Core.SimpleVector ?
                ja([jb(t === Any) for t in a[3]]) : "null"
            return jo("k" => "\"fc\"", "a" => opsj(a), "aa" => aa)
        elseif h === :foreignglobal
            return jo("k" => "\"fg\"", "a" => opsj(a))
        elseif h === :throw_undef_if_not
            return jo("k" => "\"tu\"", "a" => opsj(a))
        elseif CC.is_meta_expr_head(h) || h === :leave || h === :the_exception ||
               h === :pop_exception || h === :static_parameter || h === :copyast ||
               h === :isdefined
            return jo("k" => "\"skip\"")
        elseif h === :gc_preserve_begin
            return jo("k" => "\"noop\"")
        elseif h === :gc_preserve_end
            ok = length(a) == 1 && a[1] isa Core.SSAValue &&
                 Meta.isexpr(ir[a[1]][:stmt], :gc_preserve_begin)
            return jo("k" => "\"gpe\"", "b" => ok ? opsj(ir[a[1]][:stmt].args) : "null")
        else
            return jo("k" => "\"cons\"", "a" => opsj(a))
        end
    elseif stmt isa Core.EnterNode
        l = stmt.catch_dest == 0 ? "null" : string(first(ir.cfg.blocks[stmt.catch_dest].stmts))
        return jo("k" => "\"enter\"", "l" => l)
    elseif stmt isa Core.ReturnNode
        return jo("k" => "\"ret\"", "v" => isdefined(stmt, :val) ? enc_opnd(stmt.val) : "null")
    elseif stmt isa Core.PhiNode || stmt isa Core.PhiCNode
        v = stmt.values
        return jo("k" => "\"phi\"",
                  "v" => ja([isassigned(v, i) ? enc_opnd(v[i]) : "null" for i in 1:length(v)]))
    elseif stmt isa Core.PiNode || stmt isa Core.UpsilonNode
        return jo("k" => "\"val\"", "v" => isdefined(stmt, :val) ? enc_opnd(stmt.val) : "null")
    elseif stmt isa GlobalRef || stmt isa Core.BindingPartition
        return jo("k" => "\"gl\"")
    elseif stmt isa Core.SSAValue || stmt isa Core.Argument
        return jo("k" => "\"val\"", "v" => enc_opnd(stmt))
    else
        return jo("k" => "\"skip\"")
    end
end

function enc_ir(ir, nargs, 𝕃ₒ, cachef)
    n = length(ir.stmts)
    insts = String[]
    for pc in 1:n
        s = Core.SSAValue(pc)
        nf = CC.fieldcount_noerror(CC.argextype_widened(s, ir))
        push!(insts, jo("s" => enc_stmt(ir, pc, 𝕃ₒ, cachef),
            "f" => jb(CC.is_identity_free_argtype(CC.argextype(s, ir))),
            "n" => jb(CC.has_flag(ir[s], CC.IR_FLAG_NOTHROW)),
            "nf" => nf === nothing ? "null" : string(nf)))
    end
    ai = ja([jb(CC.is_identity_free_argtype(ir.argtypes[i])) for i in 1:nargs])
    return "\"nargs\":$nargs,\"ai\":$ai,\"st\":$(ja(insts))"
end

function enc_partition(s)
    s = deepcopy(s)
    roots = [EA.find_root!(s, i) for i in 1:length(s.parents)]
    groups = String[]
    for i in 1:length(roots)
        mem = findall(==(roots[i]), roots)
        length(mem) > 1 && first(mem) == i && push!(groups, ja(mem))
    end
    return ja(groups)
end

function expected_ir(ir, nargs, 𝕃ₒ, cachef)
    estate = try
        EA.analyze_escapes(ir, nargs, 𝕃ₒ, cachef)
    catch e
        e isa InterruptException && rethrow()
        return errj(e)
    end
    es = ja([enc_info(i) for i in estate.escapes])
    part = enc_partition(estate.aliasset)
    par = ja(estate.aliasset.parents); rk = ja(estate.aliasset.ranks)
    # Copy only the union-find: a `deepcopy` would also copy the constant `BitSet`s that the
    # analysis compares with `===`.
    fresh_aliases() = EA.EscapeState(estate.escapes, deepcopy(estate.aliasset), estate.nargs)
    ac = try
        c = EA.ArgEscapeCache(fresh_aliases())
        jo("e" => ja([string(a.escape_bits) for a in c.argescapes]),
           "al" => ja([ja([a.aidx, a.bidx]) for a in c.argaliases]))
    catch e
        e isa InterruptException && rethrow()
        errj(e)
    end
    st = fresh_aliases()
    ga = String[]
    for i in 1:length(estate.escapes)
        r = EA.getaliases(i, st)
        push!(ga, r === nothing ? "null" : ja(r))
    end
    return jo("es" => es, "part" => part, "par" => par, "rk" => rk, "ac" => ac, "ga" => ja(ga))
end

const INTERP = CC.NativeInterpreter()
const OPT_LATTICE = CC.optimizer_lattice(INTERP)
const NATIVE_CACHE = CC.GetNativeEscapeCache(INTERP)

const IRS = Dict{Int,Any}()

function errkind(kind, exp)
    m = match(r"^\{\"err\":\"(\w+)\"", exp)
    return m === nothing ? kind : kind * "-err-" * m[1]
end

function gen_ir_case(rng, id, io)
    ir, nargs = gen_ir(rng)
    IRS[id] = ir
    cachef = RandCache(Random.Xoshiro(rand(rng, UInt64)), nothing, IdDict{Any,Any}())
    body = enc_ir(ir, nargs, OPT_LATTICE, cachef)
    exp = expected_ir(ir, nargs, OPT_LATTICE, cachef)
    println(io, "{\"id\":$id,\"ea\":\"ir\",$body,\"exp\":$exp}")
    return errkind("ir", exp)
end

## Real IR

mutable struct Cell; v; end
mutable struct Pair2; a; b; end
@noinline sink(x) = (GXR[] = x; nothing)
c01(x) = (r = Ref{Any}(x); r[])
c02(x) = (c = Cell(x); c.v = 1; c)
c03(x) = (c = Cell(x); sink(c); nothing)
c04(x, y) = (p = Pair2(x, y); p.a)
c05(c::Bool, x) = (r = c ? Cell(x) : Cell(nothing); r.v)
c06(x) = try; Cell(x).v; catch e; e; end
c07(x) = (t = (x, Cell(x)); t[2])
c08(x) = (c = Cell(x); finalizer(c -> nothing, c); c.v)
c09(xs) = (s = 0; for x in xs; s += x; end; s)
c10(x) = (a = Any[x]; a[1])
c11(n::Int) = (c = Cell(0); for i in 1:n; c.v = Cell(c.v); end; c)
c12(x::Int) = ifelse(x > 0, Cell(1), Cell(2))
c13(x) = (c = Cell(x)::Cell; c)
c14(x) = GC.@preserve x Cell(x)
c15(x) = ccall(:jl_object_id, UInt, (Any,), x)
c16(x) = (r = Ref(x); throw(r))
c17(x) = (c = Cell(x); while c.v isa Cell; c = c.v; end; c)
c18(a, b) = (p = Pair2(a, b); p.a = p.b; p.b = p; p)
c19(x) = (nt = (a = x, b = Cell(x)); nt.b.v)
c20(x) = string(x)
c21(x) = (c = Cell(x); try; sink(c); catch; end; c.v)
c22(x::Int) = Cell(x).v + 1
c23(xs::Vector{Any}) = (push!(xs, Cell(1)); xs)
c24(x) = isdefined(x, :v)
c25(f, x) = f(x)
c26(x) = (y = Cell(x); z = Cell(y); z.v.v)
c27(x) = getfield(Cell(x), 1)
c28(m::Module) = getfield(m, :x)
c29(x) = (c = Cell(x); setfield!(c, :v, c); c)
c30(x) = Some(Cell(x))
c31(x) = (c = Cell(x); d = Cell(c); fid(d); c.v)
c32(x, n::Int) = (c = Cell(x); for i in 1:n; c = Cell(c); end; c.v)
c33(x) = (p = Pair2(Cell(x), Cell(x)); q = p.a; q.v = p.b; p.b.v)
c34(x) = (r = Ref(Cell(x)); r[] = Cell(r); r[].v)
c35(b::Bool, x) = (c = Cell(x); d = b ? c : Cell(c); d.v)

const REAL_FUNCS = Any[(c01, (Any,)), (c02, (Any,)), (c03, (Any,)), (c04, (Any, Any)),
    (c05, (Bool, Any)), (c06, (Any,)), (c07, (Any,)), (c08, (Any,)), (c09, (Vector{Int},)),
    (c10, (Any,)), (c11, (Int,)), (c12, (Int,)), (c13, (Any,)), (c14, (Any,)), (c15, (Any,)),
    (c16, (Any,)), (c17, (Any,)), (c18, (Any, Any)), (c19, (Any,)), (c20, (Int,)),
    (c21, (Any,)), (c22, (Int,)), (c23, (Vector{Any},)), (c24, (Cell,)),
    (c25, (typeof(identity), Any)), (c26, (Any,)), (c27, (Any,)), (c28, (Module,)),
    (c29, (Any,)), (c30, (Any,)), (c31, (Any,)), (c32, (Any, Int)), (c33, (Any,)),
    (c34, (Any,)), (c35, (Bool, Any)), (c01, (Int,)), (c07, (String,)), (c18, (Int, Cell))]
const STAGES = Any["CC: COMPACT_1", "CC: COMPACT_2", "CC: ADCE", nothing]

const REAL_IRS = let irs = Any[]
    for (f, tt) in REAL_FUNCS, stage in STAGES
        res = stage === nothing ? Base.code_ircode(f, tt) : Base.code_ircode(f, tt; optimize_until=stage)
        for (ir, _) in res
            isempty(ir.new_nodes.stmts) && push!(irs, ir)
        end
    end
    irs
end

function gen_real_case(rng, id, io)
    ir = rand(rng, REAL_IRS)
    IRS[id] = ir
    nargs = length(ir.argtypes)
    native = rand(rng) < 0.5 ? NATIVE_CACHE : nothing
    cachef = RandCache(Random.Xoshiro(rand(rng, UInt64)), native, IdDict{Any,Any}())
    body = enc_ir(ir, nargs, OPT_LATTICE, cachef)
    exp = expected_ir(ir, nargs, OPT_LATTICE, cachef)
    println(io, "{\"id\":$id,\"ea\":\"ir\",$body,\"exp\":$exp}")
    return errkind("real", exp)
end

function gen_case(rng, id, io)
    r = rand(rng)
    r < 0.45 && return gen_lat(rng, id, io)
    r < 0.88 && return gen_ir_case(rng, id, io)
    return gen_real_case(rng, id, io)
end

function main(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    dir = mktempdir()
    casefile = joinpath(dir, "cases.jsonl")
    ops = Dict{Int,String}()
    open(casefile, "w") do io
        for id in 1:n
            ops[id] = gen_case(rng, id, io)
        end
    end
    if haskey(opts, "dump")
        cp(casefile, opts["dump"]; force=true)
        println("WROTE $n cases to $(opts["dump"])")
    end
    out = read(pipeline(`$(opts["exe"])`, stdin=casefile), String)
    agree = 0; bad = String[]; seen = 0
    perop = Dict{String,Vector{Int}}()
    for line in split(out, '\n'; keepempty=false)
        m = match(r"\"id\":(\d+)", line)
        if m === nothing
            push!(bad, line); continue
        end
        id = parse(Int, m[1]); seen += 1
        st = get!(perop, ops[id], [0, 0])
        if occursin("\"agree\":true", line)
            agree += 1; st[1] += 1
        else
            push!(bad, line); st[2] += 1
        end
    end
    for (op, st) in sort(collect(perop))
        println(rpad(op, 12), " agree=", st[1], " disagree=", st[2])
    end
    for line in first(bad, parse(Int, opts["show"]))
        println("DISAGREE ", first(line, 6000))
        m = match(r"\"id\":(\d+)", line)
        if haskey(opts, "debug") && m !== nothing && haskey(IRS, parse(Int, m[1]))
            println(IRS[parse(Int, m[1])])
        end
    end
    println("REAL_IRS $(length(REAL_IRS))")
    println("SEED $seed CASES $n ANSWERED $seen")
    println("AGREE $agree/$seen")
    rm(dir; recursive=true)
    return isempty(bad) && seen == n ? 0 : 1
end

abspath(PROGRAM_FILE) == (@__FILE__) && exit(main())
