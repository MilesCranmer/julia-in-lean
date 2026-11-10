# Serialize Julia types, values and inference lattice elements to the JSON that `compilerdiff`
# (CompilerDiff.lean) reads, together with the type-name universe they need.
#
# Usage:
#     include("common.jl"); using .LatticeSer
#     s = Ser()                      # one per run: ids are shared by all cases of the run
#     arg = selt(s, x)               # lattice element; sval(s, t) for a type or value
#     exp = expected(s, kind, f)     # run f() and encode its result or exception
#     write_case(io, s, id, op, lattice, [args...], exp)
#
# `write_case` first writes a `{"U": ...}` line with the type names and layouts that the case
# added to the universe. TypeVars and mutable objects get ids from one table per run, so the same
# object always has the same id; the table keeps the objects alive, so ids are never reused.
module LatticeSer

export Ser, sval, selt, expected, write_case, CC, jstr

const CC = Base.Compiler

mutable struct Ser
    ids::IdDict{Any,Int}
    next::Int
    seen_names::Set{String}
    pending_names::Vector{Core.TypeName}
    seen_layouts::IdDict{Any,Nothing}
    pending::Vector{String}          # encoded layout objects
    nfields::Vector{String}
    instances::Vector{String}
    constfields::Vector{String}
    primitives::Vector{String}
end

function Ser()
    s = Ser(IdDict{Any,Int}(), 1, Set{String}(), Core.TypeName[], IdDict{Any,Nothing}(),
            String[], String[], String[], String[], String[])
    # `jl_type_type` (`Type`) is `TypeEq{T} where T`; the model gives its variable id 0.
    s.ids[Type.var] = 0
    for T in (Any, Core.AnyType, Core.TypeofBottom, Core.TypeEq, Core.TypeEgal, DataType, Union,
              UnionAll, Core.Intersect, TypeVar, Core.TypeofVararg, Symbol, Tuple, Int64, Bool,
              Module, Nothing, Task, Core.TypeApp)
        regname!(s, Base.unwrap_unionall(T).name)
    end
    return s
end

objid!(s::Ser, @nospecialize(x)) = get!(() -> (s.next += 1; s.next - 1), s.ids, x)

function jstr(x::AbstractString)
    io = IOBuffer()
    print(io, '"')
    for c in x
        if c == '"' || c == '\\'
            print(io, '\\', c)
        elseif c < ' '
            print(io, "\\u", string(UInt16(c), base=16, pad=4))
        else
            print(io, c)
        end
    end
    print(io, '"')
    String(take!(io))
end
jstr(x::Symbol) = jstr(string(x))

obj(pairs...) = "{" * join((jstr(k) * ":" * v for (k, v) in pairs), ",") * "}"
arr(xs) = "[" * join(xs, ",") * "]"
jbool(b::Bool) = b ? "true" : "false"

tnname(tn::Core.TypeName) = join(string.(fullname(tn.module)), ".") * "." * string(tn.name)

function regname!(s::Ser, tn::Core.TypeName)
    name = tnname(tn)
    name in s.seen_names && return name
    push!(s.seen_names, name)
    push!(s.pending_names, tn)
    return name
end

function reglayout!(s::Ser, dt::DataType)
    haskey(s.seen_layouts, dt) && return
    s.seen_layouts[dt] = nothing
    isconcretetype(dt) || return
    Base.datatype_fieldtypes(dt) # force computation of has_concrete_subtype
    push!(s.pending, obj("dt" => sval(s, dt), "isbits" => jbool(isbitstype(dt)),
        "singleton" => jbool(Base.issingletontype(dt)),
        "cs" => jbool(dt.flags & 0x0020 == 0x0020)))
    if Base.issingletontype(dt)
        push!(s.instances, arr([sval(s, dt), sval(s, dt.instance)]))
    end
    if isstructtype(dt) && !(dt <: Tuple)
        push!(s.nfields, arr([sval(s, dt), string(fieldcount(dt))]))
    end
end

function sval(s::Ser, @nospecialize(x))
    x === Union{} && return "\"bot\""
    if x isa DataType
        regname!(s, x.name)
        enc = obj("dt" => jstr(tnname(x.name)), "p" => arr([sval(s, p) for p in x.parameters]))
        reglayout!(s, x)
        return enc
    elseif x isa Union
        return obj("u" => arr([sval(s, x.a), sval(s, x.b)]))
    elseif x isa UnionAll
        v = x.var
        return obj("ua" => string(objid!(s, v)), "n" => jstr(v.name), "lb" => sval(s, v.lb),
                   "ub" => sval(s, v.ub), "body" => sval(s, x.body))
    elseif x isa TypeVar
        return obj("tv" => string(objid!(s, x)), "n" => jstr(x.name), "lb" => sval(s, x.lb),
                   "ub" => sval(s, x.ub))
    elseif x isa Core.TypeofVararg
        parts = Pair{String,String}["va" => "true"]
        isdefined(x, :T) && push!(parts, "T" => sval(s, x.T))
        isdefined(x, :N) && push!(parts, "N" => sval(s, x.N))
        return obj(parts...)
    elseif x isa Core.TypeEq
        return obj("teq" => sval(s, getfield(x, :T)))
    elseif x isa Core.TypeEgal
        return obj("tegal" => sval(s, getfield(x, :T)))
    elseif x isa Int64
        return obj("long" => string(x))
    elseif x isa Symbol
        return obj("sym" => jstr(x))
    elseif x isa Module
        return obj("mod" => jstr(join(string.(fullname(x)), ".")))
    end
    T = typeof(x)
    if isprimitivetype(T)
        sz = sizeof(T)
        U = sz == 1 ? UInt8 : sz == 2 ? UInt16 : sz == 4 ? UInt32 : sz == 8 ? UInt64 : UInt128
        return obj("bits" => sval(s, T), "v" => string(reinterpret(U, x)))
    elseif ismutable(x)
        return obj("mut" => sval(s, T), "a" => string(objid!(s, x)))
    else
        fs = String[]
        for i in 1:nfields(x)
            isdefined(x, i) || break
            push!(fs, sval(s, getfield(x, i)))
        end
        return obj("imm" => sval(s, T), "f" => arr(fs))
    end
end

function selt(s::Ser, @nospecialize(x))
    if x isa Core.Const
        return obj("C" => sval(s, x.val))
    elseif x isa Core.PartialStruct
        us = [u === nothing ? "null" : jbool(u) for u in x.undefs]
        return obj("PS" => sval(s, x.typ), "u" => arr(us), "f" => arr([selt(s, f) for f in x.fields]),
                   "uid" => string(objid!(s, x.undefs)), "fid" => string(objid!(s, x.fields)))
    elseif x isa CC.Conditional
        return obj("Cond" => arr([string(x.slot), string(x.ssadef)]), "t" => selt(s, x.thentype),
                   "e" => selt(s, x.elsetype), "d" => jbool(x.isdefined))
    elseif x isa Core.InterConditional
        return obj("ICond" => string(x.slot), "t" => selt(s, x.thentype), "e" => selt(s, x.elsetype))
    elseif x isa CC.MustAlias
        return obj("MA" => arr([string(x.slot), string(x.ssadef)]), "v" => selt(s, x.vartyp),
                   "i" => string(x.fldidx), "f" => selt(s, x.fldtyp))
    elseif x isa Core.InterMustAlias
        return obj("IMA" => string(x.slot), "v" => selt(s, x.vartyp), "i" => string(x.fldidx),
                   "f" => selt(s, x.fldtyp))
    elseif x isa CC.PartialTypeVar
        return obj("PTV" => sval(s, x.tv), "l" => jbool(x.lb_certain), "u" => jbool(x.ub_certain))
    elseif x isa CC.LimitedAccuracy
        return obj("LA" => selt(s, x.typ), "c" => arr([string(objid!(s, c)) for c in x.causes]),
                   "cid" => string(objid!(s, x.causes)))
    elseif x isa Core.PartialOpaque
        return obj("PO" => sval(s, x.typ), "env" => selt(s, x.env),
                   "par" => string(objid!(s, x.parent)), "src" => string(objid!(s, x.source)))
    elseif x isa Core.PartialTask
        return obj("PT" => selt(s, x.fetch_type))
    end
    return obj("T" => sval(s, x))
end

"""
    expected(s, kind, f)

Run `f()` on the pinned Julia and encode the result as `kind` (`:bool`, `:optbool`, `:val`,
`:elt`, `:nothing`, `:vals` for a vector of types or values, `:elts` for a vector of lattice
elements, `:eltss` for a vector of vectors of
lattice elements, `:ints_or_nothing` for `nothing` or a `Vector{Int}`), or the exception type it
throws.
"""
function expected(s::Ser, kind::Symbol, f)
    r = try
        f()
    catch e
        return obj("err" => jstr(string(nameof(typeof(e)))))
    end
    kind === :bool && return obj("bool" => jbool(r::Bool))
    kind === :optbool && return obj("optbool" => r === nothing ? "null" : jbool(r::Bool))
    kind === :val && return obj("val" => sval(s, r))
    kind === :nothing && return (r === nothing ? obj("nothing" => "true") : obj("elt" => selt(s, r)))
    kind === :vals && return obj("list" => arr([obj("val" => sval(s, x)) for x in r]))
    kind === :elts && return obj("list" => arr([obj("elt" => selt(s, x)) for x in r]))
    kind === :eltss && return obj("list" => arr([obj("list" => arr([obj("elt" => selt(s, x)) for x in xs]))
                                                 for xs in r]))
    if kind === :ints_or_nothing
        r === nothing && return obj("nothing" => "true")
        return obj("list" => arr([obj("val" => sval(s, x::Int)) for x in r]))
    end
    return obj("elt" => selt(s, r))
end

function flush_universe(io::IO, s::Ser)
    names = String[]
    while !isempty(s.pending_names)
        tn = popfirst!(s.pending_names)
        body = Base.unwrap_unionall(tn.wrapper)::DataType
        parts = Pair{String,String}["name" => jstr(tnname(tn)),
            "abstract" => jbool(isabstracttype(body)), "mutable" => jbool(Base.ismutabletypename(tn)),
            "wrapper" => sval(s, tn.wrapper)]
        body.super === body || push!(parts, "super" => sval(s, body.super))
        tn.constfields != C_NULL && push!(s.constfields, jstr(tnname(tn)))
        isprimitivetype(body) && push!(s.primitives, jstr(tnname(tn)))
        push!(names, obj(parts...))
    end
    if !isempty(names) || !isempty(s.pending) || !isempty(s.nfields) || !isempty(s.instances) ||
            !isempty(s.constfields) || !isempty(s.primitives)
        println(io, obj("U" => obj("names" => arr(names), "layouts" => arr(s.pending),
            "nfields" => arr(s.nfields), "instances" => arr(s.instances), "constfields" => arr(s.constfields),
            "primitives" => arr(s.primitives))))
        empty!(s.pending); empty!(s.nfields); empty!(s.instances); empty!(s.constfields); empty!(s.primitives)
    end
end

"""
    write_case(io, s, id, op, lattice, args, exp)

Write the universe delta and one case line. `args` are already encoded; `lattice` is one of the
names `compilerdiff` knows (`typeinf`, `ipo`, `opt`, ...).
"""
function write_case(io::IO, s::Ser, id::Int, op::String, lattice::String, args::Vector{String},
                    exp::String)
    # Encoding the universe can register further names; loop until nothing is pending.
    flush_universe(io, s)
    println(io, obj("id" => string(id), "op" => jstr(op), "L" => jstr(lattice), "a" => arr(args),
                    "next" => string(s.next + 1000), "exp" => exp))
end

end # module

# Serialize control-flow graphs and dominator trees to the JSON that `compilerdiff` reads for the
# `difftest/compiler/domtree.jl` cases (`CompilerDiff.Domtree` in CompilerDiff.lean).
module CFGSer

export mkblocks, enc_blocks, enc_state, errj, tryj, ja, jo

const CC = Base.Compiler

ja(xs) = "[" * join(xs, ",") * "]"
jo(pairs...) = "{" * join(("\"$k\":$v" for (k, v) in pairs), ",") * "}"

# Blocks from `(preds, succs)` pairs; `stmts` is a dummy range, which the domtree code never reads.
mkblocks(b) = CC.BasicBlock[CC.BasicBlock(CC.StmtRange(i, i), copy(p), copy(s))
                            for (i, (p, s)) in enumerate(b)]

enc_blocks(bs) = ja([ja([ja(b.preds), ja(b.succs)]) for b in bs])

# The observable state of a dominator tree. `to_post` is `null` where `to_pre` is 0 (stale or
# undefined there) and `from_post` is cut to `length(from_pre)` (the post-dominator tree's extra
# slot is undefined).
function enc_state(dt)
    D = dt.dfs_tree
    post = [(i <= length(D.to_pre) && D.to_pre[i] != 0) ? string(D.to_post[i]) : "null"
            for i in 1:length(D.to_post)]
    fpost = D.from_post[1:min(length(D.from_pre), length(D.from_post))]
    jo("pre" => ja(D.to_pre), "fpre" => ja(D.from_pre), "par" => ja(D.to_parent_pre),
       "post" => ja(post), "fpost" => ja(fpost),
       "semi" => ja([ja([s.semi, s.label]) for s in dt.snca_state]),
       "idom" => ja(dt.idoms_bb),
       "nodes" => ja([ja([string(n.level), ja(n.children)]) for n in dt.nodes]))
end

errj(e) = jo("err" => "\"$(nameof(typeof(e)))\"")

function tryj(f)
    try
        return f()
    catch e
        e isa InterruptException && rethrow()
        return errj(e)
    end
end

end # module CFGSer

# Serialize escape-analysis states and abstracted IR to the JSON that `compilerdiff` reads for the
# `difftest/compiler/escape.jl` cases (`CompilerDiff.Escape` in CompilerDiff.lean).
module EscSer

export enc_ainfo, enc_alias, enc_thrown, enc_live, enc_info, enc_opnd, aelt_key

using ..CFGSer: ja, jo

const CC = Base.Compiler
const EA = CC.EscapeAnalysis

jb(b::Bool) = b ? "true" : "false"
jints(xs) = ja(sort!(collect(Int, xs)))

# `LocalDef(i)` is `2i`, `LocalUse(i)` is `2i + 1`; an `AInfo` is written in iteration order.
aelt_key(x::EA.LocalDef) = 2 * x.idx
aelt_key(x::EA.LocalUse) = 2 * x.idx + 1
enc_ainfo(s) = ja([aelt_key(e) for e in s])

enc_alias(a) = a === true ? "true" : a === false ? "false" :
    a isa EA.IndexableFields ? jo("i" => ja(map(enc_ainfo, a.infos))) :
    jo("u" => enc_ainfo((a::EA.Unindexable).info))

enc_thrown(t::BitSet) = t === EA.TOP_THROWN_ESCAPE ? "\"T\"" :
    t === EA.BOT_THROWN_ESCAPE ? "\"B\"" : jints(t)

# A `Liveness` constant, `{"x":1}`/`{"y":1}` when `l` is the object `x`/`y`, else its contents.
enc_live(l::BitSet, x=nothing, y=nothing) =
    l === EA.TOP_LIVENESS ? "\"T\"" : l === EA.BOT_LIVENESS ? "\"B\"" :
    l === EA.ARG_LIVENESS ? "\"A\"" : (x !== nothing && l === x) ? jo("x" => "1") :
    (y !== nothing && l === y) ? jo("y" => "1") : jints(l)

enc_info(i::EA.EscapeInfo, x=nothing, y=nothing) =
    jo("a" => jb(i.Analyzed), "r" => jb(i.ReturnEscape), "t" => enc_thrown(i.ThrownEscape),
       "al" => enc_alias(i.AliasInfo), "l" => enc_live(i.Liveness, x, y))

enc_opnd(@nospecialize x) = x isa Core.Argument ? jo("a" => string(x.n)) :
    x isa Core.SSAValue ? jo("s" => string(x.id)) :
    (x isa GlobalRef || x isa Core.BindingPartition) ? "\"g\"" :
    Meta.isexpr(x, :tuple) ? "\"t\"" : "\"o\""

end # module EscSer
