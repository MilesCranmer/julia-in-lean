# Differential test of the Lean model of Compiler/src/effects.jl (JuliaLean/Compiler/src/effects.lean)
# against the pinned Julia (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     bash -c $JULIA difftest/compiler/effects.jl \
#         --cases 50000 --seed 1'
#
# Covers `Effects(e; kwargs...)`, `is_better_effects`, `merge_effects`, both `merge_effectbits`
# methods, every `is_*` query (and `is_foldable`/`is_foldable_nothrow` with both `check_rtcall`),
# `encode_effects`/`decode_effects`, `encode_effects_override`/`decode_effects_override`,
# `decode_statement_effects_override`, `override_effects` (abstractinterpretation.jl) and
# `adjust_effects(e, ::Method)` (typeinfer.jl, with `Method.purity` set on a probe method). The C
# side of `Expr(:purity)` (src/method.c) is checked end to end: `eff.methodPurity` evals a function
# with `:purity` metas and reads `Method.purity`; `eff.stmtPurity` evals one with call-site
# `:purity` regions and reads the call statement's `ssaflags` from `Base.uncompressed_ir`. The two
# C readers of `ipo_purity_bits` (`effects_foldable`, `effects_ipo_reset_safe`) are static C
# functions with no Julia entry point and are not difftested.
#
# Field values are drawn mostly from the states the compiler names (ALWAYS_TRUE, ALWAYS_FALSE,
# CONSISTENT_IF_NOTRETURNED, CONSISTENT_IF_INACCESSIBLEMEMONLY and their union,
# EFFECT_FREE_IF_INACCESSIBLEMEMONLY, EFFECT_FREE_GLOBALLY, INACCESSIBLEMEM_OR_ARGMEMONLY,
# NOUB_IF_NOINBOUNDS, CONSISTENT_OVERLAY, RESET_SAFE_IF_INACCESSIBLEMEMONLY), then from the
# values that fit the encoded width, then from any byte. Words are drawn from encodings of such
# Effects, from 17-bit and full 32-bit values, and override words from the `@assume_effects`
# settings and from any 16-bit value.
#
# Runs (seed, cases, agreement):
#   2026-11-09, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 50000 cases: AGREE 50000/50000 (208 methodPurity, 196 stmtPurity)
#   seed 2, 50000 cases: AGREE 50000/50000 (189 methodPurity, 194 stmtPurity)
#   seed 3, 50000 cases: AGREE 50000/50000 (208 methodPurity, 183 stmtPurity)
#   No case is unmodelled; the model has no unmodelled branch.

include(joinpath(@__DIR__, "common.jl"))
using .LatticeSer
using Random

const Eff = CC.Effects

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

jarr(xs) = "[" * join(string.(xs), ",") * "]"
jbool(b::Bool) = b ? "true" : "false"

effnums(e::Eff) = Int[getfield(e, i) for i in 1:fieldcount(Eff)]
ovrnums(o::Base.EffectsOverride) = Int[getfield(o, i) for i in 1:fieldcount(Base.EffectsOverride)]
senc(e::Eff) = jarr(effnums(e))
senc(o::Base.EffectsOverride) = jarr(ovrnums(o))

numsexp(xs) = "{\"nums\":" * jarr(xs) * "}"
boolexp(b::Bool) = "{\"bool\":" * jbool(b) * "}"
function guarded(f)
    try
        f()
    catch e
        "{\"err\":" * jstr(string(nameof(typeof(e)))) * "}"
    end
end

# Named states first; widths of the encoding next; any byte last.
const CONSISTENT_STATES = UInt8[CC.ALWAYS_TRUE, CC.ALWAYS_FALSE, CC.CONSISTENT_IF_NOTRETURNED,
    CC.CONSISTENT_IF_INACCESSIBLEMEMONLY, CC.CONSISTENT_IF_NOTRETURNED | CC.CONSISTENT_IF_INACCESSIBLEMEMONLY]
const EFFECT_FREE_STATES = UInt8[CC.ALWAYS_TRUE, CC.ALWAYS_FALSE, CC.EFFECT_FREE_IF_INACCESSIBLEMEMONLY,
    CC.EFFECT_FREE_GLOBALLY]
const RESET_SAFE_STATES = UInt8[CC.ALWAYS_TRUE, CC.ALWAYS_FALSE, CC.RESET_SAFE_IF_INACCESSIBLEMEMONLY]
const IAMO_STATES = UInt8[CC.ALWAYS_TRUE, CC.ALWAYS_FALSE, CC.INACCESSIBLEMEM_OR_ARGMEMONLY]
const NOUB_STATES = UInt8[CC.ALWAYS_TRUE, CC.ALWAYS_FALSE, CC.NOUB_IF_NOINBOUNDS]
const OVERLAY_STATES = UInt8[CC.ALWAYS_TRUE, CC.ALWAYS_FALSE, CC.CONSISTENT_OVERLAY]
const NAMED = Eff[CC.EFFECTS_TOTAL, CC.EFFECTS_THROWS, CC.EFFECTS_UNKNOWN, CC.EFFECTS_MINIMAL]

function rand_field(rng, states::Vector{UInt8}, width::Int)
    r = rand(rng)
    r < 0.85 && return rand(rng, states)
    r < 0.96 && return UInt8(rand(rng, 0:(1 << width) - 1))
    return rand(rng, UInt8)
end

function rand_effects(rng)
    rand(rng) < 0.08 && return rand(rng, NAMED)
    return Eff(rand_field(rng, CONSISTENT_STATES, 3), rand_field(rng, EFFECT_FREE_STATES, 2),
               rand_field(rng, RESET_SAFE_STATES, 2), rand(rng, Bool), rand(rng, Bool), rand(rng, Bool),
               rand_field(rng, IAMO_STATES, 2), rand_field(rng, NOUB_STATES, 2),
               rand_field(rng, OVERLAY_STATES, 2), rand(rng, Bool))
end

# Pairs that share most fields exercise the per-field branches of `is_better_effects`.
function related_effects(rng, e::Eff)
    f = Any[getfield(e, i) for i in 1:fieldcount(Eff)]
    o = rand_effects(rng)
    for i in 1:fieldcount(Eff)
        rand(rng) < 0.25 && (f[i] = getfield(o, i))
    end
    return Eff(f...)
end

const SETTINGS = (:consistent, :effect_free, :nothrow, :terminates_globally, :terminates_locally,
    :notaskstate, :inaccessiblememonly, :noub, :noub_if_noinbounds, :foldable, :removable, :total)

function rand_override(rng)
    r = rand(rng)
    if r < 0.4
        ss = Any[rand(rng, SETTINGS) for _ in 1:rand(rng, 1:3)]
        ss = Any[rand(rng) < 0.2 ? Expr(:call, :!, s) : s for s in ss]
        o = Base.compute_assumed_settings(ss)
        rand(rng) < 0.2 && (o = Base.EffectsOverride(o; consistent_overlay=true))
        rand(rng) < 0.2 && (o = Base.EffectsOverride(o; nortcall=rand(rng, Bool)))
        return o
    end
    return Base.decode_effects_override(rand(rng, UInt16))
end

function rand_word32(rng)
    r = rand(rng)
    r < 0.6 && return CC.encode_effects(rand_effects(rng))
    r < 0.85 && return UInt32(rand(rng, 0:(1 << 17) - 1))
    return rand(rng, UInt32)
end

rand_bools(rng) = Bool[rand(rng) < 0.35 for _ in 1:Base.NUM_EFFECTS_OVERRIDES]

module Probe
f_probe(x) = x
end
const PROBE = only(methods(Probe.f_probe))

const QUERIES = (:is_consistent, :is_effect_free, :is_reset_safe, :is_nothrow, :is_terminates,
    :is_notaskstate, :is_inaccessiblememonly, :is_noub, :is_noub_if_noinbounds, :is_nonoverlayed,
    :is_nortcall, :is_foldable, :is_foldable_nothrow, :is_removable_if_unused,
    :is_finalizer_inlineable, :is_consistent_if_notreturned, :is_consistent_if_inaccessiblememonly,
    :is_effect_free_if_inaccessiblememonly, :is_reset_safe_if_inaccessiblememonly,
    :is_inaccessiblemem_or_argmemonly, :is_consistent_overlay)

const KWNAMES = fieldnames(Eff)

const OPS = [("eff.merge", 14), ("eff.isBetter", 12), ("eff.query", 16), ("eff.encode", 8),
    ("eff.decode", 8), ("eff.encodeOverride", 5), ("eff.decodeOverride", 5),
    ("eff.decodeStmtOverride", 5), ("eff.override", 9), ("eff.adjustMethod", 7), ("eff.kw", 4),
    ("eff.mergebits", 5), ("eff.mergebitsBool", 1), ("eff.methodPurity", 0.4), ("eff.stmtPurity", 0.4)]
const OPW = cumsum([w for (_, w) in OPS]) ./ sum(w for (_, w) in OPS)

pick_op(rng) = OPS[searchsortedfirst(OPW, rand(rng))][1]

function purity_method(exprs::Vector{Vector{Bool}}, together::Bool)
    metas = together ? Any[Expr(:meta, (Expr(:purity, bs...) for bs in exprs)...)] :
                       Any[Expr(:meta, Expr(:purity, bs...)) for bs in exprs]
    fname = gensym("purity_probe")
    f = Core.eval(Probe, Expr(:function, Expr(:call, fname, :x), Expr(:block, metas..., :x)))
    return only(methods(f))
end

function stmt_flag(exprs::Vector{Vector{Bool}})
    body = Any[Expr(:purity, bs...) for bs in exprs]
    push!(body, Expr(:local, Expr(:(=), :val, Expr(:call, :identity, :x))))
    append!(body, Any[Expr(:purity) for _ in exprs])
    push!(body, :val)
    fname = gensym("stmt_probe")
    f = Core.eval(Probe, Expr(:function, Expr(:call, fname, :x), Expr(:block, body...)))
    ci = Base.uncompressed_ir(only(methods(f)))
    # Lowering leaves the call as the right-hand side of `val = (%k)(x)`.
    iscall(st) = st isa Expr && st.head === :call
    i = findfirst(st -> iscall(st) || (st isa Expr && st.head === :(=) && iscall(st.args[2])), ci.code)
    return ci.ssaflags[i]
end

function gen_case(rng, id::Int, io::IO)
    op = pick_op(rng)
    args = String[]
    exp = ""
    if op == "eff.merge"
        a = rand_effects(rng); b = rand(rng) < 0.5 ? related_effects(rng, a) : rand_effects(rng)
        args = [senc(a), senc(b)]
        exp = guarded(() -> numsexp(effnums(CC.merge_effects(a, b))))
    elseif op == "eff.isBetter"
        a = rand_effects(rng); b = rand(rng) < 0.7 ? related_effects(rng, a) : rand_effects(rng)
        args = [senc(a), senc(b)]
        exp = guarded(() -> boolexp(CC.is_better_effects(a, b)))
    elseif op == "eff.query"
        q = rand(rng, QUERIES); e = rand_effects(rng); check = rand(rng, Bool)
        args = [jstr(string(q)), senc(e), check ? "1" : "0"]
        f = getfield(CC, q)
        exp = guarded(() -> boolexp(q in (:is_foldable, :is_foldable_nothrow) ? f(e, check) : f(e)))
    elseif op == "eff.encode"
        e = rand_effects(rng)
        args = [senc(e)]
        exp = guarded(() -> numsexp([CC.encode_effects(e)]))
    elseif op == "eff.decode"
        w = rand_word32(rng)
        args = [string(w)]
        exp = guarded(() -> numsexp(effnums(CC.decode_effects(w))))
    elseif op == "eff.encodeOverride"
        o = rand_override(rng)
        args = [senc(o)]
        exp = guarded(() -> numsexp([Base.encode_effects_override(o)]))
    elseif op == "eff.decodeOverride"
        w = rand(rng) < 0.5 ? Base.encode_effects_override(rand_override(rng)) : rand(rng, UInt16)
        args = [string(w)]
        exp = guarded(() -> numsexp(ovrnums(Base.decode_effects_override(w))))
    elseif op == "eff.decodeStmtOverride"
        r = rand(rng)
        w = r < 0.5 ? (UInt32(Base.encode_effects_override(rand_override(rng))) << CC.NUM_IR_FLAGS) |
                      UInt32(rand(rng, 0:7)) | (rand(rng) < 0.3 ? rand(rng, UInt32) & 0xffff0000 : 0x0) :
                      rand(rng, UInt32)
        args = [string(w)]
        exp = guarded(() -> numsexp(ovrnums(CC.decode_statement_effects_override(w))))
    elseif op == "eff.override"
        e = rand_effects(rng); o = rand_override(rng)
        args = [senc(e), senc(o)]
        exp = guarded(() -> numsexp(effnums(CC.override_effects(e, o))))
    elseif op == "eff.adjustMethod"
        e = rand_effects(rng)
        p = rand(rng) < 0.6 ? Base.encode_effects_override(rand_override(rng)) : rand(rng, UInt16)
        args = [senc(e), string(p)]
        exp = guarded(() -> (PROBE.purity = p; numsexp(effnums(CC.adjust_effects(e, PROBE)))))
    elseif op == "eff.kw"
        e = rand_effects(rng); v = rand_effects(rng)
        given = Bool[rand(rng) < 0.3 for _ in 1:fieldcount(Eff)]
        kws = (KWNAMES[i] => getfield(v, i) for i in 1:fieldcount(Eff) if given[i])
        args = [senc(e), jarr(Int.(given)), senc(v)]
        exp = guarded(() -> numsexp(effnums(Eff(e; kws...))))
    elseif op == "eff.mergebits"
        a = rand(rng) < 0.8 ? rand(rng, UInt8[0x00, 0x01, 0x02, 0x03, 0x04, 0x06, 0x07]) : rand(rng, UInt8)
        b = rand(rng) < 0.8 ? rand(rng, UInt8[0x00, 0x01, 0x02, 0x03, 0x04, 0x06, 0x07]) : rand(rng, UInt8)
        args = [string(a), string(b)]
        exp = guarded(() -> numsexp([CC.merge_effectbits(a, b)]))
    elseif op == "eff.mergebitsBool"
        a = rand(rng, Bool); b = rand(rng, Bool)
        args = [string(Int(a)), string(Int(b))]
        exp = guarded(() -> boolexp(CC.merge_effectbits(a, b)))
    elseif op == "eff.methodPurity"
        exprs = [rand_bools(rng) for _ in 1:rand(rng, 1:3)]
        together = rand(rng, Bool)
        args = [jarr([jarr(Int.(bs)) for bs in exprs])]
        exp = guarded(() -> numsexp([purity_method(exprs, together).purity]))
    elseif op == "eff.stmtPurity"
        exprs = [rand_bools(rng) for _ in 1:rand(rng, 1:3)]
        args = [jarr([jarr(Int.(bs)) for bs in exprs])]
        exp = guarded(() -> numsexp([stmt_flag(exprs)]))
    end
    println(io, "{\"id\":", id, ",\"op\":", jstr(op), ",\"L\":\"typeinf\",\"a\":", jarr(args),
            ",\"next\":0,\"exp\":", exp, "}")
    return op
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
        return 0
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
        println(rpad(op, 28), " agree=", st[1], " disagree=", st[2])
    end
    for line in first(bad, parse(Int, opts["show"]))
        println("DISAGREE ", line)
    end
    println("SEED $seed CASES $n ANSWERED $seen")
    println("AGREE $agree/$seen")
    rm(dir; recursive=true)
    return isempty(bad) && seen == n ? 0 : 1
end

exit(main())
