# Differential test of the Lean models of the inlining cost model and statement flags
# (JuliaLean/Compiler/src/optimize.lean) and of the inlining decision helpers
# (JuliaLean/Compiler/src/ssair/inlining.lean) against the pinned Julia
# (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA difftest/compiler/inlining.jl --cases 50000 --seed 1
#
# Covers, from Compiler/src/optimize.jl: the IR_FLAG_*/IR_FLAGS_*/SLOT_*/SRC_FLAG_* constants,
# `has_flag`, `is_stmt_inline`, `is_stmt_noinline`, `iscallstmt`, `flags_for_effects`,
# `inlining_cost`, `is_inlineable`, `set_inlineable!`, `inline_cost_clamp` (and through it, and
# directly by `ccall`, `jl_encode_inlining_cost`/`jl_decode_inlining_cost` of src/ircode.c),
# `is_declared_inline`, `is_declared_noinline`, both `src_inlining_policy` methods,
# `plus_saturate`, `statement_or_branch_cost` (so `statement_cost`), `statement_costs!` and
# `inline_cost_model(::IRCode, ...)`; from Compiler/src/typeinfer.jl:
# `inline_cost_model(interp, result, inline_flag, ir)` and `is_result_constabi_eligible`; from
# Compiler/src/ssair/inlining.jl: `early_inline_special_case`, `handle_cases!`,
# `inline_const_if_inlineable!` and `linear_inline_eligible`.
#
# Statements come from randomly generated functions (arguments of concrete, abstract and Union
# types; arithmetic, array, tuple, field, global, ccall/cglobal/llvmcall, typeassert (also with
# one argument), compilerbarrier, quoted-Expr, try/catch, loop and branch code) and from a fixed
# list of Base calls, each taken as optimized `IRCode`, as `IRCode` stopped after slot2reg or
# inlining, and as unoptimized `CodeInfo`. The driver computes the type answers the model takes
# as inputs (see the docstrings of `ArgFacts`, `CallFacts`, `ResultFacts`, `EarlyFacts`) with
# the same Compiler functions the code calls. Parameters are biased to the edges: penalties and
# thresholds of 0, negative, `typemax(Int)` and `typemin(Int)`, thresholds that overflow under
# `19*default`, and costs at the boundaries of the 8-bit cost encoding (31/32, 63/64, 3968/3969,
# 65535/65536).
#
# Harness normalizations (in CompilerDiff.lean, not in the model): an `early_inline_special_case`
# result `stmt.args[4]` is reported as `arg3` when `stmt.args[3] === stmt.args[4]`, and
# `instanceof` as `quoted` when the two values are `==`; a `handle_cases!` flag update that adds
# no bit is reported as `none`. In each pair Julia's result is the same object.
#
# Runs (seed, cases, agreement):
#   2026-11-10, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 50000 cases: AGREE 50000/50000 (pool 834 sources, 22330 statements)
#   seed 2, 50000 cases: AGREE 50000/50000 (pool 834 sources, 22419 statements)
#   seed 3, 50000 cases: AGREE 50000/50000 (pool 833 sources, 23583 statements)
#   2026-11-10, after the property pass (model of the difftested functions unchanged; new
#   decision models added): seed 4, 50000 cases: AGREE 50000/50000
#   2026-11-10, after the review fixes (model unchanged; exact statements added, their Julia checks
#   are in inlining_props.jl): seed 5, 50000 cases: AGREE 50000/50000
#   Each run reaches every statement kind (the pool histogram it prints), the one-argument
#   `typeassert` BoundsError (80-152 cases per cost op), and every `early_inline_special_case`
#   and `handle_cases!` outcome. No case is unmodelled. A planted model change (backward-branch
#   cost 41 instead of 40) gave 102 disagreements in 5000 cases.
#
# Not in this driver: `resolveTodoDecision`, `semiconcreteDecision` and `callsiteInlineBits`
# (JuliaLean/Compiler/src/ssair/inlining.lean), which need a call result and an inlining state.
# The @inline/@noinline docstring examples behind compiler-inlining-callsite-annotations were run
# end to end on the pinned Julia instead (2026-11-10, f755f49a9e): a call-site @inline inlines a
# @noinline callee; a call-site @noinline keeps a call to an @inline callee; the innermost of
# nested @noinline/@inline regions wins in both orders (one call left each); a callee with
# try/catch is not inlined by cost but is with a call-site @inline.

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

jb(b::Bool) = b ? "true" : "false"
jarr(xs) = "[" * join(string.(xs), ",") * "]"
jobj(ps...) = "{" * join([jstr(string(k)) * ":" * string(v) for (k, v) in ps], ",") * "}"
numsexp(xs) = "{\"nums\":" * jarr(Int.(xs)) * "}"
boolexp(b::Bool) = "{\"bool\":" * jb(b) * "}"
jsonexp(s) = "{\"json\":" * s * "}"
function guarded(f)
    try
        f()
    catch e
        "{\"err\":" * jstr(string(nameof(typeof(e)))) * "}"
    end
end

########################
# Effects (as effects.jl)
########################

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
    rand(rng) < 0.15 && return rand(rng, NAMED)
    return Eff(rand_field(rng, CONSISTENT_STATES, 3), rand_field(rng, EFFECT_FREE_STATES, 2),
               rand_field(rng, RESET_SAFE_STATES, 2), rand(rng, Bool), rand(rng, Bool), rand(rng, Bool),
               rand_field(rng, IAMO_STATES, 2), rand_field(rng, NOUB_STATES, 2),
               rand_field(rng, OVERLAY_STATES, 2), rand(rng, Bool))
end

senc(e::Eff) = jarr(Int[getfield(e, i) for i in 1:fieldcount(Eff)])

#################
# Edge-biased ints
#################

const FLAG_BITS = UInt32[CC.IR_FLAG_INBOUNDS, CC.IR_FLAG_INLINE, CC.IR_FLAG_NOINLINE, CC.IR_FLAG_CONSISTENT,
    CC.IR_FLAG_EFFECT_FREE, CC.IR_FLAG_NOTHROW, CC.IR_FLAG_TERMINATES, CC.IR_FLAG_NOUB, CC.IR_FLAG_NORTCALL,
    CC.IR_FLAG_RESET_SAFE, CC.IR_FLAG_REFINED, CC.IR_FLAG_UNUSED, CC.IR_FLAG_EFIIMO,
    CC.IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM, CC.IR_FLAG_RSIIMO, CC.IR_FLAGS_EFFECTS, CC.IR_FLAGS_REMOVABLE,
    CC.IR_FLAGS_NEEDS_EA, UInt32(1) << 7, UInt32(1) << 15, UInt32(1) << 31]

function rand_flag(rng)
    r = rand(rng)
    r < 0.15 && return zero(UInt32)
    if r < 0.75
        f = zero(UInt32)
        for _ in 1:rand(rng, 1:4)
            f |= rand(rng, FLAG_BITS)
        end
        return f
    end
    r < 0.85 && return CC.flags_for_effects(rand_effects(rng)) | (rand(rng, Bool) ? rand(rng, FLAG_BITS) : 0x0)
    r < 0.93 && return UInt32(rand(rng, 0:(1 << 21) - 1))
    return rand(rng, UInt32)
end

const INT_EDGES = Int[0, 1, -1, 2, 9, 10, 11, 19, 20, 21, 31, 32, 33, 39, 40, 41, 63, 64, 65, 99, 100, 101,
    127, 128, 1000, 2047, 2048, 3968, 3969, 4031, 4032, 4095, 4096, 65534, 65535, 65536, 65537,
    typemax(Int), typemax(Int) - 1, typemin(Int), typemin(Int) + 1, typemax(Int) ÷ 19,
    typemax(Int) ÷ 19 + 1, typemax(Int) ÷ 4 + 1, typemax(Int) ÷ 2, typemax(Int) ÷ 2 + 1]

function rand_int(rng)
    r = rand(rng)
    r < 0.35 && return rand(rng, INT_EDGES)
    r < 0.55 && return rand(rng, INT_EDGES) + rand(rng, -3:3)
    r < 0.75 && return rand(rng, 0:5000)
    r < 0.85 && return rand(rng, -100:100)
    r < 0.92 && (k = rand(rng, 0:62); return (1 << k) + rand(rng, -1:1))
    return rand(rng, Int)
end

function rand_u16(rng)
    r = rand(rng)
    r < 0.4 && return UInt16(clamp(rand(rng, INT_EDGES) + rand(rng, -2:2), 0, 65535))
    r < 0.7 && return UInt16(rand(rng, 0:4100))
    r < 0.85 && (k = rand(rng, 0:15); return UInt16(clamp((1 << k) + rand(rng, -1:1), 0, 65535)))
    return rand(rng, UInt16)
end

const PENALTIES = Int[1000, 1000, 1000, 1000, 0, 1, 20, 100, -1, -1000, typemax(Int), typemin(Int),
    typemax(Int) ÷ 2]
rand_penalty(rng) = rand(rng) < 0.85 ? rand(rng, PENALTIES) : rand(rng, -10^6:10^6)

const THRESHOLDS = Int[100, 100, 100, 0, -1, 1, 10, 50, 99, 101, 208, 209, 250, 350, 1000, 2000, 3968,
    3969, 4000, 10^6, typemax(Int), typemin(Int), typemax(Int) ÷ 19, typemax(Int) ÷ 19 + 1,
    typemax(Int) ÷ 20 + 1, typemax(Int) ÷ 4 + 1]
rand_threshold(rng) = rand(rng) < 0.8 ? rand(rng, THRESHOLDS) : rand(rng, -10:5000)
const BONUSES = Int[250, 250, 250, 0, 1, -250, typemax(Int), typemin(Int)]
rand_bonus(rng) = rand(rng) < 0.85 ? rand(rng, BONUSES) : rand(rng, -1000:5000)

####################################
# Generated functions and their IR
####################################

module Gen
@noinline noinl(x) = x
@inline inl(x) = x isa Int ? x + 1 : x
@noinline thrower(x) = throw(ArgumentError("x"))
const G_INT = 3
G_ANY = 1
mutable struct MS
    a::Int
    b::Any
end
struct IS
    a::Int
    b::Float64
end
iterate(::IS) = nothing          # a method named `iterate` outside Base
@generated gen1(x) = :(x + 1)
@generated function gen2(x)
    if x <: Integer
        return :(x * 2)
    else
        return :(x)
    end
end
function gen3(x)
    if @generated
        return :(x + 1)
    else
        return x
    end
end
end

const ARG_TYPES = Any[Int, Int, Float64, Bool, Any, Any, Vector{Int}, Vector{Any}, Tuple{Int,Float64},
    Union{Int,Nothing}, String, Gen.MS, Gen.IS, Complex{Int}, Symbol, Integer, Ref{Int}, Tuple{Vararg{Int}},
    NTuple{3,Int}, Vector{Float64}]

const LITERALS = ["1", "2", "0", "-1", "2.5", "true", "false", ":sym", "\"str\"", "nothing", "Gen.G_INT",
    "Gen.G_ANY", "(1, 2)", "Int"]

function gen_expr(rng, names::Vector{String}, depth::Int=0)
    pick() = rand(rng) < 0.75 && !isempty(names) ? rand(rng, names) : rand(rng, LITERALS)
    if depth > 2 || rand(rng) < 0.25
        return pick()
    end
    sub() = gen_expr(rng, names, depth + 1)
    r = rand(rng, 1:50)
    x = sub(); y = sub()
    return r == 1 ? "($x + $y)" :
           r == 2 ? "($x * $y)" :
           r == 3 ? "($x - 1)" :
           r == 4 ? "($x < $y)" :
           r == 5 ? "($x === $y)" :
           r == 6 ? "($x isa Int)" :
           r == 7 ? "($x, $y)" :
           r == 8 ? "$x[1]" :
           r == 9 ? "$x[$y]" :
           r == 10 ? "length($x)" :
           r == 11 ? "Core.typeassert($x, Int)" :
           r == 12 ? "($x::Int)" :
           r == 13 ? "Core.ifelse($x, $y, $x)" :
           r == 14 ? "Gen.noinl($x)" :
           r == 15 ? "Gen.inl($x)" :
           r == 16 ? "Gen.thrower($x)" :
           r == 17 ? "sizeof($x)" :
           r == 18 ? "typeof($x)" :
           r == 19 ? "Ref($x)[]" :
           r == 20 ? "getfield($x, 1)" :
           r == 21 ? "($x).a" :
           r == 22 ? "ccall(:jl_object_id, UInt, (Any,), $x)" :
           r == 23 ? "pointer(\"abc\")" :
           r == 24 ? "unsafe_load(cglobal(:jl_n_threads, Cint))" :
           r == 25 ? "Base.llvmcall(\"ret i64 %0\", Int, Tuple{Int}, $x)" :
           r == 26 ? "isassigned($x, 1)" :
           r == 27 ? "pop!($x)" :
           r == 28 ? "Base.inferencebarrier($x)" :
           r == 29 ? "Base.compilerbarrier(:conditional, $x)" :
           r == 30 ? ":(g(1))" :
           r == 31 ? "(@inbounds $x[1])" :
           r == 32 ? "Core.typeassert($x)" :
           r == 33 ? "($x)($y)" :
           r == 34 ? "Base.add_int($x, $y)" :
           r == 35 ? "Core.Intrinsics.mul_int($x, 3)" :
           r == 36 ? "abs($x)" :
           r == 37 ? "string($x)" :
           r == 38 ? "($x ? $y : $x)" :
           r == 39 ? "Core.tuple($x)" :
           r == 40 ? "fieldtype(typeof($x), 1)" :
           r == 41 ? "($x !== $y)" :
           r == 42 ? "Base.inferencebarrier($x)::Int" :
           r == 43 ? "Gen.MS($x, $y)" :
           r == 44 ? "Gen.IS($x, 1.0)" :
           r == 45 ? "($x[1] = $y)" :
           r == 46 ? "Core.invoke(Gen.noinl, Tuple{Any}, $x)" :
           r == 47 ? "isassigned(Any[$x], 1)" :
           r == 48 ? "(Any[$x])[1]" :
           r == 49 ? "Core.Intrinsics.llvmcall(\"ret i64 %0\", Int, Tuple{Int}, 1)" :
                     "sum($x)"
end

function gen_body!(rng, lines::Vector{String}, names::Vector{String}, nvar::Ref{Int}, depth::Int)
    for _ in 1:rand(rng, 1:(depth == 0 ? 6 : 3))
        r = rand(rng)
        if r < 0.45 || depth > 1
            nvar[] += 1
            v = "v$(nvar[])"
            push!(lines, "$v = $(gen_expr(rng, names))")
            push!(names, v)
        elseif r < 0.58
            push!(lines, "if $(gen_expr(rng, names))")
            gen_body!(rng, lines, copy(names), nvar, depth + 1)
            if rand(rng, Bool)
                push!(lines, "else")
                gen_body!(rng, lines, copy(names), nvar, depth + 1)
            end
            push!(lines, "end")
        elseif r < 0.68
            push!(lines, "for i in 1:$(rand(rng, ["3", "length(\"ab\")", rand(rng, names)]))")
            gen_body!(rng, lines, vcat(names, ["i"]), nvar, depth + 1)
            push!(lines, "end")
        elseif r < 0.74
            nvar[] += 1
            k = "v$(nvar[])"
            push!(lines, "$k = 0")
            push!(lines, "while $k < 3")
            push!(lines, "$k += 1")
            gen_body!(rng, lines, vcat(names, [k]), nvar, depth + 1)
            push!(lines, "end")
            push!(names, k)
        elseif r < 0.80
            push!(lines, "try")
            gen_body!(rng, lines, copy(names), nvar, depth + 1)
            push!(lines, "catch")
            push!(lines, "end")
        elseif r < 0.83
            push!(lines, "global Gen.G_ANY = $(gen_expr(rng, names))")
        elseif r < 0.85
            push!(lines, "global G_ANY")
            push!(lines, "G_ANY = $(gen_expr(rng, names))")
        elseif r < 0.88
            push!(lines, "@inline")
        elseif r < 0.92
            push!(lines, "$(rand(rng, names)) isa Int && return $(gen_expr(rng, names))")
        else
            push!(lines, gen_expr(rng, names))
        end
    end
end

function gen_function(rng, k::Int)
    nargs = rand(rng, 0:3)
    names = ["a$i" for i in 1:nargs]
    types = Any[rand(rng, ARG_TYPES) for _ in 1:nargs]
    lines = String[]
    gen_body!(rng, lines, copy(names), Ref(0), 0)
    allnames = vcat(names, [m.match for m in eachmatch(r"\bv\d+(?= = )", join(lines, "\n"))])
    push!(lines, "return " * (isempty(allnames) ? "1" : rand(rng, allnames)))
    ann = rand(rng) < 0.15 ? "@inline " : rand(rng) < 0.1 ? "@noinline " : ""
    fname = "f$k"
    src = "$(ann)function $fname($(join(names, ", ")))\n" * join(lines, "\n") * "\nend"
    f = Core.eval(Gen, Meta.parse(src))
    return f, Tuple{types...}
end

const BASE_CALLS = Any[(sum, (Vector{Int},)), (sort!, (Vector{Int},)), (push!, (Vector{Any}, Int)),
    (string, (Int,)), (parse, (Type{Int}, String)), (getindex, (Dict{Int,Int}, Int)),
    (setindex!, (Dict{Symbol,Any}, Int, Symbol)), (iterate, (Vector{Int}, Int)), (iterate, (String,)),
    (+, (Int, Float64)), (sqrt, (Float64,)), (map, (typeof(abs), Vector{Int})), (join, (Vector{String}, String)),
    (show, (IOBuffer, Float64)), (reverse, (String,)), (findfirst, (typeof(iseven), Vector{Int})),
    (copy, (Vector{Any},)), (Base.unsafe_convert, (Type{Ptr{UInt8}}, String)), (Base.cconvert, (Type{Ptr{UInt8}}, String)),
    (hash, (Tuple{Int,String}, UInt)), (div, (Int, Int)), (rem, (Int8, Int8)), (exp, (Float64,)),
    (isless, (String, String)), (Base.ht_keyindex, (Dict{Int,Int}, Int)), (print, (IOBuffer, Any)),
    (filter, (typeof(iseven), Vector{Int})), (getindex, (Vector{Any}, Int)), (pop!, (Vector{Any},)),
    (fill, (Int, Int)), (zeros, (Int, Int)), (Base.power_by_squaring, (Int, Int)), (ntuple, (typeof(identity), Val{3}))]

struct IREntry
    src::Any                 # IRCode or CodeInfo
    isIR::Bool
    sptypes::Vector{CC.VarState}
    stmts::Vector{String}    # model encodings of each statement
    blockfirst::String
    mi::Core.MethodInstance
end

const BUILTIN_KIND = IdDict{Any,String}(Core.getfield => "getfield", Core.tuple => "tuple",
    Core.getglobal => "getglobal", Core.memoryrefget => "memoryrefget",
    Core.const_memoryrefget => "const_memoryrefget", Core.memoryref_isassigned => "memoryref_isassigned",
    Core.memoryrefset! => "memoryrefset!", Core.memoryrefunset! => "memoryrefunset!",
    Core.typeassert => "typeassert", Core.invoke => "invoke")

function callee_json(@nospecialize(ftyp))
    f = CC.singleton_type(ftyp)
    if isa(f, Core.IntrinsicFunction)
        iidx = Int(reinterpret(Int32, f)) + 1
        ll = f === Core.Intrinsics.llvmcall
        if isassigned(CC.T_IFUNC, iidx)
            minarg, maxarg, = CC.T_IFUNC[iidx]
            return jobj("t" => "\"i\"", "as" => "true", "mn" => minarg, "mx" => maxarg,
                        "c" => CC.T_IFUNC_COST[iidx], "ll" => jb(ll))
        end
        return jobj("t" => "\"i\"", "as" => "false", "mn" => 0, "mx" => 0, "c" => 0, "ll" => jb(ll))
    elseif isa(f, Core.Builtin)
        fidx = CC.find_tfunc(f)
        return jobj("t" => "\"b\"", "k" => jstr(get(BUILTIN_KIND, f, "other")),
                    "tc" => (fidx === nothing ? "null" : string(CC.T_FFUNC_COST[fidx])))
    end
    return jobj("t" => "\"o\"")
end

function arg_facts(@nospecialize(a), src, sptypes)
    try
        t = CC.argextype(a, src, sptypes)
        aty = CC.widenconditional(t)
        aty′ = CC.widenconst_split(aty)
        de = CC.isdispatchelem(aty′)
        cc = aty isa CC.Const && CC.isconcretedispatch(aty′)
        kn = CC.isknowntype(t)
        ct = CC.isconstType(CC.argextype_widened(a, src, sptypes))
        return jarr(jb.([de, cc, kn, ct]))
    catch
        return "null"
    end
end

function call_facts(ex::Expr, line::Int, src, sptypes)
    farg = ex.args[1]
    ftyp0 = CC.argextype(farg, src, sptypes)
    fi = ftyp0 === Core.IntrinsicFunction
    fs = farg isa Core.SSAValue
    dr = false
    ftyp1 = Any
    if fi && fs
        d = isa(src, Core.CodeInfo) ? src.code[farg.id] : src[farg][:stmt]
        dr = isa(d, GlobalRef) || isa(d, QuoteNode) || isa(d, Core.IntrinsicFunction) || Meta.isexpr(d, :static_parameter)
        dr && (ftyp1 = CC.argextype(d, src, sptypes))
    end
    final = (fi && fs && dr) ? ftyp1 : ftyp0
    skipargs = CC.singleton_type(final) === Core.Intrinsics.llvmcall
    args = skipargs ? String[] : String[arg_facts(ex.args[i], src, sptypes) for i in 2:length(ex.args)]
    rb = line == -1 ? false : CC.argextype(Core.SSAValue(line), src, sptypes) === Union{}
    return jobj("c0" => callee_json(ftyp0), "fi" => jb(fi), "fs" => jb(fs), "dr" => jb(dr),
                "c1" => callee_json(ftyp1), "n" => length(ex.args), "a" => jarr(args), "rb" => jb(rb))
end

function expr_facts(ex::Expr, line::Int, src, sptypes)
    h = ex.head
    if Base.is_meta_expr_head(h)
        return jobj("h" => "\"meta\"")
    elseif h === :call
        return jobj("h" => "\"call\"", "c" => call_facts(ex, line, src, sptypes))
    elseif h === :foreigncall
        fc = ex.args[1]
        sp = Meta.isexpr(fc, :tuple, 1) && fc.args[1] isa QuoteNode && fc.args[1].value === :jl_string_ptr
        return jobj("h" => "\"fc\"", "sp" => jb(sp))
    elseif h === :foreignglobal
        return jobj("h" => "\"fg\"")
    elseif h === :invoke || h === :invoke_modify
        rb = line == -1 ? false : CC.argextype(Core.SSAValue(line), src, sptypes) === Union{}
        return jobj("h" => "\"inv\"", "rb" => jb(rb))
    elseif h === :(=)
        lhs = ex.args[1]
        g = isa(lhs, GlobalRef) || isa(lhs, Core.BindingPartition)
        rhs = ex.args[2]
        if isa(rhs, Expr)
            return jobj("h" => "\"=e\"", "g" => jb(g), "r" => expr_facts(rhs, -1, src, sptypes))
        end
        return jobj("h" => "\"=\"", "g" => jb(g))
    elseif h === :copyast
        return jobj("h" => "\"copyast\"")
    end
    return jobj("h" => "\"o\"")
end

function stmt_facts(@nospecialize(stmt), line::Int, src, sptypes)
    if stmt isa Expr
        return jobj("k" => "\"e\"", "e" => expr_facts(stmt, line, src, sptypes))
    elseif stmt isa Core.GotoNode
        return jobj("k" => "\"g\"", "l" => stmt.label)
    elseif stmt isa Core.GotoIfNot
        return jobj("k" => "\"gi\"", "l" => stmt.dest)
    elseif stmt isa Core.EnterNode
        return jobj("k" => "\"enter\"")
    end
    return jobj("k" => "\"o\"")
end

body_of(e::IREntry) = e.isIR ? Any[e.src[Core.SSAValue(i)][:stmt] for i in 1:length(e.src.stmts)] : e.src.code

function make_entry(src, isIR::Bool, mi::Core.MethodInstance)
    sptypes = isIR ? src.sptypes : CC.sptypes_from_meth_instance(mi)
    body = isIR ? Any[src[Core.SSAValue(i)][:stmt] for i in 1:length(src.stmts)] : src.code
    stmts = String[stmt_facts(body[i], i, src, sptypes) for i in 1:length(body)]
    bf = isIR ? jarr([first(b.stmts) for b in src.cfg.blocks]) : "[]"
    return IREntry(src, isIR, sptypes, stmts, bf, mi)
end

const STAGES = ["CC: SLOT2REG", "CC: INLINING", "CC: COMPACT_2"]

function entries_for(rng, @nospecialize(f), @nospecialize(tt))
    out = IREntry[]
    types = tt isa DataType ? Tuple(tt.parameters) : tt
    mi = try
        Base.method_instance(f, types)
    catch
        return out
    end
    mi isa Core.MethodInstance || return out
    try
        ir, = only(Base.code_ircode(f, types))
        push!(out, make_entry(ir, true, mi))
    catch
    end
    if rand(rng) < 0.4
        try
            ir, = only(Base.code_ircode(f, types; optimize_until=rand(rng, STAGES)))
            push!(out, make_entry(ir, true, mi))
        catch
        end
    end
    if rand(rng) < 0.4
        try
            ci, = only(Base.code_typed(f, types; optimize=false))
            push!(out, make_entry(ci, false, mi))
        catch
        end
    end
    # The case `statement_cost` recovers from: a callee whose `Const` type was widened to
    # `IntrinsicFunction` by earlier inlining.
    for e in copy(out)
        w = widen_intrinsics(e.src)
        w === nothing || push!(out, make_entry(w, e.isIR, mi))
    end
    return out
end

function widen_intrinsics(src)
    src = copy(src)
    types = src isa Core.CodeInfo ? src.ssavaluetypes : src.stmts.type
    changed = false
    for i in eachindex(types)
        t = types[i]
        if t isa CC.Const && t.val isa Core.IntrinsicFunction
            types[i] = Core.IntrinsicFunction
            changed = true
        end
    end
    return changed ? src : nothing
end

function build_pool(rng, n::Int)
    pool = IREntry[]
    k = 0
    for (f, tt) in BASE_CALLS
        append!(pool, entries_for(rng, f, tt))
    end
    while length(pool) < n
        k += 1
        f, tt = try
            gen_function(rng, k)
        catch
            continue
        end
        append!(pool, entries_for(rng, f, tt))
    end
    return pool
end

##########################
# Method instances, types
##########################

function mi_pool()
    mis = Core.MethodInstance[]
    add(f, tt) = try
        push!(mis, Base.method_instance(f, tt))
    catch
    end
    add(iterate, (Vector{Int},)); add(iterate, (Vector{Int}, Int)); add(iterate, (String, Int))
    add(Base.unsafe_convert, (Type{Ptr{UInt8}}, String)); add(Base.cconvert, (Type{Ptr{UInt8}}, String))
    add(Gen.iterate, (Gen.IS,)); add(Gen.noinl, (Int,)); add(Gen.noinl, (Any,)); add(Gen.inl, (Int,))
    add(+, (Int, Int)); add(+, (Integer, Integer)); add(sum, (Vector{Int},)); add(sum, (AbstractVector,))
    add(Core.kwcall, (NamedTuple, typeof(sum), Vector{Int})); add(getindex, (Vector{Any}, Int))
    add(Gen.gen1, (Int,)); add(Gen.gen1, (Any,)); add(Gen.gen2, (Integer,)); add(Gen.gen3, (Int,)); add(Gen.gen3, (Any,))
    add(Base.tail, (Tuple{Int,Int},)); add(Base.tail, (Tuple{Vararg{Int}},))
    # A method instance whose specTypes is not a `Tuple` data type, and one for a toplevel thunk.
    m = only(methods(Gen.noinl))
    try
        push!(mis, CC.specialize_method(m, Union{Tuple{typeof(Gen.noinl),Int},Tuple{typeof(Gen.noinl),Float64}}, Core.svec()))
    catch
    end
    try
        push!(mis, ccall(:jl_method_instance_for_thunk, Ref{Core.MethodInstance}, (Any, Any),
                         Meta.lower(Main, :(1 + 1)).args[1], Main))
    catch
    end
    try
        push!(mis, CC.specialize_method(m, Tuple{typeof(Gen.noinl),Vector{T}} where T, Core.svec(TypeVar(:T))))
    catch
    end
    return mis
end

const RTS = Any[Union{}, Int, Any, Tuple{Int,Int}, Tuple{Int,Any}, Tuple, NTuple{3,Int}, Tuple{Vararg{Int}},
    CC.Const(1), CC.Const((1, 2)), CC.Const(nothing), Union{Tuple{Int},Nothing}, Type{Int}, Bool, Tuple{},
    CC.Const(Tuple{Int,Int}), Vector{Int}, Tuple{Union{Int,Nothing}}]
for mk in (() -> CC.PartialStruct(CC.fallback_lattice, Tuple{Int,Any}, Any[CC.Const(1), Any]),
           () -> CC.Conditional(2, Int, Any), () -> CC.Conditional(2, Union{}, Bool))
    try
        push!(RTS, mk())
    catch
    end
end

const CONSTS = Any[CC.Const(1), CC.Const("str"), CC.Const(:s), CC.Const(nothing), CC.Const(zeros(Int, 100)),
    CC.Const(ntuple(i -> i, 40)), CC.Const(Int), CC.Const((1, "a")), CC.Const(Gen.IS(1, 2.0)),
    CC.Const(Core.svec(1)), CC.Const(Base), Int, Any, Union{}, Bool]

######################
# Case generation
######################

const OPS = [("inl.consts", 0.2), ("inl.hasFlag", 4), ("inl.isStmtInline", 1.5), ("inl.isStmtNoinline", 1.5),
    ("inl.iscallstmt", 1), ("inl.flagsForEffects", 6), ("inl.plusSaturate", 5), ("inl.clamp", 6),
    ("inl.encode", 4), ("inl.decode", 2), ("inl.inliningCost", 3), ("inl.isInlineable", 3),
    ("inl.isDeclaredInline", 1.5), ("inl.isDeclaredNoinline", 1.5), ("inl.setInlineable", 0.5),
    ("inl.srcPolicy", 4), ("inl.srcPolicyMI", 3), ("inl.stmtCost", 22), ("inl.stmtCosts", 3),
    ("inl.bodyCost", 8), ("inl.threshold", 9), ("inl.constabi", 2), ("inl.early", 6),
    ("inl.handleCases", 4), ("inl.inlineConst", 2), ("inl.linear", 1.5)]
const OPW = cumsum([w for (_, w) in OPS]) ./ sum(w for (_, w) in OPS)
pick_op(rng) = OPS[searchsortedfirst(OPW, rand(rng))][1]

const HEADS = Any[:call, :invoke, :foreigncall, :foreignglobal, :new, :invoke_modify, :(=), :meta,
    :boundscheck, :copyast, :splatnew, :foreigncal, nothing]

struct Ctx
    pool::Vector{IREntry}
    irs::Vector{IREntry}
    mis::Vector{Core.MethodInstance}
    method::Method
    ci::Core.CodeInfo
    interp::CC.NativeInterpreter
end

function rand_src(rng, ctx::Ctx)
    r = rand(rng)
    if r < 0.3
        c = rand_u16(rng); i = rand(rng) < 0.8 ? rand(rng, UInt8(0):UInt8(3)) : rand(rng, UInt8)
        ci = copy(ctx.ci); ci.inlining_cost = c; ci.inlining = i
        return jobj("s" => "\"ci\"", "c" => Int(c), "i" => Int(i)), ci
    elseif r < 0.6
        c = rand_u16(rng); i = rand(rng) < 0.8 ? rand(rng, UInt8(0):UInt8(3)) : rand(rng, UInt8(0):UInt8(15))
        ci = copy(ctx.ci); ci.inlining_cost = c; ci.inlining = i
        s = ccall(:jl_compress_ir, Any, (Any, Any), ctx.method, ci)::String
        return jobj("s" => "\"str\"", "c" => Int(c), "i" => Int(i)), s
    elseif r < 0.72
        b = rand(rng, UInt8)
        return jobj("s" => "\"u8\"", "b" => Int(b)), b
    elseif r < 0.82
        return jobj("s" => "\"ir\""), rand(rng, ctx.irs).src
    elseif r < 0.94
        c = rand_u16(rng); i = rand(rng, UInt8(0):UInt8(3))
        ci = copy(ctx.ci); ci.inlining_cost = c; ci.inlining = i
        os = CC.OptimizationState(ctx.mis[1], ci, ctx.interp)
        return jobj("s" => "\"opt\"", "c" => Int(c), "i" => Int(i)), os
    end
    return jobj("s" => "\"other\""), nothing
end

function rand_compressed_src(rng, ctx::Ctx)
    while true
        s, x = rand_src(rng, ctx)
        (x isa Core.CodeInfo || x isa String) && return s, x
    end
end

function result_facts(mi::Core.MethodInstance, @nospecialize(rt), interp)
    def = mi.def
    dm = isa(def, Method)
    sig = Base.unwrap_unionall(mi.specTypes)
    st = isa(sig, DataType) && sig.name === Tuple.name
    rt′ = CC.widenslotwrapper(rt)
    rb = rt′ === Union{}
    dt = Base.isdispatchtuple(mi.specTypes)
    tr = CC.:⊑(CC.optimizer_lattice(interp), rt′, Tuple) && !isconcretetype(CC.widenconst(rt′))
    mt = dm && def.module === CC._topmod(def.module)
    nm = dm ? string(def.name) : ""
    return jobj("dm" => jb(dm), "st" => jb(st), "rb" => jb(rb), "dt" => jb(dt), "tr" => jb(tr),
                "mt" => jb(mt), "nm" => jstr(nm))
end

const EARLY_FS = Any[Core.Intrinsics.add_int, Core.Intrinsics.pointerref, Core.Intrinsics.llvmcall,
    Core.Intrinsics.sqrt_llvm, Core.tuple, Core.:(===), typeof, Core.getfield, Core.isa, Core.svec,
    Base.compilerbarrier, Core.ifelse, Core.task_result_type, Base.:+, Core.typeassert, Core.throw,
    Core.setfield!, Core.nfields, Core.sizeof, Core._typevar]
const ARG2S = Any[CC.Const(true), CC.Const(false), CC.Const(:conditional), CC.Const(:const), CC.Const(:type),
    CC.Const(1), Bool, Any, Task, CC.Const(nothing), Int, Union{Bool,Nothing}, CC.Const(Task)]
try
    push!(ARG2S, CC.Conditional(1, Int, Any))
catch
end

function early_case(rng, ctx::Ctx)
    f = rand(rng, EARLY_FS)
    na = rand(rng) < 0.7 ? (f === Core.ifelse ? 4 : f === Base.compilerbarrier ? 3 :
                             f === Core.task_result_type ? 2 : rand(rng, 1:5)) : rand(rng, 1:5)
    ft = CC.Const(f)
    argtypes = Any[ft]
    for i in 2:na
        push!(argtypes, rand(rng, ARG2S))
    end
    # Steer the special callees to the inputs their rewrites need.
    if na >= 2 && rand(rng) < 0.6
        f === Base.compilerbarrier && (argtypes[2] = rand(rng, Any[CC.Const(:conditional), CC.Const(:type), CC.Const(1), Symbol]))
        f === Core.ifelse && (argtypes[2] = rand(rng, Any[CC.Const(true), CC.Const(false), Bool, CC.Const(1)]))
        f === Core.task_result_type && (argtypes[2] = rand(rng, Any[Task, CC.Const(Task), Any]))
    end
    type = rand(rng, CONSTS)
    f in (Base.compilerbarrier, Core.ifelse, Core.task_result_type) && rand(rng) < 0.5 &&
        (type = rand(rng, Any[Int, Any, Bool, CC.Const("str"), CC.Const(Int), CC.Const(1)]))
    flag = rand(rng) < 0.4 ? (rand(rng, Bool) ? CC.IR_FLAG_NOTHROW : zero(UInt32)) : rand_flag(rng)
    e34 = rand(rng) < 0.3
    a3 = Core.SSAValue(93)
    stmt = Expr(:call, f, Core.SSAValue(92), a3, e34 ? a3 : Core.SSAValue(94))
    inl = rand(rng) < 0.9
    interp = inl ? ctx.interp : CC.NativeInterpreter(; opt_params=CC.OptimizationParams(; inlining=false))
    state = CC.InliningState(interp)
    𝕃ₒ = CC.optimizer_lattice(interp)
    sig = CC.Signature(f, ft, argtypes)
    tc = type isa CC.Const
    vi = tc && CC.is_inlineable_constant(type.val)
    fi = f isa Core.IntrinsicFunction
    pi = fi && CC.is_pure_intrinsic_infer(f)
    sp = f === Base.compilerbarrier ? "compilerbarrier" : f === Core.ifelse ? "ifelse" :
         f === Core.task_result_type ? "task_result_type" : "none"
    a2 = na >= 2 ? argtypes[2] : Union{}
    a2c = na >= 2 && a2 isa CC.Const
    a2s = a2c && a2.val isa Symbol
    a2cd = a2s && a2.val === :conditional
    a2t = a2c && a2.val === true
    a2f = a2c && a2.val === false
    a2b = na >= 2 && CC.:⊑(𝕃ₒ, a2, Bool)
    a2k = na >= 2 && CC.:⊑(𝕃ₒ, a2, Task)
    facts = jobj("inl" => jb(inl), "tc" => jb(tc), "vi" => jb(vi), "fi" => jb(fi), "pi" => jb(pi),
        "ip" => jb(CC.contains_is(CC._PURE_BUILTINS, f)), "ie" => jb(CC.contains_is(CC._EFFECT_FREE_BUILTINS, f)),
        "sp" => jstr(sp), "na" => na, "a2c" => jb(a2c), "a2s" => jb(a2s), "a2cd" => jb(a2cd),
        "a2t" => jb(a2t), "a2f" => jb(a2f), "a2b" => jb(a2b), "a2k" => jb(a2k), "e34" => jb(e34))
    ieq = try
        tc && CC.quoted(type.val) == CC.quoted(CC.instanceof_tfunc(type)[1])
    catch
        false
    end
    ir = rand(rng, ctx.irs).src
    exp = guarded() do
        res = CC.early_inline_special_case(ir, stmt, flag, type, sig, state)
        tag = if res === nothing
            "none"
        elseif tc && res.val == CC.quoted(type.val)
            "quoted"
        elseif res.val === stmt.args[3]
            "arg3"
        elseif res.val === stmt.args[4]
            "arg4"
        elseif res.val == CC.quoted(CC.instanceof_tfunc(type)[1])
            "instanceof"
        else
            "unknown"
        end
        jsonexp(jstr(tag))
    end
    return [facts, string(flag), jb(ieq)], exp
end

const ATYPES = Any[Tuple{typeof(sum),Int}, Tuple{typeof(sum),Union{Int,Float64}}, Union{Tuple{Int},Tuple{Float64}},
    Tuple{Vector{T}} where T, Tuple{Vararg{Int}}]
const SIGS = Any[Tuple{typeof(sum),Int}, Tuple{typeof(sum),Float64}, Tuple{Vector{T}} where T,
    Union{Tuple{Int},Tuple{Float64}}, Tuple{Any}]

function handle_cases_case(rng, ctx::Ctx)
    e = rand(rng, ctx.irs)
    ir = copy(e.src)
    idx = rand(rng, 1:length(ir.stmts))
    oldflag = rand_flag(rng)
    ir[Core.SSAValue(idx)][:flag] = oldflag
    hac = rand(rng, Bool); fc = rand(rng, Bool)
    ncases = rand(rng) < 0.5 ? rand(rng, 0:1) : rand(rng, 0:4)
    atype = rand(rng) < 0.8 ? ATYPES[1 + (rand(rng) < 0.7 ? 0 : rand(rng, 1:4))] : rand(rng, ATYPES)
    sentinel = Core.SSAValue(10^6)
    cases = CC.InliningCase[CC.InliningCase(rand(rng) < 0.85 ? SIGS[rand(rng, 1:2)] : rand(rng, SIGS),
                                            CC.ConstantCase(sentinel)) for _ in 1:ncases]
    joint = rand_effects(rng)
    todo = Pair{Int,Any}[]
    stmt = Expr(:call, sum, 1)
    args = [jb(hac), jb(fc), string(ncases), jb(isa(atype, DataType)),
            jarr([jb(isa(c.sig, DataType)) for c in cases]), senc(joint), string(oldflag)]
    exp = guarded() do
        CC.handle_cases!(todo, ir, idx, stmt, atype, cases, hac, fc, joint)
        newflag = ir[Core.SSAValue(idx)][:flag]
        s = if ir[Core.SSAValue(idx)][:stmt] === sentinel
            "\"single\""
        elseif !isempty(todo)
            us = todo[1].second::CC.UnionSplit
            "[\"us\"," * jb(us.handled_all_cases) * "," * jb(us.fully_covered) * "]"
        elseif newflag != oldflag
            "[\"flags\"," * string(newflag) * "]"
        else
            "\"none\""
        end
        jsonexp(s)
    end
    return args, exp
end

function gen_case(rng, id::Int, io::IO, ctx::Ctx)
    op = pick_op(rng)
    args = String[]
    exp = ""
    if op == "inl.consts"
        xs = UInt32[CC.IR_FLAG_NULL, CC.IR_FLAG_INBOUNDS, CC.IR_FLAG_INLINE, CC.IR_FLAG_NOINLINE,
            CC.IR_FLAG_CONSISTENT, CC.IR_FLAG_EFFECT_FREE, CC.IR_FLAG_NOTHROW, CC.IR_FLAG_TERMINATES,
            CC.IR_FLAG_NOUB, CC.IR_FLAG_NORTCALL, CC.IR_FLAG_RESET_SAFE, CC.IR_FLAG_REFINED, CC.IR_FLAG_UNUSED,
            CC.IR_FLAG_EFIIMO, CC.IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM, CC.IR_FLAG_RSIIMO, CC.IR_FLAGS_EFFECTS,
            CC.IR_FLAGS_REMOVABLE, CC.IR_FLAGS_NEEDS_EA]
        ys = Int[CC.NUM_IR_FLAGS, CC.SLOT_STATICUNDEF, CC.SLOT_ASSIGNEDONCE, CC.SLOT_USEDUNDEF,
            CC.MAX_INLINE_COST, CC.MIN_INLINE_COST, CC.SRC_FLAG_DECLARED_INLINE, CC.SRC_FLAG_DECLARED_NOINLINE]
        exp = numsexp(vcat(Int.(xs), ys))
    elseif op == "inl.hasFlag"
        a = rand_flag(rng); b = rand(rng) < 0.6 ? rand(rng, FLAG_BITS) : rand_flag(rng)
        rand(rng) < 0.3 && (a |= b)
        args = [string(a), string(b)]
        exp = guarded(() -> boolexp(CC.has_flag(a, b)))
    elseif op == "inl.isStmtInline" || op == "inl.isStmtNoinline"
        a = rand_flag(rng)
        args = [string(a)]
        exp = guarded(() -> boolexp(op == "inl.isStmtInline" ? CC.is_stmt_inline(a) : CC.is_stmt_noinline(a)))
    elseif op == "inl.iscallstmt"
        h = rand(rng, HEADS)
        args = [h === nothing ? "null" : jstr(string(h))]
        exp = guarded(() -> boolexp(CC.iscallstmt(h === nothing ? Core.SSAValue(1) : Expr(h))))
    elseif op == "inl.flagsForEffects"
        e = rand_effects(rng)
        args = [senc(e)]
        exp = guarded(() -> numsexp([CC.flags_for_effects(e)]))
    elseif op == "inl.plusSaturate"
        x = rand_int(rng); y = rand_int(rng)
        rand(rng) < 0.3 && (x = abs(x) % (typemax(Int) ÷ 2) + typemax(Int) ÷ 2)
        args = [string(x), string(y)]
        exp = guarded(() -> jsonexp(string(CC.plus_saturate(x, y))))
    elseif op == "inl.clamp"
        x = rand_int(rng)
        args = [string(x)]
        exp = guarded(() -> numsexp([CC.inline_cost_clamp(x)]))
    elseif op == "inl.encode"
        c = rand_u16(rng)
        args = [string(c)]
        exp = guarded(() -> numsexp([ccall(:jl_encode_inlining_cost, UInt8, (UInt16,), c)]))
    elseif op == "inl.decode"
        b = rand(rng, UInt8)
        args = [string(b)]
        exp = guarded(() -> numsexp([ccall(:jl_decode_inlining_cost, UInt16, (UInt8,), b)]))
    elseif op == "inl.inliningCost" || op == "inl.isInlineable"
        s, x = rand_src(rng, ctx)
        args = [s]
        exp = guarded(() -> op == "inl.inliningCost" ? numsexp([CC.inlining_cost(x)]) : boolexp(CC.is_inlineable(x)))
    elseif op == "inl.isDeclaredInline" || op == "inl.isDeclaredNoinline"
        s, x = rand_compressed_src(rng, ctx)
        args = [s]
        exp = guarded(() -> boolexp(op == "inl.isDeclaredInline" ? CC.is_declared_inline(x) : CC.is_declared_noinline(x)))
    elseif op == "inl.setInlineable"
        v = rand(rng, Bool)
        args = [jb(v)]
        exp = guarded(() -> (ci = copy(ctx.ci); CC.set_inlineable!(ci, v); numsexp([ci.inlining_cost])))
    elseif op == "inl.srcPolicy"
        s, x = rand_src(rng, ctx)
        flag = rand_flag(rng)
        args = [s, string(flag)]
        exp = guarded(() -> boolexp(CC.src_inlining_policy(ctx.interp, x, CC.NoCallInfo(), flag)))
    elseif op == "inl.srcPolicyMI"
        mi = rand(rng, ctx.mis)
        s, x = rand_src(rng, ctx)
        flag = rand_flag(rng)
        dm = isa(mi.def, Method)
        hg = dm && CC.hasgenerator(mi)
        mg = dm && hg && CC.may_invoke_generator(mi)
        args = [jb(dm), jb(hg), jb(mg), s, string(flag)]
        exp = guarded(() -> boolexp(CC.src_inlining_policy(ctx.interp, mi, x, CC.NoCallInfo(), flag)))
    elseif op == "inl.stmtCost"
        e = rand(rng, ctx.pool)
        line = rand(rng, 1:length(e.stmts))
        pen = rand_penalty(rng)
        p = CC.OptimizationParams(; inline_nonleaf_penalty=pen)
        args = [e.stmts[line], string(line), jb(e.isIR), e.blockfirst, string(pen)]
        stmt = body_of(e)[line]
        exp = guarded(() -> jsonexp(string(CC.statement_or_branch_cost(stmt, line, e.src, e.sptypes, p))))
    elseif op == "inl.stmtCosts"
        e = rand(rng, ctx.pool)
        pen = rand_penalty(rng)
        p = CC.OptimizationParams(; inline_nonleaf_penalty=pen)
        args = [jarr(e.stmts), jb(e.isIR), e.blockfirst, string(pen)]
        body = e.isIR ? e.src.stmts.stmt : e.src.code
        exp = guarded() do
            cost = Vector{Int}(undef, length(body))
            m = CC.statement_costs!(cost, body, e.src, e.sptypes, p)
            jsonexp("{\"c\":" * jarr(cost) * ",\"m\":" * string(m) * "}")
        end
    elseif op == "inl.bodyCost"
        e = rand(rng, ctx.irs)
        pen = rand_penalty(rng)
        th = rand(rng) < 0.3 ? rand(rng, 0:600) : rand_threshold(rng)
        p = CC.OptimizationParams(; inline_nonleaf_penalty=pen)
        args = [jarr(e.stmts), e.blockfirst, string(pen), string(th)]
        exp = guarded(() -> numsexp([CC.inline_cost_model(e.src, p, th)]))
    elseif op == "inl.threshold"
        e = rand(rng, ctx.irs)
        mi = rand(rng) < 0.5 ? e.mi : rand(rng, ctx.mis)
        rt = rand(rng, RTS)
        flag = rand(rng) < 0.85 ? rand(rng, UInt8(0):UInt8(3)) : rand(rng, UInt8)
        th = rand_threshold(rng); pen = rand_penalty(rng); bonus = rand_bonus(rng)
        rand(rng) < 0.5 && (pen = 1000)
        p = CC.OptimizationParams(; inline_cost_threshold=th, inline_nonleaf_penalty=pen,
                                  inline_tupleret_bonus=bonus)
        interp = CC.NativeInterpreter(; opt_params=p)
        facts = try
            result_facts(mi, rt, interp)
        catch
            nothing
        end
        if facts === nothing
            op = "inl.flagsForEffects"
            ef = rand_effects(rng); args = [senc(ef)]
            exp = guarded(() -> numsexp([CC.flags_for_effects(ef)]))
        else
            args = [jarr([th, pen, bonus]), facts, string(flag), e.blockfirst, jarr(e.stmts)]
            exp = guarded() do
                result = CC.InferenceResult(mi)
                result.result = rt
                numsexp([CC.inline_cost_model(interp, result, flag, e.src)])
            end
        end
    elseif op == "inl.constabi"
        rt = rand(rng, CONSTS)
        ef = rand(rng) < 0.3 ? CC.EFFECTS_TOTAL : rand_effects(rng)
        mi = rand(rng, ctx.mis)
        isc = rt isa CC.Const
        vi = isc && CC.is_inlineable_constant(rt.val)
        args = [jb(isc), senc(ef), jb(vi)]
        exp = guarded() do
            result = CC.InferenceResult(mi)
            result.result = rt
            result.ipo_effects = ef
            boolexp(CC.is_result_constabi_eligible(result))
        end
    elseif op == "inl.early"
        args, exp = early_case(rng, ctx)
    elseif op == "inl.handleCases"
        args, exp = handle_cases_case(rng, ctx)
    elseif op == "inl.inlineConst"
        e = rand(rng, ctx.irs)
        ir = copy(e.src)
        idx = rand(rng, 1:length(ir.stmts))
        rt = rand(rng, CONSTS)
        flag = rand_flag(rng)
        isc = rt isa CC.Const
        vi = isc && CC.is_inlineable_constant(rt.val)
        args = [jb(isc), jb(vi), string(flag)]
        exp = guarded() do
            inst = ir[Core.SSAValue(idx)]
            inst[:type] = rt
            inst[:flag] = flag
            b = CC.inline_const_if_inlineable!(inst)
            jsonexp("[" * jb(b) * "," * string(inst[:flag]) * "]")
        end
    elseif op == "inl.linear"
        e = rand(rng, ctx.irs)
        ir = e.src
        nb = length(ir.cfg.blocks)
        term = ir[Core.SSAValue(last(ir.cfg.blocks[1].stmts))][:stmt]
        t = isa(term, Core.ReturnNode) ? (isdefined(term, :val) ? "rv" : "ru") : "o"
        args = [string(nb), jobj("t" => jstr(t))]
        exp = guarded(() -> boolexp(CC.linear_inline_eligible(ir)))
    end
    println(io, "{\"id\":", id, ",\"op\":", jstr(op), ",\"L\":\"typeinf\",\"a\":", jarr(args),
            ",\"next\":0,\"exp\":", exp, "}")
    return op
end

# What the statements of the pool exercise, so a run shows the edge cases were reached.
function pool_histogram(pool::Vector{IREntry})
    h = Dict{String,Int}()
    for e in pool, s in e.stmts
        for (pat, name) in (("\"h\":\"meta\"", "meta"), ("\"t\":\"i\",\"as\":true", "intrinsic"),
                            ("\"ll\":true", "llvmcall"), ("\"k\":\"memoryrefget\"", "memoryrefget"),
                            ("\"k\":\"memoryrefset!\"", "memoryrefset!"), ("\"k\":\"memoryrefunset!\"", "memoryrefunset!"),
                            ("\"k\":\"memoryref_isassigned\"", "memoryref_isassigned"), ("\"k\":\"typeassert\"", "typeassert"),
                            ("\"k\":\"getfield\"", "getfield"), ("\"k\":\"invoke\"", "builtin invoke"),
                            ("\"h\":\"fc\",\"sp\":true", "jl_string_ptr"), ("\"h\":\"fc\"", "foreigncall"),
                            ("\"h\":\"fg\"", "foreignglobal"), ("\"h\":\"inv\"", "invoke"),
                            ("\"h\":\"=\"", "assign"), ("\"h\":\"=e\"", "assign expr"), ("\"g\":true", "global assign"),
                            ("\"h\":\"copyast\"", "copyast"), ("\"k\":\"g\"", "goto"), ("\"k\":\"gi\"", "gotoifnot"),
                            ("\"k\":\"enter\"", "enter"), ("\"fi\":true,\"fs\":true,\"dr\":true", "recovered intrinsic"),
                            ("\"rb\":true", "Union{} result"), ("\"t\":\"o\"},\"fi\"", "generic call"))
            occursin(pat, s) && (h[name] = get(h, name, 0) + 1)
        end
    end
    return sort(collect(h))
end

function main(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    t0 = time()
    pool = build_pool(rng, max(60, n ÷ 60))
    irs = filter(e -> e.isIR, pool)
    m = only(methods(Gen.noinl))
    ci = Base.uncompressed_ir(m)
    ctx = Ctx(pool, irs, mi_pool(), m, ci, CC.NativeInterpreter())
    println("POOL $(length(pool)) sources ($(length(irs)) IRCode), $(sum(e -> length(e.stmts), pool)) statements, ",
            round(time() - t0; digits=1), " s")
    for (k, v) in pool_histogram(pool)
        println("  ", rpad(k, 22), v)
    end
    dir = mktempdir()
    casefile = joinpath(dir, "cases.jsonl")
    ops = Dict{Int,String}()
    open(casefile, "w") do io
        for id in 1:n
            ops[id] = gen_case(rng, id, io, ctx)
        end
    end
    # Expected outcomes of the decision ops, so a run shows every branch was reached.
    outcomes = Dict{String,Int}()
    for line in eachline(casefile)
        op = match(r"\"op\":\"([^\"]+)\"", line)[1]
        op in ("inl.stmtCost", "inl.bodyCost", "inl.threshold", "inl.early", "inl.handleCases",
               "inl.srcPolicyMI", "inl.clamp", "inl.isDeclaredInline", "inl.inlineConst") || continue
        ex = match(r"\"exp\":(.*)}$", line)[1]
        key = occursin("\"err\"", ex) ? "error " * ex :
              op in ("inl.early",) ? ex :
              op == "inl.handleCases" ? first(ex, 18) :
              op in ("inl.bodyCost", "inl.threshold", "inl.clamp") ?
                  (occursin("[65535]", ex) ? "MAX" : occursin("[10]", ex) ? "MIN" : "other") :
              op in ("inl.srcPolicyMI", "inl.isDeclaredInline") ? ex :
              op == "inl.inlineConst" ? first(ex, 14) : "value"
        k = op * " " * key
        outcomes[k] = get(outcomes, k, 0) + 1
    end
    for (k, v) in sort(collect(outcomes))
        println("  ", rpad(k, 50), v)
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
        mm = match(r"\"id\":(\d+)", line)
        if mm === nothing
            push!(bad, line); continue
        end
        id = parse(Int, mm[1]); seen += 1
        st = get!(perop, ops[id], [0, 0])
        if occursin("\"agree\":true", line)
            agree += 1; st[1] += 1
        else
            push!(bad, line); st[2] += 1
        end
    end
    for (op, st) in sort(collect(perop))
        println(rpad(op, 24), " agree=", st[1], " disagree=", st[2])
    end
    for line in first(bad, parse(Int, opts["show"]))
        println("DISAGREE ", first(line, 1500))
    end
    println("SEED $seed CASES $n ANSWERED $seen")
    println("AGREE $agree/$seen")
    rm(dir; recursive=true)
    return isempty(bad) && seen == n ? 0 : 1
end

exit(main())
