# Checks on the pinned Julia of the branch-by-branch statements added after the review of the
# inlining area (JuliaLean/Proofs/Compiler/src/optimize/Exact.lean and the "Exact decisions"
# section of JuliaLean/Proofs/Compiler/src/ssair/inlining.lean). Each check calls the Compiler
# function and compares it with the value the Lean statement gives.
#
#     $JULIA difftest/compiler/inlining_props.jl
#
# Prints one line per check with the number of cases and failures, then `PROPS OK` or
# `PROPS FAILED`.
#
# Runs:
#   2026-11-10, pinned Julia 1.15.0-DEV.184 f755f49a9e: PROPS OK, no failures. Cases per check:
#   inlining_cost(UInt8) 256, below 32 32, is_inlineable(UInt8) 256, CodeInfo/String 35,
#   non-sources 6, is_declared_* 25, is_stmt_* bits 42008, statement_cost branches 23,
#   statement_or_branch_cost on CodeInfo 75 and on IRCode 497, statement_costs! 12.

const CC = Base.Compiler
using Random

const results = Pair{String,Tuple{Int,Int}}[]
const firstfail = Dict{String,Any}()

function check(name, cases)
    n = 0; bad = 0
    for (input, got, want) in cases
        n += 1
        if !isequal(got, want)
            bad += 1
            haskey(firstfail, name) || (firstfail[name] = (input, got, want))
        end
    end
    push!(results, name => (n, bad))
end

trycall(f) = try
    f()
catch err
    typeof(err)
end

const MAXC = CC.MAX_INLINE_COST
decode(b::UInt8) = ccall(:jl_decode_inlining_cost, UInt16, (UInt8,), b)
encode(c::UInt16) = ccall(:jl_encode_inlining_cost, UInt8, (UInt16,), c)

f_plain(x) = x + 1
@inline f_inl(x) = x + 2
@noinline f_noinl(x) = x + 3

lowered(f, T) = first(code_lowered(f, T))
methodof(f, T) = which(f, T)

# InliningCostExact and IsInlineableExact
check("inlining_cost(UInt8) == decode", ((b, CC.inlining_cost(b), decode(b)) for b in 0x00:0xff))
check("inlining_cost(UInt8 < 32) == b", ((b, CC.inlining_cost(b), UInt16(b)) for b in 0x00:0x1f))
check("is_inlineable(UInt8) == (b != 0xff)", ((b, CC.is_inlineable(b), b != 0xff) for b in 0x00:0xff))
let ci = lowered(f_plain, (Int,))
    cases = []
    for c in UInt16[0, 1, 10, 31, 63, 64, 3968, 3969, 65534, 65535]
        ci.inlining_cost = c
        push!(cases, (c, CC.inlining_cost(ci), c))
        push!(cases, (c, CC.is_inlineable(ci), c != MAXC))
        s = ccall(:jl_compress_ir, Any, (Any, Any), methodof(f_plain, (Int,)), ci)::String
        push!(cases, (c, CC.inlining_cost(s), decode(encode(c))))
        c < 64 && push!(cases, (c, CC.inlining_cost(s), c))
    end
    check("inlining_cost/is_inlineable CodeInfo and String", cases)
end
let ir = first(Base.code_ircode(f_plain, (Int,)))[1]
    check("non-sources cost MAX_INLINE_COST, not inlineable",
        [(:nothing, CC.inlining_cost(nothing), MAXC), (:nothing, CC.is_inlineable(nothing), false),
         (:IRCode, CC.inlining_cost(ir), MAXC), (:IRCode, CC.is_inlineable(ir), false),
         (:Int, CC.inlining_cost(1), MAXC), (:Int, CC.is_inlineable(1), false)])
end

# DeclaredInlineExact
let cases = []
    for (f, want) in ((f_plain, 0x00), (f_inl, 0x01), (f_noinl, 0x02))
        ci = lowered(f, (Int,))
        push!(cases, (f, ci.inlining, want))
    end
    ci = lowered(f_plain, (Int,))
    m = methodof(f_plain, (Int,))
    for i in 0x00:0x03
        ci.inlining = i
        push!(cases, (i, CC.is_declared_inline(ci), i == 0x01))
        push!(cases, (i, CC.is_declared_noinline(ci), i == 0x02))
        s = ccall(:jl_compress_ir, Any, (Any, Any), m, ci)::String
        push!(cases, (i, CC.is_declared_inline(s), i == 0x01))
        push!(cases, (i, CC.is_declared_noinline(s), i == 0x02))
    end
    ir = first(Base.code_ircode(f_plain, (Int,)))[1]
    for x in (nothing, 0x05, ir)
        push!(cases, (typeof(x), trycall(() -> CC.is_declared_inline(x)), MethodError))
        push!(cases, (typeof(x), trycall(() -> CC.is_declared_noinline(x)), MethodError))
    end
    check("is_declared_inline/noinline exact", cases)
end

# StmtInlineExact
let rng = Random.Xoshiro(1)
    flags = UInt32[0, CC.IR_FLAG_INLINE, CC.IR_FLAG_NOINLINE, typemax(UInt32)]
    append!(flags, rand(rng, UInt32, 20000))
    cases = []
    for f in flags
        push!(cases, (f, CC.is_stmt_inline(f), (f >> 1) & 1 == 1))
        push!(cases, (f, CC.is_stmt_noinline(f), (f >> 2) & 1 == 1))
    end
    for _ in 1:2000
        e = CC.Effects(; consistent = rand(rng, (0x00, 0x01, 0x02, 0x04, 0x06)),
            effect_free = rand(rng, (0x00, 0x01, 0x02, 0x03)), reset_safe = rand(rng, (0x00, 0x01, 0x02)),
            nothrow = rand(rng, Bool), terminates = rand(rng, Bool), notaskstate = rand(rng, Bool),
            inaccessiblememonly = rand(rng, (0x00, 0x01, 0x02)), noub = rand(rng, (0x00, 0x01, 0x02)),
            nonoverlayed = rand(rng, (0x00, 0x01, 0x02)), nortcall = rand(rng, Bool))
        fl = CC.flags_for_effects(e)
        push!(cases, (e, (CC.is_stmt_inline(fl), CC.is_stmt_noinline(fl)), (false, false)))
    end
    check("is_stmt_inline/noinline are bits 1 and 2", cases)
end

# StatementCostExact (branches that need no type answers beyond constants)
const params = CC.OptimizationParams()
const pen = params.inline_nonleaf_penalty
sc(ex) = trycall(() -> CC.statement_cost(ex, -1, lowered(f_plain, (Int,)), CC.VarState[], params))
ifunc_cost(f) = CC.T_IFUNC_COST[Int(reinterpret(Int32, f)) + 1]
let I = Core.Intrinsics, cases = []
    push!(cases, (:meta, sc(Expr(:meta, :inline)), 0))
    push!(cases, (:boundscheck, sc(Expr(:boundscheck)), 0))
    push!(cases, (:copyast, sc(Expr(:copyast, QuoteNode(:(x + 1)))), 100))
    push!(cases, (:foreigncall, sc(Expr(:foreigncall, QuoteNode(:strlen), Csize_t, Core.svec(Ptr{UInt8}), 0, QuoteNode(:ccall), C_NULL)), 20))
    push!(cases, (:foreigncall_strptr, sc(Expr(:foreigncall, Expr(:tuple, QuoteNode(:jl_string_ptr)), Ptr{UInt8}, Core.svec(Any), 0, QuoteNode(:ccall), "a")), 1))
    push!(cases, (:new, sc(Expr(:new, Some{Int}, 1)), 0))
    push!(cases, (:getfield, sc(Expr(:call, GlobalRef(Core, :getfield), (1, 2), 1)), 0))
    push!(cases, (:tuple, sc(Expr(:call, GlobalRef(Core, :tuple), 1, 2)), 0))
    push!(cases, (:typeassert_const, sc(Expr(:call, GlobalRef(Core, :typeassert), 1, Int)), 1))
    push!(cases, (:typeassert_one, sc(Expr(:call, GlobalRef(Core, :typeassert), 1)), BoundsError))
    push!(cases, (:generic_call, sc(Expr(:call, GlobalRef(Base, :sin), 1.0)), pen))
    push!(cases, (:assign_local, sc(Expr(:(=), Core.SlotNumber(2), 1)), 0))
    push!(cases, (:assign_global, sc(Expr(:(=), GlobalRef(Main, :G), 1)), 3))
    push!(cases, (:assign_global_expr, sc(Expr(:(=), GlobalRef(Main, :G), Expr(:call, GlobalRef(Base, :sin), 1.0))), 3 + pen))
    for f in (I.add_int, I.mul_int, I.sub_int, I.mul_float, I.div_float, I.sqrt_llvm, I.neg_int)
        k = ifunc_cost(f)
        nargs = f in (I.sqrt_llvm, I.neg_int) ? 2 : 3
        args = nargs == 3 ? (1, 2) : (2,)
        args = f in (I.mul_float, I.div_float, I.sqrt_llvm) ? Float64.(args) : args
        want = (k == 0 || nargs < 3) ? k : (k - 1) ÷ 2
        push!(cases, (Symbol(f), sc(Expr(:call, GlobalRef(I, nameof(f)), args...)), want))
    end
    push!(cases, (:add_int_arity, sc(Expr(:call, GlobalRef(I, :add_int), 1)), 20))
    push!(cases, (:llvmcall, sc(Expr(:call, GlobalRef(I, :llvmcall), "ret void", Cvoid, Tuple{})), 20))
    check("statement_cost branches", cases)
end

# StatementOrBranchCostExact on a CodeInfo
let ci = lowered(f_plain, (Int,)), cases = []
    sobc(stmt, line) = CC.statement_or_branch_cost(stmt, line, ci, CC.VarState[], params)
    for t in 1:6, line in 1:6
        push!(cases, ((:goto, t, line), sobc(Core.GotoNode(t), line), t < line ? 40 : 0))
        push!(cases, ((:gotoifnot, t, line), sobc(Core.GotoIfNot(true, t), line), t < line ? 40 : 0))
    end
    push!(cases, (:enter, sobc(Core.EnterNode(3), 1), typemax(Int)))
    push!(cases, (:return, sobc(Core.ReturnNode(1), 1), 0))
    push!(cases, (:pinode, sobc(Core.PiNode(1, Int), 1), 0))
    check("statement_or_branch_cost on CodeInfo", cases)
end
# ... and on an IRCode: the target is the first statement of the block.
loopy(n) = (s = 0; for i in 1:n; s += i; end; s)
let ir = first(Base.code_ircode(loopy, (Int,)))[1], cases = []
    nb = length(ir.cfg.blocks)
    for b in 1:nb, line in 1:length(ir.stmts)
        d = first(ir.cfg.blocks[b].stmts)
        push!(cases, ((b, line), CC.statement_or_branch_cost(Core.GotoNode(b), line, ir, ir.sptypes, params), d < line ? 40 : 0))
    end
    push!(cases, ((nb + 1,), trycall(() -> CC.statement_or_branch_cost(Core.GotoNode(nb + 1), 1, ir, ir.sptypes, params)), BoundsError))
    push!(cases, ((0,), trycall(() -> CC.statement_or_branch_cost(Core.GotoNode(0), 1, ir, ir.sptypes, params)), BoundsError))
    check("statement_or_branch_cost on IRCode", cases)
end

# StatementCostsExact
let cases = []
    for (f, T) in ((f_plain, (Int,)), (loopy, (Int,)), (sum, (Vector{Float64},)), (string, (Int, Float64)),
                   (sort!, (Vector{Int},)), (x -> try x catch; 0 end, (Int,)))
        ci = first(code_typed(f, T; optimize=false))[1]
        body = ci.code
        sptypes = CC.VarState[]
        cost = zeros(Int, length(body))
        m = CC.statement_costs!(cost, body, ci, sptypes, params)
        each = [CC.statement_or_branch_cost(body[l], l, ci, sptypes, params) for l in 1:length(body)]
        push!(cases, ((f, :costs), cost, each))
        push!(cases, ((f, :max), m, max(0, maximum(each; init=0))))
    end
    check("statement_costs! writes each line's cost and returns the max", cases)
end

bad = false
for (name, (n, nb)) in results
    println(rpad(name, 64), " cases ", n, " failures ", nb)
    if nb > 0
        global bad = true
        println("    first failure: ", firstfail[name])
    end
end
println(bad ? "PROPS FAILED" : "PROPS OK")
println("VERSION ", VERSION, " ", Base.GIT_VERSION_INFO.commit)
