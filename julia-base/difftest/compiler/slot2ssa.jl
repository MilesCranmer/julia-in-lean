# Differential test of the Lean model of Compiler/src/ssair/slot2ssa.jl
# (JuliaLean/Compiler/src/ssair/slot2ssa.lean) against the pinned Julia
# (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA difftest/compiler/slot2ssa.jl --cases 20000 --seed 1
#
# Operations:
#
#   ssa     end to end on the lowered code of a generated function: inference, then
#           `convert_to_ircode!`, then what `slot2reg` does (`construct_domtree`,
#           `scan_slot_def_use`, `construct_ssa!`, which ends in `domsort_ssa!`). The model gets
#           the IR after `convert_to_ircode!` plus what `construct_ssa!` reads from the
#           `OptimizationState` (block entry states, the `π` test results, the slot names, the
#           statement handlers, the static parameters). The whole result is compared: every
#           statement, every new node (position, `attach_after`, statement) and the CFG. Types
#           and line numbers are not compared (the model leaves them out).
#           The generated functions mix assignments, `if`/`else`, `while` and `for` loops with
#           `break`/`continue`, `try`/`catch`/`finally`, `local` (NewvarNode), `@isdefined`,
#           reads of possibly undefined locals, `@goto`/`@label` (irreducible flow), typed
#           locals, `return`/`error` inside branches (unreachable blocks), Union-typed slots that
#           inference narrows (π nodes), and static parameters.
#   scan    scan_slot_def_use on generated statement vectors (every IR node kind, slot ids out
#           of range, `nargs` larger than the slot count)
#   live    compute_live_ins on generated CFGs with sorted (and sometimes unsorted) def and use
#           statement lists, argument defs (0), duplicates and out-of-range statements
#   idf     iterated_dominance_frontier on generated CFGs (lowered shapes, irreducible loops,
#           self loops, unreachable cycles, catch blocks with the virtual predecessor 0), def
#           blocks with duplicates, unreachable defs, and with and without live-in pruning
#   redge   rename_incoming_edge, rename_outgoing_edge and rename_phinode_edges on generated
#           `result_order`/`bb_rename` pairs (fixup blocks 0, dropped blocks -1)
#   bfi     block_for_inst on generated CFG indices
#   fixup   fixup_uses! alone on generated statement vectors in a generated CFG: the use list of
#           one slot from scan_slot_def_use (sometimes with an extra or out-of-range entry), the
#           new value an SSA value, an argument, a literal or UNDEF_TOKEN, random
#           IR_FLAG_NOTHROW flags, static parameters with a Const or a non-Const type
#   dsort   domsort_ssa! alone on synthesized IR in BB addressing over generated CFGs (fall
#           throughs that stop being fall throughs, so the fixup `goto`s and split blocks run),
#           with phi nodes, uses of values from dominating and from unreachable blocks, and new
#           nodes
#
# Errors are compared by exception type. Prints `AGREE k/n`. As information only (not agreement
# with the model): how often the `ssa` cases reach each shape (`INFO features`), how many of
# their results fail `verify_ir` after `compact!`, and the smallest such function without
# `@goto`.
#
# Runs (seed, cases, agreement):
#   2026-11-10, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 20000 cases: AGREE 20000/20000 (ssa 7873, dsort 2735, idf 2770, live 2138,
#                        scan 2082, redge 1431, bfi 971)
#   seed 2, 20000 cases: AGREE 20000/20000 (ssa 7909, dsort 2639, idf 2655, live 2182,
#                        scan 2205, redge 1466, bfi 944)
#   seed 3, 20000 cases: AGREE 20000/20000 (ssa 8000, dsort 2641, idf 2631, live 2151,
#                        scan 2091, redge 1464, bfi 1022)
#   2026-11-10, after adding the fixup op and generalizing the model's fixemup! (same pinned Julia):
#   seed 1, 20000 cases: AGREE 20000/20000 (ssa 7848, idf 2742, live 2234, dsort 2212,
#                        scan 2140, fixup 1187, redge 928, bfi 709)
#   seed 2, 20000 cases: AGREE 20000/20000 (ssa 7996, idf 2655, live 2221, dsort 2187,
#                        scan 2074, fixup 1207, redge 935, bfi 725)
#   seed 3, 20000 cases: AGREE 20000/20000 (ssa 8022, idf 2707, live 2169, dsort 2154,
#                        scan 2136, fixup 1139, redge 961, bfi 712)
#   Per seed the ssa cases had phi nodes in ~2800, PhiC/upsilons in ~1240, π nodes in ~2700,
#   `throw_undef_if_not` in ~4300, inference-unreachable blocks in ~6600, static parameters in
#   ~1230; dsort had ~130 fixup gotos and ~120 split blocks.
#
# Leads for the property work (seen in these runs, not model mismatches):
#   * `construct_ssa!` throws `AssertionError: val.id > 0` (in `renumber_ssa` from
#     `domsort_ssa!`) on 7-9 functions per seed, all with a `@goto` into a loop, e.g.
#         function g2(a)
#             @goto L1
#             for i = 1:a
#                 w = 1
#                 while @isdefined(w)
#                     @label L1
#                     y = 1
#                 end
#             end
#             return 0
#         end
#     `code_typed(g2, (Int,))` throws on the pinned Julia. Calling the first such generated
#     function (seed 3) printed the internal inference error and then died with `Unreachable
#     reached` (SIGILL) on the pinned Julia, nightly 290d5bb5f5 and 1.13.3.
#   * 20-26 `ssa` results per seed fail `verify_ir` after `compact!`, 7-12 of them without
#     `@goto`; the messages are "Basic Block N does not dominate block N (tried to use value
#     %N at %N)" and "φ node N is not at the beginning of the basic block N".
# What the property work found for these leads (2026-11-10): the first is the known lowering
# bug JuliaLang/julia#61132 (SSA values of a `for` loop that the `@goto` skips). Every
# `verify_ir` failure without `@goto` that was inspected has a `catch` or `finally` body starting
# with a `while` loop, which makes the catch block a loop header; that is the miscompile
# `compiler-slot2ssa-catch-loop-header` (repro/compiler-slot2ssa-catch-loop-header.jl).

include(joinpath(@__DIR__, "common.jl"))
using .CFGSer
using .LatticeSer: jstr
using Random

const CC = Base.Compiler

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

## IR value encoding (the `decIRV`/`encIRV` format of CompilerDiff.lean)

litstr(@nospecialize(x)) = string(typeof(x), ":", repr(x))
optenc(v, i) = isassigned(v, i) ? enc(v[i]) : "null"

function enc(@nospecialize(x))
    x === nothing && return "\"nothing\""
    x === CC.UNDEF_TOKEN && return "\"undef\""
    x isa Core.SlotNumber && return jo("sl" => x.id)
    x isa Core.SSAValue && return jo("s" => x.id)
    x isa CC.NewSSAValue && return jo("ns" => x.id)
    x isa Core.Argument && return jo("a" => x.n)
    x isa GlobalRef && return jo("g" => jstr(string(x.mod, ".", x.name)))
    x isa Symbol && return jo("sym" => jstr(string(x)))
    x isa QuoteNode && return jo("q" => jstr(litstr(x.value)))
    x isa Expr && return jo("e" => jstr(string(x.head)), "x" => ja([enc(a) for a in x.args]))
    x isa Core.GotoNode && return jo("goto" => x.label)
    x isa Core.GotoIfNot && return jo("gin" => enc(x.cond), "d" => x.dest)
    if x isa Core.ReturnNode
        return isdefined(x, :val) ? jo("ret" => enc(x.val)) : jo("ret0" => "true")
    end
    if x isa Core.EnterNode
        return isdefined(x, :scope) ? jo("enter" => x.catch_dest, "sc" => enc(x.scope)) :
                                      jo("enter" => x.catch_dest)
    end
    x isa Core.NewvarNode && return jo("nv" => (x.slot::Core.SlotNumber).id)
    if x isa Core.PhiNode
        return jo("phi" => ja(Int.(x.edges)), "v" => ja([optenc(x.values, i) for i in 1:length(x.values)]))
    end
    x isa Core.PhiCNode && return jo("phic" => ja([optenc(x.values, i) for i in 1:length(x.values)]))
    if x isa Core.UpsilonNode
        return isdefined(x, :val) ? jo("ups" => enc(x.val)) : jo("ups0" => "true")
    end
    x isa Core.PiNode && return jo("pi" => enc(x.val), "t" => jstr(string(x.typ)))
    return jo("l" => jstr(litstr(x)))
end

encblocks(cfg) = ja([ja([first(b.stmts), last(b.stmts), ja(b.preds), ja(b.succs)]) for b in cfg.blocks])

function encir(ir)
    stmts = [enc(ir.stmts.stmt[i]) for i in 1:length(ir.stmts)]
    nn = [ja([ir.new_nodes.info[i].pos, string(ir.new_nodes.info[i].attach_after),
              enc(ir.new_nodes.stmts.stmt[i])]) for i in 1:length(ir.new_nodes)]
    jo("stmts" => ja(stmts), "nn" => ja(nn), "b" => encblocks(ir.cfg), "idx" => ja(ir.cfg.index))
end

## CFGs with statement ranges

function gen_succs(rng, n)
    succs = [Int[] for _ in 1:n]
    catches = Int[]
    r = rand(rng)
    for i in 1:n
        if r < 0.5              # lowered shapes: fall through, branch, goto, return, enter
            q = rand(rng)
            nxt = i < n ? [i + 1] : Int[]
            if i == n
                succs[i] = rand(rng) < 0.85 ? Int[] : [rand(rng, 1:n)]
            elseif q < 0.3
                succs[i] = nxt
            elseif q < 0.6
                t = rand(rng, 1:n); succs[i] = t == i + 1 ? nxt : [t; nxt]
            elseif q < 0.75
                succs[i] = [rand(rng, 1:n)]
            elseif q < 0.85
                succs[i] = Int[]
            else
                c = rand(rng, min(i + 1, n):n); succs[i] = unique([c; nxt]); push!(catches, c)
            end
        elseif r < 0.8          # random, with self loops and back edges into the entry
            for _ in 1:rand(rng, (0, 1, 1, 2, 2, 3))
                push!(succs[i], rand(rng) < 0.1 ? i : rand(rng) < 0.1 ? 1 : rand(rng, 1:n))
            end
            unique!(succs[i])
        else                    # a reachable part and an unreachable cycle
            m = max(1, n ÷ 2)
            if i <= m
                i < m && push!(succs[i], i + 1)
                rand(rng) < 0.4 && push!(succs[i], rand(rng, 1:m))
            else
                push!(succs[i], rand(rng, m+1:n))
                rand(rng) < 0.3 && push!(succs[i], rand(rng, 1:n))
            end
            unique!(succs[i])
        end
    end
    if n >= 4 && rand(rng) < 0.2        # an irreducible loop
        a, b = rand(rng, 2:n), rand(rng, 2:n)
        if a != b
            h = rand(rng, 1:min(a, b) - 1)
            for (x, y) in ((h, a), (h, b), (a, b), (b, a))
                y in succs[x] || push!(succs[x], y)
            end
        end
    end
    return succs, catches
end

# A CFG with statement ranges: `(blocks, index)` with `blocks[i] = (first, last, preds, succs)`.
function gen_scfg(rng; n=rand(rng) < 0.1 ? rand(rng, 1:2) : rand(rng) < 0.8 ? rand(rng, 2:10) : rand(rng, 11:40),
                  succfn=gen_succs)
    succs, catches = succfn(rng, n)
    preds = [Int[] for _ in 1:n]
    push!(preds[1], 0)
    for i in 1:n, s in succs[i]
        push!(preds[s], i)
    end
    for c in unique(catches)
        push!(preds[c], 0)
    end
    for i in 1:n
        rand(rng) < 0.1 && shuffle!(rng, preds[i])
    end
    sizes = [rand(rng, (1, 1, 2, 3, 4)) for _ in 1:n]
    firsts = cumsum([1; sizes[1:end-1]])
    blocks = [(firsts[i], firsts[i] + sizes[i] - 1, preds[i], succs[i]) for i in 1:n]
    index = [firsts[i] for i in 2:n]
    return blocks, index
end

mkcfg(blocks, index) = CC.CFG(CC.BasicBlock[CC.BasicBlock(CC.StmtRange(f, l), copy(p), copy(s))
                                           for (f, l, p, s) in blocks], copy(index))
jscfg(blocks, index) = ("b" => ja([ja([f, l, ja(p), ja(s)]) for (f, l, p, s) in blocks]),
                        "idx" => ja(index))
nstmts_of(blocks) = isempty(blocks) ? 0 : blocks[end][2]

function gen_bfi(rng, id, io)
    blocks, index = gen_scfg(rng)
    if rand(rng) < 0.05 && length(index) >= 2
        shuffle!(rng, index)                    # an unsorted index
    end
    cfg = mkcfg(blocks, index)
    q = [rand(rng, -1:nstmts_of(blocks) + 2) for _ in 1:10]
    exp = ja([tryj(() -> string(CC.block_for_inst(cfg, x))) for x in q])
    println(io, jo("id" => id, "s2s" => "\"bfi\"", jscfg(blocks, index)..., "q" => ja(q), "exp" => exp))
end

function gen_stmtlist(rng, nst; zero=false, dup=true)
    k = rand(rng, 0:min(8, 2nst))
    xs = sort!([rand(rng, 1:nst) for _ in 1:k])
    dup || unique!(xs)
    zero && pushfirst!(xs, 0)
    if rand(rng) < 0.03 && !isempty(xs)
        xs[rand(rng, 1:length(xs))] = nst + rand(rng, 1:3)   # past the last statement
        sort!(xs)
    end
    rand(rng) < 0.05 && shuffle!(rng, xs)                    # unsorted
    return xs
end

function gen_live(rng, id, io)
    blocks, index = gen_scfg(rng)
    nst = nstmts_of(blocks)
    defs = gen_stmtlist(rng, nst; zero=rand(rng) < 0.4)
    uses = gen_stmtlist(rng, nst)
    cfg = mkcfg(blocks, index)
    exp = tryj() do
        l = CC.compute_live_ins(cfg, defs, uses)
        jo("d" => ja(l.def_bbs), "l" => l.live_in_bbs === nothing ? "null" : ja(l.live_in_bbs))
    end
    println(io, jo("id" => id, "s2s" => "\"live\"", jscfg(blocks, index)..., "defs" => ja(defs),
                   "uses" => ja(uses), "exp" => exp))
end

function gen_idf(rng, id, io)
    blocks, index = gen_scfg(rng)
    n = length(blocks)
    cfg = mkcfg(blocks, index)
    r = rand(rng)
    local defs, live
    if r < 0.5
        # what compute_live_ins gives, maybe with an added catch-block def
        l = try
            CC.compute_live_ins(cfg, gen_stmtlist(rng, nstmts_of(blocks); zero=rand(rng) < 0.5),
                                gen_stmtlist(rng, nstmts_of(blocks)))
        catch
            CC.BlockLiveness([1], Int[])
        end
        defs = copy(l.def_bbs)
        rand(rng) < 0.2 && push!(defs, rand(rng, 1:n))
        live = rand(rng) < 0.8 ? l.live_in_bbs : nothing
    else
        defs = [rand(rng, 1:n) for _ in 1:rand(rng, 0:4)]
        live = rand(rng) < 0.4 ? nothing : unique([rand(rng, 1:n) for _ in 1:rand(rng, 0:n)])
    end
    if rand(rng) < 0.02
        push!(defs, n + 1)            # out of range: BoundsError
    end
    exp = tryj() do
        dt = CC.construct_domtree(cfg.blocks)
        ja(CC.iterated_dominance_frontier(cfg, CC.BlockLiveness(copy(defs),
            live === nothing ? nothing : copy(live)), dt))
    end
    println(io, jo("id" => id, "s2s" => "\"idf\"", jscfg(blocks, index)..., "defs" => ja(defs),
                   "live" => live === nothing ? "null" : ja(live), "exp" => exp))
end

function gen_redge(rng, id, io)
    n = rand(rng, 1:12)
    keep = [i == 1 || rand(rng) < 0.8 for i in 1:n]
    order = shuffle!(rng, findall(keep))
    if keep[1] && rand(rng) < 0.8
        filter!(!=(1), order); pushfirst!(order, 1)
    end
    ro = Int[]
    for b in order
        push!(ro, b)
        rand(rng) < 0.25 && push!(ro, 0)
    end
    br = fill(-1, n)
    for (k, b) in enumerate(ro)
        b == 0 || (br[b] = k)
    end
    if rand(rng) < 0.05
        br[rand(rng, 1:n)] = length(ro) + 1
    end
    k = rand(rng, ("in", "out", "phi"))
    x = rand(rng) < 0.05 ? rand(rng, -1:n + 1) : rand(rng, 0:n)
    y = rand(rng, 1:n)
    if k == "in"
        exp = tryj(() -> string(CC.rename_incoming_edge(x, y, ro, br)))
        println(io, jo("id" => id, "s2s" => "\"redge\"", "k" => "\"in\"", "ro" => ja(ro), "br" => ja(br),
                       "x" => x, "y" => y, "exp" => exp))
    elseif k == "out"
        x = max(x, 1)
        exp = tryj(() -> string(CC.rename_outgoing_edge(x, y, ro, br)))
        println(io, jo("id" => id, "s2s" => "\"redge\"", "k" => "\"out\"", "ro" => ja(ro), "br" => ja(br),
                       "x" => x, "y" => y, "exp" => exp))
    else
        m = rand(rng, 0:5)
        edges = Int32[rand(rng) < 0.15 ? 0 : rand(rng, 1:n) for _ in 1:m]
        vals = Vector{Any}(undef, m)
        for i in 1:m
            rand(rng) < 0.8 && (vals[i] = rand(rng) < 0.5 ? Core.SSAValue(rand(rng, 1:9)) : rand(rng, 1:3))
        end
        p = Core.PhiNode(edges, vals)
        exp = tryj(() -> enc(CC.rename_phinode_edges(p, y, ro, br)))
        println(io, jo("id" => id, "s2s" => "\"redge\"", "k" => "\"phi\"", "ro" => ja(ro), "br" => ja(br),
                       "x" => y, "y" => 0, "p" => enc(p), "exp" => exp))
    end
end

## Statement vectors for scan_slot_def_use

function gen_operand(rng, ns)
    r = rand(rng)
    r < 0.45 && return Core.SlotNumber(rand(rng) < 0.03 ? ns + 1 : rand(rng, 1:max(ns, 1)))
    r < 0.6 && return Core.SSAValue(rand(rng, 1:5))
    r < 0.7 && return GlobalRef(Base, :sin)
    r < 0.8 && return rand(rng, 1:3)
    r < 0.85 && return QuoteNode(:q)
    r < 0.9 && return Core.Argument(rand(rng, 1:3))
    return Expr(:call, GlobalRef(Base, :+), gen_operand(rng, ns), 1)
end

function gen_scan_stmt(rng, ns)
    r = rand(rng)
    sl() = Core.SlotNumber(rand(rng) < 0.03 ? ns + 1 : rand(rng, 1:max(ns, 1)))
    r < 0.12 && return Core.NewvarNode(sl())
    r < 0.30 && return Expr(:(=), sl(), rand(rng) < 0.5 ? gen_operand(rng, ns) :
                            Expr(:call, GlobalRef(Base, :+), gen_operand(rng, ns), gen_operand(rng, ns)))
    r < 0.34 && return Expr(:(=), GlobalRef(Main, :g), gen_operand(rng, ns))
    r < 0.38 && return Expr(:(=), sl(), Expr(:boundscheck))
    r < 0.48 && return Expr(:call, GlobalRef(Base, :f), [gen_operand(rng, ns) for _ in 1:rand(rng, 0:3)]...)
    r < 0.52 && return sl()
    r < 0.56 && return Core.ReturnNode(gen_operand(rng, ns))
    r < 0.58 && return Core.ReturnNode()
    r < 0.62 && return Core.GotoIfNot(gen_operand(rng, ns), 2)
    r < 0.64 && return Core.GotoNode(1)
    if r < 0.68
        vals = Vector{Any}(undef, 3)
        for i in 1:3
            rand(rng) < 0.7 && (vals[i] = gen_operand(rng, ns))
        end
        return Core.PhiNode(Int32[1, 2, 3], vals)
    end
    r < 0.71 && return Core.PiNode(gen_operand(rng, ns), Int)
    r < 0.74 && return Core.UpsilonNode(gen_operand(rng, ns))
    r < 0.76 && return Core.EnterNode(3, gen_operand(rng, ns))
    r < 0.79 && return Expr(:isdefined, sl())
    r < 0.82 && return Expr(:meta, sl())
    r < 0.85 && return Expr(:throw_undef_if_not, :x, gen_operand(rng, ns))
    r < 0.88 && return Expr(:new, GlobalRef(Base, :T), gen_operand(rng, ns))
    r < 0.90 && return Expr(:call)
    r < 0.93 && return nothing
    return Core.PhiCNode(Any[gen_operand(rng, ns)])
end

const SCAN_CI = let ci = copy(first(code_lowered(+, (Int, Int))))
    ci
end

function gen_scan(rng, id, io)
    ns = rand(rng, 0:6)
    nargs = rand(rng) < 0.05 ? ns + 1 : rand(rng, 0:ns)
    code = Any[gen_scan_stmt(rng, ns) for _ in 1:rand(rng, 0:10)]
    ci = copy(SCAN_CI)
    ci.slotflags = zeros(UInt8, ns)
    exp = tryj() do
        r = CC.scan_slot_def_use(nargs, ci, copy(code))
        ja([ja([ja(si.defs), ja(si.uses)]) for si in r])
    end
    println(io, jo("id" => id, "s2s" => "\"scan\"", "code" => ja([enc(s) for s in code]),
                   "nargs" => nargs, "nslots" => ns, "exp" => exp))
end

## fixup_uses! alone

# Statements of the scan generator (plus static parameters) in a generated CFG with statement
# ranges, the use list of one slot from `scan_slot_def_use` (sometimes with an extra or
# out-of-range entry), random `IR_FLAG_NOTHROW` flags, and a new value that is an SSA value, an
# argument, a literal or UNDEF_TOKEN. `code` is `ir.stmts.stmt`, as in construct_ssa!.
function gen_fixup(rng, id, io)
    blocks, index = gen_scfg(rng; n=rand(rng, 1:5))
    nst = nstmts_of(blocks)
    ns = rand(rng, 1:4)
    code = Any[]
    for _ in 1:nst
        st = gen_scan_stmt(rng, ns)
        if rand(rng) < 0.08
            st = Expr(:call, GlobalRef(Base, :f), Core.SlotNumber(rand(rng, 1:ns)),
                      Expr(:static_parameter, rand(rng, 1:2)))
        end
        push!(code, st)
    end
    slot = rand(rng, 1:ns)
    ci = copy(SCAN_CI)
    ci.slotflags = zeros(UInt8, ns)
    ci.slotnames = Symbol[Symbol(:s, i) for i in 1:ns]
    uses = try
        CC.scan_slot_def_use(0, ci, copy(code))[slot].uses
    catch
        Int[]
    end
    rand(rng) < 0.05 && push!(uses, rand(rng, 1:nst + 1))
    r = rand(rng)
    ssa = r < 0.35 ? Core.SSAValue(rand(rng, 1:9)) : r < 0.6 ? Core.Argument(2) :
          r < 0.75 ? 7 : CC.UNDEF_TOKEN
    nt = [rand(rng) < 0.3 for _ in 1:nst]
    sptypes = CC.VarState[CC.VarState(rand(rng) < 0.5 ? CC.Const(3) : Int, 0, false)]
    input = ("code" => ja([enc(st) for st in code]), "nt" => ja(string.(nt)), jscfg(blocks, index)...,
             "names" => ja([jstr(string(x)) for x in ci.slotnames]),
             "sp" => ja([t.typ isa CC.Const ? enc(CC.quoted(t.typ.val)) : "null" for t in sptypes]),
             "uses" => ja(uses), "slot" => slot, "ssa" => enc(ssa))
    exp = tryj() do
        stmts = CC.InstructionStream(nst)
        for i in 1:nst
            stmts.stmt[i] = code[i]; stmts.type[i] = Any
            stmts.flag[i] = nt[i] ? CC.IR_FLAG_NOTHROW : CC.IR_FLAG_NULL
        end
        ir = CC.IRCode(stmts, mkcfg(blocks, index), CC.DebugInfoStream(stmts.line), Any[], Expr[],
                       sptypes)
        CC.fixup_uses!(ir, ci, ir.stmts.stmt, uses, slot, ssa)
        encir(ir)
    end
    println(io, jo("id" => id, "s2s" => "\"fixup\"", input..., "exp" => exp))
end

## Synthesized IR for domsort_ssa! alone

# An IR in BB addressing over a generated CFG: each block ends in the terminator its successor
# list asks for (none for a plain fall through, sometimes `:leave`), fillers use earlier values
# (mostly from dominating blocks, sometimes from anywhere, which `renumber_ssa` rejects when the
# definition is in an unreachable block), phi nodes at block starts, and new nodes.
# Successors where most blocks fall through and many also jump, so that a fall-through
# successor is often not the next block in domtree order.
function gen_fall_succs(rng, n)
    succs = [Int[] for _ in 1:n]
    for i in 1:n
        i < n && rand(rng) < 0.75 && push!(succs[i], i + 1)
        rand(rng) < 0.4 && push!(succs[i], rand(rng, 1:n))
    end
    # Jumps to blocks that nothing else enters, which become domtree children that are not the
    # fall-through block.
    for i in 1:n-2
        if rand(rng) < 0.35
            j = rand(rng, i+2:n)
            foreach(k -> k != i && filter!(!=(j), succs[k]), 1:n)
            push!(succs[i], j)
        end
    end
    for i in 1:n
        unique!(succs[i])
        rand(rng) < 0.5 && reverse!(succs[i])
    end
    return succs, Int[]
end

function gen_dsort(rng, id, io, info)
    blocks, index = rand(rng) < 0.6 ? gen_scfg(rng; n=rand(rng, 3:16), succfn=gen_fall_succs) :
                                      gen_scfg(rng)
    n = length(blocks)
    cfg = mkcfg(blocks, index)
    dt = CC.construct_domtree(cfg.blocks)
    nst = nstmts_of(blocks)
    code = Vector{Any}(undef, nst)
    blk = [CC.block_for_inst(cfg, i) for i in 1:nst]
    function operand(i)
        b = blk[i]
        cands = [j for j in 1:nst if j != i && (j < i ? blk[j] == b : false) ||
                 (blk[j] != b && CC.dominates(dt, blk[j], b))]
        r = rand(rng)
        r < 0.04 && return Core.SSAValue(rand(rng, 1:nst + 2))
        (r < 0.75 && !isempty(cands)) && return Core.SSAValue(rand(rng, cands))
        return rand(rng) < 0.5 ? Core.Argument(1) : 1
    end
    for (b, (f, l, preds, succs)) in enumerate(blocks)
        for i in f:l-1
            if i == f && rand(rng) < 0.3
                vals = Vector{Any}(undef, length(preds))
                for k in 1:length(preds)
                    rand(rng) < 0.8 && (vals[k] = operand(i))
                end
                code[i] = Core.PhiNode(Int32.(preds), vals)
            else
                code[i] = Expr(:call, GlobalRef(Base, :f), operand(i))
            end
        end
        others = [t for t in succs if t != b + 1]
        code[l] = if isempty(succs)
            Core.ReturnNode(operand(l))
        elseif isempty(others)
            r = rand(rng)
            r < 0.15 ? Expr(:leave, Core.SSAValue(max(l - 1, 1))) :
            r < 0.25 ? Core.GotoNode(b + 1) : Expr(:call, GlobalRef(Base, :g), operand(l))
        elseif (b + 1) in succs
            rand(rng) < 0.25 ? Core.EnterNode(others[1]) : Core.GotoIfNot(operand(l), others[1])
        else
            Core.GotoNode(others[1])
        end
    end
    stmts = CC.InstructionStream(nst)
    for i in 1:nst
        stmts.stmt[i] = code[i]; stmts.type[i] = Any
    end
    ir = CC.IRCode(stmts, cfg, CC.DebugInfoStream(stmts.line), Any[], Expr[], CC.VarState[])
    nn = Tuple{Int,Bool,Any}[]
    for _ in 1:rand(rng, 0:4)
        nst == 0 && break
        pos = rand(rng, 1:nst)
        r = rand(rng)
        st = if r < 0.4
            preds = blocks[blk[pos]][3]
            vals = Vector{Any}(undef, length(preds))
            for k in 1:length(preds)
                rand(rng) < 0.8 && (vals[k] = operand(pos))
            end
            Core.PhiNode(Int32.(preds), vals)
        elseif r < 0.6
            Core.PiNode(operand(pos), Int)
        elseif r < 0.7
            Core.UpsilonNode(operand(pos))
        else
            Expr(:call, GlobalRef(Base, :h), operand(pos), Core.SSAValue(nst + rand(rng, 1:3)))
        end
        push!(nn, (pos, rand(rng) < 0.3, st))
        CC.insert_node!(ir, pos, CC.NewInstruction(st, Any, CC.NoCallInfo(), nothing, CC.IR_FLAG_NULL),
                        nn[end][2])
    end
    input = ("code" => ja([enc(s) for s in code]), "nt" => ja(fill("false", nst)), jscfg(blocks, index)...,
             "nn" => ja([ja([p, string(a), enc(st)]) for (p, a, st) in nn]))
    exp = tryj() do
        out = CC.domsort_ssa!(ir, dt)
        length(out.cfg.blocks) > n && bump!(info, "dsort_split")
        length(out.stmts) > nst && bump!(info, "dsort_goto")
        encir(out)
    end
    startswith(exp, "{\"err\"") && bump!(info, "dsort_error")
    println(io, jo("id" => id, "s2s" => "\"dsort\"", input..., "exp" => exp))
end

## Generated functions for the end-to-end case

module Gen
const SV = Base.ScopedValues.ScopedValue(0)
end

const VARS = (:x, :y, :z, :w)

mutable struct GenState
    rng::Xoshiro
    where_T::Bool
    labels::Vector{Symbol}
    toplace::Vector{Symbol}
    nstmts::Int
end

function gval(g::GenState, depth::Int=0)
    rng = g.rng
    r = rand(rng)
    depth > 2 && (r = r * 0.55)
    r < 0.28 && return rand(rng, VARS)
    r < 0.38 && return rand(rng, (:a, :b))
    r < 0.48 && return rand(rng, -1:3)
    r < 0.53 && return :nothing
    r < 0.56 && g.where_T && return :T
    r < 0.62 && return :(identity($(gval(g, depth + 1))))
    r < 0.70 && return :($(gval(g, depth + 1)) + 1)
    r < 0.75 && return :(@isdefined($(rand(rng, VARS))))
    r < 0.80 && return :($(gcond(g, depth + 1)) ? $(gval(g, depth + 1)) : $(gval(g, depth + 1)))
    r < 0.85 && return :(Base.inferencebarrier($(gval(g, depth + 1))))
    r < 0.90 && return :(rand(Bool) ? 1 : nothing)
    return :($(gval(g, depth + 1)) === nothing)
end

function gcond(g::GenState, depth::Int=0)
    rng = g.rng
    r = rand(rng)
    v = rand(rng, VARS)
    r < 0.15 && return :(a > 0)
    r < 0.25 && return :b
    r < 0.40 && return :($v isa Int)
    r < 0.50 && return :($v === nothing)
    r < 0.60 && return :(@isdefined($v))
    r < 0.66 && return true
    r < 0.72 && return false
    r < 0.86 && return :(rand(Bool))
    return :($(gval(g, depth + 1)) == 1)
end

function gblock(g::GenState, depth::Int, inloop::Bool, intry::Bool)
    n = depth > 2 ? rand(g.rng, 0:2) : rand(g.rng, 1:4)
    stmts = Any[gstmt(g, depth, inloop, intry) for _ in 1:n]
    # A label inside a nested block, so that a `@goto` can jump into the middle of a branch.
    if !intry && !isempty(g.toplace) && rand(g.rng) < 0.3
        insert!(stmts, rand(g.rng, 1:length(stmts) + 1), :(@label $(pop!(g.toplace))))
    end
    return Expr(:block, stmts...)
end

function gstmt(g::GenState, depth::Int, inloop::Bool, intry::Bool)
    rng = g.rng
    g.nstmts += 1
    r = rand(rng)
    if depth > 3 || g.nstmts > 40
        r = r * 0.3
    end
    v = rand(rng, VARS)
    r < 0.30 && return :($v = $(gval(g)))
    r < 0.40 && return Expr(:if, gcond(g), gblock(g, depth + 1, inloop, intry),
                            rand(rng) < 0.5 ? gblock(g, depth + 1, inloop, intry) : Expr(:block))
    r < 0.47 && return :(while $(gcond(g)); $(gblock(g, depth + 1, true, intry)); end)
    r < 0.51 && return :(for i in 1:a; $(gblock(g, depth + 1, true, intry)); end)
    r < 0.57 && return :(try; $(gblock(g, depth + 1, inloop, true)); catch; $(gblock(g, depth + 1, inloop, intry)); end)
    r < 0.60 && return :(try; $(gblock(g, depth + 1, inloop, true)); finally; $(gblock(g, depth + 1, inloop, intry)); end)
    r < 0.64 && return Expr(:block, :(local $v), :($v = $(gval(g))))
    r < 0.66 && return :(local $v)
    r < 0.69 && return :(return $(gval(g)))
    r < 0.71 && return :(error("e"))
    r < 0.74 && inloop && return rand(rng, Bool) ? :(break) : :(continue)
    r < 0.79 && !isempty(g.labels) && return rand(rng, Bool) ? :(@goto $(rand(rng, g.labels))) :
                                                 :($(gcond(g)) && @goto $(rand(rng, g.labels)))
    r < 0.80 && return :($(gcond(g)) && return $(gval(g)))
    r < 0.82 && return :($v === nothing && ($v = 0))
    r < 0.84 && return :(identity($(gval(g))))
    # A scoped `:enter`; when nothing in it can throw, `convert_to_ircode!` keeps the `EnterNode`
    # with catch destination 0.
    r < 0.855 && return :(Base.ScopedValues.@with(SV => 1, $(gblock(g, depth + 1, inloop, true))))
    r < 0.86 && return :($v = $(gval(g)); $v = $v + 1)
    return :($v = $(gval(g)))
end

const SIGS = Any[(Int, Bool), (Union{Int,Nothing}, Bool), (Any, Any), (Int, Int), (Bool, Bool)]

function gen_function(rng, name)
    g = GenState(rng, rand(rng) < 0.15, Symbol[], Symbol[], 0)
    if rand(rng) < 0.3
        g.labels = [Symbol(:L, i) for i in 1:rand(rng, 1:3)]
        g.toplace = copy(g.labels)
    end
    body = Any[gstmt(g, 0, false, false) for _ in 1:rand(rng, 1:6)]
    for (i, l) in enumerate(g.toplace)
        insert!(body, rand(rng, 1:length(body) + 1), :(@label $l))
    end
    if rand(rng) < 0.2
        pushfirst!(body, :(x::Int = a isa Int ? a : 0))   # a typed local
    end
    push!(body, :(return $(gval(g))))
    sig = g.where_T ? (Int, Bool) : rand(rng, SIGS)
    head = g.where_T ? :($name(a::T, b) where {T}) : :($name(a, b))
    return Expr(:function, head, Expr(:block, body...)), sig
end

mutable struct Info
    verify_fail::Int
    examples::Vector{String}
    skipped::Int
    feat::Dict{String,Int}
    smallest::String
end

# How often the `ssa` cases reach each shape (information on the input bias, from the expected
# result).
const FEATURES = ("phi" => "{\"phi\":", "phic" => "{\"phic\":", "upsilon" => "{\"ups",
                  "pi" => "{\"pi\":", "throw_undef_if_not" => "throw_undef_if_not",
                  "enter" => "{\"enter\":", "error" => "{\"err\":")

bump!(info, k) = (info.feat[k] = get(info.feat, k, 0) + 1)

function count_features!(info, exp)
    for (k, pat) in FEATURES
        occursin(pat, exp) && bump!(info, k)
    end
end

function ssa_case(rng, id, info)
    local name, ex, sig
    for attempt in 1:20
        name = Symbol(:f, id, :_, attempt)
        ex, sig = gen_function(rng, name)
        ok = try
            Core.eval(Gen, ex); true
        catch
            false
        end
        ok || continue
        f = invokelatest(getfield, Gen, name)
        mi = try
            Base.method_instance(f, sig)
        catch
            nothing
        end
        mi === nothing && continue
        interp = CC.NativeInterpreter()
        frame = try CC.typeinf_frame(interp, mi, false) catch; nothing end
        frame === nothing && continue
        opt = CC.OptimizationState(frame, interp)
        ci = opt.src
        ir = try CC.convert_to_ircode!(ci, opt) catch; nothing end
        ir === nothing && continue
        code = ir.stmts.stmt
        (length(ci.ssavaluetypes) == length(code) && length(ci.slotnames) == length(ci.slotflags) &&
         length(opt.slottypes) == length(ci.slotflags) && isempty(ir.new_nodes) &&
         isempty(ir.stmts.type)) || (info.skipped += 1; continue)
        𝕃ₒ = CC.optimizer_lattice(interp)
        nslots = length(ci.slotflags)
        bbs = map(opt.bb_states) do st
            st === nothing && return "null"
            ja([begin
                    vt = st.vartable[s]
                    np = try !CC.:⊑(𝕃ₒ, opt.slottypes[s], vt.typ) catch; false end
                    ja([string(vt.typ === Union{}), string(vt.undef), jstr(string(vt.typ)), string(np)])
                end for s in 1:nslots])
        end
        hi = CC.compute_trycatch(code)
        handlers = [begin
                        h = CC.gethandler(hi, pc)
                        h === nothing ? 0 : CC.get_enter_idx(h)
                    end for pc in 1:length(code)]
        sp = [begin
                  t = ir.sptypes[i].typ
                  t isa CC.Const ? enc(CC.quoted(t.val)) : "null"
              end for i in 1:length(ir.sptypes)]
        nt = [string(CC.has_flag(ir.stmts[i], CC.IR_FLAG_NOTHROW)) for i in 1:length(code)]
        input = ("code" => ja([enc(s) for s in code]), "nt" => ja(nt), "b" => encblocks(ir.cfg),
                 "idx" => ja(ir.cfg.index), "nargs" => Int(ci.nargs),
                 "names" => ja([jstr(string(s)) for s in ci.slotnames]), "bbs" => ja(bbs),
                 "h" => ja(handlers), "sp" => ja(sp))
        local out
        exp = tryj() do
            domtree = CC.construct_domtree(ir)
            defuse = CC.scan_slot_def_use(Int(ci.nargs), ci, ir.stmts.stmt)
            out = CC.construct_ssa!(ci, ir, opt, domtree, defuse, 𝕃ₒ)
            encir(out)
        end
        if @isdefined(out)
            length(out.cfg.blocks) > length(ir.cfg.blocks) && bump!(info, "domsort_split")
            length(out.stmts) > length(ir.stmts) && bump!(info, "domsort_goto")
            any(i -> i != 0 && out.cfg.blocks[i].preds != ir.cfg.blocks[i].preds,
                1:min(length(out.cfg.blocks), length(ir.cfg.blocks))) && bump!(info, "domsort_reorder")
            try
                CC.verify_ir(CC.compact!(CC.copy(out)), false)
            catch e
                e isa InterruptException && rethrow()
                info.verify_fail += 1
                if !occursin("@goto", string(ex))
                    bump!(info, "verify_fail_without_goto")
                    src = string(Base.remove_linenums!(ex))
                    if isempty(info.smallest) || length(src) < length(info.smallest)
                        info.smallest = "on $sig:\n" * src
                    end
                end
                length(info.examples) < 3 && push!(info.examples, "verify_ir after compact! fails on $sig for\n$(Base.remove_linenums!(ex))")
            end
        end
        count_features!(info, exp)
        startswith(exp, "{\"err\"") && !occursin("@goto", string(ex)) && bump!(info, "error_without_goto")
        if startswith(exp, "{\"err\"") && length(info.examples) < 6
            push!(info.examples, "construct_ssa! threw $exp on $sig for\n$(Base.remove_linenums!(ex))")
        end
        any(st -> st === nothing, opt.bb_states) && bump!(info, "unreachable_bb")
        isempty(ir.sptypes) || bump!(info, "sparams")
        return jo("id" => id, "s2s" => "\"ssa\"", input..., "exp" => exp)
    end
    return nothing
end

function gen_case(rng, id, io, info)
    r = rand(rng)
    if r < 0.40
        line = ssa_case(rng, id, info)
        if line !== nothing
            println(io, line); return "ssa"
        end
    end
    r = rand(rng)
    if r < 0.22
        gen_idf(rng, id, io); return "idf"
    elseif r < 0.40
        gen_live(rng, id, io); return "live"
    elseif r < 0.58
        gen_scan(rng, id, io); return "scan"
    elseif r < 0.76
        gen_dsort(rng, id, io, info); return "dsort"
    elseif r < 0.86
        gen_fixup(rng, id, io); return "fixup"
    elseif r < 0.94
        gen_redge(rng, id, io); return "redge"
    else
        gen_bfi(rng, id, io); return "bfi"
    end
end

function main(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    info = Info(0, String[], 0, Dict{String,Int}(), "")
    dir = mktempdir()
    casefile = joinpath(dir, "cases.jsonl")
    ops = Dict{Int,String}()
    open(casefile, "w") do io
        for id in 1:n
            ops[id] = gen_case(rng, id, io, info)
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
        println(rpad(op, 10), " agree=", st[1], " disagree=", st[2])
    end
    for line in first(bad, parse(Int, opts["show"]))
        println("DISAGREE ", first(line, 6000))
    end
    println("INFO verify_ir_after_compact_fail=$(info.verify_fail) skipped_inputs=$(info.skipped)")
    println("INFO features: ", join(("$k=$v" for (k, v) in sort(collect(info.feat))), " "))
    isempty(info.smallest) || println("INFO smallest verify_ir failure without @goto ", info.smallest)
    for e in info.examples
        println("INFO ", first(e, 3000))
    end
    println("SEED $seed CASES $n ANSWERED $seen")
    println("AGREE $agree/$seen")
    rm(dir; recursive=true)
    return isempty(bad) && seen == n ? 0 : 1
end

exit(main())
