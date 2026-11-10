# Differential test of the Lean model of Compiler/src/ssair/domtree.jl and the CFG edits of
# Compiler/src/ssair/ir.jl against the pinned Julia (f755f49a9e41380d7da126b3c1db9fe7f83dd027).
#
# Run from julia-base, after `lake build compilerdiff`:
#     $JULIA difftest/compiler/domtree.jl \
#         --cases 20000 --seed 1
#
# Generates CFGs biased toward the shapes that stress dominator code: lowered-code shapes
# (fall-through, `GotoIfNot`, `goto`, `return`, `:enter` with a catch block and its virtual
# predecessor 0), irreducible loops, self loops, hubs with many predecessors, unreachable
# cycles, back edges into the entry block, duplicate edges, and long chains with cross edges
# (more than 32 reachable blocks switches `SNCA!` to `snca_compress_worklist!`). Operations:
#
#   dom     construct_domtree; dominates, nearest_common_dominator, dominated, bb_unreachable
#   pdom    construct_postdomtree; postdominates, nearest_common_dominator
#   seq     construct_domtree, then cfg_insert_edge!/cfg_delete_edge! each followed by
#           domtree_insert_edge!/domtree_delete_edge! (edges into unreachable blocks, from
#           unreachable blocks, deleting the only edge into a block, DFS-tree edges, ...),
#           the full state after every step, then dominates/nearest_common_dominator
#   naive   naive_idoms, both directions
#   kill    kill_edge!(bbs, from, to, callback) with a recording callback
#   rename  construct_domtree, then rename_nodes! with a bijection from kept blocks onto 1:k,
#           or (30%) an injection into 1:n that leaves slots unwritten
#
# The full tree state (DFS numbering, SNCA state, idoms, nodes) is compared, except the slots
# Julia leaves undefined (see `enc_state` in common.jl). Errors are compared by exception type.
# Prints `AGREE k/n`, and as information only (not agreement with the model) how often SNCA
# disagrees with naive_idoms and a dynamic update with a rebuild from scratch.
#
# Runs (seed, cases, agreement):
#   2026-11-09, compilerdiff at the f755f49 model, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 20000 cases: AGREE 20000/20000 (dom 6028, pdom 4002, seq 4963, naive 1998,
#                        kill 1556, rename 1453); INFO snca_vs_naive=0 dynamic_vs_rebuild=2
#   seed 2, 20000 cases: AGREE 20000/20000 (dom 5949, pdom 3975, seq 4987, naive 2115,
#                        kill 1575, rename 1399); INFO snca_vs_naive=0 dynamic_vs_rebuild=2
#   seed 3, 20000 cases: AGREE 20000/20000 (dom 6049, pdom 4066, seq 4956, naive 1983,
#                        kill 1591, rename 1355); INFO snca_vs_naive=0 dynamic_vs_rebuild=0
#   2026-11-09, after modelling `DFSTree._worklist`, the return value of `resize!(::DFSTree)`
#   and the in-place `map!` of `rename_nodes!` on unwritten slots, with injective rename maps
#   added, pinned Julia 1.15.0-DEV.184 f755f49a9e:
#   seed 1, 20000 cases: AGREE 20000/20000 (dom 6107, pdom 3956, seq 4882, naive 2077,
#                        kill 1595, rename 1383); INFO snca_vs_naive=0 dynamic_vs_rebuild=0
#   seed 2, 20000 cases: AGREE 20000/20000 (dom 6021, pdom 4040, seq 4882, naive 2068,
#                        kill 1585, rename 1404); INFO snca_vs_naive=0 dynamic_vs_rebuild=3
#   seed 3, 20000 cases: AGREE 20000/20000 (dom 6128, pdom 4024, seq 4898, naive 1991,
#                        kill 1622, rename 1337); INFO snca_vs_naive=0 dynamic_vs_rebuild=4
#   The dynamic_vs_rebuild cases are all `domtree_delete_edge!` leaving an idom higher in
#   the tree than a rebuild gives (a lead for the property work, not a model mismatch).

include(joinpath(@__DIR__, "common.jl"))
using .CFGSer
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

## CFG generation. A CFG is a vector of successor lists; predecessors are derived the way
## `compute_basic_blocks` pushes them, with the virtual predecessor 0 on the entry block and on
## catch blocks.

function pick_n(rng)
    r = rand(rng)
    r < 0.02 && return 0
    r < 0.40 && return rand(rng, 1:6)
    r < 0.72 && return rand(rng, 7:14)
    r < 0.90 && return rand(rng, 15:32)
    return rand(rng, 33:72)
end

function lowered_cfg(rng, n)
    succs = [Int[] for _ in 1:n]
    catches = Int[]
    for i in 1:n
        r = rand(rng)
        nxt = i + 1 <= n ? [i + 1] : Int[]
        if i == n
            succs[i] = rand(rng) < 0.8 ? Int[] : [rand(rng, 1:n)]
        elseif r < 0.25
            succs[i] = nxt
        elseif r < 0.55
            t = rand(rng, 1:n)
            succs[i] = t == i + 1 ? nxt : [t; nxt]
        elseif r < 0.70
            succs[i] = [rand(rng, 1:n)]
        elseif r < 0.80
            succs[i] = Int[]
        elseif r < 0.92
            c = rand(rng) < 0.8 ? rand(rng, min(i + 1, n):n) : rand(rng, 1:n)
            succs[i] = [c; nxt]
            push!(catches, c)
        else
            succs[i] = nxt
        end
    end
    return succs, catches
end

function random_cfg(rng, n)
    succs = [Int[] for _ in 1:n]
    for i in 1:n
        k = rand(rng, (0, 1, 1, 2, 2, 2, 3, 4))
        for _ in 1:k
            push!(succs[i], rand(rng, 1:n))
        end
        rand(rng) < 0.9 && unique!(succs[i])
    end
    return succs, Int[]
end

function irreducible_cfg(rng, n)
    n < 4 && return random_cfg(rng, n)
    succs, catches = rand(rng, Bool) ? lowered_cfg(rng, n) : random_cfg(rng, n)
    a, b = rand(rng, 2:n), rand(rng, 2:n)
    while b == a
        b = rand(rng, 2:n)
    end
    h = rand(rng, 1:min(a, b) - 1)
    for (x, y) in ((h, a), (h, b), (a, b), (b, a))
        y in succs[x] || push!(succs[x], y)
    end
    return succs, catches
end

function hub_cfg(rng, n)
    n < 2 && return random_cfg(rng, n)
    succs, catches = lowered_cfg(rng, n)
    h = rand(rng, 1:n)
    for i in 1:n
        if i != h && rand(rng) < 0.7 && !(h in succs[i])
            push!(succs[i], h)
        end
    end
    return succs, catches
end

function unreachable_cycles_cfg(rng, n)
    n < 3 && return random_cfg(rng, n)
    m = rand(rng, 1:n - 1)
    succs = [Int[] for _ in 1:n]
    for i in 1:m
        for _ in 1:rand(rng, 0:2)
            push!(succs[i], rand(rng, 1:m))
        end
        i < m && rand(rng) < 0.6 && push!(succs[i], i + 1)
    end
    for i in m+1:n
        for _ in 1:rand(rng, 1:3)
            push!(succs[i], rand(rng) < 0.85 ? rand(rng, m+1:n) : rand(rng, 1:n))
        end
    end
    foreach(unique!, succs)
    return succs, Int[]
end

function chain_cfg(rng, n)
    succs = [i < n ? [i + 1] : Int[] for i in 1:n]
    for _ in 1:rand(rng, 0:2n)
        x, y = rand(rng, 1:n), rand(rng, 1:n)
        y in succs[x] || push!(succs[x], y)
    end
    for s in succs
        rand(rng) < 0.3 && shuffle!(rng, s)
    end
    return succs, Int[]
end

function selfloop_cfg(rng, n)
    succs, catches = rand(rng, Bool) ? lowered_cfg(rng, n) : random_cfg(rng, n)
    for i in 1:n
        rand(rng) < 0.3 && !(i in succs[i]) && push!(succs[i], i)
    end
    return succs, catches
end

function gen_succs(rng, n)
    n == 0 && return Vector{Int}[], Int[]
    r = rand(rng)
    r < 0.25 && return lowered_cfg(rng, n)
    r < 0.42 && return random_cfg(rng, n)
    r < 0.54 && return irreducible_cfg(rng, n)
    r < 0.64 && return hub_cfg(rng, n)
    r < 0.76 && return unreachable_cycles_cfg(rng, n)
    r < 0.90 && return chain_cfg(rng, n)
    return selfloop_cfg(rng, n)
end

function gen_cfg(rng; n=pick_n(rng))
    succs, catches = gen_succs(rng, n)
    if n > 0 && rand(rng) < 0.05
        # an occasional duplicate edge, as `:enter` whose catch block is the next block gives
        i = rand(rng, 1:n)
        isempty(succs[i]) || push!(succs[i], succs[i][1])
    end
    if rand(rng) < 0.03 && n >= 2
        # a block whose only predecessor is the virtual one (a catch block whose `:enter` is gone)
        c = rand(rng, 2:n)
        foreach(s -> filter!(!=(c), s), succs)
        push!(catches, c)
    end
    preds = [Int[] for _ in 1:n]
    n > 0 && rand(rng) < 0.9 && push!(preds[1], 0)
    for i in 1:n, s in succs[i]
        push!(preds[s], i)
    end
    for c in unique(catches)
        (isempty(preds[c]) || rand(rng) < 0.9) && push!(preds[c], 0)
    end
    for i in 1:n
        rand(rng) < 0.15 && shuffle!(rng, preds[i])
        rand(rng) < 0.10 && shuffle!(rng, succs[i])
    end
    return [(preds[i], succs[i]) for i in 1:n]
end

jblocks(b) = ja([ja([ja(p), ja(s)]) for (p, s) in b])
jpairs(ps) = ja([ja([a, b]) for (a, b) in ps])

function pick_pairs(rng, n; lo=1, extra=0)
    n == 0 && return Tuple{Int,Int}[]
    ps = n <= 8 ? [(a, b) for a in 1:n for b in 1:n] :
                  [(rand(rng, 1:n), rand(rng, 1:n)) for _ in 1:40]
    for _ in 1:extra
        push!(ps, (rand(rng, lo:n), rand(rng, lo:n)))
    end
    rand(rng) < 0.03 && push!(ps, (rand(rng, 1:n), n + 1))
    return ps
end

## Expected results from the pinned Compiler.

function query_fields(dt, q, nq, roots, isdom; withdd=isdom)
    dom = [tryj(() -> string(isdom ? CC.dominates(dt, a, b) : CC.postdominates(dt, a, b)))
           for (a, b) in q]
    nca = [tryj(() -> string(CC.nearest_common_dominator(dt, a, b))) for (a, b) in nq]
    out = Pair{String,String}["st" => enc_state(dt), "dom" => ja(dom), "nca" => ja(nca)]
    if withdd
        dd = map(roots) do r
            tryj() do
                it = CC.dominated(dt, r); res = Int[]
                y = CC.iterate(it)
                while y !== nothing
                    push!(res, y[1]); y = CC.iterate(it, y[2])
                end
                ja(res)
            end
        end
        unr = [tryj(() -> string(CC.bb_unreachable(dt, b))) for b in 1:length(dt.dfs_tree.to_pre)]
        push!(out, "dd" => ja(dd), "unr" => ja(unr))
    end
    return out
end

queries(dt, q, nq, roots, isdom) = jo(query_fields(dt, q, nq, roots, isdom)...)

mutable struct Info
    snca_vs_naive::Int
    dyn_vs_rebuild::Int
    examples::Vector{String}
end

function naive_check!(info, b, post)
    blocks = mkblocks(b)
    try
        dt = post ? CC.construct_postdomtree(blocks) : CC.construct_domtree(blocks)
        nv = CC.naive_idoms(blocks, post)
        if dt.idoms_bb != nv
            info.snca_vs_naive += 1
            length(info.examples) < 10 &&
                push!(info.examples, "snca/naive post=$post b=$(jblocks(b)) snca=$(dt.idoms_bb) naive=$nv")
        end
    catch
    end
end

function gen_dom(rng, id, io, info, op)
    b = gen_cfg(rng); n = length(b)
    q = pick_pairs(rng, n)
    nq = pick_pairs(rng, n; lo=0, extra=4)
    roots = n == 0 ? Int[] : n <= 8 ? collect(1:n) : rand(rng, 1:n, 5)
    isdom = op == "dom"
    exp = tryj(() -> queries(isdom ? CC.construct_domtree(mkblocks(b)) :
                                     CC.construct_postdomtree(mkblocks(b)), q, nq, roots, isdom))
    naive_check!(info, b, !isdom)
    println(io, jo("id" => id, "dt" => "\"$op\"", "b" => jblocks(b), "q" => jpairs(q),
                   "nq" => jpairs(nq), "roots" => ja(roots), "exp" => exp))
end

function gen_steps(rng, b, nsteps)
    n = length(b)
    succs = [copy(s) for (_, s) in b]
    preds = [copy(p) for (p, _) in b]
    steps = Tuple{String,Int,Int}[]
    for _ in 1:nsteps
        edges = [(f, t) for f in 1:n for t in succs[f]]
        r = rand(rng)
        if (r < 0.5 || isempty(edges)) && n > 0
            f, t = rand(rng, 1:n), rand(rng, 1:n)
            r2 = rand(rng)
            if r2 < 0.15
                t = 1                      # back edge into the entry block
            elseif r2 < 0.25
                t = f                      # self loop
            elseif r2 < 0.30 && !isempty(edges)
                f, t = rand(rng, edges)    # duplicate edge
            end
            push!(steps, ("ins", f, t)); push!(succs[f], t); push!(preds[t], f)
        elseif !isempty(edges)
            if rand(rng) < 0.03
                f, t = rand(rng, 1:n), rand(rng, 1:n)   # maybe not an edge: TypeError
            else
                single = [(f, t) for (f, t) in edges if count(!=(0), preds[t]) == 1]
                f, t = (!isempty(single) && rand(rng) < 0.3) ? rand(rng, single) : rand(rng, edges)
            end
            push!(steps, ("del", f, t))
            i = findfirst(==(f), preds[t]); i === nothing || deleteat!(preds[t], i)
            j = findfirst(==(t), succs[f]); j === nothing || deleteat!(succs[f], j)
        end
    end
    return steps
end

function gen_seq(rng, id, io, info)
    b = gen_cfg(rng)
    n = length(b)
    steps = gen_steps(rng, b, rand(rng, 1:10))
    q = pick_pairs(rng, n)
    nq = pick_pairs(rng, n; lo=0, extra=4)
    blocks = mkblocks(b)
    cfg = CC.CFG(blocks, Int[])
    states = String[]
    tail = Pair{String,String}[]
    try
        dt = CC.construct_domtree(blocks)
        push!(states, enc_state(dt))
        failed = false
        for (k, f, t) in steps
            try
                if k == "ins"
                    CC.cfg_insert_edge!(cfg, f, t); CC.domtree_insert_edge!(dt, blocks, f, t)
                else
                    CC.cfg_delete_edge!(cfg, f, t); CC.domtree_delete_edge!(dt, blocks, f, t)
                end
            catch e
                e isa InterruptException && rethrow()
                push!(states, errj(e)); failed = true; break
            end
            push!(states, enc_state(dt))
            rebuilt = try CC.construct_domtree(blocks).idoms_bb catch; nothing end
            if rebuilt !== nothing && rebuilt != dt.idoms_bb
                info.dyn_vs_rebuild += 1
                length(info.examples) < 10 && push!(info.examples,
                    "dynamic/rebuild b=$(jblocks(b)) steps=$steps at=$((k, f, t)) dyn=$(dt.idoms_bb) rebuilt=$rebuilt")
            end
        end
        failed || (tail = query_fields(dt, q, nq, Int[], true; withdd=false))
    catch e
        e isa InterruptException && rethrow()
        push!(states, errj(e))
    end
    exp = jo("states" => ja(states), tail...)
    println(io, jo("id" => id, "dt" => "\"seq\"", "b" => jblocks(b),
                   "steps" => ja([ja(["\"$k\"", f, t]) for (k, f, t) in steps]),
                   "q" => jpairs(q), "nq" => jpairs(nq), "exp" => exp))
end

function gen_naive(rng, id, io)
    b = gen_cfg(rng); post = rand(rng, Bool)
    exp = tryj(() -> ja(CC.naive_idoms(mkblocks(b), post)))
    println(io, jo("id" => id, "dt" => "\"naive\"", "b" => jblocks(b), "post" => string(post),
                   "exp" => exp))
end

function gen_kill(rng, id, io)
    b = gen_cfg(rng); n = length(b)
    edges = [(f, t) for f in 1:n for t in b[f][2]]
    f, t = (isempty(edges) || rand(rng) < 0.03) ? (rand(rng, 1:max(n, 1)), rand(rng, 1:max(n, 1))) :
                                                  rand(rng, edges)
    exp = tryj() do
        bbs = mkblocks(b)
        rec = Tuple{Int,Int}[]
        CC.kill_edge!(bbs, f, t, (a, c) -> push!(rec, (a, c)))
        jo("b" => enc_blocks(bbs), "cb" => jpairs(rec))
    end
    println(io, jo("id" => id, "dt" => "\"kill\"", "b" => jblocks(b), "f" => f, "t" => t,
                   "exp" => exp))
end

function gen_rename(rng, id, io)
    b = gen_cfg(rng); n = length(b)
    reach = try
        CC.construct_domtree(mkblocks(b)).dfs_tree.to_pre
    catch
        zeros(Int, n)
    end
    dropunreach = rand(rng) < 0.7
    keep = [i == 1 ? rand(rng) < 0.97 :
            (dropunreach && reach[i] == 0) ? false : rand(rng) < 0.8 for i in 1:n]
    kept = findall(keep)
    u = rand(rng)
    # Distinct targets with gaps (the last case) leave slots at most max_new_bb unwritten, where
    # Julia's shallow copy of `nodes` shows through.
    targets = u < 0.45 ? collect(1:length(kept)) : u < 0.7 ? shuffle(rng, collect(1:length(kept))) :
        shuffle(rng, collect(1:n))[1:length(kept)]
    r = fill(-1, n)
    for (k, i) in enumerate(kept)
        r[i] = targets[k]
    end
    if rand(rng) < 0.03 && n > 0
        r[rand(rng, 1:n)] = n + 1   # out of range: BoundsError
    end
    exp = tryj(() -> enc_state(CC.rename_nodes!(CC.construct_domtree(mkblocks(b)), r)))
    println(io, jo("id" => id, "dt" => "\"rename\"", "b" => jblocks(b), "r" => ja(r),
                   "exp" => exp))
end

function gen_case(rng, id, io, info)
    r = rand(rng)
    if r < 0.30
        gen_dom(rng, id, io, info, "dom"); return "dom"
    elseif r < 0.50
        gen_dom(rng, id, io, info, "pdom"); return "pdom"
    elseif r < 0.75
        gen_seq(rng, id, io, info); return "seq"
    elseif r < 0.85
        gen_naive(rng, id, io); return "naive"
    elseif r < 0.93
        gen_kill(rng, id, io); return "kill"
    else
        gen_rename(rng, id, io); return "rename"
    end
end

function main(args=ARGS)
    opts = parse_args(args)
    n = parse(Int, opts["cases"]); seed = parse(Int, opts["seed"])
    rng = Random.Xoshiro(seed)
    info = Info(0, 0, String[])
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
        println("DISAGREE ", first(line, 4000))
    end
    println("INFO snca_vs_naive=$(info.snca_vs_naive) dynamic_vs_rebuild=$(info.dyn_vs_rebuild)")
    for e in info.examples
        println("INFO ", first(e, 2000))
    end
    println("SEED $seed CASES $n ANSWERED $seen")
    println("AGREE $agree/$seen")
    rm(dir; recursive=true)
    return isempty(bad) && seen == n ? 0 : 1
end

exit(main())
