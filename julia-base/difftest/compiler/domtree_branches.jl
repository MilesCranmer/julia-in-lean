# Search on a Julia binary for the CFGs and counterexamples that the bounded domtree entries
# use (JuliaLean/Proofs/Compiler/src/ssair/domtree/). Run from julia-base:
#     $JULIA difftest/compiler/domtree_branches.jl
#
# 1. Random CFGs in the shapes compute_basic_blocks gives (return, goto, `GotoIfNot` and
#    `:enter` as `[dest, next]`, fall-through; catch blocks get the virtual predecessor 0), with
#    up to four random edge deletions each. For every deletion it checks the strengthened
#    `deleteSoundOK` of domtree/Checks.lean (children, levels, exact bb_unreachable, every
#    reachable block's idom a strict dominator, no false dominance), counts trees that differ
#    from a rebuild, and compares on_semidominator_path with its docstring (domtree.jl:550-553)
#    by definition.
# 2. Small CFGs that reach the update branch of snca_compress! and its recursion (the push branch
#    of snca_compress_worklist!), found with a copy of SNCA!'s semidominator loop that counts
#    them. The 24 compression CFGs of branchCFGs in domtree/Checks.lean came from an earlier
#    run of this search; the last part prints, for each of them, the counts it reaches.
#
# Runs:
#   2026-11-09, pinned 1.15.0-DEV.184 f755f49a9e: see the summary lines printed at the end,
#   recorded in the notes of compiler-domtree-delete-sound-small and
#   compiler-domtree-on-semi-path-miss.
const CC = Base.Compiler
using Random

function mk(succs, zp=[1])
    n = length(succs)
    preds = [Int[] for _ in 1:n]
    for j in 1:n, s in succs[j]; push!(preds[s], j); end
    [CC.BasicBlock(CC.StmtRange(i, i), [(i in zp ? [0] : Int[]); preds[i]], copy(succs[i])) for i in 1:n]
end
function reach(bbs, avoid)
    avoid == 1 && return Set{Int}()
    seen = Set([1]); st = [1]
    while !isempty(st)
        x = pop!(st)
        for y in bbs[x].succs
            (y == avoid || y in seen) && continue
            push!(seen, y); push!(st, y)
        end
    end
    seen
end
# by definition: x == s, or pre(x) > pre(y) and s reaches x through nodes of pre > pre(y)
function on_sdom_path_def(bbs, D, s_pre, x, y)
    s = D.from_pre[s_pre]; py = D.to_pre[y]
    x == s && return true
    D.to_pre[x] > py || return false
    seen = Set([s]); st = [s]
    while !isempty(st)
        u = pop!(st)
        for v in bbs[u].succs
            (v in seen || D.to_pre[v] <= py) && continue
            v == x && return true
            push!(seen, v); push!(st, v)
        end
    end
    false
end
function randcfg(rng, n)
    succs = Vector{Int}[]; zp = [1]
    for i in 1:n
        k = rand(rng, 1:6)
        if k == 1
            push!(succs, Int[])
        elseif k == 2
            push!(succs, [rand(rng, 1:n)])
        elseif k <= 4
            d = rand(rng, 1:n)
            push!(succs, i == n ? [d] : d == i + 1 ? [d] : [d, i + 1])
        elseif k == 5
            push!(succs, i == n ? Int[] : [i + 1])
        else
            c = rand(rng, 1:n)
            if i == n || c == i + 1 || c == 1
                push!(succs, i == n ? Int[] : [i + 1])
            else
                push!(succs, [c, i + 1]); push!(zp, c)
            end
        end
    end
    succs, unique(zp)
end

function search_deletes(seed, iters)
    rng = MersenneTwister(seed)
    c = Dict{String,Int}()
    bump(k) = (c[k] = get(c, k, 0) + 1)
    smallest = typemax(Int)
    for _ in 1:iters
        n = rand(rng, 2:20)
        succs, zp = randcfg(rng, n)
        bbs = mk(succs, zp)
        cfg = CC.CFG(bbs, Int[])
        dt = CC.construct_domtree(bbs)
        for _ in 1:4
            edges = [(f, t) for f in 1:n for t in bbs[f].succs]
            isempty(edges) && break
            (f, t) = rand(rng, edges)
            D = dt.dfs_tree
            if !CC.bb_unreachable(dt, f) && t != 1 && !CC.is_parent(D, f, t)
                bump("semipath-checks")
                a = CC.on_semidominator_path(dt, f, t)
                b = on_sdom_path_def(bbs, D, dt.snca_state[D.to_pre[t]].semi, f, t)
                a && !b && bump("semipath-true-off-path(info)")
                !a && b && bump("semipath-miss")
            end
            old = [copy(bb.succs) for bb in bbs]
            CC.cfg_delete_edge!(cfg, f, t)
            CC.domtree_delete_edge!(dt, bbs, f, t)
            bump("deletes")
            r = reach(bbs, -1)
            av = Dict(x => reach(bbs, x) for x in 1:n)
            dom(x, y) = (y in r) && (x == y || !(y in av[x]))
            ok = length(dt.idoms_bb) == n && length(dt.nodes) == n &&
                all(d -> dt.nodes[d].children == [x for x in 1:n if dt.idoms_bb[x] == d], 1:n) &&
                all(x -> dt.nodes[x].level == (dt.idoms_bb[x] == 0 ? 1 : dt.nodes[dt.idoms_bb[x]].level + 1), 1:n) &&
                all(x -> CC.bb_unreachable(dt, x) == (x != 1 && !(x in r)), 1:n) &&
                all(x -> x == 1 || !(x in r) || (dt.idoms_bb[x] != 0 && dt.idoms_bb[x] != x && dom(dt.idoms_bb[x], x)), 1:n) &&
                all(((x, y),) -> !CC.dominates(dt, x, y) || x == y || dom(x, y), Iterators.product(1:n, 1:n))
            ok || (bump("delete-sound-fail"); println("delete-sound-fail: ", old, " zp=", zp, " del ", (f, t)))
            if CC.construct_domtree(bbs).idoms_bb != dt.idoms_bb
                bump("stale(info)")
                if n < smallest
                    smallest = n
                    println("stale: n=$n succs=", old, " zp=", zp, " del ", (f, t))
                end
            end
        end
    end
    c
end

function branches(bbs, post)
    D = CC.DFS(bbs, post)
    n = length(D)
    st = [(typemax(Int), w) for w in 1:n]   # (semi, label)
    anc = copy(D.to_parent_pre)
    update = 0; recursion = 0
    function comp!(v, ll, depth)
        u = anc[v]
        if u >= ll
            depth >= 1 && (recursion += 1)
            comp!(u, ll, depth + 1)
            if st[u][2] < st[v][2]; st[v] = (st[v][1], st[u][2]); end
            anc[v] = anc[u]
            update += 1
        end
    end
    for w in reverse(post ? (1:n) : (2:n))
        s = anc[w]; ll = w + 1
        for v in (post ? bbs[D.from_pre[w]].succs : bbs[D.from_pre[w]].preds)
            v == 0 && continue
            vp = D.to_pre[v]; vp == 0 && continue
            vp >= ll && comp!(vp, ll, 0)
            s = min(s, st[vp][2])
        end
        st[w] = (s, s)
    end
    update, recursion
end
function search_branches(seed, iters)
    rng = MersenneTwister(seed)
    found = Dict{Tuple{Bool,Symbol}, Vector{Vector{Vector{Int}}}}()
    for _ in 1:iters
        succs, zp = randcfg(rng, rand(rng, 4:6))
        zp == [1] || continue
        bbs = mk(succs)
        for post in (false, true)
            u, r = branches(bbs, post)
            for (key, k) in ((:update, u), (:recursion, r))
                k > 0 || continue
                v = get!(found, (post, key), Vector{Vector{Int}}[])
                length(v) < 12 && !(succs in v) && push!(v, succs)
            end
        end
    end
    found
end

println("Julia ", VERSION, " ", Base.GIT_VERSION_INFO.commit[1:10])
for seed in (7, 8)
    println("seed $seed deletes: ", search_deletes(seed, 60000))
end
for (k, v) in sort(collect(search_branches(11, 200000)))
    println(k, " => ", length(v))
    for s in v; println("   ", s); end
end

branch24 = [[[2], [3], [4], [5], [2], Int[]], [[2], [5, 3], [4], [5], [2], Int[]],
          [[3, 2], Int[], [1, 4], [5], [2, 6], Int[]], [[5, 2], [1], [1, 4], [2], [3], Int[]],
          [[2], [4, 3], [1, 4], [5], [2, 6], Int[]], [[4, 2], [6, 3], [4], [6, 5], [2, 6], Int[]],
          [[2], [3], [4], [2], Int[]], [[3, 2], [3], [4], [2], Int[]], [[2], [3], [2, 4], [2], Int[]],
          [[5, 2], [4], [2], [3, 5], Int[]], [[2], [1, 3], [5, 4], [2, 5], Int[]],
          [[4], [3], [1, 4], [4, 5], [3], Int[]],
          [[2], [3], [4], [1, 5], Int[]], [[5, 2], [3], [4], [1], Int[]], [[4, 2], [3], [4], [1, 5], Int[]],
          [[2], [3], [4], Int[], [1, 6], Int[]], [[2], [4, 3], [2], [6], [3, 6], Int[]],
          [[3, 2], [6, 3], [3, 4], [4, 5], [1, 6], Int[]],
          [[2], [3], [1, 4], Int[]], [[4], [4, 3], [1], Int[]], [[2], [4, 3], [1], Int[], Int[]],
          [[3], [1, 3], Int[], [2, 5], Int[]], [[5, 2], [3], [6, 4], Int[], [6], Int[]],
          [Int[], Int[], [6, 4], [5], Int[], Int[]]]
for (i, s) in enumerate(branch24)
    println("branchCFGs[$i] forward (update, recursion) = ", branches(mk(s), false),
            ", post-dominance = ", branches(mk(s), true))
end
