# Smoke test of the bounded domtree statements (JuliaLean/Proofs/Compiler/src/ssair/domtree/)
# on a Julia binary, over the same CFG family as `smallCFGs` in domtree/Checks.lean, with the
# same checks written against Julia's functions. Run from julia-base:
#     $JULIA difftest/compiler/domtree_smoke.jl
#
# Runs:
#   2026-11-09, pinned 1.15.0-DEV.184 f755f49a9e: family 564 CFGs; failures Dict{String, Int64}()
#   2026-11-09, nightly 1.15.0-DEV.304 290d5bb5f5: family 564 CFGs; failures Dict{String, Int64}()
#   2026-11-09, with lower3, branchCFGs and the strengthened delete checks:
#     pinned 1.15.0-DEV.184 f755f49a9e: family 639 CFGs; failures Dict("delete-rebuild(info)" => 1)
#     nightly 1.15.0-DEV.304 290d5bb5f5: family 639 CFGs; failures Dict("delete-rebuild(info)" => 1)
# "delete-rebuild(info)" (dynamic deletion equal to a rebuild) is information only; the
# 9-block CFG at the end of the family is its counterexample (compiler-domtree-delete-stale-idom).
# "ncd-0-unreachable(info)" checks nearest_common_dominator with the virtual exit 0 and
# unreachable blocks against what NCDSpec gives (0, or the block itself when a == b).
const CC = Base.Compiler
subsets(xs) = isempty(xs) ? [Int[]] : (r = subsets(xs[2:end]); vcat(r, [[xs[1]; s] for s in r]))
perms(xs) = isempty(xs) ? [Int[]] : [[p[1:i]; xs[1]; p[i+1:end]] for p in perms(xs[2:end]) for i in 0:length(p)]
choices(n; ordered) = ordered ? vcat(perms.(subsets(collect(1:n)))...) : subsets(collect(1:n))
function cfgs(n; ordered)
    ch = choices(n; ordered)
    out = Vector{Vector{Int}}[Vector{Int}[]]
    for _ in 1:n
        out = [[c; [s]] for c in out for s in ch]
    end
    out
end
function mk(succs, zp)
    n = length(succs)
    preds = [Int[] for _ in 1:n]
    for j in 1:n, s in succs[j]; push!(preds[s], j); end
    [CC.BasicBlock(CC.StmtRange(i, i), [(i in zp ? [0] : Int[]); preds[i]], copy(succs[i])) for i in 1:n]
end
family = Tuple{Vector{Vector{Int}},Vector{Int}}[]
for s in cfgs(1; ordered=true); push!(family, (s, [1])); end
for s in cfgs(2; ordered=true); push!(family, (s, [1])); push!(family, (s, [1, 2])); end
for s in cfgs(3; ordered=false); push!(family, (s, [1])); end
# lower3: block 1 `[3, 2]`, blocks 2 and 3 any successor list compute_basic_blocks gives
lowerchoices(n, i) = vcat([Int[]], [[d] for d in 1:n], i < n ? [[d, i + 1] for d in 1:n if d != i + 1] : Vector{Int}[])
for b2 in lowerchoices(3, 2), b3 in lowerchoices(3, 3)
    push!(family, ([[3, 2], b2, b3], [1])); push!(family, ([[3, 2], b2, b3], [1, 3]))
end
# branchCFGs (domtree/Checks.lean)
for s in [[[2], [3], [4], [5], [2], Int[]], [[2], [5, 3], [4], [5], [2], Int[]],
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
          [Int[], Int[], [6, 4], [5], Int[], Int[]],
          [[2], [3], [4], [5], [6], [7], Int[]], [[2, 3], [4], [4], [5, 6], [7], [7], Int[]]]
    push!(family, (s, [1]))
end
push!(family, ([[2], [5, 3], [5, 4], [7, 5], [9, 6], [7], [5, 8], [8, 9], [6]], [1, 9, 5]))

# Dominance by definition: b is reachable from the root, and not reachable when a is removed.
function reachset(bbs, post, avoid)
    n = length(bbs)
    root = post ? 0 : 1
    root == avoid && return Set{Int}()
    seen = Set([root]); st = [root]
    edges(x) = post ? (x == 0 ? [b for b in 1:n if isempty(bbs[b].succs)] : filter(!=(0), bbs[x].preds)) : bbs[x].succs
    while !isempty(st)
        x = pop!(st)
        for y in edges(x)
            (y == avoid || y in seen) && continue
            push!(seen, y); push!(st, y)
        end
    end
    seen
end
function domrel(bbs, post)
    n = length(bbs); r0 = reachset(bbs, post, -1)
    cands = post ? (0:n) : (1:n)
    av = Dict(a => reachset(bbs, post, a) for a in cands)
    dom(a, b) = (b in r0) && (a == b || !(b in get(av, a, r0)))
    dom, r0, cands
end
function idom_ok(bbs, post, b, d)
    dom, r0, cands = domrel(bbs, post)
    ((!post && b == 1) || !(b in r0)) && return d == 0
    d != b && d in cands && dom(d, b) && all(c -> c == b || !dom(c, b) || dom(c, d), cands)
end
function tree_ok(bbs, post, dt)
    n = length(bbs); dom, r0, cands = domrel(bbs, post)
    length(dt.idoms_bb) == n || return false
    all(b -> idom_ok(bbs, post, b, dt.idoms_bb[b]), 1:n) || return false
    all(d -> dt.nodes[d].children == [b for b in 1:n if dt.idoms_bb[b] == d], 1:n) || return false
    all(b -> dt.nodes[b].level == (dt.idoms_bb[b] == 0 ? 1 : dt.nodes[dt.idoms_bb[b]].level + 1), 1:n) || return false
    f = post ? CC.postdominates : CC.dominates
    all(((a, b),) -> f(dt, a, b) == (a == b || dom(a, b)), Iterators.product(1:n, 1:n)) || return false
    for a in 1:n, b in 1:n
        (a in r0 && b in r0) || continue
        d = CC.nearest_common_dominator(dt, a, b)
        (dom(d, a) && dom(d, b) && all(c -> !(dom(c, a) && dom(c, b)) || dom(c, d), cands)) || return false
    end
    # the virtual exit and unreachable blocks (information for NCDSpec, which covers them in general)
    for a in 0:n, b in 0:n
        d = CC.nearest_common_dominator(dt, a, b)
        want = (a == 0 || b == 0) ? 0 : (a in r0 && b in r0) ? d : a == b ? a : 0
        d == want || (counts["ncd-0-unreachable(info)"] = get(counts, "ncd-0-unreachable(info)", 0) + 1)
    end
    if !post
        all(b -> CC.bb_unreachable(dt, b) == (b != 1 && !(b in r0)), 1:n) || return false
        dominated_list(r) = (xs = Int[]; for x in CC.dominated(dt, r); push!(xs, x); end; sort!(xs))
        all(r -> dominated_list(r) == [b for b in 1:n if b == r || dom(r, b)], 1:n) || return false
    end
    true
end
counts = Dict{String,Int}()
bad(k) = (counts[k] = get(counts, k, 0) + 1)
for (s, zp) in family
    n = length(s)
    tree_ok(mk(s, zp), false, CC.construct_domtree(mk(s, zp))) || bad("dom")
    tree_ok(mk(s, zp), true, CC.construct_postdomtree(mk(s, zp))) || bad("pdom")
    for f in 1:n, t in 1:n
        b = mk(s, zp); t in b[f].succs && continue
        dt = CC.construct_domtree(b)
        CC.cfg_insert_edge!(CC.CFG(b, Int[]), f, t)
        CC.domtree_insert_edge!(dt, b, f, t)
        tree_ok(b, false, dt) || bad("insert")
    end
    for f in 1:n, t in s[f]
        b = mk(s, zp); dt = CC.construct_domtree(b)
        CC.cfg_delete_edge!(CC.CFG(b, Int[]), f, t)
        CC.domtree_delete_edge!(dt, b, f, t)
        dom, r0, _ = domrel(b, false)
        all(x -> CC.bb_unreachable(dt, x) == (x != 1 && !(x in r0)), 1:n) || bad("delete-reach")
        (length(dt.idoms_bb) == n && length(dt.nodes) == n) || bad("delete-size")
        all(d -> dt.nodes[d].children == [x for x in 1:n if dt.idoms_bb[x] == d], 1:n) || bad("delete-children")
        all(x -> dt.nodes[x].level == (dt.idoms_bb[x] == 0 ? 1 : dt.nodes[dt.idoms_bb[x]].level + 1), 1:n) || bad("delete-levels")
        all(x -> x == 1 || !(x in r0) || (dt.idoms_bb[x] != 0 && dt.idoms_bb[x] != x && dom(dt.idoms_bb[x], x)), 1:n) || bad("delete-idom-strict-dominator")
        all(((x, y),) -> !CC.dominates(dt, x, y) || x == y || dom(x, y), Iterators.product(1:n, 1:n)) || bad("delete-sound")
        dt.idoms_bb == CC.construct_domtree(b).idoms_bb || bad("delete-rebuild(info)")
    end
    b = mk(s, zp)
    for post in (false, true)
        if !post && any(x -> x != 1 && !isempty(b[x].preds) && all(==(0), b[x].preds), 1:n)
            try; CC.naive_idoms(b, post); bad("naive-no-throw"); catch e; e isa TypeError || bad("naive-other-error"); end
            continue
        end
        ids = CC.naive_idoms(b, post)
        all(x -> idom_ok(b, post, x, ids[x]), 1:n) || bad("naive")
    end
    # rename_nodes!: drop the unreachable blocks, number the rest in order
    dt = CC.construct_domtree(b)
    _, r0, _ = domrel(b, false)
    r = Int[]; k = 0
    for x in 1:n; if x == 1 || x in r0; k += 1; push!(r, k); else push!(r, -1); end; end
    nb = CC.BasicBlock[]
    for x in 1:n
        r[x] == -1 && continue
        push!(nb, CC.BasicBlock(CC.StmtRange(x, x), [p == 0 ? 0 : r[p] for p in b[x].preds if p == 0 || r[p] != -1], [r[y] for y in b[x].succs]))
    end
    d1 = CC.rename_nodes!(dt, r); d2 = CC.construct_domtree(nb)
    (d1.idoms_bb == d2.idoms_bb && d1.dfs_tree.to_pre == d2.dfs_tree.to_pre && [x.level for x in d1.nodes] == [x.level for x in d2.nodes] &&
     [x.children for x in d1.nodes] == [x.children for x in d2.nodes]) || bad("rename")
    # kill_edge!
    for f in 1:n, t in s[f]
        b = mk(s, zp); before = sort([(x, y) for x in 1:n for y in b[x].succs])
        rec = Tuple{Int,Int}[]
        CC.kill_edge!(b, f, t, (x, y) -> push!(rec, (x, y)))
        after = [(x, y) for x in 1:n for y in b[x].succs]
        ok = last(rec) == (f, t) && sort([after; rec]) == before &&
             all(((x, y),) -> count(==(y), b[x].succs) == count(==(x), b[y].preds), Iterators.product(1:n, 1:n)) &&
             all(((x, y),) -> !isempty(b[y].preds) || isempty(b[y].succs), rec) &&
             all(((x, y),) -> (x, y) == (f, t) || isempty(b[x].preds), rec)
        ok || bad("kill")
    end
end
println("Julia ", VERSION, " ", Base.GIT_VERSION_INFO.commit[1:10], ": family ", length(family), " CFGs; failures ", counts)
