import JuliaLean.Compiler.src.ssair.ir

/-!
Source-mirrored model of `Compiler/src/ssair/domtree.jl` at
f755f49a9e41380d7da126b3c1db9fe7f83dd027: the DFS numbering, Semi-NCA (`SNCA!`), the
dominator and post-dominator trees, the dynamic edge insertion and deletion updates (DSNCA),
`rename_nodes!`, `dominates`, `postdominates`, `dominated`, `nearest_common_dominator` and the
reference `naive_idoms`.

Modelling choices (see also `JuliaLean/Compiler/src/ssair/ir.lean`):

* `GenericDomTree{IsPostDom}` is one structure with an `isPostDom` field.
* `DomTreeCache` holds scratch buffers that every use resets (`copy!` into `ancestors` and
  `idoms_pre`, `empty!` of `worklist`), so no value flows through it between calls. Its
  constructor is modelled (`DomTreeCache.new`), but the functions that take a `cache` keyword
  use fresh values where Julia reuses the buffers. `DFSTree._worklist` is modelled: `DFS!` uses
  it as its stack, and it is empty again when `DFS!` returns.
* Slots Julia leaves undefined (grown by `resize!` or made by `Vector(undef, n)`) are 0. The only
  such slots that survive a call are `to_post` of blocks with `to_pre == 0` and, for the
  post-dominator tree, the last slot of `from_post` (it gets `post_num - 1` slots, one more
  than the reached real blocks, because the virtual exit takes a postorder number but has no
  slot). The difftest masks exactly these.
* `DomTreeNode.children` vectors are values. Julia's `rename_nodes!(::DomTree, ...)` copies
  `nodes` shallowly, so when `rename_bb` leaves a slot at most `max_new_bb` unwritten, that
  slot keeps its old children vector, which the slot it was renamed to also holds. The `map!`
  then renames the vector in both places; the model mirrors that effect within the call (an
  unwritten slot of a kept block gets the renamed children). What a value model cannot show is
  that the two slots still share one vector afterwards, so a later `compute_domtree_nodes!`
  that empties one empties both. The difftest uses maps that are bijections from the kept
  blocks onto `1:k`, where nothing is left unwritten.
-/

namespace JuliaLean.Compiler.ssair

/-- `typemax(Int)`. -/
def typemaxInt : Int := 9223372036854775807

/-- A `to_visit` entry of `DFS!`: `(current_node_bb, parent_pre, pushed_children)`. -/
abbrev Frame := Int × Int × Bool

/-- `struct DFSTree`.

Julia source: Compiler/src/ssair/domtree.jl:74-87 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct DFSTree
    # These map between BB number and pre- or postorder numbers
    to_pre::Vector{PreNumber}
    from_pre::Vector{BBNumber}
    to_post::Vector{PostNumber}
    from_post::Vector{BBNumber}

    # Records parent relationships in the DFS tree
    # (preorder number -> preorder number)
    # Storing it this way saves a few lookups in the snca_compress! algorithm
    to_parent_pre::Vector{PreNumber}

    _worklist::Vector{Tuple{BBNumber, PreNumber, Bool}}
end
```
-/
structure DFSTree where
  toPre : Array Int
  fromPre : Array Int
  toPost : Array Int
  fromPost : Array Int
  toParentPre : Array Int
  worklist : Array Frame
  deriving Repr, BEq, Inhabited

/-- `DFSTree(n_blocks)`

Julia source: Compiler/src/ssair/domtree.jl:89-96 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function DFSTree(n_blocks::Int)
    return DFSTree(zeros(PreNumber, n_blocks),
                   Vector{BBNumber}(undef, n_blocks),
                   zeros(PostNumber, n_blocks),
                   Vector{BBNumber}(undef, n_blocks),
                   zeros(PreNumber, n_blocks),
                   Vector{Tuple{BBNumber, PreNumber, Bool}}())
end
```
-/
def DFSTree.new (n : Nat) : DFSTree :=
  { toPre := .replicate n 0, fromPre := .replicate n 0, toPost := .replicate n 0,
    fromPost := .replicate n 0, toParentPre := .replicate n 0, worklist := #[] }

/-- `copy(D::DFSTree)`: the positional constructor applied to a copy of each field, in the
order of the Julia call. Vectors are values, so `copy(v)` is `v`.

Julia source: Compiler/src/ssair/domtree.jl:98-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(D::DFSTree) = DFSTree(copy(D.to_pre),
                           copy(D.from_pre),
                           copy(D.to_post),
                           copy(D.from_post),
                           copy(D.to_parent_pre),
                           copy(D._worklist))
```
-/
def DFSTree.copy (D : DFSTree) : DFSTree :=
  DFSTree.mk D.toPre D.fromPre D.toPost D.fromPost D.toParentPre D.worklist

/-- `copy!(dst::DFSTree, src::DFSTree)`: `copy!` of each of the five vectors, which resizes
`dst`'s vectors to `src`'s; `dst._worklist` is kept.

Julia source: Compiler/src/ssair/domtree.jl:105-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy!(dst::DFSTree, src::DFSTree)
    copy!(dst.to_pre, src.to_pre)
    copy!(dst.from_pre, src.from_pre)
    copy!(dst.to_post, src.to_post)
    copy!(dst.from_post, src.from_post)
    copy!(dst.to_parent_pre, src.to_parent_pre)
    return dst
end
```
-/
def DFSTree.copyInto (dst src : DFSTree) : DFSTree :=
  let dst := { dst with toPre := src.toPre }
  let dst := { dst with fromPre := src.fromPre }
  let dst := { dst with toPost := src.toPost }
  let dst := { dst with fromPost := src.fromPost }
  { dst with toParentPre := src.toParentPre }

/-- `resize!(D::DFSTree, n)`

Julia source: Compiler/src/ssair/domtree.jl:113-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function resize!(D::DFSTree, n::Integer)
    resize!(D.to_pre, n)
    resize!(D.from_pre, n)
    resize!(D.to_post, n)
    resize!(D.from_post, n)
    resize!(D.to_parent_pre, n)
end
```
Returns the updated tree and the method's own return value, which is that of its last call:
the resized `D.to_parent_pre` vector itself. -/
def DFSTree.resize (D : DFSTree) (n : Nat) : DFSTree × Array Int :=
  let D := { D with toPre := ssair.resize D.toPre n 0 }
  let D := { D with fromPre := ssair.resize D.fromPre n 0 }
  let D := { D with toPost := ssair.resize D.toPost n 0 }
  let D := { D with fromPost := ssair.resize D.fromPost n 0 }
  let D := { D with toParentPre := ssair.resize D.toParentPre n 0 }
  (D, D.toParentPre)

/-- `length(D::DFSTree) = length(D.from_pre)` (Compiler/src/ssair/domtree.jl:121). -/
def DFSTree.length (D : DFSTree) : Nat := D.fromPre.size

/-- The `edges` of `DFS!` (Compiler/src/ssair/domtree.jl:169-174): for the virtual exit `-1`
of the post-dominator tree, the blocks without successors in order; otherwise `preds` or
`succs` of `blocks[current_node_bb]`. -/
def dfsEdges (blocks : Blocks) (isPost : Bool) (bb : Int) : JM (Array Int) :=
  if isPost && bb == -1 then
    pure (((Array.range blocks.size).filter fun (i : Nat) =>
      match blocks[i]? with
      | some b => b.succs.isEmpty
      | none => false).map fun (i : Nat) => (i : Int) + 1)
  else do
    let b ← aget blocks bb
    pure (if isPost then b.preds else b.succs)

/-- The `for succ_bb in edges` loop of `DFS!` (Compiler/src/ssair/domtree.jl:177-185). -/
def dfsPushChildren (isPost : Bool) (preNum : Int) : Array Frame → List Int → JM (Array Frame)
  | stk, [] => pure stk
  | stk, s :: rest =>
    if s == 0 then
      if isPost then dfsPushChildren isPost preNum stk rest
      else throw "julia:AssertionError"
    else dfsPushChildren isPost preNum (stk.push (s, preNum, false)) rest

/-- The `while !isempty(to_visit)` loop of `DFS!` (Compiler/src/ssair/domtree.jl:136-189).
Returns the tree, the final `pre_num` and `post_num`, and the stack `to_visit` (empty). -/
def dfsLoop (blocks : Blocks) (isPost : Bool) :
    Nat → DFSTree → Array Frame → Int → Int → JM (DFSTree × Int × Int × Array Frame)
  | 0, _, _, _, _ => outOfBudget
  | fuel + 1, D, stk, preNum, postNum =>
    match stk.back? with
    | none => pure (D, preNum, postNum, stk)
    | some (cur, parentPre, pushed) =>
      if pushed then do
        let D ← if cur != -1 then do
            let toPost ← aset D.toPost cur postNum
            let fromPost ← aset D.fromPost postNum cur
            pure { D with toPost, fromPost }
          else pure D
        dfsLoop blocks isPost fuel D stk.pop preNum (postNum + 1)
      else do
        let visited ← if cur != -1 then (fun p => p != 0) <$> aget D.toPre cur else pure false
        if visited then dfsLoop blocks isPost fuel D stk.pop preNum postNum
        else do
          let D ← if cur != -1 then do
              let toPre ← aset D.toPre cur preNum
              let fromPre ← aset D.fromPre preNum cur
              let toParentPre ← aset D.toParentPre preNum parentPre
              pure { D with toPre, fromPre, toParentPre }
            else pure D
          let stk := stk.set! (stk.size - 1) (cur, parentPre, true)
          let edges ← dfsEdges blocks isPost cur
          let stk ← dfsPushChildren isPost preNum stk edges.toList
          dfsLoop blocks isPost fuel D stk (preNum + 1) postNum

/-- Enough fuel for `dfsLoop`: every entry is pushed by one edge (or is the start or a virtual
exit edge) and is looked at at most twice. -/
def dfsFuel (blocks : Blocks) : Nat := 2 * (edgeCount blocks + blocks.size + 2) + 1

/-- `DFS!(D, blocks, is_post_dominator)`

Julia source: Compiler/src/ssair/domtree.jl:123-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function DFS!(D::DFSTree, blocks::Vector{BasicBlock}, is_post_dominator::Bool)
    resize!(D, length(blocks))
    fill!(D.to_pre, 0)
    to_visit = D._worklist # always starts empty
    if is_post_dominator
        # TODO: We're using -1 as the virtual exit node here. Would it make
        #       sense to actually have a real BB for the exit always?
        push!(to_visit, (-1, 0, false))
    else
        push!(to_visit, (1, 0, false))
    end
    pre_num = is_post_dominator ? 0 : 1
    post_num = 1
    while !isempty(to_visit)
        # Because we want the postorder number as well as the preorder number,
        # we don't pop the current node from the stack until we're moving up
        # the tree
        (current_node_bb, parent_pre, pushed_children) = to_visit[end]

        if pushed_children
            # Going up the DFS tree, so all we need to do is record the
            # postorder number, then move on
            if current_node_bb != -1
                D.to_post[current_node_bb] = post_num
                D.from_post[post_num] = current_node_bb
            end
            post_num += 1
            pop!(to_visit)

        elseif current_node_bb != -1 && D.to_pre[current_node_bb] != 0
            # Node has already been visited, move on
            pop!(to_visit)
            continue
        else
            # Going down the DFS tree

            # Record preorder number
            if current_node_bb != -1
                D.to_pre[current_node_bb] = pre_num
                D.from_pre[pre_num] = current_node_bb
                D.to_parent_pre[pre_num] = parent_pre
            end

            # Record that children (will) have been pushed
            to_visit[end] = (current_node_bb, parent_pre, true)

            if is_post_dominator && current_node_bb == -1
                edges = Int[bb for bb in 1:length(blocks) if isempty(blocks[bb].succs)]
            else
                edges = is_post_dominator ? blocks[current_node_bb].preds :
                                            blocks[current_node_bb].succs
            end

            # Push children to the stack
            for succ_bb in edges
                if succ_bb == 0
                    # Edge 0 indicates an error entry, but shouldn't affect
                    # the post-dominator tree.
                    @assert is_post_dominator
                    continue
                end
                push!(to_visit, (succ_bb, pre_num, false))
            end

            pre_num += 1
        end
    end

    # If all blocks are reachable, this is a no-op, otherwise, we shrink these
    # arrays.
    resize!(D.from_pre, pre_num - 1)
    resize!(D.from_post, post_num - 1) # should be same size as pre_num - 1
    resize!(D.to_parent_pre, pre_num - 1)

    return D
end
```
-/
def DFS! (D : DFSTree) (blocks : Blocks) (isPost : Bool) : JM DFSTree := do
  let D := (D.resize blocks.size).1
  let D := { D with toPre := Array.replicate D.toPre.size 0 }
  let stk : Array Frame := D.worklist.push (if isPost then -1 else 1, 0, false)
  let preNum : Int := if isPost then 0 else 1
  let (D, preNum, postNum, stk) ← dfsLoop blocks isPost (dfsFuel blocks) D stk preNum 1
  pure { D with
    worklist := stk
    fromPre := ssair.resize D.fromPre (preNum - 1).toNat 0
    fromPost := ssair.resize D.fromPost (postNum - 1).toNat 0
    toParentPre := ssair.resize D.toParentPre (preNum - 1).toNat 0 }

/-- `DFS(blocks, is_post_dominator=false) = DFS!(DFSTree(0), blocks, is_post_dominator)`
(Compiler/src/ssair/domtree.jl:200). -/
def DFS (blocks : Blocks) (isPost : Bool := false) : JM DFSTree :=
  DFS! (DFSTree.new 0) blocks isPost

/-- `struct SNCAData` (Compiler/src/ssair/domtree.jl:207-210). -/
structure SNCAData where
  semi : Int
  label : Int
  deriving Repr, BEq, Inhabited

/-- `struct DomTreeNode` (Compiler/src/ssair/domtree.jl:213-218). -/
structure DomTreeNode where
  level : Int
  children : Array Int
  deriving Repr, BEq, Inhabited

/-- `DomTreeNode() = DomTreeNode(1, Vector{BBNumber}())` (Compiler/src/ssair/domtree.jl:220). -/
def DomTreeNode.new : DomTreeNode := ⟨1, #[]⟩

/-- `struct GenericDomTree{IsPostDom}` (Compiler/src/ssair/domtree.jl:223-235), with the type
parameter as the field `isPostDom`. -/
structure GenericDomTree where
  isPostDom : Bool
  dfsTree : DFSTree
  sncaState : Array SNCAData
  idomsBB : Array Int
  nodes : Array DomTreeNode
  deriving Repr, BEq, Inhabited

/-- `DomTree()` / `PostDomTree()`

Julia source: Compiler/src/ssair/domtree.jl:237-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (T::Type{<:GenericDomTree})()
    return T(DFSTree(0), SNCAData[], BBNumber[], DomTreeNode[])
end
```
-/
def GenericDomTree.new (isPostDom : Bool) : GenericDomTree :=
  ⟨isPostDom, DFSTree.new 0, #[], #[], #[]⟩

/-- `struct DomTreeCache` (Compiler/src/ssair/domtree.jl:252-256): scratch buffers. -/
structure DomTreeCache where
  ancestors : Array Int
  idomsPre : Array Int
  worklist : Array (Int × Int)
  deriving Repr, BEq, Inhabited

/-- `DomTreeCache()`

Julia source: Compiler/src/ssair/domtree.jl:257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
DomTreeCache() = DomTreeCache(PreNumber[], PreNumber[], Tuple{Int, Int}[])
```
-/
def DomTreeCache.new : DomTreeCache := ⟨#[], #[], #[]⟩

/-- `dom_edges` (Compiler/src/ssair/domtree.jl:331-334): `blocks[idx].preds` for a `DomTree`,
`blocks[idx].succs` for a `PostDomTree`. -/
def domEdges (isPost : Bool) (blocks : Blocks) (idx : Int) : JM (Array Int) := do
  let b ← aget blocks idx
  pure (if isPost then b.succs else b.preds)

/-- `snca_compress!(state, ancestors, v, last_linked)`

Julia source: Compiler/src/ssair/domtree.jl:450-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function snca_compress!(state::Vector{SNCAData}, ancestors::Vector{PreNumber},
                        v::PreNumber, last_linked::PreNumber)
    u = ancestors[v]
    @assert u < v
    if u >= last_linked
        snca_compress!(state, ancestors, u, last_linked)
        if state[u].label < state[v].label
            state[v] = SNCAData(state[v].semi, state[u].label)
        end
        ancestors[v] = ancestors[u]
    end
    nothing
end
```
The recursion is on `u < v`, so fuel `v` is enough. -/
def sncaCompress : Nat → Array SNCAData → Array Int → Int → Int →
    JM (Array SNCAData × Array Int)
  | 0, _, _, _, _ => outOfBudget
  | fuel + 1, state, ancestors, v, lastLinked => do
    let u ← aget ancestors v
    unless u < v do throw "julia:AssertionError"
    if u >= lastLinked then
      let (state, ancestors) ← sncaCompress fuel state ancestors u lastLinked
      let su ← aget state u
      let sv ← aget state v
      let state ← if su.label < sv.label then aset state v ⟨sv.semi, su.label⟩ else pure state
      let ancestors ← aset ancestors v (← aget ancestors u)
      pure (state, ancestors)
    else pure (state, ancestors)

/-- The `while !isempty(worklist)` loop of `snca_compress_worklist!`
(Compiler/src/ssair/domtree.jl:473-486). -/
def sncaCompressWorklistLoop : Nat → Array SNCAData → Array Int → Int → Array (Int × Int) →
    JM (Array SNCAData × Array Int)
  | 0, _, _, _, _ => outOfBudget
  | fuel + 1, state, ancestors, lastLinked, wl =>
    match wl.back? with
    | none => pure (state, ancestors)
    | some (u, v) =>
      if u >= lastLinked then do
        let au ← aget ancestors u
        if au >= lastLinked then
          sncaCompressWorklistLoop fuel state ancestors lastLinked (wl.push (au, u))
        else
          let su ← aget state u
          let sv ← aget state v
          let state ← if su.label < sv.label then aset state v ⟨sv.semi, su.label⟩
            else pure state
          let ancestors ← aset ancestors v (← aget ancestors u)
          sncaCompressWorklistLoop fuel state ancestors lastLinked wl.pop
      else sncaCompressWorklistLoop fuel state ancestors lastLinked wl.pop

/-- `snca_compress_worklist!(state, ancestors, v, last_linked, worklist)`

Julia source: Compiler/src/ssair/domtree.jl:464-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function snca_compress_worklist!(
        state::Vector{SNCAData}, ancestors::Vector{PreNumber},
        v::PreNumber, last_linked::PreNumber,
        worklist::Vector{Tuple{PreNumber, PreNumber}})
    # TODO: There is a smarter way to do this
    u = ancestors[v]
    @assert u < v
    empty!(worklist)
    push!(worklist, (u, v))
    while !isempty(worklist)
        u, v = last(worklist)
        if u >= last_linked
            if ancestors[u] >= last_linked
                push!(worklist, (ancestors[u], u))
                continue
            end
            if state[u].label < state[v].label
                state[v] = SNCAData(state[v].semi, state[u].label)
            end
            ancestors[v] = ancestors[u]
        end
        pop!(worklist)
    end
end
```
-/
def sncaCompressWorklist (fuel : Nat) (state : Array SNCAData) (ancestors : Array Int)
    (v lastLinked : Int) : JM (Array SNCAData × Array Int) := do
  let u ← aget ancestors v
  unless u < v do throw "julia:AssertionError"
  sncaCompressWorklistLoop fuel state ancestors lastLinked #[(u, v)]

/-- The `for v ∈ dom_edges(...)` loop of `SNCA!` (Compiler/src/ssair/domtree.jl:386-415).
`small` is `length(ancestors) <= 32`. Returns the state, the ancestors and `semi_w`. -/
def sncaEdgeLoop (fuel : Nat) (D : DFSTree) (small : Bool) (lastLinked : Int) :
    List Int → Array SNCAData → Array Int → Int → JM (Array SNCAData × Array Int × Int)
  | [], state, ancestors, semiW => pure (state, ancestors, semiW)
  | v :: rest, state, ancestors, semiW =>
    if v == 0 then sncaEdgeLoop fuel D small lastLinked rest state ancestors semiW
    else do
      let vPre ← aget D.toPre v
      if vPre == 0 then sncaEdgeLoop fuel D small lastLinked rest state ancestors semiW
      else
        let (state, ancestors) ← if vPre >= lastLinked then
            (if small then sncaCompress fuel state ancestors vPre lastLinked
             else sncaCompressWorklist fuel state ancestors vPre lastLinked)
          else pure (state, ancestors)
        let semiW := min semiW (← aget state vPre).label
        sncaEdgeLoop fuel D small lastLinked rest state ancestors semiW

/-- The `for w::PreNumber in reverse(relevant_blocks)` loop of `SNCA!`
(Compiler/src/ssair/domtree.jl:383-417). -/
def sncaSemiLoop (fuel : Nat) (blocks : Blocks) (isPost : Bool) (D : DFSTree) (small : Bool) :
    List Int → Array SNCAData → Array Int → JM (Array SNCAData × Array Int)
  | [], state, ancestors => pure (state, ancestors)
  | w :: rest, state, ancestors => do
    let semiW ← aget ancestors w
    let edges ← domEdges isPost blocks (← aget D.fromPre w)
    let (state, ancestors, semiW) ←
      sncaEdgeLoop fuel D small (w + 1) edges.toList state ancestors semiW
    let state ← aset state w ⟨semiW, semiW⟩
    sncaSemiLoop fuel blocks isPost D small rest state ancestors

/-- The `while idom > vsemi` loop of `SNCA!` (Compiler/src/ssair/domtree.jl:427-429). -/
def idomWalk : Nat → Array Int → Int → Int → JM Int
  | 0, _, _, _ => outOfBudget
  | fuel + 1, idoms, idom, vsemi =>
    if idom > vsemi then do idomWalk fuel idoms (← aget idoms idom) vsemi else pure idom

/-- The immediate-dominator loop of `SNCA!` (Compiler/src/ssair/domtree.jl:424-431). -/
def idomLoop (fuel : Nat) (state : Array SNCAData) : List Int → Array Int → JM (Array Int)
  | [], idoms => pure idoms
  | v :: rest, idoms => do
    let idom ← aget idoms v
    let vsemi := (← aget state v).semi
    let idom ← idomWalk fuel idoms idom vsemi
    idomLoop fuel state rest (← aset idoms v idom)

/-- The loop expressing idoms in BB indexing (Compiler/src/ssair/domtree.jl:435-442). -/
def idomsBBLoop (isPost : Bool) (D : DFSTree) (idomsPre : Array Int) :
    List Int → Array Int → JM (Array Int)
  | [], out => pure out
  | i :: rest, out => do
    let skip ← if !isPost && i == 1 then pure true else (fun p => p == 0) <$> aget D.toPre i
    let v ← if skip then pure 0 else do
      let ip ← aget idomsPre (← aget D.toPre i)
      if ip == 0 then pure 0 else aget D.fromPre ip
    idomsBBLoop isPost D idomsPre rest (← aset out i v)

/-- `SNCA!(domtree, blocks, max_pre, cache)`

Julia source: Compiler/src/ssair/domtree.jl:342-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function SNCA!(domtree::GenericDomTree{IsPostDom}, blocks::Vector{BasicBlock}, max_pre::PreNumber, cache::DomTreeCache) where {IsPostDom}
    D = domtree.dfs_tree
    state = domtree.snca_state
    # There may be more blocks than are reachable in the DFS / dominator tree
    n_blocks = length(blocks)
    n_nodes = length(D)

    # `label` is initialized to the identity mapping (though the paper doesn't
    # make that clear). [...]
    resize!(state, n_nodes)
    for w in 1:max_pre
        # Only reset semidominators for nodes we want to recompute
        state[w] = SNCAData(typemax(PreNumber), w)
    end

    # If we are only recomputing some of the semidominators, the remaining
    # labels should be reset, [...]
    for w in max_pre+1:n_nodes
        semi = state[w].semi
        state[w] = SNCAData(semi, semi)
    end

    # Calculate semidominators, but only for blocks with preorder number up to
    # max_pre
    ancestors = cache.ancestors
    copy!(ancestors, D.to_parent_pre)
    relevant_blocks = IsPostDom ? (1:max_pre) : (2:max_pre)
    for w::PreNumber in reverse(relevant_blocks)
        semi_w = ancestors[w]
        last_linked = PreNumber(w + 1)
        for v ∈ dom_edges(domtree, blocks, D.from_pre[w])
            # For the purpose of the domtree, ignore virtual predecessors into
            # catch blocks.
            v == 0 && continue

            v_pre = D.to_pre[v]

            # Ignore unreachable predecessors
            v_pre == 0 && continue

            # N.B.: [...]
            if v_pre >= last_linked
                # `v` has already been processed, so perform path compression

                # For performance, if the number of ancestors is small avoid
                # the extra allocation of the worklist.
                if length(ancestors) <= 32
                    snca_compress!(state, ancestors, v_pre, last_linked)
                else
                    snca_compress_worklist!(state, ancestors, v_pre, last_linked,
                                            cache.worklist)
                end
            end

            # The (preorder number of the) semidominator of a block is the
            # minimum over the labels of its predecessors
            semi_w = min(semi_w, state[v_pre].label)
        end
        state[w] = SNCAData(semi_w, semi_w)
    end

    # Compute immediate dominators, [...]
    idoms_pre = cache.idoms_pre
    copy!(idoms_pre, D.to_parent_pre)
    for v in (IsPostDom ? (1:n_nodes) : (2:n_nodes))
        idom = idoms_pre[v]
        vsemi = state[v].semi
        while idom > vsemi
            idom = idoms_pre[idom]
        end
        idoms_pre[v] = idom
    end

    # Express idoms in BB indexing
    resize!(domtree.idoms_bb, n_blocks)
    for i::BBNumber in 1:n_blocks
        if (!IsPostDom && i == 1) || D.to_pre[i] == 0
            domtree.idoms_bb[i] = 0
        else
            ip = idoms_pre[D.to_pre[i]]
            domtree.idoms_bb[i] = ip == 0 ? 0 : D.from_pre[ip]
        end
    end
end
```
(Long comments elided with `[...]`.) -/
def SNCA! (domtree : GenericDomTree) (blocks : Blocks) (maxPre : Int) : JM GenericDomTree := do
  let D := domtree.dfsTree
  let isPost := domtree.isPostDom
  let nBlocks := blocks.size
  let nNodes := D.length
  let fuel := 4 * (nNodes + 2)
  let state := ssair.resize domtree.sncaState nNodes ⟨0, 0⟩
  let state ← (irange 1 maxPre).foldlM (fun st w => aset st w ⟨typemaxInt, w⟩) state
  let state ← (irange (maxPre + 1) nNodes).foldlM
    (fun st w => do let semi := (← aget st w).semi; aset st w ⟨semi, semi⟩) state
  let ancestors := D.toParentPre
  let relevant := if isPost then irange 1 maxPre else irange 2 maxPre
  let small := ancestors.size ≤ 32
  let (state, _) ← sncaSemiLoop fuel blocks isPost D small relevant.reverse state ancestors
  let idomsPre ← idomLoop fuel state (if isPost then irange 1 nNodes else irange 2 nNodes)
    D.toParentPre
  let idomsBB ← idomsBBLoop isPost D idomsPre (irange 1 nBlocks)
    (ssair.resize domtree.idomsBB nBlocks 0)
  pure { domtree with sncaState := state, idomsBB }

/-- The loop of `update_level!` (Compiler/src/ssair/domtree.jl:322-328). -/
def updateLevelLoop : Nat → Array DomTreeNode → Array (Int × Int) → JM (Array DomTreeNode)
  | 0, _, _ => outOfBudget
  | fuel + 1, nodes, wl =>
    match wl.back? with
    | none => pure nodes
    | some (node, level) => do
      let wl := wl.pop
      let n ← aget nodes node
      let nodes ← aset nodes node ⟨level, n.children⟩
      let wl := n.children.foldl (fun wl child => wl.push (child, level + 1)) wl
      updateLevelLoop fuel nodes wl

/-- `update_level!(nodes, node, level, worklist)`

Julia source: Compiler/src/ssair/domtree.jl:318-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function update_level!(nodes::Vector{DomTreeNode}, node::BBNumber, level::Int,
                       worklist::Vector{Tuple{BBNumber, Int}})
    empty!(worklist)
    push!(worklist, (node, level))
    while !isempty(worklist)
        (node, level) = pop!(worklist)
        nodes[node] = DomTreeNode(level, nodes[node].children)
        foreach(nodes[node].children) do child
            push!(worklist, (child, level+1))
        end
    end
end
```
On a forest each node is popped once; the fuel allows that. -/
def updateLevel! (nodes : Array DomTreeNode) (node level : Int) : JM (Array DomTreeNode) :=
  updateLevelLoop (2 * (nodes.size + 2)) nodes #[(node, level)]

/-- `compute_domtree_nodes!(domtree; cache)`

Julia source: Compiler/src/ssair/domtree.jl:283-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compute_domtree_nodes!(domtree::GenericDomTree{IsPostDom};
                                cache::DomTreeCache=DomTreeCache()) where {IsPostDom}
    # Compute children. Reuse any existing `children` vectors (e.g. when
    # recomputing the domtree during a dynamic update) to avoid reallocating
    # them, and reset the levels to the default of 1.
    nodes = domtree.nodes
    new_len = length(domtree.idoms_bb)
    old_len = length(nodes)
    for i in 1:min(old_len, new_len)
        children = nodes[i].children
        empty!(children)
        nodes[i] = DomTreeNode(1, children)
    end
    resize!(nodes, new_len)
    for i in (old_len+1):new_len
        nodes[i] = DomTreeNode()
    end
    for (idx, idom) in Iterators.enumerate(domtree.idoms_bb)
        ((!IsPostDom && idx == 1) || idom == 0) && continue
        push!(nodes[idom].children, idx)
    end
    # n.b. now issorted(domtree.nodes[*].children) since idx is sorted above
    # Recursively set level
    worklist = cache.worklist
    if IsPostDom
        for (node, idom) in enumerate(domtree.idoms_bb)
            idom == 0 || continue
            update_level!(domtree.nodes, node, 1, worklist)
        end
    else
        update_level!(domtree.nodes, 1, 1, worklist)
    end
    return domtree.nodes
end
```
-/
def computeDomtreeNodes! (domtree : GenericDomTree) : JM GenericDomTree := do
  let isPost := domtree.isPostDom
  let newLen := domtree.idomsBB.size
  let oldLen := domtree.nodes.size
  let nodes ← (irange 1 (min oldLen newLen)).foldlM
    (fun nodes i => do aset nodes i ⟨1, #[]⟩) domtree.nodes
  let nodes := ssair.resize nodes newLen DomTreeNode.new
  let nodes ← (irange (oldLen + 1) newLen).foldlM
    (fun nodes i => aset nodes i DomTreeNode.new) nodes
  let nodes ← (irange 1 newLen).foldlM (fun nodes idx => do
    let idom ← aget domtree.idomsBB idx
    if (!isPost && idx == 1) || idom == 0 then pure nodes
    else do
      let n ← aget nodes idom
      aset nodes idom { n with children := n.children.push idx }) nodes
  let nodes ← if isPost then
      (irange 1 newLen).foldlM (fun nodes node => do
        let idom ← aget domtree.idomsBB node
        if idom == 0 then updateLevel! nodes node 1 else pure nodes) nodes
    else updateLevel! nodes 1 1
  pure { domtree with nodes }

/-- `update_domtree!(blocks, domtree, recompute_dfs, max_pre; cache)`

Julia source: Compiler/src/ssair/domtree.jl:267-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function update_domtree!(blocks::Vector{BasicBlock}, domtree::GenericDomTree{IsPostDom},
                         recompute_dfs::Bool, max_pre::PreNumber;
                         cache::DomTreeCache=DomTreeCache()) where {IsPostDom}
    if recompute_dfs
        DFS!(domtree.dfs_tree, blocks, IsPostDom)
    end

    if max_pre == 0
        max_pre = length(domtree.dfs_tree)
    end

    SNCA!(domtree, blocks, max_pre, cache)
    compute_domtree_nodes!(domtree; cache)
    return domtree
end
```
-/
def updateDomtree! (blocks : Blocks) (domtree : GenericDomTree) (recomputeDfs : Bool)
    (maxPre : Int) : JM GenericDomTree := do
  let domtree ← if recomputeDfs then do
      pure { domtree with dfsTree := ← DFS! domtree.dfsTree blocks domtree.isPostDom }
    else pure domtree
  let maxPre : Int := if maxPre == 0 then domtree.dfsTree.length else maxPre
  let domtree ← SNCA! domtree blocks maxPre
  computeDomtreeNodes! domtree

/-- `construct_domtree(blocks)` (Compiler/src/ssair/domtree.jl:259-261):
`update_domtree!(blocks, DomTree(), true, 0; cache)`. -/
def constructDomtree (blocks : Blocks) : JM GenericDomTree :=
  updateDomtree! blocks (GenericDomTree.new false) true 0

/-- `construct_postdomtree(blocks)` (Compiler/src/ssair/domtree.jl:263-265):
`update_domtree!(blocks, PostDomTree(), true, 0; cache)`. -/
def constructPostdomtree (blocks : Blocks) : JM GenericDomTree :=
  updateDomtree! blocks (GenericDomTree.new true) true 0

/-- `bb_unreachable(domtree::DomTree, bb)`

Julia source: Compiler/src/ssair/domtree.jl:670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bb_unreachable(domtree::DomTree, bb::BBNumber) = bb != 1 && domtree.dfs_tree.to_pre[bb] == 0
```
-/
def bbUnreachable (domtree : GenericDomTree) (bb : Int) : JM Bool :=
  if bb != 1 then (fun p => p == 0) <$> aget domtree.dfsTree.toPre bb else pure false

/-- `is_parent(dfs_tree, x, y)`

Julia source: Compiler/src/ssair/domtree.jl:544-548 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_parent(dfs_tree::DFSTree, x::BBNumber, y::BBNumber)
    x_pre = dfs_tree.to_pre[x]
    y_pre = dfs_tree.to_pre[y]
    return x_pre == dfs_tree.to_parent_pre[y_pre]
end
```
-/
def isParent (D : DFSTree) (x y : Int) : JM Bool := do
  let xPre ← aget D.toPre x
  let yPre ← aget D.toPre y
  return xPre == (← aget D.toParentPre yPre)

/-- The loop of `on_semidominator_path` (Compiler/src/ssair/domtree.jl:566-571). -/
def semiPathLoop (state : Array SNCAData) (semiY : Int) : Nat → Int → JM Bool
  | 0, _ => outOfBudget
  | fuel + 1, cur =>
    if cur >= semiY then
      if semiY == cur then pure true
      else do semiPathLoop state semiY fuel (← aget state cur).semi
    else pure false

/-- `on_semidominator_path(domtree, x, y)`

Julia source: Compiler/src/ssair/domtree.jl:550-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
Check if x is on some semidominator path from the semidominator of y to y,
assuming there is an edge from x to y.
"""
function on_semidominator_path(domtree::DomTree, x::BBNumber, y::BBNumber)
    x_pre = domtree.dfs_tree.to_pre[x]
    y_pre = domtree.dfs_tree.to_pre[y]

    semi_y = domtree.snca_state[y_pre].semi
    current_block = x_pre

    # Follow the semidominators of `x` up the DFS tree to see if we ever reach
    # the semidominator of `y`. If so, `x` is on a semidominator path between
    # `y` and its semidominator. We can stop if the preorder number of the
    # semidominators becomes less than that of the semidominator of `y`,
    # because it can only decrease further.
    while current_block >= semi_y
        if semi_y == current_block
            return true
        end
        current_block = domtree.snca_state[current_block].semi
    end
    return false
end
```
-/
def onSemidominatorPath (domtree : GenericDomTree) (x y : Int) : JM Bool := do
  let xPre ← aget domtree.dfsTree.toPre x
  let yPre ← aget domtree.dfsTree.toPre y
  let semiY := (← aget domtree.sncaState yPre).semi
  semiPathLoop domtree.sncaState semiY (domtree.sncaState.size + 2) xPre

/-- `domtree_insert_edge!(domtree, blocks, from, to; cache)`

Julia source: Compiler/src/ssair/domtree.jl:489-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"Given updated blocks, update the given dominator tree with an inserted edge."
function domtree_insert_edge!(domtree::DomTree, blocks::Vector{BasicBlock},
                              from::BBNumber, to::BBNumber; cache::DomTreeCache=DomTreeCache())
    # `from` is unreachable, so `from` and `to` aren't in domtree
    if bb_unreachable(domtree, from)
        return domtree
    end

    # Implements Section 3.1 of [GI16]
    dt        = domtree.dfs_tree
    from_pre  = dt.to_pre[from]
    to_pre    = dt.to_pre[to]
    from_post = dt.to_post[from]
    to_post   = dt.to_post[to]
    if to_pre == 0 || (from_pre < to_pre && from_post < to_post)
        # The DFS tree is invalidated by the edge insertion, so run from
        # scratch
        update_domtree!(blocks, domtree, true, 0; cache)
    else
        # DFS tree is still valid, so update only affected nodes
        update_domtree!(blocks, domtree, false, to_pre; cache)
    end

    return domtree
end
```
-/
def domtreeInsertEdge! (domtree : GenericDomTree) (blocks : Blocks) (frm to : Int) :
    JM GenericDomTree := do
  if ← bbUnreachable domtree frm then return domtree
  let dt := domtree.dfsTree
  let fromPre ← aget dt.toPre frm
  let toPre ← aget dt.toPre to
  let fromPost ← aget dt.toPost frm
  let toPost ← aget dt.toPost to
  if toPre == 0 || (fromPre < toPre && fromPost < toPost) then
    updateDomtree! blocks domtree true 0
  else
    updateDomtree! blocks domtree false toPre

/-- `domtree_delete_edge!(domtree, blocks, from, to; cache)`

Julia source: Compiler/src/ssair/domtree.jl:515-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"Given updated blocks, update the given dominator tree with a deleted edge."
function domtree_delete_edge!(domtree::DomTree, blocks::Vector{BasicBlock},
                              from::BBNumber, to::BBNumber; cache::DomTreeCache=DomTreeCache())
    # `from` is unreachable, so `from` and `to` aren't in domtree
    if bb_unreachable(domtree, from)
        return domtree
    end

    # Implements Section 3.1 of [GI16]
    if is_parent(domtree.dfs_tree, from, to)
        # The `from` block is the parent of the `to` block in the DFS tree, so
        # deleting the edge invalidates the DFS tree, so start from scratch
        update_domtree!(blocks, domtree, true, 0; cache)
    elseif on_semidominator_path(domtree, from, to)
        # Recompute semidominators for blocks with preorder number up to that
        # of `to` block. [...]
        to_pre = domtree.dfs_tree.to_pre[to]
        update_domtree!(blocks, domtree, false, to_pre; cache)
    end
    # Otherwise, dominator tree is not affected

    return domtree
end
```
-/
def domtreeDeleteEdge! (domtree : GenericDomTree) (blocks : Blocks) (frm to : Int) :
    JM GenericDomTree := do
  if ← bbUnreachable domtree frm then return domtree
  if ← isParent domtree.dfsTree frm to then
    updateDomtree! blocks domtree true 0
  else if ← onSemidominatorPath domtree frm to then
    let toPre ← aget domtree.dfsTree.toPre to
    updateDomtree! blocks domtree false toPre
  else pure domtree

/-- `rename_nodes!(D::DFSTree, rename_bb)`

Julia source: Compiler/src/ssair/domtree.jl:605-635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rename_nodes!(D::DFSTree, rename_bb::Vector{BBNumber})
    n_blocks = length(D.to_pre)
    n_reachable_blocks = length(D.from_pre)

    old_to_pre = copy(D.to_pre)
    old_from_pre = copy(D.from_pre)
    old_to_post = copy(D.to_post)
    old_from_post = copy(D.from_post)
    max_new_bb = 0
    for (old_bb, new_bb) in enumerate(rename_bb)
        if new_bb != -1
            D.to_pre[new_bb] = old_to_pre[old_bb]
            D.from_pre[old_to_pre[old_bb]] = new_bb
            D.to_post[new_bb] = old_to_post[old_bb]
            D.from_post[old_to_post[old_bb]] = new_bb

            # Keep track of highest BB number to resize arrays with
            if new_bb > max_new_bb
                max_new_bb = new_bb
            end
        end
    end
    resize!(D.to_pre, max_new_bb)
    resize!(D.to_post, max_new_bb)
    # `to_parent_pre` should be unchanged
    return D
end
```
The unused `n_blocks`, `n_reachable_blocks`, `old_from_pre` and `old_from_post` are left out. -/
def renameNodesDFS! (D : DFSTree) (renameBB : Array Int) : JM DFSTree := do
  let oldToPre := D.toPre
  let oldToPost := D.toPost
  let (D, maxNewBB) ← (irange 1 renameBB.size).foldlM (fun (acc : DFSTree × Int) oldBB => do
    let (D, maxNewBB) := acc
    let newBB ← aget renameBB oldBB
    if newBB != -1 then
      let toPre ← aset D.toPre newBB (← aget oldToPre oldBB)
      let fromPre ← aset D.fromPre (← aget oldToPre oldBB) newBB
      let toPost ← aset D.toPost newBB (← aget oldToPost oldBB)
      let fromPost ← aset D.fromPost (← aget oldToPost oldBB) newBB
      pure ({ D with toPre, fromPre, toPost, fromPost }, if newBB > maxNewBB then newBB else maxNewBB)
    else pure (D, maxNewBB)) (D, 0)
  pure { D with toPre := ssair.resize D.toPre maxNewBB.toNat 0,
                toPost := ssair.resize D.toPost maxNewBB.toNat 0 }

/-- `rename_nodes!(domtree::DomTree, rename_bb)`

Julia source: Compiler/src/ssair/domtree.jl:575-603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rename_nodes!(domtree::DomTree, rename_bb::Vector{BBNumber})
    # Rename DFS tree
    rename_nodes!(domtree.dfs_tree, rename_bb)

    # `snca_state` is indexed by preorder number, so should be unchanged

    # Rename `idoms_bb` and `nodes`
    old_idoms_bb = copy(domtree.idoms_bb)
    old_nodes = copy(domtree.nodes)
    for (old_bb, new_bb) in enumerate(rename_bb)
        if new_bb != -1
            domtree.idoms_bb[new_bb] = (new_bb == 1) ?
                0 : rename_bb[old_idoms_bb[old_bb]]
            domtree.nodes[new_bb] = old_nodes[old_bb]
            map!(i -> rename_bb[i],
                 domtree.nodes[new_bb].children,
                 domtree.nodes[new_bb].children)
        end
    end

    # length of `to_pre` after renaming DFS tree is new number of basic blocks
    resize!(domtree.idoms_bb, length(domtree.dfs_tree.to_pre))
    resize!(domtree.nodes, length(domtree.dfs_tree.to_pre))
    return domtree
end
```
`old_nodes` is a shallow copy, so the children vector of `old_nodes[old_bb]` is also the one
of `domtree.nodes[old_bb]`. The `map!` renames that vector in place, so a slot `old_bb` that no
block is renamed to ends up with the renamed children too; the last step mirrors that. See the
module docstring for the sharing that remains after the call. -/
def renameNodes! (domtree : GenericDomTree) (renameBB : Array Int) : JM GenericDomTree := do
  let D ← renameNodesDFS! domtree.dfsTree renameBB
  let oldIdoms := domtree.idomsBB
  let oldNodes := domtree.nodes
  let (idomsBB, nodes, written) ← (irange 1 renameBB.size).foldlM
    (fun (acc : Array Int × Array DomTreeNode × List Int) oldBB => do
      let (idomsBB, nodes, written) := acc
      let newBB ← aget renameBB oldBB
      if newBB != -1 then
        let idom ← if newBB == 1 then pure 0 else aget renameBB (← aget oldIdoms oldBB)
        let idomsBB ← aset idomsBB newBB idom
        let old ← aget oldNodes oldBB
        let nodes ← aset nodes newBB old
        let children ← old.children.mapM (aget renameBB)
        let nodes ← aset nodes newBB { old with children }
        pure (idomsBB, nodes, newBB :: written)
      else pure (idomsBB, nodes, written)) (domtree.idomsBB, domtree.nodes, [])
  -- A kept block's own slot that nothing overwrote still holds its (now renamed) vector.
  let nodes ← (irange 1 renameBB.size).foldlM (fun nodes oldBB => do
      if (← aget renameBB oldBB) != -1 && !written.contains oldBB then
        let old ← aget oldNodes oldBB
        aset nodes oldBB { old with children := ← old.children.mapM (aget renameBB) }
      else pure nodes) nodes
  let n := D.toPre.size
  pure { domtree with dfsTree := D, idomsBB := ssair.resize idomsBB n 0,
                      nodes := ssair.resize nodes n DomTreeNode.new }

/-- `_dominates(domtree, bb1, bb2)`; `dominates` and `postdominates` are this function.

Julia source: Compiler/src/ssair/domtree.jl:645-668 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dominates(domtree::DomTree, bb1::BBNumber, bb2::BBNumber) =
    _dominates(domtree, bb1, bb2)

postdominates(domtree::PostDomTree, bb1::BBNumber, bb2::BBNumber) =
    _dominates(domtree, bb1, bb2)

function _dominates(domtree::GenericDomTree, bb1::BBNumber, bb2::BBNumber)
    bb1 == bb2 && return true
    target_level = domtree.nodes[bb1].level
    source_level = domtree.nodes[bb2].level
    source_level < target_level && return false
    for _ in (source_level - 1):-1:target_level
        bb2 = domtree.idoms_bb[bb2]
    end
    return bb1 == bb2
end
```
-/
def dominates (domtree : GenericDomTree) (bb1 bb2 : Int) : JM Bool := do
  if bb1 == bb2 then return true
  let targetLevel := (← aget domtree.nodes bb1).level
  let sourceLevel := (← aget domtree.nodes bb2).level
  if sourceLevel < targetLevel then return false
  let bb2 ← (irange targetLevel (sourceLevel - 1)).foldlM
    (fun bb2 _ => aget domtree.idomsBB bb2) bb2
  return bb1 == bb2

/-- The `iterate` loop over `DominatedBlocks`, collected. -/
def dominatedLoop (domtree : GenericDomTree) : Nat → Array Int → Array Int → JM (Array Int)
  | 0, _, _ => outOfBudget
  | fuel + 1, wl, out =>
    match wl.back? with
    | none => pure out
    | some bb => do
      let n ← aget domtree.nodes bb
      dominatedLoop domtree fuel (n.children.foldl Array.push wl.pop) (out.push bb)

/-- `collect(dominated(domtree, root))`: the blocks the iterator yields, in order.

Julia source: Compiler/src/ssair/domtree.jl:672-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"Iterable data structure that walks through all dominated blocks"
struct DominatedBlocks
    domtree::DomTree
    worklist::Vector{BBNumber}
end

"Returns an iterator that walks through all blocks dominated by the basic block at index `root`"
function dominated(domtree::DomTree, root::BBNumber)
    doms = DominatedBlocks(domtree, Vector{BBNumber}())
    push!(doms.worklist, root)
    doms
end

function iterate(doms::DominatedBlocks, state::Nothing=nothing)
    isempty(doms.worklist) && return nothing
    bb = pop!(doms.worklist)
    for dominated in doms.domtree.nodes[bb].children
        push!(doms.worklist, dominated)
    end
    return (bb, nothing)
end
```
-/
def dominated (domtree : GenericDomTree) (root : Int) : JM (Array Int) :=
  dominatedLoop domtree (2 * (domtree.nodes.size + 2)) #[root] #[]

/-- The two loops of `nearest_common_dominator` (Compiler/src/ssair/domtree.jl:709-716). -/
def ncdLevelLoop (idoms : Array Int) (blevel : Int) : Nat → Int → Int → JM Int
  | 0, _, _ => outOfBudget
  | fuel + 1, a, alevel =>
    if alevel > blevel then do ncdLevelLoop idoms blevel fuel (← aget idoms a) (alevel - 1)
    else pure a

def ncdLoop (idoms : Array Int) : Nat → Int → Int → JM (Int × Int)
  | 0, _, _ => outOfBudget
  | fuel + 1, a, b =>
    if a != b && a != 0 then do ncdLoop idoms fuel (← aget idoms a) (← aget idoms b)
    else pure (a, b)

/-- `nearest_common_dominator(domtree, a, b)`

Julia source: Compiler/src/ssair/domtree.jl:694-719 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function nearest_common_dominator(domtree::GenericDomTree, a::BBNumber, b::BBNumber)
    a == 0 && return a
    b == 0 && return b
    alevel = domtree.nodes[a].level
    blevel = domtree.nodes[b].level
    # W.l.g. assume blevel <= alevel
    if alevel < blevel
        a, b = b, a
        alevel, blevel = blevel, alevel
    end
    while alevel > blevel
        a = domtree.idoms_bb[a]
        alevel -= 1
    end
    while a != b && a != 0
        a = domtree.idoms_bb[a]
        b = domtree.idoms_bb[b]
    end
    @assert a == b
    return a
end
```
-/
def nearestCommonDominator (domtree : GenericDomTree) (a b : Int) : JM Int := do
  if a == 0 then return a
  if b == 0 then return b
  let alevel := (← aget domtree.nodes a).level
  let blevel := (← aget domtree.nodes b).level
  let (a, b, alevel, blevel) := if alevel < blevel then (b, a, blevel, alevel)
    else (a, b, alevel, blevel)
  let fuel := 2 * (domtree.nodes.size + 2)
  let a ← ncdLevelLoop domtree.idomsBB blevel ((alevel - blevel).toNat + 1) a alevel
  let (a, b) ← ncdLoop domtree.idomsBB fuel a b
  unless a == b do throw "julia:AssertionError"
  return a

/-! ### `naive_idoms`

`BitSet`s are sorted lists without duplicates. -/

/-- `push!(s, x)` on a `BitSet`. -/
def bsInsert (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x == y then y :: ys else y :: bsInsert x ys

/-- `intersect!(s, t)` on `BitSet`s. -/
def bsInter (s t : List Int) : List Int := s.filter (t.contains ·)

/-- One `for n in relevant_blocks` sweep of `naive_idoms`
(Compiler/src/ssair/domtree.jl:732-745). Returns the sets and `changed`. -/
def naiveSweep (blocks : Blocks) (isPost : Bool) :
    List Int → Array (List Int) → Bool → JM (Array (List Int) × Bool)
  | [], doms, changed => pure (doms, changed)
  | n :: rest, doms, changed => do
    let b ← aget blocks n
    let edges := if isPost then b.succs else b.preds
    if edges.isEmpty then naiveSweep blocks isPost rest doms changed
    else
      match edges.toList.filter (· != 0) with
      | [] => throw "julia:TypeError"
      | firstp :: ps => do
        let newDoms ← ps.foldlM (fun s p => do pure (bsInter s (← aget doms p)))
          (← aget doms firstp)
        let newDoms := bsInsert n newDoms
        let changed := changed || newDoms != (← aget doms n)
        naiveSweep blocks isPost rest (← aset doms n newDoms) changed

def naiveFixpoint (blocks : Blocks) (isPost : Bool) (relevant : List Int) :
    Nat → Array (List Int) → JM (Array (List Int))
  | 0, _ => outOfBudget
  | fuel + 1, doms => do
    let (doms, changed) ← naiveSweep blocks isPost relevant doms false
    if changed then naiveFixpoint blocks isPost relevant fuel doms else pure doms

/-- The idom choice of `naive_idoms` for one block (Compiler/src/ssair/domtree.jl:754-765):
the last `dom` that passes the test is kept. -/
def naivePick (dominators : Array (List Int)) (i : Int) (doms : List Int) :
    List Int → Int → JM Int
  | [], cur => pure cur
  | dom :: rest, cur =>
    if i == dom then naivePick dominators i doms rest cur
    else do
      let hasany ← doms.anyM fun p => do
        if p != i && p != dom then pure ((← aget dominators p).contains dom) else pure false
      naivePick dominators i doms rest (if hasany then cur else dom)

/-- `naive_idoms(blocks, is_post_dominator=false)`

Julia source: Compiler/src/ssair/domtree.jl:721-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function naive_idoms(blocks::Vector{BasicBlock}, is_post_dominator::Bool=false)
    nblocks = length(blocks)
    # The extra +1 helps us detect unreachable blocks below
    dom_all = BitSet(1:nblocks+1)
    dominators = is_post_dominator ?
        BitSet[isempty(blocks[n].succs) ? BitSet(n) : copy(dom_all) for n = 1:nblocks] :
        BitSet[n == 1 ? BitSet(1) : copy(dom_all) for n = 1:nblocks]
    changed = true
    relevant_blocks = (is_post_dominator ? (1:nblocks) : (2:nblocks))
    while changed
        changed = false
        for n in relevant_blocks
            edges = is_post_dominator ? blocks[n].succs : blocks[n].preds
            if isempty(edges)
                continue
            end
            firstp, rest = Iterators.peel(Iterators.filter(p->p != 0, edges))::NTuple{2,Any}
            new_doms = copy(dominators[firstp])
            for p in rest
                intersect!(new_doms, dominators[p])
            end
            push!(new_doms, n)
            changed = changed || (new_doms != dominators[n])
            dominators[n] = new_doms
        end
    end
    # Compute idoms
    idoms = fill(0, nblocks)
    for i in relevant_blocks
        if dominators[i] == dom_all
            idoms[i] = 0
            continue
        end
        doms = collect(dominators[i])
        for dom in doms
            i == dom && continue
            hasany = false
            for p in doms
                if p !== i && p !== dom && dom in dominators[p]
                    hasany = true; break
                end
            end
            hasany && continue
            idoms[i] = dom
        end
    end
    idoms
end
```
The sets only shrink, so `nblocks * (nblocks + 2) + 2` sweeps are enough. -/
def naiveIdoms (blocks : Blocks) (isPost : Bool := false) : JM (Array Int) := do
  let nblocks := blocks.size
  let domAll := irange 1 (nblocks + 1)
  let dominators := (Array.range nblocks).map fun (i : Nat) =>
    let n : Int := (i : Int) + 1
    if isPost then (if (blocks[i]?.map (·.succs.isEmpty)).getD false then [n] else domAll)
    else if n == 1 then [1] else domAll
  let relevant := if isPost then irange 1 nblocks else irange 2 nblocks
  let dominators ← naiveFixpoint blocks isPost relevant (nblocks * (nblocks + 2) + 2) dominators
  relevant.foldlM (fun idoms i => do
    let di ← aget dominators i
    if di == domAll then aset idoms i 0
    else aset idoms i (← naivePick dominators i di di (← aget idoms i)))
    (Array.replicate nblocks (0 : Int))

end JuliaLean.Compiler.ssair
