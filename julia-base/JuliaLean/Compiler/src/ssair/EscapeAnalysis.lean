import JuliaLean.Compiler.src.ssair.disjoint_set

/-!
Source-mirrored model of `Compiler/src/ssair/EscapeAnalysis.jl` at
f755f49a9e41380d7da126b3c1db9fe7f83dd027: the `EscapeInfo` lattice (`==`, `⊑ₑ`, `⊏ₑ`, `⋤ₑ`,
`⊔ₑ`, `merge_alias_info`, `merge_to_unindexable`), the escape queries, the `ignore_*`
constructors, `ArgEscapeInfo`/`from_interprocedural`/`ArgEscapeCache`, the alias-set queries,
the change propagation, every statement transfer function (`escape_call!` with the builtin
handlers, `escape_new!`, `escape_invoke!`, `escape_foreigncall!`, `escape_foreignglobal!`,
`escape_gc_preserve!`, `escape_edges!`, `escape_val!`, `escape_exception!`) and the fixed-point
loop `analyze_escapes`.

Modelling choices:

* `BitSet`s are sorted lists of `Int` (`IntSet`). The source compares the `ThrownEscape` and
  `Liveness` fields with `===` against the constants `BOT_THROWN_ESCAPE`, `TOP_THROWN_ESCAPE`,
  `BOT_LIVENESS`, `TOP_LIVENESS` and `ARG_LIVENESS`, so those constants are separate
  constructors (`TSet.bot`/`top`, `LRef.bot`/`top`/`arg`), distinct from a fresh set with the
  same contents.
* `ThrownEscape` sets are never mutated after construction, so `TSet.fresh` is a value.
  `Liveness` sets are mutated in place by `propagate_liveness_change!` (line 760), and `⊔ₑ`,
  the keyword constructors and the change records share one `BitSet` object between several
  `EscapeInfo`s. So a non-constant `Liveness` is a reference `LRef.ref n` into a `Heap`, and
  every function that allocates or mutates one threads the heap.
* `AliasInfo` sets (`IdSet{Any}` of `LocalDef`/`LocalUse`) are shared by `merge_alias_info`
  but only ever mutated right after a `copy` or a fresh construction in the same function, so
  they are values. An element is encoded as one integer: `LocalDef(i)` is `2i`, `LocalUse(i)`
  is `2i + 1` (`AElt.key`). An `IdSet` iterates in insertion order and `a ∪ b` lists `a`
  first, so `AInfo` is an insertion-ordered list and `add_alias_escapes!` visits it in order.
* The IR is abstracted to what the analysis reads. Each statement is a `Stmt` whose operands are
  `Opnd`s, and each type-dependent query the source makes (`is_identity_free_argtype`,
  `fieldcount_noerror`, `try_compute_fieldidx`, `hasintersect(_, Module)`, `setfield!_nothrow`,
  `IR_FLAG_NOTHROW`, the `Const` condition of `ifelse`, `singleton_type` of the callee, the escape
  cache) is a precomputed field, filled by the difftest from the pinned Compiler's own functions.
  These belong to other files (typeutils, tfuncs, optimize) and are not modelled here.
* `ir.new_nodes` is not modelled: the statements are `ir.stmts` only, and the difftest only
  uses IR whose `new_nodes` is empty.
* Julia exceptions are `julia:<Exception>` strings in `JM`; the fixed-point loop takes fuel.
-/

namespace JuliaLean.Compiler.ssair.EA

open JuliaLean.Compiler.ssair

/-! ## Sets -/

/-- A `BitSet`'s contents, kept sorted and without duplicates. -/
abbrev IntSet := List Int

namespace IntSet
def norm (l : List Int) : IntSet := (l.mergeSort fun a b => decide (a ≤ b)).eraseDups
def mem (s : IntSet) (x : Int) : Bool := s.contains x
def subset (a b : IntSet) : Bool := a.all fun x => b.contains x
def union (a b : IntSet) : IntSet := norm (a ++ b)
def insert (s : IntSet) (x : Int) : IntSet := norm (x :: s)
def erase (s : IntSet) (x : Int) : IntSet := s.filter (· != x)
def seteq (a b : IntSet) : Bool := subset a b && subset b a
end IntSet

/-- An `AInfo` element. `LocalDef(i)` (line 821) and `LocalUse(i)` (line 824). -/
inductive AElt where
  | def_ (i : Int)
  | use (i : Int)
  deriving Repr, BEq, DecidableEq, Inhabited

def AElt.key : AElt → Int
  | .def_ i => 2 * i
  | .use i => 2 * i + 1

def AElt.ofKey (k : Int) : AElt := if k % 2 == 1 then .use (k / 2) else .def_ (k / 2)

/-- `const AInfo = IdSet{Any}` (line 43), as the keys of its elements in insertion order, which
is the order an `IdSet` iterates (no element is ever deleted from one here). -/
abbrev AInfo := List Int

namespace AInfo
/-- `push!(s, x)`: appended unless already present. -/
def push (s : AInfo) (x : Int) : AInfo := if s.contains x then s else s ++ [x]
/-- `a ∪ b`: the elements of `a`, then those of `b` not in `a`. -/
def union (a b : AInfo) : AInfo := b.foldl push a
end AInfo

/-- The `ThrownEscape` field: one of the two constants, or a fresh `BitSet`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:127-130
```julia
const BOT_THROWN_ESCAPE = BitSet()
# NOTE the lattice operations should try to avoid actual set computations on this top value,
# and e.g. BitSet(0:1000000) should also work without incurring excessive computations
const TOP_THROWN_ESCAPE = BitSet(-1)
```
-/
inductive TSet where
  | bot
  | top
  | fresh (s : IntSet)
  deriving Repr, BEq, DecidableEq, Inhabited

def TSet.elems : TSet → IntSet
  | .bot => []
  | .top => [-1]
  | .fresh s => s

/-- The `Liveness` field: one of the three constants, or a heap reference.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:132-136
```julia
const BOT_LIVENESS = BitSet()
# NOTE the lattice operations should try to avoid actual set computations on this top value,
# and e.g. BitSet(0:1000000) should also work without incurring excessive computations
const TOP_LIVENESS = BitSet(-1:0)
const ARG_LIVENESS = BitSet(0)
```
-/
inductive LRef where
  | bot
  | top
  | arg
  | ref (n : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The mutable `Liveness` `BitSet`s that are not constants. -/
structure Heap where
  sets : Array IntSet := #[]
  deriving Repr, Inhabited

namespace Heap
def get (h : Heap) : LRef → IntSet
  | .bot => []
  | .top => [-1, 0]
  | .arg => [0]
  | .ref n => h.sets.getD n []
def alloc (h : Heap) (s : IntSet) : LRef × Heap := (.ref h.sets.size, ⟨h.sets.push s⟩)
/-- `push!(Liveness, x)` on a non-constant set: every `EscapeInfo` holding `r` sees it. -/
def push (h : Heap) (r : LRef) (x : Int) : Heap :=
  match r with
  | .ref n => ⟨h.sets.modify n fun s => IntSet.insert s x⟩
  | _ => h
end Heap

/-! ## The lattice -/

/-- `AliasInfo::Union{Bool,IndexableFields,Unindexable}`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:165-170
```julia
struct IndexableFields
    infos::Vector{AInfo}
end
struct Unindexable
    info::AInfo
end
```
-/
inductive AliasInfo where
  | bool (b : Bool)
  | indexable (infos : List AInfo)
  | unindexable (info : AInfo)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `struct EscapeInfo`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:85-90
```julia
struct EscapeInfo
    Analyzed::Bool
    ReturnEscape::Bool
    ThrownEscape::BitSet
    AliasInfo #::Union{IndexableFields,Unindexable,Bool}
    Liveness::BitSet
```
-/
structure EscapeInfo where
  analyzed : Bool
  returnEscape : Bool
  thrown : TSet
  alias : AliasInfo
  live : LRef
  deriving Repr, BEq, DecidableEq, Inhabited

/-- `NotAnalyzed()`, which is `⊥`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:139
```julia
NotAnalyzed() = EscapeInfo(false, false, BOT_THROWN_ESCAPE, false, BOT_LIVENESS) # not formally part of the lattice
```
-/
def notAnalyzed : EscapeInfo := ⟨false, false, .bot, .bool false, .bot⟩

/-- `NoEscape()`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:140
```julia
NoEscape() = EscapeInfo(true, false, BOT_THROWN_ESCAPE, false, BOT_LIVENESS)
```
-/
def noEscape : EscapeInfo := ⟨true, false, .bot, .bool false, .bot⟩

/-- `ArgEscape()`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:141
```julia
ArgEscape() = EscapeInfo(true, false, BOT_THROWN_ESCAPE, true, ARG_LIVENESS)
```
-/
def argEscape : EscapeInfo := ⟨true, false, .bot, .bool true, .arg⟩

/-- `ReturnEscape(pc)`: allocates the fresh `BitSet(pc)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:142
```julia
ReturnEscape(pc::Int) = EscapeInfo(true, true, BOT_THROWN_ESCAPE, false, BitSet(pc))
```
-/
def returnEscapeAt (h : Heap) (pc : Int) : EscapeInfo × Heap :=
  let (r, h) := h.alloc [pc]
  (⟨true, true, .bot, .bool false, r⟩, h)

/-- `AllReturnEscape()`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:143
```julia
AllReturnEscape() = EscapeInfo(true, true, BOT_THROWN_ESCAPE, false, TOP_LIVENESS)
```
-/
def allReturnEscape : EscapeInfo := ⟨true, true, .bot, .bool false, .top⟩

/-- `ThrownEscape(pc)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:144
```julia
ThrownEscape(pc::Int) = EscapeInfo(true, false, BitSet(pc), false, BOT_LIVENESS)
```
-/
def thrownEscapeAt (pc : Int) : EscapeInfo := ⟨true, false, .fresh [pc], .bool false, .bot⟩

/-- `AllEscape()`, which is `⊤`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:145-147
```julia
AllEscape() = EscapeInfo(true, true, TOP_THROWN_ESCAPE, true, TOP_LIVENESS)

const ⊥, ⊤ = NotAnalyzed(), AllEscape()
```
-/
def allEscape : EscapeInfo := ⟨true, true, .top, .bool true, .top⟩

/-- `x === ⊤`. `EscapeInfo` is immutable, so `===` compares its fields with `===`; the constant
sets of `⊤` are the `TSet.top`/`LRef.top` constructors. -/
def isTop (x : EscapeInfo) : Bool :=
  x.analyzed && x.returnEscape && x.thrown == .top && x.alias == .bool true && x.live == .top

/-- `x === ⊥`. -/
def isBot (x : EscapeInfo) : Bool :=
  !x.analyzed && !x.returnEscape && x.thrown == .bot && x.alias == .bool false && x.live == .bot

/-! ### Queries -/

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:150
```julia
has_no_escape(x::EscapeInfo) = !x.ReturnEscape && isempty(x.ThrownEscape) && 0 ∉ x.Liveness
```
-/
def hasNoEscape (h : Heap) (x : EscapeInfo) : Bool :=
  !x.returnEscape && x.thrown.elems.isEmpty && !(h.get x.live).mem 0

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:151
```julia
has_arg_escape(x::EscapeInfo) = 0 ∈ x.Liveness
```
-/
def hasArgEscape (h : Heap) (x : EscapeInfo) : Bool := (h.get x.live).mem 0

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:152
```julia
has_return_escape(x::EscapeInfo) = x.ReturnEscape
```
-/
def hasReturnEscape (x : EscapeInfo) : Bool := x.returnEscape

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:153
```julia
has_return_escape(x::EscapeInfo, pc::Int) = x.ReturnEscape && (-1 ∈ x.Liveness || pc ∈ x.Liveness)
```
-/
def hasReturnEscapeAt (h : Heap) (x : EscapeInfo) (pc : Int) : Bool :=
  x.returnEscape && ((h.get x.live).mem (-1) || (h.get x.live).mem pc)

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:154
```julia
has_thrown_escape(x::EscapeInfo) = !isempty(x.ThrownEscape)
```
-/
def hasThrownEscape (x : EscapeInfo) : Bool := !x.thrown.elems.isEmpty

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:155
```julia
has_thrown_escape(x::EscapeInfo, pc::Int) = -1 ∈ x.ThrownEscape || pc ∈ x.ThrownEscape
```
-/
def hasThrownEscapeAt (x : EscapeInfo) (pc : Int) : Bool :=
  x.thrown.elems.mem (-1) || x.thrown.elems.mem pc

/-! ### Alias information -/

/-- `merge_to_unindexable(info::AInfo, infos::Vector{AInfo})`, and with `AInfo()` for the
one-argument method.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:176-184
```julia
merge_to_unindexable(AliasInfo::IndexableFields) = Unindexable(merge_to_unindexable(AliasInfo.infos))
merge_to_unindexable(AliasInfo::Unindexable, AliasInfos::IndexableFields) = Unindexable(merge_to_unindexable(AliasInfo.info, AliasInfos.infos))
merge_to_unindexable(infos::Vector{AInfo}) = merge_to_unindexable(AInfo(), infos)
function merge_to_unindexable(info::AInfo, infos::Vector{AInfo})
    for i = 1:length(infos)
        info = info ∪ infos[i]
    end
    return info
end
```
-/
def mergeToUnindexable (info : AInfo) (infos : List AInfo) : AInfo :=
  infos.foldl AInfo.union info

/-- `merge_alias_info(xa, ya)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:362-400
```julia
function merge_alias_info(@nospecialize(xa), @nospecialize(ya))
    if xa === true || ya === true
        return true
    elseif xa === false
        return ya
    elseif ya === false
        return xa
    elseif isa(xa, IndexableFields)
        if isa(ya, IndexableFields)
            xinfos, yinfos = xa.infos, ya.infos
            xn, yn = length(xinfos), length(yinfos)
            nmax, nmin = max(xn, yn), min(xn, yn)
            infos = Vector{AInfo}(undef, nmax)
            for i in 1:nmax
                if i > nmin
                    infos[i] = (xn > yn ? xinfos : yinfos)[i]
                else
                    infos[i] = xinfos[i] ∪ yinfos[i]
                end
            end
            return IndexableFields(infos)
        elseif isa(ya, Unindexable)
            xinfos, yinfo = xa.infos, ya.info
            return merge_to_unindexable(ya, xa)
        else
            return true # handle conflicting case conservatively
        end
    else
        xa = xa::Unindexable
        if isa(ya, IndexableFields)
            return merge_to_unindexable(xa, ya)
        else
            ya = ya::Unindexable
            xinfo, yinfo = xa.info, ya.info
            info = xinfo ∪ yinfo
            return Unindexable(info)
        end
    end
end
```
-/
def mergeAliasInfo (xa ya : AliasInfo) : AliasInfo :=
  if xa == .bool true || ya == .bool true then .bool true
  else if xa == .bool false then ya
  else if ya == .bool false then xa
  else match xa, ya with
    | .indexable xinfos, .indexable yinfos =>
      let xn := xinfos.length
      let yn := yinfos.length
      let nmin := min xn yn
      let longer := if xn > yn then xinfos else yinfos
      .indexable ((List.range (max xn yn)).map fun i =>
        if i + 1 > nmin then longer.getD i []
        else AInfo.union (xinfos.getD i []) (yinfos.getD i []))
    | .indexable xinfos, .unindexable yinfo => .unindexable (mergeToUnindexable yinfo xinfos)
    | .indexable _, .bool _ => .bool true
    | .unindexable xinfo, .indexable yinfos => .unindexable (mergeToUnindexable xinfo yinfos)
    | .unindexable xinfo, .unindexable yinfo => .unindexable (AInfo.union xinfo yinfo)
    -- unreachable: both `Bool` cases returned above
    | _, _ => .bool true

/-! ### Order and join -/

/-- `x == y`, the lattice equality used for convergence. The `x === y` fast path is left out:
`===` on `EscapeInfo` implies every later test passes, so it never changes the result.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:188-221
```julia
x::EscapeInfo == y::EscapeInfo = begin
    # fast path: better to avoid top comparison
    x === y && return true
    x.Analyzed === y.Analyzed || return false
    x.ReturnEscape === y.ReturnEscape || return false
    xt, yt = x.ThrownEscape, y.ThrownEscape
    if xt === TOP_THROWN_ESCAPE
        yt === TOP_THROWN_ESCAPE || return false
    elseif yt === TOP_THROWN_ESCAPE
        return false # x.ThrownEscape === TOP_THROWN_ESCAPE
    else
        xt == yt || return false
    end
    xa, ya = x.AliasInfo, y.AliasInfo
    if isa(xa, Bool)
        xa === ya || return false
    elseif isa(xa, IndexableFields)
        isa(ya, IndexableFields) || return false
        xa.infos == ya.infos || return false
    else
        xa = xa::Unindexable
        isa(ya, Unindexable) || return false
        xa.info == ya.info || return false
    end
    xl, yl = x.Liveness, y.Liveness
    if xl === TOP_LIVENESS
        yl === TOP_LIVENESS || return false
    elseif yl === TOP_LIVENESS
        return false # x.Liveness === TOP_LIVENESS
    else
        xl == yl || return false
    end
    return true
end
```
-/
def eqE (h : Heap) (x y : EscapeInfo) : Bool := Id.run do
  if x.analyzed != y.analyzed then return false
  if x.returnEscape != y.returnEscape then return false
  if x.thrown == .top then
    if y.thrown != .top then return false
  else if y.thrown == .top then return false
  else if !IntSet.seteq x.thrown.elems y.thrown.elems then return false
  match x.alias with
  | .bool b => if y.alias != .bool b then return false
  | .indexable xinfos =>
    match y.alias with
    | .indexable yinfos =>
      if !(xinfos.length == yinfos.length &&
          (xinfos.zip yinfos).all fun (a, b) => IntSet.seteq a b) then return false
    | _ => return false
  | .unindexable xinfo =>
    match y.alias with
    | .unindexable yinfo => if !IntSet.seteq xinfo yinfo then return false
    | _ => return false
  if x.live == .top then
    if y.live != .top then return false
  else if y.live == .top then return false
  else if !IntSet.seteq (h.get x.live) (h.get y.live) then return false
  return true

/-- `x ⊑ₑ y`. In the `IndexableFields`/`Unindexable` case the source loops over
`for i = length(xinfos)`, which is the single index `length(xinfos)`; the model does the same,
including the `BoundsError` when `xinfos` is empty.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:246-300
```julia
x::EscapeInfo ⊑ₑ y::EscapeInfo = begin
    # fast path: better to avoid top comparison
    if y === ⊤
        return true
    elseif x === ⊤
        return false # return y === ⊤
    elseif x === ⊥
        return true
    elseif y === ⊥
        return false # return x === ⊥
    end
    x.Analyzed ≤ y.Analyzed || return false
    x.ReturnEscape ≤ y.ReturnEscape || return false
    xt, yt = x.ThrownEscape, y.ThrownEscape
    if xt === TOP_THROWN_ESCAPE
        yt !== TOP_THROWN_ESCAPE && return false
    elseif yt !== TOP_THROWN_ESCAPE
        xt ⊆ yt || return false
    end
    xa, ya = x.AliasInfo, y.AliasInfo
    if isa(xa, Bool)
        xa && ya !== true && return false
    elseif isa(xa, IndexableFields)
        if isa(ya, IndexableFields)
            xinfos, yinfos = xa.infos, ya.infos
            xn, yn = length(xinfos), length(yinfos)
            xn > yn && return false
            for i in 1:xn
                xinfos[i] ⊆ yinfos[i] || return false
            end
        elseif isa(ya, Unindexable)
            xinfos, yinfo = xa.infos, ya.info
            for i = length(xinfos)
                xinfos[i] ⊆ yinfo || return false
            end
        else
            ya === true || return false
        end
    else
        xa = xa::Unindexable
        if isa(ya, Unindexable)
            xinfo, yinfo = xa.info, ya.info
            xinfo ⊆ yinfo || return false
        else
            ya === true || return false
        end
    end
    xl, yl = x.Liveness, y.Liveness
    if xl === TOP_LIVENESS
        yl !== TOP_LIVENESS && return false
    elseif yl !== TOP_LIVENESS
        xl ⊆ yl || return false
    end
    return true
end
```
-/
def sqsub (h : Heap) (x y : EscapeInfo) : JM Bool := do
  if isTop y then return true
  else if isTop x then return false
  else if isBot x then return true
  else if isBot y then return false
  if !(!x.analyzed || y.analyzed) then return false
  if !(!x.returnEscape || y.returnEscape) then return false
  if x.thrown == .top then
    if y.thrown != .top then return false
  else if y.thrown != .top then
    if !IntSet.subset x.thrown.elems y.thrown.elems then return false
  match x.alias with
  | .bool b => if b && y.alias != .bool true then return false
  | .indexable xinfos =>
    match y.alias with
    | .indexable yinfos =>
      if xinfos.length > yinfos.length then return false
      if !((xinfos.zip yinfos).all fun (a, b) => IntSet.subset a b) then return false
    | .unindexable yinfo =>
      let xi ← aget xinfos.toArray xinfos.length
      if !IntSet.subset xi yinfo then return false
    | .bool b => if !b then return false
  | .unindexable xinfo =>
    match y.alias with
    | .unindexable yinfo => if !IntSet.subset xinfo yinfo then return false
    | .bool b => if !b then return false
    | .indexable _ => return false
  if x.live == .top then
    if y.live != .top then return false
  else if y.live != .top then
    if !IntSet.subset (h.get x.live) (h.get y.live) then return false
  return true

/-- `x ⊏ₑ y`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:308
```julia
x::EscapeInfo ⊏ₑ y::EscapeInfo = x ⊑ₑ y && !(y ⊑ₑ x)
```
-/
def sqsubStrict (h : Heap) (x y : EscapeInfo) : JM Bool := do
  if ← sqsub h x y then return !(← sqsub h y x) else return false

/-- `x ⋤ₑ y`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:316
```julia
x::EscapeInfo ⋤ₑ y::EscapeInfo = !(y ⊑ₑ x)
```
-/
def sqsubNe (h : Heap) (x y : EscapeInfo) : JM Bool := do return !(← sqsub h y x)

/-- `has_all_escape(x)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:156
```julia
has_all_escape(x::EscapeInfo) = ⊤ ⊑ₑ x
```
-/
def hasAllEscape (h : Heap) (x : EscapeInfo) : JM Bool := sqsub h allEscape x

/-- `x ⊔ₑ y`. A fresh `xl ∪ yl` is allocated in the heap; otherwise the result shares one of
the argument `Liveness` objects.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:323-360
```julia
x::EscapeInfo ⊔ₑ y::EscapeInfo = begin
    # fast path: better to avoid top join
    if x === ⊤ || y === ⊤
        return ⊤
    elseif x === ⊥
        return y
    elseif y === ⊥
        return x
    end
    xt, yt = x.ThrownEscape, y.ThrownEscape
    if xt === TOP_THROWN_ESCAPE || yt === TOP_THROWN_ESCAPE
        ThrownEscape = TOP_THROWN_ESCAPE
    elseif xt === BOT_THROWN_ESCAPE
        ThrownEscape = yt
    elseif yt === BOT_THROWN_ESCAPE
        ThrownEscape = xt
    else
        ThrownEscape = xt ∪ yt
    end
    AliasInfo = merge_alias_info(x.AliasInfo, y.AliasInfo)
    xl, yl = x.Liveness, y.Liveness
    if xl === TOP_LIVENESS || yl === TOP_LIVENESS
        Liveness = TOP_LIVENESS
    elseif xl === BOT_LIVENESS
        Liveness = yl
    elseif yl === BOT_LIVENESS
        Liveness = xl
    else
        Liveness = xl ∪ yl
    end
    return EscapeInfo(
        x.Analyzed | y.Analyzed,
        x.ReturnEscape | y.ReturnEscape,
        ThrownEscape,
        AliasInfo,
        Liveness,
        )
end
```
-/
def join (h : Heap) (x y : EscapeInfo) : EscapeInfo × Heap :=
  if isTop x || isTop y then (allEscape, h)
  else if isBot x then (y, h)
  else if isBot y then (x, h)
  else
    let thrown : TSet :=
      if x.thrown == .top || y.thrown == .top then .top
      else if x.thrown == .bot then y.thrown
      else if y.thrown == .bot then x.thrown
      else .fresh (IntSet.union x.thrown.elems y.thrown.elems)
    let alias := mergeAliasInfo x.alias y.alias
    let (live, h) :=
      if x.live == .top || y.live == .top then (LRef.top, h)
      else if x.live == .bot then (y.live, h)
      else if y.live == .bot then (x.live, h)
      else h.alloc (IntSet.union (h.get x.live) (h.get y.live))
    (⟨x.analyzed || y.analyzed, x.returnEscape || y.returnEscape, thrown, alias, live⟩, h)

/-! ### Utility constructors -/

/-- `ignore_argescape(x)`: a fresh copy of `Liveness` without `0`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:159
```julia
ignore_argescape(x::EscapeInfo) = EscapeInfo(x; Liveness=delete!(copy(x.Liveness), 0))
```
-/
def ignoreArgescape (h : Heap) (x : EscapeInfo) : EscapeInfo × Heap :=
  let (r, h) := h.alloc ((h.get x.live).erase 0)
  ({ x with live := r }, h)

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:160
```julia
ignore_thrownescapes(x::EscapeInfo) = EscapeInfo(x; ThrownEscape=BOT_THROWN_ESCAPE)
```
-/
def ignoreThrownescapes (x : EscapeInfo) : EscapeInfo := { x with thrown := .bot }

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:161
```julia
ignore_aliasinfo(x::EscapeInfo) = EscapeInfo(x, false)
```
-/
def ignoreAliasinfo (x : EscapeInfo) : EscapeInfo := { x with alias := .bool false }

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:162
```julia
ignore_liveness(x::EscapeInfo) = EscapeInfo(x; Liveness=BOT_LIVENESS)
```
-/
def ignoreLiveness (x : EscapeInfo) : EscapeInfo := { x with live := .bot }

/-! ### Interprocedural summaries -/

/-- `ARG_ALL_ESCAPE`, `ARG_RETURN_ESCAPE`, `ARG_THROWN_ESCAPE` (lines 508-510). -/
def ARG_ALL_ESCAPE : UInt8 := 1
def ARG_RETURN_ESCAPE : UInt8 := 2
def ARG_THROWN_ESCAPE : UInt8 := 4

/-- `ArgEscapeInfo(x)`, as its `escape_bits`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:500-506
```julia
function ArgEscapeInfo(x::EscapeInfo)
    x === ⊤ && return ArgEscapeInfo(ARG_ALL_ESCAPE)
    escape_bits = 0x00
    has_return_escape(x) && (escape_bits |= ARG_RETURN_ESCAPE)
    has_thrown_escape(x) && (escape_bits |= ARG_THROWN_ESCAPE)
    return ArgEscapeInfo(escape_bits)
end
```
-/
def argEscapeInfo (x : EscapeInfo) : UInt8 :=
  if isTop x then ARG_ALL_ESCAPE
  else
    let b : UInt8 := if hasReturnEscape x then ARG_RETURN_ESCAPE else 0
    if hasThrownEscape x then b ||| ARG_THROWN_ESCAPE else b

/-- Julia source: Compiler/src/ssair/EscapeAnalysis.jl:512-515
```julia
has_no_escape(x::ArgEscapeInfo)     = !has_all_escape(x) && !has_return_escape(x) && !has_thrown_escape(x)
has_all_escape(x::ArgEscapeInfo)    = x.escape_bits & ARG_ALL_ESCAPE    ≠ 0
has_return_escape(x::ArgEscapeInfo) = x.escape_bits & ARG_RETURN_ESCAPE ≠ 0
has_thrown_escape(x::ArgEscapeInfo) = x.escape_bits & ARG_THROWN_ESCAPE ≠ 0
```
-/
def aHasAllEscape (b : UInt8) : Bool := b &&& ARG_ALL_ESCAPE != 0
def aHasReturnEscape (b : UInt8) : Bool := b &&& ARG_RETURN_ESCAPE != 0
def aHasThrownEscape (b : UInt8) : Bool := b &&& ARG_THROWN_ESCAPE != 0
def aHasNoEscape (b : UInt8) : Bool := !aHasAllEscape b && !aHasReturnEscape b && !aHasThrownEscape b

/-- `from_interprocedural(argescape, pc)`: allocates the fresh `BitSet(pc)` liveness.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1032-1043
```julia
function from_interprocedural(argescape::ArgEscapeInfo, pc::Int)
    has_all_escape(argescape) && return ⊤
    ThrownEscape = has_thrown_escape(argescape) ? BitSet(pc) : BOT_THROWN_ESCAPE
    # TODO implement interprocedural memory effect-analysis:
    # currently, this essentially disables the entire field analysis–it might be okay from
    # the SROA point of view, since we can't remove the allocation as far as it's passed to
    # a callee anyway, but still we may want some field analysis for e.g. stack allocation
    # or some other IPO optimizations
    AliasInfo = true
    Liveness = BitSet(pc)
    return EscapeInfo(#=Analyzed=#true, #=ReturnEscape=#false, ThrownEscape, AliasInfo, Liveness)
end
```
-/
def fromInterprocedural (h : Heap) (argescape : UInt8) (pc : Int) : EscapeInfo × Heap :=
  if aHasAllEscape argescape then (allEscape, h)
  else
    let thrown : TSet := if aHasThrownEscape argescape then .fresh [pc] else .bot
    let (r, h) := h.alloc [pc]
    (⟨true, false, thrown, .bool true, r⟩, h)

/-! ## The abstracted IR -/

/-- An operand, by the `isa` tests the analysis makes on it. `gref` is a `GlobalRef` or a
`Core.BindingPartition`, `tupleExpr` an `Expr(:tuple, ...)` (only tested as a `foreigncall`
name), `other` anything else (literals, `QuoteNode`s, `MethodInstance`s, ...). -/
inductive Opnd where
  | arg (n : Nat)
  | ssa (n : Nat)
  | gref
  | tupleExpr
  | other
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The callee of a `:call`, by `singleton_type(argextype(args[1], ir))`: an intrinsic, a builtin
(by name, `"other"` for one without an `escape_builtin!` method), or anything else. -/
inductive FKind where
  | intrinsic
  | builtin (name : String)
  | other
  deriving Repr, BEq, Inhabited

/-- What `get_escape_cache` returned for an `:invoke`: a `Bool`, or an `ArgEscapeCache` (its
`argescapes` bits and `argaliases` pairs). -/
inductive Cache where
  | bool (b : Bool)
  | cache (argescapes : Array UInt8) (argaliases : List (Nat × Nat))
  deriving Repr, Inhabited

/-- The type-dependent facts a `:call` statement's handler reads, computed by the pinned
Compiler:

* `modint`: `hasintersect(argextype_widened(args[2], ir), Module)` (getfield);
* `onflds`, `ofidx`: `fieldcount_noerror(typ)` and, when `typ isa DataType`,
  `try_compute_fieldidx(typ, try_compute_field(ir, args[3]))`, for
  `typ = argextype_widened(args[2], ir)` (getfield, setfield!);
* `sfNothrow`: the `setfield!_nothrow` test of lines 1399-1404;
* `condConst`: `cond.val` when `argextype(args[2], ir)` is a `Const` of a `Bool` (ifelse). -/
structure CallInfo where
  fk : FKind
  modint : Bool := false
  onflds : Option Nat := none
  ofidx : Option Nat := none
  sfNothrow : Bool := false
  condConst : Option Bool := none
  deriving Repr, Inhabited

/-- A statement, by the branch of `analyze_escapes` (lines 591-651) it takes.

* `call`, `invoke`, `new` (`:new`, `:splatnew`), `foreigncall`, `foreignglobal`,
  `throwUndefIfNot` (`:throw_undef_if_not`): their handlers. `foreigncall` carries
  `argtypes[i] === Any` for each `argtypes` entry, or `none` when `args[3]` is not a
  `SimpleVector`.
* `gcPreserveEnd`: the `:gc_preserve_begin` arguments, or `none` when one of the
  `@assert`s of `escape_gc_preserve!` fails.
* `conservative`: any other `Expr` head (`add_conservative_changes!`).
* `skip`: the branches that `continue` before the propagation (meta heads, `:leave`,
  `:the_exception`, `:pop_exception`, `:static_parameter`, `:copyast`, `:isdefined`,
  `GotoNode`, `GotoIfNot`, literals, ...).
* `noop`: `:gc_preserve_begin`, which falls through to the propagation.
* `enter`: an `EnterNode`, with the first statement of its catch block when `catch_dest ≠ 0`.
* `ret`, `phi` (`PhiNode` and `PhiCNode`, `none` for an unassigned value), `val` (`PiNode`,
  `UpsilonNode`, `SSAValue`, `Argument`; `none` when `val` is undefined), `globalLoad`
  (`GlobalRef`, `Core.BindingPartition`). -/
inductive Stmt where
  | call (args : Array Opnd) (ci : CallInfo)
  | invoke (args : Array Opnd) (cache : Cache) (mnargs : Nat)
  | new (args : Array Opnd)
  | foreigncall (args : Array Opnd) (argAny : Option (List Bool))
  | foreignglobal (args : Array Opnd)
  | throwUndefIfNot (args : Array Opnd)
  | gcPreserveEnd (beginArgs : Option (Array Opnd))
  | conservative (args : Array Opnd)
  | skip
  | noop
  | enter (leavePc : Option Int)
  | ret (v : Option Opnd)
  | phi (vals : List (Option Opnd))
  | val (v : Option Opnd)
  | globalLoad
  deriving Repr, Inhabited

/-- One instruction: its statement and the facts about `SSAValue(pc)` itself:
`is_identity_free_argtype(argextype(SSAValue(pc), ir))`, `IR_FLAG_NOTHROW`, and
`fieldcount_noerror(argextype_widened(SSAValue(pc), ir))` (read by `escape_new!`). -/
structure Inst where
  stmt : Stmt
  idfree : Bool
  nothrow : Bool
  nflds : Option Nat
  deriving Repr, Inhabited

/-- The analysed `IRCode` (no `new_nodes`), with `nargs` and
`is_identity_free_argtype(ir.argtypes[i])` for each argument. -/
structure IR where
  insts : Array Inst
  nargs : Nat
  argIdfree : Array Bool
  deriving Repr, Inhabited

/-! ## The analysis state -/

/-- `struct EscapeState`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:410-414
```julia
struct EscapeState
    escapes::Vector{EscapeInfo}
    aliasset::AliasSet
    nargs::Int
end
```
-/
structure EscapeState where
  escapes : Array EscapeInfo
  aliasset : IntDisjointSet
  nargs : Nat
  deriving Repr, Inhabited

/-- `EscapeState(nargs, nstmts)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:415-420
```julia
function EscapeState(nargs::Int, nstmts::Int)
    escapes = EscapeInfo[
        1 ≤ i ≤ nargs ? ArgEscape() : ⊥ for i in 1:(nargs+nstmts)]
    aliasset = AliasSet(nargs+nstmts)
    return EscapeState(escapes, aliasset, nargs)
end
```
-/
def EscapeState.new (nargs nstmts : Nat) : EscapeState :=
  ⟨((List.range (nargs + nstmts)).map fun i =>
      if i + 1 ≤ nargs then argEscape else notAnalyzed).toArray,
    IntDisjointSet.new (nargs + nstmts), nargs⟩

/-- `iridx(x, estate)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:443-453
```julia
function iridx(@nospecialize(x), estate::EscapeState)
    if isa(x, Argument)
        xidx = x.n
        @assert 1 ≤ xidx ≤ estate.nargs "invalid Argument"
    elseif isa(x, SSAValue)
        xidx = x.id + estate.nargs
    else
        return nothing
    end
    return xidx
end
```
-/
def iridx (nargs : Nat) : Opnd → JM (Option Nat)
  | .arg n => if 1 ≤ n ∧ n ≤ nargs then pure (some n) else throw "julia:AssertionError"
  | .ssa n => pure (some (n + nargs))
  | _ => pure none

/-- `irval(xidx, estate)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:464-466
```julia
function irval(xidx::Int, estate::EscapeState)
    return xidx > estate.nargs ? SSAValue(xidx-estate.nargs) : Argument(xidx)
end
```
-/
def irval (nargs xidx : Nat) : Opnd := if xidx > nargs then .ssa (xidx - nargs) else .arg xidx

/-- `getaliases(xidx, estate)`: `none` for a singleton set, else every index whose *direct*
parent is the root (after compressing the path from `xidx` only).

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:474-490
```julia
function getaliases(xidx::Int, estate::EscapeState)
    aliasset = estate.aliasset
    root = find_root!(aliasset, xidx)
    if xidx ≠ root || aliasset.ranks[xidx] > 0
        # the size of this alias set containing `key` is larger than 1,
        # collect the entire alias set
        aliases = Int[]
        for aidx in 1:length(aliasset.parents)
            if aliasset.parents[aidx] == root
                push!(aliases, aidx)
            end
        end
        return aliases
    else
        return nothing
    end
end
```
-/
def getaliases (estate : EscapeState) (xidx : Nat) : JM (EscapeState × Option (List Nat)) := do
  let (aliasset, root) ← estate.aliasset.findRoot xidx
  let estate := { estate with aliasset }
  if (xidx : Int) != root || (← aget aliasset.ranks xidx) > 0 then
    let aliases := (List.range aliasset.parents.size).filterMap fun i =>
      if aliasset.parents.getD i 0 == root then some (i + 1) else none
    return (estate, some aliases)
  else
    return (estate, none)

/-- `isaliased(xidx, yidx, estate)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:494-495
```julia
isaliased(xidx::Int, yidx::Int, estate::EscapeState) =
    in_same_set(estate.aliasset, xidx, yidx)
```
-/
def isaliased (estate : EscapeState) (xidx yidx : Nat) : JM (EscapeState × Bool) := do
  let (aliasset, b) ← estate.aliasset.inSameSet xidx yidx
  return ({ estate with aliasset }, b)

/-- `ArgEscapeCache(estate)`: the argument summaries and the aliased argument pairs.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:525-540
```julia
    function ArgEscapeCache(estate::EscapeState)
        nargs = estate.nargs
        argescapes = Vector{ArgEscapeInfo}(undef, nargs)
        argaliases = ArgAliasing[]
        for i = 1:nargs
            info = estate.escapes[i]
            @assert info.AliasInfo === true
            argescapes[i] = ArgEscapeInfo(info)
            for j = (i+1):nargs
                if isaliased(i, j, estate)
                    push!(argaliases, ArgAliasing(i, j))
                end
            end
        end
        return new(argescapes, argaliases)
    end
```
-/
def argEscapeCache (estate : EscapeState) : JM (List UInt8 × List (Nat × Nat)) := do
  let mut estate := estate
  let mut bits : List UInt8 := []
  let mut aliases : List (Nat × Nat) := []
  for i in List.range estate.nargs do
    let info ← aget estate.escapes (i + 1)
    if info.alias != .bool true then throw "julia:AssertionError"
    bits := bits ++ [argEscapeInfo info]
    for j in List.range (estate.nargs - (i + 1)) do
      let (e, b) ← isaliased estate (i + 1) (i + 2 + j)
      estate := e
      if b then aliases := aliases ++ [(i + 1, i + 2 + j)]
  return (bits, aliases)

/-- `EscapeChange`, `LivenessChange` and `AliasChange` (lines 544-559). `ArgAliasChange` is
never constructed. -/
inductive Change where
  | escape (xidx : Nat) (info : EscapeInfo)
  | liveness (xidx : Nat) (livepc : Int)
  | alias (xidx yidx : Nat)
  deriving Repr, Inhabited

/-- `AnalysisState`'s mutable parts (lines 562-568), with the `Liveness` heap. -/
structure AState where
  estate : EscapeState
  changes : Array Change
  heap : Heap
  deriving Repr, Inhabited

abbrev EM := StateT AState JM

def getInfo (xidx : Nat) : EM EscapeInfo := do aget (← get).estate.escapes xidx
def setInfo (xidx : Nat) (v : EscapeInfo) : EM Unit := do
  let s ← get
  let escapes ← aset s.estate.escapes xidx v
  set { s with estate := { s.estate with escapes } }
def joinM (x y : EscapeInfo) : EM EscapeInfo := do
  let s ← get
  let (r, heap) := join s.heap x y
  set { s with heap }
  return r
def allocM (l : IntSet) : EM LRef := do
  let s ← get
  let (r, heap) := s.heap.alloc l
  set { s with heap }
  return r
def pushChange (c : Change) : EM Unit := modify fun s => { s with changes := s.changes.push c }
def pushfirstChange (c : Change) : EM Unit :=
  modify fun s => { s with changes := #[c] ++ s.changes }
def getaliasesM (xidx : Nat) : EM (Option (List Nat)) := do
  let s ← get
  let (estate, r) ← getaliases s.estate xidx
  set { s with estate }
  return r
def isaliasedM (xidx yidx : Nat) : EM Bool := do
  let s ← get
  let (estate, r) ← isaliased s.estate xidx yidx
  set { s with estate }
  return r

/-- `is_identity_free_argtype(argextype(x, ir))` for an operand that `iridx` maps to an index.
For other operands the value is never used (every caller first needs an index). -/
def idfreeOf (ir : IR) : Opnd → JM Bool
  | .arg n => aget ir.argIdfree n
  | .ssa n => do return (← aget ir.insts n).idfree
  | _ => pure true

def isNothrow (ir : IR) (pc : Nat) : JM Bool := do return (← aget ir.insts pc).nothrow

/-! ## Propagation -/

/-- `_propagate_escape_change!(⊔ₑ, estate, xidx, info)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:734-743
```julia
@inline function _propagate_escape_change!(@specialize(op),
    estate::EscapeState, xidx::Int, info::EscapeInfo)
    old = estate.escapes[xidx]
    new = op(old, info)
    if old ≠ new
        estate.escapes[xidx] = new
        return true
    end
    return false
end
```
-/
def propagateOne (xidx : Nat) (info : EscapeInfo) : EM Bool := do
  let old ← getInfo xidx
  let new ← joinM old info
  if !eqE (← get).heap old new then
    setInfo xidx new
    return true
  return false

/-- `propagate_escape_change!(⊔ₑ, estate, change)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:716-732
```julia
@inline propagate_escape_change!(estate::EscapeState, change::EscapeChange) =
    propagate_escape_change!(⊔ₑ, estate, change)

# allows this to work as lattice join as well as lattice meet
@inline function propagate_escape_change!(@specialize(op),
    estate::EscapeState, change::EscapeChange)
    (; xidx, xinfo) = change
    anychanged = _propagate_escape_change!(op, estate, xidx, xinfo)
    # COMBAK is there a more efficient method of escape information equalization on aliasset?
    aliases = getaliases(xidx, estate)
    if aliases !== nothing
        for aidx in aliases
            anychanged |= _propagate_escape_change!(op, estate, aidx, xinfo)
        end
    end
    return anychanged
end
```
-/
def propagateEscapeChange (xidx : Nat) (xinfo : EscapeInfo) : EM Bool := do
  let mut anychanged ← propagateOne xidx xinfo
  match ← getaliasesM xidx with
  | none => pure ()
  | some aliases =>
    for aidx in aliases do
      let c ← propagateOne aidx xinfo
      anychanged := anychanged || c
  return anychanged

/-- `propagate_liveness_change!`: a constant set is copied, any other is mutated in place.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:746-763
```julia
@inline function propagate_liveness_change!(estate::EscapeState, change::LivenessChange)
    (; xidx, livepc) = change
    info = estate.escapes[xidx]
    Liveness = info.Liveness
    Liveness === TOP_LIVENESS && return false
    livepc ∈ Liveness && return false
    if Liveness === BOT_LIVENESS || Liveness === ARG_LIVENESS
        # if this Liveness is a constant, we shouldn't modify it and propagate this change as a new EscapeInfo
        Liveness = copy(Liveness)
        push!(Liveness, livepc)
        estate.escapes[xidx] = EscapeInfo(info; Liveness)
        return true
    else
        # directly modify Liveness property in order to avoid excessive copies
        push!(Liveness, livepc)
        return true
    end
end
```
-/
def propagateLivenessChange (xidx : Nat) (livepc : Int) : EM Bool := do
  let info ← getInfo xidx
  let s ← get
  if info.live == .top then return false
  if (s.heap.get info.live).mem livepc then return false
  if info.live == .bot || info.live == .arg then
    let r ← allocM (IntSet.insert (s.heap.get info.live) livepc)
    setInfo xidx { info with live := r }
    return true
  else
    set { s with heap := s.heap.push info.live livepc }
    return true

/-- `propagate_alias_change!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:765-776
```julia
@inline function propagate_alias_change!(estate::EscapeState, change::AliasChange)
    anychange = false
    (; xidx, yidx) = change
    aliasset = estate.aliasset
    xroot = find_root!(aliasset, xidx)
    yroot = find_root!(aliasset, yidx)
    if xroot ≠ yroot
        union!(aliasset, xroot, yroot)
        return true
    end
    return false
end
```
-/
def propagateAliasChange (xidx yidx : Nat) : EM Bool := do
  let s ← get
  let (a, xroot) ← s.estate.aliasset.findRoot xidx
  let (a, yroot) ← a.findRoot yidx
  if xroot ≠ yroot then
    let (a, _) ← a.union xroot yroot
    set { s with estate := { s.estate with aliasset := a } }
    return true
  set { s with estate := { s.estate with aliasset := a } }
  return false

/-- `propagate_changes!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:701-714
```julia
function propagate_changes!(estate::EscapeState, changes::Changes)
    local anychanged = false
    for change in changes
        if isa(change, EscapeChange)
            anychanged |= propagate_escape_change!(estate, change)
        elseif isa(change, LivenessChange)
            anychanged |= propagate_liveness_change!(estate, change)
        else
            change = change::AliasChange
            anychanged |= propagate_alias_change!(estate, change)
        end
    end
    return anychanged
end
```
-/
def propagateChanges : EM Bool := do
  let mut anychanged := false
  for change in (← get).changes do
    let c ← match change with
      | .escape xidx xinfo => propagateEscapeChange xidx xinfo
      | .liveness xidx livepc => propagateLivenessChange xidx livepc
      | .alias xidx yidx => propagateAliasChange xidx yidx
    anychanged := anychanged || c
  return anychanged

/-! ## Recording changes -/

/-- `add_escape_change!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:778-788
```julia
function add_escape_change!(astate::AnalysisState, @nospecialize(x), xinfo::EscapeInfo,
    force::Bool = false)
    xinfo === ⊥ && return nothing # performance optimization
    xidx = iridx(x, astate.estate)
    if xidx !== nothing
        if force || !is_identity_free_argtype(argextype(x, astate.ir))
            push!(astate.changes, EscapeChange(xidx, xinfo))
        end
    end
    return nothing
end
```
-/
def addEscapeChange (ir : IR) (x : Opnd) (xinfo : EscapeInfo) (force : Bool := false) :
    EM Unit := do
  if isBot xinfo then return
  match ← iridx ir.nargs x with
  | none => pure ()
  | some xidx =>
    if force || !(← idfreeOf ir x) then pushChange (.escape xidx xinfo)

/-- `add_liveness_change!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:790-798
```julia
function add_liveness_change!(astate::AnalysisState, @nospecialize(x), livepc::Int)
    xidx = iridx(x, astate.estate)
    if xidx !== nothing
        if !is_identity_free_argtype(argextype(x, astate.ir))
            push!(astate.changes, LivenessChange(xidx, livepc))
        end
    end
    return nothing
end
```
-/
def addLivenessChange (ir : IR) (x : Opnd) (livepc : Int) : EM Unit := do
  match ← iridx ir.nargs x with
  | none => pure ()
  | some xidx => if !(← idfreeOf ir x) then pushChange (.liveness xidx livepc)

/-- `add_alias_change!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:800-819
```julia
function add_alias_change!(astate::AnalysisState, @nospecialize(x), @nospecialize(y))
    if isa(x, GlobalRef) || isa(x, Core.BindingPartition)
        return add_escape_change!(astate, y, ⊤)
    elseif isa(y, GlobalRef) || isa(y, Core.BindingPartition)
        return add_escape_change!(astate, x, ⊤)
    end
    estate = astate.estate
    xidx = iridx(x, estate)
    yidx = iridx(y, estate)
    if xidx !== nothing && yidx !== nothing
        if !isaliased(xidx, yidx, astate.estate)
            pushfirst!(astate.changes, AliasChange(xidx, yidx))
        end
        # add new escape change here so that it's shared among the expanded `aliasset` in `propagate_escape_change!`
        xinfo = estate.escapes[xidx]
        yinfo = estate.escapes[yidx]
        add_escape_change!(astate, x, xinfo ⊔ₑ yinfo, #=force=#true)
    end
    return nothing
end
```
-/
def addAliasChange (ir : IR) (x y : Opnd) : EM Unit := do
  if x == .gref then
    addEscapeChange ir y allEscape
    return
  if y == .gref then
    addEscapeChange ir x allEscape
    return
  let xidx ← iridx ir.nargs x
  let yidx ← iridx ir.nargs y
  match xidx, yidx with
  | some xi, some yi =>
    if !(← isaliasedM xi yi) then pushfirstChange (.alias xi yi)
    let xinfo ← getInfo xi
    let yinfo ← getInfo yi
    addEscapeChange ir x (← joinM xinfo yinfo) true
  | _, _ => pure ()

/-- `add_alias_escapes!`, visiting `ainfo` in insertion order.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:828-835
```julia
function add_alias_escapes!(astate::AnalysisState, @nospecialize(v), ainfo::AInfo)
    estate = astate.estate
    for x in ainfo
        isa(x, LocalUse) || continue # ignore def
        x = SSAValue(x.idx) # obviously this won't be true once we implement interprocedural AliasInfo
        add_alias_change!(astate, v, x)
    end
end
```
-/
def addAliasEscapes (ir : IR) (v : Opnd) (ainfo : AInfo) : EM Unit := do
  for k in ainfo do
    match AElt.ofKey k with
    | .use i => addAliasChange ir v (.ssa i.toNat)
    | .def_ _ => pure ()

/-- `add_thrown_escapes!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:837-843
```julia
function add_thrown_escapes!(astate::AnalysisState, pc::Int, args::Vector{Any},
    first_idx::Int = 1, last_idx::Int = length(args))
    info = ThrownEscape(pc)
    for i in first_idx:last_idx
        add_escape_change!(astate, args[i], info)
    end
end
```
-/
def addThrownEscapes (ir : IR) (pc : Nat) (args : Array Opnd) (firstIdx : Nat := 1) : EM Unit := do
  let info := thrownEscapeAt pc
  for i in irange firstIdx args.size do
    addEscapeChange ir (← aget args i) info

/-- `add_liveness_changes!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:845-851
```julia
function add_liveness_changes!(astate::AnalysisState, pc::Int, args::Vector{Any},
    first_idx::Int = 1, last_idx::Int = length(args))
    for i in first_idx:last_idx
        arg = args[i]
        add_liveness_change!(astate, arg, pc)
    end
end
```
-/
def addLivenessChanges (ir : IR) (pc : Nat) (args : Array Opnd) (firstIdx : Nat := 1) :
    EM Unit := do
  for i in irange firstIdx args.size do
    addLivenessChange ir (← aget args i) pc

/-- `add_fallback_changes!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:853-861
```julia
function add_fallback_changes!(astate::AnalysisState, pc::Int, args::Vector{Any},
    first_idx::Int = 1, last_idx::Int = length(args))
    info = ThrownEscape(pc)
    for i in first_idx:last_idx
        arg = args[i]
        add_escape_change!(astate, arg, info)
        add_liveness_change!(astate, arg, pc)
    end
end
```
-/
def addFallbackChanges (ir : IR) (pc : Nat) (args : Array Opnd) (firstIdx : Nat := 1) :
    EM Unit := do
  let info := thrownEscapeAt pc
  for i in irange firstIdx args.size do
    let arg ← aget args i
    addEscapeChange ir arg info
    addLivenessChange ir arg pc

/-- `add_conservative_changes!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:863-870
```julia
function add_conservative_changes!(astate::AnalysisState, pc::Int, args::Vector{Any},
    first_idx::Int = 1, last_idx::Int = length(args))
    for i in first_idx:last_idx
        add_escape_change!(astate, args[i], ⊤)
    end
    add_escape_change!(astate, SSAValue(pc), ⊤) # it may return GlobalRef etc.
    return nothing
end
```
-/
def addConservativeChanges (ir : IR) (pc : Nat) (args : Array Opnd) (firstIdx : Nat := 1) :
    EM Unit := do
  for i in irange firstIdx args.size do
    addEscapeChange ir (← aget args i) allEscape
  addEscapeChange ir (.ssa pc) allEscape

/-- `escape_edges!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:872-880
```julia
function escape_edges!(astate::AnalysisState, pc::Int, edges::Vector{Any})
    ret = SSAValue(pc)
    for i in 1:length(edges)
        if isassigned(edges, i)
            v = edges[i]
            add_alias_change!(astate, ret, v)
        end
    end
end
```
-/
def escapeEdges (ir : IR) (pc : Nat) (edges : List (Option Opnd)) : EM Unit := do
  for e in edges do
    match e with
    | some v => addAliasChange ir (.ssa pc) v
    | none => pure ()

/-- `escape_val!` (and `escape_val_ifdefined!` once `val` is defined).

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:882-891
```julia
function escape_val_ifdefined!(astate::AnalysisState, pc::Int, x)
    if isdefined(x, :val)
        escape_val!(astate, pc, x.val)
    end
end

function escape_val!(astate::AnalysisState, pc::Int, @nospecialize(val))
    ret = SSAValue(pc)
    add_alias_change!(astate, ret, val)
end
```
-/
def escapeVal (ir : IR) (pc : Nat) (v : Opnd) : EM Unit := addAliasChange ir (.ssa pc) v

/-- `escape_unanalyzable_obj!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:893-897
```julia
function escape_unanalyzable_obj!(astate::AnalysisState, @nospecialize(obj), objinfo::EscapeInfo)
    objinfo = EscapeInfo(objinfo, true)
    add_escape_change!(astate, obj, objinfo)
    return objinfo
end
```
-/
def escapeUnanalyzableObj (ir : IR) (obj : Opnd) (objinfo : EscapeInfo) : EM EscapeInfo := do
  let objinfo := { objinfo with alias := .bool true }
  addEscapeChange ir obj objinfo
  return objinfo

/-- `escape_exception!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:942-964
```julia
function escape_exception!(astate::AnalysisState, tryregions::Vector{UnitRange{Int}})
    estate = astate.estate
    # NOTE if `:the_exception` is the only way to access the exception, we can do:
    # exc = SSAValue(pc)
    # excinfo = estate[exc]
    # TODO? set up a special effect bit that checks the existence of `rethrow` and `current_exceptions` and use it here
    excinfo = ⊤
    escapes = estate.escapes
    for i in 1:length(escapes)
        x = escapes[i]
        xt = x.ThrownEscape
        xt === TOP_THROWN_ESCAPE && @goto propagate_exception_escape # fast path
        for pc in xt
            for region in tryregions
                pc ∈ region && @goto propagate_exception_escape # early break because of AllEscape
            end
        end
        continue
        @label propagate_exception_escape
        xval = irval(i, estate)
        add_escape_change!(astate, xval, excinfo)
    end
end
```
-/
def escapeException (ir : IR) (tryregions : List (Int × Int)) : EM Unit := do
  let escapes := (← get).estate.escapes
  for i in List.range escapes.size do
    let x := escapes.getD i default
    let hit := x.thrown == .top ||
      x.thrown.elems.any fun pc => tryregions.any fun (lo, hi) => lo ≤ pc && pc ≤ hi
    if hit then addEscapeChange ir (irval ir.nargs (i + 1)) allEscape

/-! ## Statement handlers -/

/-- `escape_invoke!`, with the result of `get_escape_cache` and `method.nargs` precomputed.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:967-1024
```julia
function escape_invoke!(astate::AnalysisState, pc::Int, args::Vector{Any})
    codeinst = first(args)
    if codeinst isa MethodInstance
        mi = codeinst
    else
        mi = (codeinst::CodeInstance).def
    end
    first_idx, last_idx = 2, length(args)
    add_liveness_changes!(astate, pc, args, first_idx, last_idx)
    # TODO inspect `astate.ir.stmts[pc][:info]` and use const-prop'ed `InferenceResult` if available
    cache = astate.get_escape_cache(codeinst)
    ret = SSAValue(pc)
    if cache isa Bool
        if cache
            # This method call is very simple and has good effects, so there's no need to
            # escape its arguments. However, since the arguments might be returned, we need
            # to consider the possibility of aliasing between them and the return value.
            for argidx = first_idx:last_idx
                arg = args[argidx]
                if arg isa GlobalRef || arg isa Core.BindingPartition
                    continue # :effect_free guarantees that nothing escapes to the global scope
                end
                if !is_identity_free_argtype(argextype(arg, astate.ir))
                    add_alias_change!(astate, ret, arg)
                end
            end
            return nothing
        else
            return add_conservative_changes!(astate, pc, args, 2)
        end
    end
    cache = cache::ArgEscapeCache
    retinfo = astate.estate[ret] # escape information imposed on the call statement
    method = mi.def::Method
    nargs = Int(method.nargs)
    for (i, argidx) in enumerate(first_idx:last_idx)
        arg = args[argidx]
        if i > nargs
            # handle isva signature
            # COMBAK will this be invalid once we take alias information into account?
            i = nargs
        end
        argescape = cache.argescapes[i]
        info = from_interprocedural(argescape, pc)
        # propagate the escape information imposed on this call argument by the callee
        add_escape_change!(astate, arg, info)
        if has_return_escape(argescape)
            # if this argument can be "returned", we should also account for possible
            # aliasing between this argument and the returned value
            add_alias_change!(astate, ret, arg)
        end
    end
    for (; aidx, bidx) in cache.argaliases
        add_alias_change!(astate, args[aidx+(first_idx-1)], args[bidx+(first_idx-1)])
    end
    # we should disable the alias analysis on this newly introduced object
    add_escape_change!(astate, ret, EscapeInfo(retinfo, true))
end
```
-/
def escapeInvoke (ir : IR) (pc : Nat) (args : Array Opnd) (cache : Cache) (mnargs : Nat) :
    EM Unit := do
  addLivenessChanges ir pc args 2
  let ret := Opnd.ssa pc
  match cache with
  | .bool true =>
    for argidx in irange 2 args.size do
      let arg ← aget args argidx
      if arg == .gref then continue
      if !(← idfreeOf ir arg) then addAliasChange ir ret arg
  | .bool false => addConservativeChanges ir pc args 2
  | .cache argescapes argaliases =>
    let retinfo ← getInfo (pc + ir.nargs)
    let mut i : Nat := 0
    for argidx in irange 2 args.size do
      i := i + 1
      let arg ← aget args argidx
      let ii := if i > mnargs then mnargs else i
      let argescape ← aget argescapes ii
      let s ← get
      let (info, heap) := fromInterprocedural s.heap argescape pc
      set { s with heap }
      addEscapeChange ir arg info
      if aHasReturnEscape argescape then addAliasChange ir ret arg
    for (aidx, bidx) in argaliases do
      addAliasChange ir (← aget args (aidx + 1)) (← aget args (bidx + 1))
    addEscapeChange ir ret { retinfo with alias := .bool true }

/-- `escape_foreignglobal!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1047-1060
```julia
function escape_foreignglobal!(astate::AnalysisState, pc::Int, args::Vector{Any})
    nargs = length(args)
    if nargs != 1
        # invalid foreignglobal, no escape
        return
    end
    name = args[1]
    nothrow = is_nothrow(astate.ir, pc)
    name_info = nothrow ? ⊥ : ThrownEscape(pc)
    if !isexpr(name, :tuple)
        add_escape_change!(astate, name, name_info)
        add_liveness_change!(astate, name, pc)
    end
end
```
-/
def escapeForeignglobal (ir : IR) (pc : Nat) (args : Array Opnd) : EM Unit := do
  if args.size != 1 then return
  let name ← aget args 1
  let nameInfo := if ← isNothrow ir pc then notAnalyzed else thrownEscapeAt pc
  if name != .tupleExpr then
    addEscapeChange ir name nameInfo
    addLivenessChange ir name pc

/-- `escape_foreigncall!`. The last loop starts at `5+nargs`, one before the `gc_roots`; that
slot is the last call argument (or `args[5]`, the calling convention, when there are none).

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1064-1097
```julia
function escape_foreigncall!(astate::AnalysisState, pc::Int, args::Vector{Any})
    nargs = length(args)
    if nargs < 6
        # invalid foreigncall, just escape everything
        add_conservative_changes!(astate, pc, args)
        return
    end
    argtypes = args[3]::SimpleVector
    nargs = length(argtypes)
    name = args[1]
    # NOTE array allocations might have been proven as nothrow (https://github.com/JuliaLang/julia/pull/43565)
    nothrow = is_nothrow(astate.ir, pc)
    name_info = nothrow ? ⊥ : ThrownEscape(pc)
    if !isexpr(name, :tuple)
        add_escape_change!(astate, name, name_info)
        add_liveness_change!(astate, name, pc)
    end
    for i = 1:nargs
        # we should escape this argument if it is directly called,
        # otherwise just impose ThrownEscape if not nothrow
        if argtypes[i] === Any
            arg_info = ⊤
        else
            arg_info = nothrow ? ⊥ : ThrownEscape(pc)
        end
        add_escape_change!(astate, args[5+i], arg_info)
        add_liveness_change!(astate, args[5+i], pc)
    end
    for i = (5+nargs):length(args)
        arg = args[i]
        add_escape_change!(astate, arg, ⊥)
        add_liveness_change!(astate, arg, pc)
    end
end
```
-/
def escapeForeigncall (ir : IR) (pc : Nat) (args : Array Opnd) (argAny : Option (List Bool)) :
    EM Unit := do
  if args.size < 6 then
    addConservativeChanges ir pc args
    return
  let some argtypes := argAny | throw "julia:TypeError"
  let nargs := argtypes.length
  let name ← aget args 1
  let nothrow ← isNothrow ir pc
  let nameInfo := if nothrow then notAnalyzed else thrownEscapeAt pc
  if name != .tupleExpr then
    addEscapeChange ir name nameInfo
    addLivenessChange ir name pc
  for i in List.range nargs do
    let argInfo := if argtypes.getD i false then allEscape
      else if nothrow then notAnalyzed else thrownEscapeAt pc
    addEscapeChange ir (← aget args (6 + i)) argInfo
    addLivenessChange ir (← aget args (6 + i)) pc
  for i in irange (5 + nargs) args.size do
    let arg ← aget args i
    addEscapeChange ir arg notAnalyzed
    addLivenessChange ir arg pc

/-- `escape_gc_preserve!`, with its three `@assert`s folded into `beginArgs = none`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1099-1108
```julia
function escape_gc_preserve!(astate::AnalysisState, pc::Int, args::Vector{Any})
    @assert length(args) == 1 "invalid :gc_preserve_end"
    val = args[1]
    @assert val isa SSAValue "invalid :gc_preserve_end"
    beginstmt = astate.ir[val][:stmt]
    @assert isexpr(beginstmt, :gc_preserve_begin) "invalid :gc_preserve_end"
    beginargs = beginstmt.args
    # COMBAK we might need to add liveness for all statements from `:gc_preserve_begin` to `:gc_preserve_end`
    add_liveness_changes!(astate, pc, beginargs)
end
```
-/
def escapeGcPreserve (ir : IR) (pc : Nat) (beginArgs : Option (Array Opnd)) : EM Unit := do
  let some beginargs := beginArgs | throw "julia:AssertionError"
  addLivenessChanges ir pc beginargs

/-- `escape_new!` (also the `tuple` handler). `nflds` is
`fieldcount_noerror(argextype_widened(SSAValue(pc), ir))`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1177-1242
```julia
function escape_new!(astate::AnalysisState, pc::Int, args::Vector{Any})
    obj = SSAValue(pc)
    objinfo = astate.estate[obj]
    AliasInfo = objinfo.AliasInfo
    nargs = length(args)
    if isa(AliasInfo, Bool)
        AliasInfo && @goto conservative_propagation
        # AliasInfo of this object hasn't been analyzed yet: set AliasInfo now
        typ = argextype_widened(obj, astate.ir)
        nflds = fieldcount_noerror(typ)
        if nflds === nothing
            AliasInfo = Unindexable()
            @goto escape_unindexable_def
        else
            AliasInfo = IndexableFields(nflds)
            @goto escape_indexable_def
        end
    elseif isa(AliasInfo, IndexableFields)
        AliasInfo = copy(AliasInfo)
        @label escape_indexable_def
        # fields are known precisely: propagate escape information imposed on recorded possibilities to the exact field values
        infos = AliasInfo.infos
        nf = length(infos)
        objinfo′ = ignore_aliasinfo(objinfo)
        for i in 2:nargs
            i-1 > nf && break # may happen when e.g. ϕ-node merges values with different types
            arg = args[i]
            add_alias_escapes!(astate, arg, infos[i-1])
            push!(infos[i-1], LocalDef(pc))
            # propagate the escape information of this object ignoring field information
            add_escape_change!(astate, arg, objinfo′)
            add_liveness_change!(astate, arg, pc)
        end
        add_escape_change!(astate, obj, EscapeInfo(objinfo, AliasInfo)) # update with new AliasInfo
    elseif isa(AliasInfo, Unindexable)
        AliasInfo = copy(AliasInfo)
        @label escape_unindexable_def
        # fields are known partially: propagate escape information imposed on recorded possibilities to all field values
        info = AliasInfo.info
        objinfo′ = ignore_aliasinfo(objinfo)
        for i in 2:nargs
            arg = args[i]
            add_alias_escapes!(astate, arg, info)
            push!(info, LocalDef(pc))
            # propagate the escape information of this object ignoring field information
            add_escape_change!(astate, arg, objinfo′)
            add_liveness_change!(astate, arg, pc)
        end
        add_escape_change!(astate, obj, EscapeInfo(objinfo, AliasInfo)) # update with new AliasInfo
    else
        # this object has been used as array, but it is allocated as struct here (i.e. should throw)
        # update obj's field information and just handle this case conservatively
        objinfo = escape_unanalyzable_obj!(astate, obj, objinfo)
        @label conservative_propagation
        # the fields couldn't be analyzed precisely: propagate the entire escape information
        # of this object to all its fields as the most conservative propagation
        for i in 2:nargs
            arg = args[i]
            add_escape_change!(astate, arg, objinfo)
            add_liveness_change!(astate, arg, pc)
        end
    end
    if !is_nothrow(astate.ir, pc)
        add_thrown_escapes!(astate, pc, args)
    end
end
```
-/
def escapeNew (ir : IR) (pc : Nat) (args : Array Opnd) : EM Unit := do
  let obj := Opnd.ssa pc
  let objinfo ← getInfo (pc + ir.nargs)
  let nargs := args.size
  let indexableDef (infos : List AInfo) : EM Unit := do
    let mut infos := infos
    let nf := infos.length
    let objinfo' := ignoreAliasinfo objinfo
    for i in irange 2 nargs do
      if i - 1 > nf then break
      let arg ← aget args i
      let k := (i - 2).toNat
      addAliasEscapes ir arg (infos.getD k [])
      infos := infos.set k (AInfo.push (infos.getD k []) (AElt.def_ pc).key)
      addEscapeChange ir arg objinfo'
      addLivenessChange ir arg pc
    addEscapeChange ir obj { objinfo with alias := .indexable infos }
  let unindexableDef (info : AInfo) : EM Unit := do
    let mut info := info
    let objinfo' := ignoreAliasinfo objinfo
    for i in irange 2 nargs do
      let arg ← aget args i
      addAliasEscapes ir arg info
      info := AInfo.push info (AElt.def_ pc).key
      addEscapeChange ir arg objinfo'
      addLivenessChange ir arg pc
    addEscapeChange ir obj { objinfo with alias := .unindexable info }
  let conservative (objinfo : EscapeInfo) : EM Unit := do
    for i in irange 2 nargs do
      let arg ← aget args i
      addEscapeChange ir arg objinfo
      addLivenessChange ir arg pc
  match objinfo.alias with
  | .bool true => conservative objinfo
  | .bool false =>
    match (← aget ir.insts pc).nflds with
    | none => unindexableDef []
    | some nflds => indexableDef (List.replicate nflds [])
  | .indexable infos => indexableDef infos
  | .unindexable info => unindexableDef info
  if !(← isNothrow ir pc) then addThrownEscapes ir pc args

/-- `analyze_fields`: `(Unindexable(), 0)` or `(IndexableFields(nflds), fidx)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1249-1264
```julia
function analyze_fields(ir::IRCode, @nospecialize(typ), @nospecialize(fld))
    nflds = fieldcount_noerror(typ)
    if nflds === nothing
        return Unindexable(), 0
    end
    if isa(typ, DataType)
        fldval = try_compute_field(ir, fld)
        fidx = try_compute_fieldidx(typ, fldval)
    else
        fidx = nothing
    end
    if fidx === nothing
        return Unindexable(), 0
    end
    return IndexableFields(nflds), fidx
end
```
-/
def analyzeFields (nflds fidx : Option Nat) : AliasInfo × Nat :=
  match nflds, fidx with
  | some n, some f => (.indexable (List.replicate n []), f)
  | _, _ => (.unindexable [], 0)

/-- `reanalyze_fields`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1266-1289
```julia
function reanalyze_fields(AliasInfo::IndexableFields, ir::IRCode, @nospecialize(typ), @nospecialize(fld))
    nflds = fieldcount_noerror(typ)
    if nflds === nothing
        return merge_to_unindexable(AliasInfo), 0
    end
    if isa(typ, DataType)
        fldval = try_compute_field(ir, fld)
        fidx = try_compute_fieldidx(typ, fldval)
    else
        fidx = nothing
    end
    if fidx === nothing
        return merge_to_unindexable(AliasInfo), 0
    end
    AliasInfo = copy(AliasInfo)
    infos = AliasInfo.infos
    ninfos = length(infos)
    if nflds > ninfos
        for _ in 1:(nflds-ninfos)
            push!(infos, AInfo())
        end
    end
    return AliasInfo, fidx
end
```
-/
def reanalyzeFields (infos : List AInfo) (nflds fidx : Option Nat) : AliasInfo × Nat :=
  match nflds, fidx with
  | some n, some f =>
    (.indexable (if n > infos.length then infos ++ List.replicate (n - infos.length) [] else infos), f)
  | _, _ => (.unindexable (mergeToUnindexable [] infos), 0)

/-- `escape_builtin!(::typeof(getfield), ...)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1291-1337
```julia
function escape_builtin!(::typeof(getfield), astate::AnalysisState, pc::Int, args::Vector{Any})
    length(args) ≥ 3 || return false
    ir, estate = astate.ir, astate.estate
    obj = args[2]
    typ = argextype_widened(obj, ir)
    if hasintersect(typ, Module) # global load
        add_escape_change!(astate, SSAValue(pc), ⊤)
    end
    if isa(obj, SSAValue) || isa(obj, Argument)
        objinfo = estate[obj]
    else
        # unanalyzable object, so the return value is also unanalyzable
        add_escape_change!(astate, SSAValue(pc), ⊤)
        return false
    end
    AliasInfo = objinfo.AliasInfo
    if isa(AliasInfo, Bool)
        AliasInfo && @goto conservative_propagation
        # AliasInfo of this object hasn't been analyzed yet: set AliasInfo now
        AliasInfo, fidx = analyze_fields(ir, typ, args[3])
        if isa(AliasInfo, IndexableFields)
            @goto record_indexable_use
        else
            @goto record_unindexable_use
        end
    elseif isa(AliasInfo, IndexableFields)
        AliasInfo, fidx = reanalyze_fields(AliasInfo, ir, typ, args[3])
        isa(AliasInfo, Unindexable) && @goto record_unindexable_use
        @label record_indexable_use
        push!(AliasInfo.infos[fidx], LocalUse(pc))
        add_escape_change!(astate, obj, EscapeInfo(objinfo, AliasInfo)) # update with new AliasInfo
    elseif isa(AliasInfo, Unindexable)
        AliasInfo = copy(AliasInfo)
        @label record_unindexable_use
        push!(AliasInfo.info, LocalUse(pc))
        add_escape_change!(astate, obj, EscapeInfo(objinfo, AliasInfo)) # update with new AliasInfo
    else
        # this object has been used as array, but it is used as struct here (i.e. should throw)
        # update obj's field information and just handle this case conservatively
        objinfo = escape_unanalyzable_obj!(astate, obj, objinfo)
        @label conservative_propagation
        # at the extreme case, a field of `obj` may point to `obj` itself
        # so add the alias change here as the most conservative propagation
        add_alias_change!(astate, obj, SSAValue(pc))
    end
    return false
end
```
-/
def escapeGetfield (ir : IR) (pc : Nat) (args : Array Opnd) (ci : CallInfo) : EM Bool := do
  if args.size < 3 then return false
  let obj ← aget args 2
  if ci.modint then addEscapeChange ir (.ssa pc) allEscape
  let analyzable := match obj with | .ssa _ | .arg _ => true | _ => false
  let some xidx ← (if analyzable then iridx ir.nargs obj else pure none : JM (Option Nat))
    | do
      addEscapeChange ir (.ssa pc) allEscape
      return false
  let objinfo ← getInfo xidx
  let recordIndexable (infos : List AInfo) (fidx : Nat) : EM Unit := do
    let cur ← aget infos.toArray fidx
    let infos := infos.set (fidx - 1) (AInfo.push cur (AElt.use pc).key)
    addEscapeChange ir obj { objinfo with alias := .indexable infos }
  let recordUnindexable (info : AInfo) : EM Unit :=
    addEscapeChange ir obj { objinfo with alias := .unindexable (AInfo.push info (AElt.use pc).key) }
  let dispatch : AliasInfo × Nat → EM Unit := fun
    | (.indexable infos, fidx) => recordIndexable infos fidx
    | (.unindexable info, _) => recordUnindexable info
    | _ => pure ()
  match objinfo.alias with
  | .bool true => addAliasChange ir obj (.ssa pc)
  | .bool false => dispatch (analyzeFields ci.onflds ci.ofidx)
  | .indexable infos => dispatch (reanalyzeFields infos ci.onflds ci.ofidx)
  | .unindexable info => recordUnindexable info
  return false

/-- `escape_builtin!(::typeof(setfield!), ...)`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1339-1409
```julia
function escape_builtin!(::typeof(setfield!), astate::AnalysisState, pc::Int, args::Vector{Any})
    length(args) ≥ 4 || return false
    ir, estate = astate.ir, astate.estate
    obj = args[2]
    val = args[4]
    if isa(obj, SSAValue) || isa(obj, Argument)
        objinfo = estate[obj]
    else
        # unanalyzable object (e.g. obj::GlobalRef):
        # escape field value conservatively. Force the change so it applies even to an
        # identity-free value (e.g. a `String` stored into a global): the value genuinely
        # escapes to global scope, matching the aliasing path taken when `obj` is an SSA value.
        add_escape_change!(astate, val, ⊤, #=force=#true)
        @goto add_thrown_escapes
    end
    AliasInfo = objinfo.AliasInfo
    if isa(AliasInfo, Bool)
        AliasInfo && @goto conservative_propagation
        # AliasInfo of this object hasn't been analyzed yet: set AliasInfo now
        typ = argextype_widened(obj, ir)
        AliasInfo, fidx = analyze_fields(ir, typ, args[3])
        if isa(AliasInfo, IndexableFields)
            @goto escape_indexable_def
        else
            @goto escape_unindexable_def
        end
    elseif isa(AliasInfo, IndexableFields)
        typ = argextype_widened(obj, ir)
        AliasInfo, fidx = reanalyze_fields(AliasInfo, ir, typ, args[3])
        isa(AliasInfo, Unindexable) && @goto escape_unindexable_def
        @label escape_indexable_def
        add_alias_escapes!(astate, val, AliasInfo.infos[fidx])
        push!(AliasInfo.infos[fidx], LocalDef(pc))
        objinfo = EscapeInfo(objinfo, AliasInfo)
        add_escape_change!(astate, obj, objinfo) # update with new AliasInfo
        # propagate the escape information of this object ignoring field information
        add_escape_change!(astate, val, ignore_aliasinfo(objinfo))
    elseif isa(AliasInfo, Unindexable)
        AliasInfo = copy(AliasInfo)
        @label escape_unindexable_def
        add_alias_escapes!(astate, val, AliasInfo.info)
        push!(AliasInfo.info, LocalDef(pc))
        objinfo = EscapeInfo(objinfo, AliasInfo)
        add_escape_change!(astate, obj, objinfo) # update with new AliasInfo
        # propagate the escape information of this object ignoring field information
        add_escape_change!(astate, val, ignore_aliasinfo(objinfo))
    else
        # this object has been used as array, but it is used as struct here (i.e. should throw)
        # update obj's field information and just handle this case conservatively
        objinfo = escape_unanalyzable_obj!(astate, obj, objinfo)
        @label conservative_propagation
        # the field couldn't be analyzed: alias this object to the value being assigned
        # as the most conservative propagation (as required for ArgAliasing)
        add_alias_change!(astate, val, obj)
    end
    # also propagate escape information imposed on the return value of this `setfield!`
    ssainfo = estate[SSAValue(pc)]
    add_escape_change!(astate, val, ssainfo)
    # compute the throwness of this setfield! call here since builtin_nothrow doesn't account for that
    @label add_thrown_escapes
    if length(args) == 4 && setfield!_nothrow(astate.𝕃ₒ,
        argextype(args[2], ir), argextype(args[3], ir), argextype(args[4], ir))
        return true
    elseif length(args) == 3 && setfield!_nothrow(astate.𝕃ₒ,
        argextype(args[2], ir), argextype(args[3], ir))
        return true
    else
        add_thrown_escapes!(astate, pc, args, 2)
        return true
    end
end
```
-/
def escapeSetfield (ir : IR) (pc : Nat) (args : Array Opnd) (ci : CallInfo) : EM Bool := do
  if args.size < 4 then return false
  let obj ← aget args 2
  let val ← aget args 4
  let thrownTail : EM Bool := do
    if !ci.sfNothrow then addThrownEscapes ir pc args 2
    return true
  let analyzable := match obj with | .ssa _ | .arg _ => true | _ => false
  let some xidx ← (if analyzable then iridx ir.nargs obj else pure none : JM (Option Nat))
    | do
      addEscapeChange ir val allEscape true
      thrownTail
  let objinfo ← getInfo xidx
  let indexableDef (infos : List AInfo) (fidx : Nat) : EM Unit := do
    let cur ← aget infos.toArray fidx
    addAliasEscapes ir val cur
    let infos := infos.set (fidx - 1) (AInfo.push cur (AElt.def_ pc).key)
    let objinfo := { objinfo with alias := .indexable infos }
    addEscapeChange ir obj objinfo
    addEscapeChange ir val (ignoreAliasinfo objinfo)
  let unindexableDef (info : AInfo) : EM Unit := do
    addAliasEscapes ir val info
    let objinfo := { objinfo with alias := .unindexable (AInfo.push info (AElt.def_ pc).key) }
    addEscapeChange ir obj objinfo
    addEscapeChange ir val (ignoreAliasinfo objinfo)
  let dispatch : AliasInfo × Nat → EM Unit := fun
    | (.indexable infos, fidx) => indexableDef infos fidx
    | (.unindexable info, _) => unindexableDef info
    | _ => pure ()
  match objinfo.alias with
  | .bool true => addAliasChange ir val obj
  | .bool false => dispatch (analyzeFields ci.onflds ci.ofidx)
  | .indexable infos => dispatch (reanalyzeFields infos ci.onflds ci.ofidx)
  | .unindexable info => unindexableDef info
  let ssainfo ← getInfo (pc + ir.nargs)
  addEscapeChange ir val ssainfo
  thrownTail

/-- The `escape_builtin!` methods: `none` for `missing` (no method), else the returned `Bool`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1138-1175, 1244-1247, 1411-1417
```julia
escape_builtin!(@nospecialize(f), _...) = missing

# safe builtins
escape_builtin!(::typeof(isa), _...) = false
escape_builtin!(::typeof(typeof), _...) = false
escape_builtin!(::typeof(sizeof), _...) = false
escape_builtin!(::typeof(===), _...) = false
escape_builtin!(::typeof(Core.donotdelete), _...) = false
# not really safe, but `ThrownEscape` will be imposed later
escape_builtin!(::typeof(isdefined), _...) = false
escape_builtin!(::typeof(throw), _...) = false
escape_builtin!(::typeof(Core.throw_methoderror), _...) = false

function escape_builtin!(::typeof(ifelse), astate::AnalysisState, pc::Int, args::Vector{Any})
    length(args) == 4 || return false
    f, cond, th, el = args
    ret = SSAValue(pc)
    condt = argextype(cond, astate.ir)
    if isa(condt, Const) && (cond = condt.val; isa(cond, Bool))
        if cond
            add_alias_change!(astate, th, ret)
        else
            add_alias_change!(astate, el, ret)
        end
    else
        add_alias_change!(astate, th, ret)
        add_alias_change!(astate, el, ret)
    end
    return false
end

function escape_builtin!(::typeof(typeassert), astate::AnalysisState, pc::Int, args::Vector{Any})
    length(args) == 3 || return false
    f, obj, typ = args
    ret = SSAValue(pc)
    add_alias_change!(astate, ret, obj)
    return false
end

function escape_builtin!(::typeof(tuple), astate::AnalysisState, pc::Int, args::Vector{Any})
    escape_new!(astate, pc, args)
    return false
end

function escape_builtin!(::typeof(Core.finalizer), astate::AnalysisState, pc::Int, args::Vector{Any})
    if length(args) ≥ 3
        obj = args[3]
        add_liveness_change!(astate, obj, pc) # TODO setup a proper FinalizerEscape?
    end
    return false
end
```
-/
def escapeBuiltin (ir : IR) (name : String) (pc : Nat) (args : Array Opnd) (ci : CallInfo) :
    EM (Option Bool) := do
  match name with
  | "isa" | "typeof" | "sizeof" | "===" | "donotdelete" | "isdefined" | "throw"
  | "throw_methoderror" => return some false
  | "ifelse" =>
    if args.size != 4 then return some false
    let th ← aget args 3
    let el ← aget args 4
    let ret := Opnd.ssa pc
    match ci.condConst with
    | some true => addAliasChange ir th ret
    | some false => addAliasChange ir el ret
    | none =>
      addAliasChange ir th ret
      addAliasChange ir el ret
    return some false
  | "typeassert" =>
    if args.size != 3 then return some false
    addAliasChange ir (.ssa pc) (← aget args 2)
    return some false
  | "tuple" =>
    escapeNew ir pc args
    return some false
  | "getfield" => return some (← escapeGetfield ir pc args ci)
  | "setfield!" => return some (← escapeSetfield ir pc args ci)
  | "finalizer" =>
    if args.size ≥ 3 then addLivenessChange ir (← aget args 3) pc
    return some false
  | _ => return none

/-- `escape_call!`.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:1110-1136
```julia
function escape_call!(astate::AnalysisState, pc::Int, args::Vector{Any})
    ft = argextype(first(args), astate.ir)
    f = singleton_type(ft)
    if f isa IntrinsicFunction
        if is_nothrow(astate.ir, pc)
            add_liveness_changes!(astate, pc, args, 2)
        else
            add_fallback_changes!(astate, pc, args, 2)
        end
        # TODO needs to account for pointer operations?
    elseif f isa Builtin
        result = escape_builtin!(f, astate, pc, args)
        if result === missing
            # if this call hasn't been handled by any of pre-defined handlers, escape it conservatively
            add_conservative_changes!(astate, pc, args)
        elseif result === true
            add_liveness_changes!(astate, pc, args, 2)
        elseif is_nothrow(astate.ir, pc)
            add_liveness_changes!(astate, pc, args, 2)
        else
            add_fallback_changes!(astate, pc, args, 2)
        end
    else
        # escape this generic function or unknown function call conservatively
        add_conservative_changes!(astate, pc, args)
    end
end
```
-/
def escapeCall (ir : IR) (pc : Nat) (args : Array Opnd) (ci : CallInfo) : EM Unit := do
  match ci.fk with
  | .intrinsic =>
    if ← isNothrow ir pc then addLivenessChanges ir pc args 2
    else addFallbackChanges ir pc args 2
  | .builtin name =>
    match ← escapeBuiltin ir name pc args ci with
    | none => addConservativeChanges ir pc args
    | some true => addLivenessChanges ir pc args 2
    | some false =>
      if ← isNothrow ir pc then addLivenessChanges ir pc args 2
      else addFallbackChanges ir pc args 2
  | .other => addConservativeChanges ir pc args

/-! ## The fixed-point loop -/

/-- `compute_frameinfo(ir)`: the `idx:leave_pc` ranges of the `EnterNode`s with a catch block.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:681-698
```julia
function compute_frameinfo(ir::IRCode)
    nstmts, nnewnodes = length(ir.stmts), length(ir.new_nodes.stmts)
    tryregions = nothing
    for idx in 1:nstmts+nnewnodes
        inst = ir[SSAValue(idx)]
        stmt = inst[:stmt]
        if isa(stmt, EnterNode)
            leave_block = stmt.catch_dest
            if leave_block ≠ 0
                @assert idx ≤ nstmts "try/catch inside new_nodes unsupported"
                tryregions === nothing && (tryregions = UnitRange{Int}[])
                leave_pc = first(ir.cfg.blocks[leave_block].stmts)
                push!(tryregions, idx:leave_pc)
            end
        end
    end
    return tryregions
end
```
-/
def computeFrameinfo (ir : IR) : Option (List (Int × Int)) := Id.run do
  let mut tryregions : Option (List (Int × Int)) := none
  for idx in List.range ir.insts.size do
    match (ir.insts.getD idx default).stmt with
    | .enter (some leavePc) => tryregions := some (tryregions.getD [] ++ [((idx + 1 : Int), leavePc)])
    | _ => pure ()
  return tryregions

/-- One statement of the `for pc in nstmts:-1:1` loop: runs its handler and returns whether
the loop `continue`s before the propagation.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:592-651
```julia
            stmt = ir[SSAValue(pc)][:stmt]

            # collect escape information
            if isa(stmt, Expr)
                head = stmt.head
                if head === :call
                    escape_call!(astate, pc, stmt.args)
                elseif head === :invoke
                    escape_invoke!(astate, pc, stmt.args)
                elseif head === :new || head === :splatnew
                    escape_new!(astate, pc, stmt.args)
                elseif head === :foreigncall
                    escape_foreigncall!(astate, pc, stmt.args)
                elseif head === :foreignglobal
                    escape_foreignglobal!(astate, pc, stmt.args)
                elseif head === :throw_undef_if_not # XXX when is this expression inserted ?
                    add_escape_change!(astate, stmt.args[1], ThrownEscape(pc))
                elseif is_meta_expr_head(head)
                    # meta expressions doesn't account for any usages
                    continue
                elseif head === :leave || head === :the_exception || head === :pop_exception
                    # ignore these expressions since escapes via exceptions are handled by `escape_exception!`
                    # `escape_exception!` conservatively propagates `AllEscape` anyway,
                    # and so escape information imposed on `:the_exception` isn't computed
                    continue
                elseif head === :gc_preserve_begin
                    # GC preserve is handled by `escape_gc_preserve!`
                elseif head === :gc_preserve_end
                    escape_gc_preserve!(astate, pc, stmt.args)
                elseif head === :static_parameter ||  # this exists statically, not interested in its escape
                       head === :copyast ||           # XXX escape something?
                       head === :isdefined            # just returns `Bool`, nothing accounts for any escapes
                    continue
                else
                    add_conservative_changes!(astate, pc, stmt.args)
                end
            elseif isa(stmt, EnterNode)
                # Handled via escape_exception!
                continue
            elseif isa(stmt, ReturnNode)
                if isdefined(stmt, :val)
                    add_escape_change!(astate, stmt.val, ReturnEscape(pc))
                end
            elseif isa(stmt, PhiNode)
                escape_edges!(astate, pc, stmt.values)
            elseif isa(stmt, PiNode)
                escape_val_ifdefined!(astate, pc, stmt)
            elseif isa(stmt, PhiCNode)
                escape_edges!(astate, pc, stmt.values)
            elseif isa(stmt, UpsilonNode)
                escape_val_ifdefined!(astate, pc, stmt)
            elseif isa(stmt, GlobalRef) || isa(stmt, Core.BindingPartition) # global load
                add_escape_change!(astate, SSAValue(pc), ⊤)
            elseif isa(stmt, SSAValue)
                escape_val!(astate, pc, stmt)
            elseif isa(stmt, Argument)
                escape_val!(astate, pc, stmt)
            else # otherwise `stmt` can be GotoNode, GotoIfNot, and inlined values etc.
                continue
            end
```
-/
def escapeStmt (ir : IR) (pc : Nat) : EM Bool := do
  match (← aget ir.insts pc).stmt with
  | .call args ci =>
    escapeCall ir pc args ci
    return false
  | .invoke args cache mnargs =>
    escapeInvoke ir pc args cache mnargs
    return false
  | .new args =>
    escapeNew ir pc args
    return false
  | .foreigncall args argAny =>
    escapeForeigncall ir pc args argAny
    return false
  | .foreignglobal args =>
    escapeForeignglobal ir pc args
    return false
  | .throwUndefIfNot args =>
    addEscapeChange ir (← aget args 1) (thrownEscapeAt pc)
    return false
  | .gcPreserveEnd beginArgs =>
    escapeGcPreserve ir pc beginArgs
    return false
  | .conservative args =>
    addConservativeChanges ir pc args
    return false
  | .skip => return true
  | .noop => return false
  | .enter _ => return true
  | .ret v =>
    if let some v := v then
      let s ← get
      let (info, heap) := returnEscapeAt s.heap pc
      set { s with heap }
      addEscapeChange ir v info
    return false
  | .phi vals =>
    escapeEdges ir pc vals
    return false
  | .val v =>
    if let some v := v then escapeVal ir pc v
    return false
  | .globalLoad =>
    addEscapeChange ir (.ssa pc) allEscape
    return false

/-- One pass of the `while true` loop: every statement from the last to the first, then
`escape_exception!`. Returns `anyupdate`. Changes recorded by `escape_exception!` stay in
`changes` and are propagated by the next statement that does not `continue`. -/
def escapePass (ir : IR) (tryregions : Option (List (Int × Int))) : EM Bool := do
  let mut anyupdate := false
  for k in List.range ir.insts.size do
    let pc := ir.insts.size - k
    if ← escapeStmt ir pc then continue
    if (← get).changes.isEmpty then continue
    let c ← propagateChanges
    anyupdate := anyupdate || c
    modify fun s => { s with changes := #[] }
  if let some tr := tryregions then escapeException ir tr
  return anyupdate

def escapeLoop (ir : IR) (tryregions : Option (List (Int × Int))) : Nat → EM Unit
  | 0 => throw "outOfBudget"
  | fuel + 1 => do
    if ← escapePass ir tryregions then escapeLoop ir tryregions fuel

/-- `analyze_escapes(ir, nargs, 𝕃ₒ, get_escape_cache)`: the final `EscapeState` and the
`Liveness` heap it refers to.

Julia source: Compiler/src/ssair/EscapeAnalysis.jl:578-672
```julia
function analyze_escapes(ir::IRCode, nargs::Int, 𝕃ₒ::AbstractLattice, get_escape_cache)
    stmts = ir.stmts
    nstmts = length(stmts) + length(ir.new_nodes.stmts)

    tryregions = compute_frameinfo(ir)
    estate = EscapeState(nargs, nstmts)
    changes = Changes() # keeps changes that happen at current statement
    astate = AnalysisState(ir, estate, changes, 𝕃ₒ, get_escape_cache)

    local debug_itr_counter = 0
    while true
        local anyupdate = false

        for pc in nstmts:-1:1
            stmt = ir[SSAValue(pc)][:stmt]
            ...
            isempty(changes) && continue

            anyupdate |= propagate_changes!(estate, changes)

            empty!(changes)
        end

        tryregions !== nothing && escape_exception!(astate, tryregions)

        debug_itr_counter += 1

        anyupdate || break
    end
    ...
    return estate
end
```
-/
def analyzeEscapes (ir : IR) (fuel : Nat := 10000) : JM (EscapeState × Heap) := do
  let tryregions := computeFrameinfo ir
  let s0 : AState := ⟨EscapeState.new ir.nargs ir.insts.size, #[], {}⟩
  let ((), s) ← (escapeLoop ir tryregions fuel).run s0
  return (s.estate, s.heap)

end JuliaLean.Compiler.ssair.EA
