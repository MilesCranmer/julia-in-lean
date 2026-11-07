import JuliaLean.base.broadcast
import JuliaLean.base.array
import JuliaLean.Bindings.base.iterators
import JuliaLean.base.promotion

/-! Proposal only. Every operation exposed as a binding below selects an installed
model. Incomplete materialize/broadcast/copy pipelines are listed as gaps in
broadcast.model-changes.md; no record or parameter supplies those missing calls. -/
namespace JuliaLean.Bindings.base.broadcast
open JuliaLean
abbrev M := JuliaLean.base.array.MutationM
abbrev I := JInt .i64

/-- The single Except-to-MutationM lift preserves the current heap on failure. -/
def liftExcept {α V : Type} (value : Except JuliaLean.base.array.Error V) : M α V :=
  match value with
  | .ok result => pure result
  | .error error => throw error

/-- Fully bound instantiate specialization for AbstractArrayStyle{0}. -/
def instantiateZero {α S F Args Axes : Type}
    (bc : JuliaLean.base.broadcast.Lazy.Broadcasted
      (JuliaLean.base.broadcast.Style.TypedStyle (.abstractArray 0) S) F Args Axes) :
    M α (JuliaLean.base.broadcast.Lazy.Broadcasted
      (JuliaLean.base.broadcast.Style.TypedStyle (.abstractArray 0) S) F Args Axes) :=
  pure (JuliaLean.base.broadcast.Lazy.m319 bc)

/-- Fully bound instantiate specialization for Style{Tuple}, Nothing. -/
def instantiateTupleNothing {α S F Args : Type}
    (bc : JuliaLean.base.broadcast.Lazy.Broadcasted
      (JuliaLean.base.broadcast.Style.TypedStyle .tuple S) F Args Unit) :
    M α (JuliaLean.base.broadcast.Lazy.Broadcasted
      (JuliaLean.base.broadcast.Style.TypedStyle .tuple S) F Args Unit) :=
  pure (JuliaLean.base.broadcast.Lazy.m321 bc)

/-- Vector similar uses the installed allocator and its existing memory effect. -/
def vectorSimilar {α : Type} (layout : Option JuliaLean.base.array.MemoryLayout) (a : Nat) (n : I) : M α Nat :=
  JuliaLean.base.array.similar418 (JuliaLean.base.array.mutableAllocate layout a) a n

/-- Bind the installed assignment-loop helper to actual mutable-vector reads and
writes. Its index sequence is data; computing eachindex(bc) remains an explicit gap. -/
def vectorCopyLoop {α : Type} (dest source : Nat) (indices : List I) : M α Nat :=
  JuliaLean.base.broadcast.Material.copyLoop
    (fun s i => JuliaLean.base.array.mutableGet s i)
    (fun d i v => JuliaLean.base.array.mutableSet d v i) dest source indices

namespace Checks
open JuliaLean.base.broadcast

def initial : JuliaLean.base.array.MutableMemory I :=
  JuliaLean.base.array.MutableMemory.initialMany
    [[some (JInt.lit .i64 5), some (JInt.lit .i64 7)], [some (JInt.lit .i64 0)]]

def copying (indices : List I) : Except JuliaLean.base.array.Error Nat × JuliaLean.base.array.MutableMemory I :=
  (vectorCopyLoop 1 0 indices).run initial

#guard (copying [JInt.lit .i64 1]).1 == .ok 1
#guard ((copying [JInt.lit .i64 1]).2.contents 1).map (Option.map (·.val)) == [some 5]
#guard (copying [JInt.lit .i64 1,JInt.lit .i64 2]).1 == .error .bounds
#guard ((copying [JInt.lit .i64 1,JInt.lit .i64 2]).2.contents 1).map (Option.map (·.val)) == [some 5]
#guard (liftExcept (α := I) (V := Unit) (.error .inexact) |>.run initial).1 == .error .inexact
#guard ((liftExcept (α := I) (V := Unit) (.error .inexact)).run initial).2.contents 0 == initial.contents 0

-- These are source-dispatch regressions, not implementations of open leaf calls.
def bc (family : Style.StyleType) (axes : Option (List Nat)) :
    Lazy.Broadcasted (Style.TypedStyle family Unit) Unit Nat (Option (List Nat)) :=
  ⟨⟨()⟩, (), 17, axes⟩
def instantiated (family : Style.StyleType) (axes : Option (List Nat)) :=
  Lazy.instantiateByStyle (m := Except String)
    (fun _ => .error "combine axes") (fun _ _ => .error "check axes") (bc family axes)

#guard (instantiated (.abstractArray 0) none).toOption.map (fun x => x.axes) == some none
#guard (instantiated (.abstractArray 0) (some [8])).toOption.map (fun x => x.axes) == some (some [8])
#guard (instantiated .tuple none).toOption.map (fun x => x.axes) == some none
#guard (instantiated .tuple (some [8])).toOption.isNone
#guard (instantiated (.abstractArray 1) none).toOption.isNone
#guard (instantiated (.abstractArray 1) (some [8])).toOption.isNone

-- No runtime rank argument exists: the style type indexes both copy cases.
def copied (rank : Nat) : Except String (Sum Nat Unit) :=
  Material.copyArrayStyle (m := Except String) (Iter := Unit) (State := Unit) (Index := Unit)
    (Ty := Unit) (TyVar := Unit) (NDim := Unit)
    (fun expression => pure expression.args)
    (fun _ => .error "result eltype") (fun _ => .error "concrete type")
    (fun _ _ => .error "similar") (fun _ _ => .error "copyto")
    (fun _ => .error "preprocess") (fun _ => .error "eachindex")
    (fun _ => .error "iterate") (fun _ _ => .error "getindex")
    (fun _ => .error "typeof") (fun _ _ _ => .error "setindex")
    (fun _ _ => .error "type identity") (fun _ _ => .error "subtype") () () ()
    (fun _ => .error "isa AbstractArray")
    (fun _ => .error "TypeVar") (fun _ => .error "ndims")
    (fun _ _ => .error "apply AbstractArray") (fun _ _ => .error "UnionAll")
    (fun _ _ _ _ _ => .error "nonleaf") (fun _ _ => .error "assert return")
    (bc (.abstractArray rank) none)
#guard copied 0 == .ok (.inl 17)
#guard copied 1 == .error "result eltype"

#eval IO.println "BROADCAST BIND2 CHECKS OK"
end Checks
end JuliaLean.Bindings.base.broadcast

/-! Proposed nonleaf additions only. General eltype/typeof/isa, broadcast element
reads, heterogeneous storage conversions and similar dispatch remain explicit gaps.
The following operations bind only the installed operations they name. -/
namespace JuliaLean.Bindings.base.broadcast.Nonleaf
open JuliaLean
/--
Error carrier adapter only: a disjoint sum preserves both existing array and range exception payloads without editing either error type or introducing another runtime.
Julia source: base/broadcast.jl:1136-1143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
    # Function barrier that makes the copying to newdest type stable
    for II in Iterators.take(iter, count)
        newdest[II] = dest[II]
    end
    newdest[I] = val
    return copyto_nonleaf!(newdest, bc, iter, state, count+1)
end
```
-/
abbrev Error := JuliaLean.base.array.Error ⊕ JuliaLean.base.range.Exc

/--
Bridge only: preserve the already-installed MutationM result and heap in the already-installed iterator Exec effect; do not implement a second heap or runtime.
Julia source: base/broadcast.jl:1136-1143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
    # Function barrier that makes the copying to newdest type stable
    for II in Iterators.take(iter, count)
        newdest[II] = dest[II]
    end
    newdest[I] = val
    return copyto_nonleaf!(newdest, bc, iter, state, count+1)
end
```
-/
def liftMutation {α V : Type} (action : JuliaLean.base.array.MutationM α V) :
    JuliaLean.base.iterators.Exec Error (JuliaLean.base.array.MutableMemory α) V :=
  fun heap =>
    let (result, heap) := action.run heap
    some (result.mapError Sum.inl, heap)

/--
Bridge for the existing range iterator/error result: preserve the complete exception payload and current heap.
Julia source: base/broadcast.jl:1136-1143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
    # Function barrier that makes the copying to newdest type stable
    for II in Iterators.take(iter, count)
        newdest[II] = dest[II]
    end
    newdest[I] = val
    return copyto_nonleaf!(newdest, bc, iter, state, count+1)
end
```
-/
def liftRange {H V : Type} (result : JuliaLean.base.range.JlX V) :
    JuliaLean.base.iterators.Exec Error H V :=
  fun heap => some (result.mapError Sum.inr, heap)

/--
Selected existing OrdinalRange methods for UnitRange{Int}; no new iterator semantics or prepared index list.
Julia source: base/range.jl:935-943 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::OrdinalRange) = isempty(r) ? nothing : (first(r), first(r))

function iterate(r::OrdinalRange{T}, i) where {T}
    @inline
    i == last(r) && return nothing
    next = convert(T, i + step(r))
    (next, next)
end

```
-/
def unitRangeIterate {H : Type}
    (iter : JuliaLean.Bindings.base.iterators.IntUnitRange) (state : Option JInt64) :
    JuliaLean.base.iterators.Exec Error H (Option (JInt64 × JInt64)) :=
  match state with
  | none => liftRange (JuliaLean.base.range.JIterate1.iterate iter)
  | some state => liftRange (JuliaLean.base.range.JIterate2.iterate iter state)

/-
Selected Take constructor, called by the native-count take method below.
Julia source: base/iterators.jl:781-784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Take(xs::I, n::Integer) where {I}
        n < 0 && throw(ArgumentError("Take length must be non-negative"))
        return new{I}(xs, n)
    end
```
-/
/--
Selected generic take method on UnitRange{Int}; Int conversion, negative-count check and field conversion call installed models.
Julia source: base/iterators.jl:815-815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
take(xs, n::Integer) = Take(xs, Int(n))
```
-/
def nativeTake {H : Type} (iter : JuliaLean.Bindings.base.iterators.IntUnitRange)
    (count : JInt64) : JuliaLean.base.iterators.Exec Error H
      (JuliaLean.base.iterators.Take JuliaLean.Bindings.base.iterators.IntUnitRange) :=
  let toInt := fun n : JInt64 =>
    liftRange (JuliaLean.base.range.liftJl (JuliaLean.base.int.convert .i64 n))
  JuliaLean.base.iterators.takeModel toInt
    (JuliaLean.base.iterators.mkTake
      (fun n => pure (JuliaLean.base.int.ltSame n (JInt.lit .i64 0)))
      toInt
      (fun message => JuliaLean.base.iterators.fail (.inr (.jl (.argumentError message)))))
    iter count

/--
Closed prefix-loop binding only, for the existing same-element-type mutable-vector store and actual UnitRange{Int} indices. It does not implement type widening, the final assignment or restart continuation.
Julia source: base/broadcast.jl:1136-1143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function restart_copyto_nonleaf!(newdest, dest, bc, val, I, iter, state, count)
    # Function barrier that makes the copying to newdest type stable
    for II in Iterators.take(iter, count)
        newdest[II] = dest[II]
    end
    newdest[I] = val
    return copyto_nonleaf!(newdest, bc, iter, state, count+1)
end
```
-/
def vectorCopyPrefix {α : Type} (newdest dest : Nat)
    (iter : JuliaLean.Bindings.base.iterators.IntUnitRange) (count : JInt64) :
    JuliaLean.base.iterators.Exec Error (JuliaLean.base.array.MutableMemory α) Unit := do
  let taken ← nativeTake iter count
  JuliaLean.base.broadcast.Material.copyPrefix
    (JuliaLean.base.iterators.iterateTake unitRangeIterate)
    (fun d i => liftMutation (JuliaLean.base.array.mutableGet d i))
    (fun d i v => liftMutation (JuliaLean.base.array.mutableSet d v i))
    dest newdest taken none

/--
Selected existing descriptor-level promote_typejoin binding. This does not supply actual typeof/eltype descriptors for array handles or values; none retains the installed typejoin nontermination semantics.
Julia source: base/promotion.jl:198-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function promote_typejoin(@nospecialize(a), @nospecialize(b))
    c = typejoin(_promote_typesubtract(a), _promote_typesubtract(b))
    return Union{a, b, c}
end
```
-/
def promoteTypejoin {E H : Type} (a b : JuliaLean.base.promotion.PType) :
    JuliaLean.base.iterators.Exec E H JuliaLean.base.promotion.PType :=
  fun heap =>
    (JuliaLean.base.promotion.primitivePromoteTypejoinDispatch a b).map
      (fun result => (.ok result, heap))

end JuliaLean.Bindings.base.broadcast.Nonleaf
