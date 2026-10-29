import JuliaLean.MultidimCov.ArrayV2Core

/-!
Shared vocabulary for the `base/subarray.jl` models (`SubarrayV2*`).

Index objects are the values that `to_indices` produces and a `SubArray` stores
(`ViewIndex`): `Int` scalars, `Base.Slice`, `Base.OneTo`, `UnitRange{Int}`,
`Base.IdentityUnitRange`, `StepRange{Int,Int}`, `Array{Int,N}`, the
`LogicalIndex` of a `Vector{Bool}`, and `Array{CartesianIndex{k},N}`.

`idxAxes` and `idxAt` are the documented meaning of each index object, written
from the docstrings (not from `subarray.jl`): ranges and arrays are one-based,
except `Slice` and `IdentityUnitRange`, which are their own axes
(`base/indices.jl:331-336,357-361`). `specPos` is the manual's definition of
`A[I_1, ..., I_n][J...]` (doc/src/manual/arrays.md, "Indexing"): each scalar
index is kept, each array index `I_k` contributes `I_k[j...]` for its own share
of the subscripts, and a `CartesianIndex` value is splatted.

A parent is any `AbstractArray`: its axes, its `IndexStyle`, its linear and
Cartesian `getindex`, and its type name and element type. `none` is an
`#undef` element. For an `IndexLinear` parent the two accesses agree through
`LinearIndices(A)[I...]` (`_to_linear_index`, `base/abstractarray.jl`).

Julia `Int` arithmetic in `subarray.jl` wraps; it is `iadd`/`isub`/`imul`.
-/

namespace JuliaLean.MultidimCov.SubarrayV2

open JuliaLean.MultidimCov.ArrayV2 (wrap64)

/-- Julia exceptions met by these methods. `argument` keeps its message. -/
inductive SErr where
  | bounds
  | argument (msg : String)
  | method
  | undefRef
  | inexact
  | dimensionMismatch
  deriving Repr, DecidableEq

abbrev SR (α : Type) := Except SErr α

instance {α : Type} [DecidableEq α] : DecidableEq (SR α) := fun a b =>
  match a, b with
  | .ok x, .ok y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .error x, .error y => if h : x = y then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .ok _, .error _ => isFalse (by intro e; cases e)
  | .error _, .ok _ => isFalse (by intro e; cases e)

@[simp] theorem sbind_ok {α β : Type} (x : α) (f : α → SR β) :
    ((Except.ok x : SR α) >>= f) = f x := rfl
@[simp] theorem sbind_error {α β : Type} (e : SErr) (f : α → SR β) :
    ((Except.error e : SR α) >>= f) = .error e := rfl
@[simp] theorem spure {α : Type} (x : α) : (pure x : SR α) = .ok x := rfl

/-- Wrapping `Int` arithmetic (`+`, `-`, `*` on `Int64`). -/
def iadd (a b : Int) : Int := wrap64 (a + b)
def isub (a b : Int) : Int := wrap64 (a - b)
def imul (a b : Int) : Int := wrap64 (a * b)

/-- A unit range of `Int` values `lo:hi` (an axis). -/
structure Ax where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

/-- `length(lo:hi)`. -/
def Ax.len (a : Ax) : Int := if a.hi < a.lo then 0 else a.hi - a.lo + 1

def Ax.mem (a : Ax) (j : Int) : Bool := decide (a.lo ≤ j) && decide (j ≤ a.hi)

def oneAx (n : Int) : Ax := ⟨1, n⟩

/-- Index objects stored in a `SubArray` (`ViewIndex` after `to_indices`). -/
inductive Idx where
  /-- An `Int` scalar. -/
  | int (n : Int)
  /-- `Base.Slice(r)` for an `AbstractUnitRange` `r` with values `a.lo:a.hi`. -/
  | slice (a : Ax)
  /-- `Base.OneTo(n)`, `n ≥ 0`. -/
  | oneto (n : Int)
  /-- `UnitRange{Int}` `a.lo:a.hi`. -/
  | unit (a : Ax)
  /-- `Base.IdentityUnitRange(a.lo:a.hi)`. -/
  | ident (a : Ax)
  /-- `StepRange{Int,Int}` with first element `start`, step `st ≠ 0` and `n ≥ 0` elements. -/
  | step (start st n : Int)
  /-- `Array{Int,N}` with sizes `dims`, elements in column-major order. -/
  | arr (dims : List Nat) (xs : List Int)
  /-- `LogicalIndex` of a one-based `Vector{Bool}` mask. -/
  | mask (bs : List Bool)
  /-- `Array{CartesianIndex{k},N}` with sizes `dims`, elements in column-major order. -/
  | carr (k : Nat) (dims : List Nat) (xs : List (List Int))
  deriving Repr, DecidableEq

namespace Idx

/-- `isa ScalarIndex` (`Real`). -/
def isScalar : Idx → Bool
  | .int _ => true
  | _ => false

/-- `isa AbstractRange` (with `ScalarIndex` elements). -/
def isRange : Idx → Bool
  | .slice _ | .oneto _ | .unit _ | .ident _ | .step _ _ _ => true
  | _ => false

/-- `isa AbstractUnitRange`. -/
def isUnitRange : Idx → Bool
  | .slice _ | .oneto _ | .unit _ | .ident _ => true
  | _ => false

def isSlice : Idx → Bool
  | .slice _ => true
  | _ => false

end Idx

def allScalar (I : List Idx) : Bool := I.all Idx.isScalar

/-- Number of `true` entries. -/
def countTrue : List Bool → Int
  | [] => 0
  | b :: bs => (if b then 1 else 0) + countTrue bs

/-- Positions of the `true` entries, counting from `k`. -/
def truePosFrom (k : Int) : List Bool → List Int
  | [] => []
  | b :: bs => if b then k :: truePosFrom (k + 1) bs else truePosFrom (k + 1) bs

/-- One-based positions of the `true` entries. -/
def truePos (bs : List Bool) : List Int := truePosFrom 1 bs

/-- `length` of a `StepRange` given by its first element, step and count. -/
def stepLast (start st n : Int) : Int := start + (n - 1) * st

/-- Documented axes of an index object (`axes(i)`): arrays and ordinary ranges
are one-based; `Slice` and `IdentityUnitRange` are their own axes. -/
def idxAxes : Idx → List Ax
  | .int _ => []
  | .slice a => [a]
  | .ident a => [a]
  | .oneto n => [oneAx n]
  | .unit a => [oneAx a.len]
  | .step _ _ n => [oneAx n]
  | .arr dims _ => dims.map (fun (d : Nat) => oneAx (d : Int))
  | .mask bs => [oneAx (countTrue bs)]
  | .carr _ dims _ => dims.map (fun (d : Nat) => oneAx (d : Int))

/-- Column-major zero-based offset of one-based subscripts `js` in sizes `dims`. -/
def cmOff : List Nat → List Int → Option Nat
  | [], [] => some 0
  | d :: ds, j :: js =>
      if 1 ≤ j ∧ j ≤ (d : Int) then (cmOff ds js).map (fun r => (j - 1).toNat + d * r) else none
  | _, _ => none

/-- Documented value of an index object at subscripts `js` (inside its axes), as
the parent coordinates it contributes: `[v]` for an `Int` value, the
coordinates of a `CartesianIndex` value. -/
def idxAt : Idx → List Int → Option (List Int)
  | .int n, [] => some [n]
  | .slice a, [j] => if a.mem j then some [j] else none
  | .ident a, [j] => if a.mem j then some [j] else none
  | .oneto n, [j] => if 1 ≤ j ∧ j ≤ n then some [j] else none
  | .unit a, [j] => if 1 ≤ j ∧ j ≤ a.len then some [a.lo + (j - 1)] else none
  | .step s st n, [j] => if 1 ≤ j ∧ j ≤ n then some [s + (j - 1) * st] else none
  | .arr dims xs, js => (cmOff dims js).bind (fun k => xs[k]?.map (fun v => [v]))
  | .mask bs, [j] => if 1 ≤ j then (truePos bs)[(j - 1).toNat]?.map (fun v => [v]) else none
  | .carr _ dims xs, js => (cmOff dims js).bind (fun k => xs[k]?)
  | _, _ => none

/-- `index_dimsum` contribution: the number of output dimensions of an index. -/
def idxRank (i : Idx) : Nat := (idxAxes i).length

/-- `index_ndims` contribution: the number of parent dimensions an index consumes. -/
def idxConsumes : Idx → Nat
  | .carr k _ _ => k
  | _ => 1

/-- Axes of the view `A[I...]` (the manual: the axes of the result are the axes
of the indices, in order; scalars contribute none). -/
def viewAxes (I : List Idx) : List Ax := I.flatMap idxAxes

/-- The manual's definition of the parent position of `A[I...][J...]`. -/
def specPos : List Idx → List Int → Option (List Int)
  | [], [] => some []
  | [], _ :: _ => none
  | i :: rest, js =>
      let d := idxRank i
      (idxAt i (js.take d)).bind (fun p => (specPos rest (js.drop d)).map (p ++ ·))

/-- Subscripts inside axes. -/
def inAxes : List Ax → List Int → Prop
  | [], [] => True
  | a :: as, j :: js => a.lo ≤ j ∧ j ≤ a.hi ∧ inAxes as js
  | _, _ => False

instance : (as : List Ax) → (js : List Int) → Decidable (inAxes as js)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | a :: as, j :: js =>
      match instDecidableInAxes as js with
      | isTrue h =>
          if h1 : a.lo ≤ j ∧ j ≤ a.hi then isTrue ⟨h1.1, h1.2, h⟩
          else isFalse (fun h' => h1 ⟨h'.1, h'.2.1⟩)
      | isFalse h => isFalse (fun h' => h h'.2.2)

def inAxesB : List Ax → List Int → Bool
  | [], [] => true
  | a :: as, j :: js => decide (a.lo ≤ j) && decide (j ≤ a.hi) && inAxesB as js
  | _, _ => false

/-- Column-major zero-based offset of a position inside axes. -/
def linOff : List Ax → List Int → Int
  | a :: as, p :: ps => (p - a.lo) + a.len * linOff as ps
  | _, _ => 0

/-- `LinearIndices(axes)[pos...]`: the axis value itself for a vector, else
`1 + ` the column-major offset (`base/indices.jl:476-490`). -/
def linearIndex (axs : List Ax) (pos : List Int) : Int :=
  match axs, pos with
  | [_], [p] => p
  | _, _ => 1 + linOff axs pos

/-- `length` of an array with these axes. -/
def axesLen (axs : List Ax) : Int := axs.foldr (fun a n => a.len * n) 1

/-- The axis of linear indices: `axes(A, 1)` for a vector, else `1:length(A)`. -/
def linearAxis (axs : List Ax) : Ax :=
  match axs with
  | [a] => a
  | _ => ⟨1, axesLen axs⟩

/-- `IndexStyle`. -/
inductive Style where
  | linear
  | cartesian
  deriving Repr, DecidableEq

/-- `IndexStyle(a, b)`: linear only if both are linear (`base/indices.jl:97-99`). -/
def Style.combine : Style → Style → Style
  | .linear, .linear => .linear
  | _, _ => .cartesian

/-- A Julia array type: its name and its element type parameter. -/
structure PType where
  name : String
  elt : String
  deriving Repr, DecidableEq

/-- `eltype(::Type{<:AbstractArray{T}}) = T`. -/
def eltypeOf (t : PType) : String := t.elt

/-- An `AbstractArray` parent. -/
structure Par (α : Type) where
  /-- `typeof(parent)`. -/
  ty : PType
  axes : List Ax
  linear : Bool
  /-- `A[k]` with one linear index `k`. -/
  lin : Int → Option α
  /-- `A[pos...]` with one index per dimension. For an `IndexLinear` array the
  two agree through `LinearIndices` (`PValid` states this contract). -/
  cart : List Int → Option α

def Par.style (p : Par α) : Style := if p.linear then .linear else .cartesian

/-- Element of a parent at a Cartesian position (`A[pos...]` under `@inbounds`). -/
def Par.atPos (p : Par α) (pos : List Int) : Option α := p.cart pos

/-- Read an element: `#undef` is `UndefRefError`. -/
def readElt (x : Option α) : SR α :=
  match x with
  | some v => .ok v
  | none => .error .undefRef

/-- `Int(first(i))` of an index object. -/
def idxFirst : Idx → SR Int
  | .int n => .ok n
  | .slice a => .ok a.lo
  | .ident a => .ok a.lo
  | .oneto _ => .ok 1
  | .unit a => .ok a.lo
  | .step s _ _ => .ok s
  | .arr _ xs => match xs with | x :: _ => .ok x | [] => .error .bounds
  | .mask bs => match truePos bs with | x :: _ => .ok x | [] => .error .bounds
  | .carr _ _ _ => .error .method

/-- `step(r)` of a range index (`Int`). -/
def idxStep : Idx → Int
  | .step _ st _ => st
  | _ => 1

/-- Type name used by `typeof(i)` in error messages. -/
def idxTypeName : Idx → String
  | .int _ => "Int64"
  | .slice _ => "Base.Slice{UnitRange{Int64}}"
  | .oneto _ => "Base.OneTo{Int64}"
  | .unit _ => "UnitRange{Int64}"
  | .ident _ => "Base.IdentityUnitRange{UnitRange{Int64}}"
  | .step _ _ _ => "StepRange{Int64, Int64}"
  | .arr dims _ =>
      if dims.length = 1 then "Vector{Int64}" else if dims.length = 2 then "Matrix{Int64}"
      else s!"Array\{Int64, {dims.length}}"
  | .mask _ => "Base.LogicalIndex{Int64, Vector{Bool}}"
  | .carr k dims _ =>
      if dims.length = 1 then s!"Vector\{CartesianIndex\{{k}}}"
      else if dims.length = 2 then s!"Matrix\{CartesianIndex\{{k}}}"
      else s!"Array\{CartesianIndex\{{k}}, {dims.length}}"

end JuliaLean.MultidimCov.SubarrayV2
