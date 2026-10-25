import JuliaLean.ArrayOps.Pure
import JuliaLean.Multidim.Model
import JuliaLean.ReinterpretArrays.Reshape

/-!
Models of the generic `AbstractArray` machinery in `base/abstractarray.jl` and
`base/indices.jl` at Julia `bbfa0ce4150`.

An `Axis` is an `IdentityUnitRange` described by its first index and length.
`GVec` is a mutable abstract vector described by an axis and assigned or
unassigned slots. Actual Julia arrays have `Int` lengths, so the properties
below restrict list lengths and products to the representable range where
needed.
-/

namespace JuliaLean.AbstractArrays

open JuliaLean

abbrev I64 := JInt .i64

def i64 (x : Int) : I64 := JInt.lit .i64 x

/-- An integer axis with `len` elements beginning at `first`. -/
structure Axis where
  first : I64
  len : Nat
  deriving DecidableEq, Repr

namespace Axis

/-- Last index. Empty axes use `first - 1`, as a Julia unit range does. -/
def last (a : Axis) : I64 := a.first + i64 ((a.len : Int) - 1)

/-- Numeric membership in an axis. Source: `base/abstractarray.jl:751-753`. -/
def contains (a : Axis) (i : I64) : Bool :=
  decide (a.first.val ≤ i.val ∧ i.val < a.first.val + a.len)

/-- `Base.OneTo(n)`. -/
def oneTo (n : Nat) : Axis := ⟨i64 1, n⟩

/-- Whether the axis begins at one. -/
def isOneBased (a : Axis) : Bool := a.first.val == 1

end Axis

/-- `size(A, d)`, `base/abstractarray.jl:42-46`. -/
def sizeDim (sizes : List I64) (d : I64) : Jl I64 :=
  if d.val < 1 then .error .boundsError
  else if d.val ≤ sizes.length then
    .ok (sizes.getD (d.val - 1).toNat (i64 1))
  else .ok (i64 1)

/-- `size(A, dim)` for an arbitrary fixed-width `Integer`: the first source
line is `d = Int(dim)::Int`, so conversion can fail before the trailing
dimension branch. -/
def sizeDimInteger {t : IntTy} (sizes : List I64) (d : JInt t) : Jl I64 := do
  let d ← JInt.convert .i64 d.val
  sizeDim sizes d

/-- `axes(A, d)`, `base/abstractarray.jl:79-82`, for one-based axes. -/
def axesDim (sizes : List I64) (d : I64) : Jl Axis :=
  if d.val < 1 then .error .boundsError
  else if d.val ≤ sizes.length then
    .ok (Axis.oneTo (sizes.getD (d.val - 1).toNat (i64 1)).val.toNat)
  else .ok (Axis.oneTo 1)

/-- `has_offset_axes`, `base/abstractarray.jl:114-122`. -/
def hasOffsetAxes (axes : List Axis) : Bool := axes.any (fun a => !a.isOneBased)

/-- `require_one_based_indexing`, `base/abstractarray.jl:125-135`. -/
def requireOneBased (axes : List Axis) : Jl Unit :=
  if hasOffsetAxes axes then .error (.argumentError "offset arrays are not supported") else .ok ()

/-- The vector fast path of `has_offset_axes`, `base/abstractarray.jl:116`,
for an axis whose first value has any fixed-width integer type. -/
def hasOffsetInteger {t : IntTy} (first : JInt t) : Jl Bool := do
  let first ← JInt.convert .i64 first.val
  return first.val != 1

/-- `require_one_based_indexing` after the integer-axis fast path. -/
def requireOneBasedInteger {t : IntTy} (first : JInt t) : Jl Unit := do
  if ← hasOffsetInteger first then
    throw (.argumentError "offset arrays are not supported")
  return ()

/-- Scalar `Real` indices seen by `checkindex`. `integer` is supported by
`to_index`; `unsupportedReal` represents `Bool` and non-integer reals, which
still reach the `i::Real` checkindex method. -/
inductive ScalarIndex where
  | integer (value : I64)
  | unsupportedReal (value : I64)
  deriving DecidableEq, Repr

namespace ScalarIndex

def value : ScalarIndex → I64
  | .integer i | .unsupportedReal i => i

/-- `to_index`, `base/indices.jl:243,258-266`. -/
def toIndex : ScalarIndex → Jl I64
  | .integer i => .ok i
  | .unsupportedReal _ => .error (.argumentError "invalid index")

end ScalarIndex

/-- `checkindex(Bool, inds, i::Real)`, `base/abstractarray.jl:751-753`.
The implementation tests only the numeric value and ignores whether `to_index`
supports the scalar type. -/
def checkScalar (axis : Axis) (i : ScalarIndex) : Bool := axis.contains i.value

/-- Range index. `empty` records Julia's `isempty(i)` before endpoint checks. -/
structure RangeIndex where
  first : I64
  last : I64
  empty : Bool
  deriving DecidableEq, Repr

/-- `checkindex` for `Colon` and `AbstractRange`,
`base/abstractarray.jl:754-760`. -/
def checkRange (axis : Axis) (r : RangeIndex) : Bool :=
  r.empty || (axis.contains r.first && axis.contains r.last)

/-- Cartesian scalar checks performed one axis at a time by
`checkbounds_indices`, `base/abstractarray.jl:722-728`. Missing axes are
trailing singleton dimensions, and missing indices require every remaining
axis to be singleton. -/
def checkCoords : List Axis → List ScalarIndex → Bool
  | [], [] => true
  | axes, [] => axes.all (fun a => a.len == 1)
  | [], i :: is => checkScalar (Axis.oneTo 1) i && checkCoords [] is
  | a :: axes, i :: is => checkScalar a i && checkCoords axes is

/-- The same condition as a `Prop`, used to state correctness. -/
def CoordsValid : List Axis → List ScalarIndex → Prop
  | [], [] => True
  | axes, [] => ∀ a ∈ axes, a.len = 1
  | [], i :: is => Axis.contains (Axis.oneTo 1) i.value = true ∧ CoordsValid [] is
  | a :: axes, i :: is => Axis.contains a i.value = true ∧ CoordsValid axes is

/-- `checkbounds(Bool, A, i)` for one scalar index,
`base/abstractarray.jl:687-693`. Vectors retain their axis; other arrays use
`1:length(A)`. -/
def checkLinear (axes : List Axis) (i : ScalarIndex) : Bool :=
  match axes with
  | [a] => checkScalar a i
  | _ =>
    let n := axes.foldl (fun p a => p * i64 a.len) (i64 1)
    decide (1 ≤ i.value.val ∧ i.value.val ≤ n.val)

/-- Logical-mask bounds checks, `base/multidimensional.jl:905-920`. An
N-dimensional mask must have exactly the consumed axes. -/
def checkMask (axes maskAxes : List Axis) : Bool := axes == maskAxes

/-- Raw indices accepted by `to_indices`. -/
inductive RawIndex where
  | scalar (i : ScalarIndex)
  | cartesian (is : List ScalarIndex)
  | colon
  | mask (axes : List Axis)
  deriving DecidableEq, Repr

/-- Canonical indices produced by `to_indices`: integers, slices and logical
indices. -/
inductive CanonIndex where
  | integer (i : I64)
  | slice (axis : Axis)
  | logical (axes : List Axis)
  deriving DecidableEq, Repr

/-- `to_indices`, `base/indices.jl:310-323` and
`base/multidimensional.jl:928-939`: CartesianIndex is flattened, Colon becomes
a slice of the current axis, and other scalars go through `to_index`. -/
def toIndices : List Axis → List RawIndex → Jl (List CanonIndex)
  | _, [] => .ok []
  | _, [.cartesian is] => is.mapM (fun i => return .integer (← i.toIndex))
  | axes, .cartesian is :: rest => do
      let head ← is.mapM (fun i => return .integer (← i.toIndex))
      let tail ← toIndices (axes.drop is.length) rest
      return head ++ tail
  | a :: axes, .colon :: rest => do
      let tail ← toIndices axes rest
      return .slice a :: tail
  | [], .colon :: rest => do
      let tail ← toIndices [] rest
      return .slice (Axis.oneTo 1) :: tail
  | axes, .scalar i :: rest => do
      let j ← i.toIndex
      let tail ← toIndices axes.tail rest
      return .integer j :: tail
  | axes, .mask maskAxes :: rest => do
      let tail ← toIndices (axes.drop maskAxes.length) rest
      return .logical maskAxes :: tail

/-- A generic mutable vector with offset axis and possibly unassigned slots. -/
structure GVec (α : Type) where
  first : I64
  slots : List (Option α)
  deriving DecidableEq, Repr

namespace GVec

def axis (v : GVec α) : Axis := ⟨v.first, v.slots.length⟩

def eachIndex (v : GVec α) : List I64 :=
  (List.range v.slots.length).map fun k => i64 (v.first.val + Int.ofNat k)

def firstIndex (v : GVec α) : I64 := v.first

def lastIndex (v : GVec α) : I64 := v.axis.last

/-- `isassigned`, `base/multidimensional.jl:1637-1660`: convert the scalar,
return false for bounds or unassigned slots, and propagate invalid-index
errors. -/
def isAssigned (v : GVec α) (i : ScalarIndex) : Jl Bool := do
  let i ← i.toIndex
  if !v.axis.contains i then return false
  return (v.slots.getD (i.val - v.first.val).toNat none).isSome

/-- Generic `copyto!(dest, src)` after `unalias`,
`base/abstractarray.jl:1072-1123`. Iteration order, rather than offset equality,
determines the corresponding elements. -/
def copyAll (dest src : GVec α) : Jl (GVec α) :=
  if src.slots.length ≤ dest.slots.length then
    .ok { dest with slots := src.slots ++ dest.slots.drop src.slots.length }
  else .error .boundsError

/-- Generic `similar(a, T, dims)` fallback, `base/abstractarray.jl:819-834`,
represented by an unassigned one-based vector. -/
def similar (n : Nat) : GVec α := ⟨i64 1, List.replicate n none⟩

/-- `reverse(A)` preserves the axis and reverses iteration values,
`base/array.jl:2253-2265`. -/
def reverse (v : GVec α) : GVec α := { v with slots := v.slots.reverse }

/-- `_fill!`, `base/array.jl:368-377`. -/
def fill (v : GVec α) (x : α) : GVec α :=
  { v with slots := List.replicate v.slots.length (some x) }

/-- `isempty(a::AbstractArray)`, `base/abstractarray.jl:1262`. -/
def isEmpty (v : GVec α) : Bool := v.slots.length == 0

end GVec

/-- Mixed-element-type `vcat` after promotion,
`base/abstractarray.jl:1689-1753`. -/
def vcatPromote (f : α → γ) (g : β → γ) (xs : List α) (ys : List β) : List γ :=
  xs.map f ++ ys.map g

/-- Mixed-element-type `hcat`, `base/abstractarray.jl:1755-1800`, represented
as rows. -/
def hcatPromote (f : α → γ) (g : β → γ) (xs : List α) (ys : List β) : Jl (List (γ × γ)) :=
  if xs.length = ys.length then .ok ((xs.map f).zip (ys.map g))
  else .error (.argumentError "number of rows must match")

end JuliaLean.AbstractArrays
