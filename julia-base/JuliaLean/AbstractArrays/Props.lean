import JuliaLean.AbstractArrays.Model
import JuliaLean.ArrayOps.PureProps
import JuliaLean.ReinterpretArrays.IndexProps

/-! Properties promised by Julia's array docstrings and interface invariants. -/

namespace JuliaLean.AbstractArrays

open JuliaLean

/-- `size(A,d)` and `axes(A,d)` return the stored dimension for
`1 ≤ d ≤ ndims`, a singleton beyond `ndims`, and throw below one. -/
def SizeAxesDim : Prop := ∀ (sizes : List I64) (d : I64),
  (d.val < 1 → sizeDim sizes d = .error .boundsError ∧ axesDim sizes d = .error .boundsError) ∧
  (1 ≤ d.val → d.val ≤ sizes.length →
    sizeDim sizes d = .ok (sizes.getD (d.val - 1).toNat (i64 1)) ∧
    axesDim sizes d = .ok (Axis.oneTo (sizes.getD (d.val - 1).toNat (i64 1)).val.toNat)) ∧
  (sizes.length < d.val → sizeDim sizes d = .ok (i64 1) ∧ axesDim sizes d = .ok (Axis.oneTo 1))

/-- The trailing-singleton promise for every fixed-width Integer dimension,
including positive values above `typemax(Int)`. -/
def SizeAllIntegerDims : Prop := ∀ (sizes : List I64) (t : IntTy) (d : JInt t),
  sizes.length < d.val → sizeDimInteger sizes d = .ok (i64 1)

/-- Integer, range and Colon checkindex methods accept exactly the values their
source definitions describe. -/
def CheckIndexForms : Prop :=
  (∀ (a : Axis) (i : I64), checkScalar a (.integer i) = a.contains i) ∧
  (∀ (a : Axis) (r : RangeIndex),
    checkRange a r = (r.empty || (a.contains r.first && a.contains r.last))) ∧
  (∀ a : Axis, checkRange a ⟨i64 1, i64 0, true⟩ = true)

/-- Cartesian coordinates, too many indices and too few indices obey the
trailing-singleton rules of `checkbounds_indices`. -/
def CheckboundsCartesian : Prop := ∀ (axes : List Axis) (is : List ScalarIndex),
  checkCoords axes is = true ↔ CoordsValid axes is

/-- Logical masks are accepted exactly when their axes equal the array axes
they consume. -/
def CheckboundsLogical : Prop := ∀ (axes maskAxes : List Axis),
  checkMask axes maskAxes = true ↔ axes = maskAxes

/-- A single supported integer index uses the vector axis for a vector and
`1:length(A)` for a multidimensional array. -/
def CheckboundsLinear : Prop :=
  (∀ (a : Axis) (i : I64), checkLinear [a] (.integer i) = a.contains i) ∧
  (∀ (axes : List Axis) (i : I64), axes.length ≠ 1 →
    checkLinear axes (.integer i) =
      decide (1 ≤ i.val ∧ i.val ≤ (axes.foldl (fun p a => p * i64 a.len) (i64 1)).val))

/-- `checkbounds` says true exactly when `to_index` accepts the scalar and its
numeric value is within the axis. -/
def CheckboundsAgreesGetindex : Prop := ∀ (a : Axis) (i : ScalarIndex),
  checkScalar a i = true ↔ ∃ j, i.toIndex = .ok j ∧ a.contains j = true

/-- `to_indices` flattens every CartesianIndex and rejects unsupported scalar
components before producing canonical integer indices. -/
def ToIndicesCartesian : Prop :=
  (∀ (axes : List Axis) (is : List ScalarIndex),
    toIndices axes [.cartesian is] =
      (is.mapM (fun i => return CanonIndex.integer (← i.toIndex)))) ∧
  (∀ (axes : List Axis) (i : I64),
    toIndices axes [.scalar (.integer i)] = .ok [.integer i])

/-- Generic whole-array copy writes source elements in iteration order,
preserves the rest of a longer destination, and rejects a shorter destination
without changing it. -/
def CopytoGeneric : Prop := ∀ (α : Type) (dest src : GVec α),
  (src.slots.length ≤ dest.slots.length →
    dest.copyAll src = .ok { dest with slots := src.slots ++ dest.slots.drop src.slots.length }) ∧
  (dest.slots.length < src.slots.length → dest.copyAll src = .error .boundsError)

/-- Overlapping block copy reads from an unaliased source snapshot. This is the
shared `ArrayOps` model of the same `unalias` contract. -/
def CopytoOverlap : Prop := JuliaLean.ArrayOps.CopytoAliasSpec

/-- `similar` has the requested length, one-based axis and no assigned slots. -/
def SimilarFallback : Prop := ∀ (α : Type) (n : Nat),
  let v : GVec α := GVec.similar n
  v.first = i64 1 ∧ v.slots.length = n ∧ v.slots.all Option.isNone

/-- `firstindex`, `lastindex` and `eachindex` agree for every offset vector. -/
def IndexIteration : Prop := ∀ (α : Type) (v : GVec α),
  v.eachIndex = (List.range v.slots.length).map (fun k => i64 (v.first.val + Int.ofNat k)) ∧
  v.eachIndex.length = v.slots.length ∧
  v.firstIndex = v.first ∧ v.lastIndex = v.axis.last

/-- `isassigned` is true exactly for a supported, in-bounds integer whose slot
is assigned, and propagates invalid scalar-index errors. -/
def IsassignedSpec : Prop := ∀ (α : Type) (v : GVec α) (i : I64),
  v.isAssigned (.integer i) =
    .ok (v.axis.contains i && (v.slots.getD (i.val - v.first.val).toNat none).isSome)

/-- Mixed-type vector concatenation preserves promoted values and `hcat`
rejects unequal row counts. -/
def ConcatVectors : Prop :=
  (∀ (α β γ : Type) (f : α → γ) (g : β → γ) (xs : List α) (ys : List β),
    vcatPromote f g xs ys = xs.map f ++ ys.map g) ∧
  (∀ (α β γ : Type) (f : α → γ) (g : β → γ) (xs : List α) (ys : List β),
    (xs.length = ys.length → hcatPromote f g xs ys = .ok ((xs.map f).zip (ys.map g))) ∧
    (xs.length ≠ ys.length → ∃ m, hcatPromote f g xs ys = .error (.argumentError m)))

/-- Reverse preserves offset axes and reverses values; fill assigns the same
value everywhere; isempty agrees with zero length. -/
def BasicArrayOps : Prop := ∀ (α : Type) (v : GVec α) (x : α),
  (GVec.reverse v).axis = v.axis ∧
  (GVec.reverse v).slots = v.slots.reverse ∧
  (GVec.fill v x).slots = List.replicate v.slots.length (some x) ∧
  (v.isEmpty = true ↔ v.slots = [])

/-- One-based indexing is required exactly when no axis has an offset. -/
def RequireOneBased : Prop := ∀ axes : List Axis,
  (axes.all Axis.isOneBased = true → requireOneBased axes = .ok ()) ∧
  (axes.any (fun a => !a.isOneBased) = true →
    ∃ m, requireOneBased axes = .error (.argumentError m))

/-- The documented ArgumentError for every integer-valued non-one axis start,
including values outside the Int range. -/
def RequireOneBasedAllIntegerAxes : Prop := ∀ (t : IntTy) (first : JInt t),
  first.val ≠ 1 → ∃ m, requireOneBasedInteger first = .error (.argumentError m)

/-- For every nonnegative shape whose product is an Int, conversion of an
in-bounds linear index to Cartesian subscripts and back returns the input.
`Ind2subCorrect` uses Julia's verified signed-multiplicative-inverse division
and the same column-major subscript formula. -/
def LinearCartesianRoundTrip : Prop := JuliaLean.ReinterpretArrays.Ind2subCorrect

end JuliaLean.AbstractArrays
