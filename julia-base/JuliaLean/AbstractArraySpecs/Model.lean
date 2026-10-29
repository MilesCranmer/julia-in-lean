import JuliaLean.Core

/-!
Models of the generic `AbstractArray` methods of `base/abstractarray.jl` (master
`bbfa0ce4150`) used by the spec-first properties of this area.

An input `Arr α` stores Int64 axes and mutable column-major data. Its canonical
getter and setter follow the OffsetArrays convention. The model identifies a
vector's linear axis with its axis values, which is valid for identity-indexed
axes but does not represent `first(LinearIndices(A))` for a plain offset
`UnitRange`. The generic zero-index consumer is modelled separately in
`AbstractArraySpecs.Indexing`.

Arrays are values here, so `===`, `mightalias` and `unalias` never fire; the
properties are about distinct arrays.
-/

namespace JuliaLean.AbstractArraySpecs

abbrev I64 := JInt .i64

/-- An `Int` literal. -/
def i64 (x : Int) : I64 := JInt.lit .i64 x

/-- Exceptions thrown by the modelled methods. -/
inductive Err where
  | boundsError
  | argumentError
  | dimensionMismatch
  | divideError
  | assertionError
  | methodError
  | canonicalIndexError
  | inexactError
  deriving DecidableEq, Repr

abbrev R (α : Type) := Except Err α

/-- `Int` bounds. -/
def tmin : Int := -(2 ^ 63)
def tmax : Int := 2 ^ 63 - 1

/-! ## Axes -/

inductive AxKind where
  /-- `Base.OneTo{Int}`. -/
  | oneTo
  /-- A non-OneTo unit range, represented only by its endpoint values. -/
  | unit
  deriving DecidableEq, Repr

/-- A unit-range axis `lo:hi`. -/
structure Ax where
  kind : AxKind
  lo : I64
  hi : I64
  deriving DecidableEq, Repr

/-- `Base.OneTo(n)` for `n ≥ 0`. -/
def oneTo (n : I64) : Ax := ⟨.oneTo, i64 1, n⟩

/-- `length(r)`: `r.stop` for `OneTo` (base/range.jl:806), else
`oneunit + (stop - start)` with wrapping `Int` arithmetic (base/range.jl:794-805). -/
def axLength (r : Ax) : I64 :=
  match r.kind with
  | .oneTo => r.hi
  | .unit => i64 1 + (r.hi - r.lo)

/-- `isempty(r::AbstractUnitRange) = first(r) > last(r)` (base/range.jl:711). -/
def axIsEmpty (r : Ax) : Bool := decide (r.hi < r.lo)

/-- `==` on two `AbstractUnitRange{Int}` (base/range.jl:1141-1150): empty ranges are
equal, a length-one range equals a length-one range with the same first element,
otherwise first, step (always 1) and last must agree. -/
def axEq (r s : Ax) : Bool :=
  if axIsEmpty r then axIsEmpty s
  else if axLength r == i64 1 then (axLength s == i64 1) && (r.lo == s.lo)
  else (r.lo == s.lo) && (r.hi == s.hi)

/-- Tuple `==` of axes: same length and elementwise `==`. -/
def axesEq : List Ax → List Ax → Bool
  | [], [] => true
  | r :: rs, s :: ss => axEq r s && axesEq rs ss
  | _, _ => false

/-! ## Input arrays -/

inductive Style where
  | linear
  | cartesian
  deriving DecidableEq, Repr

structure Arr (α : Type) where
  axes : List Ax
  style : Style
  /-- Elements in column-major order. -/
  data : List α
  deriving DecidableEq, Repr

/-- Mathematical length of an axis. -/
def Ax.len (r : Ax) : Int := r.hi.val - r.lo.val + 1

/-- Product of the axis lengths. -/
def totalLen : List Ax → Int
  | [] => 1
  | r :: rs => r.len * totalLen rs

/-- Well-formed axis: a `OneTo` starts at 1, lengths are nonnegative (Julia's
`UnitRange` constructor normalises `stop`) and representable as `Int`. -/
def Ax.WF (r : Ax) : Prop :=
  (r.kind = .oneTo → r.lo.val = 1) ∧ 0 ≤ r.len ∧ r.len ≤ tmax

/-- Well-formed array: axes are well formed, the element count is the product of
the axis lengths, and that count is an `Int` (as `length` returns). -/
def Arr.WF {α : Type} (A : Arr α) : Prop :=
  (∀ r ∈ A.axes, r.WF) ∧ (A.data.length : Int) = totalLen A.axes ∧ totalLen A.axes ≤ tmax

instance (r : Ax) : Decidable r.WF := by unfold Ax.WF; infer_instance
instance {α : Type} [DecidableEq α] (A : Arr α) : Decidable A.WF := by unfold Arr.WF; infer_instance

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

/-! ## Reference semantics (independent of Base)

Column-major position of a Cartesian index list, following the manual
(doc/src/manual/arrays.md, "Omitted and extra indices"): indices beyond `ndims` must
be 1, and omitted trailing indices are allowed for length-one dimensions. -/
def refCartPos : List Ax → List Int → Option Nat
  | axs, [] => if axs.all (fun r => decide (r.len = 1)) then some 0 else none
  | [], i :: is => if i = 1 then refCartPos [] is else none
  | r :: rs, i :: is =>
      if r.lo.val ≤ i ∧ i ≤ r.hi.val then
        (refCartPos rs is).map (fun p => (i - r.lo.val).toNat + r.len.toNat * p)
      else none

/-- Position of a linear index: a vector's linear indices are its axis, every other
array's are `1:length(A)` (doc/src/manual/arrays.md, "Linear indexing";
base/abstractarray.jl:337-346). -/
def refLinPos {α : Type} (A : Arr α) (k : Int) : Option Nat :=
  match A.axes with
  | [r] => if r.lo.val ≤ k ∧ k ≤ r.hi.val then some (k - r.lo.val).toNat else none
  | axs => if 1 ≤ k ∧ k ≤ totalLen axs then some (k - 1).toNat else none

/-- The position an index list refers to: one index is linear, any other number is
Cartesian. -/
def refPos {α : Type} (A : Arr α) : List I64 → Option Nat
  | [k] => refLinPos A k.val
  | I => refCartPos A.axes (I.map (·.val))

/-! ## The array type's canonical methods -/

def elemAt {α : Type} (A : Arr α) (p : Option Nat) : R α :=
  match p with
  | some p => match A.data[p]? with
    | some x => .ok x
    | none => .error .boundsError
  | none => .error .boundsError

def storeAt {α : Type} (A : Arr α) (p : Option Nat) (v : α) : R (Arr α) :=
  match p with
  | some p => if p < A.data.length then .ok { A with data := A.data.set p v } else .error .boundsError
  | none => .error .boundsError

/-- `getindex(A, i::Int)` of an `IndexLinear` array type. -/
def canonGetL {α : Type} (A : Arr α) (i : I64) : R α := elemAt A (refLinPos A i.val)
/-- `getindex(A, I::Vararg{Int,N})` of an `IndexCartesian` array type. -/
def canonGetC {α : Type} (A : Arr α) (I : List I64) : R α :=
  if I.length = A.axes.length then elemAt A (refCartPos A.axes (I.map (·.val)))
  else .error .boundsError
def canonSetL {α : Type} (A : Arr α) (v : α) (i : I64) : R (Arr α) := storeAt A (refLinPos A i.val) v
def canonSetC {α : Type} (A : Arr α) (v : α) (I : List I64) : R (Arr α) :=
  if I.length = A.axes.length then storeAt A (refCartPos A.axes (I.map (·.val))) v
  else .error .boundsError

/-! ## Base: size, length, linear indices -/

/-- `size(A)` of the array type: the axis lengths. -/
def sizeA {α : Type} (A : Arr α) : List I64 := A.axes.map axLength

/-- `length(t::AbstractArray) = prod(size(t))`, wrapping `Int` products. -/
def prodI : List I64 → I64
  | [] => i64 1
  | x :: xs => x * prodI xs

def lengthA {α : Type} (A : Arr α) : I64 := prodI (sizeA A)

/-- `oneto(n)` / `unchecked_oneto(n)` for the nonnegative `length(A)`. -/
def onetoLen {α : Type} (A : Arr α) : Ax := oneTo (lengthA A)

/-- `axes1(A)` (base/abstractarray.jl:140-141): `OneTo(1)` for 0-d, else `axes(A)[1]`. -/
def axes1 {α : Type} (A : Arr α) : Ax :=
  match A.axes with
  | [] => oneTo (i64 1)
  | r :: _ => r

/-- `eachindex(::IndexLinear, A)` (base/abstractarray.jl:394-396): `axes1(A)` for a
vector, `oneto(length(A))` otherwise. For identity-indexed vector axes this also
represents `LinearIndices(A)`. -/
def linearAxis {α : Type} (A : Arr α) : Ax :=
  match A.axes with
  | [_] => axes1 A
  | _ => onetoLen A

/-! ## Base: bounds checking -/

/-- `unsigned(x)` of an `Int`. -/
def unsignedVal (x : I64) : Int := wrapInt .u64 x.val

/-- `checkindex(Bool, inds, i::Int)` (base/abstractarray.jl:751-753): the `OneTo{Int}`
method uses `unsigned(i -% one(i)) < unsigned(last(inds))`; other unit ranges
(including `IdentityUnitRange`, line 752) compare with both endpoints. -/
def checkindex (r : Ax) (i : I64) : Bool :=
  match r.kind with
  | .oneTo => decide (unsignedVal (i - i64 1) < unsignedVal r.hi)
  | .unit => decide (r.lo ≤ i) && decide (i ≤ r.hi)

/-- `checkbounds_indices(Bool, inds, I)` (base/abstractarray.jl:722-728), with
`get(inds, 1, OneTo(1))` and `safe_tail`. -/
def checkboundsIndices : List Ax → List I64 → Bool
  | inds, [] => inds.all (fun x => axLength x == i64 1)
  | inds, i :: I => checkindex (inds.headD (oneTo (i64 1))) i && checkboundsIndices inds.tail I

/-- `checkbounds(Bool, A, I...)` (base/abstractarray.jl:682-693): one index uses
`eachindex(IndexLinear(), A)`. -/
def checkboundsBool {α : Type} (A : Arr α) (I : List I64) : Bool :=
  match I with
  | [i] => checkindex (linearAxis A) i
  | _ => checkboundsIndices A.axes I

/-- `checkbounds(A, I...)`: `BoundsError` unless in bounds. -/
def checkbounds {α : Type} (A : Arr α) (I : List I64) : R Unit :=
  if checkboundsBool A I then .ok () else .error .boundsError

/-! ## Base: index conversion -/

/-- `_sub2ind_recurse` (base/abstractarray.jl:1193-1202) with `nextL` and
`offsetin` (lines 1204-1208). -/
def sub2indRecurse : List Ax → I64 → I64 → List I64 → I64
  | _, _, ind, [] => ind
  | [], L, ind, i :: I => sub2indRecurse [] L (ind + (i - i64 1) * L) I
  | r :: rs, L, ind, i :: I => sub2indRecurse rs (L * axLength r) (ind + (i - r.lo) * L) I

/-- `_sub2ind(inds, I::Integer...)` (base/abstractarray.jl:1178-1191) for a nonempty
index list. -/
def sub2ind (inds : List Ax) (I : List I64) : R I64 :=
  match inds, I with
  | [r], [i] => if r.kind = .oneTo then .ok i else .error .argumentError
  | [r], I => if r.kind = .oneTo then .ok (sub2indRecurse [r] (i64 1) (i64 1) I) else .error .argumentError
  | inds, I => .ok (sub2indRecurse inds (i64 1) (i64 1) I)

/-- `first(LinearIndices(A))`. -/
def firstLinear {α : Type} (A : Arr α) : I64 := (linearAxis A).lo

/-- `_to_linear_index(A, I...)` (base/abstractarray.jl:1398-1401). -/
def toLinearIndex {α : Type} (A : Arr α) (I : List I64) : R I64 :=
  match I with
  | [] => .ok (firstLinear A)
  | [i] => .ok i
  | i :: I' => if A.axes.length = 1 then .ok i else sub2ind A.axes (i :: I')

/-- `divrem(x, y)` for `Int` (truncating `div` and `rem`). -/
def divrem (x y : I64) : R (I64 × I64) :=
  if y.val = 0 then .error .divideError
  else if x.val = tmin ∧ y.val = -1 then .error .divideError
  else .ok (i64 (x.val.tdiv y.val), i64 (x.val.tmod y.val))

/-- `_ind2sub_recurse` (base/abstractarray.jl:1217-1227) with `_indexlength` and
`_lookup` (lines 1229-1232). -/
def ind2subRecurse : List Ax → I64 → R (List I64)
  | [], ind => .ok [ind + i64 1]
  | [r], ind => .ok [ind + r.lo]
  | r :: rs, ind => do
      let (indnext, indsub) ← divrem ind (axLength r)
      let rest ← ind2subRecurse rs indnext
      .ok ((indsub + r.lo) :: rest)

/-- `_ind2sub(inds, ind::Integer)` (base/abstractarray.jl:1210-1215). -/
def ind2sub (inds : List Ax) (ind : I64) : R (List I64) :=
  match inds with
  | [] => if ind = i64 1 then .ok [] else .error .boundsError
  | [r] => if r.kind = .oneTo then .ok [ind] else .error .argumentError
  | inds => ind2subRecurse inds (ind - i64 1)

/-- The zero-index conversion maps `first` over axes without converting the
axis element type (base/abstractarray.jl:1415). -/
def axisStarts {Axis : Type u} {Index : Type v} (first : Axis → Index) (axes : List Axis) : List Index :=
  axes.map first

/-- An axis stores its first index in the axis's own index type. -/
structure AxisFirst (Index : Type) where
  first : Index

/-- Every output coordinate retains its own axis's index type and first value,
including when different axes use different index types. -/
def AxisStartsContract : Prop :=
  ∀ (axes : List (Σ Index : Type, AxisFirst Index)),
    let result := axisStarts (fun axis => (⟨axis.1, axis.2.first⟩ : Σ Index : Type, Index)) axes
    result.length = axes.length ∧
      ∀ i (h : i < axes.length),
        result[i]? = some (⟨axes[i].1, axes[i].2.first⟩ : Σ Index : Type, Index)

theorem axisStartsContract_proven : AxisStartsContract := by
  intro axes
  constructor
  · simp [axisStarts]
  · intro i h
    simp [axisStarts, h]

/-- `_to_subscript_indices(A, I...)` (base/abstractarray.jl:1414-1432), for an index
count different from `ndims(A)`. -/
def toSubscriptIndices {α : Type} (A : Arr α) (I : List I64) : R (List I64) :=
  match A.axes, I with
  | [], _ => .ok []
  | axs, [] => .ok (axisStarts (·.lo) axs)
  | axs, [i] => ind2sub axs i
  | axs, I =>
      if I.length ≤ axs.length then .ok (I ++ (axs.drop I.length).map (·.lo))
      else .ok (I.take axs.length)

/-! ## Base: getindex and setindex! -/

/-- `getindex(A, I::Int...)` (base/abstractarray.jl:1363-1367) for integer indices:
the array type's canonical method when the signature matches, otherwise
`_getindex(IndexStyle(A), A, I...)` (lines 1392-1397 and 1404-1409). -/
def getindex {α : Type} (A : Arr α) (I : List I64) : R α :=
  match A.style with
  | .linear =>
      if I.length = 1 then canonGetL A (I.headD (i64 0))
      else do
        checkbounds A I
        let k ← toLinearIndex A I
        canonGetL A k
  | .cartesian =>
      if I.length = A.axes.length then canonGetC A I
      else do
        checkbounds A I
        let J ← toSubscriptIndices A I
        canonGetC A J

/-- `setindex!(A, v, I::Int...)` (base/abstractarray.jl:1464-1468, 1486-1504). -/
def setindex {α : Type} (A : Arr α) (v : α) (I : List I64) : R (Arr α) :=
  match A.style with
  | .linear =>
      if I.length = 1 then canonSetL A v (I.headD (i64 0))
      else do
        checkbounds A I
        let k ← toLinearIndex A I
        canonSetL A v k
  | .cartesian =>
      if I.length = A.axes.length then canonSetC A v I
      else do
        checkbounds A I
        let J ← toSubscriptIndices A I
        canonSetC A v J

/-- `get(A, I::Dims, default)` and `get(A, i::Integer, default)`
(base/abstractarray.jl:1637-1639). -/
def getDefault {α : Type} (A : Arr α) (I : List I64) (d : α) : R α :=
  if checkboundsBool A I then getindex A I else .ok d

/-! ## Base: first, last, size(A, d), axes(A, d), isempty -/

/-- `first(a::AbstractArray) = a[first(eachindex(a))]` (base/abstractarray.jl:455).
`eachindex(A)` is `eachindex(IndexLinear(), A)` for linear arrays and
`CartesianIndices(axes(A))` otherwise, whose first element is the tuple of axis
starts. -/
def firstA {α : Type} (A : Arr α) : R α :=
  match A.style with
  | .linear => getindex A [(linearAxis A).lo]
  | .cartesian => getindex A (A.axes.map (·.lo))

/-- `last(a) = a[end]`, `lastindex(a) = last(eachindex(IndexLinear(), a))`
(base/abstractarray.jl:429, 530). -/
def lastA {α : Type} (A : Arr α) : R α := getindex A [(linearAxis A).hi]

/-- `size(t::AbstractArray, dim)` (base/abstractarray.jl:42-46) for `dim::Int`:
`s[d]` on the size tuple throws `BoundsError` for `d < 1`. -/
def sizeD {α : Type} (A : Arr α) (d : I64) : R I64 :=
  if d.val ≤ (sizeA A).length then
    match (sizeA A)[d.val.toNat - 1]?, decide (1 ≤ d.val) with
    | some s, true => .ok s
    | _, _ => .error .boundsError
  else .ok (i64 1)

/-- `axes(A, d)` (base/abstractarray.jl:79-82) for `d::Int`. -/
def axesD {α : Type} (A : Arr α) (d : I64) : R Ax :=
  if d.val ≤ A.axes.length then
    match A.axes[d.val.toNat - 1]?, decide (1 ≤ d.val) with
    | some r, true => .ok r
    | _, _ => .error .boundsError
  else .ok (oneTo (i64 1))

/-- `isempty(a::AbstractArray) = (length(a) == 0)` (base/abstractarray.jl:1262). -/
def isemptyA {α : Type} (A : Arr α) : Bool := lengthA A == i64 0

/-! ## Base: eachindex with two arrays -/

/-- `IndexStyle(A, B)`: linear only when both are. -/
def styleOf2 {α β : Type} (A : Arr α) (B : Arr β) : Style :=
  if A.style = .linear ∧ B.style = .linear then .linear else .cartesian

/-- `eachindex(A, B)` (base/abstractarray.jl:386-404 for `IndexLinear`,
base/multidimensional.jl:`eachindex(::IndexCartesian, A, B...)` for the rest).
The result is the common index range (for the linear style) or axes. -/
def eachindex2 {α β : Type} (A : Arr α) (B : Arr β) : R (List Ax) :=
  match styleOf2 A B with
  | .linear =>
      if axEq (linearAxis B) (linearAxis A) then .ok [linearAxis A] else .error .dimensionMismatch
  | .cartesian =>
      if axesEq B.axes A.axes then .ok A.axes else .error .dimensionMismatch

end JuliaLean.AbstractArraySpecs
