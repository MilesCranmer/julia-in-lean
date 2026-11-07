import JuliaLean.base.reshapedarray
import JuliaLean.Registry.Types
import JuliaLean.Bindings.base.reshapedarray
import JuliaLean.base.essentials
import JuliaLean.base.tuple
import JuliaLean.base.operators

/-!
# Properties of `base/reshapedarray.jl`

This file contains statements only. Callees outside `reshapedarray.jl` remain typed interfaces with
only the stated laws; each function defined here is named through the model in
`JuliaLean.base.reshapedarray`.
-/

namespace JuliaLean.Proofs.base.reshapedarray

open JuliaLean JuliaLean.base.int JuliaLean.base.reshapedarray JuliaLean.Registry

/-- The exact, unbounded-integer product used to describe a requested shape. -/
def exactDimProduct : List I64 → Int
  | [] => 1
  | dim :: rest => dim.val * exactDimProduct rest

/-- Every requested dimension is nonnegative. -/
def dimensionsNonnegative (dims : List I64) : Prop :=
  ∀ dim, dim ∈ dims → 0 ≤ dim.val

/-- A successful `Core.checked_dims` call preserves the exact product. -/
def checkedDimsSound {N : Nat} (checkedDims : Vector I64 N → RResult I64) : Prop :=
  ∀ dims product, checkedDims dims = .ok product →
    dimensionsNonnegative dims.toList ∧ exactDimProduct dims.toList = product.val

/-- A successful reshape checked the dimensions and found the source length. -/
def checkedShapeAgreement {N : Nat} {A : Type}
    (checkedDims : Vector I64 N → RResult I64) (length : A → RResult I64)
    (parent : A) (dims : Vector I64 N) : Prop :=
  ∃ n, checkedDims dims = .ok n ∧ length parent = .ok n ∧
    dimensionsNonnegative dims.toList ∧ exactDimProduct dims.toList = n.val

/-- `reshape` preserves a nonnegative exact element count and shares the source storage. -/
def ReshapeCheckSound : Prop :=
  (∀ {T : Type} {M N : Nat} {Ref : Type}
      (checkedDims : Vector I64 N → RResult I64)
      (length : ArrayValue T M Ref → RResult I64)
      (parent : ArrayValue T M Ref) (dims : Vector I64 N)
      (result : ArrayValue T N Ref),
      checkedDimsSound checkedDims →
      reshapeArray checkedDims length parent dims = .ok result →
      checkedShapeAgreement checkedDims length parent dims ∧
        result.ref = parent.ref ∧ result.dims = dims) ∧
  (∀ {T : Type} {N : Nat} {P : Type}
      (length : P → RResult I64)
      (checkedDims : Vector I64 N → RResult I64)
      (product : Vector I64 N → RResult I64)
      (indexStyle : P → RResult IndexStyle)
      (parent : P) (dims : Vector I64 N)
      (result : ReshapedArray T N P Unit),
      checkedDimsSound checkedDims → indexStyle parent = .ok .linear →
      reshapeAbstractArray length checkedDims (throwDmrs product) indexStyle
        (constructReshapedLinear (T := T) (N := N)) parent dims = .ok result →
      checkedShapeAgreement checkedDims length parent dims ∧
        result.parent = parent ∧ result.dims = dims) ∧
  (∀ {T : Type} {N : Nat} {P : Type}
      (length : P → RResult I64)
      (checkedDims : Vector I64 N → RResult I64)
      (product : Vector I64 N → RResult I64)
      (indexStyle : P → RResult IndexStyle)
      (parentRank : P → Nat)
      (parent : P) (dims : Vector I64 N)
      (result : ReshapedArray T N P Unit),
      checkedDimsSound checkedDims → indexStyle parent = .ok .cartesian →
      parentRank parent = 0 →
      reshapeAbstractArray length checkedDims (throwDmrs product) indexStyle
        (constructReshapedCartesianZero (T := T) (N := N)) parent dims = .ok result →
      checkedShapeAgreement checkedDims length parent dims ∧
        result.parent = parent ∧ result.dims = dims) ∧
  (∀ {T : Type} {N : Nat} {P MI : Type}
      (length : P → RResult I64)
      (checkedDims : Vector I64 N → RResult I64)
      (product : Vector I64 N → RResult I64)
      (indexStyle : P → RResult IndexStyle)
      (parentRank : P → Nat)
      (size : P → RResult (List I64)) (front : List I64 → List I64)
      (toInt : I64 → RResult I64) (makeInverse : I64 → MI)
      (parent : P) (dims : Vector I64 N)
      (result : ReshapedArray T N P MI),
      checkedDimsSound checkedDims → indexStyle parent = .ok .cartesian →
      parentRank parent > 0 →
      reshapeAbstractArray length checkedDims (throwDmrs product) indexStyle
        (constructReshapedCartesian size (fun values => .ok (front values))
          toInt (fun value => .ok (makeInverse value)) (T := T) (N := N)) parent dims = .ok result →
      checkedShapeAgreement checkedDims length parent dims ∧
        result.parent = parent ∧ result.dims = dims)

/-- The documented Core dimension-check rule is an external Base method. -/
def checkedDimsRejectsTypemax {N : Nat}
    (checkedDims : Vector I64 N → RResult I64) : Prop :=
  ∀ dims, 2 ≤ N → JInt.typemax .i64 ∈ dims.toList →
    checkedDims dims = .error .argumentError

/-- Every mathematically exact reshape succeeds, as the reshape documentation promises. -/
def ReshapeCheckComplete : Prop :=
  ∀ {T : Type} {M N : Nat} {Ref : Type}
    (checkedDims : Vector I64 N → RResult I64)
    (length : ArrayValue T M Ref → RResult I64)
    (parent : ArrayValue T M Ref) (dims : Vector I64 N) (n : I64),
    checkedDimsRejectsTypemax checkedDims → length parent = .ok n →
    dimensionsNonnegative dims.toList → exactDimProduct dims.toList = n.val →
    reshapeArray checkedDims length parent dims = .ok ⟨parent.ref, dims⟩

/-- A checked colon dimension gives a nonnegative shape with the original element count. -/
def checkedDimsListSound (checkedDims : List I64 → RResult I64) : Prop :=
  ∀ dims product, checkedDims dims = .ok product →
    dimensionsNonnegative dims ∧ exactDimProduct dims = product.val

def iszeroExact (iszero : I64 → RResult Bool) : Prop :=
  ∀ x, iszero x = .ok (decide (x.val = 0))

def divremExact (divrem : I64 → I64 → RResult (I64 × I64)) : Prop :=
  ∀ x y q r, 0 < y.val → divrem x y = .ok (q, r) →
    q.val * y.val + r.val = x.val ∧ 0 ≤ r.val ∧ r.val < y.val

def convertIntExact (convertInt : I64 → RResult I64) : Prop :=
  ∀ x y, convertInt x = .ok y → y.val = x.val

/-- The inferred colon extent makes the product of the returned dimensions exact. -/
def ReshapeColonSound : Prop :=
  ∀ (len : I64) {D : Type}
    (checkedDims : List I64 → RResult I64)
    (iszero : I64 → RResult Bool)
    (divrem : I64 → I64 → RResult (I64 × I64))
    (convertInt : I64 → RResult I64)
    (dims : D) (pre post result : List I64),
    0 ≤ len.val → dimensionsNonnegative (pre ++ post) →
    checkedDimsListSound checkedDims → iszeroExact iszero →
    divremExact divrem → convertIntExact convertInt →
    reshapeComputeSizeInt checkedDims (reshapeComputeNonempty iszero divrem)
      convertInt len dims pre post = .ok result →
    (∃ c, result = pre ++ [c] ++ post) ∧
      dimensionsNonnegative result ∧ exactDimProduct result = len.val

/-- One parent axis used to describe column-major subscript conversion. -/
structure AxisSpec where
  origin : I64
  extent : I64

/-- The zero-based linear offset represented by Cartesian coordinates. -/
def columnMajorOffset : List AxisSpec → List I64 → Int
  | [], _ => 0
  | _, [] => 0
  | axis :: axes, coordinate :: coordinates =>
      coordinate.val - axis.origin.val + axis.extent.val * columnMajorOffset axes coordinates

/-- Coordinates lie in each axis represented by the parent. -/
def coordinatesInBounds (axes : List AxisSpec) (coordinates : List I64) : Prop :=
  coordinates.length = axes.length ∧
  ∀ pair ∈ List.zip axes coordinates,
    pair.1.origin.val ≤ pair.2.val ∧
      pair.2.val < pair.1.origin.val + pair.1.extent.val

/-- `ind2sub_rs` returns the one-based column-major coordinates represented by a linear index. -/
def Ind2subCorrect : Prop :=
  ∀ {MI : Type} (axes : List AxisSpec) (multipliers : List MI)
    (divisor : MI → I64)
    (divrem : I64 → MI → RResult (I64 × I64))
    (firstAxis lastAxis : List AxisSpec → RResult AxisSpec)
    (first : AxisSpec → RResult I64)
    (tailAxes : List AxisSpec → RResult (List AxisSpec))
    (add addLast : I64 → I64 → RResult I64)
    (index : I64) (coordinates : List I64),
    multipliers.length + 1 = axes.length →
    (∀ axis ∈ axes, 0 < axis.extent.val) →
    (∀ axis ∈ axes, axis.origin.val + axis.extent.val - 1 ≤ IntTy.max .i64) →
    (∀ pair ∈ List.zip axes multipliers, divisor pair.2 = pair.1.extent) →
    (∀ axis rest, firstAxis (axis :: rest) = .ok axis) →
    (∀ axis rest, tailAxes (axis :: rest) = .ok rest) →
    (∀ axis, first axis = .ok axis.origin) →
    (∀ left right, add left right = .ok (add_int left right)) →
    (∀ left right, addLast left right = .ok (add_int left right)) →
    (∀ value multiplier quotient remainder,
      0 < (divisor multiplier).val →
      divrem value multiplier = .ok (quotient, remainder) →
      value.val = quotient.val * (divisor multiplier).val + remainder.val ∧
        0 ≤ remainder.val ∧ remainder.val < (divisor multiplier).val) →
    1 ≤ index.val → index.val ≤ exactDimProduct (axes.map AxisSpec.extent) →
    (ind2subRs
      (ind2subRsAuxDispatch divrem firstAxis first add tailAxes lastAxis first addLast)
      axes multipliers index = .ok coordinates) →
    coordinatesInBounds axes coordinates ∧
      columnMajorOffset axes coordinates = index.val - 1

/-- The checked Cartesian access path sends only the subscript tuple produced by the inverse map. -/
def MemsafetyReshapedArrayInd2sub : Prop := Ind2subCorrect

/-- Checked linear and Cartesian access preserve parent selection and stop after a failed bound check. -/
def MemsafetyReshapedArrayIndexing : Prop :=
  (∀ {T : Type} {N : Nat} {P E : Type}
    (checkbounds : ReshapedArrayLF T N P → I64 → RResult Unit)
    (firstArray : ReshapedArrayLF T N P → RResult I64)
    (firstParent : P → RResult I64)
    (getindex : P → I64 → RResult E)
    (array : ReshapedArrayLF T N P) (index firstView firstParentIndex : I64) (value : E),
    firstArray array = .ok firstView → firstParent array.parent = .ok firstParentIndex →
    checkbounds array index = .ok () →
    getindexReshapedLinear true checkbounds firstArray firstParent getindex array index = .ok value →
    getindex array.parent (add_int (sub_int index firstView) firstParentIndex) = .ok value) ∧
  (∀ {T : Type} {N : Nat} {P MI I E : Type}
    (checkbounds : P → I → RResult Unit) (getindex : P → I → RResult E)
    (array : ReshapedArray T N P MI) (index : ReshapedIndex I) (value : E),
    checkbounds array.parent index.parentindex = .ok () →
    getindexReshapedIndex true checkbounds getindex array index = .ok value →
    getindex array.parent index.parentindex = .ok value) ∧
  (∀ {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P MI I V : Type}
    (checkbounds : P → I → m Unit) (setindex : P → I → V → m Unit)
    (array : ReshapedArray T N P MI) (index : ReshapedIndex I) (value : V),
    checkbounds array.parent index.parentindex = pure () →
    setindex array.parent index.parentindex value = pure () →
    setindexReshapedIndex true checkbounds setindex array value index = pure value) ∧
  (∀ {T : Type} {N : Nat} {P MI E : Type}
    (checkbounds : ReshapedArray T N P MI → List I64 → RResult Unit)
    (unsafeGet : ReshapedArray T N P MI → List I64 → RResult E)
    (array : ReshapedArray T N P MI) (indices : List I64) (error : ReshapedError),
    checkbounds array indices = .error error →
    getindexReshapedCartesian true checkbounds unsafeGet array indices = .error error) ∧
  (∀ {T : Type} {N : Nat} {P MI V : Type}
    (checkbounds : ReshapedArray T N P MI → List I64 → RResult Unit)
    (unsafeSet : ReshapedArray T N P MI → V → List I64 → RResult V)
    (array : ReshapedArray T N P MI) (value : V) (indices : List I64) (error : ReshapedError),
    checkbounds array indices = .error error →
    setindexReshapedCartesian true checkbounds unsafeSet array value indices = .error error)

/-- Checked reshaped access and assignment preserve the parent's bounds error. -/
def ReshapedCheckedBoundsPropagate : Prop :=
  (∀ {T : Type} {N : Nat} {P E : Type}
    (checkbounds : ReshapedArrayLF T N P → I64 → RResult Unit)
    (firstArray : ReshapedArrayLF T N P → RResult I64) (firstParent : P → RResult I64)
    (getindex : P → I64 → RResult E) (array : ReshapedArrayLF T N P)
    (index : I64) (err : ReshapedError),
    checkbounds array index = .error err →
    getindexReshapedLinear true checkbounds firstArray firstParent getindex array index = .error err) ∧
  (∀ {T : Type} {N : Nat} {P MI E : Type}
    (checkbounds : ReshapedArray T N P MI → List I64 → RResult Unit)
    (unsafeGet : ReshapedArray T N P MI → List I64 → RResult E)
    (array : ReshapedArray T N P MI) (indices : List I64) (err : ReshapedError),
    checkbounds array indices = .error err →
    getindexReshapedCartesian true checkbounds unsafeGet array indices = .error err) ∧
  (∀ {T : Type} {N : Nat} {P I E : Type} {MI : Type}
    (checkbounds : P → I → RResult Unit) (getindex : P → I → RResult E)
    (array : ReshapedArray T N P MI) (index : ReshapedIndex I) (err : ReshapedError),
    checkbounds array.parent index.parentindex = .error err →
    getindexReshapedIndex true checkbounds getindex array index = .error err) ∧
  (∀ {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P V : Type}
    (checkbounds : ReshapedArrayLF T N P → I64 → m Unit)
    (firstArray : ReshapedArrayLF T N P → m I64) (firstParent : P → m I64)
    (setindex : P → I64 → V → m Unit) (array : ReshapedArrayLF T N P)
    (value : V) (index : I64) (err : ReshapedError),
    checkbounds array index = throw err →
    setindexReshapedLinear true checkbounds firstArray firstParent setindex array value index = throw err) ∧
  (∀ {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P MI V R : Type}
    (checkbounds : ReshapedArray T N P MI → List I64 → m Unit)
    (unsafeSet : ReshapedArray T N P MI → V → List I64 → m R)
    (array : ReshapedArray T N P MI) (value : V) (indices : List I64) (err : ReshapedError),
    checkbounds array indices = throw err →
    setindexReshapedCartesian true checkbounds unsafeSet array value indices = throw err) ∧
  (∀ {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P MI V I : Type}
    (checkbounds : P → I → m Unit) (setindex : P → I → V → m Unit)
    (array : ReshapedArray T N P MI) (value : V) (index : ReshapedIndex I) (err : ReshapedError),
    checkbounds array.parent index.parentindex = throw err →
    setindexReshapedIndex true checkbounds setindex array value index = throw err)

/-- An out-of-bounds assignment query returns `false` without asking the parent. -/
def ReshapedIsassignedBounds : Prop :=
  (∀ {T : Type} {N : Nat} {P : Type}
    (checkbounds : ReshapedArrayLF T N P → I64 → Bool)
    (firstArray : ReshapedArrayLF T N P → RResult I64)
    (firstParent : P → RResult I64) (isassigned : P → I64 → RResult Bool)
    (array : ReshapedArrayLF T N P) (index : I64),
    checkbounds array index = false →
    isassignedReshapedLinear true checkbounds firstArray firstParent isassigned array index = .ok false) ∧
  (∀ {T : Type} {N : Nat} {P AX MI : Type}
    (checkbounds : ReshapedArray T N P MI → List I64 → Bool)
    (axes : P → RResult (List AX)) (sub2ind : Vector I64 N → List I64 → RResult I64)
    (offset : I64 → List AX → RResult I64)
    (ind2sub : List AX → List MI → I64 → RResult (List I64))
    (isassigned : P → List I64 → RResult Bool)
    (array : ReshapedArray T N P MI) (indices : List I64),
    checkbounds array indices = false →
    isassignedReshapedCartesian true checkbounds axes sub2ind offset ind2sub
      isassigned array indices = .ok false)

/-- Successful assignment through a reshaped array returns the assigned value. -/
def ReshapedAssignmentReturnsValue : Prop :=
  (∀ {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {P V : Type}
    (checkbounds : ReshapedArrayLF T N P → I64 → m Unit)
    (firstArray : ReshapedArrayLF T N P → m I64) (firstParent : P → m I64)
    (setindex : P → I64 → V → m Unit)
    (array : ReshapedArrayLF T N P) (value : V) (index : I64),
    checkbounds array index = pure () →
    (∀ first parentFirst, firstArray array = pure first → firstParent array.parent = pure parentFirst →
      setindex array.parent (add_int (sub_int index first) parentFirst) value = pure ()) →
    setindexReshapedLinear true checkbounds firstArray firstParent setindex array value index = pure value) ∧
  (∀ {T : Type} {N : Nat} {P MI V : Type}
    (checkbounds : ReshapedArray T N P MI → List I64 → RResult Unit)
    (unsafeSet : ReshapedArray T N P MI → V → List I64 → RResult V)
    (array : ReshapedArray T N P MI) (value : V) (indices : List I64),
    checkbounds array indices = .ok () →
    unsafeSet array value indices = .ok value →
    setindexReshapedCartesian true checkbounds unsafeSet array value indices = .ok value)

/-- `reshape!` returns the original array reference after changing its stored dimensions. -/
def ReshapeBangUpdatesDimensions : Prop :=
  ∀ {m : Type → Type} [Monad m] [MonadExceptOf ReshapedError m]
    {T : Type} {N : Nat} {Ref : Type}
    (checkedDims : Vector I64 N → m I64)
    (length : ArrayValue T N Ref → m I64)
    (setfield : ArrayValue T N Ref → Vector I64 N → m Unit)
    (readDims : ArrayValue T N Ref → m (Vector I64 N))
    (array : ArrayValue T N Ref) (dims : Vector I64 N) (n : I64),
    checkedDims dims = pure n → length array = pure n →
    (do
      let result ← reshapeBang checkedDims length setfield array dims
      let storedDims ← readDims result
      pure (result.ref = array.ref ∧ storedDims = dims)) = pure True

/-- The iterator adapter returns normal exhaustion as `nothing` rather than an exception. -/
def ReshapedIteratorExhaustion : Prop :=
  ∀ {I V S : Type} {M : Nat} {MI : Type}
    (iterate : I → List S → Option (V × S))
    (iterator : ReshapedArrayIterator I M MI) (state : List S),
    iterate iterator.iter state = none →
      iterateReshapedIterator iterate iterator state = .ok none

/-- Reshape preserves the observable parent storage, requested shape, and element count. -/
def ReshapeArraySharesData : Prop :=
  (∀ {T E : Type} {M N : Nat} {Ref : Type}
    (checkedDims : Vector I64 N → RResult I64)
    (length : ArrayValue T M Ref → RResult I64)
    (read : Ref → I64 → RResult E)
    (array : ArrayValue T M Ref) (dims : Vector I64 N)
    (result : ArrayValue T N Ref) (index : I64),
    reshapeArray checkedDims length array dims = .ok result →
      result.dims = dims ∧ result.ref = array.ref ∧ read result.ref index = read array.ref index) ∧
  (∀ {T : Type} {N : Nat} {P MI : Type}
    (length : P → RResult I64) (array : ReshapedArray T N P MI),
    reshapedSize array = array.dims ∧
      reshapedLength length array = length array.parent ∧ reshapedParent array = array.parent)

/-- Reshaped-range mutation always raises the documented assignment error. -/
def ReshapedRangeAssignmentError : Prop :=
  (∀ {T : Type} {N : Nat} {A V I : Type}
    (array : ReshapedRange T N A) (value : V) (index : I),
    setindexReshapedRangeLinear rsSetindexError array value index =
      (.error .errorException : RResult Unit)) ∧
  (∀ {T : Type} {N : Nat} {A V I : Type}
    (array : ReshapedRange T N A) (value : V) (indices : I),
    setindexReshapedRangeCartesian rsSetindexError array value indices =
      (.error .errorException : RResult Unit)) ∧
  (∀ {T : Type} {N : Nat} {A V I : Type}
    (array : ReshapedRange T N A) (value : V) (index : ReshapedIndex I),
    setindexReshapedRangeIndex rsSetindexError array value index =
      (.error .errorException : RResult Unit))

/-- The first component of a promoted zero has the same numeric value as the zero length. -/
def zeroPromotionExact {N : Type} (valueOf : N → Int)
    (promote : N → N → RResult (N × N)) (iszero : N → RResult Bool) : Prop :=
  ∀ len product promoted other, iszero len = .ok true →
    promote len product = .ok (promoted, other) → valueOf promoted = valueOf len

/-- A generic product helper returns the exact product of its input values. -/
def genericProductExact {N : Type} (valueOf : N → Int)
    (product : List N → RResult N) : Prop :=
  ∀ dims result, product dims = .ok result →
    valueOf result = dims.foldl (fun acc dim => acc * valueOf dim) 1

/-- Generic integer colon inference preserves the exact element count. -/
def ReshapeGenericColonSound : Prop :=
  ∀ {N D : Type} (valueOf : N → Int)
    (product : List N → RResult N) (iszero : N → RResult Bool)
    (promote : N → N → RResult (N × N))
    (divrem : N → N → RResult (N × N))
    (len : N) (dims : D) (pre post result : List N),
    genericProductExact valueOf product →
    (∀ x, iszero x = .ok (decide (valueOf x = 0))) →
    zeroPromotionExact valueOf promote iszero →
    (∀ x y q r, 0 < valueOf y → divrem x y = .ok (q, r) →
      valueOf x = valueOf q * valueOf y + valueOf r ∧
        0 ≤ valueOf r ∧ valueOf r < valueOf y) →
    (0 ≤ valueOf len) →
    (∀ dim ∈ pre ++ post, 0 ≤ valueOf dim) →
    reshapeComputeSizeGeneric product iszero promote (reshapeComputeNonempty iszero divrem)
      len dims pre post = .ok result →
    (∃ colon, result = pre ++ [colon] ++ post) ∧
      result.foldl (fun acc dim => acc * valueOf dim) 1 = valueOf len

/-- Reshape dimension failures remain `DimensionMismatch` after the product check. -/
def ReshapeDimensionErrors : Prop :=
  (∀ dims : List I64, throw1 dims = (.error .dimensionMismatch : RResult Unit)) ∧
  (∀ len dims : I64 × List I64,
    throw2 len.1 len.2 = (.error .dimensionMismatch : RResult Unit)) ∧
  (∀ {D : Type} (product : D → RResult I64) (length : I64) (kind : String)
      (dims : D) (n : I64), product dims = .ok n →
      throwDmrs product length kind dims = (.error .dimensionMismatch : RResult Unit)) ∧
  (∀ {T : Type} {M N : Nat} {Ref : Type}
      (checkedDims : Vector I64 N → RResult I64)
      (length : ArrayValue T M Ref → RResult I64)
      (array : ArrayValue T M Ref) (dims : Vector I64 N) (n actual : I64),
      checkedDims dims = .ok n → length array = .ok actual → n != actual →
      reshapeArray checkedDims length array dims =
        (.error .dimensionMismatch : RResult (ArrayValue T N Ref)))

/-- Pointer casts preserve the address and pointer addition advances it by the byte offset. -/
def pointerAddressLaws {PtrT PtrS : Type}
    (addressT : PtrT → Int) (addressS : PtrS → Int)
    (ptrAdd : PtrT → I64 → RResult PtrT) (pointer : PtrT → RResult PtrS) : Prop :=
  (∀ base offset shifted, ptrAdd base offset = .ok shifted →
    addressT shifted = addressT base + offset.val) ∧
  (∀ base converted, pointer base = .ok converted → addressS converted = addressT base)

/-- SubArray conversion retains the parent address and applies the source or memory offset. -/
def ReshapedPointerOffsets : Prop :=
  (∀ {T C PtrT : Type}
    (pointerType : PtrT) (innerOffset outerOffset : I64) (conversion : OffsetCConvert T C),
    offsetCconvertNested (@offsetCconvertBase T C PtrT) pointerType outerOffset
      ⟨innerOffset, conversion.cconvParent⟩ =
      .ok ⟨add_int innerOffset outerOffset, conversion.cconvParent⟩) ∧
  (∀ {T C PtrT PtrS : Type}
    (convert : PtrT → C → RResult PtrT) (ptrAdd : PtrT → I64 → RResult PtrT)
    (pointer : PtrT → RResult PtrS) (addressT : PtrT → Int) (addressS : PtrS → Int)
    (pointerType : PtrT) (conversion : OffsetCConvert T C)
    (parentPointer adjusted : PtrT) (result : PtrS),
    convert pointerType conversion.cconvParent = .ok parentPointer →
    ptrAdd parentPointer conversion.byteOffset = .ok adjusted → pointer adjusted = .ok result →
    pointerAddressLaws addressT addressS ptrAdd pointer →
    unsafeConvertOffsetCconvert convert ptrAdd pointer pointerType conversion = .ok result →
    addressS result = addressT parentPointer + conversion.byteOffset.val) ∧
  (∀ {T P PtrT PtrS : Type}
    (firstIndexView : JuliaLean.base.subarray.SubArray P T → RResult I64)
    (firstIndexParent elsize : P → RResult I64)
    (firstIndices : List JuliaLean.base.subarray.Index → RResult (List I64))
    (memoryOffset : P → List I64 → RResult I64)
    (unsafeConvert : PtrT → P → RResult PtrT) (ptrAdd : PtrT → I64 → RResult PtrT)
    (pointer : PtrT → RResult PtrS) (addressT : PtrT → Int) (addressS : PtrS → Int)
    (pointerType : PtrT) (view : JuliaLean.base.subarray.SubArray P T)
    (viewFirst parentFirst elementSize : I64) (base shifted : PtrT) (result : PtrS),
    firstIndexView view = .ok viewFirst → firstIndexParent view.parent = .ok parentFirst →
    elsize view.parent = .ok elementSize →
    unsafeConvert pointerType view.parent = .ok base →
    ptrAdd base (mul_int (sub_int viewFirst parentFirst) elementSize) = .ok shifted →
    pointer shifted = .ok result →
    pointerAddressLaws addressT addressS ptrAdd pointer →
    @unsafeConvertSubArray T P PtrT PtrS (@checkcontiguousDense P Bool)
      firstIndexView firstIndexParent elsize firstIndices memoryOffset
      unsafeConvert ptrAdd pointer pointerType view = .ok result →
    addressS result = addressT base + (mul_int (sub_int viewFirst parentFirst) elementSize).val) ∧
  (∀ {T P PtrT PtrS : Type}
    (firstIndexView : JuliaLean.base.subarray.SubArray P T → RResult I64)
    (firstIndexParent elsize : P → RResult I64)
    (firstIndices : List JuliaLean.base.subarray.Index → RResult (List I64))
    (memoryOffset : P → List I64 → RResult I64)
    (unsafeConvert : PtrT → P → RResult PtrT) (ptrAdd : PtrT → I64 → RResult PtrT)
    (pointer : PtrT → RResult PtrS) (addressT : PtrT → Int) (addressS : PtrS → Int)
    (pointerType : PtrT) (view : JuliaLean.base.subarray.SubArray P T)
    (indices : List I64) (delta : I64) (base shifted : PtrT) (result : PtrS),
    firstIndices view.indices = .ok indices → memoryOffset view.parent indices = .ok delta →
    unsafeConvert pointerType view.parent = .ok base → ptrAdd base delta = .ok shifted →
    pointer shifted = .ok result → pointerAddressLaws addressT addressS ptrAdd pointer →
    @unsafeConvertSubArray T P PtrT PtrS (@checkcontiguousAbstract P Bool)
      firstIndexView firstIndexParent elsize firstIndices memoryOffset
      unsafeConvert ptrAdd pointer pointerType view = .ok result →
    addressS result = addressT base + delta.val) ∧
  (∀ {T P PtrT C : Type}
    (cconvert : PtrT → P → RResult C)
    (firstIndexView : JuliaLean.base.subarray.SubArray P T → RResult I64)
    (firstIndexParent elsize : P → RResult I64)
    (firstIndices : List JuliaLean.base.subarray.Index → RResult (List I64))
    (memoryOffset : P → List I64 → RResult I64)
    (pointerType : PtrT) (view : JuliaLean.base.subarray.SubArray P T)
    (viewFirst parentFirst elementSize : I64) (parentConversion : C),
    cconvert pointerType view.parent = .ok parentConversion →
    firstIndexView view = .ok viewFirst → firstIndexParent view.parent = .ok parentFirst →
    elsize view.parent = .ok elementSize →
    @cconvertSubArray T P PtrT C cconvert (@checkcontiguousDense P Bool)
      firstIndexView firstIndexParent elsize firstIndices memoryOffset
      (@offsetCconvertBase T C PtrT) pointerType view =
      .ok ⟨mul_int (sub_int viewFirst parentFirst) elementSize, parentConversion⟩) ∧
  (∀ {T P PtrT C : Type}
    (cconvert : PtrT → P → RResult C)
    (firstIndexView : JuliaLean.base.subarray.SubArray P T → RResult I64)
    (firstIndexParent elsize : P → RResult I64)
    (firstIndices : List JuliaLean.base.subarray.Index → RResult (List I64))
    (memoryOffset : P → List I64 → RResult I64)
    (pointerType : PtrT) (view : JuliaLean.base.subarray.SubArray P T)
    (indices : List I64) (delta : I64) (parentConversion : C),
    cconvert pointerType view.parent = .ok parentConversion →
    firstIndices view.indices = .ok indices → memoryOffset view.parent indices = .ok delta →
    @cconvertSubArray T P PtrT C cconvert (@checkcontiguousAbstract P Bool)
      firstIndexView firstIndexParent elsize firstIndices memoryOffset
      (@offsetCconvertBase T C PtrT) pointerType view = .ok ⟨delta, parentConversion⟩)

/-- Dense parents give reshaped arrays their ordinary column-major stride tuple. -/
def ReshapedContiguousStrides : Prop :=
  ∀ {T : Type} {N : Nat} {P MI : Type}
    (parentSize : P → RResult (List I64)) (parentStrides : P → RResult (List I64))
    (merge : List I64 → List I64 → RResult (I64 × I64 × I64))
    (ndims : P → RResult I64)
    (sizeToStrides : I64 → List I64 → RResult (List I64))
    (reshapedStrides : List I64 → I64 → I64 → I64 → I64 → List I64 → List I64 → RResult (List I64))
    (array : ReshapedArray T N P MI),
    stridesReshaped (fun a => checkcontiguousReshaped (@checkcontiguousDense P Bool) Bool a)
      parentSize parentStrides merge ndims sizeToStrides reshapedStrides array =
      sizeToStrides (JInt.lit .i64 1) (reshapedSize array).toList



/-- Adapt the rank-one merge method to the list interface used by `stridesReshaped`. -/
def mergeAdjacentDimOneLists (sizes strides : List I64) : RResult (I64 × I64 × I64) :=
  match sizes, strides with
  | [size], [stride] => .ok (mergeAdjacentDimOne (Vector.ofFn (fun _ : Fin 1 => size)) (Vector.ofFn (fun _ : Fin 1 => stride)))
  | _, _ => .error .argumentError

/-- A noncontiguous vector parent keeps its element stride after reshaping. -/
def ReshapedStridedVector : Prop :=
  ∀ {T : Type} {N : Nat} {P MI : Type}
    (parentSize : P → RResult (List I64)) (parentStrides : P → RResult (List I64))
    (ndims : P → RResult I64)
    (sizeToStrides : I64 → List I64 → RResult (List I64))
    (reshapedStrides : List I64 → I64 → I64 → I64 → I64 → List I64 → List I64 → RResult (List I64))
    (array : ReshapedArray T N P MI) (parentDimension parentStride : I64),
    parentSize array.parent = .ok [parentDimension] →
    parentStrides array.parent = .ok [parentStride] → ndims array.parent = .ok (JInt.lit .i64 1) →
    stridesReshaped (fun a => checkcontiguousReshaped (@checkcontiguousAbstract P Bool) Bool a)
      parentSize parentStrides mergeAdjacentDimOneLists ndims sizeToStrides reshapedStrides array =
      sizeToStrides parentStride (reshapedSize array).toList
/-! Nothing to promise:
reshapedArrayIteratorConstructor@20: Iterator construction and metadata only wrap or forward the parent iterator.
rsIterator@21: Iterator construction and metadata only wrap or forward the parent iterator.
reshapedIteratorLength@35: Iterator construction and metadata only wrap or forward the parent iterator.
reshapedIteratorEltype@36: Iterator construction and metadata only wrap or forward the parent iterator.
reshapeIntOrInd@122: This overload only converts or forwards arguments to the general reshape method.
reshapeShapeTuple@123: This overload only converts or forwards arguments to the general reshape method.
reshapeLegacyShapeTuple@126: This overload only converts or forwards arguments to the general reshape method.
reshapeIntegerTuple@127: This overload only converts or forwards arguments to the general reshape method.
reshapeDims@128: This overload only converts or forwards arguments to the general reshape method.
reshapeVectorColon@131: This overload only converts or forwards arguments to the general reshape method.
reshapeVectorColonTuple@132: This overload only converts or forwards arguments to the general reshape method.
reshapeIntVarargs@133: This overload only converts or forwards arguments to the general reshape method.
reshapeIntegerVarargs@134: This overload only converts or forwards arguments to the general reshape method.
reshapeIntegerColonVarargs@135: This overload only converts or forwards arguments to the general reshape method.
reshapeValEqual@186: These private rank-dispatch helpers do not define a separate public behavior.
reshapeValRank@187: These private rank-dispatch helpers do not define a separate public behavior.
rdimsTrailingMany@194: These private rank-dispatch helpers do not define a separate public behavior.
rdimsTrailingSingle@195: These private rank-dispatch helpers do not define a separate public behavior.
rdimsVal@196: These private rank-dispatch helpers do not define a separate public behavior.
rdimsEmptyEmpty@197: These private rank-dispatch helpers do not define a separate public behavior.
rdimsEmptyOne@198: These private rank-dispatch helpers do not define a separate public behavior.
rdimsEmptyMany@199: These private rank-dispatch helpers do not define a separate public behavior.
rdimsSingletonEmpty@200: These private rank-dispatch helpers do not define a separate public behavior.
rdimsManyEmpty@201: These private rank-dispatch helpers do not define a separate public behavior.
rdimsSingletonOne@202: These private rank-dispatch helpers do not define a separate public behavior.
rdimsSingletonMany@203: These private rank-dispatch helpers do not define a separate public behavior.
rdimsEqualRank@204: These private rank-dispatch helpers do not define a separate public behavior.
rdimsRecursive@205: These private rank-dispatch helpers do not define a separate public behavior.
reshapedSimilar@255: This metadata or alias method forwards the parent value or its metadata.
reshapedSimilarType@256: This metadata or alias method forwards the parent value or its metadata.
reshapedIndexStyle@257: This metadata or alias method forwards the parent value or its metadata.
reshapedParentIndices@259: This metadata or alias method forwards the parent value or its metadata.
reshapedElsize@260: This metadata or alias method forwards the parent value or its metadata.
reshapedUnaliascopy@262: This metadata or alias method forwards the parent value or its metadata.
reshapedDataids@263: This metadata or alias method forwards the parent value or its metadata.
mightAliasReshaped@265: This metadata or alias method forwards the parent value or its metadata.
mightAliasReshapedSub@267: This metadata or alias method forwards the parent value or its metadata.
mightAliasSubReshaped@268: This metadata or alias method forwards the parent value or its metadata.
offsetIfVec@277: This private offset helper only adapts the index before the documented access path.
offsetIfGeneral@278: This private offset helper only adapts the index before the documented access path.
unsafeGetindexReshapedScalar@316: This private scalar or tuple helper forwards the final parent access.
unsafeGetindexReshapedTuple@317: This private scalar or tuple helper forwards the final parent access.
cconvertReshaped@350: Pointer conversion on a ReshapedArray forwards directly to the parent.
unsafeConvertReshaped@351: Pointer conversion on a ReshapedArray forwards directly to the parent.
viewindexingSliceReshaped@355: These view-dispatch methods only select the linear index-style tag.
viewindexingReshapedRange@356: These view-dispatch methods only select the linear index-style tag.
computeStride1@357: These private range-stride helpers support the public stride calculation.
computeOffset1@358: These private range-stride helpers support the public stride calculation.
substridesReshapedRange@360: These private range-stride helpers support the public stride calculation.
reshapedStridesEmpty@433: These private stride-recursion and merge cases implement the public stride calculation.
reshapedStridesRecursive@437: These private stride-recursion and merge cases implement the public stride calculation.
mergeAdjacentDimEmpty@448: These private stride-recursion and merge cases implement the public stride calculation.
mergeAdjacentDimMany@450: These private stride-recursion and merge cases implement the public stride calculation.
mapReshapedArray@466: This method delegates mapping, iteration, folding, or membership to the parent.
iterateReshapedArray@468: This method delegates mapping, iteration, folding, or membership to the parent.
iterateReshapedArrayState@469: This method delegates mapping, iteration, folding, or membership to the parent.
mapfoldlReshaped@471: This method delegates mapping, iteration, folding, or membership to the parent.
mapfoldrReshaped@472: This method delegates mapping, iteration, folding, or membership to the parent.
inReshapedArray@474: This method delegates mapping, iteration, folding, or membership to the parent.
-/


namespace Round2

open JuliaLean JuliaLean.base.int JuliaLean.base.essentials JuliaLean.base.reshapedarray
open JuliaLean.base.tuple JuliaLean.base.operators JuliaLean.Proofs.base.reshapedarray

/-- Select the installed source-mirrored checked-dimension dispatcher. -/
def checkedArrayDimensions {N : Nat} (dims : Vector I64 N) : RResult I64 :=
  JuliaLean.Bindings.base.reshapedarray.checkedDimsArrayList dims.toList

/-- `ArrayValue.dims` represents the Julia Array header's `size` field. -/
def arrayHeaderSize {T : Type} {N : Nat} {Ref : Type}
    (a : ArrayValue T N Ref) : List I64 :=
  JuliaLean.base.essentials.sizeArray (fun header _ => header.dims.toList) a

/-- Bind the tuple product's variadic multiplication to the installed scalar methods. -/
def dimensionMultiply (values : List I64) : I64 :=
  match values with
  | [] => JuliaLean.base.tuple.prodEmpty
  | [x] => JuliaLean.base.operators.unaryMulNumber x
  | [x, y] => JuliaLean.base.int.binop JuliaLean.base.int.mul x y
  | x :: y :: z :: rest =>
      (JuliaLean.base.operators.naryOperator (Acc := fun _ : Unit => I64)
        (Elem := fun _ : Unit => I64)
        (fun (a b : I64) => JuliaLean.base.int.binop JuliaLean.base.int.mul a b)
        (fun (ab c : I64) => ⟨(), JuliaLean.base.int.binop JuliaLean.base.int.mul ab c⟩)
        (fun acc value => ⟨(), JuliaLean.base.int.binop JuliaLean.base.int.mul acc.2 value.2⟩)
        x y z (rest.map (fun value => ⟨(), value⟩))).2

/-- Select the installed `prod(::Tuple{})` and `prod(::Tuple{Int,Vararg{Int}})` methods. -/
def dimensionProduct (dims : List I64) : I64 :=
  match dims with
  | [] => JuliaLean.base.tuple.prodEmpty
  | _ :: _ => JuliaLean.base.tuple.prodIntTuple dimensionMultiply dims

/-- Interpret the tuple field primitive, including its actual bounds check. -/
def dimensionField (dims : List I64) (index : Nat) : RResult I64 :=
  (JuliaLean.base.tuple.getfield dims (Int.ofNat index)).mapError
    (fun _ => ReshapedError.boundsError)

/-- Bind Array length to its installed rank-one or generic size/product method. -/
def arrayHeaderLength {T : Type} {N : Nat} {Ref : Type}
    (a : ArrayValue T N Ref) : RResult I64 :=
  match a.dims.toList with
  | [_] => JuliaLean.base.essentials.lengthArray1
      (fun (header : ArrayValue T N Ref) (_ : String) => header.dims.toList)
      dimensionField a
  | _ => .ok (JuliaLean.base.essentials.lengthAbstract arrayHeaderSize dimensionProduct a)

/-- A Julia Array header has nonnegative dimensions and a representable element count. -/
def ValidArrayHeaderShape (dims : List I64) : Prop :=
  (∀ d ∈ dims, 0 ≤ d.val) ∧
  exactDimProduct dims ≤ IntTy.max .i64

/-- Requested dimensions also satisfy the pinned multidimensional extent limit. -/
def SupportedArrayShape (dims : List I64) : Prop :=
  ValidArrayHeaderShape dims ∧
  (dims.length ≤ 1 ∨ ∀ d ∈ dims, d.val < IntTy.max .i64)

/-- Array reshape succeeds exactly for supported shapes with the original element count, retaining the requested dimensions and storage handle.
Julia source: base/reshapedarray.jl:43-51; base/boot.jl:781-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/reshapedarray.jl:66-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ArrayReshapeDimensionsCorrect : Prop :=
  ∀ (T Ref : Type) (M N : Nat) (a : ArrayValue T M Ref) (dims : Vector I64 N),
    ValidArrayHeaderShape a.dims.toList →
    match JuliaLean.base.reshapedarray.reshapeArray
        checkedArrayDimensions arrayHeaderLength a dims with
    | .ok result =>
        SupportedArrayShape dims.toList ∧
        exactDimProduct dims.toList = exactDimProduct a.dims.toList ∧
        result.dims = dims ∧ result.ref = a.ref
    | .error _ =>
        ¬ (SupportedArrayShape dims.toList ∧
          exactDimProduct dims.toList = exactDimProduct a.dims.toList)

end Round2

end JuliaLean.Proofs.base.reshapedarray

namespace JuliaLean.ChatGPT.Batch4.Group22
open JuliaLean JuliaLean.base.int JuliaLean.base.reshapedarray
open JuliaLean.Proofs.base.reshapedarray

set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

theorem reshapeArray_success_fields
    {T : Type} {M N : Nat} {Ref : Type}
    (checkedDims : Vector I64 N → RResult I64)
    (length : ArrayValue T M Ref → RResult I64)
    (parent : ArrayValue T M Ref) (dims : Vector I64 N)
    (result : ArrayValue T N Ref)
    (h : reshapeArray checkedDims length parent dims = .ok result) :
    ∃ n, checkedDims dims = .ok n ∧ length parent = .ok n ∧
      result = ⟨parent.ref, dims⟩ := by
  cases hc : checkedDims dims with
  | error e => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeArray, hc] at h
  | ok n =>
    cases hl : length parent with
    | error e => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeArray, hc, hl] at h
    | ok actual =>
      by_cases heq : n = actual
      · subst actual
        have hr : (⟨parent.ref, dims⟩ : ArrayValue T N Ref) = result := by
          simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeArray, hc, hl] using h
        exact ⟨n, rfl, rfl, hr.symm⟩
      · simp [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeArray, hc, hl, heq, throw_dmrsa] at h

theorem reshapeAbstract_success_calls
    {P S R : Type} {N : Nat}
    (length : P → RResult I64) (checkedDims : Vector I64 N → RResult I64)
    (product : Vector I64 N → RResult I64)
    (indexStyle : P → RResult S)
    (construct : P × S → Vector I64 N → RResult R)
    (parent : P) (dims : Vector I64 N) (result : R)
    (h : reshapeAbstractArray length checkedDims (throwDmrs product) indexStyle
      construct parent dims = .ok result) :
    ∃ n style, checkedDims dims = .ok n ∧ length parent = .ok n ∧
      indexStyle parent = .ok style ∧ construct (parent, style) dims = .ok result := by
  cases hl : length parent with
  | error e => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeAbstractArray, hl] at h
  | ok n =>
    cases hc : checkedDims dims with
    | error e => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeAbstractArray, hl, hc] at h
    | ok requested =>
      by_cases heq : requested = n
      · subst requested
        cases hi : indexStyle parent with
        | error e => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeAbstractArray, hl, hc, hi] at h
        | ok style =>
          exact ⟨n, style, rfl, rfl, rfl, by simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeAbstractArray, hl, hc, hi] using h⟩
      · cases hp : product dims <;>
          simp [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeAbstractArray, hl, hc, heq, throwDmrs, hp] at h

theorem constructCartesian_success_fields
    {T : Type} {N : Nat} {P MI : Type}
    (size : P → RResult (List I64)) (front : List I64 → List I64)
    (toInt : I64 → RResult I64) (makeInverse : I64 → MI)
    (parent : P) (style : IndexStyle) (dims : Vector I64 N)
    (result : ReshapedArray T N P MI)
    (h : constructReshapedCartesian size (fun values => .ok (front values))
      toInt (fun value => .ok (makeInverse value)) (parent, style) dims = .ok result) :
    result.parent = parent ∧ result.dims = dims := by
  cases hs : size parent with
  | error e => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, constructReshapedCartesian, hs] at h
  | ok shape =>
    cases ha : (front shape).mapM (fun value => do
      let n ← toInt value
      pure (if n.val < 1 then JInt.lit .i64 1 else n)) with
    | error e =>
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at ha
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, constructReshapedCartesian, hs, ha] at h
    | ok adjusted =>
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at ha
      cases hm : adjusted.mapM (fun value => (.ok (makeInverse value) : RResult MI)) with
      | error e => simp [Bind.bind, Except.bind, Pure.pure, Except.pure, constructReshapedCartesian, hs, ha, hm] at h
      | ok inverses =>
        have hr : reshapedArrayConstructor parent dims inverses = result := by
          simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, constructReshapedCartesian, hs, ha, hm] using h
        subst result
        exact ⟨rfl, rfl⟩

/-- Successful shape checks retain the exact checked count and source storage. -/
theorem ReinterpretarraysReshapeCheckSound_proven : JuliaLean.Proofs.base.reshapedarray.ReshapeCheckSound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T M N Ref checkedDims length parent dims result laws h
    obtain ⟨n, hc, hl, hr⟩ := reshapeArray_success_fields checkedDims length parent dims result h
    subst result
    exact ⟨⟨n, hc, hl, laws dims n hc⟩, rfl, rfl⟩
  · intro T N P length checkedDims product indexStyle parent dims result laws hi h
    obtain ⟨n, style, hc, hl, hs, hresult⟩ :=
      reshapeAbstract_success_calls length checkedDims product indexStyle _ parent dims result h
    have hstyle : style = .linear := by simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, hi] using hs.symm
    subst style
    have hr : reshapedArrayConstructor parent dims [] = result := by
      simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, constructReshapedLinear] using hresult
    subst result
    exact ⟨⟨n, hc, hl, laws dims n hc⟩, rfl, rfl⟩
  · intro T N P length checkedDims product indexStyle parentRank parent dims result laws hi hRank h
    obtain ⟨n, style, hc, hl, hs, hresult⟩ :=
      reshapeAbstract_success_calls length checkedDims product indexStyle _ parent dims result h
    have hstyle : style = .cartesian := by simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, hi] using hs.symm
    subst style
    have hr : reshapedArrayConstructor parent dims [] = result := by
      simpa [Bind.bind, Except.bind, Pure.pure, Except.pure, constructReshapedCartesianZero] using hresult
    subst result
    exact ⟨⟨n, hc, hl, laws dims n hc⟩, rfl, rfl⟩
  · intro T N P MI length checkedDims product indexStyle parentRank size front toInt makeInverse
      parent dims result laws hi hRank h
    obtain ⟨n, style, hc, hl, hs, hresult⟩ :=
      reshapeAbstract_success_calls length checkedDims product indexStyle _ parent dims result h
    exact ⟨⟨n, hc, hl, laws dims n hc⟩,
      constructCartesian_success_fields size front toInt makeInverse parent style dims result hresult⟩

theorem reshape_exact_product_append (left right : List I64) :
    exactDimProduct (left ++ right) = exactDimProduct left * exactDimProduct right := by
  induction left with
  | nil => simp [exactDimProduct]
  | cons head tail ih => simp [exactDimProduct, ih, Int.mul_assoc]

theorem reshape_exact_product_nonnegative (dims : List I64)
    (h : dimensionsNonnegative dims) : 0 ≤ exactDimProduct dims := by
  induction dims with
  | nil => simp [exactDimProduct]
  | cons head tail ih =>
    have hh : 0 ≤ head.val := h head (by simp only [List.mem_cons, true_or])
    have ht : dimensionsNonnegative tail := fun d hd => h d (by simp only [List.mem_cons]; exact Or.inr hd)
    exact Int.mul_nonneg hh (ih ht)

theorem reshape_insert_nonnegative (pre post : List I64) (c : I64)
    (h : dimensionsNonnegative (pre ++ post)) (hc : 0 ≤ c.val) :
    dimensionsNonnegative (pre ++ [c] ++ post) := by
  intro d hd
  simp only [List.mem_append, List.mem_singleton] at hd
  rcases hd with (hd | hd) | hd
  · exact h d (List.mem_append_left post hd)
  · subst d; exact hc
  · exact h d (List.mem_append_right pre hd)

theorem reshape_exact_product_insert (pre post : List I64) (c : I64) :
    exactDimProduct (pre ++ [c] ++ post) = c.val * exactDimProduct (pre ++ post) := by
  simp [reshape_exact_product_append, exactDimProduct, Int.mul_assoc,
    Int.mul_comm, Int.mul_left_comm]

/-- The inferred colon dimension is nonnegative and restores the exact count. -/
theorem ReinterpretarraysReshapeColonSound_proven : JuliaLean.Proofs.base.reshapedarray.ReshapeColonSound := by
  intro len D checkedDims iszero divrem convertInt dims pre post result
    hlen hnonneg hchecked hzero hdivision hconvert h
  by_cases hzlen : len.val = 0
  · have hr : pre ++ [JInt.lit .i64 0] ++ post = result := by
      simpa [reshapeComputeSizeInt, hzlen, Bind.bind, Except.bind] using h
    subst result
    refine ⟨⟨JInt.lit .i64 0, rfl⟩, reshape_insert_nonnegative pre post _ hnonneg (by decide), ?_⟩
    rw [reshape_exact_product_insert]
    simp [JInt.lit, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits, hzlen]
  · cases hc : checkedDims (pre ++ post) with
    | error e =>
      simp [reshapeComputeSizeInt, hzlen, hc, Bind.bind, Except.bind] at h
    | ok product =>
      obtain ⟨_, hproduct⟩ := hchecked (pre ++ post) product hc
      have hpn : 0 ≤ product.val := hproduct ▸ reshape_exact_product_nonnegative (pre ++ post) hnonneg
      by_cases hpzero : product.val = 0
      · simp [reshapeComputeSizeInt, reshapeComputeNonempty, hzlen, hc, hzero product,
          hpzero, throw2, Bind.bind, Except.bind] at h
      · have hpp : 0 < product.val := by omega
        cases hd : divrem len product with
        | error e =>
          simp [reshapeComputeSizeInt, reshapeComputeNonempty, hzlen, hc, hzero product,
            hpzero, hd, Bind.bind, Except.bind] at h
        | ok pair =>
          rcases pair with ⟨quotient, remainder⟩
          by_cases hrzero : remainder.val = 0
          · cases hcv : convertInt quotient with
            | error e =>
              simp [reshapeComputeSizeInt, reshapeComputeNonempty, hzlen, hc, hzero product,
                hpzero, hd, hzero remainder, hrzero, hcv, Bind.bind, Except.bind] at h
            | ok c =>
              have hr : pre ++ [c] ++ post = result := by
                simpa [reshapeComputeSizeInt, reshapeComputeNonempty, hzlen, hc, hzero product,
                  hpzero, hd, hzero remainder, hrzero, hcv, Bind.bind, Except.bind] using h
              have hdiv := (hdivision len product quotient remainder hpp hd).1
              have hqprod : quotient.val * product.val = len.val := by omega
              have hqnonneg : 0 ≤ quotient.val :=
                Int.nonneg_of_mul_nonneg_left (hqprod ▸ hlen) hpp
              have hceq : c.val = quotient.val := hconvert quotient c hcv
              subst result
              refine ⟨⟨c, rfl⟩, reshape_insert_nonnegative pre post c hnonneg (hceq ▸ hqnonneg), ?_⟩
              rw [reshape_exact_product_insert, hproduct, hceq, hqprod]
          · simp [reshapeComputeSizeInt, reshapeComputeNonempty, hzlen, hc, hzero product,
              hpzero, hd, hzero remainder, hrzero, throw2, Bind.bind, Except.bind] at h

/-- A rejected assignment query stops before parent lookup. -/
theorem ReshapedarrayIsassignedBounds_proven : JuliaLean.Proofs.base.reshapedarray.ReshapedIsassignedBounds := by
  constructor
  · intro T N P checkbounds firstArray firstParent isassigned array index h
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, isassignedReshapedLinear, h]
  · intro T N P AX MI checkbounds axes sub2ind offset ind2sub isassigned array indices h
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, isassignedReshapedCartesian, h]

/-- Every successful Array reshape shares the original storage handle. -/
theorem ReshapedarrayArraySharesStorage_proven : JuliaLean.Proofs.base.reshapedarray.ReshapeArraySharesData := by
  constructor
  · intro T E M N Ref checkedDims length read array dims result index h
    obtain ⟨n, hc, hl, hr⟩ := reshapeArray_success_fields checkedDims length array dims result h
    subst result
    exact ⟨rfl, rfl, rfl⟩
  · intro T N P MI length array
    exact ⟨rfl, rfl, rfl⟩

/-- Every reshaped-range assignment dispatch selects the fixed range error. -/
theorem ReshapedarrayRangeAssignmentError_proven : JuliaLean.Proofs.base.reshapedarray.ReshapedRangeAssignmentError := by
  refine ⟨?_, ?_, ?_⟩
  · intro T N A V I array value index
    rfl
  · intro T N A V I array value indices
    rfl
  · intro T N A V I array value index
    rfl

/-- Dimension mismatch branches preserve their exception kind. -/
theorem ReshapedarrayDimensionErrors_proven : JuliaLean.Proofs.base.reshapedarray.ReshapeDimensionErrors := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro dims
    rfl
  · intro len dims
    rfl
  · intro D product length kind dims n h
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, throwDmrs, h]
  · intro T M N Ref checkedDims length array dims n actual hc hl hn
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, reshapeArray, hc, hl, hn, throw_dmrsa]
    rfl

/-- Pointer wrappers apply precisely the supplied byte-offset operations. -/
theorem ReshapedarrayPointerOffsets_proven : JuliaLean.Proofs.base.reshapedarray.ReshapedPointerOffsets := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T C PtrT pointerType innerOffset outerOffset conversion
    rfl
  · intro T C PtrT PtrS convert ptrAdd pointer addressT addressS pointerType conversion
      parentPointer adjusted result hc ha hp laws h
    exact (laws.2 adjusted result hp).trans (laws.1 parentPointer conversion.byteOffset adjusted ha)
  · intro T P PtrT PtrS firstIndexView firstIndexParent elsize firstIndices memoryOffset
      convert ptrAdd pointer addressT addressS pointerType view viewFirst parentFirst elementSize
      base shifted result hv hf he hc ha hp laws h
    exact (laws.2 shifted result hp).trans
      (laws.1 base (mul_int (sub_int viewFirst parentFirst) elementSize) shifted ha)
  · intro T P PtrT PtrS firstIndexView firstIndexParent elsize firstIndices memoryOffset
      convert ptrAdd pointer addressT addressS pointerType view indices delta base shifted result
      hi hd hc ha hp laws h
    exact (laws.2 shifted result hp).trans (laws.1 base delta shifted ha)
  · intro T P PtrT C cconvert firstIndexView firstIndexParent elsize firstIndices memoryOffset
      pointerType view viewFirst parentFirst elementSize parentConversion hc hv hp he
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, cconvertSubArray, checkcontiguousDense, offsetCconvertBase, hc, hv, hp, he]
  · intro T P PtrT C cconvert firstIndexView firstIndexParent elsize firstIndices memoryOffset
      pointerType view indices delta parentConversion hc hi hd
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, cconvertSubArray, checkcontiguousAbstract, offsetCconvertBase, hc, hi, hd]

/-- Contiguous storage immediately selects the ordinary stride helper. -/
theorem ReshapedarrayContiguousStrides_proven : JuliaLean.Proofs.base.reshapedarray.ReshapedContiguousStrides := by
  intro T N P MI parentSize parentStrides merge ndims sizeToStrides reshapedStrides array
  rfl

/-- The rank-one merge preserves the parent's element stride. -/
theorem ReshapedarrayVectorStrides_proven : JuliaLean.Proofs.base.reshapedarray.ReshapedStridedVector := by
  intro T N P MI parentSize parentStrides ndims sizeToStrides reshapedStrides array
    parentDimension parentStride hs ht hn
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, stridesReshaped, checkcontiguousReshaped, checkcontiguousAbstract, reshapedParent,
    hs, ht, hn, mergeAdjacentDimOneLists, mergeAdjacentDimOne, Vector.get]


end JuliaLean.ChatGPT.Batch4.Group22

namespace JuliaLean.ChatGPT.Batch4.Group22.ReshapeNative
open JuliaLean JuliaLean.base.int JuliaLean.base.reshapedarray
open JuliaLean.Proofs.base.reshapedarray
open JuliaLean.Proofs.base.reshapedarray.Round2
open JuliaLean.C

set_option maxRecDepth 2048
set_option linter.unusedSimpArgs false

theorem wrap_congr {a b : Int} (h : a % (18446744073709551616 : Int) = b % 18446744073709551616) :
    wrapInt .i64 a = wrapInt .i64 b := by
  change (a + 9223372036854775808) % 18446744073709551616 - 9223372036854775808 =
    (b + 9223372036854775808) % 18446744073709551616 - 9223372036854775808
  exact congrArg (fun r : Int => r - 9223372036854775808)
    (Int.add_emod_eq_add_emod_right 9223372036854775808 h)

theorem wrap_emod (z : Int) :
    wrapInt .i64 z % 18446744073709551616 = z % 18446744073709551616 := by
  change ((z + 9223372036854775808) % 18446744073709551616 - 9223372036854775808) %
    18446744073709551616 = z % 18446744073709551616
  rw [Int.emod_sub_emod, Int.add_sub_cancel]

theorem wrap_mul_left (a b : Int) :
    wrapInt .i64 (wrapInt .i64 a * b) = wrapInt .i64 (a * b) :=
  wrap_congr (by rw [Int.mul_emod, wrap_emod, ← Int.mul_emod])

theorem to_native_val (z : Int) :
    (toJInt .i64 (BitVec.ofInt 64 z)).val = wrapInt .i64 z := by
  change wrapInt .i64 (BitVec.ofInt 64 z).toInt = wrapInt .i64 z
  apply wrap_congr
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_emod

theorem native_mul_val (a b : I64) :
    (mul_int a b).val = wrapInt .i64 (a.val * b.val) := by
  simp only [mul_int, jlMulInt, fromJInt]
  rw [← BitVec.ofInt_mul]
  exact to_native_val _

theorem native_binop_mul (a b : I64) :
    JuliaLean.base.int.binop JuliaLean.base.int.mul a b = mul_int a b := by
  rfl

theorem native_mul_fits (a b : I64)
    (h : IntTy.min .i64 ≤ a.val * b.val ∧ a.val * b.val ≤ IntTy.max .i64) :
    (mul_int a b).val = a.val * b.val := by
  rw [native_mul_val, wrapInt_of_inRange .i64 _ h]

theorem native_ule_max (d : I64) :
    JuliaLean.base.int.ule_int JuliaLean.base.array.typemaxInt d =
      decide (¬ (0 ≤ d.val ∧ d.val < IntTy.max .i64)) := by
  change decide (9223372036854775807 ≤ (BitVec.ofInt 64 d.val).toNat) =
    decide (¬ (0 ≤ d.val ∧ d.val < 9223372036854775807))
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, BitVec.toNat_ofInt]
  have hd : -9223372036854775808 ≤ d.val ∧ d.val ≤ 9223372036854775807 := d.property
  change 9223372036854775807 ≤ (d.val % 18446744073709551616).toNat ↔
    ¬ (0 ≤ d.val ∧ d.val < 9223372036854775807)
  omega

open JuliaLean.base.operators

theorem afoldlFrom_append_local {τ σ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (pre suffix : List (Σ s : σ, Elem s)) (y : Σ t : τ, Acc t) :
    afoldlFrom op (pre ++ suffix) (pre.length + 1) suffix.length y =
      suffix.foldl op y := by
  induction suffix generalizing pre y with
  | nil => rfl
  | cons b bs ih =>
    have hstep : afoldlAt op y (pre ++ b :: bs) (pre.length + 1) = op y b := by
      simp [afoldlAt]
    simp only [List.length_cons, afoldlFrom, hstep, List.foldl_cons]
    have h := ih (pre ++ [b]) (op y b)
    simpa [List.append_assoc, List.length_append, Nat.add_assoc] using h

/-- All 32 early-return cases and the tail loop agree with heterogeneous left folding. -/
theorem afoldlMany_eq_foldl_local {τ σ : Type} {Acc : τ → Type} {Elem : σ → Type}
    (op : (Σ t : τ, Acc t) → (Σ s : σ, Elem s) → Σ t' : τ, Acc t')
    (a : Σ t : τ, Acc t) (bs : List (Σ s : σ, Elem s)) :
    afoldlMany op a bs = bs.foldl op a := by
  cases bs with
  | nil => rfl
  | cons b1 bs =>
    cases bs with
    | nil => rfl
    | cons b2 bs =>
      cases bs with
      | nil => rfl
      | cons b3 bs =>
        cases bs with
        | nil => rfl
        | cons b4 bs =>
          cases bs with
          | nil => rfl
          | cons b5 bs =>
            cases bs with
            | nil => rfl
            | cons b6 bs =>
              cases bs with
              | nil => rfl
              | cons b7 bs =>
                cases bs with
                | nil => rfl
                | cons b8 bs =>
                  cases bs with
                  | nil => rfl
                  | cons b9 bs =>
                    cases bs with
                    | nil => rfl
                    | cons b10 bs =>
                      cases bs with
                      | nil => rfl
                      | cons b11 bs =>
                        cases bs with
                        | nil => rfl
                        | cons b12 bs =>
                          cases bs with
                          | nil => rfl
                          | cons b13 bs =>
                            cases bs with
                            | nil => rfl
                            | cons b14 bs =>
                              cases bs with
                              | nil => rfl
                              | cons b15 bs =>
                                cases bs with
                                | nil => rfl
                                | cons b16 bs =>
                                  cases bs with
                                  | nil => rfl
                                  | cons b17 bs =>
                                    cases bs with
                                    | nil => rfl
                                    | cons b18 bs =>
                                      cases bs with
                                      | nil => rfl
                                      | cons b19 bs =>
                                        cases bs with
                                        | nil => rfl
                                        | cons b20 bs =>
                                          cases bs with
                                          | nil => rfl
                                          | cons b21 bs =>
                                            cases bs with
                                            | nil => rfl
                                            | cons b22 bs =>
                                              cases bs with
                                              | nil => rfl
                                              | cons b23 bs =>
                                                cases bs with
                                                | nil => rfl
                                                | cons b24 bs =>
                                                  cases bs with
                                                  | nil => rfl
                                                  | cons b25 bs =>
                                                    cases bs with
                                                    | nil => rfl
                                                    | cons b26 bs =>
                                                      cases bs with
                                                      | nil => rfl
                                                      | cons b27 bs =>
                                                        cases bs with
                                                        | nil => rfl
                                                        | cons b28 bs =>
                                                          cases bs with
                                                          | nil => rfl
                                                          | cons b29 bs =>
                                                            cases bs with
                                                            | nil => rfl
                                                            | cons b30 bs =>
                                                              cases bs with
                                                              | nil => rfl
                                                              | cons b31 bs =>
                                                                cases bs with
                                                                | nil => rfl
                                                                | cons b32 bs =>
                                                                  exact afoldlFrom_append_local op [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] (b32 :: bs) (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op (op a b1) b2) b3) b4) b5) b6) b7) b8) b9) b10) b11) b12) b13) b14) b15) b16) b17) b18) b19) b20) b21) b22) b23) b24) b25) b26) b27) b28) b29) b30) b31)


theorem fold_product_val (dims : List I64) (acc : I64) :
    (dims.foldl mul_int acc).val = wrapInt .i64 (acc.val * exactDimProduct dims) := by
  induction dims generalizing acc with
  | nil =>
    simp only [List.foldl_nil, exactDimProduct, Int.mul_one]
    exact (wrapInt_of_inRange .i64 acc.val acc.property).symm
  | cons d ds ih =>
    rw [List.foldl_cons, ih, native_mul_val, wrap_mul_left]
    simp only [exactDimProduct, Int.mul_assoc]

theorem sigma_fold_product (dims : List I64) (acc : I64) :
    ((dims.map fun d => (⟨(), d⟩ : Sigma (fun _ : Unit => I64))).foldl
      (fun (acc value : Sigma (fun _ : Unit => I64)) => (⟨(), mul_int acc.2 value.2⟩ : Sigma (fun _ : Unit => I64)))
      ⟨(), acc⟩) = ⟨(), dims.foldl mul_int acc⟩ := by
  induction dims generalizing acc with
  | nil => rfl
  | cons d ds ih =>
    simpa only [List.map_cons, List.foldl_cons, native_binop_mul] using ih (mul_int acc d)

theorem dimension_multiply_val (dims : List I64) :
    (dimensionMultiply dims).val = wrapInt .i64 (exactDimProduct dims) := by
  cases dims with
  | nil => rfl
  | cons a ds =>
    cases ds with
    | nil =>
      change a.val = wrapInt .i64 (a.val * 1)
      rw [Int.mul_one, wrapInt_of_inRange .i64 a.val a.property]
    | cons b ds =>
      cases ds with
      | nil =>
        change (JuliaLean.base.int.binop JuliaLean.base.int.mul a b).val = wrapInt .i64 (a.val * (b.val * 1))
        rw [native_binop_mul, native_mul_val, Int.mul_one]
      | cons c ds =>
        simp only [dimensionMultiply, naryOperator, afoldlMany_eq_foldl_local,
          native_binop_mul, sigma_fold_product, fold_product_val, native_mul_val,
          wrap_mul_left, exactDimProduct, Int.mul_assoc]

theorem dimension_product_val (dims : List I64) :
    (dimensionProduct dims).val = wrapInt .i64 (exactDimProduct dims) := by
  cases dims with
  | nil => rfl
  | cons a ds => exact dimension_multiply_val (a :: ds)

theorem array_header_length_value {T Ref : Type} {N : Nat} (a : ArrayValue T N Ref) :
    arrayHeaderLength a = .ok (dimensionProduct a.dims.toList) := by
  cases hd : a.dims.toList with
  | nil => simp only [arrayHeaderLength, hd, JuliaLean.base.essentials.lengthAbstract, arrayHeaderSize,
      JuliaLean.base.essentials.sizeArray, hd]
  | cons d ds =>
    cases ds with
    | nil =>
      simp [arrayHeaderLength, hd, JuliaLean.base.essentials.lengthArray1, dimensionField,
        JuliaLean.base.tuple.getfield, dimensionProduct, JuliaLean.base.tuple.prodIntTuple,
        dimensionMultiply, JuliaLean.base.operators.unaryMulNumber, Except.mapError]
    | cons d2 ds =>
      simp only [arrayHeaderLength, hd, JuliaLean.base.essentials.lengthAbstract, arrayHeaderSize,
        JuliaLean.base.essentials.sizeArray, hd]

open JuliaLean.base.array (checkedMulDimsLoop checkedSmulInt checkedMulDimsMany
  checkedMulDims2 checkedMulDims checkedDims typemaxInt)

def StrictDims (dims : List I64) : Prop :=
  ∀ d ∈ dims, 0 ≤ d.val ∧ d.val < IntTy.max .i64

def AccumInvariant (p : Int) (a : I64) (overflow zero : Bool) : Prop :=
  0 ≤ p ∧ a.val = wrapInt .i64 p ∧
  (zero = true → p = 0) ∧
  ((overflow = false ∨ zero = true) ↔ p ≤ IntTy.max .i64)

theorem accum_step (p : Int) (a d : I64) (overflow zero : Bool)
    (h : AccumInvariant p a overflow zero)
    (hd : 0 ≤ d.val ∧ d.val < IntTy.max .i64) :
    AccumInvariant (p * d.val) (checkedSmulInt a d).1
      (overflow || (checkedSmulInt a d).2) (zero || decide (d.val = 0)) := by
  rcases h with ⟨hp, ha, hz, hof⟩
  have hnonneg := Int.mul_nonneg hp hd.1
  refine ⟨hnonneg, ?_, ?_, ?_⟩
  · simp only [checkedSmulInt, native_mul_val, ha, wrap_mul_left]
  · intro hzero
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hzero
    rcases hzero with hzero | hzero
    · rw [hz hzero, Int.zero_mul]
    · rw [hzero, Int.mul_zero]
  · simp only [Bool.or_eq_false_iff, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · intro hresult
      rcases hresult with ⟨hov, hm⟩ | hzero | hdz
      · have hpmax : p ≤ IntTy.max .i64 := hof.mp (Or.inl hov)
        have hafit : a.val = p := by
          rw [ha, wrapInt_of_inRange .i64 p ⟨by change -9223372036854775808 ≤ p; omega, hpmax⟩]
        have hfits : IntTy.min .i64 ≤ p * d.val ∧ p * d.val ≤ IntTy.max .i64 := by
          simpa only [checkedSmulInt, Bool.not_eq_false', decide_eq_true_eq, hafit] using hm
        exact hfits.2
      · rw [hz hzero, Int.zero_mul]
        decide
      · rw [hdz, Int.mul_zero]
        decide
    · intro hprod
      by_cases hd0 : d.val = 0
      · exact Or.inr (Or.inr hd0)
      · have hd1 : 1 ≤ d.val := by omega
        have hple : p ≤ p * d.val := by
          have hm := Int.mul_le_mul_of_nonneg_left hd1 hp
          simpa only [Int.mul_one] using hm
        have hpmax : p ≤ IntTy.max .i64 := Int.le_trans hple hprod
        rcases hof.mpr hpmax with hov | hzero
        · left
          refine ⟨hov, ?_⟩
          have hafit : a.val = p := by
            rw [ha, wrapInt_of_inRange .i64 p ⟨by change -9223372036854775808 ≤ p; omega, hpmax⟩]
          simp only [checkedSmulInt, Bool.not_eq_false', decide_eq_true_eq, hafit]
          exact ⟨by change -9223372036854775808 ≤ p * d.val; omega, hprod⟩
        · exact Or.inr (Or.inl hzero)

theorem checked_loop_valid (dims : List I64) (a : I64) (p : Int) (overflow zero : Bool)
    (hinv : AccumInvariant p a overflow zero) (hdims : StrictDims dims) :
    (checkedMulDimsLoop dims a overflow false zero).1.val =
        wrapInt .i64 (p * exactDimProduct dims) ∧
    ((checkedMulDimsLoop dims a overflow false zero).2 = false ↔
        p * exactDimProduct dims ≤ IntTy.max .i64) := by
  induction dims generalizing a p overflow zero with
  | nil =>
    simp only [checkedMulDimsLoop, exactDimProduct, Int.mul_one]
    refine ⟨hinv.2.1, ?_⟩
    simpa only [Bool.false_or, Bool.and_eq_false_iff, Bool.not_eq_false'] using hinv.2.2.2
  | cons d ds ih =>
    have hd := hdims d (by simp only [List.mem_cons, true_or])
    have ht : StrictDims ds := fun x hx => hdims x (by simp only [List.mem_cons]; exact Or.inr hx)
    have hneg : JuliaLean.base.int.ule_int typemaxInt d = false := by
      rw [native_ule_max]
      simp only [decide_eq_false_iff_not, Decidable.not_not]
      exact hd
    have hs := accum_step p a d overflow zero hinv hd
    have hi := ih (checkedSmulInt a d).1 (p * d.val)
      (overflow || (checkedSmulInt a d).2) (zero || decide (d.val = 0)) hs ht
    simpa only [checkedMulDimsLoop, hneg, Bool.false_or, exactDimProduct, Int.mul_assoc] using hi

theorem checked_loop_rejects_invalid (dims : List I64) (a : I64) (overflow negative zero : Bool)
    (h : (checkedMulDimsLoop dims a overflow negative zero).2 = false) :
    negative = false ∧ StrictDims dims := by
  induction dims generalizing a overflow negative zero with
  | nil =>
    simp only [checkedMulDimsLoop, Bool.or_eq_false_iff] at h
    exact ⟨h.1, by intro d hd; cases hd⟩
  | cons d ds ih =>
    have hi := ih (checkedSmulInt a d).1 (overflow || (checkedSmulInt a d).2)
      (negative || JuliaLean.base.int.ule_int typemaxInt d) (zero || decide (d.val = 0)) h
    have hn := Bool.or_eq_false_iff.mp hi.1
    refine ⟨hn.1, ?_⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simpa only [native_ule_max, decide_eq_false_iff_not, Decidable.not_not] using hn.2
    · exact hi.2 x hx

theorem accum_initial (a : I64) (ha : 0 ≤ a.val) :
    AccumInvariant a.val a false false := by
  refine ⟨ha, (wrapInt_of_inRange .i64 a.val a.property).symm, ?_, ?_⟩
  · intro h; cases h
  · constructor
    · intro _; exact a.property.2
    · intro _; exact Or.inl rfl

theorem checked_many_iff (a : I64) (dims : List I64) :
    (checkedMulDimsMany a dims).2 = false ↔
      StrictDims (a :: dims) ∧ exactDimProduct (a :: dims) ≤ IntTy.max .i64 := by
  constructor
  · intro h
    have hf := checked_loop_rejects_invalid dims a false
      (JuliaLean.base.int.ule_int typemaxInt a) false h
    have ha : 0 ≤ a.val ∧ a.val < IntTy.max .i64 := by
      simpa only [native_ule_max, decide_eq_false_iff_not, Decidable.not_not] using hf.1
    have hs := checked_loop_valid dims a a.val false false (accum_initial a ha.1) hf.2
    refine ⟨?_, ?_⟩
    · intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact ha
      · exact hf.2 d hd
    · exact hs.2.mp (by simpa only [checkedMulDimsMany, hf.1] using h)
  · intro h
    have ha := h.1 a (by simp only [List.mem_cons, true_or])
    have ht : StrictDims dims := fun d hd => h.1 d (by simp only [List.mem_cons]; exact Or.inr hd)
    have hn : JuliaLean.base.int.ule_int typemaxInt a = false := by
      simpa only [native_ule_max, decide_eq_false_iff_not, Decidable.not_not] using ha
    have hs := checked_loop_valid dims a a.val false false (accum_initial a ha.1) ht
    simpa only [checkedMulDimsMany, hn] using hs.2.mpr h.2

theorem checked_many_val (a : I64) (dims : List I64) (h : StrictDims (a :: dims)) :
    (checkedMulDimsMany a dims).1.val = wrapInt .i64 (exactDimProduct (a :: dims)) := by
  have ha := h a (by simp only [List.mem_cons, true_or])
  have ht : StrictDims dims := fun d hd => h d (by simp only [List.mem_cons]; exact Or.inr hd)
  have hn : JuliaLean.base.int.ule_int typemaxInt a = false := by
    simpa only [native_ule_max, decide_eq_false_iff_not, Decidable.not_not] using ha
  have hs := checked_loop_valid dims a a.val false false (accum_initial a ha.1) ht
  simpa only [checkedMulDimsMany, hn, exactDimProduct] using hs.1

theorem checked_two_iff (a b : I64) :
    (checkedMulDims2 a b).2 = false ↔
      StrictDims [a, b] ∧ exactDimProduct [a, b] ≤ IntTy.max .i64 := by
  simp only [checkedMulDims2, checkedSmulInt, Bool.or_eq_false_iff, native_ule_max,
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, Decidable.not_not]
  constructor
  · rintro ⟨⟨hfits, ha⟩, hb⟩
    refine ⟨?_, ?_⟩
    · intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ha
      · exact hb
    · simpa only [exactDimProduct, Int.mul_one] using hfits.2
  · intro h
    have ha := h.1 a (by simp only [List.mem_cons, true_or])
    have hb := h.1 b (by simp only [List.mem_cons, List.not_mem_nil, or_false, or_true])
    have hp : 0 ≤ a.val * b.val := Int.mul_nonneg ha.1 hb.1
    refine ⟨⟨⟨?_, ?_⟩, ha⟩, hb⟩
    · change -9223372036854775808 ≤ a.val * b.val
      omega
    · simpa only [exactDimProduct, Int.mul_one] using h.2

theorem exact_product_nonneg (dims : List I64)
    (h : ∀ d ∈ dims, 0 ≤ d.val) : 0 ≤ exactDimProduct dims := by
  induction dims with
  | nil => decide
  | cons d ds ih =>
    exact Int.mul_nonneg (h d (by simp only [List.mem_cons, true_or]))
      (ih fun x hx => h x (by simp only [List.mem_cons]; exact Or.inr hx))

theorem checked_list_iff (dims : List I64) (hsize : 2 ≤ dims.length) :
    (checkedMulDims dims).2 = false ↔
      StrictDims dims ∧ exactDimProduct dims ≤ IntTy.max .i64 := by
  cases dims with
  | nil => simp only [List.length_nil] at hsize; omega
  | cons a ds =>
    cases ds with
    | nil => simp only [List.length_cons, List.length_nil] at hsize; omega
    | cons b ds =>
      cases ds with
      | nil => exact checked_two_iff a b
      | cons c ds => exact checked_many_iff a (b :: c :: ds)

theorem checked_list_val (dims : List I64) (hsize : 2 ≤ dims.length)
    (h : (checkedMulDims dims).2 = false) :
    (checkedMulDims dims).1.val = exactDimProduct dims := by
  have hs := (checked_list_iff dims hsize).mp h
  have hp : IntTy.min .i64 ≤ exactDimProduct dims := by
    have hnonneg := exact_product_nonneg dims (fun d hd => (hs.1 d hd).1)
    change -9223372036854775808 ≤ exactDimProduct dims
    omega
  have hw : (checkedMulDims dims).1.val = wrapInt .i64 (exactDimProduct dims) := by
    cases dims with
    | nil => simp only [List.length_nil] at hsize; omega
    | cons a ds =>
      cases ds with
      | nil => simp only [List.length_cons, List.length_nil] at hsize; omega
      | cons b ds =>
        cases ds with
        | nil =>
          simp only [checkedMulDims, checkedMulDims2, checkedSmulInt, native_mul_val,
            exactDimProduct, Int.mul_one]
        | cons c ds => exact checked_many_val a (b :: c :: ds) hs.1
  rw [hw, wrapInt_of_inRange .i64 _ ⟨hp, hs.2⟩]

def NativeAccepted (dims : List I64) : Prop :=
  dims.length ≤ 1 ∨ (StrictDims dims ∧ exactDimProduct dims ≤ IntTy.max .i64)

theorem checked_dims_many_equation (dims : List I64) (hsize : 2 ≤ dims.length) :
    JuliaLean.Bindings.base.reshapedarray.checkedDimsArrayList dims =
      if (checkedMulDims dims).2 then .error .argumentError
      else .ok (checkedMulDims dims).1 := by
  cases dims with
  | nil => simp only [List.length_nil] at hsize; omega
  | cons a ds =>
    cases ds with
    | nil => simp only [List.length_cons, List.length_nil] at hsize; omega
    | cons b ds =>
      change (JuliaLean.base.array.checkedDimsMany (m := Except JuliaLean.base.array.Error)
        (a :: b :: ds)).mapError _ = _
      cases hf : (checkedMulDims (a :: b :: ds)).2 <;>
        simp [JuliaLean.base.array.checkedDimsMany, hf, Bind.bind, Except.bind,
          Pure.pure, Except.pure, Except.mapError]
      rfl

theorem checked_dims_list_spec (dims : List I64) :
    match JuliaLean.Bindings.base.reshapedarray.checkedDimsArrayList dims with
    | .ok n => n.val = exactDimProduct dims ∧ NativeAccepted dims
    | .error _ => ¬ NativeAccepted dims := by
  by_cases hsmall : dims.length ≤ 1
  · cases dims with
    | nil =>
      change (1 : Int) = 1 ∧ NativeAccepted []
      exact ⟨rfl, Or.inl (by decide)⟩
    | cons d ds =>
      cases ds with
      | nil =>
        change d.val = d.val * 1 ∧ NativeAccepted [d]
        exact ⟨(Int.mul_one _).symm, Or.inl (by change (1 : Nat) ≤ 1; decide)⟩
      | cons e es => simp only [List.length_cons] at hsmall; omega
  · have hsize : 2 ≤ dims.length := by omega
    rw [checked_dims_many_equation dims hsize]
    cases hf : (checkedMulDims dims).2 with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      exact ⟨checked_list_val dims hsize hf, Or.inr ((checked_list_iff dims hsize).mp hf)⟩
    | true =>
      simp only [ite_true]
      intro h
      rcases h with h | h
      · exact hsmall h
      · have heq := (checked_list_iff dims hsize).mpr h
        rw [hf] at heq
        cases heq

theorem native_checked_dimensions_spec {N : Nat} (dims : Vector I64 N) :
    match Round2.checkedArrayDimensions dims with
    | .ok n => n.val = exactDimProduct dims.toList ∧
        (dims.toList.length ≤ 1 ∨ ((∀ d ∈ dims.toList, 0 ≤ d.val ∧ d.val < IntTy.max .i64) ∧
          exactDimProduct dims.toList ≤ IntTy.max .i64))
    | .error _ => ¬ (dims.toList.length ≤ 1 ∨ ((∀ d ∈ dims.toList, 0 ≤ d.val ∧ d.val < IntTy.max .i64) ∧
          exactDimProduct dims.toList ≤ IntTy.max .i64)) :=
  checked_dims_list_spec dims.toList

theorem native_array_header_length_spec {T Ref : Type} {N : Nat}
    (a : ArrayValue T N Ref) (h : Round2.ValidArrayHeaderShape a.dims.toList) :
    ∃ n, Round2.arrayHeaderLength a = .ok n ∧ n.val = exactDimProduct a.dims.toList := by
  refine ⟨dimensionProduct a.dims.toList, array_header_length_value a, ?_⟩
  rw [dimension_product_val]
  apply wrapInt_of_inRange
  refine ⟨?_, h.2⟩
  have hp := exact_product_nonneg a.dims.toList h.1
  change -9223372036854775808 ≤ exactDimProduct a.dims.toList
  omega

end JuliaLean.ChatGPT.Batch4.Group22.ReshapeNative


namespace JuliaLean.ChatGPT.Batch4.Group22.ReshapeNative
open JuliaLean JuliaLean.base.reshapedarray
open JuliaLean.Proofs.base.reshapedarray
open JuliaLean.Proofs.base.reshapedarray.Round2

 theorem assembly_product_nonnegative (dims : List I64)
    (hDims : ∀ d ∈ dims, 0 ≤ d.val) : 0 ≤ exactDimProduct dims := by
  induction dims with
  | nil => change (0 : Int) ≤ 1; omega
  | cons d ds ih =>
    change 0 ≤ d.val * exactDimProduct ds
    exact Int.mul_nonneg (hDims d (List.mem_cons_self ..))
      (ih (fun e he => hDims e (List.mem_cons_of_mem _ he)))

 theorem assembly_short_dimensions_nonnegative (dims : List I64)
    (hLen : dims.length ≤ 1) (hProduct : 0 ≤ exactDimProduct dims) :
    ∀ d ∈ dims, 0 ≤ d.val := by
  cases dims with
  | nil => intro d hd; cases hd
  | cons d ds =>
    have hEmpty : ds = [] := by
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_cons] at hLen
      omega
    subst ds
    simp only [exactDimProduct, Int.mul_one] at hProduct
    intro e he
    have heq : e = d := List.mem_singleton.mp he
    subst e
    exact hProduct

 theorem array_reshape_dimensions_assembly
    (hChecked : ∀ {N : Nat} (dims : Vector I64 N),
      match checkedArrayDimensions dims with
      | .ok n =>
          n.val = exactDimProduct dims.toList ∧
          (dims.toList.length ≤ 1 ∨
            ((∀ d ∈ dims.toList, 0 ≤ d.val ∧ d.val < IntTy.max .i64) ∧
              exactDimProduct dims.toList ≤ IntTy.max .i64))
      | .error _ =>
          ¬ (dims.toList.length ≤ 1 ∨
            ((∀ d ∈ dims.toList, 0 ≤ d.val ∧ d.val < IntTy.max .i64) ∧
              exactDimProduct dims.toList ≤ IntTy.max .i64)))
    (hLength : ∀ {T Ref : Type} {N : Nat} (a : ArrayValue T N Ref),
      ValidArrayHeaderShape a.dims.toList →
      ∃ n, arrayHeaderLength a = .ok n ∧ n.val = exactDimProduct a.dims.toList) :
    ArrayReshapeDimensionsCorrect := by
  intro T Ref M N a dims hHeader
  obtain ⟨actual, hActual, hActualVal⟩ := hLength a hHeader
  have hParentNonnegative := assembly_product_nonnegative a.dims.toList hHeader.1
  have hc := hChecked dims
  cases hCheck : checkedArrayDimensions dims with
  | error err =>
    simp only [hCheck] at hc
    have hRun : reshapeArray checkedArrayDimensions arrayHeaderLength a dims = .error err := by
      simp only [reshapeArray, hCheck, Bind.bind, Except.bind]
    rw [hRun]
    intro hGood
    apply hc
    rcases hGood.1.2 with hShort | hStrict
    · exact Or.inl hShort
    · exact Or.inr ⟨fun d hd => ⟨hGood.1.1.1 d hd, hStrict d hd⟩, hGood.1.1.2⟩
  | ok count =>
    simp only [hCheck] at hc
    by_cases hSame : count = actual
    · subst count
      have hRun : reshapeArray checkedArrayDimensions arrayHeaderLength a dims =
          .ok ⟨a.ref, dims⟩ := by
        simp [reshapeArray, hCheck, hActual, Bind.bind, Except.bind]
      rw [hRun]
      have hProduct : exactDimProduct dims.toList = exactDimProduct a.dims.toList :=
        hc.1.symm.trans hActualVal
      refine ⟨?_, hProduct, rfl, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rcases hc.2 with hShort | hStrict
        · apply assembly_short_dimensions_nonnegative dims.toList hShort
          rw [hProduct]
          exact hParentNonnegative
        · exact fun d hd => (hStrict.1 d hd).1
      · rw [hProduct]
        exact hHeader.2
      · rcases hc.2 with hShort | hStrict
        · exact Or.inl hShort
        · exact Or.inr (fun d hd => (hStrict.1 d hd).2)
    · have hRun : reshapeArray checkedArrayDimensions arrayHeaderLength a dims =
          .error .dimensionMismatch := by
        simp [reshapeArray, hCheck, hActual, hSame, Bind.bind, Except.bind, throw_dmrsa]
        rfl
      rw [hRun]
      intro hGood
      apply hSame
      apply Subtype.ext
      exact hc.1.trans (hGood.2.trans hActualVal.symm)

end JuliaLean.ChatGPT.Batch4.Group22.ReshapeNative

namespace JuliaLean.ChatGPT.Batch4.Group22

/-- The complete native Array reshape contract, including all ranks, zero
positions, intermediate overflow, negative extents, and the multidimensional
strict extent limit. -/
theorem ReinterpretarraysReshapeTypemaxDim_proven : JuliaLean.Proofs.base.reshapedarray.Round2.ArrayReshapeDimensionsCorrect := by
  exact ReshapeNative.array_reshape_dimensions_assembly
    (fun {N} dims => ReshapeNative.native_checked_dimensions_spec dims)
    (fun {T Ref N} a ha => ReshapeNative.native_array_header_length_spec a ha)

end JuliaLean.ChatGPT.Batch4.Group22

namespace JuliaLean.Proofs.base.reshapedarray

open JuliaLean JuliaLean.base.reshapedarray

/-- The pinned checked_dims rejection domain for two or more native dimensions.
Zero dimensions do not excuse a negative, oversized or overflowing dimension product. -/
def InvalidNativeDimensions (dims : List I64) : Prop :=
  2 ≤ dims.length ∧
    ¬ ((∀ d ∈ dims, 0 ≤ d.val ∧ d.val < IntTy.max .i64) ∧
      exactDimProduct dims ≤ IntTy.max .i64)

/-- Shape-count mismatches and invalid colon inference raise DimensionMismatch.
Native checked_dims rejects invalid products with ArgumentError before either Array reshape
method compares lengths or mutates the header. Other callee failures retain their error kind.
Julia source: base/reshapedarray.jl:38-62,138-177,227-229;
base/boot.jl:781-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027 -/
def FullReshapeDimensionErrors : Prop :=
  ReshapeDimensionErrors ∧
  (∀ {N : Nat} (dims : Vector I64 N), InvalidNativeDimensions dims.toList →
    Round2.checkedArrayDimensions dims = .error .argumentError) ∧
  (∀ {T Ref : Type} {M N : Nat} (a : ArrayValue T M Ref)
      (dims : Vector I64 N) (e : ReshapedError),
    Round2.checkedArrayDimensions dims = .error e →
    reshapeArray Round2.checkedArrayDimensions Round2.arrayHeaderLength a dims = .error e) ∧
  (∀ {T Ref : Type} {N : Nat} (a : ArrayValue T N Ref) (dims : Vector I64 N)
      (setfield : ArrayValue T N Ref → Vector I64 N → RResult Unit) (e : ReshapedError),
    Round2.checkedArrayDimensions dims = .error e →
    reshapeBang Round2.checkedArrayDimensions Round2.arrayHeaderLength setfield a dims = .error e) ∧
  (∀ {T Ref : Type} {N : Nat} (a : ArrayValue T N Ref) (dims : Vector I64 N)
      (setfield : ArrayValue T N Ref → Vector I64 N → RResult Unit) (n actual : I64),
    Round2.checkedArrayDimensions dims = .ok n →
    Round2.arrayHeaderLength a = .ok actual → n.val ≠ actual.val →
    reshapeBang Round2.checkedArrayDimensions Round2.arrayHeaderLength setfield a dims =
      .error .dimensionMismatch) ∧
  (∀ {D N : Type} (iszero : N → RResult Bool)
      (divrem : N → N → RResult (N × N)) (len product : N) (dims : D),
    (iszero product = .ok true →
      reshapeComputeNonempty iszero divrem len dims product = .error .dimensionMismatch) ∧
    (∀ q r, iszero product = .ok false → divrem len product = .ok (q, r) →
      iszero r = .ok false →
      reshapeComputeNonempty iszero divrem len dims product = .error .dimensionMismatch)) ∧
  (∀ {D : Type} (compute : I64 → D → I64 → RResult I64)
      (convert : I64 → RResult I64) (len : I64) (dims : D) (pre post : List I64)
      (e : ReshapedError),
    len.val ≠ 0 →
    JuliaLean.Bindings.base.reshapedarray.checkedDimsArrayList (pre ++ post) = .error e →
    reshapeComputeSizeInt JuliaLean.Bindings.base.reshapedarray.checkedDimsArrayList
      compute convert len dims pre post = .error e) ∧
  (∀ {D N : Type} (product : List N → RResult N) (iszero : N → RResult Bool)
      (promote : N → N → RResult (N × N))
      (divrem : N → N → RResult (N × N)) (len pr : N) (dims : D) (pre post : List N),
    product (pre ++ post) = .ok pr → iszero len = .ok false →
    (iszero pr = .ok true ∨
      ∃ q r, iszero pr = .ok false ∧ divrem len pr = .ok (q, r) ∧ iszero r = .ok false) →
    reshapeComputeSizeGeneric product iszero promote (reshapeComputeNonempty iszero divrem)
      len dims pre post = .error .dimensionMismatch) ∧
  (∀ {A D S L : Type} (isColon : D → Bool) (promote : D → RResult D)
      (before after : List D → RResult (List D)) (anyColon : List D → Bool)
      (length : A → RResult L) (compute : L → List D → List D → List D → RResult S)
      (a : A) (raw dims pre post : List D),
    raw.mapM (fun d => if isColon d then .ok d else promote d) = .ok dims →
    before dims = .ok pre → after dims = .ok post → anyColon post = true →
    reshapeUncolon isColon promote before after anyColon length compute a raw =
      .error .dimensionMismatch)

theorem fullReshapeDimensionErrors : FullReshapeDimensionErrors := by
  refine ⟨JuliaLean.ChatGPT.Batch4.Group22.ReshapedarrayDimensionErrors_proven,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N dims h
    unfold Round2.checkedArrayDimensions
    rw [JuliaLean.ChatGPT.Batch4.Group22.ReshapeNative.checked_dims_many_equation dims.toList h.1]
    have hbad : (JuliaLean.base.array.checkedMulDims dims.toList).2 = true := by
      cases he : (JuliaLean.base.array.checkedMulDims dims.toList).2 with
      | false =>
        exact False.elim (h.2
          ((JuliaLean.ChatGPT.Batch4.Group22.ReshapeNative.checked_list_iff dims.toList h.1).mp he))
      | true => rfl
    simp only [hbad, ite_true]
  · intro T Ref M N a dims e h
    simp [reshapeArray, h, Bind.bind, Except.bind]
  · intro T Ref N a dims setfield e h
    simp [reshapeBang, h, Bind.bind, Except.bind]
  · intro T Ref N a dims setfield n actual hc hl hne
    have hn : (n != actual) = true := by
      cases n; cases actual
      simpa using hne
    simp [reshapeBang, hc, hl, hn, throw_dmrsa, Bind.bind, Except.bind]
    rfl
  · intro D N iszero divrem len product dims
    constructor
    · intro h
      simp [reshapeComputeNonempty, h, throw2, Bind.bind, Except.bind]
    · intro q r hp hd hr
      simp [reshapeComputeNonempty, hp, hd, hr, throw2, Bind.bind, Except.bind]
  · intro D compute convert len dims pre post e hn hc
    simp [reshapeComputeSizeInt, hn, hc, Bind.bind, Except.bind]
  · intro D N product iszero promote divrem len pr dims pre post hp hl hbad
    rcases hbad with hz | ⟨q, r, hz, hd, hr⟩
    · simp [reshapeComputeSizeGeneric, hp, hl, reshapeComputeNonempty, hz, throw2,
        Bind.bind, Except.bind]
    · simp [reshapeComputeSizeGeneric, hp, hl, reshapeComputeNonempty, hz, hd, hr, throw2,
        Bind.bind, Except.bind]
  · intro A D S L isColon promote before after anyColon length compute a raw dims pre post hm hb ha hc
    simp [reshapeUncolon, hm, hb, ha, hc, throw1, Bind.bind, Except.bind]
open JuliaLean.Registry
def entries : List Entry := [
  { id := "reinterpretarrays-reshape-check-sound", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape(::Array{T,M}, ::NTuple{N,Int})", "_reshape(::AbstractArray,::Dims)",
      "__reshape(::AbstractArray,::IndexStyle)", "Core.checked_dims"],
    statement := "Successful reshape checks nonnegative dimensions and their exact product against the parent length, and retains the source storage and requested shape.",
    source := "base/reshapedarray.jl:43-50,221-251; reshape docstring lines 66-79; Core.checked_dims contract",
    status := .proven, prop := ``ReshapeCheckSound, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ReinterpretarraysReshapeCheckSound_proven },
  { id := "reinterpretarrays-reshape-colon-sound", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape(::AbstractArray,::Tuple{Vararg{Union{Integer,Colon}}})", "_reshape_uncolon",
      "_reshape_uncolon_computesize(Int)", "_reshape_uncolon_computesize_nonempty"],
    statement := "For a valid single-colon shape, the inferred nonnegative dimension makes the exact dimension product equal the parent length.",
    source := "base/reshapedarray.jl:75-80,143-177; reshape docstring",
    status := .proven, prop := ``ReshapeColonSound, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ReinterpretarraysReshapeColonSound_proven },
  { id := "reinterpretarrays-reshape-typemax-dim", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape(::Array{T,M},::NTuple{N,Int})", "_reshape(::AbstractArray,::Dims)",
      "Core.checked_dims"],
    statement := "Corrected complete Array-overload contract: for every Array element type/rank/storage representation with a nonnegative representable header shape, and every requested Int dimension tuple, reshape succeeds iff dimensions are nonnegative, their exact product is representable and equals the parent count, and every extent of a multidimensional tuple is strictly below typemax(Int); successful results retain requested dimensions and the storage handle. This covers zero dimensions in every position, intermediate overflow followed by zero, negative dimensions, empty/rank-zero shapes and mismatches, with no success assumption or arbitrary small-size cutoff.",
    source := "base/reshapedarray.jl:43-51; base/boot.jl:781-818; docs: base/reshapedarray.jl:66-79",
    status := .proven, prop := ``Round2.ArrayReshapeDimensionsCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ReinterpretarraysReshapeTypemaxDim_proven },
  { id := "memsafety-reshapedarray-ind2sub", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["isassigned(::ReshapedArray,::Int...)", "_unsafe_getindex(::ReshapedArray,::Int...)",
      "_unsafe_setindex!(::ReshapedArray,::Int...)"],
    statement := "A checked Cartesian access converts its linear index with the stored multiplicative inverses and yields parent coordinates within every parent axis.",
    source := "base/reshapedarray.jl:235-241,286-292,310-315,335-340; parent shape and inverse invariants",
    status := .todo, prop := ``MemsafetyReshapedArrayInd2sub, thm := none, notes := "Arbitrary lastAxis callback is unconstrained and empty-multiplier dispatch needs review; no full-domain proof or Julia witness." },
  { id := "memsafety-reshapedarray-indexing", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["isassigned(::ReshapedArrayLF,::Int)", "getindex(::ReshapedArrayLF,::Int)",
      "setindex!(::ReshapedArrayLF,::Int)", "getindex(::ReshapedArray,::ReshapedIndex)",
      "setindex!(::ReshapedArray,::ReshapedIndex)"],
    statement := "The checked linear path translates by the source and parent axis origins; ReshapedIndex access uses only its stored, parent-checked index.",
    source := "base/reshapedarray.jl:280-306,319-333; equal length and explicit parent bounds checks",
    status := .todo, prop := ``MemsafetyReshapedArrayIndexing, thm := none,
    notes := "Generic assignment conjunct quantifies over Monad without its equations. Concrete partial read/assignment helpers cannot settle full conjunction." },
  { id := "arraycov-reshaped-iterator-exhaustion", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["iterate(::ReshapedArrayIterator,i...)", "length(::ReshapedArrayIterator)"],
    statement := "When the parent iterator is exhausted, the wrapper returns normal iteration exhaustion rather than throwing a MethodError.",
    source := "base/reshapedarray.jl:31-36; Julia iteration protocol",
    status := .todo, prop := ``ReshapedIteratorExhaustion, thm := none,
    notes := "Frozen internal iterator model disagrees with exhaustion promise, but public eachindex dispatch is disabled. Existing internal-constructor repro is preserved, not accepted as a public runtime refutation." },
  { id := "reshapedarray-array-shares-storage", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape(::Array{T,M},::NTuple{N,Int})", "ReshapedArray(parent,dims,mi)",
      "__reshape(::AbstractArray,::IndexStyle)"],
    statement := "Every successful reshape preserves the parent data observed at every linear position and stores the requested dimensions.",
    source := "base/reshapedarray.jl:43-50,235-251; reshape docstring lines 70-79",
    status := .proven, prop := ``ReshapeArraySharesData, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ReshapedarrayArraySharesStorage_proven },
  { id := "reshapedarray-range-assignment-error", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["setindex!(::ReshapedRange,::Int)", "setindex!(::ReshapedRange,::Int...)", "_rs_setindex!_err"],
    statement := "All indexed assignments to a reshaped range raise ErrorException instead of attempting to mutate immutable range storage.",
    source := "base/reshapedarray.jl:342-348; error explains to collect first",
    status := .proven, prop := ``ReshapedRangeAssignmentError, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ReshapedarrayRangeAssignmentError_proven },
  { id := "reshapedarray-dimension-errors", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["throw_dmrsa", "throw1", "throw2", "_throw_dmrs", "reshape(::Array)", "reshape!(::Array)", "_reshape_uncolon", "_reshape_uncolon_computesize", "_reshape_uncolon_computesize_nonempty"],
    statement := "Array reshape and reshape! propagate checked-dimension errors before comparing lengths or mutating the header; invalid native products raise ArgumentError, while length mismatches, multiple colons, zero divisors and indivisible nonempty colon shapes raise DimensionMismatch.",
    source := "base/reshapedarray.jl:38-62,138-177,227-229; base/boot.jl:781-818",
    status := .proven, prop := ``FullReshapeDimensionErrors, thm := some ``fullReshapeDimensionErrors },
  { id := "reshapedarray-pointer-offsets", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["unsafe_convert(::Type{Ptr<S>},::SubArray)", "cconvert(::Type{Ptr<S>},::SubArray)",
      "_offset_cconvert", "unsafe_convert(::Type{Ptr<S>},::OffsetCConvert)"],
    statement := "For a contiguous parent, a strided SubArray pointer advances by the first-index displacement times element size; nested offsets add to the stored byte offset.",
    source := "base/reshapedarray.jl:368-400; pointer conversion and view-offset invariants",
    status := .proven, prop := ``ReshapedPointerOffsets, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ReshapedarrayPointerOffsets_proven },
  { id := "reshapedarray-contiguous-strides", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["strides(::ReshapedArray)", "_checkcontiguous(::Type{Bool},::ReshapedArray)",
      "_checkcontiguous(::Type{Bool},::DenseArray)"],
    statement := "A ReshapedArray over contiguous dense storage reports the standard column-major strides for its stored dimensions.",
    source := "base/reshapedarray.jl:417-431; strides interface and dense contiguity invariant",
    status := .todo, prop := ``ReshapedContiguousStrides, thm := none, notes := "Prop forwards an arbitrary sizeToStrides callback without requiring the standard column-major strides promised by prose." },
  { id := "reshapedarray-isassigned-bounds", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["isassigned(::ReshapedArrayLF,::Int)", "isassigned(::ReshapedArray,::Int...)"],
    statement := "An out-of-bounds assignment query returns false without querying the parent array.",
    source := "base/reshapedarray.jl:280-292; checked isassigned contract",
    status := .proven, prop := ``ReshapedIsassignedBounds, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ReshapedarrayIsassignedBounds_proven },
  { id := "reshapedarray-assignment-returns-value", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["setindex!(::ReshapedArrayLF,::Int)", "setindex!(::ReshapedArray,::Int...)",
      "setindex!(::ReshapedArray,::ReshapedIndex)"],
    statement := "Successful indexed assignment to a ReshapedArray returns the assigned value.",
    source := "base/reshapedarray.jl:319-333; setindex! return contract",
    status := .todo, prop := ``ReshapedAssignmentReturnsValue, thm := none, notes := "First-index calls need not succeed, making conditional setter premise vacuous; generic effects lack laws. Concrete Cartesian clause alone is insufficient." },
  { id := "reshapedarray-indexing-bounds-errors", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["getindex(::ReshapedArrayLF,::Int)", "getindex(::ReshapedArray,::Int...)",
      "getindex(::ReshapedArray,::ReshapedIndex)", "setindex!(::ReshapedArrayLF,::Int)",
      "setindex!(::ReshapedArray,::Int...)", "setindex!(::ReshapedArray,::ReshapedIndex)"],
    statement := "Bounds errors from checked parent access propagate unchanged through reshaped indexing and assignment.",
    source := "base/reshapedarray.jl:280-333; boundscheck wrappers",
    status := .todo, prop := ``ReshapedCheckedBoundsPropagate, thm := none, notes := "Generic monad/exception interfaces do not assert bind/throw propagation equations. Concrete Except helpers are partial only." },
  { id := "reshapedarray-vector-strides", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["strides(::ReshapedArray)", "merge_adjacent_dim(apsz::Dims{1},apst::Dims{1})"],
    statement := "Reshaping a noncontiguous one-dimensional parent preserves the parent element stride in every view dimension.",
    source := "base/reshapedarray.jl:424-431,449; stride contract for vector parents",
    status := .todo, prop := ``ReshapedStridedVector, thm := none, notes := "Prop forwards parentStride to an arbitrary callback without requiring preservation of the parent element stride in every view dimension." },
]

/-! Method -> property
reshapedArrayConstructor@10 -> reshapedarray-array-shares-storage
reshapedArrayIteratorConstructor@20 -> Nothing to promise
rsIterator@21 -> Nothing to promise
iterateReshapedIterator@31 -> arraycov-reshaped-iterator-exhaustion
reshapedIteratorLength@35 -> Nothing to promise
reshapedIteratorEltype@36 -> Nothing to promise
throw_dmrsa@38 -> reshapedarray-dimension-errors
reshapeArray@43 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage, reinterpretarrays-reshape-typemax-dim, reshapedarray-dimension-errors
reshapeBang@55 -> multidimcov-reshape-bang-field, reshapedarray-dimension-errors
reshapeIntOrInd@122 -> Nothing to promise
reshapeShapeTuple@123 -> Nothing to promise
reshapeLegacyShapeTuple@126 -> Nothing to promise
reshapeIntegerTuple@127 -> Nothing to promise
reshapeDims@128 -> Nothing to promise
reshapeVectorColon@131 -> Nothing to promise
reshapeVectorColonTuple@132 -> Nothing to promise
reshapeIntVarargs@133 -> Nothing to promise
reshapeIntegerVarargs@134 -> Nothing to promise
reshapeIntegerColonVarargs@135 -> Nothing to promise
reshapeColonTuple@136 -> reinterpretarrays-reshape-colon-sound
throw1@138 -> reshapedarray-dimension-errors
throw2@140 -> reshapedarray-dimension-errors
reshapeUncolon@143 -> reinterpretarrays-reshape-colon-sound
reshapeComputeSizeInt@152 -> reinterpretarrays-reshape-colon-sound
reshapeComputeSizeGeneric@163 -> reshapedarray-generic-colon-product
reshapeComputeNonempty@172 -> reshapedarray-generic-colon-product
anyColonNone@178 -> reinterpretarrays-reshape-colon-sound
anyColonHeadColon@179 -> reinterpretarrays-reshape-colon-sound
anyColonHeadAny@180 -> reinterpretarrays-reshape-colon-sound
beforeColonHeadAny@181 -> reinterpretarrays-reshape-colon-sound
beforeColonHeadColon@182 -> reinterpretarrays-reshape-colon-sound
afterColonHeadAny@183 -> reinterpretarrays-reshape-colon-sound
afterColonHeadColon@184 -> reinterpretarrays-reshape-colon-sound
reshapeValEqual@186 -> Nothing to promise
reshapeValRank@187 -> Nothing to promise
rdimsTrailingMany@194 -> Nothing to promise
rdimsTrailingSingle@195 -> Nothing to promise
rdimsVal@196 -> Nothing to promise
rdimsEmptyEmpty@197 -> Nothing to promise
rdimsEmptyOne@198 -> Nothing to promise
rdimsEmptyMany@199 -> Nothing to promise
rdimsSingletonEmpty@200 -> Nothing to promise
rdimsManyEmpty@201 -> Nothing to promise
rdimsSingletonOne@202 -> Nothing to promise
rdimsSingletonMany@203 -> Nothing to promise
rdimsEqualRank@204 -> Nothing to promise
rdimsRecursive@205 -> Nothing to promise
reshapeVectorArrayIdentity@209 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
reshapeDenseVector@210 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
reshapeDenseArray@211 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
reshapeAbstractVector@214 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
reshapeAbstractArray@221 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
throwDmrs@227 -> reshapedarray-dimension-errors
reshapeReshapedVector@232 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
reshapeReshapedArray@233 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
constructReshapedCartesian@235 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
constructReshapedCartesianZero@243 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
constructReshapedLinear@248 -> reinterpretarrays-reshape-check-sound, reshapedarray-array-shares-storage
reshapedSize@253 -> reshapedarray-array-shares-storage
reshapedLength@254 -> reshapedarray-array-shares-storage
reshapedSimilar@255 -> Nothing to promise
reshapedSimilarType@256 -> Nothing to promise
reshapedIndexStyle@257 -> Nothing to promise
reshapedParent@258 -> reshapedarray-array-shares-storage
reshapedParentIndices@259 -> Nothing to promise
reshapedElsize@260 -> Nothing to promise
reshapedUnaliascopy@262 -> Nothing to promise
reshapedDataids@263 -> Nothing to promise
mightAliasReshaped@265 -> Nothing to promise
mightAliasReshapedSub@267 -> Nothing to promise
mightAliasSubReshaped@268 -> Nothing to promise
ind2subRsEmpty@270 -> reinterpretarrays-ind2sub-rs, memsafety-reshapedarray-ind2sub
ind2subRs@271 -> reinterpretarrays-ind2sub-rs, memsafety-reshapedarray-ind2sub
ind2subRsAuxEmpty@272 -> reinterpretarrays-ind2sub-rs, memsafety-reshapedarray-ind2sub
ind2subRsAux@273 -> reinterpretarrays-ind2sub-rs, memsafety-reshapedarray-ind2sub
offsetIfVec@277 -> Nothing to promise
offsetIfGeneral@278 -> Nothing to promise
isassignedReshapedLinear@280 -> memsafety-reshapedarray-indexing, reshapedarray-isassigned-bounds
isassignedReshapedCartesian@286 -> memsafety-reshapedarray-indexing, reshapedarray-isassigned-bounds
getindexReshapedLinear@294 -> memsafety-reshapedarray-indexing, reshapedarray-indexing-bounds-errors
getindexReshapedCartesian@300 -> memsafety-reshapedarray-indexing, reshapedarray-indexing-bounds-errors
getindexReshapedIndex@304 -> memsafety-reshapedarray-indexing, reshapedarray-indexing-bounds-errors
unsafeGetindexReshaped@310 -> memsafety-reshapedarray-indexing, reshapedarray-indexing-bounds-errors
unsafeGetindexReshapedScalar@316 -> Nothing to promise
unsafeGetindexReshapedTuple@317 -> Nothing to promise
setindexReshapedLinear@319 -> reshapedarray-assignment-returns-value, reshapedarray-indexing-bounds-errors, memsafety-reshapedarray-ind2sub
setindexReshapedCartesian@325 -> reshapedarray-assignment-returns-value, reshapedarray-indexing-bounds-errors, memsafety-reshapedarray-ind2sub
setindexReshapedIndex@329 -> reshapedarray-assignment-returns-value, reshapedarray-indexing-bounds-errors, memsafety-reshapedarray-ind2sub
unsafeSetindexReshaped@335 -> reshapedarray-assignment-returns-value, reshapedarray-indexing-bounds-errors, memsafety-reshapedarray-ind2sub
setindexReshapedRangeLinear@344 -> reshapedarray-range-assignment-error
setindexReshapedRangeCartesian@345 -> reshapedarray-range-assignment-error
setindexReshapedRangeIndex@346 -> reshapedarray-range-assignment-error
rsSetindexError@348 -> reshapedarray-range-assignment-error
cconvertReshaped@350 -> Nothing to promise
unsafeConvertReshaped@351 -> Nothing to promise
viewindexingSliceReshaped@355 -> Nothing to promise
viewindexingReshapedRange@356 -> Nothing to promise
computeStride1@357 -> Nothing to promise
computeOffset1@358 -> Nothing to promise
substridesReshapedRange@360 -> Nothing to promise
unsafeConvertSubArray@368 -> reshapedarray-pointer-offsets
offsetCconvertNested@384 -> reshapedarray-pointer-offsets
offsetCconvertBase@391 -> reshapedarray-pointer-offsets
unsafeConvertOffsetCconvert@398 -> reshapedarray-pointer-offsets
cconvertSubArray@402 -> reshapedarray-pointer-offsets
checkcontiguousAbstract@417 -> reshapedarray-contiguous-strides, reshapedarray-vector-strides
checkcontiguousDense@420 -> reshapedarray-contiguous-strides, reshapedarray-vector-strides
checkcontiguousReshaped@421 -> reshapedarray-contiguous-strides, reshapedarray-vector-strides
checkcontiguousSubArray@422 -> reshapedarray-contiguous-strides, reshapedarray-vector-strides
stridesReshaped@424 -> reshapedarray-contiguous-strides, reshapedarray-vector-strides
reshapedStridesEmpty@433 -> Nothing to promise
reshapedStridesRecursive@437 -> Nothing to promise
mergeAdjacentDimEmpty@448 -> Nothing to promise
mergeAdjacentDimOne@449 -> reshapedarray-vector-strides
mergeAdjacentDimMany@450 -> Nothing to promise
mapReshapedArray@466 -> Nothing to promise
iterateReshapedArray@468 -> Nothing to promise
iterateReshapedArrayState@469 -> Nothing to promise
mapfoldlReshaped@471 -> Nothing to promise
mapfoldrReshaped@472 -> Nothing to promise
inReshapedArray@474 -> Nothing to promise
-/

end JuliaLean.Proofs.base.reshapedarray
