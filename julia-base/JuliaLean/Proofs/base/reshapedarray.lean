import JuliaLean.base.reshapedarray
import JuliaLean.Registry.Types

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
        (constructReshapedCartesian size front toInt makeInverse (T := T) (N := N)) parent dims = .ok result →
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

def entries : List Entry := [
  { id := "reinterpretarrays-reshape-check-sound", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape(::Array{T,M}, ::NTuple{N,Int})", "_reshape(::AbstractArray,::Dims)",
      "__reshape(::AbstractArray,::IndexStyle)", "Core.checked_dims"],
    statement := "Successful reshape checks nonnegative dimensions and their exact product against the parent length, and retains the source storage and requested shape.",
    source := "base/reshapedarray.jl:43-50,221-251; reshape docstring lines 66-79; Core.checked_dims contract",
    status := .todo, prop := ``ReshapeCheckSound, thm := none },
  { id := "reinterpretarrays-reshape-colon-sound", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape(::AbstractArray,::Tuple{Vararg{Union{Integer,Colon}}})", "_reshape_uncolon",
      "_reshape_uncolon_computesize(Int)", "_reshape_uncolon_computesize_nonempty"],
    statement := "For a valid single-colon shape, the inferred nonnegative dimension makes the exact dimension product equal the parent length.",
    source := "base/reshapedarray.jl:75-80,143-177; reshape docstring",
    status := .todo, prop := ``ReshapeColonSound, thm := none },
  { id := "reinterpretarrays-ind2sub-rs", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["ind2sub_rs", "_ind2sub_rs"],
    statement := "The computed parent coordinates are in bounds and reconstruct the input linear index in column-major order for every valid parent shape.",
    source := "base/reshapedarray.jl:270-276; reshape length and SignedMultiplicativeInverse representation invariants",
    status := .todo, prop := ``Ind2subCorrect, thm := none },
  { id := "reinterpretarrays-reshape-typemax-dim", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape(::AbstractArray,::Dims)", "_reshape(::AbstractArray,::Dims)", "Core.checked_dims"],
    statement := "Reshape succeeds whenever every requested dimension is nonnegative and their exact product equals the parent length.",
    source := "base/reshapedarray.jl:43-50,221-224; reshape docstring lines 75-79",
    status := .todo, prop := ``ReshapeCheckComplete, thm := none,
    notes := "Retained as an open statement from the previous refutation for the proof worker." },
  { id := "memsafety-reshapedarray-ind2sub", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["isassigned(::ReshapedArray,::Int...)", "_unsafe_getindex(::ReshapedArray,::Int...)",
      "_unsafe_setindex!(::ReshapedArray,::Int...)"],
    statement := "A checked Cartesian access converts its linear index with the stored multiplicative inverses and yields parent coordinates within every parent axis.",
    source := "base/reshapedarray.jl:235-241,286-292,310-315,335-340; parent shape and inverse invariants",
    status := .todo, prop := ``MemsafetyReshapedArrayInd2sub, thm := none },
  { id := "memsafety-reshapedarray-indexing", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["isassigned(::ReshapedArrayLF,::Int)", "getindex(::ReshapedArrayLF,::Int)",
      "setindex!(::ReshapedArrayLF,::Int)", "getindex(::ReshapedArray,::ReshapedIndex)",
      "setindex!(::ReshapedArray,::ReshapedIndex)"],
    statement := "The checked linear path translates by the source and parent axis origins; ReshapedIndex access uses only its stored, parent-checked index.",
    source := "base/reshapedarray.jl:280-306,319-333; equal length and explicit parent bounds checks",
    status := .todo, prop := ``MemsafetyReshapedArrayIndexing, thm := none,
    notes := "Strengthened from the old weak statement to cover both reads through the offset axis and stored ReshapedIndex reads." },
  { id := "multidimcov-reshape-bang-field", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape!(::Array{T,N},::NTuple{N,Int})"],
    statement := "When the checked dimensions have the array's length, reshape! updates the dimensions and returns the same array reference.",
    source := "base/reshapedarray.jl:53-62; source comment on reshape!",
    status := .todo, prop := ``ReshapeBangUpdatesDimensions, thm := none,
    notes := "Keep the existing repro; the proof worker will test the claim against the typed mutable-array model." },
  { id := "arraycov-reshaped-iterator-exhaustion", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["iterate(::ReshapedArrayIterator,i...)", "length(::ReshapedArrayIterator)"],
    statement := "When the parent iterator is exhausted, the wrapper returns normal iteration exhaustion rather than throwing a MethodError.",
    source := "base/reshapedarray.jl:31-36; Julia iteration protocol",
    status := .todo, prop := ``ReshapedIteratorExhaustion, thm := none,
    notes := "Keep the existing repro repro/arraycov-reshaped-iterator-exhaustion.jl for the proof worker." },
  { id := "reshapedarray-array-shares-storage", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["reshape(::Array{T,M},::NTuple{N,Int})", "ReshapedArray(parent,dims,mi)",
      "__reshape(::AbstractArray,::IndexStyle)"],
    statement := "Every successful reshape preserves the parent data observed at every linear position and stores the requested dimensions.",
    source := "base/reshapedarray.jl:43-50,235-251; reshape docstring lines 70-79",
    status := .todo, prop := ``ReshapeArraySharesData, thm := none },
  { id := "reshapedarray-range-assignment-error", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["setindex!(::ReshapedRange,::Int)", "setindex!(::ReshapedRange,::Int...)", "_rs_setindex!_err"],
    statement := "All indexed assignments to a reshaped range raise ErrorException instead of attempting to mutate immutable range storage.",
    source := "base/reshapedarray.jl:342-348; error explains to collect first",
    status := .todo, prop := ``ReshapedRangeAssignmentError, thm := none },
  { id := "reshapedarray-generic-colon-product", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["_reshape_uncolon_computesize(generic)", "_reshape_uncolon_computesize_nonempty"],
    statement := "For generic integer dimensions, successful colon inference inserts one extent whose exact mathematical product with the other dimensions equals the source length.",
    source := "base/reshapedarray.jl:163-176; reshape docstring lines 75-79",
    status := .todo, prop := ``ReshapeGenericColonSound, thm := none },
  { id := "reshapedarray-dimension-errors", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["throw_dmrsa", "throw1", "throw2", "_throw_dmrs", "reshape(::Array)", "reshape!(::Array)"],
    statement := "Reshape dimension mismatches raise DimensionMismatch, including invalid dimension products and indivisible colon shapes.",
    source := "base/reshapedarray.jl:38-62,138-141,227-229",
    status := .todo, prop := ``ReshapeDimensionErrors, thm := none },
  { id := "reshapedarray-pointer-offsets", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["unsafe_convert(::Type{Ptr<S>},::SubArray)", "cconvert(::Type{Ptr<S>},::SubArray)",
      "_offset_cconvert", "unsafe_convert(::Type{Ptr<S>},::OffsetCConvert)"],
    statement := "For a contiguous parent, a strided SubArray pointer advances by the first-index displacement times element size; nested offsets add to the stored byte offset.",
    source := "base/reshapedarray.jl:368-400; pointer conversion and view-offset invariants",
    status := .todo, prop := ``ReshapedPointerOffsets, thm := none },
  { id := "reshapedarray-contiguous-strides", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["strides(::ReshapedArray)", "_checkcontiguous(::Type{Bool},::ReshapedArray)",
      "_checkcontiguous(::Type{Bool},::DenseArray)"],
    statement := "A ReshapedArray over contiguous dense storage reports the standard column-major strides for its stored dimensions.",
    source := "base/reshapedarray.jl:417-431; strides interface and dense contiguity invariant",
    status := .todo, prop := ``ReshapedContiguousStrides, thm := none },
  { id := "reshapedarray-isassigned-bounds", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["isassigned(::ReshapedArrayLF,::Int)", "isassigned(::ReshapedArray,::Int...)"],
    statement := "An out-of-bounds assignment query returns false without querying the parent array.",
    source := "base/reshapedarray.jl:280-292; checked isassigned contract",
    status := .todo, prop := ``ReshapedIsassignedBounds, thm := none },
  { id := "reshapedarray-assignment-returns-value", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["setindex!(::ReshapedArrayLF,::Int)", "setindex!(::ReshapedArray,::Int...)",
      "setindex!(::ReshapedArray,::ReshapedIndex)"],
    statement := "Successful indexed assignment to a ReshapedArray returns the assigned value.",
    source := "base/reshapedarray.jl:319-333; setindex! return contract",
    status := .todo, prop := ``ReshapedAssignmentReturnsValue, thm := none },
  { id := "reshapedarray-indexing-bounds-errors", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["getindex(::ReshapedArrayLF,::Int)", "getindex(::ReshapedArray,::Int...)",
      "getindex(::ReshapedArray,::ReshapedIndex)", "setindex!(::ReshapedArrayLF,::Int)",
      "setindex!(::ReshapedArray,::Int...)", "setindex!(::ReshapedArray,::ReshapedIndex)"],
    statement := "Bounds errors from checked parent access propagate unchanged through reshaped indexing and assignment.",
    source := "base/reshapedarray.jl:280-333; boundscheck wrappers",
    status := .todo, prop := ``ReshapedCheckedBoundsPropagate, thm := none },
  { id := "reshapedarray-vector-strides", juliaFile := "base/reshapedarray.jl",
    juliaFns := ["strides(::ReshapedArray)", "merge_adjacent_dim(apsz::Dims{1},apst::Dims{1})"],
    statement := "Reshaping a noncontiguous one-dimensional parent preserves the parent element stride in every view dimension.",
    source := "base/reshapedarray.jl:424-431,449; stride contract for vector parents",
    status := .todo, prop := ``ReshapedStridedVector, thm := none },
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
