import JuliaLean.MultidimCov.ArrayFaithfulCore
import JuliaLean.AbstractArrays.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful

open JuliaLean.Registry
open JuliaLean.AbstractArrays
open ArrayFaithfulCore

/-! Faithful replacements for the HOLLOW interface and bounds rows in
`base/abstractarray.jl`. `IntegerValue` represents every Julia `Integer`, not a
fixed-width machine integer. Calls on arbitrary Julia objects are error-aware
callbacks; each method below controls their source order and branching. -/

structure IntegerValue where
  value : Int
  deriving Repr, DecidableEq

structure AnyValue where
  typeId : Nat
  identity : Nat
  deriving Repr, DecidableEq

inductive LazyString where
  | literal (value : String)
  | integer (value : Int)
  | dynamic (value : AnyValue)
  | append (left right : LazyString)
  deriving Repr, DecidableEq

inductive Failure where
  | argument (message : LazyString)
  | bounds
  | dimensionMismatch (message : LazyString)
  | methodError (name : String)
  | typeError
  | callback (id : Nat)
  deriving Repr, DecidableEq

abbrev JResult (α : Type) := Except Failure α

def lazyAppend (values : List LazyString) : LazyString :=
  values.foldl .append (.literal "")

def getOneBased (values : List α) (index : Int) : JResult α :=
  if index < 1 || (values.length : Int) < index then .error .bounds
  else match values[(index - 1).toNat]? with
    | some value => .ok value
    | none => .error .bounds

/-- `convert(::Type{AbstractArray{T}}, a)`, line 17: construct first, then run
the result type assertion. -/
def m17 (construct : ArrayState α → JResult (ArrayState β)) (source : ArrayState α)
    (targetType : String) : JResult (ArrayState β) := do
  let result ← construct source
  if result.elementType = targetType then .ok result else .error .typeError

def P17 : Prop := ∀ {α β : Type} (construct : ArrayState α → JResult (ArrayState β)) source targetType,
  m17 construct source targetType = do
    let result ← construct source
    if result.elementType = targetType then .ok result else .error .typeError
theorem p17 : P17 := by unfold P17; intros; rfl

/-- Rank-specialized conversion, line 18: the asserted result type fixes both
element type and rank. -/
def m18 (construct : ArrayState α → JResult (ArrayState β)) (source : ArrayState α)
    (targetType : String) (rank : Nat) : JResult (ArrayState β) := do
  let result ← construct source
  if result.elementType = targetType && result.axes.length = rank then .ok result
  else .error .typeError

def P18 : Prop := ∀ {α β : Type} (construct : ArrayState α → JResult (ArrayState β)) source targetType rank,
  m18 construct source targetType rank = do
    let result ← construct source
    if result.elementType = targetType && result.axes.length = rank then .ok result
    else .error .typeError
theorem p18 : P18 := by unfold P18; intros; rfl

/-- `size(t, dim)`, lines 42-46. The conversion accepts every Julia value for
which `Int(dim)` is defined and occurs before `size(t)`. -/
def m42 (toInt : D → JResult Int) (size : A → JResult (List Nat)) (array : A)
    (dimension : D) : JResult Nat := do
  let d ← toInt dimension
  let shape ← size array
  if d ≤ (shape.length : Int) then getOneBased shape d else .ok 1

def P42 : Prop := ∀ {A D : Type} (toInt : D → JResult Int)
    (size : A → JResult (List Nat)) array dimension,
  m42 toInt size array dimension = do
    let d ← toInt dimension
    let shape ← size array
    if d ≤ (shape.length : Int) then getOneBased shape d else .ok 1
theorem p42 : P42 := by unfold P42; intros; rfl

/-- `axes(A, d)`, lines 79-82. The type assertion is represented by the
unbounded `IntegerValue`; negative and zero values take the tuple-index path. -/
def m79 (axes : A → JResult (List Axis)) (array : A) (rank : Nat)
    (dimension : IntegerValue) : JResult Axis :=
  if dimension.value ≤ (rank : Int) then do
    let values ← axes array
    getOneBased values dimension.value
  else .ok (Axis.oneTo 1)

def P79 : Prop := ∀ {A : Type} (axes : A → JResult (List Axis)) array rank dimension,
  m79 axes array rank dimension = if dimension.value ≤ (rank : Int) then do
    let values ← axes array
    getOneBased values dimension.value
  else .ok (Axis.oneTo 1)
theorem p79 : P79 := by unfold P79; intros; rfl

/-- `_join_comma_and(indsA, indsB)`, line 329. -/
def m329 (left right : AnyValue) : LazyString :=
  lazyAppend [.dynamic left, .literal " and ", .dynamic right]
def P329 : Prop := ∀ left right,
  m329 left right = lazyAppend [.dynamic left, .literal " and ", .dynamic right]
theorem p329 : P329 := by unfold P329; intros; rfl

/-- Vararg `_join_comma_and`, line 330. A call with no trailing values reaches
the undefined one-argument method and therefore raises `MethodError`. -/
def joinCommaAnd : AnyValue → List AnyValue → JResult LazyString
  | _, [] => .error (.methodError "_join_comma_and")
  | left, [right] => .ok (m329 left right)
  | left, right :: rest => do
      let suffix ← joinCommaAnd right rest
      .ok (lazyAppend [.dynamic left, .literal ", ", suffix])

def m330 (left right : AnyValue) (rest : List AnyValue) : JResult LazyString := do
  let suffix ← joinCommaAnd right rest
  .ok (lazyAppend [.dynamic left, .literal ", ", suffix])
def P330 : Prop := ∀ left right rest,
  m330 left right rest = do
    let suffix ← joinCommaAnd right rest
    .ok (lazyAppend [.dynamic left, .literal ", ", suffix])
theorem p330 : P330 := by unfold P330; intros; rfl

/-- `throw_eachindex_mismatch_indices`, lines 331-336. -/
def mismatchMessage (indicesDescription firstIndex : AnyValue)
    (otherIndices : List AnyValue) : JResult LazyString := do
  let joined ← joinCommaAnd firstIndex otherIndices
  .ok (lazyAppend [.literal "all inputs to eachindex must have the same ",
    .dynamic indicesDescription, .literal ", got ", joined])

def m331 (indicesDescription firstIndex : AnyValue) (otherIndices : List AnyValue) : JResult α := do
  let message ← mismatchMessage indicesDescription firstIndex otherIndices
  .error (.dimensionMismatch message)
def P331 : Prop := ∀ {α : Type} indicesDescription firstIndex otherIndices,
  m331 (α := α) indicesDescription firstIndex otherIndices = do
    let message ← mismatchMessage indicesDescription firstIndex otherIndices
    .error (.dimensionMismatch message)
theorem p331 : P331 := by unfold P331; intros; rfl

def checkAllEqual (equal : I → I → JResult Bool) (first : I) : List I → JResult Bool
  | [] => .ok true
  | head :: tail => do
      if ← equal first head then checkAllEqual equal first tail else .ok false

/-- Linear vararg `eachindex`, lines 397-405: compute every index object via
`map`, compare left-to-right with `all`, construct the lazy error only on
mismatch, and return the first index object. -/
def m397 (eachIndex : A → JResult I) (equal : I → I → JResult Bool)
    (indicesDescription : AnyValue) (asAny : I → AnyValue)
    (first : A) (rest : List A) : JResult I := do
  let base ← eachIndex first
  let others ← rest.mapM eachIndex
  if ← checkAllEqual equal base others then .ok base
  else m331 (α := I) indicesDescription (asAny base) (others.map asAny)

def P397 : Prop := ∀ {A I : Type} (eachIndex : A → JResult I)
    (equal : I → I → JResult Bool) indicesDescription
    (asAny : I → AnyValue) first rest,
  m397 eachIndex equal indicesDescription asAny first rest = do
    let base ← eachIndex first
    let others ← rest.mapM eachIndex
    if ← checkAllEqual equal base others then .ok base
    else m331 (α := I) indicesDescription (asAny base) (others.map asAny)
theorem p397 : P397 := by unfold P397; intros; rfl

/-- `lastindex(a::AbstractArray)`, line 429. -/
def m429 (eachIndex : A → JResult I) (last : I → JResult K) (array : A) : JResult K := do
  let indices ← eachIndex array
  last indices
def P429 : Prop := ∀ {A I K : Type} (eachIndex : A → JResult I)
    (last : I → JResult K) array, m429 eachIndex last array = do
      let indices ← eachIndex array
      last indices
theorem p429 : P429 := by unfold P429; intros; rfl

/-- `lastindex(a,d)`, line 430. -/
def m430 (axes : A → D → JResult I) (last : I → JResult K) (array : A)
    (dimension : D) : JResult K := do
  let axis ← axes array dimension
  last axis
def P430 : Prop := ∀ {A D I K : Type} (axes : A → D → JResult I)
    (last : I → JResult K) array dimension, m430 axes last array dimension = do
      let axis ← axes array dimension
      last axis
theorem p430 : P430 := by unfold P430; intros; rfl

/-- `firstindex(a::AbstractArray)`, line 452. -/
def m452 (eachIndex : A → JResult I) (first : I → JResult K) (array : A) : JResult K := do
  let indices ← eachIndex array
  first indices
def P452 : Prop := ∀ {A I K : Type} (eachIndex : A → JResult I)
    (first : I → JResult K) array, m452 eachIndex first array = do
      let indices ← eachIndex array
      first indices
theorem p452 : P452 := by unfold P452; intros; rfl

/-- `firstindex(a,d)`, line 453. -/
def m453 (axes : A → D → JResult I) (first : I → JResult K) (array : A)
    (dimension : D) : JResult K := do
  let axis ← axes array dimension
  first axis
def P453 : Prop := ∀ {A D I K : Type} (axes : A → D → JResult I)
    (first : I → JResult K) array dimension, m453 axes first array dimension = do
      let axis ← axes array dimension
      first axis
theorem p453 : P453 := by unfold P453; intros; rfl

/-- `first(a::AbstractArray)`, line 455. -/
def m455 (eachIndex : A → JResult I) (first : I → JResult K)
    (getindex : A → K → JResult V) (array : A) : JResult V := do
  let indices ← eachIndex array
  let index ← first indices
  getindex array index
def P455 : Prop := ∀ {A I K V : Type} (eachIndex : A → JResult I)
    (first : I → JResult K) (getindex : A → K → JResult V) array,
  m455 eachIndex first getindex array = do
    let indices ← eachIndex array
    let index ← first indices
    getindex array index
theorem p455 : P455 := by unfold P455; intros; rfl

/-- Generic `first(itr)`, lines 474-478. -/
def m474 (iterate : I → JResult (Option (V × S))) (iterator : I) : JResult V := do
  match ← iterate iterator with
  | none => .error (.argument (.literal "collection must be non-empty"))
  | some (value, _) => .ok value
def P474 : Prop := ∀ {I V S : Type} (iterate : I → JResult (Option (V × S))) iterator,
  m474 iterate iterator = do
    match ← iterate iterator with
    | none => .error (.argument (.literal "collection must be non-empty"))
    | some (value, _) => .ok value
theorem p474 : P474 := by unfold P474; intros; rfl

/-- `first(itr,n)`, line 505. -/
def m505 (take : I → IntegerValue → JResult T) (collect : T → JResult C)
    (iterator : I) (count : IntegerValue) : JResult C := do
  let taken ← take iterator count
  collect taken
def P505 : Prop := ∀ {I T C : Type} (take : I → IntegerValue → JResult T)
    (collect : T → JResult C) iterator count, m505 take collect iterator count = do
      let taken ← take iterator count
      collect taken
theorem p505 : P505 := by unfold P505; intros; rfl

/-- Vector `first(v,n)`, lines 507-510. -/
def m507 (firstIndex : A → JResult K) (checkedLength : A → JResult IntegerValue)
    (makeRange : K → IntegerValue → JResult R) (getindex : A → R → JResult V)
    (array : A) (count : IntegerValue) : JResult V :=
  if count.value < 0 then .error (.argument (.literal "Number of elements must be non-negative"))
  else do
    let start ← firstIndex array
    let available ← checkedLength array
    let range ← makeRange start ⟨min count.value available.value⟩
    getindex array range
def P507 : Prop := ∀ {A K R V : Type} (firstIndex : A → JResult K)
    (checkedLength : A → JResult IntegerValue) (makeRange : K → IntegerValue → JResult R)
    (getindex : A → R → JResult V) array count,
  m507 firstIndex checkedLength makeRange getindex array count =
    if count.value < 0 then .error (.argument (.literal "Number of elements must be non-negative"))
    else do
      let start ← firstIndex array
      let available ← checkedLength array
      let range ← makeRange start ⟨min count.value available.value⟩
      getindex array range
theorem p507 : P507 := by unfold P507; intros; rfl

/-- Generic `last(itr,n)`, line 555. -/
def m555 (reverseIterator : I → JResult R) (take : R → IntegerValue → JResult T)
    (collect : T → JResult C) (reverseInPlace : C → JResult C)
    (iterator : I) (count : IntegerValue) : JResult C := do
  let reversed ← reverseIterator iterator
  let suffix ← take reversed count
  let collected ← collect suffix
  reverseInPlace collected
def P555 : Prop := ∀ {I R T C : Type} (reverseIterator : I → JResult R)
    (take : R → IntegerValue → JResult T) (collect : T → JResult C)
    (reverseInPlace : C → JResult C) iterator count,
  m555 reverseIterator take collect reverseInPlace iterator count = do
    let reversed ← reverseIterator iterator
    let suffix ← take reversed count
    let collected ← collect suffix
    reverseInPlace collected
theorem p555 : P555 := by unfold P555; intros; rfl

/-- Vector `last(v,n)`, lines 557-560. -/
def m557 (lastIndex : A → JResult K) (checkedLength : A → JResult IntegerValue)
    (makeRange : K → IntegerValue → JResult R) (getindex : A → R → JResult V)
    (array : A) (count : IntegerValue) : JResult V :=
  if count.value < 0 then .error (.argument (.literal "Number of elements must be non-negative"))
  else do
    let stop ← lastIndex array
    let available ← checkedLength array
    let range ← makeRange stop ⟨min count.value available.value⟩
    getindex array range
def P557 : Prop := ∀ {A K R V : Type} (lastIndex : A → JResult K)
    (checkedLength : A → JResult IntegerValue) (makeRange : K → IntegerValue → JResult R)
    (getindex : A → R → JResult V) array count,
  m557 lastIndex checkedLength makeRange getindex array count =
    if count.value < 0 then .error (.argument (.literal "Number of elements must be non-negative"))
    else do
      let stop ← lastIndex array
      let available ← checkedLength array
      let range ← makeRange stop ⟨min count.value available.value⟩
      getindex array range
theorem p557 : P557 := by unfold P557; intros; rfl

def strideSum (getStride getSize : Nat → JResult I64) : Nat → Nat → I64 → JResult I64
  | _, 0, total => .ok total
  | dimension, remaining + 1, total => do
      let stride ← getStride dimension
      let size ← getSize dimension
      strideSum getStride getSize (dimension + 1) remaining (total + stride * size)

/-- `stride(A,k)`, lines 597-607, including both calls to `ndims(A)`, the
source summation order, and wrapping machine-`Int` arithmetic. -/
def m597 (strides : A → JResult (List I64)) (ndims : A → JResult Nat)
    (size : A → JResult (List I64)) (array : A) (dimension : IntegerValue) : JResult I64 := do
  let values ← strides array
  let rank ← ndims array
  if dimension.value ≤ (rank : Int) then getOneBased values dimension.value
  else
    let rankAgain ← ndims array
    if rankAgain = 0 then .ok (JInt.lit .i64 1)
    else do
      let shape ← size array
      let firstStride ← getOneBased values 1
      let firstSize ← getOneBased shape 1
      strideSum (getOneBased values ∘ Int.ofNat) (getOneBased shape ∘ Int.ofNat)
        2 (rankAgain - 1) (firstStride * firstSize)
def P597 : Prop := ∀ {A : Type} (strides : A → JResult (List I64))
    (ndims : A → JResult Nat) (size : A → JResult (List I64)) array dimension,
  m597 strides ndims size array dimension = do
    let values ← strides array
    let rank ← ndims array
    if dimension.value ≤ (rank : Int) then getOneBased values dimension.value
    else
      let rankAgain ← ndims array
      if rankAgain = 0 then .ok (JInt.lit .i64 1)
      else do
        let shape ← size array
        let firstStride ← getOneBased values 1
        let firstSize ← getOneBased shape 1
        strideSum (getOneBased values ∘ Int.ofNat) (getOneBased shape ∘ Int.ofNat)
          2 (rankAgain - 1) (firstStride * firstSize)
theorem p597 : P597 := by unfold P597; intros; rfl

def sizeToStrides (multiply : N → N → JResult N) : N → List N → JResult (List N)
  | _, [] => .ok []
  | stride, dimension :: rest => do
      let next ← multiply stride dimension
      let tail ← sizeToStrides multiply next rest
      .ok (stride :: tail)

/-- Vararg `size_to_strides`, line 609. -/
def m609 (multiply : N → N → JResult N) (stride dimension : N) (rest : List N) : JResult (List N) := do
  let next ← multiply stride dimension
  let tail ← sizeToStrides multiply next rest
  .ok (stride :: tail)
def P609 : Prop := ∀ {N : Type} (multiply : N → N → JResult N) stride dimension rest,
  m609 multiply stride dimension rest = do
    let next ← multiply stride dimension
    let tail ← sizeToStrides multiply next rest
    .ok (stride :: tail)
theorem p609 : P609 := by unfold P609; intros; rfl

/-- Two-argument `size_to_strides`, line 610. -/
def m610 (stride _dimension : N) : List N := [stride]
def P610 : Prop := ∀ {N : Type} (stride dimension : N), m610 stride dimension = [stride]
theorem p610 : P610 := by unfold P610; intros; rfl

/-- One-argument `size_to_strides`, line 611. -/
def m611 (_stride : N) : List N := []
def P611 : Prop := ∀ {N : Type} (stride : N), m611 stride = []
theorem p611 : P611 := by unfold P611; intros; rfl

/-- `isstored`, lines 613-616. -/
def m613 (checkbounds : A → List IntegerValue → JResult Unit) (array : A)
    (indices : List IntegerValue) : JResult Bool := do
  checkbounds array indices
  .ok true
def P613 : Prop := ∀ {A : Type} (checkbounds : A → List IntegerValue → JResult Unit)
    array indices, m613 checkbounds array indices = do
      checkbounds array indices
      .ok true
theorem p613 : P613 := by unfold P613; intros; rfl

def trailingLoop (multiply : N → N → JResult N) (size : IntegerValue → JResult N) :
    Int → Nat → N → JResult N
  | _, 0, product => .ok product
  | dimension, remaining + 1, product => do
      let value ← size ⟨dimension⟩
      let next ← multiply product value
      trailingLoop multiply size (dimension + 1) remaining next

/-- `trailingsize(A,n)`, lines 619-625. -/
def m619 (ndims : A → JResult Nat) (size : A → IntegerValue → JResult N)
    (multiply : N → N → JResult N) (one : N)
    (array : A) (start : IntegerValue) : JResult N := do
  let rank ← ndims array
  let count := if start.value ≤ (rank : Int)
    then ((rank : Int) - start.value + 1).toNat else 0
  trailingLoop multiply (size array) start.value count one
def P619 : Prop := ∀ {A N : Type} (ndims : A → JResult Nat)
    (size : A → IntegerValue → JResult N) (multiply : N → N → JResult N)
    one array start,
  m619 ndims size multiply one array start = do
    let rank ← ndims array
    let count := if start.value ≤ (rank : Int)
      then ((rank : Int) - start.value + 1).toNat else 0
    trailingLoop multiply (size array) start.value count one
theorem p619 : P619 := by unfold P619; intros; rfl

/-- `trailingsize(inds,n)`, lines 626-632. -/
def m626 (axisLength : Axis → JResult N) (multiply : N → N → JResult N)
    (one : N) (axes : List Axis) (start : IntegerValue) : JResult N :=
  let count := if start.value ≤ (axes.length : Int)
    then ((axes.length : Int) - start.value + 1).toNat else 0
  trailingLoop multiply (fun dimension => do
    let axis ← getOneBased axes dimension.value
    axisLength axis) start.value count one
def P626 : Prop := ∀ {N : Type} (axisLength : Axis → JResult N)
    (multiply : N → N → JResult N) one axes start,
  m626 axisLength multiply one axes start =
    let count := if start.value ≤ (axes.length : Int)
      then ((axes.length : Int) - start.value + 1).toNat else 0
    trailingLoop multiply (fun dimension => do
      let axis ← getOneBased axes dimension.value
      axisLength axis) start.value count one
theorem p626 : P626 := by unfold P626; intros; rfl

/-- Recursive `checkbounds_indices`, lines 722-727. -/
def m722 (defaultAxis : Axis) (checkindex : Axis → I → JResult Bool)
    (recursive : List Axis → List I → JResult Bool) (axes : List Axis)
    (head : I) (tail : List I) : JResult Bool := do
  let firstOk ← checkindex (axes.head?.getD defaultAxis) head
  if firstOk then recursive axes.tail tail else .ok false
def P722 : Prop := ∀ {I : Type} defaultAxis (checkindex : Axis → I → JResult Bool)
    (recursive : List Axis → List I → JResult Bool) axes head tail,
  m722 defaultAxis checkindex recursive axes head tail = do
    let firstOk ← checkindex (axes.head?.getD defaultAxis) head
    if firstOk then recursive axes.tail tail else .ok false
theorem p722 : P722 := by unfold P722; intros; rfl

/-- Real scalar `checkindex`, line 751. Both comparisons run because Julia uses
bitwise `&`; errors in the upper comparison remain observable. -/
def m751 (first last : R → JResult V) (lessEqual : V → V → JResult Bool)
    (range : R) (value : V) : JResult Bool := do
  let lowerEndpoint ← first range
  let lower ← lessEqual lowerEndpoint value
  let upperEndpoint ← last range
  let upper ← lessEqual value upperEndpoint
  .ok (lower && upper)
def P751 : Prop := ∀ {R V : Type} (first last : R → JResult V)
    (lessEqual : V → V → JResult Bool) range value,
  m751 first last lessEqual range value = do
    let lowerEndpoint ← first range
    let lower ← lessEqual lowerEndpoint value
    let upperEndpoint ← last range
    let upper ← lessEqual value upperEndpoint
    .ok (lower && upper)
theorem p751 : P751 := by unfold P751; intros; rfl

/-- Range `checkindex`, lines 756-757. `|` and `&` evaluate all three calls. -/
def m756 (isEmpty : I → JResult Bool) (first last : I → JResult V)
    (checkindex : V → JResult Bool) (indices : I) : JResult Bool := do
  let empty ← isEmpty indices
  let firstValue ← first indices
  let firstOk ← checkindex firstValue
  let lastValue ← last indices
  let lastOk ← checkindex lastValue
  .ok (empty || (firstOk && lastOk))
def P756 : Prop := ∀ {I V : Type} (isEmpty : I → JResult Bool)
    (first last : I → JResult V) (checkindex : V → JResult Bool) indices,
  m756 isEmpty first last checkindex indices = do
    let empty ← isEmpty indices
    let firstValue ← first indices
    let firstOk ← checkindex firstValue
    let lastValue ← last indices
    let lastOk ← checkindex lastValue
    .ok (empty || (firstOk && lastOk))
theorem p756 : P756 := by unfold P756; intros; rfl

/-- LinearIndices overload, lines 759-760, with the same eager operators. -/
def m759 := @m756
def P759 : Prop := ∀ {I V : Type} (isEmpty : I → JResult Bool)
    (first last : I → JResult V) (checkindex : V → JResult Bool) indices,
  m759 isEmpty first last checkindex indices = m756 isEmpty first last checkindex indices
theorem p759 : P759 := by unfold P759; intros; rfl

def checkEvery (iterate : A → (Bool → I → JResult Bool) → Bool → JResult Bool)
    (check : I → JResult Bool) (array : A) : JResult Bool :=
  iterate array (fun accumulated value => do
    let current ← check value
    .ok (accumulated && current)) true

/-- Array-valued `checkindex`, lines 762-769. The iterator invokes each
`checkindex` call before requesting the next element. -/
def m762 (iterate : A → (Bool → I → JResult Bool) → Bool → JResult Bool)
    (checkindex : I → JResult Bool) (array : A) : JResult Bool :=
  checkEvery iterate checkindex array
def P762 : Prop := ∀ {A I : Type}
    (iterate : A → (Bool → I → JResult Bool) → Bool → JResult Bool)
    (checkindex : I → JResult Bool) array,
  m762 iterate checkindex array =
    iterate array (fun accumulated value => do
      let current ← checkindex value
      .ok (accumulated && current)) true
theorem p762 : P762 := by unfold P762 m762 checkEvery; intros; rfl

structure EmptyVector where
  elementType : AnyValue
  deriving Repr, DecidableEq

/-- `emptymutable(::AbstractVector, ::Type{U})`, line 895. -/
def m895 (_array : A) (elementType : AnyValue) : EmptyVector := ⟨elementType⟩
def P895 : Prop := ∀ {A : Type} (array : A) elementType,
  (m895 array elementType).elementType = elementType
theorem p895 : P895 := by unfold P895 m895; intros; rfl

/-- `emptymutable(itr, ::Type{U})`, line 896. -/
def m896 (_iterator : I) (elementType : AnyValue) : EmptyVector := ⟨elementType⟩
def P896 : Prop := ∀ {I : Type} (iterator : I) elementType,
  (m896 iterator elementType).elementType = elementType
theorem p896 : P896 := by unfold P896 m896; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
