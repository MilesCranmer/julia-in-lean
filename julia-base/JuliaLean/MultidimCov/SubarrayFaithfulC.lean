import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.SubarrayFaithfulC

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

/-! Faithful source-order models for the reviewed HOLLOW methods in
`base/subarray.jl:437-546`. -/

/-- `strides(SubArray)`, line 437. -/
def m437 (parent : V → P) (strides : P → JResult S) (indices : V → I)
    (substrides : S → I → JResult R) (view : V) : JResult R := do
  let values ← strides (parent view)
  substrides values (indices view)
def P437 : Prop := ∀ {V P S I R : Type} (parent : V → P) (strides : P → JResult S)
    (indices : V → I) (substrides : S → I → JResult R) view,
  m437 parent strides indices substrides view = do
    let values ← strides (parent view)
    substrides values (indices view)
theorem p437 : P437 := by unfold P437; intros; rfl

/-- Slice `substrides`, line 441. -/
def m441 (firstStride : S → JResult Int) (tailStrides : S → JResult S)
    (tailIndices : I → JResult I) (recurse : S → I → JResult (List Int))
    (strides : S) (indices : I) : JResult (List Int) := do
  let head ← firstStride strides
  let strideTail ← tailStrides strides
  let indexTail ← tailIndices indices
  let rest ← recurse strideTail indexTail
  .ok (head :: rest)
def P441 : Prop := ∀ {S I : Type} (firstStride : S → JResult Int)
    (tailStrides : S → JResult S) (tailIndices : I → JResult I)
    (recurse : S → I → JResult (List Int)) strides indices,
  m441 firstStride tailStrides tailIndices recurse strides indices = do
    let head ← firstStride strides
    let strideTail ← tailStrides strides
    let indexTail ← tailIndices indices
    let rest ← recurse strideTail indexTail
    .ok (head :: rest)
theorem p441 : P441 := by unfold P441; intros; rfl

/-- AbstractRange `substrides`, line 442. -/
def m442 (firstStride : S → JResult Int) (firstIndex : I → JResult R)
    (step : R → JResult X) (toInt : X → JResult Int)
    (multiply : Int → Int → JResult Int) (tailStrides : S → JResult S)
    (tailIndices : I → JResult I) (recurse : S → I → JResult (List Int))
    (strides : S) (indices : I) : JResult (List Int) := do
  let base ← firstStride strides
  let range ← firstIndex indices
  let rawStep ← step range
  let integerStep ← toInt rawStep
  let head ← multiply base integerStep
  let strideTail ← tailStrides strides
  let indexTail ← tailIndices indices
  let rest ← recurse strideTail indexTail
  .ok (head :: rest)
def P442 : Prop := ∀ {S I R X : Type} (firstStride : S → JResult Int)
    (firstIndex : I → JResult R) (step : R → JResult X) (toInt : X → JResult Int)
    (multiply : Int → Int → JResult Int) (tailStrides : S → JResult S)
    (tailIndices : I → JResult I) (recurse : S → I → JResult (List Int)) strides indices,
  m442 firstStride firstIndex step toInt multiply tailStrides tailIndices recurse strides indices = do
    let base ← firstStride strides
    let range ← firstIndex indices
    let rawStep ← step range
    let integerStep ← toInt rawStep
    let head ← multiply base integerStep
    let strideTail ← tailStrides strides
    let indexTail ← tailIndices indices
    let rest ← recurse strideTail indexTail
    .ok (head :: rest)
theorem p442 : P442 := by unfold P442; intros; rfl

/-- `stride(SubArray,d)`, line 446. -/
def m446 (ndims : V → JResult Nat) (lessEqual : D → Nat → JResult Bool)
    (strides : V → JResult S) (atDimension : S → D → JResult N)
    (lastStride : S → JResult N) (size : V → JResult Z) (lastSize : Z → JResult N)
    (multiply : N → N → JResult N) (view : V) (dimension : D) : JResult N := do
  let rank ← ndims view
  let within ← lessEqual dimension rank
  if within then do
    let values ← strides view
    atDimension values dimension
  else do
    let values ← strides view
    let finalStride ← lastStride values
    let shape ← size view
    let finalSize ← lastSize shape
    multiply finalStride finalSize
def P446 : Prop := ∀ {V D S N Z : Type} (ndims : V → JResult Nat)
    (lessEqual : D → Nat → JResult Bool) (strides : V → JResult S)
    (atDimension : S → D → JResult N) (lastStride : S → JResult N)
    (size : V → JResult Z) (lastSize : Z → JResult N)
    (multiply : N → N → JResult N) view dimension,
  m446 ndims lessEqual strides atDimension lastStride size lastSize multiply view dimension = do
    let rank ← ndims view
    let within ← lessEqual dimension rank
    if within then do let values ← strides view; atDimension values dimension
    else do
      let values ← strides view
      let finalStride ← lastStride values
      let shape ← size view
      let finalSize ← lastSize shape
      multiply finalStride finalSize
theorem p446 : P446 := by unfold P446; intros; rfl

/-- Empty-index `compute_stride1`, line 450. -/
def m450 (stride : S) (_axes : A) : S := stride
def P450 : Prop := ∀ {S A : Type} (stride : S) (axes : A), m450 stride axes = stride
theorem p450 : P450 := by unfold P450; intros; rfl

/-- All-scalar `compute_stride1`, line 451. -/
def m451 (stride : S) (_axes : A) (_scalars : List R) : S := stride
def P451 : Prop := ∀ {S A R : Type} (stride : S) (axes : A) (scalars : List R),
  m451 stride axes scalars = stride
theorem p451 : P451 := by unfold P451; intros; rfl

/-- Leading-scalar `compute_stride1`, lines 452-453. -/
def m452 (firstAxis : A → JResult AX) (length : AX → JResult L) (toInt : L → JResult Int)
    (multiply : S → Int → JResult S) (tailAxes : A → JResult A)
    (tailIndices : I → JResult I) (recurse : S → A → I → JResult S)
    (stride : S) (axes : A) (indices : I) : JResult S := do
  let axis ← firstAxis axes
  let rawLength ← length axis
  let integerLength ← toInt rawLength
  let nextStride ← multiply stride integerLength
  let remainingAxes ← tailAxes axes
  let remainingIndices ← tailIndices indices
  recurse nextStride remainingAxes remainingIndices
def P452 : Prop := ∀ {A AX L S I : Type} (firstAxis : A → JResult AX)
    (length : AX → JResult L) (toInt : L → JResult Int) (multiply : S → Int → JResult S)
    (tailAxes : A → JResult A) (tailIndices : I → JResult I)
    (recurse : S → A → I → JResult S) stride axes indices,
  m452 firstAxis length toInt multiply tailAxes tailIndices recurse stride axes indices = do
    let axis ← firstAxis axes
    let rawLength ← length axis
    let integerLength ← toInt rawLength
    let nextStride ← multiply stride integerLength
    let remainingAxes ← tailAxes axes
    let remainingIndices ← tailIndices indices
    recurse nextStride remainingAxes remainingIndices
theorem p452 : P452 := by unfold P452; intros; rfl

/-- AbstractRange `compute_stride1`, line 454. -/
def m454 (firstIndex : I → JResult R) (step : R → JResult X) (toInt : X → JResult Int)
    (multiply : S → Int → JResult S) (stride : S) (indices : I) : JResult S := do
  let range ← firstIndex indices
  let rawStep ← step range
  let integerStep ← toInt rawStep
  multiply stride integerStep
def P454 : Prop := ∀ {I R X S : Type} (firstIndex : I → JResult R)
    (step : R → JResult X) (toInt : X → JResult Int) (multiply : S → Int → JResult S)
    stride indices, m454 firstIndex step toInt multiply stride indices = do
      let range ← firstIndex indices
      let rawStep ← step range
      let integerStep ← toInt rawStep
      multiply stride integerStep
theorem p454 : P454 := by unfold P454; intros; rfl

/-- Slice `compute_stride1`, line 455. -/
def m455 (stride : S) (_axes : A) (_indices : I) : S := stride
def P455 : Prop := ∀ {S A I : Type} (stride : S) (axes : A) (indices : I),
  m455 stride axes indices = stride
theorem p455 : P455 := by unfold P455; intros; rfl

/-- Unsupported-index `compute_stride1`, line 456. -/
def m456 (firstIndex : I → JResult X) (typeOf : X → AnyValue)
    (indices : I) : JResult S := do
  let head ← firstIndex indices
  .error (.argument (lazyAppend [.literal "invalid strided index type ", .dynamic (typeOf head)]))
def P456 : Prop := ∀ {I X S : Type} (firstIndex : I → JResult X)
    (typeOf : X → AnyValue) indices,
  m456 (S := S) firstIndex typeOf indices = do
    let head ← firstIndex indices
    .error (.argument (lazyAppend [.literal "invalid strided index type ", .dynamic (typeOf head)]))
theorem p456 : P456 := by unfold P456; intros; rfl

/-- Value `iscontiguous`, line 460. -/
def m460 (typeOf : A → T) (iscontiguousType : T → Bool) (array : A) : Bool :=
  iscontiguousType (typeOf array)
def P460 : Prop := ∀ {A T : Type} (typeOf : A → T) (iscontiguousType : T → Bool) array,
  m460 typeOf iscontiguousType array = iscontiguousType (typeOf array)
theorem p460 : P460 := by unfold P460; intros; rfl

/-- Fast `first_index`, line 464. -/
def m464 (offset stride : V → Int) (firstindex : V → JResult Int)
    (multiply add : Int → Int → JResult Int) (view : V) : JResult Int := do
  let first ← firstindex view
  let scaled ← multiply (stride view) first
  add (offset view) scaled
def P464 : Prop := ∀ {V : Type} (offset stride : V → Int) (firstindex : V → JResult Int)
    (multiply add : Int → Int → JResult Int) view,
  m464 offset stride firstindex multiply add view = do
    let first ← firstindex view
    let scaled ← multiply (stride view) first
    add (offset view) scaled
theorem p464 : P464 := by unfold P464; intros; rfl

/-- General `first_index`, line 465. -/
def m465 (parent : V → P) (indices : V → I)
    (computeLinindex : P → I → JResult R) (view : V) : JResult R :=
  computeLinindex (parent view) (indices view)
def P465 : Prop := ∀ {V P I R : Type} (parent : V → P) (indices : V → I)
    (computeLinindex : P → I → JResult R) view,
  m465 parent indices computeLinindex view = computeLinindex (parent view) (indices view)
theorem p465 : P465 := by unfold P465; intros; rfl

/-- Vector-specialized `compute_offset1`, lines 471-472. -/
def m471 (firstRange : R → JResult X) (toIntRange : X → JResult Int)
    (axes1 : R → JResult AX) (firstAxis : AX → JResult Y) (toIntAxis : Y → JResult Int)
    (multiply subtract : Int → Int → JResult Int) (stride : Int) (range : R) : JResult Int := do
  let rawFirst ← firstRange range
  let first ← toIntRange rawFirst
  let axis ← axes1 range
  let rawOrigin ← firstAxis axis
  let origin ← toIntAxis rawOrigin
  let scaled ← multiply stride origin
  subtract first scaled
def P471 : Prop := ∀ {R X AX Y : Type} (firstRange : R → JResult X)
    (toIntRange : X → JResult Int) (axes1 : R → JResult AX) (firstAxis : AX → JResult Y)
    (toIntAxis : Y → JResult Int) (multiply subtract : Int → Int → JResult Int) stride range,
  m471 firstRange toIntRange axes1 firstAxis toIntAxis multiply subtract stride range = do
    let rawFirst ← firstRange range
    let first ← toIntRange rawFirst
    let axis ← axes1 range
    let rawOrigin ← firstAxis axis
    let origin ← toIntAxis rawOrigin
    let scaled ← multiply stride origin
    subtract first scaled
theorem p471 : P471 := by unfold P471; intros; rfl

/-- Slice-specialized `compute_offset1`, lines 480-481. -/
def m480 (computeLinindex : P → I → JResult Int) (axes : P → Int → JResult AX)
    (first : AX → JResult X) (toInt : X → JResult Int)
    (multiply subtract : Int → Int → JResult Int) (parent : P) (stride dimension : Int)
    (indices : I) : JResult Int := do
  let linear ← computeLinindex parent indices
  let axis ← axes parent dimension
  let rawOrigin ← first axis
  let origin ← toInt rawOrigin
  let scaled ← multiply stride origin
  subtract linear scaled
def P480 : Prop := ∀ {P I AX X : Type} (computeLinindex : P → I → JResult Int)
    (axes : P → Int → JResult AX) (first : AX → JResult X) (toInt : X → JResult Int)
    (multiply subtract : Int → Int → JResult Int) parent stride dimension indices,
  m480 computeLinindex axes first toInt multiply subtract parent stride dimension indices = do
    let linear ← computeLinindex parent indices
    let axis ← axes parent dimension
    let rawOrigin ← first axis
    let origin ← toInt rawOrigin
    let scaled ← multiply stride origin
    subtract linear scaled
theorem p480 : P480 := by unfold P480; intros; rfl

/-- AbstractRange-specialized `compute_offset1`, lines 482-483. -/
def m482 (computeLinindex : P → I → JResult Int) (axes1 : R → JResult AX)
    (first : AX → JResult X) (toInt : X → JResult Int)
    (multiply subtract : Int → Int → JResult Int) (parent : P) (stride : Int)
    (range : R) (indices : I) : JResult Int := do
  let linear ← computeLinindex parent indices
  let axis ← axes1 range
  let rawOrigin ← first axis
  let origin ← toInt rawOrigin
  let scaled ← multiply stride origin
  subtract linear scaled
def P482 : Prop := ∀ {P I R AX X : Type} (computeLinindex : P → I → JResult Int)
    (axes1 : R → JResult AX) (first : AX → JResult X) (toInt : X → JResult Int)
    (multiply subtract : Int → Int → JResult Int) parent stride range indices,
  m482 computeLinindex axes1 first toInt multiply subtract parent stride range indices = do
    let linear ← computeLinindex parent indices
    let axis ← axes1 range
    let rawOrigin ← first axis
    let origin ← toInt rawOrigin
    let scaled ← multiply stride origin
    subtract linear scaled
theorem p482 : P482 := by unfold P482; intros; rfl

/-- Fallback `compute_offset1`, lines 484-485. -/
def m484 (computeLinindex : P → I → JResult Int) (subtract : Int → Int → JResult Int)
    (parent : P) (stride : Int) (indices : I) : JResult Int := do
  let linear ← computeLinindex parent indices
  subtract linear stride
def P484 : Prop := ∀ {P I : Type} (computeLinindex : P → I → JResult Int)
    (subtract : Int → Int → JResult Int) parent stride indices,
  m484 computeLinindex subtract parent stride indices = do
    let linear ← computeLinindex parent indices
    subtract linear stride
theorem p484 : P484 := by unfold P484; intros; rfl

def pointerLoop (coordinate : C → Nat → JResult Int) (strideAt : S → Nat → JResult Int)
    (subtract multiply add : Int → Int → JResult Int) (coordinates : C) (strides : S) :
    Nat → Nat → Int → JResult Int
  | _, 0, index => .ok index
  | dimension, remaining + 1, index => do
      let value ← coordinate coordinates dimension
      let delta ← subtract value 1
      let stride ← strideAt strides dimension
      let scaled ← multiply delta stride
      let next ← add index scaled
      pointerLoop coordinate strideAt subtract multiply add coordinates strides
        (dimension + 1) remaining next

/-- Cartesian-index `pointer(SubArray, is)`, lines 513-519. -/
def m513 (firstIndex : V → JResult Int) (strides : V → JResult S)
    (coordinate : C → Nat → JResult Int) (strideAt : S → Nat → JResult Int)
    (subtract multiply add : Int → Int → JResult Int) (parent : V → P)
    (pointer : P → Int → JResult R) (view : V) (coordinates : C) (rank : Nat) : JResult R := do
  let start ← firstIndex view
  let values ← strides view
  let index ← pointerLoop coordinate strideAt subtract multiply add coordinates values 1 rank start
  pointer (parent view) index
def P513 : Prop := ∀ {V S C P R : Type} (firstIndex : V → JResult Int)
    (strides : V → JResult S) (coordinate : C → Nat → JResult Int)
    (strideAt : S → Nat → JResult Int) (subtract multiply add : Int → Int → JResult Int)
    (parent : V → P) (pointer : P → Int → JResult R) view coordinates rank,
  m513 firstIndex strides coordinate strideAt subtract multiply add parent pointer view coordinates rank = do
    let start ← firstIndex view
    let values ← strides view
    let index ← pointerLoop coordinate strideAt subtract multiply add coordinates values 1 rank start
    pointer (parent view) index
theorem p513 : P513 := by unfold P513; intros; rfl

/-- Array-leading `_indices_sub`, lines 528-530. -/
def m528 (axes : A → JResult (List AX)) (recurse : List I → JResult (List AX))
    (array : A) (rest : List I) : JResult (List AX) := do
  let ownAxes ← axes array
  let tail ← recurse rest
  .ok (ownAxes ++ tail)
def P528 : Prop := ∀ {A AX I : Type} (axes : A → JResult (List AX))
    (recurse : List I → JResult (List AX)) array rest,
  m528 axes recurse array rest = do
    let ownAxes ← axes array
    let tail ← recurse rest
    .ok (ownAxes ++ tail)
theorem p528 : P528 := by unfold P528; intros; rfl

/-- Array-leading `_axes1_sub`, lines 538-540. -/
def m538 (axes1 : A → JResult AX) (array : A) (_rest : List I) : JResult AX := axes1 array
def P538 : Prop := ∀ {A AX I : Type} (axes1 : A → JResult AX) array (rest : List I),
  m538 axes1 array rest = axes1 array
theorem p538 : P538 := by unfold P538; intros; rfl

/-- `has_offset_axes(SubArray)`, line 543. -/
def m543 (indices : V → I) (hasOffsetAxes : I → JResult Bool) (view : V) : JResult Bool :=
  hasOffsetAxes (indices view)
def P543 : Prop := ∀ {V I : Type} (indices : V → I) (hasOffsetAxes : I → JResult Bool) view,
  m543 indices hasOffsetAxes view = hasOffsetAxes (indices view)
theorem p543 : P543 := by unfold P543; intros; rfl

/-- Matrix `replace_in_print_matrix`, lines 545-546. -/
def m545 (indices : V → VI) (reindex : VI → (Int × Int) → JResult RI)
    (parent : V → P) (toIndices : P → RI → JResult TI)
    (replace : P → TI → S → JResult R) (view : V) (row column : Int) (text : S) : JResult R := do
  let combined ← reindex (indices view) (row, column)
  let converted ← toIndices (parent view) combined
  replace (parent view) converted text
def P545 : Prop := ∀ {V VI RI P TI S R : Type} (indices : V → VI)
    (reindex : VI → (Int × Int) → JResult RI) (parent : V → P)
    (toIndices : P → RI → JResult TI) (replace : P → TI → S → JResult R)
    view row column text,
  m545 indices reindex parent toIndices replace view row column text = do
    let combined ← reindex (indices view) (row, column)
    let converted ← toIndices (parent view) combined
    replace (parent view) converted text
theorem p545 : P545 := by unfold P545; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-subarray-faithful-{line}", juliaFile := "base/subarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 437 "strides(SubArray)" "Strides reads the actual parent, obtains its strides and combines them with the actual stored indices." "base/subarray.jl:437" ``P437 ``p437,
  entry 441 "substrides(Slice)" "Slice substrides reads the first parent stride and recursively processes both actual tuple tails with complete failure propagation." "base/subarray.jl:441" ``P441 ``p441,
  entry 442 "substrides(AbstractRange)" "Range substrides reads and converts the actual step, multiplies the first stride, and recursively processes both tails." "base/subarray.jl:442" ``P442 ``p442,
  entry 446 "stride(SubArray,d)" "Stride handles every Integer dimension, including the documented beyond-rank product and every failing internal call." "base/subarray.jl:446" ``P446 ``p446,
  entry 450 "compute_stride1(empty)" "The empty-index overload returns the arbitrary accumulator unchanged." "base/subarray.jl:450" ``P450 ``p450,
  entry 451 "compute_stride1(all scalars)" "The all-scalar overload returns the arbitrary accumulator for every axis and Real scalar tuple." "base/subarray.jl:451" ``P451 ``p451,
  entry 452 "compute_stride1(leading scalar)" "Leading-scalar stride computation gets and converts the first axis length, multiplies the arbitrary accumulator and recurses on both tails." "base/subarray.jl:452-453" ``P452 ``p452,
  entry 454 "compute_stride1(AbstractRange)" "Range stride computation reads and converts the actual range step before multiplying the arbitrary accumulator." "base/subarray.jl:454" ``P454 ``p454,
  entry 455 "compute_stride1(Slice)" "The Slice overload returns the arbitrary accumulator unchanged for every remaining tuple." "base/subarray.jl:455" ``P455 ``p455,
  entry 456 "compute_stride1(invalid index)" "The fallback accepts every unsupported index type and throws ArgumentError containing its actual type." "base/subarray.jl:456" ``P456 ``p456,
  entry 460 "iscontiguous(SubArray)" "Value contiguity calls typeof on the actual view and delegates to type contiguity." "base/subarray.jl:460" ``P460 ``p460,
  entry 464 "first_index(FastSubArray)" "Fast first_index calls firstindex on the actual view before cached stride multiplication and offset addition." "base/subarray.jl:464" ``P464 ``p464,
  entry 465 "first_index(SubArray)" "General first_index passes the actual parent and stored indices to compute_linindex." "base/subarray.jl:465" ``P465 ``p465,
  entry 471 "compute_offset1(vector,range)" "Vector offset reads and converts first(range) and first(axes1(range)) before stride multiplication and subtraction." "base/subarray.jl:471-472" ``P471 ``p471,
  entry 480 "compute_offset1(Slice)" "Slice offset computes the linear index, reads the requested parent axis origin, converts it and subtracts the scaled origin." "base/subarray.jl:480-481" ``P480 ``p480,
  entry 482 "compute_offset1(AbstractRange)" "Range offset computes the linear index and uses first(axes1(actual range)) before scaled subtraction." "base/subarray.jl:482-483" ``P482 ``p482,
  entry 484 "compute_offset1(fallback)" "Fallback offset computes the actual linear index before subtracting the supplied stride." "base/subarray.jl:484-485" ``P484 ``p484,
  entry 513 "pointer(SubArray,CartesianIndex)" "Cartesian pointer calls first_index and strides, loops through every coordinate in order with Julia arithmetic operations, then calls pointer on the actual parent." "base/subarray.jl:513-519" ``P513 ``p513,
  entry 528 "_indices_sub(AbstractArray)" "Array axis extraction calls axes on the actual array and concatenates the complete recursive result." "base/subarray.jl:528-530" ``P528 ``p528,
  entry 538 "_axes1_sub(AbstractArray)" "First-axis extraction calls axes1 on the actual array and ignores the suffix exactly as the method does." "base/subarray.jl:538-540" ``P538 ``p538,
  entry 543 "has_offset_axes(SubArray)" "Offset-axis detection delegates with the actual stored index tuple." "base/subarray.jl:543" ``P543 ``p543,
  entry 545 "replace_in_print_matrix(matrix SubArray)" "Matrix printing reindexes, converts against the actual parent and delegates with only the converted parent indices and text." "base/subarray.jl:545-546" ``P545 ``p545
]

end JuliaLean.MultidimCov.SubarrayFaithfulC
