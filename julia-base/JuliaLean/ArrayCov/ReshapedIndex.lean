import JuliaLean.Core
import JuliaLean.ArrayCov.ReshapedSimple

namespace JuliaLean.ArrayCov

def reshaped270Ind2subEmpty (_axes : List (List JInt64)) (index : JInt64) : List JInt64 :=
  [index]

def reshaped271Ind2sub (aux : List (List JInt64) → List JInt64 → JInt64 → List JInt64)
    (axes : List (List JInt64)) (divisors : List JInt64) (index : JInt64) : List JInt64 :=
  aux axes divisors (index - JInt.lit .i64 1)

def reshaped272Ind2subAuxEmpty (first : List JInt64 → JInt64)
    (axes : List (List JInt64)) (index : JInt64) : List JInt64 :=
  [index + first (axes.getLastD [])]

def reshaped273Ind2subAux (divrem : JInt64 → JInt64 → JInt64 × JInt64)
    (first : List JInt64 → JInt64) :
    List (List JInt64) → List JInt64 → JInt64 → List JInt64
  | axes, [], index => reshaped272Ind2subAuxEmpty first axes index
  | [], _ :: _, index => [index]
  | axis :: axes, divisor :: divisors, index =>
      let (quotient, remainder) := divrem index divisor
      (remainder + first axis) ::
        reshaped273Ind2subAux divrem first axes divisors quotient

def reshaped277OffsetVector (first : List JInt64 → JInt64)
    (index : JInt64) (axes : List (List JInt64)) : JInt64 :=
  index + first (axes.getD 0 []) - JInt.lit .i64 1

def reshaped278OffsetGeneral (index : JInt64) (_axes : List (List JInt64)) : JInt64 :=
  index

def ReshapedIndexMathCorrect : Prop :=
  (∀ axes index, reshaped270Ind2subEmpty axes index = [index]) ∧
  (∀ aux axes divisors index, reshaped271Ind2sub aux axes divisors index =
      aux axes divisors (index - JInt.lit .i64 1)) ∧
  (∀ first axes index, reshaped272Ind2subAuxEmpty first axes index =
      [index + first (axes.getLastD [])]) ∧
  (∀ divrem first axis axes divisor divisors index,
      reshaped273Ind2subAux divrem first (axis :: axes) (divisor :: divisors) index =
      let (quotient, remainder) := divrem index divisor
      (remainder + first axis) ::
        reshaped273Ind2subAux divrem first axes divisors quotient) ∧
  (∀ first index axes, reshaped277OffsetVector first index axes =
      index + first (axes.getD 0 []) - JInt.lit .i64 1) ∧
  (∀ index axes, reshaped278OffsetGeneral index axes = index)

theorem reshapedIndexMathCorrect : ReshapedIndexMathCorrect := by
  simp [ReshapedIndexMathCorrect, reshaped270Ind2subEmpty, reshaped271Ind2sub,
    reshaped272Ind2subAuxEmpty, reshaped273Ind2subAux, reshaped277OffsetVector,
    reshaped278OffsetGeneral]

inductive ReshapedIndexError where
  | bounds
  deriving Repr, DecidableEq

abbrev ReshapedIndexJl (α : Type) := Except ReshapedIndexError α

structure ReshapedAccessState where
  parent : List Int
  dims : List JInt64
  axes : List (List JInt64)
  divisors : List JInt64
  deriving Repr, DecidableEq

def reshaped280IsAssignedLinear (checkbounds : ReshapedAccessState → JInt64 → Bool)
    (firstArray firstParent : ReshapedAccessState → JInt64)
    (isassigned : List Int → JInt64 → Bool)
    (array : ReshapedAccessState) (index : JInt64) : Bool :=
  if !checkbounds array index then false
  else
    let parentIndex := index - firstArray array + firstParent array
    isassigned array.parent parentIndex

def reshaped286IsAssignedCartesian
    (checkbounds : ReshapedAccessState → List JInt64 → Bool)
    (size : ReshapedAccessState → List JInt64)
    (axes : List Int → List (List JInt64))
    (sub2ind : List JInt64 → List JInt64 → JInt64)
    (offset : JInt64 → List (List JInt64) → JInt64)
    (ind2sub : List (List JInt64) → List JInt64 → JInt64 → List JInt64)
    (isassigned : List Int → List JInt64 → Bool)
    (array : ReshapedAccessState) (indices : List JInt64) : Bool :=
  if !checkbounds array indices then false
  else
    let parentAxes := axes array.parent
    let linear := offset (sub2ind (size array) indices) parentAxes
    isassigned array.parent (ind2sub parentAxes array.divisors linear)

def reshaped294GetLinear (checkbounds : ReshapedAccessState → JInt64 → Bool)
    (firstArray firstParent : ReshapedAccessState → JInt64)
    (getindex : List Int → JInt64 → ReshapedIndexJl Int)
    (array : ReshapedAccessState) (index : JInt64) : ReshapedIndexJl Int := do
  if checkbounds array index then pure () else throw .bounds
  let parentIndex := index - firstArray array + firstParent array
  getindex array.parent parentIndex

def reshaped300GetCartesian
    (checkbounds : ReshapedAccessState → List JInt64 → Bool)
    (unsafeGet : ReshapedAccessState → List JInt64 → ReshapedIndexJl Int)
    (array : ReshapedAccessState) (indices : List JInt64) : ReshapedIndexJl Int := do
  if checkbounds array indices then pure () else throw .bounds
  unsafeGet array indices

def reshaped304GetReshapedIndex (checkbounds : List Int → JInt64 → Bool)
    (getindex : List Int → JInt64 → ReshapedIndexJl Int)
    (array : ReshapedAccessState) (parentIndex : JInt64) : ReshapedIndexJl Int := do
  if checkbounds array.parent parentIndex then pure () else throw .bounds
  getindex array.parent parentIndex

def reshaped310UnsafeGet
    (size : ReshapedAccessState → List JInt64)
    (axes : List Int → List (List JInt64))
    (sub2ind : List JInt64 → List JInt64 → JInt64)
    (offset : JInt64 → List (List JInt64) → JInt64)
    (ind2sub : List (List JInt64) → List JInt64 → JInt64 → List JInt64)
    (unsafeGetParent : List Int → List JInt64 → ReshapedIndexJl Int)
    (array : ReshapedAccessState) (indices : List JInt64) : ReshapedIndexJl Int :=
  let parentAxes := axes array.parent
  let linear := offset (sub2ind (size array) indices) parentAxes
  unsafeGetParent array.parent (ind2sub parentAxes array.divisors linear)

def reshaped316UnsafeGetScalar (getindex : List Int → JInt64 → Int)
    (parent : List Int) (index : JInt64) : Int := getindex parent index

def reshaped317UnsafeGetTuple (getindex : List Int → List JInt64 → Int)
    (parent : List Int) (indices : List JInt64) : Int := getindex parent indices

def reshaped319SetLinear (checkbounds : ReshapedAccessState → JInt64 → Bool)
    (firstArray firstParent : ReshapedAccessState → JInt64)
    (setindex : List Int → Int → JInt64 → ReshapedIndexJl (List Int))
    (array : ReshapedAccessState) (value : Int) (index : JInt64) :
    ReshapedIndexJl (Int × List Int) := do
  if checkbounds array index then pure () else throw .bounds
  let parentIndex := index - firstArray array + firstParent array
  let parent ← setindex array.parent value parentIndex
  pure (value, parent)

def reshaped325SetCartesian
    (checkbounds : ReshapedAccessState → List JInt64 → Bool)
    (unsafeSet : ReshapedAccessState → Int → List JInt64 →
      ReshapedIndexJl (Int × List Int))
    (array : ReshapedAccessState) (value : Int) (indices : List JInt64) :
    ReshapedIndexJl (Int × List Int) := do
  if checkbounds array indices then pure () else throw .bounds
  unsafeSet array value indices

def reshaped329SetReshapedIndex (checkbounds : List Int → JInt64 → Bool)
    (setindex : List Int → Int → JInt64 → ReshapedIndexJl (List Int))
    (array : ReshapedAccessState) (value : Int) (parentIndex : JInt64) :
    ReshapedIndexJl (Int × List Int) := do
  if checkbounds array.parent parentIndex then pure () else throw .bounds
  let parent ← setindex array.parent value parentIndex
  pure (value, parent)

def reshaped335UnsafeSet
    (size : ReshapedAccessState → List JInt64)
    (axes : List Int → List (List JInt64))
    (sub2ind : List JInt64 → List JInt64 → JInt64)
    (offset : JInt64 → List (List JInt64) → JInt64)
    (ind2sub : List (List JInt64) → List JInt64 → JInt64 → List JInt64)
    (setindex : List Int → Int → List JInt64 → List Int)
    (array : ReshapedAccessState) (value : Int) (indices : List JInt64) : Int × List Int :=
  let parentAxes := axes array.parent
  let linear := offset (sub2ind (size array) indices) parentAxes
  let parentIndices := ind2sub parentAxes array.divisors linear
  (value, setindex array.parent value parentIndices)

def ReshapedAccessCorrect : Prop :=
  (∀ check fa fp assigned array index, reshaped280IsAssignedLinear check fa fp assigned array index =
      if !check array index then false
      else assigned array.parent (index - fa array + fp array)) ∧
  (∀ check size axes sub offset ind assigned array indices,
      reshaped286IsAssignedCartesian check size axes sub offset ind assigned array indices =
      if !check array indices then false
      else
        let parentAxes := axes array.parent
        assigned array.parent
          (ind parentAxes array.divisors (offset (sub (size array) indices) parentAxes))) ∧
  (∀ check fa fp get array index, reshaped294GetLinear check fa fp get array index = do
      if check array index then pure () else throw .bounds
      get array.parent (index - fa array + fp array)) ∧
  (∀ check unsafeGet array indices, reshaped300GetCartesian check unsafeGet array indices = do
      if check array indices then pure () else throw .bounds
      unsafeGet array indices) ∧
  (∀ check get array index, reshaped304GetReshapedIndex check get array index = do
      if check array.parent index then pure () else throw .bounds
      get array.parent index) ∧
  (∀ size axes sub offset ind get array indices,
      reshaped310UnsafeGet size axes sub offset ind get array indices =
      let parentAxes := axes array.parent
      get array.parent (ind parentAxes array.divisors
        (offset (sub (size array) indices) parentAxes))) ∧
  (∀ get parent index, reshaped316UnsafeGetScalar get parent index = get parent index) ∧
  (∀ get parent indices, reshaped317UnsafeGetTuple get parent indices = get parent indices) ∧
  (∀ check fa fp set array value index, reshaped319SetLinear check fa fp set array value index = do
      if check array index then pure () else throw .bounds
      let parent ← set array.parent value (index - fa array + fp array)
      pure (value, parent)) ∧
  (∀ check set array value indices, reshaped325SetCartesian check set array value indices = do
      if check array indices then pure () else throw .bounds
      set array value indices) ∧
  (∀ check set array value index, reshaped329SetReshapedIndex check set array value index = do
      if check array.parent index then pure () else throw .bounds
      let parent ← set array.parent value index
      pure (value, parent)) ∧
  (∀ size axes sub offset ind set array value indices,
      reshaped335UnsafeSet size axes sub offset ind set array value indices =
      let parentAxes := axes array.parent
      let linear := offset (sub (size array) indices) parentAxes
      (value, set array.parent value (ind parentAxes array.divisors linear)))

theorem reshapedAccessCorrect : ReshapedAccessCorrect := by
  simp [ReshapedAccessCorrect, reshaped280IsAssignedLinear,
    reshaped286IsAssignedCartesian, reshaped294GetLinear, reshaped300GetCartesian,
    reshaped304GetReshapedIndex, reshaped310UnsafeGet, reshaped316UnsafeGetScalar,
    reshaped317UnsafeGetTuple, reshaped319SetLinear, reshaped325SetCartesian,
    reshaped329SetReshapedIndex, reshaped335UnsafeSet]

end JuliaLean.ArrayCov
