import JuliaLean.MultidimCov.MultidimensionalCartesianFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalIndicesFaithful

open JuliaLean
open JuliaLean.Registry
open MultidimensionalCartesianFaithful

abbrev CIAxis := MultidimensionalCartesianFaithful.Axis

abbrev Result (α : Type) := Except Error α

structure CartesianIndices where
  indices : List CIAxis
  deriving Repr, DecidableEq

inductive DimSpec where
  | integer (value : IntegerValue)
  | range (first step last : IntegerValue)
  deriving Repr, DecidableEq

def convertAxis : DimSpec → Result CIAxis
  | .integer value => do
      let converted ← toInt value
      pure ⟨JInt.lit .i64 1, converted, JInt.lit .i64 1⟩
  | .range first step last => do
      pure ⟨← toInt first, ← toInt last, ← toInt step⟩

def m299 (ranges : List DimSpec) : Result CartesianIndices :=
  CartesianIndices.mk <$> ranges.mapM convertAxis
def P299 : Prop := ∀ ranges, m299 ranges = (CartesianIndices.mk <$> ranges.mapM convertAxis)
theorem p299 : P299 := by simp [P299, m299]

def m304 (index : Cartesian) : CartesianIndices :=
  ⟨index.coordinates.map fun coordinate => ⟨JInt.lit .i64 1, coordinate, JInt.lit .i64 1⟩⟩
def P304 : Prop := ∀ index,
  m304 index = ⟨index.coordinates.map fun coordinate => ⟨JInt.lit .i64 1, coordinate, JInt.lit .i64 1⟩⟩
theorem p304 : P304 := by simp [P304, m304]

def m305 (specs : List DimSpec) : Result CartesianIndices := m299 specs
def P305 : Prop := ∀ specs, m305 specs = m299 specs
theorem p305 : P305 := by simp [P305, m305]

def m308 {A : Type} (axes : A → List CIAxis) (array : A) : CartesianIndices := ⟨axes array⟩
def P308 : Prop := ∀ {A : Type} (axes : A → List CIAxis) array, m308 axes array = ⟨axes array⟩
theorem p308 : P308 := by simp [P308, m308]

def oneTo (value : IntegerValue) : Result CIAxis := do
  let converted ← toInt value
  pure ⟨JInt.lit .i64 1, converted, JInt.lit .i64 1⟩
def m310 (value : Bool) : Result CIAxis := oneTo ⟨if value then 1 else 0⟩
def P310 : Prop := ∀ value, m310 value = oneTo ⟨if value then 1 else 0⟩
theorem p310 : P310 := by simp [P310, m310]
def m311 (value : IntegerValue) : Result CIAxis := oneTo value
def P311 : Prop := ∀ value, m311 value = oneTo value
theorem p311 : P311 := by simp [P311, m311]

def m312 (first last : IntegerValue) : Result CIAxis := do
  pure ⟨← toInt first, ← toInt last, JInt.lit .i64 1⟩
def P312 : Prop := ∀ first last, m312 first last = do
  pure ⟨← toInt first, ← toInt last, JInt.lit .i64 1⟩
theorem p312 : P312 := by simp [P312, m312]

def m313 (first step last : IntegerValue) : Result CIAxis := do
  pure ⟨← toInt first, ← toInt last, ← toInt step⟩
def P313 : Prop := ∀ first step last, m313 first step last = do
  pure ⟨← toInt first, ← toInt last, ← toInt step⟩
theorem p313 : P313 := by simp [P313, m313]

def m315 (render : CIAxis → String) (initial : String) (iter : CartesianIndices) : String :=
  initial ++ "CartesianIndices(" ++ String.intercalate ", " (iter.indices.map render) ++ ")"
def P315 : Prop := ∀ render initial iter,
  m315 render initial iter = initial ++ "CartesianIndices(" ++
    String.intercalate ", " (iter.indices.map render) ++ ")"
theorem p315 : P315 := by simp [P315, m315]

def m322 (render : CartesianIndices → String) (iter : CartesianIndices) : String := render iter
def P322 : Prop := ∀ render iter, m322 render iter = render iter
theorem p322 : P322 := by simp [P322, m322]

def m350 (first last : Cartesian) : CartesianIndices :=
  ⟨List.zipWith (fun a b => ⟨a, b, JInt.lit .i64 1⟩) first.coordinates last.coordinates⟩
def P350 : Prop := ∀ first last,
  m350 first last = ⟨List.zipWith (fun a b => ⟨a, b, JInt.lit .i64 1⟩) first.coordinates last.coordinates⟩
theorem p350 : P350 := by simp [P350, m350]

def m352 (first step last : Cartesian) : CartesianIndices :=
  ⟨List.zipWith (fun pair b => ⟨pair.1, b, pair.2⟩)
    (List.zip first.coordinates step.coordinates) last.coordinates⟩
def P352 : Prop := ∀ first step last,
  m352 first step last = ⟨List.zipWith (fun pair b => ⟨pair.1, b, pair.2⟩)
    (List.zip first.coordinates step.coordinates) last.coordinates⟩
theorem p352 : P352 := by simp [P352, m352]

def m355 {T : Type} (promoteRangeTypes : T → T → T) (left right : T) : T := promoteRangeTypes left right
def P355 : Prop := ∀ {T : Type} (promoteRangeTypes : T → T → T) left right,
  m355 promoteRangeTypes left right = promoteRangeTypes left right
theorem p355 : P355 := by simp [P355, m355]

def convertAxes {T : Type} (convert : CIAxis → Result T) (iter : CartesianIndices) : Result (List T) :=
  iter.indices.mapM convert

def m360 {T : Type} (convert : CIAxis → Result T) (iter : CartesianIndices) := convertAxes convert iter
def P360 : Prop := ∀ {T : Type} (convert : CIAxis → Result T) iter, m360 convert iter = convertAxes convert iter
theorem p360 : P360 := by simp [P360, m360]
def m363 := @m360
def P363 : Prop := ∀ {T : Type} (convert : CIAxis → Result T) iter, m363 convert iter = convertAxes convert iter
theorem p363 : P363 := by simp [P363, m363, m360]
def m365 := @m360
def P365 : Prop := ∀ {T : Type} (convert : CIAxis → Result T) iter, m365 convert iter = convertAxes convert iter
theorem p365 : P365 := by simp [P365, m365, m360]
def m367 := @m360
def P367 : Prop := ∀ {T : Type} (convert : CIAxis → Result T) iter, m367 convert iter = convertAxes convert iter
theorem p367 : P367 := by simp [P367, m367, m360]
def m369 := @m360
def P369 : Prop := ∀ {T : Type} (convert : CIAxis → Result T) iter, m369 convert iter = convertAxes convert iter
theorem p369 : P369 := by simp [P369, m369, m360]
def m371 := @m360
def P371 : Prop := ∀ {T : Type} (convert : CIAxis → Result T) iter, m371 convert iter = convertAxes convert iter
theorem p371 : P371 := by simp [P371, m371, m360]
def m373 := @m360
def P373 : Prop := ∀ {T : Type} (convert : CIAxis → Result T) iter, m373 convert iter = convertAxes convert iter
theorem p373 : P373 := by simp [P373, m373, m360]
def m375 := @m360
def P375 : Prop := ∀ {T : Type} (convert : CIAxis → Result T) iter, m375 convert iter = convertAxes convert iter
theorem p375 : P375 := by simp [P375, m375, m360]

def m378 (convert : List CIAxis → Result (List CIAxis)) (iter : CartesianIndices) : Result CartesianIndices :=
  CartesianIndices.mk <$> convert iter.indices
def P378 : Prop := ∀ convert iter, m378 convert iter = (CartesianIndices.mk <$> convert iter.indices)
theorem p378 : P378 := by simp [P378, m378]

def m382 (left right : CartesianIndices) : Bool := left.indices = right.indices
def P382 : Prop := ∀ left right, m382 left right = (left.indices = right.indices)
theorem p382 : P382 := by simp [P382, m382]

def axisLength (axis : CIAxis) : Nat :=
  if axis.step.val = 0 then 0 else ((axis.last.val - axis.first.val).natAbs / axis.step.val.natAbs) + 1
def m387 (iter : CartesianIndices) : List CIAxis :=
  iter.indices.map fun axis => ⟨JInt.lit .i64 1, JInt.wrap .i64 (axisLength axis), JInt.lit .i64 1⟩
def P387 : Prop := ∀ iter, m387 iter =
  iter.indices.map fun axis => ⟨JInt.lit .i64 1, JInt.wrap .i64 (axisLength axis), JInt.lit .i64 1⟩
theorem p387 : P387 := by simp [P387, m387]

def m388 (iter : CartesianIndices) : Bool := iter.indices.any fun axis => axis.first.val ≠ 1
def P388 : Prop := ∀ iter, m388 iter = (iter.indices.any fun axis => axis.first.val ≠ 1)
theorem p388 : P388 := by simp [P388, m388]

def axisAt (axis : CIAxis) (index : Int) : Result I64 :=
  if index < 1 || axisLength axis < index then .error .bounds
  else .ok (axis.first + axis.step * JInt.wrap .i64 (index - 1))
def m400 (iter : CartesianIndices) (indices : List Int) : Result Cartesian := do
  pure ⟨← (iter.indices.zip indices).mapM fun pair => axisAt pair.1 pair.2⟩
def P400 : Prop := ∀ iter indices, m400 iter indices = do
  pure ⟨← (iter.indices.zip indices).mapM fun pair => axisAt pair.1 pair.2⟩
theorem p400 : P400 := by simp [P400, m400]

inductive AxisIndex where | colon | range (positions : List Int) deriving Repr, DecidableEq
def selectAxis (axis : CIAxis) : AxisIndex → Result CIAxis
  | .colon => .ok axis
  | .range [] => .ok ⟨axis.first, axis.first - axis.step, axis.step⟩
  | .range positions => do
      let first ← axisAt axis positions.head!
      let last ← axisAt axis positions.getLast!
      pure ⟨first, last, axis.step⟩
def m413 (iter : CartesianIndices) (indices : List AxisIndex) : Result CartesianIndices := do
  pure ⟨← (iter.indices.zip indices).mapM fun pair => selectAxis pair.1 pair.2⟩
def P413 : Prop := ∀ iter indices, m413 iter indices = do
  pure ⟨← (iter.indices.zip indices).mapM fun pair => selectAxis pair.1 pair.2⟩
theorem p413 : P413 := by simp [P413, m413]

def m421 (iter selector : CartesianIndices) : Result CartesianIndices :=
  m413 iter (selector.indices.map fun axis =>
    .range ((List.range (axisLength axis)).map fun (n : Nat) => Int.ofNat n + 1))
def P421 : Prop := ∀ iter selector,
  m421 iter selector = m413 iter (selector.indices.map fun axis =>
    .range ((List.range (axisLength axis)).map fun (n : Nat) => Int.ofNat n + 1))
theorem p421 : P421 := by simp [P421, m421]

def m428 (iter : CartesianIndices) (indices : List AxisIndex) : Result CartesianIndices := m413 iter indices
def P428 : Prop := ∀ iter indices, m428 iter indices = m413 iter indices
theorem p428 : P428 := by simp [P428, m428]
def m431 (iter selector : CartesianIndices) : Result CartesianIndices := m421 iter selector
def P431 : Prop := ∀ iter selector, m431 iter selector = m421 iter selector
theorem p431 : P431 := by simp [P431, m431]

def m435 {A : Type} (axes : A → List CIAxis) (array : A) : CartesianIndices := ⟨axes array⟩
def P435 : Prop := ∀ {A : Type} (axes : A → List CIAxis) array, m435 axes array = ⟨axes array⟩
theorem p435 : P435 := by simp [P435, m435]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}", juliaFile := "base/multidimensional.jl",
    juliaFns := [name], statement, source := s!"base/multidimensional.jl:{line}; CartesianIndices source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalIndicesFaithful
