import JuliaLean.Core
import JuliaLean.ArrayCov.ReinterpretConstruct
import JuliaLean.ArrayCov.ReinterpretSimple

namespace JuliaLean.ArrayCov

inductive ReinterpretShapeError where
  | padding | nonIntegralStride | noncontiguous | arithmetic
  deriving Repr, DecidableEq

abbrev ReinterpretShapeJl (α : Type) := Except ReinterpretShapeError α

def reinterpret205Stride (ndims : ReinterpretValue → Int)
    (strides : ReinterpretValue → List JInt64) (length : ReinterpretValue → JInt64)
    (get : List JInt64 → Int → JInt64) (array : ReinterpretValue) (k : Int) : JInt64 :=
  if k ≤ ndims array then get (strides array) k else length array

def reinterpret222CheckedStrides : List JInt64 → JInt64 →
    ReinterpretShapeJl (List JInt64)
  | [], _ => .ok []
  | stride :: rest, elementSize => do
      let quotient ← JInt.div stride elementSize |>.mapError fun _ => .arithmetic
      let remainder ← JInt.remInt stride elementSize |>.mapError fun _ => .arithmetic
      if remainder.val != 0 then throw .nonIntegralStride
      let tail ← reinterpret222CheckedStrides rest elementSize
      pure (quotient :: tail)

def reinterpret208Strides
    (contiguous : ReinterpretValue → Bool)
    (sizeToStrides : JInt64 → List JInt64 → List JInt64)
    (size stridesParent : ReinterpretValue → List JInt64)
    (elsizeParent : ReinterpretValue → JInt64)
    (targetSize sourceSize : JInt64) (isReshaped : Bool)
    (array : ReinterpretValue) : ReinterpretShapeJl (List JInt64) := do
  if contiguous array then return sizeToStrides (JInt.lit .i64 1) (size array)
  let parentStrides := stridesParent array
  if targetSize = sourceSize then return parentStrides
  let byteStrides := parentStrides.map (· * elsizeParent array)
  if isReshaped && targetSize < sourceSize then
    return JInt.lit .i64 1 :: (← reinterpret222CheckedStrides byteStrides targetSize)
  if byteStrides.getD 0 (JInt.lit .i64 0) != sourceSize then throw .noncontiguous
  let tail ← reinterpret222CheckedStrides byteStrides.tail targetSize
  if isReshaped then return tail else return JInt.lit .i64 1 :: tail

def reinterpret234CheckReadable (subpadding : TypeLayoutModel → TypeLayoutModel → Bool)
    (source target : TypeLayoutModel) (readable : Bool) : ReinterpretShapeJl Unit :=
  if !readable && !subpadding target source then .error .padding else .ok ()

def reinterpret241CheckWritable (subpadding : TypeLayoutModel → TypeLayoutModel → Bool)
    (source target : TypeLayoutModel) (writable : Bool) : ReinterpretShapeJl Unit :=
  if !writable && !subpadding source target then .error .padding else .ok ()

inductive IndexStyleModel where
  | linear | cartesian | staticCartesian (k : JInt64)
  deriving Repr, DecidableEq

def reinterpret260IndexStyle (parentStyle : Int → IndexStyleModel)
    (parentType : Int) : IndexStyleModel :=
  if parentStyle parentType = .linear then .linear else .cartesian

def reinterpret263IndexStyleReshaped (parentStyle : Int → IndexStyleModel)
    (parentType : Int) (targetSize sourceSize : JInt64) : ReinterpretShapeJl IndexStyleModel := do
  if targetSize < sourceSize then
    if parentStyle parentType = .linear then
      let k ← JInt.div sourceSize targetSize |>.mapError fun _ => .arithmetic
      return .staticCartesian k
    return .cartesian
  return parentStyle parentType

def ReinterpretStridesAndChecksCorrect : Prop :=
  (∀ ndims strides length get array k, reinterpret205Stride ndims strides length get array k =
      if k ≤ ndims array then get (strides array) k else length array) ∧
  (∀ sub source target readable, reinterpret234CheckReadable sub source target readable =
      if !readable && !sub target source then .error .padding else .ok ()) ∧
  (∀ sub source target writable, reinterpret241CheckWritable sub source target writable =
      if !writable && !sub source target then .error .padding else .ok ()) ∧
  (∀ style parent, reinterpret260IndexStyle style parent =
      if style parent = .linear then .linear else .cartesian)

theorem reinterpretStridesAndChecksCorrect : ReinterpretStridesAndChecksCorrect := by
  simp [ReinterpretStridesAndChecksCorrect, reinterpret205Stride,
    reinterpret234CheckReadable, reinterpret241CheckWritable, reinterpret260IndexStyle]

def ReinterpretStrideCalculationCorrect : Prop :=
  (∀ elementSize, reinterpret222CheckedStrides [] elementSize = .ok []) ∧
  (∀ stride rest elementSize, reinterpret222CheckedStrides (stride :: rest) elementSize = do
      let quotient ← JInt.div stride elementSize |>.mapError fun _ => .arithmetic
      let remainder ← JInt.remInt stride elementSize |>.mapError fun _ => .arithmetic
      if remainder.val != 0 then throw .nonIntegralStride
      let tail ← reinterpret222CheckedStrides rest elementSize
      pure (quotient :: tail)) ∧
  (∀ contiguous make size strides elsize target source reshaped array,
      reinterpret208Strides contiguous make size strides elsize target source reshaped array = do
      if contiguous array then return make (JInt.lit .i64 1) (size array)
      let parentStrides := strides array
      if target = source then return parentStrides
      let byteStrides := parentStrides.map (· * elsize array)
      if reshaped && target < source then
        return JInt.lit .i64 1 :: (← reinterpret222CheckedStrides byteStrides target)
      if byteStrides.getD 0 (JInt.lit .i64 0) != source then throw .noncontiguous
      let tail ← reinterpret222CheckedStrides byteStrides.tail target
      if reshaped then return tail else return JInt.lit .i64 1 :: tail) ∧
  (∀ style parent target source,
      reinterpret263IndexStyleReshaped style parent target source = do
      if target < source then
        if style parent = .linear then
          let k ← JInt.div source target |>.mapError fun _ => .arithmetic
          return .staticCartesian k
        return .cartesian
      return style parent)

theorem reinterpretStrideCalculationCorrect : ReinterpretStrideCalculationCorrect := by
  simp [ReinterpretStrideCalculationCorrect, reinterpret222CheckedStrides,
    reinterpret208Strides, reinterpret263IndexStyleReshaped]

def reinterpret371Size (sizeParent : ReinterpretValue → List JInt64)
    (singletonTarget : Bool) (sourceSize targetSize : JInt64)
    (array : ReinterpretValue) : ReinterpretShapeJl (List JInt64) := do
  let parentSize := sizeParent array
  let first := parentSize.getD 0 (JInt.lit .i64 0)
  let size1 ← if singletonTarget then pure first else do
    JInt.div (first * sourceSize) targetSize |>.mapError fun _ => .arithmetic
  pure (size1 :: parentSize.tail)

def reinterpret376SizeReshaped (sizeParent : ReinterpretValue → List JInt64)
    (sourceSize targetSize : JInt64) (array : ReinterpretValue) :
    ReinterpretShapeJl (List JInt64) := do
  let parentSize := sizeParent array
  if targetSize < sourceSize then
    let ratio ← JInt.div sourceSize targetSize |>.mapError fun _ => .arithmetic
    return ratio :: parentSize
  if sourceSize < targetSize then return parentSize.tail
  return parentSize

def reinterpret384Axes (axesParent : ReinterpretValue → List AxisModel)
    (singletonTarget : Bool) (sourceSize targetSize : JInt64)
    (array : ReinterpretValue) : ReinterpretShapeJl (List AxisModel) := do
  let parentAxes := axesParent array
  let axis := parentAxes.getD 0 ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩
  let size1 ← if singletonTarget then pure axis.length else
    JInt.div (axis.length * sourceSize) targetSize |>.mapError fun _ => .arithmetic
  pure (⟨axis.first, size1⟩ :: parentAxes.tail)

def reinterpret390AxesReshaped (axesParent : ReinterpretValue → List AxisModel)
    (sourceSize targetSize : JInt64) (array : ReinterpretValue) :
    ReinterpretShapeJl (List AxisModel) := do
  let parentAxes := axesParent array
  if targetSize < sourceSize then
    let ratio ← JInt.div sourceSize targetSize |>.mapError fun _ => .arithmetic
    return ⟨JInt.lit .i64 1, ratio⟩ :: parentAxes
  if sourceSize < targetSize then return parentAxes.tail
  return parentAxes

def reinterpret400Elsize (parentElsize : JInt64)
    (targetSize sourceSize : JInt64) : JInt64 :=
  if targetSize = sourceSize then parentElsize else targetSize

def reinterpret410GetZero (scalarApplicable : TypeLayoutModel → TypeLayoutModel → Bool)
    (reinterpretScalar : TypeLayoutModel → Int → Int)
    (parentGetZero : ReinterpretValue → Int)
    (firstIndex : ReinterpretValue → Int)
    (getindex : ReinterpretValue → Int → Int)
    (source target : TypeLayoutModel) (array : ReinterpretValue) : Int :=
  if scalarApplicable target source then reinterpretScalar target (parentGetZero array)
  else getindex array (firstIndex array)

def reinterpret418CheckPtr (parentCheck : ReinterpretValue → Bool)
    (parent : ReinterpretValue → ReinterpretValue)
    (targetSize sourceSize : JInt64) (array : ReinterpretValue) : Bool :=
  if targetSize = sourceSize then false else parentCheck (parent array)

def ReinterpretShapeCorrect : Prop :=
  (∀ size singleton source target array, reinterpret371Size size singleton source target array = do
      let parentSize := size array
      let first := parentSize.getD 0 (JInt.lit .i64 0)
      let size1 ← if singleton then pure first else
        JInt.div (first * source) target |>.mapError fun _ => .arithmetic
      pure (size1 :: parentSize.tail)) ∧
  (∀ size source target array, reinterpret376SizeReshaped size source target array = do
      let parentSize := size array
      if target < source then
        let ratio ← JInt.div source target |>.mapError fun _ => .arithmetic
        return ratio :: parentSize
      if source < target then return parentSize.tail
      return parentSize) ∧
  (∀ axes singleton source target array, reinterpret384Axes axes singleton source target array = do
      let parentAxes := axes array
      let axis := parentAxes.getD 0 ⟨JInt.lit .i64 1, JInt.lit .i64 0⟩
      let size1 ← if singleton then pure axis.length else
        JInt.div (axis.length * source) target |>.mapError fun _ => .arithmetic
      pure (⟨axis.first, size1⟩ :: parentAxes.tail)) ∧
  (∀ axes source target array, reinterpret390AxesReshaped axes source target array = do
      let parentAxes := axes array
      if target < source then
        let ratio ← JInt.div source target |>.mapError fun _ => .arithmetic
        return ⟨JInt.lit .i64 1, ratio⟩ :: parentAxes
      if source < target then return parentAxes.tail
      return parentAxes) ∧
  (∀ parent target source, reinterpret400Elsize parent target source =
      if target = source then parent else target) ∧
  (∀ scalar reinterpret parentGet first get source target array,
      reinterpret410GetZero scalar reinterpret parentGet first get source target array =
      if scalar target source then reinterpret target (parentGet array)
      else get array (first array)) ∧
  (∀ check parent target source array, reinterpret418CheckPtr check parent target source array =
      if target = source then false else check (parent array))

theorem reinterpretShapeCorrect : ReinterpretShapeCorrect := by
  simp [ReinterpretShapeCorrect, reinterpret371Size, reinterpret376SizeReshaped,
    reinterpret384Axes, reinterpret390AxesReshaped, reinterpret400Elsize,
    reinterpret410GetZero, reinterpret418CheckPtr]

end JuliaLean.ArrayCov
