import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastIndexFaithful

open JuliaLean
open JuliaLean.Registry

inductive Error where
  | bounds
  | inexact
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure Axis where
  values : List Int
  first : Int
  deriving Repr, DecidableEq

def axisFirst (axis : Axis) : Int := axis.first

inductive Index where
  | scalar (value : Int)
  | cartesian (values : List Int)
  deriving Repr, DecidableEq

def toIndex : List Int → Index
  | [] => .cartesian []
  | [value] => .scalar value
  | values => .cartesian values

def remapAxes : List Axis → List Int → Result (List Int)
  | [], _ => .ok []
  | axis :: axes, [] => do pure (axisFirst axis :: (← remapAxes axes []))
  | axis :: axes, index :: indices => do
      let first := axisFirst axis
      let chosen := if axis.values.length = 1 then first else index
      pure (chosen :: (← remapAxes axes indices))

def m585 {A : Type} (axes : A → List Axis) (arg : A) (index : Index) : Result Index :=
  match index with
  | .cartesian values => toIndex <$> remapAxes (axes arg) values
  | .scalar value => toIndex <$> remapAxes (axes arg) [value]
def P585 : Prop := ∀ {A : Type} (axes : A → List Axis) arg values,
  m585 axes arg (.cartesian values) = (toIndex <$> remapAxes (axes arg) values)
theorem p585 : P585 := by simp [P585, m585]

def m586 {A : Type} (axes : A → List Axis) (arg : A) (index : Int) : Result Index :=
  toIndex <$> remapAxes (axes arg) [index]
def P586 : Prop := ∀ {A : Type} (axes : A → List Axis) arg index,
  m586 axes arg index = (toIndex <$> remapAxes (axes arg) [index])
theorem p586 : P586 := by simp [P586, m586]

def m587 (axis : Axis) (axes : List Axis) (index : Int) (indices : List Int) : Result (List Int) := do
  let first := axisFirst axis
  let chosen := if axis.values.length = 1 then first else index
  pure (chosen :: (← remapAxes axes indices))
def P587 : Prop := ∀ axis axes index indices,
  m587 axis axes index indices = do
    let first := axisFirst axis
    let chosen := if axis.values.length = 1 then first else index
    pure (chosen :: (← remapAxes axes indices))
theorem p587 : P587 := by simp [P587, m587]

def m588 {I : Type} (_indices : I) : List Int := []
def P588 : Prop := ∀ {I : Type} (indices : I), m588 indices = []
theorem p588 : P588 := by simp [P588, m588]

def m589 (axis : Axis) (axes : List Axis) : Result (List Int) := do
  pure (axisFirst axis :: (← remapAxes axes []))
def P589 : Prop := ∀ axis axes,
  m589 axis axes = do pure (axisFirst axis :: (← remapAxes axes []))
theorem p589 : P589 := by simp [P589, m589]

def m590 : List Int := []
def P590 : Prop := ∀ _ : Unit, m590 = []
theorem p590 : P590 := by simp [P590, m590]

def remapKeep : List Int → List Bool → List Int → List Int
  | [], _, _ => []
  | _, [], _ => []
  | _, _, [] => []
  | index :: indices, keep :: keeps, default :: defaults =>
      (if keep then index else default) :: remapKeep indices keeps defaults

def m593 (index : Index) (keep : List Bool) (defaults : List Int) : Index :=
  match index with
  | .cartesian values => toIndex (remapKeep values keep defaults)
  | .scalar value => toIndex (remapKeep [value] keep defaults)
def P593 : Prop := ∀ values keep defaults,
  m593 (.cartesian values) keep defaults = toIndex (remapKeep values keep defaults)
theorem p593 : P593 := by simp [P593, m593]

def m594 (value : Int) (keep : List Bool) (defaults : List Int) : Index :=
  m593 (.scalar value) keep defaults
def P594 : Prop := ∀ value keep defaults,
  m594 value keep defaults = m593 (.scalar value) keep defaults
theorem p594 : P594 := by simp [P594, m594]

def convertInt (value : Int) : Jl JInt64 := JInt.convert .i64 value

def m595 (value : Int) (keep : Bool) (firstDefault secondDefault : Int) : Jl Index := do
  let convertedValue ← convertInt value
  let convertedDefault ← convertInt firstDefault
  let chosen := if keep then convertedValue.val else convertedDefault.val
  pure (.cartesian [chosen, secondDefault])
def P595 : Prop := ∀ value keep firstDefault secondDefault,
  m595 value keep firstDefault secondDefault = do
    let convertedValue ← convertInt value
    let convertedDefault ← convertInt firstDefault
    let chosen := if keep then convertedValue.val else convertedDefault.val
    pure (.cartesian [chosen, secondDefault])
theorem p595 : P595 := by simp [P595, m595]

def m596 (value : Int) (keep : Bool) (default : Int) : Int := if keep then value else default
def P596 : Prop := ∀ value keep default, m596 value keep default = if keep then value else default
theorem p596 : P596 := by simp [P596, m596]

def m597 {D : Type} (_value : Int) (_keep : List Bool) (_defaults : D) : Index := .cartesian []
def P597 : Prop := ∀ {D : Type} value keep (defaults : D), m597 value keep defaults = .cartesian []
theorem p597 : P597 := by simp [P597, m597]

def m598 (index : Int) (indices : List Int) (keep : Bool) (keeps : List Bool)
    (default : Int) (defaults : List Int) : List Int :=
  (if keep then index else default) :: remapKeep indices keeps defaults
def P598 : Prop := ∀ index indices keep keeps default defaults,
  m598 index indices keep keeps default defaults =
    (if keep then index else default) :: remapKeep indices keeps defaults
theorem p598 : P598 := by simp [P598, m598]

def m600 {I D : Type} (_indices : I) (_defaults : D) : List Int := []
def P600 : Prop := ∀ {I D : Type} (indices : I) (defaults : D), m600 indices defaults = []
theorem p600 : P600 := by simp [P600, m600]

def m601 {K D : Type} (_keep : K) (_defaults : D) : List Int := []
def P601 : Prop := ∀ {K D : Type} (keep : K) (defaults : D), m601 keep defaults = []
theorem p601 : P601 := by simp [P601, m601]

def m602 {D : Type} (_defaults : D) : List Int := []
def P602 : Prop := ∀ {D : Type} (defaults : D), m602 defaults = []
theorem p602 : P602 := by simp [P602, m602]

def newIndexer : List Axis → Result (List Bool × List Int)
  | [] => .ok ([], [])
  | axis :: axes => do
      let rest ← newIndexer axes
      pure ((axis.values.length ≠ 1) :: rest.1, axisFirst axis :: rest.2)

def m606 {A : Type} (axes : A → List Axis) (array : A) : Result (List Bool × List Int) :=
  newIndexer (axes array)
def P606 : Prop := ∀ {A : Type} (axes : A → List Axis) array,
  m606 axes array = newIndexer (axes array)
theorem p606 : P606 := by simp [P606, m606]

def m607 (axes : List Axis) : Result (List Bool × List Int) := newIndexer axes
def P607 : Prop := ∀ axes, m607 axes = newIndexer axes
theorem p607 : P607 := by simp [P607, m607]

def m608 : List Bool × List Int := ([], [])
def P608 : Prop := ∀ _ : Unit, m608 = ([], [])
theorem p608 : P608 := by simp [P608, m608]

def m609 (axis : Axis) (axes : List Axis) : Result (List Bool × List Int) := do
  let rest ← newIndexer axes
  pure ((axis.values.length ≠ 1) :: rest.1, axisFirst axis :: rest.2)
def P609 : Prop := ∀ axis axes,
  m609 axis axes = do
    let rest ← newIndexer axes
    pure ((axis.values.length ≠ 1) :: rest.1, axisFirst axis :: rest.2)
theorem p609 : P609 := by simp [P609, m609]

def m615 {BC Raw Flat R : Type} (flatten : Raw → Flat) (toIndexFn : Flat → Index)
    (indexStyle : BC → Bool) (getindex : Bool → BC → Index → R)
    (bc : BC) (indices : Raw) : R :=
  let index := toIndexFn (flatten indices)
  getindex (indexStyle bc) bc index
def P615 : Prop := ∀ {BC Raw Flat R : Type} (flatten : Raw → Flat) (toIndexFn : Flat → Index)
    (indexStyle : BC → Bool) (getindex : Bool → BC → Index → R) bc indices,
  m615 flatten toIndexFn indexStyle getindex bc indices =
    getindex (indexStyle bc) bc (toIndexFn (flatten indices))
theorem p615 : P615 := by simp [P615, m615]

def m619 {BC I V : Type} (checkbounds : BC → I → Result Unit)
    (uncheckedGet : BC → I → Result V) (_style : Bool) (bc : BC) (index : I) : Result V := do
  checkbounds bc index
  uncheckedGet bc index
def P619 : Prop := ∀ {BC I V : Type} (checkbounds : BC → I → Result Unit)
    (uncheckedGet : BC → I → Result V) style bc index,
  m619 checkbounds uncheckedGet style bc index = do
    checkbounds bc index
    uncheckedGet bc index
theorem p619 : P619 := by simp [P619, m619]

def m623 {BC CI V : Type} (axes : BC → List Axis) (cartesianIndices : List Axis → Int → Result CI)
    (getindex : Bool → BC → CI → Result V) (style : Bool) (bc : BC) (index : Int) : Result V := do
  let converted ← cartesianIndices (axes bc) index
  getindex style bc converted
def P623 : Prop := ∀ {BC CI V : Type} (axes : BC → List Axis)
    (cartesianIndices : List Axis → Int → Result CI)
    (getindex : Bool → BC → CI → Result V) style bc index,
  m623 axes cartesianIndices getindex style bc index = do
    let converted ← cartesianIndices (axes bc) index
    getindex style bc converted
theorem p623 : P623 := by simp [P623, m623]

def m627 {BC CI V : Type} (axes : BC → List Axis) (linearIndices : List Axis → CI → Result Int)
    (getindex : Bool → BC → Int → Result V) (style : Bool) (bc : BC) (index : CI) : Result V := do
  let converted ← linearIndices (axes bc) index
  getindex style bc converted
def P627 : Prop := ∀ {BC CI V : Type} (axes : BC → List Axis)
    (linearIndices : List Axis → CI → Result Int)
    (getindex : Bool → BC → Int → Result V) style bc index,
  m627 axes linearIndices getindex style bc index = do
    let converted ← linearIndices (axes bc) index
    getindex style bc converted
theorem p627 : P627 := by simp [P627, m627]

def m631 : Index := .cartesian []
def P631 : Prop := ∀ _ : Unit, m631 = .cartesian []
theorem p631 : P631 := by simp [P631, m631]

def m632 {α : Type} (value : α) : α := value
def P632 : Prop := ∀ {α : Type} (value : α), m632 value = value
theorem p632 : P632 := by simp [P632, m632]

def m633 (values : List Int) : Index := .cartesian values
def P633 : Prop := ∀ values, m633 values = .cartesian values
theorem p633 : P633 := by simp [P633, m633]

def m635 {BC CI : Type} (axes : BC → List Axis)
    (checkboundsIndices : List Axis → CI → Bool) (bc : BC) (index : CI) : Result Unit :=
  if checkboundsIndices (axes bc) index then .ok () else .error .bounds
def P635 : Prop := ∀ {BC CI : Type} (axes : BC → List Axis)
    (checkboundsIndices : List Axis → CI → Bool) bc index,
  m635 axes checkboundsIndices bc index =
    if checkboundsIndices (axes bc) index then .ok () else .error .bounds
theorem p635 : P635 := by simp [P635, m635]

def m640 {BC : Type} (eachindex : BC → List Int) (bc : BC) (index : Int) : Result Unit :=
  if (eachindex bc).contains index then .ok () else .error .bounds
def P640 : Prop := ∀ {BC : Type} (eachindex : BC → List Int) bc index,
  m640 eachindex bc index = if (eachindex bc).contains index then .ok () else .error .bounds
theorem p640 : P640 := by simp [P640, m640]

def m651 {A I V : Type} (getZero : A → V) (array : A) (_index : I) : V := getZero array
def P651 : Prop := ∀ {A I V : Type} (getZero : A → V) array (index : I),
  m651 getZero array index = getZero array
theorem p651 : P651 := by simp [P651, m651]

def m652 {T I : Type} (typeValue : T) (_index : I) : T := typeValue
def P652 : Prop := ∀ {T I : Type} (typeValue : T) (index : I), m652 typeValue index = typeValue
theorem p652 : P652 := by simp [P652, m652]

def m654 {α I : Type} (value : α) (_index : I) : α := value
def P654 : Prop := ∀ {α I : Type} (value : α) (index : I), m654 value index = value
theorem p654 : P654 := by simp [P654, m654]

def m655 {α : Type} (tuple : List α) (index : List Int) : Result α :=
  match index.head? with
  | none => .error .bounds
  | some i =>
      if i < 1 then .error .bounds
      else match tuple[(i - 1).toNat]? with
        | none => .error .bounds
        | some value => .ok value
def P655 : Prop := ∀ {α : Type} (tuple : List α) index,
  m655 tuple index =
    match index.head? with
    | none => .error .bounds
    | some i =>
        if i < 1 then .error .bounds
        else match tuple[(i - 1).toNat]? with
          | none => .error .bounds
          | some value => .ok value
theorem p655 : P655 := by simp [P655, m655]

def m657 {A I V : Type} (newindex : A → I → I) (getindex : A → I → V)
    (array : A) (index : I) : V := getindex array (newindex array index)
def P657 : Prop := ∀ {A I V : Type} (newindex : A → I → I) (getindex : A → I → V) array index,
  m657 newindex getindex array index = getindex array (newindex array index)
theorem p657 : P657 := by simp [P657, m657]

structure Extruded (A : Type) where
  x : A
  keeps : List Bool
  defaults : List Int
  deriving Repr, DecidableEq

def m669 {A : Type} (axes : A → List Axis) (value : Extruded A) : List Axis := axes value.x
def P669 : Prop := ∀ {A : Type} (axes : A → List Axis) value, m669 axes value = axes value.x
theorem p669 : P669 := by simp [P669, m669]

def m670 {A V : Type} (getindex : A → Index → V) (value : Extruded A) (index : Index) : V :=
  getindex value.x (m593 index value.keeps value.defaults)
def P670 : Prop := ∀ {A V : Type} (getindex : A → Index → V) value index,
  m670 getindex value index = getindex value.x (m593 index value.keeps value.defaults)
theorem p670 : P670 := by simp [P670, m670]

def m671 {A : Type} (newindexer : A → List Bool × List Int) (array : A) : Extruded A :=
  let pair := newindexer array
  ⟨array, pair.1, pair.2⟩
def P671 : Prop := ∀ {A : Type} (newindexer : A → List Bool × List Int) array,
  m671 newindexer array = let pair := newindexer array; ⟨array, pair.1, pair.2⟩
theorem p671 : P671 := by simp [P671, m671]

def m672 {A : Type} (value : A) : A := value
def P672 : Prop := ∀ {A : Type} (value : A), m672 value = value
theorem p672 : P672 := by simp [P672, m672]

structure EvalBroadcasted (A V : Type) where
  f : List V → V
  args : List A

def gather {A I V : Type} (getindex : A → I → V) : List A → I → List V
  | [], _ => []
  | head :: tail, index => getindex head index :: gather getindex tail index

def m675 {A I V : Type} (getindex : A → I → V) (bc : EvalBroadcasted A V) (index : I) : V :=
  bc.f (gather getindex bc.args index)
def P675 : Prop := ∀ {A I V : Type} (getindex : A → I → V) bc index,
  m675 getindex bc index = bc.f (gather getindex bc.args index)
theorem p675 : P675 := by simp [P675, m675]

def m685 {A I T V : Type} (getindex : A → I → V) (f : T → List V → V)
    (typeValue : T) (tail : List A) (index : I) : V := f typeValue (gather getindex tail index)
def P685 : Prop := ∀ {A I T V : Type} (getindex : A → I → V)
    (f : T → List V → V) typeValue tail index,
  m685 getindex f typeValue tail index = f typeValue (gather getindex tail index)
theorem p685 : P685 := by simp [P685, m685]

def m689 {A I T V : Type} (getindex : A → I → V) (f : V → T → List V → V)
    (first : A) (typeValue : T) (tail : List A) (index : I) : V :=
  let firstValue := getindex first index
  f firstValue typeValue (gather getindex tail index)
def P689 : Prop := ∀ {A I T V : Type} (getindex : A → I → V)
    (f : V → T → List V → V) first typeValue tail index,
  m689 getindex f first typeValue tail index = f (getindex first index) typeValue (gather getindex tail index)
theorem p689 : P689 := by simp [P689, m689]

def m694 {A I T S V : Type} (getindex : A → I → V) (f : T → S → List V → V)
    (firstType : T) (secondType : S) (tail : List A) (index : I) : V :=
  f firstType secondType (gather getindex tail index)
def P694 : Prop := ∀ {A I T S V : Type} (getindex : A → I → V)
    (f : T → S → List V → V) firstType secondType tail index,
  m694 getindex f firstType secondType tail index =
    f firstType secondType (gather getindex tail index)
theorem p694 : P694 := by simp [P694, m694]

def m700 {A I V : Type} (getindex : A → I → V) (head : A) (tail : List A) (index : I) : List V :=
  getindex head index :: gather getindex tail index
def P700 : Prop := ∀ {A I V : Type} (getindex : A → I → V) head tail index,
  m700 getindex head tail index = getindex head index :: gather getindex tail index
theorem p700 : P700 := by simp [P700, m700]

def m701 {A I V : Type} (getindex : A → I → V) (head : A) (index : I) : List V := [getindex head index]
def P701 : Prop := ∀ {A I V : Type} (getindex : A → I → V) head index,
  m701 getindex head index = [getindex head index]
theorem p701 : P701 := by simp [P701, m701]

def m702 {I V : Type} (_index : I) : List V := []
def P702 : Prop := ∀ {I V : Type} (index : I), (m702 index : List V) = []
theorem p702 : P702 := by simp [P702, m702]

def m704 {A V : Type} (f : List A → V) (args : List A) : V := f args
def P704 : Prop := ∀ {A V : Type} (f : List A → V) args, m704 f args = f args
theorem p704 : P704 := by simp [P704, m704]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; newindex docstring and source equation"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.BroadcastIndexFaithful
