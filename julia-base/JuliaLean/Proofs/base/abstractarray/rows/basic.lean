import JuliaLean.base.abstractarray
import JuliaLean.Registry.Types


namespace JuliaLean.AbstractArrayCov.Rows.Basic

open JuliaLean
open JuliaLean.AbstractArrays
open JuliaLean.Registry


def Property16 : Prop := ∀ (α : Type) (a : α), method16 a = a
theorem property16 : Property16 := by
  unfold Property16
  intros
  rfl

def Property17 : Prop := ∀ (α β : Type) (construct : α → β) a,
  method17 construct a = construct a
theorem property17 : Property17 := by
  unfold Property17
  intros
  rfl

def Property18 : Prop := ∀ (α β : Type) (construct : α → β) a,
  method18 construct a = construct a
theorem property18 : Property18 := by
  unfold Property18
  intros
  rfl


def Property42 : Prop := ∀ (t : IntTy) (size : Unit → List I64) (dim : JInt t),
  method42 size dim = do
    let d ← JInt.convert (IntTy.i64.name) .i64 dim.val
    let s := size ()
    if d.val ≤ s.length then tupleGet s d else .ok (i64 1)
theorem property42 : Property42 := by
  unfold Property42
  intros
  rfl


def Property79 : Prop := ∀ (t : IntTy) rank (axes : Unit → List Axis) (d : JInt t),
  method79 rank axes d =
    if d.val ≤ rank then do
      let i ← JInt.convert (IntTy.i64.name) .i64 d.val
      tupleGet (axes ()) i
    else .ok (Axis.oneTo 1)
theorem property79 : Property79 := by
  unfold Property79
  intros
  rfl


def Property100 : Prop := ∀ (α : Type) (size : α → List I64)
    (uncheckedOneTo : I64 → Axis) a,
  method100 size uncheckedOneTo a = (size a).map uncheckedOneTo
theorem property100 : Property100 := by
  unfold Property100
  intros
  rfl

def Property114 : Prop := ∀ _ : Unit, method114 = false
theorem property114 : Property114 := by unfold Property114; intros; rfl


def Property115 : Prop := ∀ (α β : Type) (axes : β → List α) (first : α → Int) a,
  method115 axes first a = offsetAxesLoop first (axes a)
theorem property115 : Property115 := by
  unfold Property115
  intros
  rfl


def Property116 : Prop := ∀ (α : Type) (firstindex : α → Int) a,
  method116 firstindex a = do
    let i ← JInt.convert (IntTy.i64.name) .i64 (firstindex a)
    return i.val != 1
theorem property116 : Property116 := by
  unfold Property116
  intros
  rfl

def Property117 : Prop := ∀ _colon : Unit, method117 = false
theorem property117 : Property117 := by unfold Property117; intros; rfl

def Property118 : Prop := ∀ (α : Type) (_array : α), method118 = false
theorem property118 : Property118 := by unfold Property118; intros; rfl


def Property122 : Prop := ∀ (α : Type) (hasOffset : α → Jl Bool) a rest,
  method122 hasOffset a rest = do
    if ← hasOffset a then return true
    for x in rest do
      if ← hasOffset x then return true
    return false
theorem property122 : Property122 := by
  unfold Property122
  intros
  rfl


def Property135 : Prop := ∀ (α : Type) (hasOffset : List α → Jl Bool) arrays,
  method135 hasOffset arrays = do
    if ← hasOffset arrays then
      throw (.argumentError "offset arrays are not supported but got an array with index other than 1")
    return ()
theorem property135 : Property135 := by
  unfold Property135
  intros
  rfl

def Property140 : Prop := ∀ _array : Unit, method140 = Axis.oneTo 1
theorem property140 : Property140 := by unfold Property140; intros; rfl

def Property141 : Prop := ∀ (α : Type) (axes : α → List Axis) a,
  method141 axes a = tupleGet (axes a) (i64 1)
theorem property141 : Property141 := by
  unfold Property141
  intros
  rfl

def Property142 : Prop := ∀ (α : Type) (length : α → Nat) (oneto : Nat → Axis) iter,
  method142 length oneto iter = oneto (length iter)
theorem property142 : Property142 := by
  unfold Property142
  intros
  rfl

def Property169 : Prop := ∀ (α β : Type) (axes : α → List Axis)
    (cartesianIndices : List Axis → β) a,
  method169 axes cartesianIndices a = cartesianIndices (axes a)
theorem property169 : Property169 := by
  unfold Property169
  intros
  rfl

def Property170 : Prop := ∀ (α β : Type) (linearIndices : α → β) a,
  method170 linearIndices a = linearIndices a
theorem property170 : Property170 := by
  unfold Property170
  intros
  rfl

def Property192 : Prop := ∀ (α : Type) (typeof : α → TypeTag)
    (keytype : TypeTag → TypeTag) a,
  method192 typeof keytype a = keytype (typeof a)
theorem property192 : Property192 := by
  unfold Property192
  intros
  rfl

def Property193 : Prop := ∀ eltype : TypeTag → Jl TypeTag,
  method193 eltype = eltype .bottom
theorem property193 : Property193 := by
  unfold Property193
  intros
  rfl

def Property195 : Prop := ∀ ndims arrayType,
  method195 ndims arrayType = .cartesian (ndims arrayType)
theorem property195 : Property195 := by
  unfold Property195
  intros
  rfl

def Property196 : Prop := ∀ _vectorType : Unit, method196 = .int
theorem property196 : Property196 := by unfold Property196; intros; rfl

def Property198 : Prop := ∀ (α : Type) (typeof : α → TypeTag)
    (valtype : TypeTag → TypeTag) a,
  method198 typeof valtype a = valtype (typeof a)
theorem property198 : Property198 := by
  unfold Property198
  intros
  rfl

def Property199 : Prop := ∀ eltype : TypeTag → Jl TypeTag,
  method199 eltype = eltype .bottom
theorem property199 : Property199 := by
  unfold Property199
  intros
  rfl

def Property217 : Prop := ∀ eltype arrayType,
  method217 eltype arrayType = eltype arrayType
theorem property217 : Property217 := by
  unfold Property217
  intros
  rfl

def Property219 : Prop := ∀ raw, method219 raw = do
  let i ← JInt.convert (IntTy.i64.name) .i64 raw
  return i - i64 1
theorem property219 : Property219 := by
  unfold Property219
  intros
  rfl

def Property220 : Prop := ∀ raw, method220 raw = do
  let i ← JInt.convert (IntTy.i64.name) .i64 raw
  return i + i64 1
theorem property220 : Property220 := by
  unfold Property220
  intros
  rfl

def Property243 : Prop := ∀ _type : TypeTag, method243 = .any
theorem property243 : Property243 := by unfold Property243; intros; rfl

def Property244 : Prop := ∀ _bottom : Unit,
  method244 = .error (.argumentError "Union{} does not have elements")
theorem property244 : Property244 := by unfold Property244; intros; rfl

def Property245 : Prop := ∀ (α : Type) (typeof : α → TypeTag)
    (eltype : TypeTag → TypeTag) x,
  method245 typeof eltype x = eltype (typeof x)
theorem property245 : Property245 := by
  unfold Property245
  intros
  rfl

def Property246 : Prop := ∀ defined element,
  method246 defined element = if defined then element else .any
theorem property246 : Property246 := by
  unfold Property246
  intros
  rfl

def Property261 : Prop := ∀ (α : Type) (typeof : α → TypeTag) (elsize : TypeTag → Nat) a,
  method261 typeof elsize a = elsize (typeof a)
theorem property261 : Property261 := by
  unfold Property261
  intros
  rfl

def Property278 : Prop := ∀ rank, method278 rank = rank
theorem property278 : Property278 := by
  unfold Property278
  intros
  rfl

def Property279 : Prop := ∀ rank, method279 rank = rank
theorem property279 : Property279 := by
  unfold Property279
  intros
  rfl

def Property280 : Prop := ∀ _bottom : Unit,
  method280 = .error (.argumentError "Union{} does not have elements")
theorem property280 : Property280 := by unfold Property280; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/abstractarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.Basic
