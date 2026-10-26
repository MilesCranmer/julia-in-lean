import JuliaLean.AbstractArrays.Model
import JuliaLean.Registry.Types

/-!
Method-specific models for `base/abstractarray.jl:16-280` at `bbfa0ce4150`.
Each definition follows one Julia method body. Function arguments represent
the Julia methods called by that body; the model controls their call order,
branches, conversions, errors, and returned value.
-/

namespace JuliaLean.AbstractArrayCov.Rows.Basic

open JuliaLean
open JuliaLean.AbstractArrays
open JuliaLean.Registry

abbrev I64 := JInt .i64

def i64 (x : Int) : I64 := JInt.lit .i64 x

inductive TypeTag where
  | any | bottom | int | cartesian (rank : Nat) | element (id : Nat) | other (id : Nat)
  deriving Repr, DecidableEq

/-- One-based tuple indexing, including the BoundsError from `s[d]`. -/
def tupleGet (xs : List α) (i : I64) : Jl α :=
  if h : 1 ≤ i.val ∧ i.val ≤ xs.length then
    .ok (xs[(i.val - 1).toNat]'(by omega))
  else .error .boundsError

/-- `convert(::Type{T}, a::T)`, line 16. -/
def method16 (a : α) : α := a
def Property16 : Prop := ∀ (α : Type) (a : α), method16 a = a
theorem property16 : Property16 := by
  unfold Property16
  intros
  rfl

/-- `convert(::Type{AbstractArray{T}}, a::AbstractArray)`, line 17. -/
def method17 (construct : α → β) (a : α) : β := construct a
def Property17 : Prop := ∀ (α β : Type) (construct : α → β) a,
  method17 construct a = construct a
theorem property17 : Property17 := by
  unfold Property17
  intros
  rfl

/-- Rank-specialized `convert`, line 18. -/
def method18 (construct : α → β) (a : α) : β := construct a
def Property18 : Prop := ∀ (α β : Type) (construct : α → β) a,
  method18 construct a = construct a
theorem property18 : Property18 := by
  unfold Property18
  intros
  rfl

/-- `size(t, dim)`, lines 42-46: convert `dim`, call `size(t)`, then index or return 1. -/
def method42 {t : IntTy} (size : Unit → List I64) (dim : JInt t) : Jl I64 := do
  let d ← JInt.convert .i64 dim.val
  let s := size ()
  if d.val ≤ s.length then tupleGet s d else .ok (i64 1)

def Property42 : Prop := ∀ (t : IntTy) (size : Unit → List I64) (dim : JInt t),
  method42 size dim = do
    let d ← JInt.convert .i64 dim.val
    let s := size ()
    if d.val ≤ s.length then tupleGet s d else .ok (i64 1)
theorem property42 : Property42 := by
  unfold Property42
  intros
  rfl

/-- `axes(A, d)`, lines 79-82: compare before indexing, with `OneTo(1)` past rank. -/
def method79 {t : IntTy} (rank : Nat) (axes : Unit → List Axis) (d : JInt t) : Jl Axis :=
  if d.val ≤ rank then do
    let i ← JInt.convert .i64 d.val
    tupleGet (axes ()) i
  else .ok (Axis.oneTo 1)

def Property79 : Prop := ∀ (t : IntTy) rank (axes : Unit → List Axis) (d : JInt t),
  method79 rank axes d =
    if d.val ≤ rank then do
      let i ← JInt.convert .i64 d.val
      tupleGet (axes ()) i
    else .ok (Axis.oneTo 1)
theorem property79 : Property79 := by
  unfold Property79
  intros
  rfl

/-- `axes(A)`, lines 100-103. -/
def method100 (size : α → List I64) (uncheckedOneTo : I64 → Axis) (a : α) : List Axis :=
  (size a).map uncheckedOneTo

def Property100 : Prop := ∀ (α : Type) (size : α → List I64)
    (uncheckedOneTo : I64 → Axis) a,
  method100 size uncheckedOneTo a = (size a).map uncheckedOneTo
theorem property100 : Property100 := by
  unfold Property100
  intros
  rfl

/-- `has_offset_axes()`, line 114. -/
def method114 : Bool := false
def Property114 : Prop := ∀ _ : Unit, method114 = false
theorem property114 : Property114 := by unfold Property114; intros; rfl

/-- `_any_tuple(x -> Int(first(x)) != 1, false, axes(A)...)`, line 115. -/
def offsetAxesLoop (first : α → Int) : List α → Jl Bool
  | [] => .ok false
  | axis :: rest => do
      let i ← JInt.convert .i64 (first axis)
      if i.val != 1 then .ok true else offsetAxesLoop first rest

def method115 (axes : β → List α) (first : α → Int) (a : β) : Jl Bool :=
  offsetAxesLoop first (axes a)

def Property115 : Prop := ∀ (α β : Type) (axes : β → List α) (first : α → Int) a,
  method115 axes first a = offsetAxesLoop first (axes a)
theorem property115 : Property115 := by
  unfold Property115
  intros
  rfl

/-- Vector fast path of `has_offset_axes`, line 116. -/
def method116 (firstindex : α → Int) (a : α) : Jl Bool := do
  let i ← JInt.convert .i64 (firstindex a)
  return i.val != 1

def Property116 : Prop := ∀ (α : Type) (firstindex : α → Int) a,
  method116 firstindex a = do
    let i ← JInt.convert .i64 (firstindex a)
    return i.val != 1
theorem property116 : Property116 := by
  unfold Property116
  intros
  rfl

/-- `has_offset_axes(::Colon)`, line 117. -/
def method117 : Bool := false
def Property117 : Prop := ∀ _colon : Unit, method117 = false
theorem property117 : Property117 := by unfold Property117; intros; rfl

/-- `has_offset_axes(::Array)`, line 118. -/
def method118 : Bool := false
def Property118 : Prop := ∀ (α : Type) (_array : α), method118 = false
theorem property118 : Property118 := by unfold Property118; intros; rfl

/-- Vararg `has_offset_axes`, line 122, with source short-circuit order. -/
def method122 (hasOffset : α → Jl Bool) (a : α) (rest : List α) : Jl Bool := do
  if ← hasOffset a then return true
  for x in rest do
    if ← hasOffset x then return true
  return false

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

/-- `require_one_based_indexing`, line 135. -/
def method135 (hasOffset : List α → Jl Bool) (arrays : List α) : Jl Unit := do
  if ← hasOffset arrays then
    throw (.argumentError "offset arrays are not supported but got an array with index other than 1")
  return ()

def Property135 : Prop := ∀ (α : Type) (hasOffset : List α → Jl Bool) arrays,
  method135 hasOffset arrays = do
    if ← hasOffset arrays then
      throw (.argumentError "offset arrays are not supported but got an array with index other than 1")
    return ()
theorem property135 : Property135 := by
  unfold Property135
  intros
  rfl

/-- Zero-dimensional `axes1`, line 140. -/
def method140 : Axis := Axis.oneTo 1
def Property140 : Prop := ∀ _array : Unit, method140 = Axis.oneTo 1
theorem property140 : Property140 := by unfold Property140; intros; rfl

/-- Array `axes1`, line 141. -/
def method141 (axes : α → List Axis) (a : α) : Jl Axis := tupleGet (axes a) (i64 1)
def Property141 : Prop := ∀ (α : Type) (axes : α → List Axis) a,
  method141 axes a = tupleGet (axes a) (i64 1)
theorem property141 : Property141 := by
  unfold Property141
  intros
  rfl

/-- Generic iterable `axes1`, line 142. -/
def method142 (length : α → Nat) (oneto : Nat → Axis) (iter : α) : Axis :=
  oneto (length iter)
def Property142 : Prop := ∀ (α : Type) (length : α → Nat) (oneto : Nat → Axis) iter,
  method142 length oneto iter = oneto (length iter)
theorem property142 : Property142 := by
  unfold Property142
  intros
  rfl

/-- `keys(a::AbstractArray)`, line 169. -/
def method169 (axes : α → List Axis) (cartesianIndices : List Axis → β) (a : α) : β :=
  cartesianIndices (axes a)
def Property169 : Prop := ∀ (α β : Type) (axes : α → List Axis)
    (cartesianIndices : List Axis → β) a,
  method169 axes cartesianIndices a = cartesianIndices (axes a)
theorem property169 : Property169 := by
  unfold Property169
  intros
  rfl

/-- `keys(a::AbstractVector)`, line 170. -/
def method170 (linearIndices : α → β) (a : α) : β := linearIndices a
def Property170 : Prop := ∀ (α β : Type) (linearIndices : α → β) a,
  method170 linearIndices a = linearIndices a
theorem property170 : Property170 := by
  unfold Property170
  intros
  rfl

/-- `keytype(a) = keytype(typeof(a))`, line 192. -/
def method192 (typeof : α → TypeTag) (keytype : TypeTag → TypeTag) (a : α) : TypeTag :=
  keytype (typeof a)
def Property192 : Prop := ∀ (α : Type) (typeof : α → TypeTag)
    (keytype : TypeTag → TypeTag) a,
  method192 typeof keytype a = keytype (typeof a)
theorem property192 : Property192 := by
  unfold Property192
  intros
  rfl

/-- Bottom `keytype` delegates to Bottom `eltype`, line 193. -/
def method193 (eltype : TypeTag → Jl TypeTag) : Jl TypeTag := eltype .bottom
def Property193 : Prop := ∀ eltype : TypeTag → Jl TypeTag,
  method193 eltype = eltype .bottom
theorem property193 : Property193 := by
  unfold Property193
  intros
  rfl

/-- Generic AbstractArray key type, line 195. -/
def method195 (ndims : TypeTag → Nat) (arrayType : TypeTag) : TypeTag :=
  .cartesian (ndims arrayType)
def Property195 : Prop := ∀ ndims arrayType,
  method195 ndims arrayType = .cartesian (ndims arrayType)
theorem property195 : Property195 := by
  unfold Property195
  intros
  rfl

/-- AbstractVector key type, line 196. -/
def method196 : TypeTag := .int
def Property196 : Prop := ∀ _vectorType : Unit, method196 = .int
theorem property196 : Property196 := by unfold Property196; intros; rfl

/-- `valtype(a) = valtype(typeof(a))`, line 198. -/
def method198 (typeof : α → TypeTag) (valtype : TypeTag → TypeTag) (a : α) : TypeTag :=
  valtype (typeof a)
def Property198 : Prop := ∀ (α : Type) (typeof : α → TypeTag)
    (valtype : TypeTag → TypeTag) a,
  method198 typeof valtype a = valtype (typeof a)
theorem property198 : Property198 := by
  unfold Property198
  intros
  rfl

/-- Bottom `valtype` delegates to Bottom `eltype`, line 199. -/
def method199 (eltype : TypeTag → Jl TypeTag) : Jl TypeTag := eltype .bottom
def Property199 : Prop := ∀ eltype : TypeTag → Jl TypeTag,
  method199 eltype = eltype .bottom
theorem property199 : Property199 := by
  unfold Property199
  intros
  rfl

/-- AbstractArray `valtype` delegates to `eltype`, line 217. -/
def method217 (eltype : TypeTag → TypeTag) (arrayType : TypeTag) : TypeTag :=
  eltype arrayType
def Property217 : Prop := ∀ eltype arrayType,
  method217 eltype arrayType = eltype arrayType
theorem property217 : Property217 := by
  unfold Property217
  intros
  rfl

/-- `prevind`, line 219. -/
def method219 (raw : Int) : Jl I64 := do
  let i ← JInt.convert .i64 raw
  return i - i64 1
def Property219 : Prop := ∀ raw, method219 raw = do
  let i ← JInt.convert .i64 raw
  return i - i64 1
theorem property219 : Property219 := by
  unfold Property219
  intros
  rfl

/-- `nextind`, line 220. -/
def method220 (raw : Int) : Jl I64 := do
  let i ← JInt.convert .i64 raw
  return i + i64 1
def Property220 : Prop := ∀ raw, method220 raw = do
  let i ← JInt.convert .i64 raw
  return i + i64 1
theorem property220 : Property220 := by
  unfold Property220
  intros
  rfl

/-- Default `eltype(::Type)`, line 243. -/
def method243 : TypeTag := .any
def Property243 : Prop := ∀ _type : TypeTag, method243 = .any
theorem property243 : Property243 := by unfold Property243; intros; rfl

/-- Bottom `eltype`, line 244. -/
def method244 : Jl TypeTag := .error (.argumentError "Union{} does not have elements")
def Property244 : Prop := ∀ _bottom : Unit,
  method244 = .error (.argumentError "Union{} does not have elements")
theorem property244 : Property244 := by unfold Property244; intros; rfl

/-- Value `eltype` delegates through `typeof`, line 245. -/
def method245 (typeof : α → TypeTag) (eltype : TypeTag → TypeTag) (x : α) : TypeTag :=
  eltype (typeof x)
def Property245 : Prop := ∀ (α : Type) (typeof : α → TypeTag)
    (eltype : TypeTag → TypeTag) x,
  method245 typeof eltype x = eltype (typeof x)
theorem property245 : Property245 := by
  unfold Property245
  intros
  rfl

/-- AbstractArray element type branch, line 246. -/
def method246 (defined : Bool) (element : TypeTag) : TypeTag := if defined then element else .any
def Property246 : Prop := ∀ defined element,
  method246 defined element = if defined then element else .any
theorem property246 : Property246 := by
  unfold Property246
  intros
  rfl

/-- `elsize(A) = elsize(typeof(A))`, line 261. -/
def method261 (typeof : α → TypeTag) (elsize : TypeTag → Nat) (a : α) : Nat :=
  elsize (typeof a)
def Property261 : Prop := ∀ (α : Type) (typeof : α → TypeTag) (elsize : TypeTag → Nat) a,
  method261 typeof elsize a = elsize (typeof a)
theorem property261 : Property261 := by
  unfold Property261
  intros
  rfl

/-- Value `ndims`, line 278. -/
def method278 (rank : I64) : I64 := rank
def Property278 : Prop := ∀ rank, method278 rank = rank
theorem property278 : Property278 := by
  unfold Property278
  intros
  rfl

/-- Type `ndims`, line 279. -/
def method279 (rank : I64) : I64 := rank
def Property279 : Prop := ∀ rank, method279 rank = rank
theorem property279 : Property279 := by
  unfold Property279
  intros
  rfl

/-- Bottom `ndims`, line 280. -/
def method280 : Jl I64 := .error (.argumentError "Union{} does not have elements")
def Property280 : Prop := ∀ _bottom : Unit,
  method280 = .error (.argumentError "Union{} does not have elements")
theorem property280 : Property280 := by unfold Property280; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/abstractarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry "abstractarraycov-line16-convert" "convert(::Type{T}, a::T) where T<:AbstractArray" "Conversion to the value's existing array type returns that value for every array." "base/abstractarray.jl:16" ``Property16 ``property16,
  entry "abstractarraycov-line17-convert" "convert(::Type{AbstractArray{T}}, a::AbstractArray)" "The element-type conversion calls the AbstractArray constructor once and returns its typed result." "base/abstractarray.jl:17" ``Property17 ``property17,
  entry "abstractarraycov-line18-convert" "convert(::Type{AbstractArray{T,N}}, a::AbstractArray{<:Any,N})" "The rank-preserving conversion calls the rank-specific constructor once and returns its typed result." "base/abstractarray.jl:18" ``Property18 ``property18,
  entry "abstractarraycov-line42-size" "size(::AbstractArray, dim)" "The method converts dim to Int before calling size and then returns the selected or trailing singleton dimension." "base/abstractarray.jl:42-46" ``Property42 ``property42,
  entry "abstractarraycov-line79-axes" "axes(::AbstractArray{T,N}, d)" "The method compares d with rank before indexing axes and returns OneTo(1) past rank." "base/abstractarray.jl:79-82" ``Property79 ``property79,
  entry "abstractarraycov-line100-axes" "axes(A)" "The method maps unchecked_oneto over size(A) in order." "base/abstractarray.jl:100-103" ``Property100 ``property100,
  entry "abstractarraycov-line114-has-offset-axes" "has_offset_axes()" "The zero-argument method is false." "base/abstractarray.jl:114" ``Property114 ``property114,
  entry "abstractarraycov-line115-has-offset-axes" "has_offset_axes(A)" "The generic method scans axes in order, converting each first index to Int and short-circuiting at the first offset." "base/abstractarray.jl:115" ``Property115 ``property115,
  entry "abstractarraycov-line116-has-offset-axes" "has_offset_axes(::AbstractVector)" "The vector fast path converts firstindex to Int before comparing it with one." "base/abstractarray.jl:116" ``Property116 ``property116,
  entry "abstractarraycov-line117-has-offset-axes" "has_offset_axes(::Colon)" "Colon never has offset axes." "base/abstractarray.jl:117" ``Property117 ``property117,
  entry "abstractarraycov-line118-has-offset-axes" "has_offset_axes(::Array)" "Array never has offset axes." "base/abstractarray.jl:118" ``Property118 ``property118,
  entry "abstractarraycov-line122-has-offset-axes" "has_offset_axes(A, As...)" "The vararg method checks arguments left to right and short-circuits on true or an error." "base/abstractarray.jl:122" ``Property122 ``property122,
  entry "abstractarraycov-line135-require-one-based" "require_one_based_indexing(A...)" "The method returns unit exactly when has_offset_axes is false and otherwise throws ArgumentError." "base/abstractarray.jl:135" ``Property135 ``property135,
  entry "abstractarraycov-line140-axes1" "axes1(::AbstractArray{<:Any,0})" "A zero-dimensional array has the singleton first axis." "base/abstractarray.jl:140" ``Property140 ``property140,
  entry "abstractarraycov-line141-axes1" "axes1(::AbstractArray)" "The method returns the first member of axes(A), including its bounds error." "base/abstractarray.jl:141" ``Property141 ``property141,
  entry "abstractarraycov-line142-axes1" "axes1(iter)" "The generic iterable method calls length and then oneto." "base/abstractarray.jl:142" ``Property142 ``property142,
  entry "abstractarraycov-line169-keys" "keys(::AbstractArray)" "The generic array method constructs CartesianIndices from axes(A)." "base/abstractarray.jl:169" ``Property169 ``property169,
  entry "abstractarraycov-line170-keys" "keys(::AbstractVector)" "The vector method constructs LinearIndices from the vector." "base/abstractarray.jl:170" ``Property170 ``property170,
  entry "abstractarraycov-line192-keytype" "keytype(::AbstractArray)" "The value method calls typeof before keytype." "base/abstractarray.jl:192" ``Property192 ``property192,
  entry "abstractarraycov-line193-keytype" "keytype(::Type{Union{}}, slurp...)" "The Bottom keytype method delegates to Bottom eltype." "base/abstractarray.jl:193" ``Property193 ``property193,
  entry "abstractarraycov-line195-keytype" "keytype(::Type{<:AbstractArray})" "A generic rank-N array has CartesianIndex{N} keys." "base/abstractarray.jl:195" ``Property195 ``property195,
  entry "abstractarraycov-line196-keytype" "keytype(::Type{<:AbstractVector})" "An AbstractVector has Int keys." "base/abstractarray.jl:196" ``Property196 ``property196,
  entry "abstractarraycov-line198-valtype" "valtype(::AbstractArray)" "The value method calls typeof before valtype." "base/abstractarray.jl:198" ``Property198 ``property198,
  entry "abstractarraycov-line199-valtype" "valtype(::Type{Union{}}, slurp...)" "The Bottom valtype method delegates to Bottom eltype." "base/abstractarray.jl:199" ``Property199 ``property199,
  entry "abstractarraycov-line217-valtype" "valtype(::Type{<:AbstractArray})" "Array valtype delegates to eltype." "base/abstractarray.jl:217" ``Property217 ``property217,
  entry "abstractarraycov-line219-prevind" "prevind(::AbstractArray, ::Integer)" "prevind converts the index to Int before subtracting one with Julia Int arithmetic." "base/abstractarray.jl:219" ``Property219 ``property219,
  entry "abstractarraycov-line220-nextind" "nextind(::AbstractArray, ::Integer)" "nextind converts the index to Int before adding one with Julia Int arithmetic." "base/abstractarray.jl:220" ``Property220 ``property220,
  entry "abstractarraycov-line243-eltype" "eltype(::Type)" "The default type eltype is Any." "base/abstractarray.jl:243" ``Property243 ``property243,
  entry "abstractarraycov-line244-eltype" "eltype(::Type{Bottom}, slurp...)" "Bottom eltype throws the documented ArgumentError." "base/abstractarray.jl:244" ``Property244 ``property244,
  entry "abstractarraycov-line245-eltype" "eltype(x)" "The value method calls typeof before eltype." "base/abstractarray.jl:245" ``Property245 ``property245,
  entry "abstractarraycov-line246-eltype" "eltype(::Type{<:AbstractArray{E}})" "The array type method returns its defined element parameter and Any otherwise." "base/abstractarray.jl:246" ``Property246 ``property246,
  entry "abstractarraycov-line261-elsize" "elsize(::AbstractArray)" "The value method calls typeof before elsize." "base/abstractarray.jl:261" ``Property261 ``property261,
  entry "abstractarraycov-line278-ndims" "ndims(::AbstractArray{T,N})" "The value method returns rank N as Int." "base/abstractarray.jl:278" ``Property278 ``property278,
  entry "abstractarraycov-line279-ndims" "ndims(::Type{<:AbstractArray{<:Any,N}})" "The type method returns rank N as Int." "base/abstractarray.jl:279" ``Property279 ``property279,
  entry "abstractarraycov-line280-ndims" "ndims(::Type{Union{}}, slurp...)" "Bottom ndims throws the documented ArgumentError." "base/abstractarray.jl:280" ``Property280 ``property280
]

end JuliaLean.AbstractArrayCov.Rows.Basic
