import JuliaLean.AbstractArrayCov.Rows.Stack

/-! Method-specific models for `base/abstractarray.jl:3106-3275`. -/

namespace JuliaLean.AbstractArrayCov.Rows.OrderIndex

open JuliaLean
open JuliaLean.Registry
open JuliaLean.AbstractArrays

abbrev I64 := JInt .i64
def i64 (x : Int) : I64 := JInt.lit .i64 x

def method3106 [BEq β] (identical : α → α → Bool) (axes : α → β)
    (values : α → List γ) (equal : γ → γ → Bool) (a b : α) : Bool :=
  if identical a b then true
  else if axes a != axes b then false
  else ((values a).zip (values b)).all fun p => equal p.1 p.2
def Property3106 : Prop := ∀ (α β γ : Type) [BEq β]
    (identical : α → α → Bool) (axes : α → β) (values : α → List γ)
    (equal : γ → γ → Bool) (a b : α),
  method3106 identical axes values equal a b =
    if identical a b then true
    else if axes a != axes b then false
    else ((values a).zip (values b)).all fun p => equal p.1 p.2
theorem property3106 : Property3106 := by unfold Property3106; intros; rfl

def lexCmp (equal : α → β → Bool) (less : α → β → Bool) : List (α × β) → Int
  | [] => 0
  | p :: rest => if equal p.1 p.2 then lexCmp equal less rest else if less p.1 p.2 then -1 else 1

def compareInt (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0
def compareNat (a b : Nat) : Int := if a < b then -1 else if b < a then 1 else 0

def method3119 (firstindex : α → Int) (values : α → List β)
    (equal less : β → β → Bool) (a b : α) : Int :=
  let firstCmp := compareInt (firstindex a) (firstindex b)
  let pairs := (values a).zip (values b)
  let lengthCmp := compareNat (values a).length (values b).length
  if firstCmp != 0 then firstCmp
  else let c := lexCmp equal less pairs; if c != 0 then c else lengthCmp
def Property3119 : Prop := ∀ (α β : Type) (firstindex : α → Int)
    (values : α → List β) (equal less : β → β → Bool) (a b : α),
  method3119 firstindex values equal less a b =
    let firstCmp := compareInt (firstindex a) (firstindex b)
    let pairs := (values a).zip (values b)
    let lengthCmp := compareNat (values a).length (values b).length
    if firstCmp != 0 then firstCmp
    else let c := lexCmp equal less pairs; if c != 0 then c else lengthCmp
theorem property3119 : Property3119 := by unfold Property3119; intros; rfl

def method3135 (onlyA : α) (onlyB : β) (less : α → β → Bool) : Bool := less onlyA onlyB
def Property3135 : Prop := ∀ (α β : Type) (a : α) (b : β) (less : α → β → Bool),
  method3135 a b less = less a b
theorem property3135 : Property3135 := by unfold Property3135; intros; rfl

def method3145 (cmp : α → α → Int) (a b : α) : Bool := decide (cmp a b < 0)
def Property3145 : Prop := ∀ (α : Type) (cmp : α → α → Int) (a b : α),
  method3145 cmp a b = decide (cmp a b < 0)
theorem property3145 : Property3145 := by unfold Property3145; intros; rfl

def method3147 (elementStyle : τ → σ) (t : τ) : σ := elementStyle t
def Property3147 : Prop := ∀ (τ σ : Type) (elementStyle : τ → σ) (t : τ),
  method3147 elementStyle t = elementStyle t
theorem property3147 : Property3147 := by unfold Property3147; intros; rfl

inductive Tri where | false | missing | true
  deriving Repr, DecidableEq

def method3149 [BEq β] (axes : α → β) (compareValues : α → α → List Tri) (a b : α) : Tri :=
  if axes a != axes b then .false
  else let results := compareValues a b
    if results.contains .false then .false
    else if results.contains .missing then .missing else .true
def Property3149 : Prop := ∀ (α β : Type) [BEq β] (axes : α → β)
    (compareValues : α → α → List Tri) (a b : α),
  method3149 axes compareValues a b = if axes a != axes b then .false
    else let results := compareValues a b
      if results.contains .false then .false
      else if results.contains .missing then .missing else .true
theorem property3149 : Property3149 := by unfold Property3149; intros; rfl

def method3167 (axes : α → β) (sub2ind : β → List Int → γ) (a : α) (indices : List Int) : γ :=
  sub2ind (axes a) indices
def Property3167 : Prop := ∀ (α β γ : Type) (axes : α → β)
    (sub2ind : β → List Int → γ) (a : α) indices,
  method3167 axes sub2ind a indices = sub2ind (axes a) indices
theorem property3167 : Property3167 := by unfold Property3167; intros; rfl

def method3172 (axes : α → β) (ind2sub : β → Int → γ) (a : α) (index : Int) : γ :=
  ind2sub (axes a) index
def Property3172 : Prop := ∀ (α β γ : Type) (axes : α → β)
    (ind2sub : β → Int → γ) (a : α) index,
  method3172 axes ind2sub a index = ind2sub (axes a) index
theorem property3172 : Property3172 := by unfold Property3172; intros; rfl

def method3178 : Int := 1
def Property3178 : Prop := ∀ _empty : Unit, method3178 = 1
theorem property3178 : Property3178 := by unfold Property3178; intros; rfl
def method3179 (_dims : α) : Int := 1
def Property3179 : Prop := ∀ (α : Type) (dims : α), method3179 dims = 1
theorem property3179 : Property3179 := by unfold Property3179; intros; rfl
def method3180 (_inds : α) : Int := 1
def Property3180 : Prop := ∀ (α : Type) (inds : α), method3180 inds = 1
theorem property3180 : Property3180 := by unfold Property3180; intros; rfl

def method3181 (recurse : List Int → I64 → I64 → List I64 → I64)
    (indices : List I64) : I64 := recurse [] (i64 1) (i64 1) indices
def Property3181 : Prop := ∀ recurse indices,
  method3181 recurse indices = recurse [] (i64 1) (i64 1) indices
theorem property3181 : Property3181 := by unfold Property3181; intros; rfl

def method3184 (recurse : α → I64 → I64 → List I64 → I64)
    (dims : α) (indices : List I64) : I64 := recurse dims (i64 1) (i64 1) indices
def Property3184 : Prop := ∀ (α : Type) (recurse : α → I64 → I64 → List I64 → I64)
    (dims : α) indices,
  method3184 recurse dims indices = recurse dims (i64 1) (i64 1) indices
theorem property3184 : Property3184 := by unfold Property3184; intros; rfl

def method3185 (recurse : α → I64 → I64 → List I64 → I64)
    (inds : α) (indices : List I64) : I64 := recurse inds (i64 1) (i64 1) indices
def Property3185 : Prop := ∀ (α : Type) (recurse : α → I64 → I64 → List I64 → I64)
    (inds : α) indices,
  method3185 recurse inds indices = recurse inds (i64 1) (i64 1) indices
theorem property3185 : Property3185 := by unfold Property3185; intros; rfl

def method3188 : Jl I64 := .error (.argumentError "Linear indexing is not defined for one-dimensional arrays")
def Property3188 : Prop := ∀ _indices : List I64,
  method3188 = .error (.argumentError "Linear indexing is not defined for one-dimensional arrays")
theorem property3188 : Property3188 := by unfold Property3188; intros; rfl

def method3190 (recurse : α → I64 → I64 → List I64 → I64)
    (inds : α) (indices : List I64) : I64 := recurse inds (i64 1) (i64 1) indices
def Property3190 : Prop := ∀ (α : Type) (recurse : α → I64 → I64 → List I64 → I64)
    (inds : α) indices,
  method3190 recurse inds indices = recurse inds (i64 1) (i64 1) indices
theorem property3190 : Property3190 := by unfold Property3190; intros; rfl

def method3191 (i : I64) : I64 := i
def Property3191 : Prop := ∀ i, method3191 i = i
theorem property3191 : Property3191 := by unfold Property3191; intros; rfl

def method3193 (_inds : α) (_stride : I64) (index : I64) : I64 := index
def Property3193 : Prop := ∀ (α : Type) (inds : α) stride index,
  method3193 inds stride index = index
theorem property3193 : Property3193 := by unfold Property3193; intros; rfl

def method3194 (recurse : I64 → I64 → List I64 → I64)
    (stride index : I64) (indices : List I64) : I64 :=
  match indices with
  | [] => index
  | i :: rest => recurse stride (index + (i - i64 1) * stride) rest
def Property3194 : Prop := ∀ recurse stride index indices,
  method3194 recurse stride index indices = match indices with
    | [] => index
    | i :: rest => recurse stride (index + (i - i64 1) * stride) rest
theorem property3194 : Property3194 := by
  unfold Property3194
  intro recurse stride index indices
  cases indices <;> rfl

def method3198 (nextStride : I64 → Axis → I64) (recurse : List Axis → I64 → I64 → List I64 → I64)
    (inds : List Axis) (stride index : I64) (indices : List I64) : I64 :=
  match inds, indices with
  | axis :: axes, i :: rest => recurse axes (nextStride stride axis)
      (index + (i - axis.first) * stride) rest
  | _, _ => index
def Property3198 : Prop := ∀ nextStride recurse inds stride index indices,
  method3198 nextStride recurse inds stride index indices = match inds, indices with
    | axis :: axes, i :: rest => recurse axes (nextStride stride axis)
      (index + (i - axis.first) * stride) rest
    | _, _ => index
theorem property3198 : Property3198 := by
  unfold Property3198
  intro nextStride recurse inds stride index indices
  cases inds <;> cases indices <;> rfl

def method3204 (stride length : I64) : I64 := stride * length
def Property3204 : Prop := ∀ stride length, method3204 stride length = stride * length
theorem property3204 : Property3204 := by unfold Property3204; intros; rfl
def method3205 (stride : I64) (axis : Axis) : I64 := stride * i64 axis.len
def Property3205 : Prop := ∀ stride axis, method3205 stride axis = stride * i64 axis.len
theorem property3205 : Property3205 := by unfold Property3205; intros; rfl
def method3206 (stride : I64) (slice : Axis) : I64 := stride * i64 slice.len
def Property3206 : Prop := ∀ stride slice, method3206 stride slice = stride * i64 slice.len
theorem property3206 : Property3206 := by unfold Property3206; intros; rfl
def method3207 (i _length : I64) : I64 := i - i64 1
def Property3207 : Prop := ∀ i length, method3207 i length = i - i64 1
theorem property3207 : Property3207 := by unfold Property3207; intros; rfl
def method3208 (i : I64) (axis : Axis) : I64 := i - axis.first
def Property3208 : Prop := ∀ i axis, method3208 i axis = i - axis.first
theorem property3208 : Property3208 := by unfold Property3208; intros; rfl

def method3210 (index : I64) : Jl (List I64) :=
  if index.val = 1 then .ok [] else .error .boundsError
def Property3210 : Prop := ∀ index, method3210 index =
  if index.val = 1 then .ok [] else .error .boundsError
theorem property3210 : Property3210 := by unfold Property3210; intros; rfl

def method3211 (recurse : α → I64 → β) (dims : α) (index : I64) : β :=
  recurse dims (index - i64 1)
def Property3211 : Prop := ∀ (α β : Type) (recurse : α → I64 → β)
    (dims : α) index,
  method3211 recurse dims index = recurse dims (index - i64 1)
theorem property3211 : Property3211 := by unfold Property3211; intros; rfl
def method3212 (recurse : α → I64 → β) (inds : α) (index : I64) : β :=
  recurse inds (index - i64 1)
def Property3212 : Prop := ∀ (α β : Type) (recurse : α → I64 → β)
    (inds : α) index,
  method3212 recurse inds index = recurse inds (index - i64 1)
theorem property3212 : Property3212 := by unfold Property3212; intros; rfl
def method3213 : Jl (List I64) := .error (.argumentError "Linear indexing is not defined for one-dimensional arrays")
def Property3213 : Prop := ∀ _index : I64,
  method3213 = .error (.argumentError "Linear indexing is not defined for one-dimensional arrays")
theorem property3213 : Property3213 := by unfold Property3213; intros; rfl
def method3215 (index : I64) : List I64 := [index]
def Property3215 : Prop := ∀ index, method3215 index = [index]
theorem property3215 : Property3215 := by unfold Property3215; intros; rfl

def method3217 (index : I64) : List I64 := [index + i64 1]
def Property3217 : Prop := ∀ index, method3217 index = [index + i64 1]
theorem property3217 : Property3217 := by unfold Property3217; intros; rfl
def method3218 (lookup : I64 → Axis → I64) (axis : Axis) (index : I64) : List I64 :=
  [lookup index axis]
def Property3218 : Prop := ∀ lookup axis index, method3218 lookup axis index = [lookup index axis]
theorem property3218 : Property3218 := by unfold Property3218; intros; rfl

def method3222 (recurse : List Axis → I64 → List I64) (inds : List Axis) (index : I64) : List I64 :=
  match inds with
  | [] => [index + i64 1]
  | axis :: rest =>
      let divisor := i64 axis.len
      let q := i64 (index.val / divisor.val)
      let r := i64 (index.val % divisor.val)
      (axis.first + r) :: recurse rest q
def Property3222 : Prop := ∀ recurse inds index,
  method3222 recurse inds index = match inds with
    | [] => [index + i64 1]
    | axis :: rest =>
      let divisor := i64 axis.len
      let q := i64 (index.val / divisor.val)
      let r := i64 (index.val % divisor.val)
      (axis.first + r) :: recurse rest q
theorem property3222 : Property3222 := by
  unfold Property3222
  intro recurse inds index
  cases inds <;> rfl

def method3229 (dimension : I64) : I64 := dimension
def Property3229 : Prop := ∀ d, method3229 d = d
theorem property3229 : Property3229 := by unfold Property3229; intros; rfl
def method3230 (axis : Axis) : I64 := i64 axis.len
def Property3230 : Prop := ∀ axis, method3230 axis = i64 axis.len
theorem property3230 : Property3230 := by unfold Property3230; intros; rfl
def method3231 (index _dimension : I64) : I64 := index + i64 1
def Property3231 : Prop := ∀ index d, method3231 index d = index + i64 1
theorem property3231 : Property3231 := by unfold Property3231; intros; rfl
def method3232 (index : I64) (axis : Axis) : I64 := index + axis.first
def Property3232 : Prop := ∀ index axis, method3232 index axis = index + axis.first
theorem property3232 : Property3232 := by unfold Property3232; intros; rfl

def method3235 : Jl (List I64) := .error (.argumentError "Linear indexing is not defined for one-dimensional arrays")
def Property3235 : Prop := ∀ _vectors : List (List I64),
  method3235 = .error (.argumentError "Linear indexing is not defined for one-dimensional arrays")
theorem property3235 : Property3235 := by unfold Property3235; intros; rfl
def method3238 (call : List Axis → List (List I64) → β) (inds : List Axis) (indices : List (List I64)) : β := call inds indices
def Property3238 : Prop := ∀ (β : Type) (call : List Axis → List (List I64) → β)
    inds indices, method3238 call inds indices = call inds indices
theorem property3238 : Property3238 := by unfold Property3238; intros; rfl
def method3240 (call : List Axis → List (List I64) → β) (inds : List Axis) (indices : List (List I64)) : β := call inds indices
def Property3240 : Prop := ∀ (β : Type) (call : List Axis → List (List I64) → β)
    inds indices, method3240 call inds indices = call inds indices
theorem property3240 : Property3240 := by unfold Property3240; intros; rfl

def method3242 (sameAxes : List (List I64) → Bool)
    (similar : List I64 → List I64) (fill : List I64 → List (List I64) → List I64)
    (indices : List (List I64)) : Except String (List I64) :=
  match indices with
  | [] => .error "missing index vector"
  | first :: _ => if !sameAxes indices then .error "index axes mismatch"
    else .ok (fill (similar first) indices)
def Property3242 : Prop := ∀ sameAxes similar fill indices,
  method3242 sameAxes similar fill indices = match indices with
    | [] => .error "missing index vector"
    | first :: _ => if !sameAxes indices then .error "index axes mismatch"
      else .ok (fill (similar first) indices)
theorem property3242 : Property3242 := by
  unfold Property3242
  intro sameAxes similar fill indices
  cases indices <;> rfl

def method3253 (sub2ind : List Axis → List I64 → I64)
    (inds : List Axis) (coordinates : List (List I64)) : List I64 :=
  match coordinates with
  | [] => []
  | first :: _ => (List.range first.length).map fun k =>
      sub2ind inds (coordinates.filterMap fun is => is[k]?)
def Property3253 : Prop := ∀ sub2ind inds coordinates,
  method3253 sub2ind inds coordinates = match coordinates with
    | [] => []
    | first :: _ => (List.range first.length).map fun k =>
      sub2ind inds (coordinates.filterMap fun is => is[k]?)
theorem property3253 : Property3253 := by
  unfold Property3253
  intro sub2ind inds coordinates
  cases coordinates <;> rfl

def method3262 (sub2ind : List Axis → List I64 → I64) (inds : List Axis)
    (i : Nat) (vectors : List (List I64)) : I64 :=
  sub2ind inds (vectors.filterMap fun v => v[i]?)
def Property3262 : Prop := ∀ sub2ind inds i vectors,
  method3262 sub2ind inds i vectors = sub2ind inds (vectors.filterMap fun v => v[i]?)
theorem property3262 : Property3262 := by unfold Property3262; intros; rfl

def method3263 (i : Nat) (first : List I64) (rest : List (List I64)) : List I64 :=
  first[i]?.toList ++ rest.filterMap fun v => v[i]?
def Property3263 : Prop := ∀ i first rest,
  method3263 i first rest = first[i]?.toList ++ rest.filterMap fun v => v[i]?
theorem property3263 : Property3263 := by unfold Property3263; intros; rfl
def method3264 (_i : Nat) : List I64 := []
def Property3264 : Prop := ∀ i, method3264 i = []
theorem property3264 : Property3264 := by unfold Property3264; intros; rfl

def method3266 (ind2sub : List Axis → I64 → List I64)
    (inds : List Axis) (indices : List I64) : List (List I64) :=
  (List.range inds.length).map fun d => indices.filterMap fun index => (ind2sub inds index)[d]?
def Property3266 : Prop := ∀ ind2sub inds indices,
  method3266 ind2sub inds indices =
    (List.range inds.length).map fun d => indices.filterMap fun index => (ind2sub inds index)[d]?
theorem property3266 : Property3266 := by unfold Property3266; intros; rfl

private def entry (line : Nat) (slug fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"abstractarraycov-line{line}-{slug}", juliaFile := "base/abstractarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.OrderIndex
