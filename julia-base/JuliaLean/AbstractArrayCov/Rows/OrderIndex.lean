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

def entries : List Entry := [
  entry 3106 "isequal" "isequal(A,B)" "Array isequal checks identity, axes, then zipped elements in order." "base/abstractarray.jl:3106-3117" ``Property3106 ``property3106,
  entry 3119 "cmp" "cmp(A,B)" "Vector cmp checks first indices, elements lexicographically, then lengths." "base/abstractarray.jl:3119-3128" ``Property3119 ``property3119,
  entry 3135 "isless-zero-array" "isless(0d-array,0d-array)" "Zero-dimensional array ordering compares their only elements." "base/abstractarray.jl:3135-3137" ``Property3135 ``property3135,
  entry 3145 "isless-vector" "isless(vector,vector)" "Vector isless is cmp less than zero." "base/abstractarray.jl:3145" ``Property3145 ``property3145,
  entry 3147 "order-style" "OrderStyle(AbstractVector{T})" "Vector ordering style delegates to element ordering style." "base/abstractarray.jl:3147" ``Property3147 ``property3147,
  entry 3149 "array-equality" "==(A,B)" "Array equality checks axes and returns false, missing, or true from element comparisons." "base/abstractarray.jl:3149-3163" ``Property3149 ``property3149,
  entry 3167 "sub2ind" "_sub2ind(A,I...)" "Array sub2ind obtains axes before delegation." "base/abstractarray.jl:3167-3170" ``Property3167 ``property3167,
  entry 3172 "ind2sub" "_ind2sub(A,index)" "Array ind2sub obtains axes before delegation." "base/abstractarray.jl:3172-3175" ``Property3172 ``property3172,
  entry 3178 "sub2ind-empty" "_sub2ind(())" "Empty dimensions map to linear index one." "base/abstractarray.jl:3178" ``Property3178 ``property3178,
  entry 3179 "sub2ind-dims-empty-index" "_sub2ind(::DimsInteger)" "No supplied indices map to one." "base/abstractarray.jl:3179" ``Property3179 ``property3179,
  entry 3180 "sub2ind-indices-empty-index" "_sub2ind(::Indices)" "No supplied indices map to one." "base/abstractarray.jl:3180" ``Property3180 ``property3180,
  entry 3181 "sub2ind-empty-dims" "_sub2ind((),I...)" "Extra singleton subscripts use the empty-axis recurrence." "base/abstractarray.jl:3181" ``Property3181 ``property3181,
  entry 3184 "sub2ind-dims" "_sub2ind(dims,I...)" "Dims sub2ind starts stride and index at one." "base/abstractarray.jl:3184" ``Property3184 ``property3184,
  entry 3185 "sub2ind-indices" "_sub2ind(inds,I...)" "Axis sub2ind starts stride and index at one." "base/abstractarray.jl:3185" ``Property3185 ``property3185,
  entry 3188 "sub2ind-one-axis-error" "_sub2ind(inds::Indices{1},I...)" "One-dimensional non-OneTo axes reject ambiguous linear indexing." "base/abstractarray.jl:3188-3189" ``Property3188 ``property3188,
  entry 3190 "sub2ind-oneto" "_sub2ind((OneTo,),I...)" "OneTo axes use the standard recurrence." "base/abstractarray.jl:3190" ``Property3190 ``property3190,
  entry 3191 "sub2ind-oneto-linear" "_sub2ind((OneTo,),i)" "One OneTo linear index is returned unchanged." "base/abstractarray.jl:3191" ``Property3191 ``property3191,
  entry 3193 "sub2ind-recurse-base" "_sub2ind_recurse(any,L,index)" "The recurrence base returns its accumulated index." "base/abstractarray.jl:3193" ``Property3193 ``property3193,
  entry 3194 "sub2ind-recurse-empty" "_sub2ind_recurse((),L,index,i,I...)" "Trailing singleton indices add (i-1)*stride before recursion." "base/abstractarray.jl:3194-3197" ``Property3194 ``property3194,
  entry 3198 "sub2ind-recurse" "_sub2ind_recurse(inds,L,index,i,I...)" "The recurrence updates stride from the first axis and index from its offset." "base/abstractarray.jl:3198-3202" ``Property3198 ``property3198,
  entry 3204 "next-stride" "nextL(L,length)" "Integer dimensions multiply the running stride." "base/abstractarray.jl:3204" ``Property3204 ``property3204,
  entry 3205 "next-stride" "nextL(L,range)" "Range dimensions multiply by their length." "base/abstractarray.jl:3205" ``Property3205 ``property3205,
  entry 3206 "next-stride" "nextL(L,slice)" "Slice dimensions multiply by their underlying length." "base/abstractarray.jl:3206" ``Property3206 ``property3206,
  entry 3207 "offsetin" "offsetin(i,length)" "Integer dimensions use i-1." "base/abstractarray.jl:3207" ``Property3207 ``property3207,
  entry 3208 "offsetin" "offsetin(i,range)" "Range dimensions use i-first(range)." "base/abstractarray.jl:3208" ``Property3208 ``property3208,
  entry 3210 "ind2sub-empty" "_ind2sub((),index)" "Empty dimensions accept only index one." "base/abstractarray.jl:3210" ``Property3210 ``property3210,
  entry 3211 "ind2sub-dims" "_ind2sub(dims,index)" "Dims ind2sub subtracts one before recursion." "base/abstractarray.jl:3211" ``Property3211 ``property3211,
  entry 3212 "ind2sub-indices" "_ind2sub(inds,index)" "Axis ind2sub subtracts one before recursion." "base/abstractarray.jl:3212" ``Property3212 ``property3212,
  entry 3213 "ind2sub-one-axis-error" "_ind2sub(Indices{1},index)" "One-dimensional non-OneTo axes reject ambiguous linear indexing." "base/abstractarray.jl:3213-3214" ``Property3213 ``property3213,
  entry 3215 "ind2sub-oneto" "_ind2sub((OneTo,),index)" "One OneTo axis returns the index tuple unchanged." "base/abstractarray.jl:3215" ``Property3215 ``property3215,
  entry 3217 "ind2sub-recurse-empty" "_ind2sub_recurse((),index)" "The empty recurrence restores one-based indexing." "base/abstractarray.jl:3217" ``Property3217 ``property3217,
  entry 3218 "ind2sub-recurse-one" "_ind2sub_recurse((axis,),index)" "One remaining axis applies lookup." "base/abstractarray.jl:3218-3221" ``Property3218 ``property3218,
  entry 3222 "ind2sub-recurse" "_ind2sub_recurse(inds,index)" "The recurrence divides by first-axis length, looks up its remainder, and recurs on the quotient." "base/abstractarray.jl:3222-3227" ``Property3222 ``property3222,
  entry 3229 "indexlength" "_indexlength(integer)" "Integer dimension length is the dimension itself." "base/abstractarray.jl:3229" ``Property3229 ``property3229,
  entry 3230 "indexlength" "_indexlength(range)" "Range dimension length is length(range)." "base/abstractarray.jl:3230" ``Property3230 ``property3230,
  entry 3231 "lookup" "_lookup(index,dimension)" "Integer dimension lookup adds one." "base/abstractarray.jl:3231" ``Property3231 ``property3231,
  entry 3232 "lookup" "_lookup(index,range)" "Range lookup adds first(range)." "base/abstractarray.jl:3232" ``Property3232 ``property3232,
  entry 3235 "sub2ind-vector-error" "_sub2ind(Indices{1},vectors...)" "Vectorized one-dimensional non-OneTo axes reject linear indexing." "base/abstractarray.jl:3235-3237" ``Property3235 ``property3235,
  entry 3238 "sub2ind-vectors-oneto" "_sub2ind((OneTo,),vectors...)" "Vectorized OneTo axes delegate to _sub2ind_vecs." "base/abstractarray.jl:3238-3239" ``Property3238 ``property3238,
  entry 3240 "sub2ind-vectors" "_sub2ind(dims-or-indices,vectors...)" "Vectorized dims and axes delegate to _sub2ind_vecs." "base/abstractarray.jl:3240-3241" ``Property3240 ``property3240,
  entry 3242 "sub2ind-vecs" "_sub2ind_vecs" "The method checks all vector axes, allocates like the first, then fills each shared index." "base/abstractarray.jl:3242-3251" ``Property3242 ``property3242,
  entry 3253 "sub2ind-fill" "_sub2ind!" "The fill loop computes one linear index at every shared vector index." "base/abstractarray.jl:3253-3260" ``Property3253 ``property3253,
  entry 3262 "sub2ind-vec" "sub2ind_vec" "The helper gathers every coordinate at i before scalar sub2ind." "base/abstractarray.jl:3262" ``Property3262 ``property3262,
  entry 3263 "sub2ind-vec-tail" "_sub2ind_vec(i,I1,I...)" "The recursive gather prepends I1[i]." "base/abstractarray.jl:3263" ``Property3263 ``property3263,
  entry 3264 "sub2ind-vec-empty" "_sub2ind_vec(i)" "The coordinate gather base returns empty." "base/abstractarray.jl:3264" ``Property3264 ``property3264,
  entry 3266 "ind2sub-vectors" "_ind2sub(inds,index-vector)" "Vectorized ind2sub allocates one output per axis and fills every input index." "base/abstractarray.jl:3266-3275" ``Property3266 ``property3266
]

end JuliaLean.AbstractArrayCov.Rows.OrderIndex
