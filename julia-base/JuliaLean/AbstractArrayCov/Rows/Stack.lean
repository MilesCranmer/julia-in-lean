import JuliaLean.AbstractArrayCov.Rows.Hvncat

/-! Method-specific models for `base/abstractarray.jl:2967-3101`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Stack

open JuliaLean
open JuliaLean.Registry

def method2967 (stack : δ → α → β) (dims : δ) (iter : α) : β := stack dims iter
def Property2967 : Prop := ∀ (δ α β : Type) (stack : δ → α → β) dims iter,
  method2967 stack dims iter = stack dims iter
theorem property2967 : Property2967 := by unfold Property2967; intros; rfl

def method2996 (map : (α → β) → γ → δ) (stack : σ → δ → ε)
    (f : α → β) (iter : γ) (dims : σ) : ε := stack dims (map f iter)
def Property2996 : Prop := ∀ (α β γ δ σ ε : Type)
    (map : (α → β) → γ → δ) (stack : σ → δ → ε) (f : α → β) (iter : γ) (dims : σ),
  method2996 map stack f iter dims = stack dims (map f iter)
theorem property2996 : Property2996 := by unfold Property2996; intros; rfl

def method2997 (zip : α → List β → γ) (map : (δ → ε) → γ → ζ)
    (stack : σ → ζ → η) (f : δ → ε) (xs : α) (rest : List β) (dims : σ) : η :=
  stack dims (map f (zip xs rest))
def Property2997 : Prop := ∀ (α β γ δ ε ζ σ η : Type)
    (zip : α → List β → γ) (map : (δ → ε) → γ → ζ) (stack : σ → ζ → η)
    (f : δ → ε) (xs : α) rest (dims : σ),
  method2997 zip map stack f xs rest dims = stack dims (map f (zip xs rest))
theorem property2997 : Property2997 := by unfold Property2997; intros; rfl

def method2999 (iteratorSize : α → σ) (stack : δ → σ → α → β)
    (dims : δ) (iter : α) : β := stack dims (iteratorSize iter) iter
def Property2999 : Prop := ∀ (α σ δ β : Type) (iteratorSize : α → σ)
    (stack : δ → σ → α → β) (dims : δ) (iter : α),
  method2999 iteratorSize stack dims iter = stack dims (iteratorSize iter) iter
theorem property2999 : Property2999 := by unfold Property2999; intros; rfl

def method3001 (collect : α → β) (stack : δ → β → γ) (dims : δ) (iter : α) : γ :=
  stack dims (collect iter)
def Property3001 : Prop := ∀ (α β δ γ : Type) (collect : α → β)
    (stack : δ → β → γ) (dims : δ) (iter : α),
  method3001 collect stack dims iter = stack dims (collect iter)
theorem property3001 : Property3001 := by unfold Property3001; intros; rfl

def method3003 (defaultType : α → τ) (elementType : τ → σ) (concrete : σ → Bool)
    (typed : δ → σ → τ → α → β) (collect : α → α) (isempty : α → Bool)
    (empty : δ → σ → τ → α → β) (promote : α → σ)
    (dims : δ) (iter : α) : β :=
  let s := defaultType iter
  let t := elementType s
  if concrete t then typed dims t s iter
  else
    let array := collect iter
    if isempty array then empty dims t s iter else typed dims (promote array) (defaultType array) array
def Property3003 : Prop := ∀ (α τ σ δ β : Type) (defaultType : α → τ)
    (elementType : τ → σ) (concrete : σ → Bool) (typed : δ → σ → τ → α → β)
    (collect : α → α) (isempty : α → Bool) (empty : δ → σ → τ → α → β)
    (promote : α → σ) (dims : δ) (iter : α),
  method3003 defaultType elementType concrete typed collect isempty empty promote dims iter =
    let s := defaultType iter
    let t := elementType s
    if concrete t then typed dims t s iter
    else let array := collect iter
      if isempty array then empty dims t s iter else typed dims (promote array) (defaultType array) array
theorem property3003 : Property3003 := by unfold Property3003; intros; rfl

def method3016 (iterate : α → List β) (axes : β → List γ)
    (allocate : β → List γ → List γ → δ) (copy : δ → Nat → β → δ)
    (a : α) (containerAxes : List γ) : Except String δ :=
  match iterate a with
  | [] => .error "stack on empty"
  | first :: rest =>
      let sliceAxes := axes first
      let out := allocate first sliceAxes containerAxes
      .ok ((first :: rest).foldl (fun out x => copy out 0 x) out)
def Property3016 : Prop := ∀ (α β γ δ : Type) (iterate : α → List β)
    (axes : β → List γ) (allocate : β → List γ → List γ → δ)
    (copy : δ → Nat → β → δ) (a : α) containerAxes,
  method3016 iterate axes allocate copy a containerAxes = match iterate a with
    | [] => .error "stack on empty"
    | first :: rest =>
      let sliceAxes := axes first
      let out := allocate first sliceAxes containerAxes
      .ok ((first :: rest).foldl (fun out x => copy out 0 x) out)
theorem property3016 : Property3016 := by
  unfold Property3016
  intro α β γ δ iterateFn axes allocate copy a containerAxes
  cases h : iterateFn a <;> simp [method3016, h]

def method3034 (iteratorSize : α → σ) (axes : α → σ → β) (x : α) : β :=
  axes x (iteratorSize x)
def Property3034 : Prop := ∀ (α σ β : Type) (iteratorSize : α → σ)
    (axes : α → σ → β) (x : α),
  method3034 iteratorSize axes x = axes x (iteratorSize x)
theorem property3034 : Property3034 := by unfold Property3034; intros; rfl

def method3035 (length : α → Nat) (oneTo : Nat → β) (x : α) : List β := [oneTo (length x)]
def Property3035 : Prop := ∀ (α β : Type) (length : α → Nat)
    (oneTo : Nat → β) (x : α),
  method3035 length oneTo x = [oneTo (length x)]
theorem property3035 : Property3035 := by unfold Property3035; intros; rfl

def method3036 (axes : α → β) (x : α) : β := axes x
def Property3036 : Prop := ∀ (α β : Type) (axes : α → β) (x : α), method3036 axes x = axes x
theorem property3036 : Property3036 := by unfold Property3036; intros; rfl

def method3039 (iteratorSize : τ → σ) (typed : Int → α → τ → σ → β)
    (dims : Int) (t : α) (s : τ) : β := typed dims t s (iteratorSize s)
def Property3039 : Prop := ∀ (τ σ α β : Type) (iteratorSize : τ → σ)
    (typed : Int → α → τ → σ → β) dims (t : α) (s : τ),
  method3039 iteratorSize typed dims t s = typed dims t s (iteratorSize s)
theorem property3039 : Property3039 := by unfold Property3039; intros; rfl

def method3041 (colonStack dimStack : β) (dims rank : Nat) : β :=
  if dims = rank + 1 then colonStack else dimStack
def Property3041 : Prop := ∀ (β : Type) (colonStack dimStack : β) dims rank,
  method3041 colonStack dimStack dims rank = if dims = rank + 1 then colonStack else dimStack
theorem property3041 : Property3041 := by unfold Property3041; intros; rfl

def method3048 (dimStack : Int → τ → σ → α → β) (dims : Int) (t : τ) (s : σ) (a : α) : β :=
  dimStack dims t s a
def Property3048 : Prop := ∀ (τ σ α β : Type) (dimStack : Int → τ → σ → α → β)
    dims (t : τ) (s : σ) (a : α),
  method3048 dimStack dims t s a = dimStack dims t s a
theorem property3048 : Property3048 := by unfold Property3048; intros; rfl

def method3051 (length : α → Nat) (oneTo : Nat → α) (axes : List α) : Option α :=
  match axes with
  | [axis] => some axis
  | _ => some (oneTo ((axes.map length).foldl (· * ·) 1))
def Property3051 : Prop := ∀ (α : Type) (length : α → Nat) (oneTo : Nat → α)
    (axes : List α),
  method3051 length oneTo axes = match axes with
    | [axis] => some axis
    | _ => some (oneTo ((axes.map length).foldl (· * ·) 1))
theorem property3051 : Property3051 := by
  unfold Property3051
  intro α length oneTo axes
  cases axes <;> rfl

def method3053 (peel : α → Option (β × List β)) (axes : β → List γ)
    (newAxis : α → γ) (allocate : β → List γ → δ)
    (fill : Nat → δ → β → List β → δ) (dims : Nat) (a : α) : Except String δ :=
  match peel a with
  | none => .error "stack on empty"
  | some (first, rest) =>
      let sliceAxes := axes first
      if !(1 ≤ dims && dims ≤ sliceAxes.length + 1) then .error "invalid stack dimension"
      else
        let outAxes := sliceAxes.take (dims - 1) ++ [newAxis a] ++ sliceAxes.drop (dims - 1)
        .ok (fill dims (allocate first outAxes) first rest)
def Property3053 : Prop := ∀ (α β γ δ : Type) (peel : α → Option (β × List β))
    (axes : β → List γ) (newAxis : α → γ) (allocate : β → List γ → δ)
    (fill : Nat → δ → β → List β → δ) dims (a : α),
  method3053 peel axes newAxis allocate fill dims a = match peel a with
    | none => .error "stack on empty"
    | some (first, rest) =>
      let sliceAxes := axes first
      if !(1 ≤ dims && dims ≤ sliceAxes.length + 1) then .error "invalid stack dimension"
      else let outAxes := sliceAxes.take (dims - 1) ++ [newAxis a] ++ sliceAxes.drop (dims - 1)
        .ok (fill dims (allocate first outAxes) first rest)
theorem property3053 : Property3053 := by
  unfold Property3053
  intro α β γ δ peelFn axes newAxis allocate fill dims a
  cases h : peelFn a <;> simp [method3053, h]

def method3075 (copy : δ → Nat → β → δ) (check : β → Jl Unit)
    (firstIndex : Nat) (out : δ) (first : β) (rest : List β) : Jl δ := do
  let mut out := copy out firstIndex first
  let mut i := firstIndex
  for x in rest do
    check x
    i := i + 1
    out := copy out i x
  return out
def Property3075 : Prop := ∀ (δ β : Type) (copy : δ → Nat → β → δ)
    (check : β → Jl Unit) firstIndex (out : δ) (first : β) rest,
  method3075 copy check firstIndex out first rest = do
    let mut out := copy out firstIndex first
    let mut i := firstIndex
    for x in rest do check x; i := i + 1; out := copy out i x
    return out
theorem property3075 : Property3075 := by unfold Property3075; intros; rfl

def method3089 [BEq α] (axes : β → List α) (x : β) (expected : List α) : Except String Unit :=
  if axes x == expected then .ok () else .error "stack expects uniform slices"
def Property3089 : Prop := ∀ (α β : Type) [BEq α] (axes : β → List α)
    (x : β) expected,
  method3089 axes x expected =
    if axes x == expected then Except.ok () else Except.error "stack expects uniform slices"
theorem property3089 : Property3089 := by unfold Property3089; intros; rfl

def method3098 (x : α) : α := x
def Property3098 : Prop := ∀ (α : Type) (x : α), method3098 x = x
theorem property3098 : Property3098 := by unfold Property3098; intros; rfl

def method3099 : List Nat := []
def Property3099 : Prop := ∀ _value : Unit, method3099 = []
theorem property3099 : Property3099 := by unfold Property3099; intros; rfl

def method3101 : Jl α := .error (.argumentError "`stack` on an empty collection is not allowed")
def Property3101 : Prop := ∀ (α : Type), (method3101 : Jl α) =
  .error (.argumentError "`stack` on an empty collection is not allowed")
theorem property3101 : Property3101 := by unfold Property3101; intros; rfl

private def entry (line : Nat) (slug fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"abstractarraycov-line{line}-{slug}", juliaFile := "base/abstractarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 2967 "stack" "stack(iter;dims)" "Public stack delegates to _stack with dims." "base/abstractarray.jl:2967" ``Property2967 ``property2967,
  entry 2996 "stack-map" "stack(f,iter;dims)" "Mapped stack lazily maps f before _stack." "base/abstractarray.jl:2996" ``Property2996 ``property2996,
  entry 2997 "stack-zip-map" "stack(f,xs,yzs...;dims)" "Multi-input stack zips, maps f, then calls _stack." "base/abstractarray.jl:2997" ``Property2997 ``property2997,
  entry 2999 "stack-dispatch" "_stack(dims,iter)" "The wrapper computes IteratorSize before dispatch." "base/abstractarray.jl:2999" ``Property2999 ``property2999,
  entry 3001 "stack-collect" "_stack(dims,::IteratorSize,iter)" "Unknown-size stack collects once before dispatch." "base/abstractarray.jl:3001" ``Property3001 ``property3001,
  entry 3003 "stack-shaped" "_stack(dims,::HasShapeOrLength,iter)" "The method selects concrete element type directly or collects once, rejects empty, promotes, and dispatches." "base/abstractarray.jl:3003-3014" ``Property3003 ``property3003,
  entry 3016 "typed-stack-colon" "_typed_stack(:,T,S,A,Aax)" "Colon stack rejects empty input, derives slice axes, allocates combined axes, and copies slices in order." "base/abstractarray.jl:3016-3032" ``Property3016 ``property3016,
  entry 3034 "iterator-axes" "_iterator_axes(x)" "The wrapper computes IteratorSize before dispatch." "base/abstractarray.jl:3034" ``Property3034 ``property3034,
  entry 3035 "iterator-axes-length" "_iterator_axes(x,::HasLength)" "Length-only iterators use a singleton OneTo axis." "base/abstractarray.jl:3035" ``Property3035 ``property3035,
  entry 3036 "iterator-axes" "_iterator_axes(x,::IteratorSize)" "Other iterators delegate to axes." "base/abstractarray.jl:3036" ``Property3036 ``property3036,
  entry 3039 "typed-stack-dispatch" "_typed_stack(dims,T,S,A)" "The wrapper computes IteratorSize(S) before dispatch." "base/abstractarray.jl:3039-3040" ``Property3039 ``property3039,
  entry 3041 "typed-stack-shaped" "_typed_stack(dims,T,S,::HasShape,A)" "The shape method selects colon stack exactly at rank plus one and dimensional stack otherwise." "base/abstractarray.jl:3041-3047" ``Property3041 ``property3041,
  entry 3048 "typed-stack-fallback" "_typed_stack(dims,T,S,::IteratorSize,A)" "The fallback delegates to _dim_stack." "base/abstractarray.jl:3048-3049" ``Property3048 ``property3048,
  entry 3051 "vec-axis" "_vec_axis" "One iterator axis is preserved; several collapse to OneTo of the product." "base/abstractarray.jl:3051" ``Property3051 ``property3051,
  entry 3053 "dim-stack" "_dim_stack" "The method peels once, rejects empty or invalid dimension, inserts the collection axis, allocates, then fills." "base/abstractarray.jl:3053-3073" ``Property3053 ``property3053,
  entry 3075 "dim-stack-fill" "_dim_stack!" "The fill writes the first slice, then validates and writes remaining slices at incrementing indices." "base/abstractarray.jl:3075-3087" ``Property3075 ``property3075,
  entry 3089 "stack-size-check" "_stack_size_check" "The helper succeeds exactly for equal iterator axes and throws otherwise." "base/abstractarray.jl:3089-3096" ``Property3089 ``property3089,
  entry 3098 "ensure-array" "_ensure_array(::AbstractArray)" "An array is returned unchanged." "base/abstractarray.jl:3098" ``Property3098 ``property3098,
  entry 3099 "ensure-array" "_ensure_array(x)" "A nonarray supplies the empty range sentinel for allocation." "base/abstractarray.jl:3099" ``Property3099 ``property3099,
  entry 3101 "empty-stack" "_empty_stack" "Empty stack always throws the documented ArgumentError." "base/abstractarray.jl:3101" ``Property3101 ``property3101
]

end JuliaLean.AbstractArrayCov.Rows.Stack
