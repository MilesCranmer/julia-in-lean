import JuliaLean.base.abstractarray
import JuliaLean.base.array
import JuliaLean.Proofs.base.abstractarray.rows.order_index


namespace JuliaLean.AbstractArrayCov.Rows.MapMut

open JuliaLean
open JuliaLean.Registry

def Property3307 : Prop := ∀ (σ α : Type) (f : σ → α → σ) state values,
  method3307 f state values = (values.foldl f state, ())
theorem property3307 : Property3307 := by unfold Property3307; intros; rfl

def Property3308 : Prop := ∀ (σ α : Type) (f : σ → List α → σ) state zipped,
  method3308 f state zipped = (zipped.foldl f state, ())
theorem property3308 : Property3308 := by unfold Property3308; intros; rfl

def Property3385 : Prop := ∀ (α γ δ ε : Type) (mapAll : Jl ε) rank dims
    (firstSlice : Jl α) (applyFirst : α → Jl γ) (prepare : α → γ → Jl δ)
    (allocate : δ → Jl ε) (place : ε → δ → Jl ε) (inner : ε → Jl ε),
  method3385 mapAll rank dims firstSlice applyFirst prepare allocate place inner = do
    if dims.isEmpty then return ← mapAll
    for d in dims do
      if d < 1 then throw (.argumentError "mapslices dimension must be at least 1")
      if rank < d then throw (.argumentError "mapslices dimension exceeds rank")
    let slice ← firstSlice
    let firstResult ← applyFirst slice
    let prepared ← prepare slice firstResult
    let out ← allocate prepared
    let out ← place out prepared
    inner out
theorem property3385 : Property3385 := by unfold Property3385; intros; rfl

def Property3450 : Prop := ∀ (δ ι : Type) safe (reuse fresh : δ → ι → Jl δ)
    (out : δ) indices,
  method3450 safe reuse fresh out indices =
    if safe then foldIndices reuse out indices else foldIndices fresh out indices
theorem property3450 : Property3450 := by unfold Property3450; intros; rfl

def Property3477 : Prop := ∀ (δ ι α : Type) (broadcastSet : δ → List ι → α → δ)
    (out : δ) (value : α) indices,
  method3477 broadcastSet out value indices = broadcastSet out indices value
theorem property3477 : Property3477 := by unfold Property3477; intros; rfl

def Property3478 : Prop := ∀ (δ ι α : Type) (set : δ → List ι → α → δ)
    (out : δ) (value : α) indices,
  method3478 set out value indices = set out indices value
theorem property3478 : Property3478 := by unfold Property3478; intros; rfl

def Property3482 : Prop := ∀ (α β : Type) (f : α → β) (dest : List β) (source : List α),
  method3482 f dest source = source.map f ++ dest.drop source.length
theorem property3482 : Property3482 := by
  unfold Property3482
  intros
  simp [method3482]

def Property3491 : Prop := ∀ (α β γ δ ε : Type)
    (generator : (α → β) → γ → δ) (collect : γ → δ → ε)
    (f : α → β) (a : γ),
  method3491 generator collect f a = collect a (generator f a)
theorem property3491 : Property3491 := by unfold Property3491; intros; rfl

def Property3493 : Prop := ∀ (α β : Type) (allocate : Nat → List β)
    (f : α → β) (source : List α),
  method3493 allocate f source = method3482 f (allocate source.length) source
theorem property3493 : Property3493 := by unfold Property3493; intros; rfl

def Property3494 : Prop := ∀ (α β : Type) (f : α → β) (source : List α),
  method3494 f source = source.map f
theorem property3494 : Property3494 := by unfold Property3494; intros; rfl

def Property3521 : Prop := ∀ (α β γ δ ε : Type)
    (generator : (α → β) → γ → δ) (collect : δ → ε)
    (f : α → β) (source : γ),
  method3521 generator collect f source = collect (generator f source)
theorem property3521 : Property3521 := by unfold Property3521; intros; rfl

def Property3523 : Prop := ∀ (α : Type), (method3523 : Except String α) =
  .error "map is not defined on dictionaries"
theorem property3523 : Property3523 := by unfold Property3523; intros; rfl
def Property3524 : Prop := ∀ (α : Type), (method3524 : Except String α) =
  .error "map is not defined on sets"
theorem property3524 : Property3524 := by unfold Property3524; intros; rfl

def Property3527 : Prop := ∀ (α β γ : Type) (f : α → β → γ)
    (dest : List γ) (as : List α) (bs : List β),
  method3527 f dest as bs =
    let values := (as.zip bs).map fun p => f p.1 p.2
    values ++ dest.drop values.length
theorem property3527 : Property3527 := by unfold Property3527; intros; rfl

def Property3538 : Prop := ∀ (α : Type) i, (method3538 i : List α) = []
theorem property3538 : Property3538 := by unfold Property3538; intros; rfl

def Property3539 : Prop := ∀ (α : Type) i (arrays : List (List α)),
  method3539 i arrays = arrays.filterMap fun a => a[i]?
theorem property3539 : Property3539 := by unfold Property3539; intros; rfl

def Property3544 : Prop := ∀ (δ α : Type) (linearIndices : List α → List Nat)
    (linear cartesian : δ → List (List α) → δ) destIndices (dest : δ) arrays,
  method3544 linearIndices linear cartesian destIndices dest arrays =
    if arrays.all (fun a => linearIndices a == destIndices) then linear dest arrays else cartesian dest arrays
theorem property3544 : Property3544 := by unfold Property3544; intros; rfl

def Property3593 : Prop := ∀ (α β δ γ : Type)
    (mapN : (List α → β) → δ → List (List α) → γ)
    (f : List α → β) (dest : δ) arrays,
  method3593 mapN f dest arrays =
    if arrays.isEmpty then .error "should dispatch to unary map!" else .ok (mapN f dest arrays)
theorem property3593 : Property3593 := by unfold Property3593; intros; rfl

def Property3618 : Prop := ∀ (α β γ : Type) (map : (α → α) → β → β → γ)
    (f : α → α) (array : β),
  method3618 map f array = map f array array
theorem property3618 : Property3618 := by unfold Property3618; intros; rfl

def Property3645 : Prop := ∀ (α β γ δ : Type)
    (generator : (List α → β) → List (List α) → γ) (collect : γ → δ)
    (f : List α → β) iters,
  method3645 generator collect f iters = collect (generator f iters)
theorem property3645 : Property3645 := by unfold Property3645; intros; rfl

def Property3649 : Prop := ∀ (α β : Type) (convert : α → Jl β)
    (append : List β → β → List β) (a : List β) (item : α),
  method3649 convert append a item = do let item ← convert item; return append a item
theorem property3649 : Property3649 := by unfold Property3649; intros; rfl

def Property3659 : Prop := ∀ (α : Type) (a : List α) (x : α), method3659 a x = a ++ [x]
theorem property3659 : Property3659 := by unfold Property3659; intros; rfl
def Property3665 : Prop := ∀ (α : Type) (a xs : List α), method3665 a xs = a ++ xs
theorem property3665 : Property3665 := by unfold Property3665; intros; rfl

def Property3679 : Prop := ∀ (α β : Type) (push : α → β → α) (a : α) (x y : β),
  method3679 push a x y = push (push a x) y
theorem property3679 : Property3679 := by unfold Property3679; intros; rfl
def Property3680 : Prop := ∀ (α β : Type) (push2 : α → β → β → α)
    (pushMany : α → List β → α) (a : α) (x y : β) rest,
  method3680 push2 pushMany a x y rest = pushMany (push2 a x y) rest
theorem property3680 : Property3680 := by unfold Property3680; intros; rfl
def Property3681 : Prop := ∀ (α β : Type) (pushfirst : α → β → α)
    (a : α) (x y : β),
  method3681 pushfirst a x y = pushfirst (pushfirst a y) x
theorem property3681 : Property3681 := by unfold Property3681; intros; rfl
def Property3682 : Prop := ∀ (α β : Type) (pushMany : α → List β → α)
    (push2 : α → β → β → α) (a : α) (x y : β) rest,
  method3682 pushMany push2 a x y rest = push2 (pushMany a rest) x y
theorem property3682 : Property3682 := by unfold Property3682; intros; rfl

def Property3685 : Prop := ∀ (α β : Type) (a : α) (hint : β), method3685 a hint = a
theorem property3685 : Property3685 := by unfold Property3685; intros; rfl

def Property3688 : Prop := ∀ (α σ β : Type) (length : α → Nat)
    (rest : α → σ → List β) (a : α) (state : σ),
  method3688 length rest a state = (rest a state).foldl (fun out x => out ++ [x]) []
theorem property3688 : Property3688 := by unfold Property3688; intros; rfl

def Property3699 : Prop := ∀ (α : Type) values indices,
  method3699 (α := α) JuliaLean.ArrayOps.keepat values indices = JuliaLean.ArrayOps.keepat values indices
theorem property3699 : Property3699 := by unfold Property3699; intros; rfl

def Property3717 : Prop := ∀ (α : Type) values mask,
  method3717 (α := α) values mask = if mask.length != values.length then .error "bounds"
    else .ok ((values.zip mask).filterMap fun p => if p.2 then some p.1 else none)
theorem property3717 : Property3717 := by unfold Property3717; intros; rfl

def Property3756 : Prop := ∀ (α : Type) (length : α → Nat) (modShift : Int → Nat → Int)
    (lastindex firstindex : α → Int) (reverseWindow : α → Int → Int → α)
    (reverseAll : α → α) (a : α) shift,
  method3756 length modShift lastindex firstindex reverseWindow reverseAll a shift =
    let n := length a
    if n = 0 then a
    else let shift := modShift shift n
      if shift = 0 then a
      else let last := lastindex a
        reverseAll (reverseWindow (reverseWindow a (firstindex a) (last - shift))
          (last - shift + 1) (lastindex a))
theorem property3756 : Property3756 := by unfold Property3756; intros; rfl

private def entry (line : Nat) (slug fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"abstractarraycov-line{line}-{slug}", juliaFile := "base/abstractarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.MapMut
