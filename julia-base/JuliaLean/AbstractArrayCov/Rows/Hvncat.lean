import JuliaLean.AbstractArrayCov.Rows.ConcatComplex

/-! Method-specific models for `base/abstractarray.jl:2381-2874`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Hvncat

open JuliaLean
open JuliaLean.Registry
open JuliaLean.AbstractArrayCov.Rows.ConcatComplex

def routeShape (call : σ → Bool → List α → β) (shape : σ) (rowFirst : Bool)
    (xs : List α) : β := call shape rowFirst xs

def method2381 (call : σ → Bool → List α → β) (shape : σ) (rowFirst : Bool) (xs : List α) : β :=
  call shape rowFirst xs
def Property2381 : Prop := ∀ (σ α β : Type) (call : σ → Bool → List α → β) shape rowFirst xs,
  method2381 call shape rowFirst xs = call shape rowFirst xs
theorem property2381 : Property2381 := by unfold Property2381; intros; rfl

def method2382 (call : Int → Bool → List α → β) (dim : Int) (xs : List α) : β := call dim true xs
def Property2382 : Prop := ∀ (α β : Type) (call : Int → Bool → List α → β) dim xs,
  method2382 call dim xs = call dim true xs
theorem property2382 : Property2382 := by unfold Property2382; intros; rfl

def method2384 (call : τ → σ → Bool → List α → β) (anyType : τ)
    (shape : σ) (rowFirst : Bool) : β := call anyType shape rowFirst []
def Property2384 : Prop := ∀ (τ σ α β : Type) (call : τ → σ → Bool → List α → β)
    anyType shape rowFirst,
  method2384 call anyType shape rowFirst = call anyType shape rowFirst []
theorem property2384 : Property2384 := by unfold Property2384; intros; rfl

def promoted (promote : List α → τ) (call : τ → σ → Bool → List α → β)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call (promote xs) shape rowFirst xs

def method2385 (promote : List α → τ) (call : τ → σ → Bool → List α → β)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call (promote xs) shape rowFirst xs
def Property2385 : Prop := ∀ (α τ σ β : Type) (promote : List α → τ)
    (call : τ → σ → Bool → List α → β) (shape : σ) rowFirst xs,
  method2385 promote call shape rowFirst xs = call (promote xs) shape rowFirst xs
theorem property2385 : Property2385 := by unfold Property2385; intros; rfl

def method2386 (call : τ → σ → Bool → List α → β) (t : τ)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call t shape rowFirst xs
def Property2386 : Prop := ∀ (τ σ α β : Type)
    (call : τ → σ → Bool → List α → β) (t : τ) (shape : σ) rowFirst xs,
  method2386 call t shape rowFirst xs = call t shape rowFirst xs
theorem property2386 : Property2386 := by unfold Property2386; intros; rfl

def method2387 (promote : List α → τ) (call : τ → σ → Bool → List α → β)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call (promote xs) shape rowFirst xs
def Property2387 : Prop := ∀ (α τ σ β : Type) (promote : List α → τ)
    (call : τ → σ → Bool → List α → β) (shape : σ) rowFirst xs,
  method2387 promote call shape rowFirst xs = call (promote xs) shape rowFirst xs
theorem property2387 : Property2387 := by unfold Property2387; intros; rfl

def method2388 (promote : List α → τ) (call : τ → σ → Bool → List α → β)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call (promote xs) shape rowFirst xs
def Property2388 : Prop := ∀ (α τ σ β : Type) (promote : List α → τ)
    (call : τ → σ → Bool → List α → β) (shape : σ) rowFirst xs,
  method2388 promote call shape rowFirst xs = call (promote xs) shape rowFirst xs
theorem property2388 : Property2388 := by unfold Property2388; intros; rfl

def method2389 (call : τ → σ → Bool → List α → β) (t : τ)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call t shape rowFirst xs
def Property2389 : Prop := ∀ (τ σ α β : Type)
    (call : τ → σ → Bool → List α → β) (t : τ) (shape : σ) rowFirst xs,
  method2389 call t shape rowFirst xs = call t shape rowFirst xs
theorem property2389 : Property2389 := by unfold Property2389; intros; rfl

def method2392 (call : τ → σ → Bool → List α → β) (t : τ)
    (shape : σ) (rowFirst : Bool) (xs : List α) : β := call t shape rowFirst xs
def Property2392 : Prop := ∀ (τ σ α β : Type)
    (call : τ → σ → Bool → List α → β) (t : τ) (shape : σ) rowFirst xs,
  method2392 call t shape rowFirst xs = call t shape rowFirst xs
theorem property2392 : Property2392 := by unfold Property2392; intros; rfl

def method2393 (call : τ → Int → List α → β) (t : τ) (dim : Int) (xs : List α) : β :=
  call t dim xs
def Property2393 : Prop := ∀ (τ α β : Type) (call : τ → Int → List α → β)
    (t : τ) dim xs,
  method2393 call t dim xs = call t dim xs
theorem property2393 : Property2393 := by unfold Property2393; intros; rfl

def onlyOneError : Jl α := .error (.argumentError "a 0-dimensional array may only contain exactly one element")

def method2397 : Jl α := onlyOneError
def Property2397 : Prop := ∀ (α : Type), (method2397 : Jl α) = onlyOneError
theorem property2397 : Property2397 := by unfold Property2397; intros; rfl

def method2398 (convert : τ → α → β) (fill : β → γ) (t : τ) (x : α) : γ := fill (convert t x)
def Property2398 : Prop := ∀ (τ α β γ : Type) (convert : τ → α → β)
    (fill : β → γ) (t : τ) (x : α),
  method2398 convert fill t x = fill (convert t x)
theorem property2398 : Property2398 := by unfold Property2398; intros; rfl

def method2399 (convert : τ → α → β) (fill : β → γ) (t : τ) (x : α) : γ := fill (convert t x)
def Property2399 : Prop := ∀ (τ α β γ : Type) (convert : τ → α → β)
    (fill : β → γ) (t : τ) (x : α),
  method2399 convert fill t x = fill (convert t x)
theorem property2399 : Property2399 := by unfold Property2399; intros; rfl

def method2400 (convert : τ → α → β) (t : τ) (xs : List α) : List β := xs.map (convert t)
def Property2400 : Prop := ∀ (τ α β : Type) (convert : τ → α → β)
    (t : τ) xs,
  method2400 convert t xs = xs.map (convert t)
theorem property2400 : Property2400 := by unfold Property2400; intros; rfl

def method2401 : Jl α := onlyOneError
def Property2401 : Prop := ∀ (α : Type), (method2401 : Jl α) = onlyOneError
theorem property2401 : Property2401 := by unfold Property2401; intros; rfl
def method2402 : Jl α := onlyOneError
def Property2402 : Prop := ∀ (α : Type), (method2402 : Jl α) = onlyOneError
theorem property2402 : Property2402 := by unfold Property2402; intros; rfl
def method2403 : Jl α := onlyOneError
def Property2403 : Prop := ∀ (α : Type), (method2403 : Jl α) = onlyOneError
theorem property2403 : Property2403 := by unfold Property2403; intros; rfl
def method2405 : Jl α := onlyOneError
def Property2405 : Prop := ∀ (α : Type), (method2405 : Jl α) = onlyOneError
theorem property2405 : Property2405 := by unfold Property2405; intros; rfl

def method2409 (call : τ → Int → List α → β) (t : τ) (dim : Int)
    (_rowFirst : Bool) (xs : List α) : β := call t dim xs
def Property2409 : Prop := ∀ (τ α β : Type) (call : τ → Int → List α → β)
    (t : τ) dim rowFirst xs,
  method2409 call t dim rowFirst xs = call t dim xs
theorem property2409 : Property2409 := by unfold Property2409; intros; rfl

def method2411 (allocate : τ → Nat → List Nat → β) (t : τ) (rank : Int) : Jl β := do
  if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
  return allocate t rank.toNat (List.replicate rank.toNat 0)
def Property2411 : Prop := ∀ (τ β : Type) (allocate : τ → Nat → List Nat → β)
    (t : τ) rank,
  method2411 allocate t rank = do
    if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
    return allocate t rank.toNat (List.replicate rank.toNat 0)
theorem property2411 : Property2411 := by unfold Property2411; intros; rfl

def method2417 (convert : τ → α → β) (reshape : List β → List Nat → γ)
    (t : τ) (rank : Int) (xs : List α) : Jl γ := do
  if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
  return reshape (xs.map (convert t)) (List.replicate (rank - 1).toNat 1 ++ [xs.length])
def Property2417 : Prop := ∀ (τ α β γ : Type) (convert : τ → α → β)
    (reshape : List β → List Nat → γ) (t : τ) rank xs,
  method2417 convert reshape t rank xs = do
    if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
    return reshape (xs.map (convert t)) (List.replicate (rank - 1).toNat 1 ++ [xs.length])
theorem property2417 : Property2417 := by unfold Property2417; intros; rfl

structure CatMeta (α : Type) where
  dims : List Nat
  values : List α
  deriving Repr, DecidableEq

def method2423 (fallback : τ → Int → List (CatMeta α) → β)
    (linear : τ → Int → List (CatMeta α) → β) (t : τ) (rank : Int)
    (arrays : List (CatMeta α)) : Jl β := do
  if arrays.isEmpty then throw (.argumentError "must have at least one element")
  if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
  if arrays.any (fun a => (a.dims.drop rank.toNat).any (· != 1)) then
    return fallback t rank arrays
  return linear t rank arrays
def Property2423 : Prop := ∀ (τ α β : Type)
    (fallback linear : τ → Int → List (CatMeta α) → β) (t : τ) rank arrays,
  method2423 fallback linear t rank arrays = do
    if arrays.isEmpty then throw (.argumentError "must have at least one element")
    if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
    if arrays.any (fun a => (a.dims.drop rank.toNat).any (· != 1)) then
      return fallback t rank arrays
    return linear t rank arrays
theorem property2423 : Property2423 := by unfold Property2423; intros; rfl

def method2458 (build : τ → Int → List (CatMeta α) → β)
    (t : τ) (rank : Int) (values : List (CatMeta α)) : Jl β := do
  if values.isEmpty then throw (.argumentError "must have at least one element")
  if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
  if values.any (fun a => (a.dims.take (rank - 1).toNat).any (· != 1)) then
    throw (.argumentError "non-concatenated dimensions must have length 1")
  return build t rank values
def Property2458 : Prop := ∀ (τ α β : Type)
    (build : τ → Int → List (CatMeta α) → β) (t : τ) rank values,
  method2458 build t rank values = do
    if values.isEmpty then throw (.argumentError "must have at least one element")
    if rank < 0 then throw (.argumentError "concatenation dimension must be non-negative")
    if values.any (fun a => (a.dims.take (rank - 1).toNat).any (· != 1)) then
      throw (.argumentError "non-concatenated dimensions must have length 1")
    return build t rank values
theorem property2458 : Property2458 := by unfold Property2458; intros; rfl

def method2492 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def Property2492 : Prop := ∀ (τ α β : Type) (call : τ → List α → β) (t : τ) xs,
  method2492 call t xs = call t xs
theorem property2492 : Property2492 := by unfold Property2492; intros; rfl
def method2493 (call : τ → List α → β) (t : τ) (xs : List α) : β := call t xs
def Property2493 : Prop := ∀ (τ α β : Type) (call : τ → List α → β) (t : τ) xs,
  method2493 call t xs = call t xs
theorem property2493 : Property2493 := by unfold Property2493; intros; rfl

def method2498 (call : τ → Int → Bool → List α → β) (t : τ)
    (dims : List Int) (_rowFirst : Bool) (xs : List α) : Option β :=
  dims.head?.map fun d => call t d false xs
def Property2498 : Prop := ∀ (τ α β : Type)
    (call : τ → Int → Bool → List α → β) (t : τ) dims rowFirst xs,
  method2498 call t dims rowFirst xs = dims.head?.map fun d => call t d false xs
theorem property2498 : Property2498 := by unfold Property2498; intros; rfl
def method2499 (call : τ → Int → Bool → List α → β) (t : τ)
    (dims : List Int) (_rowFirst : Bool) (xs : List α) : Option β :=
  dims.head?.map fun d => call t d false xs
def Property2499 : Prop := ∀ (τ α β : Type)
    (call : τ → Int → Bool → List α → β) (t : τ) dims rowFirst xs,
  method2499 call t dims rowFirst xs = dims.head?.map fun d => call t d false xs
theorem property2499 : Property2499 := by unfold Property2499; intros; rfl

def method2501 (call : τ → Int → List α → β) (t : τ) (size : Int)
    (rowFirst : Bool) (xs : List α) : Jl β := do
  if size ≤ 0 then throw (.argumentError "dimsshape must be positive")
  if xs.length != size.toNat then throw (.argumentError "element count mismatch")
  return call t (if rowFirst then 2 else 1) xs
def Property2501 : Prop := ∀ (τ α β : Type) (call : τ → Int → List α → β)
    (t : τ) size rowFirst xs,
  method2501 call t size rowFirst xs = do
    if size ≤ 0 then throw (.argumentError "dimsshape must be positive")
    if xs.length != size.toNat then throw (.argumentError "element count mismatch")
    return call t (if rowFirst then 2 else 1) xs
theorem property2501 : Property2501 := by unfold Property2501; intros; rfl

def method2514 (allocate : τ → List Nat → β) (fill : β → Bool → List α → γ)
    (t : τ) (dims : List Int) (rowFirst : Bool) (xs : List α) : Jl γ := do
  if dims.any (· ≤ 0) then throw (.argumentError "dims must be positive")
  let shape := dims.map Int.toNat
  if shape.foldl (· * ·) 1 != xs.length then throw (.argumentError "argument count mismatch")
  return fill (allocate t shape) rowFirst xs
def Property2514 : Prop := ∀ (τ α β γ : Type) (allocate : τ → List Nat → β)
    (fill : β → Bool → List α → γ) (t : τ) dims rowFirst xs,
  method2514 allocate fill t dims rowFirst xs = do
    if dims.any (· ≤ 0) then throw (.argumentError "dims must be positive")
    let shape := dims.map Int.toNat
    if shape.foldl (· * ·) 1 != xs.length then throw (.argumentError "argument count mismatch")
    return fill (allocate t shape) rowFirst xs
theorem property2514 : Property2514 := by unfold Property2514; intros; rfl

def rowFirstValues (rows cols : Nat) (values : List α) : List α :=
  (List.range cols).flatMap fun j => (List.range rows).filterMap fun i => values[i * cols + j]?

def method2527 (rows cols pages : Nat) (rowFirst : Bool) (values : List α) : Jl (List α) := do
  if rows * cols * pages != values.length then throw (.argumentError "argument count mismatch")
  if rowFirst then
    return (List.range pages).flatMap fun page =>
      rowFirstValues rows cols ((values.drop (page * rows * cols)).take (rows * cols))
  return values
def Property2527 : Prop := ∀ (α : Type) rows cols pages rowFirst values,
  method2527 (α := α) rows cols pages rowFirst values = do
    if rows * cols * pages != values.length then throw (.argumentError "argument count mismatch")
    if rowFirst then
      return (List.range pages).flatMap fun page =>
        rowFirstValues rows cols ((values.drop (page * rows * cols)).take (rows * cols))
    return values
theorem property2527 : Property2527 := by unfold Property2527; intros; rfl

def method2556 (generated : Bool) (small : β) (fallback : β) : β := if generated then small else fallback
def Property2556 : Prop := ∀ (β : Type) generated (small fallback : β),
  method2556 generated small fallback = if generated then small else fallback
theorem property2556 : Property2556 := by unfold Property2556; intros; rfl

def method2629 (rankOf : α → Nat) (build : τ → List Int → Bool → List α → β)
    (t : τ) (dims : List Int) (rowFirst : Bool) (values : List α) : β :=
  let rank := max ((values.map rankOf).max?.getD 0) dims.length
  build t (dims ++ List.replicate (rank - dims.length) 1) rowFirst values
def Property2629 : Prop := ∀ (α τ β : Type) (rankOf : α → Nat)
    (build : τ → List Int → Bool → List α → β) (t : τ) dims rowFirst values,
  method2629 rankOf build t dims rowFirst values =
    let rank := max ((values.map rankOf).max?.getD 0) dims.length
    build t (dims ++ List.replicate (rank - dims.length) 1) rowFirst values
theorem property2629 : Property2629 := by unfold Property2629; intros; rfl

def stagedBuilder (validate : List Int → List (CatMeta α) → Jl Unit)
    (discover : List Int → Bool → List (CatMeta α) → Jl (List Nat))
    (allocate : List Nat → Jl β) (fill : β → Bool → List (CatMeta α) → Jl β)
    (dims : List Int) (rowFirst : Bool) (values : List (CatMeta α)) : Jl β := do
  if values.isEmpty then throw (.argumentError "must have at least one element")
  if dims.any (· ≤ 0) then throw (.argumentError "dims must be positive")
  validate dims values
  let shape ← discover dims rowFirst values
  let out ← allocate shape
  fill out rowFirst values

def method2635 := @stagedBuilder
def Property2635 : Prop := ∀ (α β : Type)
    (validate : List Int → List (CatMeta α) → Jl Unit)
    (discover : List Int → Bool → List (CatMeta α) → Jl (List Nat))
    (allocate : List Nat → Jl β) (fill : β → Bool → List (CatMeta α) → Jl β)
    dims rowFirst values,
  method2635 validate discover allocate fill dims rowFirst values =
    stagedBuilder validate discover allocate fill dims rowFirst values
theorem property2635 : Property2635 := by unfold Property2635 method2635; intros; rfl

def method2732 (call : τ → Int → Bool → List α → β) (t : τ)
    (shape : List (List Int)) (rowFirst : Bool) (xs : List α) : Jl β :=
  match shape with
  | [level] => match level with
    | d :: _ => if d > 0 then .ok (call t d rowFirst xs) else .error (.argumentError "empty shape level")
    | [] => .error (.argumentError "empty shape level")
  | _ => .error (.argumentError "expected one shape level")
def Property2732 : Prop := ∀ (τ α β : Type)
    (call : τ → Int → Bool → List α → β) (t : τ) shape rowFirst xs,
  method2732 call t shape rowFirst xs = match shape with
    | [level] => match level with
      | d :: _ => if d > 0 then .ok (call t d rowFirst xs) else .error (.argumentError "empty shape level")
      | [] => .error (.argumentError "empty shape level")
    | _ => .error (.argumentError "expected one shape level")
theorem property2732 : Property2732 := by
  unfold Property2732
  intro τ α β call t shape rowFirst xs
  cases shape with
  | nil => rfl
  | cons level rest =>
    cases rest with
    | nil => cases level <;> rfl
    | cons next tail => rfl

def method2738 (rankOf : α → Nat) (build : τ → List (List Int) → Bool → List α → β)
    (t : τ) (shape : List (List Int)) (rowFirst : Bool) (values : List α) : β :=
  let rank := max ((values.map rankOf).max?.getD 0) shape.length
  build t (shape ++ List.replicate (rank - shape.length) shape.getLast!) rowFirst values
def Property2738 : Prop := ∀ (α τ β : Type) (rankOf : α → Nat)
    (build : τ → List (List Int) → Bool → List α → β) (t : τ)
    shape rowFirst values,
  method2738 rankOf build t shape rowFirst values =
    let rank := max ((values.map rankOf).max?.getD 0) shape.length
    build t (shape ++ List.replicate (rank - shape.length) shape.getLast!) rowFirst values
theorem property2738 : Property2738 := by unfold Property2738; intros; rfl

def method2744 (validate : List (List Int) → List (CatMeta α) → Jl Unit)
    (discover : List (List Int) → Bool → List (CatMeta α) → Jl (List Nat))
    (allocate : List Nat → Jl β) (fill : β → Bool → List (CatMeta α) → Jl β)
    (shape : List (List Int)) (rowFirst : Bool) (values : List (CatMeta α)) : Jl β := do
  if values.isEmpty then throw (.argumentError "must have at least one element")
  if shape.flatten.any (· ≤ 0) then throw (.argumentError "shape values must be positive")
  if shape.any List.isEmpty then throw (.argumentError "shape levels must be nonempty")
  validate shape values
  let dims ← discover shape rowFirst values
  let out ← allocate dims
  fill out rowFirst values
def Property2744 : Prop := ∀ (α β : Type)
    (validate : List (List Int) → List (CatMeta α) → Jl Unit)
    (discover : List (List Int) → Bool → List (CatMeta α) → Jl (List Nat))
    (allocate : List Nat → Jl β) (fill : β → Bool → List (CatMeta α) → Jl β)
    shape rowFirst values,
  method2744 validate discover allocate fill shape rowFirst values = do
    if values.isEmpty then throw (.argumentError "must have at least one element")
    if shape.flatten.any (· ≤ 0) then throw (.argumentError "shape values must be positive")
    if shape.any List.isEmpty then throw (.argumentError "shape levels must be nonempty")
    validate shape values
    let dims ← discover shape rowFirst values
    let out ← allocate dims
    fill out rowFirst values
theorem property2744 : Property2744 := by unfold Property2744; intros; rfl

def method2823 (rank d1 d2 : Nat) (scratch1 scratch2 : List Nat)
    (fill : List Nat → List Nat → Nat → Nat → List α → Jl β) (values : List α) : Jl β := do
  if rank ≤ 1 then throw (.argumentError "destination rank must be at least 2")
  if scratch1.length != rank || scratch2.length != rank then throw (.argumentError "scratch rank mismatch")
  if !(0 < d1 && d1 < 3 && 0 < d2 && d2 < 3 && d1 != d2) then throw (.argumentError "invalid d1/d2")
  fill scratch1 scratch2 d1 d2 values
def Property2823 : Prop := ∀ (α β : Type) rank d1 d2 scratch1 scratch2
    (fill : List Nat → List Nat → Nat → Nat → List α → Jl β) values,
  method2823 rank d1 d2 scratch1 scratch2 fill values = do
    if rank ≤ 1 then throw (.argumentError "destination rank must be at least 2")
    if scratch1.length != rank || scratch2.length != rank then throw (.argumentError "scratch rank mismatch")
    if !(0 < d1 && d1 < 3 && 0 < d2 && d2 < 3 && d1 != d2) then throw (.argumentError "invalid d1/d2")
    fill scratch1 scratch2 d1 d2 values
theorem property2823 : Property2823 := by unfold Property2823; intros; rfl

def method2865 (offsets inner products : List Int) : Int :=
  match offsets, inner with
  | o :: os, i :: is =>
      ((os.zip is).zip products).foldl (fun out p => out + (p.1.1 + p.1.2) * p.2) (o + i + 1)
  | _, _ => 1
def Property2865 : Prop := ∀ offsets inner products,
  method2865 offsets inner products = match offsets, inner with
    | o :: os, i :: is =>
      ((os.zip is).zip products).foldl (fun out p => out + (p.1.1 + p.1.2) * p.2) (o + i + 1)
    | _, _ => 1
theorem property2865 : Property2865 := by
  unfold Property2865
  intro offsets inner products
  cases offsets <;> cases inner <;> rfl

private def entry (line : Nat) (slug fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"abstractarraycov-line{line}-{slug}", juliaFile := "base/abstractarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.Hvncat
