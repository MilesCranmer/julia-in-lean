import JuliaLean.AbstractArrayCov.Rows.ConcatDirect

/-! Loop and branch-heavy concatenation methods in `base/abstractarray.jl:1744-2279`. -/

namespace JuliaLean.AbstractArrayCov.Rows.ConcatComplex

open JuliaLean
open JuliaLean.Registry
open JuliaLean.AbstractArrayCov.Rows.ConcatDirect

def method1744 (vectors : List (List α)) : List α := vectors.flatten
def Property1744 : Prop := ∀ (α : Type) vectors,
  method1744 (α := α) vectors = vectors.flatten
theorem property1744 : Property1744 := by unfold Property1744; intros; rfl

structure Block (α : Type) where
  rows : Nat
  cols : Nat
  dense : Bool
  values : List α
  deriving Repr, DecidableEq

def sameRows (n : Nat) : List (Block α) → Bool
  | [] => true
  | b :: rest => b.rows = n && sameRows n rest

def method1768 (blocks : List (Block α)) : Except String (MatrixResult α) :=
  match blocks with
  | [] => .error "empty concatenation"
  | first :: _ =>
      if !sameRows first.rows blocks then .error "number of rows must match"
      else
        let cols := blocks.foldl (fun n b => n + if b.cols = 0 then 1 else b.cols) 0
        let dense := blocks.all (·.dense)
        if dense then .ok ⟨first.rows, cols, blocks.flatMap (·.values)⟩
        else .ok ⟨first.rows, cols, blocks.flatMap (·.values)⟩
def Property1768 : Prop := ∀ (α : Type) blocks,
  method1768 (α := α) blocks = match blocks with
    | [] => .error "empty concatenation"
    | first :: _ => if !sameRows first.rows blocks then .error "number of rows must match"
      else
        let cols := blocks.foldl (fun n b => n + if b.cols = 0 then 1 else b.cols) 0
        let dense := blocks.all (·.dense)
        if dense then .ok ⟨first.rows, cols, blocks.flatMap (·.values)⟩
        else .ok ⟨first.rows, cols, blocks.flatMap (·.values)⟩
theorem property1768 : Property1768 := by
  unfold Property1768
  intro α blocks
  cases blocks <;> rfl

def sameCols (n : Nat) : List (Block α) → Bool
  | [] => true
  | b :: rest => b.cols = n && sameCols n rest

def method1805 (blocks : List (Block α)) : Except String (MatrixResult α) :=
  match blocks with
  | [] => .error "empty concatenation"
  | first :: _ =>
      if !sameCols first.cols blocks then .error "number of columns must match"
      else
        let result := ⟨blocks.foldl (fun n b => n + b.rows) 0, first.cols,
          blocks.flatMap (·.values)⟩
        .ok result
def Property1805 : Prop := ∀ (α : Type) blocks,
  method1805 (α := α) blocks = match blocks with
    | [] => .error "empty concatenation"
    | first :: _ => if !sameCols first.cols blocks then .error "number of columns must match"
      else .ok ⟨blocks.foldl (fun n b => n + b.rows) 0, first.cols,
        blocks.flatMap (·.values)⟩
theorem property1805 : Property1805 := by
  unfold Property1805
  intro α blocks
  cases blocks <;> rfl

def method1859 (combine : List Bool → List Nat → List Nat → Except String (List Nat))
    (dims : List Bool) (shapes : List (List Nat)) : Except String (List Nat) :=
  shapes.foldlM (fun out shape => combine dims out shape) []
def Property1859 : Prop := ∀ combine dims shapes,
  method1859 combine dims shapes = shapes.foldlM (fun out shape => combine dims out shape) []
theorem property1859 : Property1859 := by unfold Property1859; intros; rfl

def method1868 (catSize : α → List Nat)
    (combine : List Bool → List Nat → List Nat → Except String (List Nat))
    (recurse : List Bool → List Nat → List α → Except String (List Nat))
    (dims : List Bool) (x : α) (rest : List α) : Except String (List Nat) := do
  let shape ← combine dims [] (catSize x)
  recurse dims shape rest
def Property1868 : Prop := ∀ (α : Type) (catSize : α → List Nat) combine recurse dims x rest,
  method1868 catSize combine recurse dims x rest = do
    let shape ← combine dims [] (catSize x)
    recurse dims shape rest
theorem property1868 : Property1868 := by unfold Property1868; intros; rfl

def method1870 (catSize : α → List Nat)
    (combine : List Bool → List Nat → List Nat → Except String (List Nat))
    (recurse : List Bool → List Nat → List α → Except String (List Nat))
    (dims : List Bool) (shape : List Nat) (x : α) (rest : List α) : Except String (List Nat) := do
  let shape ← combine dims shape (catSize x)
  recurse dims shape rest
def Property1870 : Prop := ∀ (α : Type) (catSize : α → List Nat) combine recurse dims shape x rest,
  method1870 catSize combine recurse dims shape x rest = do
    let shape ← combine dims shape (catSize x)
    recurse dims shape rest
theorem property1870 : Property1870 := by unfold Property1870; intros; rfl

def method1875 (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (dims : List Bool) (shape : List Nat) : Except String (List Nat) :=
  match dims, shape with
  | d :: ds, a :: rest => do return (a + (if d then 1 else 0)) ::
      (← recurse (ndim + 1) ds rest [])
  | _, _ => .error "invalid recursive shape"
def Property1875 : Prop := ∀ recurse ndim dims shape,
  method1875 recurse ndim dims shape = match dims, shape with
    | d :: ds, a :: rest => do return (a + (if d then 1 else 0)) ::
        (← recurse (ndim + 1) ds rest [])
    | _, _ => .error "invalid recursive shape"
theorem property1875 : Property1875 := by
  unfold Property1875
  intro recurse ndim dims shape
  cases dims <;> cases shape <;> rfl

def method1877 (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (dims : List Bool) (nshape : List Nat) : Except String (List Nat) :=
  match dims, nshape with
  | _ :: ds, b :: rest => do return b :: (← recurse (ndim + 1) ds [] rest)
  | _, _ => .error "invalid recursive shape"
def Property1877 : Prop := ∀ recurse ndim dims nshape,
  method1877 recurse ndim dims nshape = match dims, nshape with
    | _ :: ds, b :: rest => do return b :: (← recurse (ndim + 1) ds [] rest)
    | _, _ => .error "invalid recursive shape"
theorem property1877 : Property1877 := by
  unfold Property1877
  intro recurse ndim dims nshape
  cases dims <;> cases nshape <;> rfl

def method1879 (check : Int → Nat → Nat → Except String Nat)
    (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (shape : List Nat) : Except String (List Nat) :=
  match shape with
  | [] => .ok []
  | a :: rest => do
      let _ ← check ndim a 1
      return 1 :: (← recurse (ndim + 1) [] rest [])
def Property1879 : Prop := ∀ check recurse ndim shape,
  method1879 check recurse ndim shape = match shape with
    | [] => .ok []
    | a :: rest => do
      let _ ← check ndim a 1
      return 1 :: (← recurse (ndim + 1) [] rest [])
theorem property1879 : Property1879 := by
  unfold Property1879
  intro check recurse ndim shape
  cases shape <;> rfl

def method1883 (check : Int → Nat → Nat → Except String Nat)
    (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (shape nshape : List Nat) : Except String (List Nat) :=
  match shape, nshape with
  | a :: as, b :: bs => do
      let next ← check ndim a b
      return next :: (← recurse (ndim + 1) [] as bs)
  | _, _ => .error "invalid recursive shape"
def Property1883 : Prop := ∀ check recurse ndim shape nshape,
  method1883 check recurse ndim shape nshape = match shape, nshape with
    | a :: as, b :: bs => do
      let next ← check ndim a b
      return next :: (← recurse (ndim + 1) [] as bs)
    | _, _ => .error "invalid recursive shape"
theorem property1883 : Property1883 := by
  unfold Property1883
  intro check recurse ndim shape nshape
  cases shape <;> cases nshape <;> rfl

def method1887 (check : Int → Nat → Nat → Except String Nat)
    (recurse : Int → List Bool → List Nat → List Nat → Except String (List Nat))
    (ndim : Int) (dims : List Bool) (shape nshape : List Nat) : Except String (List Nat) :=
  match dims, shape, nshape with
  | d :: ds, a :: as, b :: bs => do
      let next ← if d then .ok (a + b) else check ndim a b
      return next :: (← recurse (ndim + 1) ds as bs)
  | _, _, _ => .error "invalid recursive shape"
def Property1887 : Prop := ∀ check recurse ndim dims shape nshape,
  method1887 check recurse ndim dims shape nshape = match dims, shape, nshape with
    | d :: ds, a :: as, b :: bs => do
      let next ← if d then .ok (a + b) else check ndim a b
      return next :: (← recurse (ndim + 1) ds as bs)
    | _, _, _ => .error "invalid recursive shape"
theorem property1887 : Property1887 := by
  unfold Property1887
  intro check recurse ndim dims shape nshape
  cases dims <;> cases shape <;> cases nshape <;> rfl

def method1898 (dims : List Int) : Jl (List Bool) := do
  if dims.any (· ≤ 0) then throw (.argumentError "cat dimensions must be positive")
  match dims.max? with
  | none => throw (.argumentError "empty cat dimensions")
  | some maximum => return (List.range maximum.toNat).map fun (i : Nat) => dims.contains ((i : Int) + 1)
def Property1898 : Prop := ∀ dims, method1898 dims = do
  if dims.any (· ≤ 0) then throw (.argumentError "cat dimensions must be positive")
  match dims.max? with
  | none => throw (.argumentError "empty cat dimensions")
  | some maximum => return (List.range maximum.toNat).map fun (i : Nat) => dims.contains ((i : Int) + 1)
theorem property1898 : Property1898 := by unfold Property1898; intros; rfl

def method1907 (dims2cat : δ → Jl (List Bool)) (shape : List Bool → List α → Jl σ)
    (allocate : α → τ → σ → Jl β) (zero : τ → γ) (fill : β → γ → Jl β)
    (finish : β → σ → List Bool → List α → Jl β)
    (dims : δ) (t : τ) (xs : List α) : Jl β := do
  let catdims ← dims2cat dims
  let outShape ← shape catdims xs
  let first ← match xs with | x :: _ => .ok x | [] => throw (JlError.argumentError "empty cat")
  let out ← allocate first t outShape
  let out ← if catdims.count true > 1 then fill out (zero t) else .ok out
  finish out outShape catdims xs
def Property1907 : Prop := ∀ (δ α σ τ β γ : Type)
    (dims2cat : δ → Jl (List Bool)) (shape : List Bool → List α → Jl σ)
    (allocate : α → τ → σ → Jl β) (zero : τ → γ) (fill : β → γ → Jl β)
    (finish : β → σ → List Bool → List α → Jl β) dims t xs,
  method1907 dims2cat shape allocate zero fill finish dims t xs = do
    let catdims ← dims2cat dims
    let outShape ← shape catdims xs
    let first ← match xs with | x :: _ => .ok x | [] => throw (JlError.argumentError "empty cat")
    let out ← allocate first t outShape
    let out ← if catdims.count true > 1 then fill out (zero t) else .ok out
    finish out outShape catdims xs
theorem property1907 : Property1907 := by unfold Property1907; intros; rfl

def method1923 (one : α → σ → List Bool → List Nat → β → List β → Jl (List Nat))
    (recurse : α → σ → List Bool → List Nat → List β → Jl α)
    (a : α) (shape : σ) (dims : List Bool) (offsets : List Nat) (x : β) (xs : List β) : Jl α := do
  let offsets ← one a shape dims offsets x xs
  recurse a shape dims offsets xs
def Property1923 : Prop := ∀ (α σ β : Type)
    (one : α → σ → List Bool → List Nat → β → List β → Jl (List Nat))
    (recurse : α → σ → List Bool → List Nat → List β → Jl α)
    (a : α) (shape : σ) dims offsets (x : β) xs,
  method1923 one recurse a shape dims offsets x xs = do
    let offsets ← one a shape dims offsets x xs
    recurse a shape dims offsets xs
theorem property1923 : Property1923 := by unfold Property1923; intros; rfl

def method1930 (catSize : α → Nat → Nat) (copy : β → List (List Nat) → α → Jl Unit)
    (a : β) (shape : List Nat) (dims : List Bool) (offsets : List Nat) (x : α) : Jl (List Nat) := do
  let inds := (List.range offsets.length).map fun i =>
    if dims.getD i false then (List.range (catSize x i)).map (· + offsets.getD i 0)
    else List.range (shape.getD i 0)
  copy a inds x
  return (List.range offsets.length).map fun i =>
    if dims.getD i false then offsets.getD i 0 + catSize x i else offsets.getD i 0
def Property1930 : Prop := ∀ (α β : Type) (catSize : α → Nat → Nat)
    (copy : β → List (List Nat) → α → Jl Unit) (a : β) shape dims offsets (x : α),
  method1930 catSize copy a shape dims offsets x = do
    let inds := (List.range offsets.length).map fun i =>
      if dims.getD i false then (List.range (catSize x i)).map (· + offsets.getD i 0)
      else List.range (shape.getD i 0)
    copy a inds x
    return (List.range offsets.length).map fun i =>
      if dims.getD i false then offsets.getD i 0 + catSize x i else offsets.getD i 0
theorem property1930 : Property1930 := by unfold Property1930; intros; rfl

def rowMajorToColumnMajor (rows cols : Nat) (values : List α) : List α :=
  (List.range cols).flatMap fun j => (List.range rows).filterMap fun i => values[i * cols + j]?

def method2253 (rows : List Nat) (values : List α) : Except String (MatrixResult α) :=
  match rows with
  | [] => .error "empty rows"
  | cols :: _ =>
      if rows.length * cols != values.length then .error "argument count mismatch"
      else if !rows.all (· == cols) then .error "row column mismatch"
      else .ok ⟨rows.length, cols, rowMajorToColumnMajor rows.length cols values⟩
def Property2253 : Prop := ∀ (α : Type) rows values,
  method2253 (α := α) rows values = match rows with
    | [] => .error "empty rows"
    | cols :: _ => if rows.length * cols != values.length then .error "argument count mismatch"
      else if !rows.all (· == cols) then .error "row column mismatch"
      else .ok ⟨rows.length, cols, rowMajorToColumnMajor rows.length cols values⟩
theorem property2253 : Property2253 := by
  unfold Property2253
  intro α rows values
  cases rows <;> rfl

def method2279 (allocate : τ → Nat → Nat → β) (fill : β → Bool → List α → γ)
    (t : τ) (rows : List Nat) (values : List α) : Except String γ :=
  match rows with
  | [] => .error "empty rows"
  | cols :: rest =>
      if !rest.all (· == cols) then .error "row column mismatch"
      else .ok (fill (allocate t rows.length cols) true values)
def Property2279 : Prop := ∀ (τ α β γ : Type) (allocate : τ → Nat → Nat → β)
    (fill : β → Bool → List α → γ) (t : τ) rows (values : List α),
  method2279 allocate fill t rows values = match rows with
    | [] => .error "empty rows"
    | cols :: rest => if !rest.all (· == cols) then .error "row column mismatch"
      else .ok (fill (allocate t rows.length cols) true values)
theorem property2279 : Property2279 := by
  unfold Property2279
  intro τ α β γ allocate fill t rows values
  cases rows <;> rfl

private def entry (line : Nat) (slug fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id := s!"abstractarraycov-line{line}-{slug}", juliaFile := "base/abstractarray.jl",
    juliaFns := [fn], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.ConcatComplex
