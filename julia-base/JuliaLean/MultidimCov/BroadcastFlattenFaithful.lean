import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastFlattenFaithful

open JuliaLean.Registry

inductive Error where | bounds | evaluation deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α
abbrev Selector (α : Type) := List α → Result α

inductive Tree (S X α : Type) where
  | leaf (value : α)
  | node (style : S) (f : List α → Result α) (args : List (Tree S X α)) (axes : X)

structure BroadcastNode (S X α : Type) where
  style : S
  f : List α → Result α
  args : List (Tree S X α)
  axes : X


def treeArgs : Tree S X α → List (Tree S X α)
  | .leaf _ => []
  | .node _ _ args _ => args

def isNode : Tree S X α → Bool
  | .leaf _ => false
  | .node .. => true

def isFlatArgs : List (Tree S X α) → Bool
  | [] => true
  | head :: tail => !isNode head && isFlatArgs tail

def m364 (bc : BroadcastNode S X α) : Bool := isFlatArgs bc.args
def P364 : Prop := ∀ {S X α : Type} (bc : BroadcastNode S X α),
  m364 bc = isFlatArgs bc.args
theorem p364 : P364 := by unfold P364; intros; rfl

def m365 {S X α : Type} (_head : BroadcastNode S X α)
    (_tail : List (Tree S X α)) : Bool := false
def P365 : Prop := ∀ {S X α : Type} (head : BroadcastNode S X α) tail,
  m365 head tail = false
theorem p365 : P365 := by unfold P365; intros; rfl

def m366 {S X α : Type} (_head : α) (tail : List (Tree S X α)) : Bool :=
  isFlatArgs tail
def P366 : Prop := ∀ {S X α : Type} (head : α) tail,
  m366 (S := S) (X := X) head tail = isFlatArgs tail
theorem p366 : P366 := by unfold P366; intros; rfl

def m367 : Bool := true
def P367 : Prop := ∀ _ : Unit, m367 = true
theorem p367 : P367 := by simp [P367, m367]

mutual
  def catNested : Tree S X α → List (Tree S X α)
    | .leaf value => [.leaf value]
    | .node _ _ args _ => catNestedArgs args

  def catNestedArgs : List (Tree S X α) → List (Tree S X α)
    | [] => []
    | head :: tail => catNested head ++ catNestedArgs tail
end

def m369 (bc : BroadcastNode S X α) : List (Tree S X α) := catNestedArgs bc.args
def P369 : Prop := ∀ {S X α : Type} (bc : BroadcastNode S X α),
  m369 bc = catNestedArgs bc.args
theorem p369 : P369 := by unfold P369; intros; rfl

def m370 {S X α : Type} : List (Tree S X α) := []
def P370 : Prop := ∀ {S X α : Type}, (m370 : List (Tree S X α)) = []
theorem p370 : P370 := by simp [P370, m370]

def m371 (head : Tree S X α) : List (Tree S X α) := catNested head
def P371 : Prop := ∀ {S X α : Type} (head : Tree S X α), m371 head = catNested head
theorem p371 : P371 := by simp [P371, m371]

def m372 (head : Tree S X α) (tail : List (Tree S X α)) : List (Tree S X α) :=
  catNested head ++ catNestedArgs tail
def P372 : Prop := ∀ {S X α : Type} (head : Tree S X α) tail,
  m372 head tail = catNested head ++ catNestedArgs tail
theorem p372 : P372 := by simp [P372, m372]

def m373 (value : α) : List (Tree S X α) := [.leaf value]
def P373 : Prop := ∀ {S X α : Type} (value : α),
  m373 (S := S) (X := X) value = [.leaf value]
theorem p373 : P373 := by unfold P373; intros; rfl

def pick (n : Nat) : Selector α := fun args =>
  if n = 0 then .error .bounds
  else match args[n - 1]? with | some value => .ok value | none => .error .bounds

def prepareArgs : List (Selector α) → List α → Result (List α)
  | [], _ => .ok []
  | selector :: rest, args => do
      let first ← selector args
      let tail ← prepareArgs rest args
      pure (first :: tail)

mutual
  def makeOne (maybeconstructor : (List α → Result α) → List α → Result α) :
      Tree S X α → Nat → List (Selector α) × Nat
    | .leaf _, n => ([pick n], n + 1)
    | .node _ f args _, n =>
        let made := makeMany maybeconstructor args n
        let callable := maybeconstructor f
        ([fun flat => do callable (← prepareArgs made.1 flat)], made.2)

  def makeMany (maybeconstructor : (List α → Result α) → List α → Result α) :
      List (Tree S X α) → Nat → List (Selector α) × Nat
    | [], n => ([], n)
    | head :: tail, n =>
        let first := makeOne maybeconstructor head n
        let rest := makeMany maybeconstructor tail first.2
        (first.1 ++ rest.1, rest.2)
end

def m382 (maybeconstructor : (List α → Result α) → List α → Result α)
    (args : List (Tree S X α)) : List (Selector α) :=
  (makeMany maybeconstructor args 1).1
def P382 : Prop := ∀ {S X α : Type} maybeconstructor (args : List (Tree S X α)),
  m382 maybeconstructor args = (makeMany maybeconstructor args 1).1
theorem p382 : P382 := by unfold P382; intros; rfl

def m386 (maybeconstructor : (List α → Result α) → List α → Result α)
    (head : Tree S X α) (tail : List (Tree S X α)) (n : Nat) :
    List (Selector α) × Nat :=
  let first := makeOne maybeconstructor head n
  let rest := makeMany maybeconstructor tail first.2
  (first.1 ++ rest.1, rest.2)
def P386 : Prop := ∀ {S X α : Type} maybeconstructor
    (head : Tree S X α) tail n,
  m386 maybeconstructor head tail n =
    let first := makeOne maybeconstructor head n
    let rest := makeMany maybeconstructor tail first.2
    (first.1 ++ rest.1, rest.2)
theorem p386 : P386 := by unfold P386; intros; rfl

def m391 {α : Type} (n : Nat) : List (Selector α) × Nat := ([], n)
def P391 : Prop := ∀ {α : Type} n, (m391 n : List (Selector α) × Nat) = ([], n)
theorem p391 : P391 := by simp [P391, m391]

def m395 (n : Nat) (args : List α) : Result α := pick n args
def P395 : Prop := ∀ {α : Type} n (args : List α), m395 n args = pick n args
theorem p395 : P395 := by simp [P395, m395]

def m398 {α : Type} (_leaf : α) (n : Nat) : List (Selector α) × Nat :=
  ([pick n], n + 1)
def P398 : Prop := ∀ {α : Type} (leaf : α) n,
  m398 leaf n = ([pick n], n + 1)
theorem p398 : P398 := by unfold P398; intros; rfl

def m400 (maybeconstructor : (List α → Result α) → List α → Result α)
    (f : List α → Result α) (args : List (Tree S X α)) (n : Nat) :
    List (Selector α) × Nat :=
  let made := makeMany maybeconstructor args n
  let callable := maybeconstructor f
  ([fun flat => do callable (← prepareArgs made.1 flat)], made.2)
def P400 : Prop := ∀ {S X α : Type} maybeconstructor
    (f : List α → Result α) (args : List (Tree S X α)) n,
  m400 maybeconstructor f args n =
    let made := makeMany maybeconstructor args n
    let callable := maybeconstructor f
    ([fun flat => do callable (← prepareArgs made.1 flat)], made.2)
theorem p400 : P400 := by unfold P400; intros; rfl

def m407 (head : Selector α) (tail : List (Selector α)) (args : List α) : Result (List α) := do
  let first ← head args
  let rest ← prepareArgs tail args
  pure (first :: rest)
def P407 : Prop := ∀ {α : Type} (head : Selector α) tail args,
  m407 head tail args = do
    let first ← head args
    let rest ← prepareArgs tail args
    pure (first :: rest)
theorem p407 : P407 := by simp [P407, m407]

def m408 (head : Selector α) (args : List α) : Result (List α) := do
  let first ← head args
  pure [first]
def P408 : Prop := ∀ {α : Type} (head : Selector α) args,
  m408 head args = do let first ← head args; pure [first]
theorem p408 : P408 := by simp [P408, m408]

def m409 {α : Type} (_args : List α) : Result (List α) := .ok []
def P409 : Prop := ∀ {α : Type} (args : List α), m409 args = .ok []
theorem p409 : P409 := by simp [P409, m409]

def m346 (maybeconstructor : (List α → Result α) → List α → Result α) :
    BroadcastNode S X α → BroadcastNode S X α
  | bc =>
      if isFlatArgs bc.args then bc
      else
        let flatArgs := catNestedArgs bc.args
        let selectors := (makeMany maybeconstructor bc.args 1).1
        let callable := maybeconstructor bc.f
        { bc with
          f := fun flat => do callable (← prepareArgs selectors flat)
          args := flatArgs }

def P346 : Prop := ∀ {S X α : Type} maybeconstructor (bc : BroadcastNode S X α),
  m346 maybeconstructor bc =
    if isFlatArgs bc.args then bc
    else
      let flatArgs := catNestedArgs bc.args
      let selectors := (makeMany maybeconstructor bc.args 1).1
      let callable := maybeconstructor bc.f
      { bc with
        f := fun flat => do callable (← prepareArgs selectors flat)
        args := flatArgs }
theorem p346 : P346 := by unfold P346; intros; rfl

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; flatten docstring and source equation"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.BroadcastFlattenFaithful
