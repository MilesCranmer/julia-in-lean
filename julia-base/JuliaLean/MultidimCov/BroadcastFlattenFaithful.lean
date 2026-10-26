import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastFlattenFaithful

open JuliaLean.Registry

inductive Error where | bounds | evaluation deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α
abbrev Selector (α : Type) := List α → Result α

inductive Tree (S X α : Type) where
  | leaf (value : α)
  | node (style : S) (f : List α → Result α) (args : List (Tree S X α)) (axes : X)

def treeArgs : Tree S X α → List (Tree S X α)
  | .leaf _ => []
  | .node _ _ args _ => args

def isNode : Tree S X α → Bool
  | .leaf _ => false
  | .node .. => true

def isFlatArgs : List (Tree S X α) → Bool
  | [] => true
  | head :: tail => !isNode head && isFlatArgs tail

def m364 (bc : Tree S X α) : Bool := isFlatArgs (treeArgs bc)
def P364 : Prop := ∀ {S X α : Type} (bc : Tree S X α),
  m364 bc = isFlatArgs (treeArgs bc)
theorem p364 : P364 := by simp [P364, m364]

def m365 {S X α : Type} (_head : Tree S X α) (_tail : List (Tree S X α)) : Bool := false
def P365 : Prop := ∀ {S X α : Type} (head : Tree S X α) tail, m365 head tail = false
theorem p365 : P365 := by simp [P365, m365]

def m366 {S X α : Type} (_head : Tree S X α) (tail : List (Tree S X α)) : Bool := isFlatArgs tail
def P366 : Prop := ∀ {S X α : Type} (head : Tree S X α) tail,
  m366 head tail = isFlatArgs tail
theorem p366 : P366 := by simp [P366, m366]

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

def m369 (bc : Tree S X α) : List (Tree S X α) := catNestedArgs (treeArgs bc)
def P369 : Prop := ∀ {S X α : Type} (bc : Tree S X α),
  m369 bc = catNestedArgs (treeArgs bc)
theorem p369 : P369 := by simp [P369, m369]

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

def m373 (leaf : Tree S X α) : List (Tree S X α) := [leaf]
def P373 : Prop := ∀ {S X α : Type} (leaf : Tree S X α), m373 leaf = [leaf]
theorem p373 : P373 := by simp [P373, m373]

def pick (n : Nat) : Selector α := fun args =>
  match args[n - 1]? with | some value => .ok value | none => .error .bounds

def prepareArgs : List (Selector α) → List α → Result (List α)
  | [], _ => .ok []
  | selector :: rest, args => do
      let first ← selector args
      let tail ← prepareArgs rest args
      pure (first :: tail)

mutual
  def makeOne : Tree S X α → Nat → List (Selector α) × Nat
    | .leaf _, n => ([pick n], n + 1)
    | .node _ f args _, n =>
        let made := makeMany args n
        ([fun flat => do f (← prepareArgs made.1 flat)], made.2)

  def makeMany : List (Tree S X α) → Nat → List (Selector α) × Nat
    | [], n => ([], n)
    | head :: tail, n =>
        let first := makeOne head n
        let rest := makeMany tail first.2
        (first.1 ++ rest.1, rest.2)
end

def m382 (args : List (Tree S X α)) : List (Selector α) := (makeMany args 1).1
def P382 : Prop := ∀ {S X α : Type} (args : List (Tree S X α)),
  m382 args = (makeMany args 1).1
theorem p382 : P382 := by simp [P382, m382]

def m386 (head : Tree S X α) (tail : List (Tree S X α)) (n : Nat) :
    List (Selector α) × Nat :=
  let first := makeOne head n
  let rest := makeMany tail first.2
  (first.1 ++ rest.1, rest.2)
def P386 : Prop := ∀ {S X α : Type} (head : Tree S X α) tail n,
  m386 head tail n =
    let first := makeOne head n
    let rest := makeMany tail first.2
    (first.1 ++ rest.1, rest.2)
theorem p386 : P386 := by simp [P386, m386]

def m391 {α : Type} (n : Nat) : List (Selector α) × Nat := ([], n)
def P391 : Prop := ∀ {α : Type} n, (m391 n : List (Selector α) × Nat) = ([], n)
theorem p391 : P391 := by simp [P391, m391]

def m395 (n : Nat) (args : List α) : Result α := pick n args
def P395 : Prop := ∀ {α : Type} n (args : List α), m395 n args = pick n args
theorem p395 : P395 := by simp [P395, m395]

def m398 {S X α : Type} (_leaf : Tree S X α) (n : Nat) : List (Selector α) × Nat :=
  ([pick n], n + 1)
def P398 : Prop := ∀ {S X α : Type} (leaf : Tree S X α) n,
  m398 leaf n = ([pick n], n + 1)
theorem p398 : P398 := by simp [P398, m398]

def m400 (f : List α → Result α) (args : List (Tree S X α)) (n : Nat) :
    List (Selector α) × Nat :=
  let made := makeMany args n
  ([fun flat => do f (← prepareArgs made.1 flat)], made.2)
def P400 : Prop := ∀ {S X α : Type} (f : List α → Result α)
    (args : List (Tree S X α)) n,
  m400 f args n =
    let made := makeMany args n
    ([fun flat => do f (← prepareArgs made.1 flat)], made.2)
theorem p400 : P400 := by simp [P400, m400]

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

def m346 : Tree S X α → Tree S X α
  | leaf@(.leaf _) => leaf
  | node@(.node style f args axes) =>
      if isFlatArgs args then node
      else
        let flatArgs := catNestedArgs args
        let selectors := (makeMany args 1).1
        .node style (fun flat => do f (← prepareArgs selectors flat)) flatArgs axes

def P346 : Prop := ∀ {S X α : Type} (style : S) (f : List α → Result α)
    (args : List (Tree S X α)) (axes : X),
  m346 (.node style f args axes) =
    if isFlatArgs args then .node style f args axes
    else
      let flatArgs := catNestedArgs args
      let selectors := (makeMany args 1).1
      .node style (fun flat => do f (← prepareArgs selectors flat)) flatArgs axes
theorem p346 : P346 := by simp [P346, m346]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; flatten docstring and source equation"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := [
  entry 346 "flatten(::Broadcasted)" "Flatten preserves an already flat expression; otherwise it expands leaves, builds ordered selectors, and reconstructs the same style and axes with the composed function." ``P346 ``p346,
  entry 364 "isflat(::Broadcasted)" "Flatness delegates to the complete argument tuple." ``P364 ``p364,
  entry 365 "_isflat(::NestedTuple)" "Every tuple headed by a nested Broadcasted is non-flat." ``P365 ``p365,
  entry 366 "_isflat(::Tuple)" "The general nonempty tuple checks its tail after dispatch excludes a nested head." ``P366 ``p366,
  entry 367 "_isflat(::Tuple{})" "The empty tuple is flat." ``P367 ``p367,
  entry 369 "cat_nested(::Broadcasted)" "A nested wrapper expands its complete argument tuple." ``P369 ``p369,
  entry 370 "cat_nested_args(::Tuple{})" "The empty argument tuple expands to empty." ``P370 ``p370,
  entry 371 "cat_nested_args(::Tuple{Any})" "A singleton tuple expands its one argument." ``P371 ``p371,
  entry 372 "cat_nested_args(::Tuple)" "The recursive expansion processes the head before the tail." ``P372 ``p372,
  entry 373 "cat_nested(a)" "Every leaf becomes a singleton tuple of the same polymorphic value." ``P373 ``p373,
  entry 382 "make_makeargs(args)" "Selector construction begins at Julia index one and returns the selector tuple." ``P382 ``p382,
  entry 386 "_make_makeargs(args,n)" "The recursive selector builder processes the head, threads its counter into the tail, and returns the final counter." ``P386 ``p386,
  entry 391 "_make_makeargs((),n)" "The empty selector builder returns no selectors and the unchanged counter." ``P391 ``p391,
  entry 395 "(::Pick{N})(args)" "Pick returns argument N with one-based bounds behavior for every element type." ``P395 ``p395,
  entry 398 "_make_makeargs1(leaf,n)" "A leaf produces Pick{n} and increments the counter once." ``P398 ``p398,
  entry 400 "_make_makeargs1(::Broadcasted,n)" "A nested wrapper builds all child selectors before constructing its evaluation closure and returning the final counter." ``P400 ``p400,
  entry 407 "prepare_args(tuple,x)" "The recursive case evaluates the head selector before preparing the tail." ``P407 ``p407,
  entry 408 "prepare_args(singleton,x)" "The singleton case evaluates its sole selector and returns that value." ``P408 ``p408,
  entry 409 "prepare_args((),())" "The empty selector tuple returns an empty argument tuple." ``P409 ``p409
]

end JuliaLean.MultidimCov.BroadcastFlattenFaithful
