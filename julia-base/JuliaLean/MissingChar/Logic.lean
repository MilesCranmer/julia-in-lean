import JuliaLean.MissingChar.Basic

/-!
# `missing` semantics: three-valued logic, comparisons, `isless`, `isequal`

Model of the `Missing` methods of `base/missing.jl` and the generic operator
fallbacks of `base/operators.jl` they combine with (master `bbfa0ce4150`).

A Julia value that may be `missing` is `Option α`: `none` is `missing`, `some a`
is an ordinary value `a`. The methods for ordinary values (`==`, `<`, `isless`,
`isequal` on two non-missing arguments) are parameters, so every statement
holds for every type of non-missing values.
-/

namespace JuliaLean.MissingChar

/-! ## Three-valued logic, `base/missing.jl:157-171`, `base/bool.jl` -/

/-- `!x`: `!(::Missing) = missing` (`base/missing.jl:96-103`), `!b` for Bool. -/
def not3 : Option Bool → Option Bool
  | none => none
  | some b => some (!b)

/-- `a & b` on `Union{Bool, Missing}`, `base/missing.jl:157-159`:
`(&)(::Missing, ::Missing) = missing`, `(&)(a::Missing, b::Bool) = ifelse(b, missing, false)`,
`(&)(b::Bool, a::Missing) = ifelse(b, missing, false)`; Bool `&` otherwise. -/
def and3 : Option Bool → Option Bool → Option Bool
  | none, none => none
  | none, some b => if b then none else some false
  | some b, none => if b then none else some false
  | some a, some b => some (a && b)

/-- `a | b`, `base/missing.jl:162-164`: `ifelse(b, true, missing)` with one missing. -/
def or3 : Option Bool → Option Bool → Option Bool
  | none, none => none
  | none, some b => if b then some true else none
  | some b, none => if b then some true else none
  | some a, some b => some (a || b)

/-- `xor(a, b)`, `base/missing.jl:167-169`: missing whenever an argument is. -/
def xor3 : Option Bool → Option Bool → Option Bool
  | none, _ => none
  | _, none => none
  | some a, some b => some (a ^^ b)

/-- `nand(x, y) = ~(x & y)`, `base/bool.jl` (`~(::Missing) = missing`). -/
def nand3 (a b : Option Bool) : Option Bool := not3 (and3 a b)

/-- `nor(x, y) = ~(x | y)`, `base/bool.jl`. -/
def nor3 (a b : Option Bool) : Option Bool := not3 (or3 a b)

/-- The Boolean values an operand may stand for: `missing` stands for either. -/
def completions : Option Bool → List Bool
  | none => [false, true]
  | some b => [b]

/-- Kleene's strong three-valued logic: the result is a Boolean exactly when
every completion of the missing operands gives that same Boolean. -/
def kleene2 (f : Bool → Bool → Bool) (a b : Option Bool) : Option Bool :=
  let rs := (completions a).flatMap fun x => (completions b).map fun y => f x y
  if rs.all (· == true) then some true else if rs.all (· == false) then some false else none

def kleene1 (f : Bool → Bool) (a : Option Bool) : Option Bool :=
  kleene2 (fun x _ => f x) a (some false)

/-- The manual's three-valued logic (doc/src/manual/missing.md:105-201): `&`, `|`,
`xor`, `!`, `nand` and `nor` on `Union{Bool, Missing}` return `missing` exactly
when the result depends on the value of a missing operand, and otherwise the
Boolean every completion gives. -/
def ThreeValuedLogic : Prop :=
  ∀ a b : Option Bool,
    and3 a b = kleene2 (· && ·) a b ∧ or3 a b = kleene2 (· || ·) a b ∧
    xor3 a b = kleene2 (· ^^ ·) a b ∧ not3 a = kleene1 (! ·) a ∧
    nand3 a b = kleene2 (fun x y => !(x && y)) a b ∧ nor3 a b = kleene2 (fun x y => !(x || y)) a b

theorem threeValuedLogic_proven : ThreeValuedLogic := by
  intro a b
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> decide

/-- `&` and `|` are commutative and associative, and De Morgan's laws hold, on
`Union{Bool, Missing}` (consequences of the three-valued semantics). -/
def LogicAlgebra : Prop :=
  ∀ a b c : Option Bool,
    and3 a b = and3 b a ∧ or3 a b = or3 b a ∧
    and3 (and3 a b) c = and3 a (and3 b c) ∧ or3 (or3 a b) c = or3 a (or3 b c) ∧
    not3 (and3 a b) = or3 (not3 a) (not3 b) ∧ not3 (or3 a b) = and3 (not3 a) (not3 b) ∧
    and3 a (or3 b c) = or3 (and3 a b) (and3 a c)

theorem logicAlgebra_proven : LogicAlgebra := by
  intro a b c
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> rcases c with _ | _ | _ <;> decide

/-! ## Comparison operators, `base/missing.jl:74-88`, `base/operators.jl` -/

/-- `x == y`, `base/missing.jl:74-76`: missing if either argument is missing;
`eq` is the method for two non-missing values. -/
def eq3 (eq : α → α → Bool) : Option α → Option α → Option Bool
  | none, _ => none
  | _, none => none
  | some a, some b => some (eq a b)

/-- `x < y`, `base/missing.jl:83-85`. -/
def lt3 (lt : α → α → Bool) : Option α → Option α → Option Bool
  | none, _ => none
  | _, none => none
  | some a, some b => some (lt a b)

/-- `x != y = !(x == y)`, `base/operators.jl:338`. -/
def ne3 (eq : α → α → Bool) (x y : Option α) : Option Bool := not3 (eq3 eq x y)

/-- `x <= y = (x < y) | (x == y)`, `base/operators.jl:467`. -/
def le3 (eq lt : α → α → Bool) (x y : Option α) : Option Bool := or3 (lt3 lt x y) (eq3 eq x y)

/-- `x > y = y < x`, `base/operators.jl:443`. -/
def gt3 (lt : α → α → Bool) (x y : Option α) : Option Bool := lt3 lt y x

/-- `x >= y = y <= x`, `base/operators.jl:499`. -/
def ge3 (eq lt : α → α → Bool) (x y : Option α) : Option Bool := le3 eq lt y x

/-- doc/src/manual/missing.md:49-50: "if any of the operands is `missing`, the
result is `missing`" for the standard equality and comparison operators, and
with no missing operand they agree with the ordinary methods. -/
def ComparisonPropagates : Prop :=
  ∀ (α : Type) (eq lt : α → α → Bool) (x y : Option α),
    ((x = none ∨ y = none) →
      eq3 eq x y = none ∧ ne3 eq x y = none ∧ lt3 lt x y = none ∧
      le3 eq lt x y = none ∧ gt3 lt x y = none ∧ ge3 eq lt x y = none) ∧
    (∀ a b, x = some a → y = some b →
      eq3 eq x y = some (eq a b) ∧ ne3 eq x y = some (!eq a b) ∧
      le3 eq lt x y = some (lt a b || eq a b) ∧ ge3 eq lt x y = some (lt b a || eq b a))

theorem comparisonPropagates_proven : ComparisonPropagates := by
  intro α eq lt x y
  refine ⟨?_, ?_⟩
  · rintro (rfl | rfl)
    · cases y <;> simp [eq3, ne3, lt3, le3, gt3, ge3, or3, not3]
    · cases x <;> simp [eq3, ne3, lt3, le3, gt3, ge3, or3, not3]
  · rintro a b rfl rfl
    simp [eq3, ne3, lt3, le3, ge3, or3, not3]

/-! ## `isless` and `isequal`, `base/missing.jl:80-88` -/

/-- `isless(x, y)`, `base/missing.jl:86-88`: `missing` is after every value. -/
def islessM (lt : α → α → Bool) : Option α → Option α → Bool
  | none, none => false
  | none, some _ => false
  | some _, none => true
  | some a, some b => lt a b

/-- `isequal(x, y)`, `base/missing.jl:80-82`. -/
def isequalM (eqv : α → α → Bool) : Option α → Option α → Bool
  | none, none => true
  | none, some _ => false
  | some _, none => false
  | some a, some b => eqv a b

/-- A strict weak order, the contract of `isless` (`base/operators.jl:206-217`). -/
def StrictWeak (lt : α → α → Bool) : Prop :=
  (∀ a, lt a a = false) ∧
  (∀ a b c, lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b c, lt a b = false → lt b a = false → lt b c = false → lt c b = false →
    lt a c = false ∧ lt c a = false)

/-- `isless` on values that may be missing is a strict weak order whenever
`isless` on the non-missing values is one (the order `sort!` relies on). -/
def IslessStrictWeak : Prop :=
  ∀ (α : Type) (lt : α → α → Bool), StrictWeak lt → StrictWeak (islessM lt)

theorem islessStrictWeak_proven : IslessStrictWeak := by
  intro α lt ⟨hirr, htr, hinc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a; cases a <;> simp [islessM, hirr]
  · intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [islessM]
    exact htr _ _ _ hab hbc
  · intro a b c h1 h2 h3 h4
    cases a <;> cases b <;> cases c <;> simp_all [islessM]
    exact hinc _ _ _ h1 h2 h3 h4

/-- doc/src/manual/missing.md:90-92: "`missing` is considered as greater than
any other value" by `isless`, and `isless(missing, missing)` is false. -/
def MissingLast : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (x : Option α),
    islessM lt none x = false ∧ (x ≠ none → islessM lt x none = true)

theorem missingLast_proven : MissingLast := by
  intro α lt x
  cases x <;> simp [islessM]

/-- doc/src/manual/missing.md:71-74: `isequal` always returns a Bool,
considering `missing` equal to `missing` and different from any other value;
it is an equivalence relation when `isequal` on the other values is one. -/
def IsequalMissing : Prop :=
  ∀ (α : Type) (eqv : α → α → Bool),
    (∀ x : Option α, isequalM eqv none x = true ↔ x = none) ∧
    ((∀ a, eqv a a = true) → (∀ a b, eqv a b = eqv b a) →
      (∀ a b c, eqv a b = true → eqv b c = true → eqv a c = true) →
      (∀ x : Option α, isequalM eqv x x = true) ∧
      (∀ x y : Option α, isequalM eqv x y = isequalM eqv y x) ∧
      (∀ x y z : Option α, isequalM eqv x y = true → isequalM eqv y z = true →
        isequalM eqv x z = true))

theorem isequalMissing_proven : IsequalMissing := by
  intro α eqv
  refine ⟨?_, ?_⟩
  · intro x; cases x <;> simp [isequalM]
  · intro hr hs ht
    refine ⟨?_, ?_, ?_⟩
    · intro x; cases x <;> simp [isequalM, hr]
    · intro x y; cases x <;> cases y <;> simp [isequalM, hs]
    · intro x y z h1 h2
      cases x <;> cases y <;> cases z <;> simp_all [isequalM]
      exact ht _ _ _ h1 h2

/-- The `isless` docstring, `base/operators.jl:206-217`: "exactly one of" `isless(x, y)`,
`isless(y, x)` and `isequal(x, y)` "yields `true`". With `missing` this holds
whenever it holds for the non-missing values. -/
def IslessTrichotomy : Prop :=
  ∀ (α : Type) (lt eqv : α → α → Bool),
    (∀ a b, [lt a b, lt b a, eqv a b].count true = 1) →
    ∀ x y : Option α, [islessM lt x y, islessM lt y x, isequalM eqv x y].count true = 1

theorem islessTrichotomy_proven : IslessTrichotomy := by
  intro α lt eqv h x y
  cases x <;> cases y <;> simp [islessM, isequalM]
  exact h _ _

/-! ## `min`, `max`, `minmax`, `isgreater` -/

/-- `min(x, y)`: `min(::Missing, ::Any) = missing` etc. (`base/missing.jl:129-136`),
else `min(x,y) = ifelse(isless(y, x), y, x)` (`base/operators.jl:573`). -/
def minM (lt : α → α → Bool) : Option α → Option α → Option α
  | none, _ => none
  | _, none => none
  | some a, some b => if lt b a then some b else some a

/-- `max(x, y)`, `base/missing.jl:129-136`, `base/operators.jl:555`. -/
def maxM (lt : α → α → Bool) : Option α → Option α → Option α
  | none, _ => none
  | _, none => none
  | some a, some b => if lt b a then some a else some b

/-- `minmax(x, y)`, `base/missing.jl:129-136`, `base/operators.jl:588`. -/
def minmaxM (lt : α → α → Bool) : Option α → Option α → Option α × Option α
  | none, _ => (none, none)
  | _, none => (none, none)
  | some a, some b => if lt b a then (some b, some a) else (some a, some b)

/-- The `max` and `min` docstrings, `base/operators.jl:540-572`: "If any of the
arguments is `missing`, return `missing`"; `minmax(x, y)` is `(min(x,y), max(x,y))`
(`:575-587`). -/
def MinMaxMissing : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (x y : Option α),
    ((x = none ∨ y = none) → minM lt x y = none ∧ maxM lt x y = none) ∧
    minmaxM lt x y = (minM lt x y, maxM lt x y)

theorem minMaxMissing_proven : MinMaxMissing := by
  intro α lt x y
  refine ⟨?_, ?_⟩
  · intro h
    cases x <;> cases y <;> simp_all [minM, maxM]
  · cases x <;> cases y <;> simp [minmaxM, minM, maxM]
    split <;> simp

/-- `isunordered(::Missing) = true` (`base/operators.jl:311`); `unord` is
`isunordered` on the other values (`isnan` for floats). -/
def isunorderedM (unord : α → Bool) : Option α → Bool
  | none => true
  | some a => unord a

/-- `isgreater(x, y) = isunordered(x) || isunordered(y) ? isless(x, y) : isless(y, x)`,
`base/operators.jl:295`. -/
def isgreaterM (lt : α → α → Bool) (unord : α → Bool) (x y : Option α) : Bool :=
  if isunorderedM unord x || isunorderedM unord y then islessM lt x y else islessM lt y x

/-- The `isgreater` docstring, `base/operators.jl:255-262`: `NaN` and `missing` "are
ordered as smaller than any regular value with `missing` smaller than `NaN`":
every non-missing value is greater than `missing`, and `missing` is greater than
nothing. -/
def IsgreaterMissingSmallest : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (unord : α → Bool) (x : Option α),
    isgreaterM lt unord none x = false ∧ (x ≠ none → isgreaterM lt unord x none = true)

theorem isgreaterMissingSmallest_proven : IsgreaterMissingSmallest := by
  intro α lt unord x
  cases x <;> simp [isgreaterM, isunorderedM, islessM]

end JuliaLean.MissingChar
