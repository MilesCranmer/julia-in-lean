import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.Sort

/-- Constructor-normal orderings from `base/ordering.jl:31-111`.
`forward` and `custom` carry the underlying `isless` and `Lt` comparisons;
the Boolean records their optional ReverseOrdering wrapper. By and Perm
remain outside that wrapper, as required by the specialized constructors.
Explicit parametric ReverseOrdering constructors that bypass those methods
are outside this representation. Data lookup in Perm is restricted to valid indices. -/
inductive Ordering : Type → Type 1 where
  | forward {α : Type} (cmp : α → α → Bool) (rev : Bool := false) : Ordering α
  | custom {α : Type} (cmp : α → α → Bool) (rev : Bool := false) : Ordering α
  | by {α β : Type} (f : α → β) (order : Ordering β) : Ordering α
  | perm {α : Type} (order : Ordering α) (data : Int → α) : Ordering Int

/-- `ReverseOrdering` dispatch, `base/ordering.jl:46-48,110-111`. -/
def reverseOrdering : Ordering α → Ordering α
  | .forward cmp rev => .forward cmp (!rev)
  | .custom cmp rev => .custom cmp (!rev)
  | .by f order => .by f (reverseOrdering order)
  | .perm order data => .perm (reverseOrdering order) data

/-- `lt`, including the eager Boolean Perm tie breaker,
`base/ordering.jl:118-127`. -/
def orderingLt : Ordering α → α → α → Bool
  | .forward cmp rev, a, b => if rev then cmp b a else cmp a b
  | .custom cmp rev, a, b => if rev then cmp b a else cmp a b
  | .by f order, a, b => orderingLt order (f a) (f b)
  | .perm order data, a, b =>
      orderingLt order (data a) (data b) ||
        (!(orderingLt order (data b) (data a)) && decide (a < b))

/-- Function identity is part of Julia dispatch, rather than extensional equality. -/
inductive ByArg (α : Type) where
  | identity
  | transform (f : α → α)

/-- `_by`, `base/ordering.jl:136-137`. -/
def applyBy (key : ByArg α) (order : Ordering α) : Ordering α :=
  match key with
  | .identity => order
  | .transform f => .by f order

/-- `_ord`, `base/ordering.jl:130-137`. `none` denotes the actual `isless`
function object; `some` denotes a custom comparator. Ambiguous arguments
produce Julia's ErrorException, represented separately because Core has no
ErrorException constructor. -/
def baseOrd (cmp : Option (α → α → Bool)) (key : ByArg α)
    (order : Ordering α) : Except String (Ordering α) :=
  match cmp with
  | none => .ok (applyBy key order)
  | some f => match order with
    | .forward _ false => .ok (applyBy key (.custom f))
    | .forward _ true => .ok (reverseOrdering (applyBy key (.custom f)))
    | _ => .error "ErrorException: Passing both lt= and order= arguments is ambiguous"

/-- `ord`, `base/ordering.jl:155-160`; Nothing and false leave `_ord` unchanged. -/
def ord (cmp : Option (α → α → Bool)) (key : ByArg α)
    (rev : Option Bool) (order : Ordering α) : Except String (Ordering α) := do
  let o ← baseOrd cmp key order
  pure (if rev == some true then reverseOrdering o else o)

def ReverseCancellation : Prop := ∀ (α : Type) (o : Ordering α),
  reverseOrdering (reverseOrdering o) = o

theorem reverseCancellation : ReverseCancellation := by
  intro α o
  induction o with
  | forward cmp rev => cases rev <;> rfl
  | custom cmp rev => cases rev <;> rfl
  | «by» f o ih => simp [reverseOrdering, ih]
  | perm o data ih => simp [reverseOrdering, ih]

/-- `ord(lt, by, rev, order)` for every combination the docstring allows
(`base/ordering.jl:140-153`: "all options are independent and can be used
together in all possible combinations"): `lt` is `isless` (`none`) or custom,
`by` is `identity` or a key function, `rev` is `nothing`, `false` or `true`, and
`order` is `Forward` or `Reverse`. The result compares the keys with the base
comparison, reversed exactly when one of `rev=true` and `order=Reverse` holds. -/
def OrdCombinations : Prop := ∀ (α : Type) (isl : α → α → Bool)
    (lt : Option (α → α → Bool)) (key : ByArg α) (rev : Option Bool) (orderRev : Bool) (a b : α),
  (ord lt key rev (.forward isl orderRev)).map (fun o => orderingLt o a b) =
    .ok (let base := lt.getD isl
         let k : α → α := match key with | .identity => id | .transform f => f
         if (rev == some true) != orderRev then base (k b) (k a) else base (k a) (k b))

theorem ordCombinations : OrdCombinations := by
  intro α isl lt key rev orderRev a b
  cases lt <;> cases key <;> cases orderRev <;>
    (cases rev with
      | none => rfl
      | some r => cases r <;> rfl)

def PermStability : Prop := ∀ (α : Type) (o : Ordering α) (data : Int → α)
    (i j : Int), orderingLt o (data i) (data j) = false →
  orderingLt o (data j) (data i) = false →
  orderingLt (.perm o data) i j = decide (i < j)

theorem permStability : PermStability := by
  intro α o data i j hij hji
  simp [orderingLt, hij, hji]

end JuliaLean.Sort
