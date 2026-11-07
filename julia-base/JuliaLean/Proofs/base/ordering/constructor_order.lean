import JuliaLean.base.ordering

namespace JuliaLean.Sort

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
