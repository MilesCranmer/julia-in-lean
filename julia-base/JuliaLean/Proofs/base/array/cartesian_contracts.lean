import JuliaLean.base.array
import JuliaLean.Proofs.base.multidimensional.cartesian_contracts

namespace JuliaLean.Multidim

/-- The first index of `A` (column-major order) holding `true`. -/
def firstTrue (sz : List Nat) (A : List Int → Bool) : Option (List I64) :=
  (elems (sz.map fun (n : Nat) => (⟨i64 1, i64 1, n⟩ : Rng))).find? fun I => A (I.map (·.val))

/-- `findfirst(f, A)` on an array with no empty dimension returns the first index
(column-major) where `f` holds, or `nothing`. -/
def FindfirstNonempty : Prop :=
  ∀ (sz : List Nat) (A : List Int → Bool), (∀ n ∈ sz, 0 < n ∧ n < 2 ^ 20) →
    findfirst inc ciLess sz A = .ok (firstTrue sz A)

/-- `findfirst(f, A)` returns the first index (column-major) where `f` holds, or
`nothing`; it never throws. -/
def FindfirstCartesian : Prop :=
  ∀ (sz : List Nat) (A : List Int → Bool), (∀ n ∈ sz, n < 2 ^ 20) →
    findfirst inc ciLess sz A = .ok (firstTrue sz A)

end JuliaLean.Multidim
