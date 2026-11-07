import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- `split(s, '/'; limit=2)` returns one field without a slash and two with a
slash. Only the two-field branch reads `ss[1]` and `ss[2]`,
`base/rational.jl:175-186`. -/
def rationalPartCount (s : List Char) : Nat := if s.contains '/' then 2 else 1

inductive RationalPart where
  | numerator
  | denominator

def rationalAccess (s : List Char) (which : RationalPart) : Option (Nat × Int) :=
  if s.contains '/' then
    some (2, match which with | .numerator => 1 | .denominator => 2)
  else none

def RationalSplitInBounds : Prop :=
  ∀ (s : List Char) (which : RationalPart) (n : Nat) (i : Int),
    rationalAccess s which = some (n, i) → InBounds n i


theorem rationalSplitInBounds : RationalSplitInBounds := by
  intro s which n i h
  unfold rationalAccess at h
  split at h
  · cases which <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      rcases h with ⟨rfl, rfl⟩ <;> exact ⟨by omega, by omega⟩
  · contradiction

end JuliaLean.MemSafety.G4
