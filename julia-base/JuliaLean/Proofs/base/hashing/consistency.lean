import JuliaLean.base.hashing
import JuliaLean.base.rational

namespace JuliaLean.HashOps

open JuliaLean JuliaLean.Promotion

/-- Hashing equal machine integers of any widths through 64 bits makes the same
primitive-call term for every seed. -/
def SmallIntegerHashConsistency : Prop :=
  ∀ (t s : IntTy) (x : JInt t) (y : JInt s) (h : HTerm),
    t ≠ .i128 → t ≠ .u128 → s ≠ .i128 → s ≠ .u128 → x.val = y.val →
    hashNum (.int t x) h = hashNum (.int s y) h

/-- The generic `hash(::Real)` path is consistent whenever `decompose` gives
equal normalized triples and the intermediate integer storage type is the same.
This is the source obligation shared by Int128, UInt128, BigInt, BigFloat and
generic Rational/Real implementations. -/
def DecomposedHashConsistency : Prop :=
  ∀ (α : Type) (eqv : α → α → Bool) (decompose : α → Decomposition)
    (numTy : α → IntTy),
    (∀ x y, eqv x y = true → decompose x = decompose y ∧ numTy x = numTy y) →
    ∀ x y h, eqv x y = true →
      hashDecomposed (numTy x) (decompose x) h =
      hashDecomposed (numTy y) (decompose y) h

/-- Valid byte-backed strings and character-iterated AbstractStrings with the
same character sequence hash equally for every seed. -/
def StringHashConsistency : Prop :=
  ∀ a b : Text, a.Valid → b.Valid → a.chars = b.chars →
    ∀ h, hashText a h = hashText b h

theorem smallIntegerHashConsistency_proven : SmallIntegerHashConsistency := by
  intro t s x y h ht1 ht2 hs1 hs2 hv
  cases t <;> cases s <;>
    simp_all [hashNum, hashI64, wrapInt, IntTy.signed, IntTy.bits]
  all_goals
    apply congrArg Int.toNat
    have hx := x.property
    have hy := y.property
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx hy
    omega

theorem decomposedHashConsistency_proven : DecomposedHashConsistency := by
  intro α eqv decompose numTy lawful x y h hxy
  obtain ⟨hd, ht⟩ := lawful x y hxy
  rw [hd, ht]

theorem stringHashConsistency_proven : StringHashConsistency := by
  rintro ⟨ac, ar, ab⟩ ⟨bc, br, bb⟩ ha hb hc h
  cases ab <;> cases bb <;>
    simp_all [Text.Valid, hashText, Text.utf8units, Text.canonicalBytes]

end JuliaLean.HashOps
