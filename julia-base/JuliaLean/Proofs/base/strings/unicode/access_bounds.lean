import JuliaLean.Proofs.base.abstractarray.common.input_invariants
import JuliaLean.base.strings.unicode

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- The utf8proc category table used by `category_code`. Its result type is the
documented range `0:30` (`base/strings/unicode.jl:371-381`). -/
structure CategoryData where
  cat : UInt32 → Fin 31
  idStart : UInt32 → Bool
  idChar : UInt32 → Bool

def CategoryData.toUData (d : CategoryData) : Show.UData :=
  ⟨fun u => (d.cat u).val, d.idStart, d.idChar⟩

/-- The index computed by `category_string(::Char)`, including the malformed
character branch of `category_code`, `base/strings/unicode.jl:371-403`. -/
def categoryStringIndex (d : CategoryData) (c : UInt32) : Nat :=
  Show.categoryCode d.toUData c + 1

def UnicodeCategorySafe : Prop :=
  ∀ (d : CategoryData) (c : UInt32), inOneBased 32 (categoryStringIndex d c)

private theorem asciiCategoryBound :
    ∀ k : Fin 128, Show.asciiCats.getD k.val 0 ≤ 30 := by
  decide +kernel

theorem unicodeCategorySafe_proven : UnicodeCategorySafe := by
  intro d c
  unfold categoryStringIndex inOneBased Show.categoryCode
  split
  · omega
  · split
    · rename_i u hcp
      split
      · unfold Show.utf8procCategory
        split
        · rename_i hu
          have hk : u.toNat < 128 := by
            simpa using UInt32.lt_iff_toNat_lt.mp hu
          have hb : Show.asciiCats.getD u.toNat 0 ≤ 30 := by
            simpa using asciiCategoryBound ⟨u.toNat, hk⟩
          omega
        · constructor
          · omega
          · simp [CategoryData.toUData]
      · omega
    · omega

end JuliaLean.MemSafety.G3
