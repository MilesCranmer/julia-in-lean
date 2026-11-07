import JuliaLean.base.deprecated
import JuliaLean.Proofs.base.strings.string.properties

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

/-- The representation invariant required by every operation on a `SubString`:
its signed offset and code-unit count describe a span inside the parent. -/
def validSubString (ss : Strings.JSub) : Prop :=
  0 ≤ ss.offset.val ∧ 0 ≤ ss.ncu.val ∧
    ss.offset.val + ss.ncu.val ≤ ss.str.bytes.length

/-- Both deprecated public caller paths must preserve the SubString
representation invariant on every successful result. -/
def DeprecatedSubstringValid : Prop :=
  (∀ s i n ss, deprecatedNoshiftString s i n = .ok ss → validSubString ss) ∧
  (∀ s i n ss, validSubString s →
    deprecatedNoshiftSubString s i n = .ok ss → validSubString ss)

theorem deprecatedSubstringValid_refuted : ¬ DeprecatedSubstringValid := by
  intro h
  let result : Strings.JSub :=
    ⟨Strings.strABC, Strings.ix 2, Strings.ix (-1)⟩
  have hr : deprecatedNoshiftString Strings.strABC (Strings.ix 2) (Strings.ix (-1)) =
      .ok result := by decide
  have hv := h.1 Strings.strABC (Strings.ix 2) (Strings.ix (-1)) result hr
  have hn : (Strings.ix (-1)).val = -1 := by decide
  have hnonneg : 0 ≤ result.ncu.val := hv.2.1
  change 0 ≤ (Strings.ix (-1)).val at hnonneg
  rw [hn] at hnonneg
  omega

end JuliaLean.MemSafety.G1
