import JuliaLean.base.intfuncs
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.intfuncs.lcm_zero_absorption

open JuliaLean JuliaLean.base.intfuncs

/-- The documented n-argument LCM is zero whenever any argument is zero.
Source promise: base/intfuncs.jl:98-101; implementation: base/intfuncs.jl:162
at f755f49a9e41380d7da126b3c1db9fe7f83dd027. All inputs are fixed-width
integers; the result zero is representable at every width. -/
def LcmZeroAbsorption : Prop :=
  ∀ (t : IntTy) (a b c : JInt t) (cs : List (JInt t)),
    (∃ x ∈ a :: b :: c :: cs, x.val = 0) →
    (lcm_Nary lcmBits
      (lcm_Unary (gcd_Unary_Integer JuliaLean.base.checked.checkedAbsBits))
      a b (c :: cs)).map Subtype.val = .ok 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem lcmZeroAbsorption_refuted : ¬ LcmZeroAbsorption := by
  intro h
  let a := JuliaLean.base.int.lit .i8 0
  let b := JuliaLean.base.int.lit .i8 64
  let c := JuliaLean.base.int.lit .i8 3
  have hzero : ∃ x ∈ a :: b :: c :: [], x.val = 0 :=
    ⟨a, by simp, by decide⟩
  have hresult := h .i8 a b c [] hzero
  have hfailed : ((lcm_Nary lcmBits
      (lcm_Unary (gcd_Unary_Integer JuliaLean.base.checked.checkedAbsBits))
      a b [c]).map Subtype.val).isOk = false := by decide
  rw [hresult] at hfailed
  exact Bool.noConfusion hfailed

def entries : List JuliaLean.Registry.Entry := [
  { id := "intfuncs-lcm-nary-zero", juliaFile := "base/intfuncs.jl",
    juliaFns := ["lcm(a::Real, b::Real, c::Real...)"],
    statement := "For every fixed-width integer type and every list of at least three inputs, lcm returns zero if any input is zero.",
    source := "base/intfuncs.jl:98-101,136-144,162", status := .refuted,
    prop := ``LcmZeroAbsorption, thm := some ``lcmZeroAbsorption_refuted,
    issue := "none found (issues: lcm zero; lcm. PRs: lcm overflow; lcm zero)",
    notes := "lcm(Int8(0), Int8(64), Int8(3)) overflows in the right-hand pair before considering the zero; moving zero into that pair returns zero." }
]

end JuliaLean.Proofs.base.intfuncs.lcm_zero_absorption
