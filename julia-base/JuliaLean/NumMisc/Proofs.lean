import JuliaLean.NumMisc.Model

namespace JuliaLean.NumMisc

def fooPayload : List Byte := [102, 111, 111]

theorem sourceNanPayload_foo : sourceNanPayload fooPayload = some 0 := by decide +kernel

theorem documentedNanPayload_foo : documentedNanPayload fooPayload = false := by decide +kernel

theorem floatGrammarExact_refuted : ¬ FloatGrammarExact := by
  intro h
  have hs := h fooPayload
  rw [sourceNanPayload_foo, documentedNanPayload_foo] at hs
  simp at hs

theorem floatExactIntegerRounding_proven : FloatExactIntegerRounding := by
  intro w hw
  simp [fromDecimalInteger, hw]

def tinyAboveOne : IrrationalNearOne := ⟨.above, 1000⟩

def tinyBelowOne : IrrationalNearOne := ⟨.below, 1000⟩

theorem tinyAbove_source : sourceIrrationalConvert tinyAboveOne .up = .one := by decide +kernel

theorem tinyAbove_exact : exactIrrationalConvert tinyAboveOne .up = .next := by decide +kernel

theorem irrationalRoundingCorrect_refuted : ¬ IrrationalRoundingCorrect := by
  intro h
  have hs := h tinyAboveOne .up
  rw [tinyAbove_source, tinyAbove_exact] at hs
  cases hs

theorem irrationalSeparatedRoundingCorrect_proven : IrrationalSeparatedRoundingCorrect := by
  intro x hx r
  unfold sourceIrrationalConvert exactIrrationalConvert bigAt256
  simp [show ¬x.separationBits > 256 by omega]

theorem fastMathCoverage_refuted : ¬ FastMathCoverage := by
  intro h
  have hs := h 3 (by decide)
  simp [hypotFastSupportsArity] at hs

def tanhX32 : NF32 := nf32 0x3efbfa81

def tanhY32 : NF32 := nf32 0x3efbfa82

theorem tanhX32_value : tanhSmall32 tanhX32 = nf32 0x3ee96e0c := by decide +kernel

theorem tanhY32_value : tanhSmall32 tanhY32 = nf32 0x3ee96e0b := by decide +kernel

theorem tanhResultsNotOrdered :
    JuliaLean.Promotion.Fl.le (nf32 0x3ee96e0c) (nf32 0x3ee96e0b) = false := by
  decide +kernel

theorem tanhMonotone_refuted : ¬ TanhMonotone := by
  intro h
  have hm := h tanhX32 tanhY32 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [tanhX32_value, tanhY32_value, tanhResultsNotOrdered] at hm
  cases hm

theorem hyperbolicSymmetry_proven : HyperbolicSymmetry := by
  intro x
  cases x <;> decide

theorem hyperbolicSpecialValues_proven : HyperbolicSpecialValues := by
  intro x
  cases x <;> decide

theorem viewsDocumentedRewrite_proven : ViewsDocumentedRewrite := by
  constructor
  · intro a is
    simp only [rewriteViews]
  constructor
  · intro args
    exact ⟨args.map rewriteViews, by simp only [rewriteViews]⟩
  constructor
  · intro a is rhs
    simp only [rewriteViews]
  · intro id
    simp only [rewriteViews]

theorem pointerRefSemantics_proven : PointerRefSemantics := by
  constructor
  · intro p offset
    exact ⟨rfl, rfl⟩
  constructor
  · intro p elementBytes index
    rfl
  constructor
  · intro len index slot
    unfold derefArray
    split
    · rename_i h
      simp only [Except.ok.injEq]
      omega
    · rename_i h
      constructor
      · intro heq
        cases heq
      · intro hr
        exact (h ⟨hr.1, hr.2.1⟩).elim
  · intro xs
    rfl

end JuliaLean.NumMisc
