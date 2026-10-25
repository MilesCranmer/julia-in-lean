import JuliaLean.Iterators.Spec

namespace JuliaLean.Iterators

open JuliaLean

private theorem indexPromotedWrap (t : IntTy) (n : JInt t) :
    promotedWrap .i64 t (1 + n.val - 1) = n.val := by
  have hn := n.property
  have hr : (IntTy.promote .i64 t).min ≤ n.val ∧
      n.val ≤ (IntTy.promote .i64 t).max := by
    cases t <;>
      simp [IntTy.promote, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max] at hn ⊢ <;>
      omega
  unfold promotedWrap
  have he : 1 + n.val - 1 = n.val := by omega
  rw [he]
  exact wrapInt_of_inRange _ _ hr

theorem nthVectorCorrect : NthVectorCorrect := by
  intro t xs n fuel _
  simp only [nthJ, nth, arrayNth, indexPromotedWrap]
  rfl

end JuliaLean.Iterators
