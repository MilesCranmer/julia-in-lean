import JuliaLean.base.float

namespace JuliaLean.IntArith.Division

/-- uabs returns the mathematical magnitude even at every signed typemin. -/
def UabsTypemin : Prop := ∀ t : IntTy, t.signed = true →
  (uabs (lit t t.min)).int.val = -t.min

theorem uabsTypemin : UabsTypemin := by
  intro t ht
  cases t <;> first | contradiction | decide

end JuliaLean.IntArith.Division
