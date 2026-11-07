import JuliaLean.base.div
import JuliaLean.base.promotion
import JuliaLean.Proofs.base.float.IntArithDivision
import JuliaLean.Registry.Types

namespace JuliaLean.IntArith.Division

/-- fldmod's documentation promises the same numeric pair as fld and mod,
including when fixed-width inputs have different signedness. -/
def FldmodConsistency : Prop := ∀ x y : Value, ∀ q r m : Value,
  fldmod x y = .ok (q, r) → mod (rem promotedRem) x y = .ok m → r.int.val = m.int.val

set_option maxRecDepth 10000 in
theorem fldmodInconsistent : ¬ FldmodConsistency := by
  intro h
  have bad := h (lit .u8 1) (lit .i8 (-2)) (lit .u8 255) (lit .u8 255)
    (lit .i8 (-1)) (by rfl) (by rfl)
  exact (by decide : ¬ ((lit .u8 255).int.val = (lit .i8 (-1)).int.val)) bad

def entries : List JuliaLean.Registry.Entry := []

end JuliaLean.IntArith.Division
