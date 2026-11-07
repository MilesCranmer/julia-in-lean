import JuliaLean.base.number
import JuliaLean.base.promotion
import JuliaLean.base.intfuncs

namespace JuliaLean.HashOps

open JuliaLean JuliaLean.Promotion

/-- Direct equations promised by `zero`, `one`, `oneunit`, `iszero`, `isone`,
`signbit`, `abs`, `sign`, `muladd`, `fma`, `inv`, and literal powers. -/
def NumberFallbacks : Prop :=
  ∀ (α : Type) (o : FallbackOps α) (pow : α → Int → α) (x y z : α),
    zeroFallback o x = o.zero x ∧ oneFallback o x = o.one x ∧
    oneunitFallback o x = o.castOne (o.one x) ∧
    iszeroFallback o x = o.eq x (o.zero x) ∧ isoneFallback o x = o.eq x (o.one x) ∧
    signbitFallback o x = o.lt x (o.zero x) ∧
    absFallback o x = (if o.lt x (o.zero x) then o.neg x else x) ∧
    signFallback o x = (if o.lt x (o.zero x) then o.neg (o.one x)
      else if o.lt (o.zero x) x then o.one x else x) ∧
    muladdFallback o x y z = o.add (o.mul x y) z ∧
    fmaNumberFallback x y z = .noOperation ∧
    fmaIntegerFallback o x y z = .ok (o.add (o.mul x y) z) ∧
    invFallback o x = o.div (o.one x) x ∧
    literalPowHW o pow x 0 = o.one x ∧ literalPowHW o pow x 1 = x ∧
    literalPowHW o pow x 2 = o.mul x x ∧
    literalPowHW o pow x 3 = o.mul (o.mul x x) x ∧
    literalPowHW o pow x (-1) = o.div (o.one x) x

theorem numberFallbacks_proven : NumberFallbacks := by
  intro α o pow x y z
  simp [zeroFallback, oneFallback, oneunitFallback, iszeroFallback, isoneFallback,
    signbitFallback, absFallback, signFallback, muladdFallback, fmaNumberFallback, fmaIntegerFallback,
    invFallback, literalPowHW] <;> rfl

end JuliaLean.HashOps
