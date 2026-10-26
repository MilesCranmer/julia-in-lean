import JuliaLean.NumbersCov.Rows.ComplexBasic

namespace JuliaLean.NumbersCov.Rows.Complex

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

def m587 := @ComplexModel.cis
def P587 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) x,
  @m587 α o x = ⟨o.cos x, o.sin x⟩
theorem p587 : P587 := by simp [P587, m587, ComplexModel.cis]
def m592 := @ComplexModel.cisComplex
def P592 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m592 α o z)
theorem p592 : P592 := by simp [P592, HasResult]
def m618 := @ComplexModel.cispi
def P618 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) x,
  @m618 α o x = ⟨o.cospi x, o.sinpi x⟩
theorem p618 : P618 := by simp [P618, m618, ComplexModel.cispi]
def m620 := @ComplexModel.cispiComplex
def P620 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m620 α o z)
theorem p620 : P620 := by simp [P620, HasResult]
def m651 := @ComplexModel.angle
def P651 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z,
  @m651 α o z = o.atan2 z.im z.re
theorem p651 : P651 := by simp [P651, m651, ComplexModel.angle]
def m653 := @ComplexModel.log
def P653 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α)
  (s : α → α → α × Int) z, HasResult (@m653 α o s z)
theorem p653 : P653 := by simp [P653, HasResult]
def m695 (o : ComplexModel.ScalarOps α) (logC : C α → C α) z :=
  ComplexModel.logBase o (o.ofInt 10) (logC z)
def P695 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (l : C α → C α) z,
  HasResult (m695 o l z)
theorem p695 : P695 := by simp [P695, HasResult]
def m699 (o : ComplexModel.ScalarOps α) (logC : C α → C α) z :=
  ComplexModel.logBase o (o.ofInt 2) (logC z)
def P699 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (l : C α → C α) z,
  HasResult (m699 o l z)
theorem p699 : P699 := by simp [P699, HasResult]
def m704 := @ComplexModel.exp
def P704 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m704 α o z)
theorem p704 : P704 := by simp [P704, HasResult]
def m727 := @ComplexModel.expm1
def P727 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m727 α o z)
theorem p727 : P727 := by simp [P727, HasResult]
def m757 := @ComplexModel.log1p
def P757 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (l : C α → C α) z,
  HasResult (@m757 α o l z)
theorem p757 : P757 := by simp [P757, HasResult]
def m775 := @ComplexModel.exp2
def P775 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m775 α o z)
theorem p775 : P775 := by simp [P775, HasResult]
def m783 := @ComplexModel.exp10
def P783 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m783 α o z)
theorem p783 : P783 := by simp [P783, HasResult]

def m792 := @ComplexModel.cpowFull
def P792 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (float : C α → C α)
  (integer : α → Bool) (toInt : α → Int) (power : C α → Int → C α)
  (inv : C α → C α) (abs : C α → α) (cis : α → C α) (angle : C α → α)
  real z p, HasResult (@m792 α o float integer toInt power inv abs cis angle real z p)
theorem p792 : P792 := by simp [P792, HasResult]
def m882 (cpow : C α → C α → C α) z p := ComplexModel.powerCpow cpow z p
def P882 : Prop := ∀ (α : Type) (p : C α → C α → C α) z x, m882 p z x = p z x
theorem p882 : P882 := by simp [P882, m882, ComplexModel.powerCpow]
def m883 (cpow : C α → C α → C α) (toComplex : α → C α) z p := cpow z (toComplex p)
def P883 : Prop := ∀ (α : Type) (p : C α → C α → C α) (c : α → C α) z x,
  m883 p c z x = p z (c x)
theorem p883 : P883 := by simp [P883, m883]
def m884 (cpow : C α → C α → C α) (toComplex : α → C α) z p := cpow (toComplex z) p
def P884 : Prop := ∀ (α : Type) (p : C α → C α → C α) (c : α → C α) z x,
  m884 p c z x = p (c z) x
theorem p884 : P884 := by simp [P884, m884]
def m886 := @ComplexModel.powerBool
def P886 : Prop := ∀ (α : Type) (one : C α → C α) z n,
  @m886 α one z n = if n then z else one z
theorem p886 : P886 := by simp [P886, m886, ComplexModel.powerBool]
def m887 := @ComplexModel.powerViaComplexExponent
def P887 : Prop := ∀ (α : Type) (c : Int → C α) (p : C α → C α → C α) z n,
  @m887 α c p z n = p z (c n)
theorem p887 : P887 := by simp [P887, m887, ComplexModel.powerViaComplexExponent]
def m889 := @ComplexModel.powerBool
def P889 : Prop := P886
theorem p889 : P889 := p886
def m890 := @ComplexModel.powerBool
def P890 : Prop := P886
theorem p890 : P890 := p886
def m896 := @ComplexModel.powerPromotedComplexReal
def P896 : Prop := ∀ (α β γ δ : Type) (pr : α → β → γ)
  (cc : γ → C α → C δ) (cr : γ → β → δ) (pow : C δ → δ → C δ)
  component z p, HasResult (@m896 α β γ δ pr cc cr pow component z p)
theorem p896 : P896 := by simp [P896, HasResult]
def m900 := @ComplexModel.powerPromotedRealComplex
def P900 : Prop := ∀ (α β γ δ : Type) (pr : α → β → γ)
  (cr : γ → α → δ) (cc : γ → C β → C δ) (pow : δ → C δ → C δ)
  z component p, HasResult (@m900 α β γ δ pr cr cc pow z component p)
theorem p900 : P900 := by simp [P900, HasResult]

def m905 := @ComplexModel.sin
def P905 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m905 α o z)
theorem p905 : P905 := by simp [P905, HasResult]
def m923 := @ComplexModel.cos
def P923 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m923 α o z)
theorem p923 : P923 := by simp [P923, HasResult]
def m943 := @ComplexModel.tanFromTanh
def P943 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (t : C α → C α) z,
  HasResult (@m943 α o t z)
theorem p943 : P943 := by simp [P943, HasResult]
def m949 := @ComplexModel.asin
def P949 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (s : C α → C α) z,
  HasResult (@m949 α o s z)
theorem p949 : P949 := by simp [P949, HasResult]
def m963 := @ComplexModel.acosFull
def P963 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α)
  (f s : C α → C α) z, HasResult (@m963 α o f s z)
theorem p963 : P963 := by simp [P963, HasResult]
def m986 := @ComplexModel.atanFromAtanh
def P986 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (a : C α → C α) z,
  HasResult (@m986 α o a z)
theorem p986 : P986 := by simp [P986, HasResult]
def m991 := @ComplexModel.sinhFromSin
def P991 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (s : C α → C α) z,
  HasResult (@m991 α o s z)
theorem p991 : P991 := by simp [P991, HasResult]
def m997 := @ComplexModel.coshFromCos
def P997 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (c : C α → C α) z,
  HasResult (@m997 α o c z)
theorem p997 : P997 := by simp [P997, HasResult]
def m1002 := @ComplexModel.tanh
def P1002 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) large z,
  HasResult (@m1002 α o large z)
theorem p1002 : P1002 := by simp [P1002, HasResult]
def m1024 := @ComplexModel.asinhFromAsin
def P1024 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (a : C α → C α) z,
  HasResult (@m1024 α o a z)
theorem p1024 : P1024 := by simp [P1024, HasResult]
def m1029 := @ComplexModel.acoshFull
def P1029 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (s : C α → C α) z,
  HasResult (@m1029 α o s z)
theorem p1029 : P1029 := by simp [P1029, HasResult]
def m1048 := @ComplexModel.atanhFull
def P1048 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) large (i : C α → C α) z,
  HasResult (@m1048 α o large i z)
theorem p1048 : P1048 := by simp [P1048, HasResult]

def m1123 := @ComplexModel.round
def P1123 : Prop := ∀ (α : Type) (rr ri : α → α) z,
  @m1123 α rr ri z = ⟨rr z.re, ri z.im⟩
theorem p1123 : P1123 := by simp [P1123, m1123, ComplexModel.round]
def m1129 := @ComplexModel.floatIdentity
def P1129 : Prop := ∀ (α : Type) (z : C α), @m1129 α z = z
theorem p1129 : P1129 := by simp [P1129, m1129, ComplexModel.floatIdentity]
def m1130 := @ComplexModel.mapComponents
def P1130 : Prop := ∀ (α β : Type) (f : α → β) z,
  @m1130 α β f z = ⟨f z.re, f z.im⟩
theorem p1130 : P1130 := by simp [P1130, m1130, ComplexModel.mapComponents]
def m1132 := @ComplexModel.bigType
def P1132 : Prop := ∀ (α β γ : Type) (b : α → β) (c : β → γ) t,
  @m1132 α β γ b c t = c (b t)
theorem p1132 : P1132 := by simp [P1132, m1132, ComplexModel.bigType]
def m1133 := @ComplexModel.bigValue
def P1133 : Prop := ∀ (α β γ : Type) (b : α → β) (c : β → C α → C γ) t z,
  @m1133 α β γ b c t z = c (b t) z
theorem p1133 : P1133 := by simp [P1133, m1133, ComplexModel.bigValue]
def m1153 := @ComplexModel.arrayComplexIdentity
def P1153 : Prop := ∀ (α : Type) (x : α), @m1153 α x = x
theorem p1153 : P1153 := by simp [P1153, m1153, ComplexModel.arrayComplexIdentity]
def m1155 := @ComplexModel.arrayComplexConvert
def P1155 : Prop := ∀ (α β : Type) concrete (c : α → β) x,
  HasResult (@m1155 α β concrete c x)
theorem p1155 : P1155 := by simp [P1155, HasResult]
def m1164 := @ComplexModel.epsValue
def P1164 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z,
  HasResult (@m1164 α o z)
theorem p1164 : P1164 := by simp [P1164, HasResult]
def m1166 := @ComplexModel.epsType
def P1166 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) x,
  HasResult (@m1166 α o x)
theorem p1166 : P1166 := by simp [P1166, HasResult]

end JuliaLean.NumbersCov.Rows.Complex
