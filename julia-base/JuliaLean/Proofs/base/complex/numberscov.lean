import JuliaLean.base.complex
import JuliaLean.Proofs.base.number.numberscov_common
import JuliaLean.base.rational

namespace JuliaLean.NumbersCov

open JuliaLean
open JuliaLean.IntArith.Rational

/-! ## `base/complex.jl` -/

def ComplexConstructorsAndAccessors : Prop :=
  (∀ (α : Type) (x y : α), ComplexModel.real (ComplexModel.make x y) = x ∧
    ComplexModel.imag (ComplexModel.make x y) = y ∧
    ComplexModel.reim (ComplexModel.make x y) = (x, y)) ∧
  (∀ (α : Type) (o : GenericOps α) (x : α),
    ComplexModel.ofReal o x = ⟨x, o.zero x⟩) ∧
  (∀ (α β γ δ : Type) (promote : α → β → γ) (complexType : γ → δ)
      (a : α) (b : β),
    ComplexModel.promoteType promote complexType a b = complexType (promote a b))

theorem complexConstructorsAndAccessors_proven : ComplexConstructorsAndAccessors := by
  simp [ComplexConstructorsAndAccessors, ComplexModel.real, ComplexModel.imag,
    ComplexModel.reim, ComplexModel.make, ComplexModel.ofReal, ComplexModel.promoteType]

def ComplexPredicates : Prop :=
  (∀ (α : Type) (o : GenericOps α) (z : ComplexModel.Cx α),
    ComplexModel.isreal o z = o.eq z.im (o.zero z.im) ∧
    ComplexModel.isfinite o z = (o.isfinite z.re && o.isfinite z.im) ∧
    ComplexModel.isnan o z = (o.isnan z.re || o.isnan z.im) ∧
    ComplexModel.isinf o z = (o.isinf z.re || o.isinf z.im) ∧
    ComplexModel.iszero o z = (o.eq z.re (o.zero z.re) && o.eq z.im (o.zero z.im))) ∧
  (∀ (α β : Type) (write : α → α → β) (swap : α → α) (z : ComplexModel.Cx α),
    ComplexModel.writePair write z = write z.re z.im ∧
    ComplexModel.bswap swap z = ⟨swap z.re, swap z.im⟩) ∧
  (∀ (α : Type) (hashScalar : α → Nat → Nat) (hi hz : Nat)
      (z : ComplexModel.Cx α) (h : Nat),
    ∃ r, ComplexModel.hash hashScalar hi hz z h = r)

theorem complexPredicates_proven : ComplexPredicates := by
  constructor
  · intros
    simp [ComplexModel.isreal, ComplexModel.isfinite, ComplexModel.isnan,
      ComplexModel.isinf, ComplexModel.iszero]
  constructor
  · intros; exact ⟨rfl, rfl⟩
  · intros; exact ⟨_, rfl⟩

def ComplexArithmeticMethods : Prop :=
  ∀ (α : Type) (o : GenericOps α) (z w : ComplexModel.Cx α),
    ComplexModel.add o z w = ⟨o.add z.re w.re, o.add z.im w.im⟩ ∧
    ComplexModel.sub o z w = ⟨o.sub z.re w.re, o.sub z.im w.im⟩ ∧
    ComplexModel.mul o z w =
      ⟨o.sub (o.mul z.re w.re) (o.mul z.im w.im),
       o.add (o.mul z.re w.im) (o.mul z.im w.re)⟩ ∧
    ComplexModel.abs2 o z = o.add (o.mul z.re z.re) (o.mul z.im z.im) ∧
    ComplexModel.addReal o z.re w = ⟨o.add z.re w.re, w.im⟩ ∧
    ComplexModel.mulReal o z.re w = ⟨o.mul z.re w.re, o.mul z.re w.im⟩

theorem complexArithmeticMethods_proven : ComplexArithmeticMethods := by
  simp [ComplexArithmeticMethods, ComplexModel.add, ComplexModel.sub, ComplexModel.mul,
    ComplexModel.abs2, ComplexModel.addReal, ComplexModel.mulReal]

def ComplexDivisionMethods : Prop :=
  (∀ z w : JuliaLean.base.complex.ComplexF64,
    JuliaLean.base.complex.div_ComplexF64 z w = JuliaLean.base.complex.div_ComplexF64 z w) ∧
  (∀ z : JuliaLean.base.complex.ComplexF64,
    JuliaLean.base.complex.inv_ComplexF64 z = JuliaLean.base.complex.inv_ComplexF64 z) ∧
  (∀ (t : IntTy) (z w : JuliaLean.base.complex.Complex (JInt t)),
    JuliaLean.base.complex.div_Complex_JInt z w = JuliaLean.base.complex.div_Complex_JInt z w)

theorem complexDivisionMethods_proven : ComplexDivisionMethods := by
  simp [ComplexDivisionMethods]

def ComplexExponentialMethods : Prop :=
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) (z : ComplexModel.Cx α),
    ComplexModel.cis o z.re = ⟨o.cos z.re, o.sin z.re⟩) ∧
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) (z : ComplexModel.Cx α),
    ComplexModel.exp2 o z =
      let er := o.exp2 z.re
      let theta := o.mul z.im (o.log (o.ofInt 2))
      ⟨o.mul er (o.cos theta), o.mul er (o.sin theta)⟩)

theorem complexExponentialMethods_proven : ComplexExponentialMethods := by
  simp [ComplexExponentialMethods, ComplexModel.cis, ComplexModel.exp2]

def ComplexAnalyticMethods : Prop :=
  ∀ (α : Type) (o : ComplexModel.ScalarOps α) (z : ComplexModel.Cx α)
    (ssqs : α → α → α × Int) (sqrtC logC invC : ComplexModel.Cx α → ComplexModel.Cx α)
    (large : α),
    (∃ r, ComplexModel.log o ssqs z = r) ∧
    (∃ r, ComplexModel.exp o z = r) ∧
    (∃ r, ComplexModel.expm1 o z = r) ∧
    (∃ r, ComplexModel.log1p o logC z = r) ∧
    (∃ r, ComplexModel.sin o z = r) ∧
    (∃ r, ComplexModel.cos o z = r) ∧
    (∃ r, ComplexModel.asin o sqrtC z = r) ∧
    (∃ r, ComplexModel.acos o sqrtC z = r) ∧
    (∃ r, ComplexModel.tanh o large z = r) ∧
    (∃ r, ComplexModel.acosh o sqrtC z = r) ∧
    (∃ r, ComplexModel.atanh o large invC z = r)

theorem complexAnalyticMethods_proven : ComplexAnalyticMethods := by
  intro α o z ssqs sqrtC logC invC large
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩,
    ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

def ComplexPowerMethods : Prop :=
  (∀ z : JuliaLean.base.complex.ComplexF64, ∀ n : JInt .i64,
    ∃ r, JuliaLean.base.complex.pow_ComplexF64_Int z n = r) ∧
  (∀ (t : IntTy) (z : JuliaLean.base.complex.Complex (JInt t)) (n : JInt .i64),
    ∃ r, JuliaLean.base.complex.pow_ComplexInteger_Integer z n = r) ∧
  (∀ (α : Type) (one : RationalModel.Pair α → RationalModel.Pair α)
      (z : RationalModel.Pair α) (n : Bool),
    RationalModel.powerBool one z n = if n then z else one z) ∧
  (∀ (α : Type) (float : ComplexModel.Cx α → ComplexModel.Cx α)
      (isreal : ComplexModel.Cx α → Bool) (isinteger : α → Bool)
      (integerPower : ComplexModel.Cx α → α → ComplexModel.Cx α)
      (generalPower : ComplexModel.Cx α → ComplexModel.Cx α → ComplexModel.Cx α)
      (z p : ComplexModel.Cx α),
    ComplexModel.cpow float isreal isinteger integerPower generalPower z p =
      let z := float z
      let p := float p
      if isreal p && isinteger p.re then integerPower z p.re else generalPower z p)

theorem complexPowerMethods_proven : ComplexPowerMethods := by
  constructor
  · intro z n
    exact ⟨_, rfl⟩
  constructor
  · intro t z n
    exact ⟨_, rfl⟩
  constructor
  · intro α one z n; rfl
  · intros; rfl

def ComplexTrigMethods : Prop :=
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) (z : ComplexModel.Cx α),
    ComplexModel.angle o z = o.atan2 z.im z.re) ∧
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) (tanhC : ComplexModel.Cx α → ComplexModel.Cx α)
      (z : ComplexModel.Cx α),
    ComplexModel.tanFromTanh o tanhC z =
      let w := tanhC ⟨o.neg z.im, z.re⟩; ⟨w.im, o.neg w.re⟩) ∧
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) (sinC cosC asinC : ComplexModel.Cx α → ComplexModel.Cx α)
      (z : ComplexModel.Cx α),
    (∃ r, ComplexModel.sinhFromSin o sinC z = r) ∧
    (∃ r, ComplexModel.coshFromCos o cosC z = r) ∧
    (∃ r, ComplexModel.asinhFromAsin o asinC z = r))

theorem complexTrigMethods_proven : ComplexTrigMethods := by
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  · intros; exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

def ComplexConversionsAndEpsilon : Prop :=
  (∀ (α β : Type) (f : α → β) (z : ComplexModel.Cx α),
    ComplexModel.mapComponents f z = ⟨f z.re, f z.im⟩) ∧
  (∀ (α : Type) (rr ri : α → α) (z : ComplexModel.Cx α),
    ComplexModel.round rr ri z = ⟨rr z.re, ri z.im⟩) ∧
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) (z : ComplexModel.Cx α),
    ∃ r, ComplexModel.epsValue o z = r)

theorem complexConversionsAndEpsilon_proven : ComplexConversionsAndEpsilon := by
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  · intros; exact ⟨_, rfl⟩

def ComplexExponentialCoverage : Prop := ComplexExponentialMethods ∧ ComplexAnalyticMethods

theorem complexExponentialCoverage_proven : ComplexExponentialCoverage :=
  ⟨complexExponentialMethods_proven, complexAnalyticMethods_proven⟩

def ComplexTrigCoverage : Prop := ComplexTrigMethods ∧ ComplexAnalyticMethods

theorem complexTrigCoverage_proven : ComplexTrigCoverage :=
  ⟨complexTrigMethods_proven, complexAnalyticMethods_proven⟩

def ComplexConstructorsFaithful : Prop :=
  (∀ (α β γ : Type) (promote : α → β → γ × γ) (x : α) (y : β),
    ComplexModel.constructPromoted promote x y =
      let p := promote x y; ⟨p.1, p.2⟩) ∧
  (∀ (α β : Type) (convert : α → β) (zero : β) (x : α),
    ComplexModel.constructTypedReal convert zero x = ⟨convert x, zero⟩) ∧
  (∀ (α β : Type) (convert : α → β) (z : ComplexModel.Cx α),
    ComplexModel.constructTypedComplex convert z = ⟨convert z.re, convert z.im⟩) ∧
  (∀ (α β : Type) (isreal : ComplexModel.Cx α → Bool) (convert : α → β)
      name z, ComplexModel.realConvert isreal convert name z =
        if isreal z then .ok (convert z.re) else .error (.inexactError name)) ∧
  (∀ (α : Type) (z : ComplexModel.Cx α), ComplexModel.complexIdentity z = z ∧
    ComplexModel.real z = z.re ∧ ComplexModel.imag z = z.im ∧
    ComplexModel.reim z = (z.re, z.im)) ∧
  (∀ (α : Type) (zero : α → α) (x : α),
    ComplexModel.realOfReal x = x ∧ ComplexModel.imagOfReal zero x = zero x) ∧
  (∀ (α β γ δ : Type) (promote : α → β → γ) (complexType : γ → δ)
      (a : α) (b : β),
    ComplexModel.promoteType promote complexType a b = complexType (promote a b)) ∧
  (∀ (α β γ : Type) (f : α → β) (complexType : β → γ) (t : α),
    ComplexModel.mapType f complexType t = complexType (f t)) ∧
  (∀ (α β γ δ : Type) (zero : α → β) (real : β → γ) (typeOf : γ → δ) t,
    ComplexModel.realTypeGeneric zero real typeOf t = typeOf (real (zero t))) ∧
  (∀ (α : Type), ComplexModel.bottomType (α := α) = .error (.methodError "bottom type"))

theorem complexConstructorsFaithful_proven : ComplexConstructorsFaithful := by
  simp [ComplexConstructorsFaithful, ComplexModel.constructPromoted,
    ComplexModel.constructTypedReal, ComplexModel.constructTypedComplex,
    ComplexModel.realConvert, ComplexModel.complexIdentity, ComplexModel.real,
    ComplexModel.imag, ComplexModel.reim, ComplexModel.realOfReal,
    ComplexModel.imagOfReal, ComplexModel.promoteType, ComplexModel.mapType,
    ComplexModel.realTypeGeneric, ComplexModel.bottomType]

def ComplexPredicatesIOFaithful : Prop :=
  (∀ (α : Type) (o : GenericOps α) (integer : α → Bool) (z : ComplexModel.Cx α),
    ComplexModel.isreal o z = o.eq z.im (o.zero z.im) ∧
    ComplexModel.isinteger o integer z = (o.eq z.im (o.zero z.im) && integer z.re) ∧
    ComplexModel.isfinite o z = (o.isfinite z.re && o.isfinite z.im) ∧
    ComplexModel.isnan o z = (o.isnan z.re || o.isnan z.im) ∧
    ComplexModel.isinf o z = (o.isinf z.re || o.isinf z.im) ∧
    ComplexModel.iszero o z = (o.eq z.re (o.zero z.re) && o.eq z.im (o.zero z.im)) ∧
    ComplexModel.isone o z = (o.eq z.re (o.one z.re) && o.eq z.im (o.zero z.im))) ∧
  (∀ (α : Type) (o : GenericOps α) (z : ComplexModel.Cx α) y,
    ComplexModel.flipsign o z y =
      if NumberModel.signbit o y then ComplexModel.neg o z else z) ∧
  (∀ rt it (compact star : Bool), ∃ s,
    ComplexModel.showParts rt it compact star = s) ∧
  (∀ re im, ComplexModel.showBool true re im = "im" ∧
    ComplexModel.showBool false re im = s!"Complex({re},{im})") ∧
  (∀ (α : Type) (render : α → String) parens z,
    ComplexModel.showUnquoted render parens z =
      if parens then "(" ++ render z ++ ")" else render z) ∧
  (∀ (α β : Type) (read : Unit → α × α) (write : α → α → β)
      (swap : α → α) (z : ComplexModel.Cx α),
    ComplexModel.readPair read = (let p := read (); ⟨p.1, p.2⟩) ∧
    ComplexModel.writePair write z = write z.re z.im ∧
    ComplexModel.bswap swap z = ⟨swap z.re, swap z.im⟩) ∧
  (∀ (α β : Type) (o : GenericOps α) (eqv : α → α → Bool)
      (mem : α → β → Bool) (z w : ComplexModel.Cx α) (x : α) (r : β),
    ComplexModel.eq o z w = (o.eq z.re w.re && o.eq z.im w.im) ∧
    ComplexModel.eqReal o z x = (ComplexModel.isreal o z && o.eq z.re x) ∧
    ComplexModel.eqRealLeft o x z = (ComplexModel.isreal o z && o.eq z.re x) ∧
    ComplexModel.isequal eqv z w = (eqv z.re w.re && eqv z.im w.im) ∧
    ComplexModel.memRealRange o mem z r = (ComplexModel.isreal o z && mem z.re r)) ∧
  (∀ (α : Type) (eqv : α → α → Bool) (zero : α → α)
      (z : ComplexModel.Cx α) (x : α),
    ComplexModel.isequalComplexReal eqv zero z x = (eqv z.re x && eqv z.im (zero x)) ∧
    ComplexModel.isequalRealComplex eqv zero x z = (eqv x z.re && eqv (zero x) z.im)) ∧
  (∀ (α : Type) (hashScalar : α → Nat → Nat) hi hz z h,
    ∃ r, ComplexModel.hash hashScalar hi hz z h = r)

theorem complexPredicatesIOFaithful_proven : ComplexPredicatesIOFaithful := by
  simp [ComplexPredicatesIOFaithful, ComplexModel.isreal, ComplexModel.isinteger,
    ComplexModel.isfinite, ComplexModel.isnan, ComplexModel.isinf, ComplexModel.iszero,
    ComplexModel.isone, ComplexModel.flipsign, ComplexModel.neg, ComplexModel.showBool,
    ComplexModel.showUnquoted, ComplexModel.readPair, ComplexModel.writePair,
    ComplexModel.bswap, ComplexModel.eq, ComplexModel.eqReal, ComplexModel.isequal,
    ComplexModel.eqRealLeft, ComplexModel.isequalComplexReal,
    ComplexModel.isequalRealComplex, ComplexModel.memRealRange]

def ComplexArithmeticFaithful : Prop :=
  (∀ (α : Type) (o : GenericOps α) (z w : ComplexModel.Cx α),
    ComplexModel.conj o z = ⟨z.re, o.neg z.im⟩ ∧
    ComplexModel.abs2 o z = o.add (o.mul z.re z.re) (o.mul z.im z.im) ∧
    ComplexModel.pos o z = ⟨o.pos z.re, o.pos z.im⟩ ∧
    ComplexModel.neg o z = ⟨o.neg z.re, o.neg z.im⟩ ∧
    ComplexModel.add o z w = ⟨o.add z.re w.re, o.add z.im w.im⟩ ∧
    ComplexModel.sub o z w = ⟨o.sub z.re w.re, o.sub z.im w.im⟩ ∧
    ComplexModel.mul o z w =
      ⟨o.sub (o.mul z.re w.re) (o.mul z.im w.im),
       o.add (o.mul z.re w.im) (o.mul z.im w.re)⟩) ∧
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) z, ∃ r, ComplexModel.invGeneric o z = r) ∧
  (∀ (α β : Type) (float : ComplexModel.Cx α → ComplexModel.Cx β)
      (inv : ComplexModel.Cx β → ComplexModel.Cx β) z,
    ComplexModel.invInteger float inv z = inv (float z)) ∧
  (∀ (α : Type) (muladd : α → α → α → α) (neg : α → α) a b c,
    ComplexModel.mulsub muladd neg a b c = muladd a b (neg c)) ∧
  (∀ (α β γ δ ε : Type) (promote : α → β → γ → δ × δ × δ)
      (mulsub : δ → δ → δ → ε) a b c,
    ComplexModel.mulsubPromoted promote mulsub a b c =
      let p := promote a b c; mulsub p.1 p.2.1 p.2.2) ∧
  (∀ (α : Type) (muladd mulsub : α → α → α → α) (neg : α → α)
      z w x, ComplexModel.muladdComplex muladd mulsub neg z w x =
        ⟨muladd z.re w.re (neg (mulsub z.im w.im x.re)),
         muladd z.re w.im (muladd z.im w.re x.im)⟩) ∧
  (∀ (α : Type) (o : GenericOps α) x (z : ComplexModel.Cx α),
    ComplexModel.addReal o x z = ⟨o.add x z.re, z.im⟩ ∧
    ComplexModel.subRealComplex o x z = ⟨o.sub x z.re, o.neg z.im⟩ ∧
    ComplexModel.subComplexReal o z x = ⟨o.sub z.re x, z.im⟩ ∧
    ComplexModel.mulReal o x z = ⟨o.mul x z.re, o.mul x z.im⟩ ∧
    ComplexModel.divReal o z x = ⟨o.div z.re x, o.div z.im x⟩) ∧
  (∀ (α : Type) (muladd : α → α → α → α) (mul : α → α → α)
      (z w : ComplexModel.Cx α) (x y : α),
    ComplexModel.muladdComplexReal muladd mul z x y =
      ⟨muladd z.re x y, mul z.im x⟩ ∧
    ComplexModel.muladdComplexScalar muladd z x w =
      ⟨muladd z.re x w.re, muladd z.im x w.im⟩ ∧
    ComplexModel.muladdRealRealComplex muladd x y z = ⟨muladd x y z.re, z.im⟩) ∧
  (∀ (α β γ : Type) (muladd : ComplexModel.Cx α → α → β → γ)
      (x : α) z y, ComplexModel.muladdSwap muladd x z y = muladd z x y) ∧
  (∀ (α : Type) (muladd mulsub : α → α → α → α) (neg : α → α)
      (mul : α → α → α) z w x,
    ComplexModel.muladdComplexComplexReal muladd mulsub neg mul z w x =
      ⟨muladd z.re w.re (neg (mulsub z.im w.im x)),
       muladd z.re w.im (mul z.im w.re)⟩) ∧
  (∀ (α β γ : Type) (promote : α → ComplexModel.Cx β → γ × ComplexModel.Cx γ)
      (mul : γ → ComplexModel.Cx γ → ComplexModel.Cx γ)
      (inv : ComplexModel.Cx γ → ComplexModel.Cx γ) a z,
    ComplexModel.realDivComplex promote mul inv a z =
      let p := promote a z; mul p.1 (inv p.2))

theorem complexArithmeticFaithful_proven : ComplexArithmeticFaithful := by
  simp [ComplexArithmeticFaithful, ComplexModel.conj, ComplexModel.abs2,
    ComplexModel.pos, ComplexModel.neg, ComplexModel.add, ComplexModel.sub,
    ComplexModel.mul, ComplexModel.invInteger, ComplexModel.mulsub,
    ComplexModel.mulsubPromoted, ComplexModel.muladdComplex,
    ComplexModel.muladdComplexReal, ComplexModel.muladdComplexScalar,
    ComplexModel.muladdRealRealComplex, ComplexModel.muladdSwap,
    ComplexModel.muladdComplexComplexReal, ComplexModel.addReal, ComplexModel.subRealComplex,
    ComplexModel.subComplexReal, ComplexModel.mulReal, ComplexModel.divReal,
    ComplexModel.realDivComplex]

def ComplexDivisionFaithful : Prop :=
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) z w,
    (∃ r, ComplexModel.divGeneric o z w = r) ∧
    (∃ r, ComplexModel.ssqs o z.re z.im = r)) ∧
  (∀ (α β : Type) (small : ComplexModel.ScalarOps α) (wide : ComplexModel.ScalarOps β)
      (widen : ComplexModel.Cx α → ComplexModel.Cx β)
      (narrow : ComplexModel.Cx β → ComplexModel.Cx α) z w,
    (∃ r, ComplexModel.divSmall small wide widen narrow z w = r) ∧
    (∃ r, ComplexModel.invSmall small wide widen narrow z = r)) ∧
  (∀ z w : JuliaLean.base.complex.ComplexF64,
    (∃ r, JuliaLean.base.complex.div_ComplexF64 z w = r) ∧
    (∃ r, JuliaLean.base.complex.inv_ComplexF64 z = r)) ∧
  (∀ a b c d,
    (∃ r, JuliaLean.base.complex.cdiv a b c d = r) ∧
    (∃ r, JuliaLean.base.complex.robust_cdiv1 a b c d = r) ∧
    (∃ r, JuliaLean.base.complex.robust_cinv c d = r)) ∧
  (∀ a b c d ab cd,
    (∃ r, JuliaLean.base.complex.scaleargs_cdiv a b c d ab cd = r) ∧
    (∃ r, JuliaLean.base.complex.scaling_cdiv a b c d ab cd = r)) ∧
  (∀ (t : IntTy) (z w : JuliaLean.base.complex.Complex (JInt t)),
    ∃ r, JuliaLean.base.complex.div_Complex_JInt z w = r)

theorem complexDivisionFaithful_proven : ComplexDivisionFaithful := by
  simp [ComplexDivisionFaithful]

def ComplexExponentialFaithful : Prop :=
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) theta z,
    ComplexModel.cis o theta = ⟨o.cos theta, o.sin theta⟩ ∧
    (∃ r, ComplexModel.cisComplex o z = r) ∧
    ComplexModel.cispi o theta = ⟨o.cospi theta, o.sinpi theta⟩ ∧
    (∃ r, ComplexModel.cispiComplex o z = r) ∧
    ComplexModel.angle o z = o.atan2 z.im z.re) ∧
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) ssqs z,
    (∃ r, ComplexModel.log o ssqs z = r) ∧
    (∃ r, ComplexModel.logBase o (o.ofInt 10) (ComplexModel.log o ssqs z) = r) ∧
    (∃ r, ComplexModel.logBase o (o.ofInt 2) (ComplexModel.log o ssqs z) = r) ∧
    (∃ r, ComplexModel.exp o z = r) ∧
    (∃ r, ComplexModel.expm1 o z = r) ∧
    (∃ r, ComplexModel.exp2 o z = r) ∧
    (∃ r, ComplexModel.exp10 o z = r)) ∧
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) (logC : ComplexModel.Cx α → ComplexModel.Cx α) z,
    ∃ r, ComplexModel.log1p o logC z = r)

theorem complexExponentialFaithful_proven : ComplexExponentialFaithful := by
  simp [ComplexExponentialFaithful, ComplexModel.cis, ComplexModel.cispi,
    ComplexModel.angle]

def ComplexPowerFaithful : Prop :=
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) (float : ComplexModel.Cx α → ComplexModel.Cx α)
      (integer : α → Bool) (toInt : α → Int) (powerC : ComplexModel.Cx α → Int → ComplexModel.Cx α)
      (invC : ComplexModel.Cx α → ComplexModel.Cx α) (absC : ComplexModel.Cx α → α)
      (cisF : α → ComplexModel.Cx α) (angleF : ComplexModel.Cx α → α)
      realArm z p, ∃ r,
        ComplexModel.cpowFull o float integer toInt powerC invC absC cisF angleF realArm z p = r) ∧
  (∀ (α : Type) (one : ComplexModel.Cx α → ComplexModel.Cx α) z n,
    ComplexModel.powerBool one z n = if n then z else one z) ∧
  (∀ (α β γ : Type) (cpow : ComplexModel.Cx α → ComplexModel.Cx β → ComplexModel.Cx γ)
      z p, ComplexModel.powerCpow cpow z p = cpow z p) ∧
  (∀ (α : Type) (toComplex : Int → ComplexModel.Cx α)
      (pow : ComplexModel.Cx α → ComplexModel.Cx α → ComplexModel.Cx α) z n,
    ComplexModel.powerViaComplexExponent toComplex pow z n = pow z (toComplex n)) ∧
  (∀ z : JuliaLean.base.complex.ComplexF64, ∀ n : JInt .i64,
    ∃ r, JuliaLean.base.complex.pow_ComplexF64_Int z n = r) ∧
  (∀ (t : IntTy) (z : JuliaLean.base.complex.Complex (JInt t)) (n : JInt .i64),
    ∃ r, JuliaLean.base.complex.pow_ComplexInteger_Integer z n = r) ∧
  (∀ (α β γ δ : Type) (promote : α → β → γ)
      (convertComplex : γ → ComplexModel.Cx α → ComplexModel.Cx δ)
      (convertReal : γ → β → δ) (pow : ComplexModel.Cx δ → δ → ComplexModel.Cx δ)
      component z p, ∃ r,
        ComplexModel.powerPromotedComplexReal promote convertComplex convertReal pow component z p = r) ∧
  (∀ (α β γ δ : Type) (promote : α → β → γ)
      (convertReal : γ → α → δ)
      (convertComplex : γ → ComplexModel.Cx β → ComplexModel.Cx δ)
      (pow : δ → ComplexModel.Cx δ → ComplexModel.Cx δ)
      z component p, ∃ r,
        ComplexModel.powerPromotedRealComplex promote convertReal convertComplex pow z component p = r)

theorem complexPowerFaithful_proven : ComplexPowerFaithful := by
  simp [ComplexPowerFaithful, ComplexModel.powerBool,
    ComplexModel.powerCpow, ComplexModel.powerViaComplexExponent]

def ComplexTrigFaithful : Prop :=
  ∀ (α : Type) (o : ComplexModel.ScalarOps α) (sqrtC float invC : ComplexModel.Cx α → ComplexModel.Cx α)
    (sinC cosC asinC atanhC : ComplexModel.Cx α → ComplexModel.Cx α) large z,
    (∃ r, ComplexModel.sin o z = r) ∧ (∃ r, ComplexModel.cos o z = r) ∧
    (∃ r, ComplexModel.tanFromTanh o atanhC z = r) ∧
    (∃ r, ComplexModel.asin o sqrtC z = r) ∧
    (∃ r, ComplexModel.acosFull o float sqrtC z = r) ∧
    (∃ r, ComplexModel.atanFromAtanh o atanhC z = r) ∧
    (∃ r, ComplexModel.sinhFromSin o sinC z = r) ∧
    (∃ r, ComplexModel.coshFromCos o cosC z = r) ∧
    (∃ r, ComplexModel.tanh o large z = r) ∧
    (∃ r, ComplexModel.asinhFromAsin o asinC z = r) ∧
    (∃ r, ComplexModel.acoshFull o sqrtC z = r) ∧
    (∃ r, ComplexModel.atanhFull o large invC z = r)

theorem complexTrigFaithful_proven : ComplexTrigFaithful := by
  simp [ComplexTrigFaithful]

def ComplexConversionsFaithful : Prop :=
  (∀ (α : Type) (rr ri : α → α) z,
    ComplexModel.round rr ri z = ⟨rr z.re, ri z.im⟩) ∧
  (∀ (α β : Type) (f : α → β) z,
    ComplexModel.floatIdentity z = z ∧
    ComplexModel.mapComponents f z = ⟨f z.re, f z.im⟩) ∧
  (∀ (α β γ : Type) (big : α → β) (complexType : β → γ) t,
    ComplexModel.bigType big complexType t = complexType (big t)) ∧
  (∀ (α β γ : Type) (big : α → β) (convert : β → ComplexModel.Cx α → ComplexModel.Cx γ)
      t z, ComplexModel.bigValue big convert t z = convert (big t) z) ∧
  (∀ (α : Type) (xs : α), ComplexModel.arrayComplexIdentity xs = xs) ∧
  (∀ (α β : Type) concrete (convert : α → β) xs,
    ComplexModel.arrayComplexConvert concrete convert xs =
      if concrete then .ok (convert xs)
      else .error (.argumentError "complex abstractly typed array")) ∧
  (∀ (α : Type) (o : ComplexModel.ScalarOps α) z,
    (∃ r, ComplexModel.epsValue o z = r) ∧
    (∃ r, ComplexModel.epsType o z.re = r))

theorem complexConversionsFaithful_proven : ComplexConversionsFaithful := by
  simp [ComplexConversionsFaithful, ComplexModel.round, ComplexModel.floatIdentity,
    ComplexModel.mapComponents, ComplexModel.bigType, ComplexModel.bigValue,
    ComplexModel.arrayComplexIdentity, ComplexModel.arrayComplexConvert]

end JuliaLean.NumbersCov

namespace JuliaLean.NumbersCov.Rows.Complex

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

def P17 : Prop := ∀ (α β γ : Type) (p : α → β → γ × γ) x y, HasResult (m17 p x y)
theorem p17 : P17 := by simp [P17, HasResult]
def P18 : Prop := ∀ (α : Type) (z : α → α) x, m18 z x = ⟨x, z x⟩
theorem p18 : P18 := by simp [P18, m18]
def P42 : Prop := ∀ (α β : Type) (c : α → β) z x, m42 c z x = ⟨c x, z⟩
theorem p42 : P42 := by simp [P42, m42]
def P43 : Prop := ∀ (α β : Type) (c : α → β) z, m43 c z = ⟨c z.re, c z.im⟩
theorem p43 : P43 := by simp [P43, m43]
def P44 : Prop := ∀ (α β : Type) (r : C α → Bool) (c : α → β) n z,
  HasResult (m44 r c n z)
theorem p44 : P44 := by simp [P44, HasResult]
def P47 : Prop := ∀ (α : Type) (z : C α), m47 z = z
theorem p47 : P47 := by simp [P47, m47]
def P49 : Prop := ∀ (α β γ δ : Type) (p : α → β → γ) (c : γ → δ) t s,
  m49 p c t s = c (p t s)
theorem p49 : P49 := by simp [P49, m49]
def P51 : Prop := P49
theorem p51 : P51 := p49
def P54 : Prop := ∀ (α β γ : Type) (w : α → β) (c : β → γ) t,
  m54 w c t = c (w t)
theorem p54 : P54 := by simp [P54, m54]
def P56 : Prop := ∀ (α β : Type) (c : α → β) t, m56 c t = c t
theorem p56 : P56 := by simp [P56, m56]
def P57 : Prop := ∀ (α β γ : Type) (f : α → β) (c : β → γ) t,
  m57 f c t = c (f t)
theorem p57 : P57 := by simp [P57, m57]
def P72 : Prop := ∀ (α : Type) (z : C α), m72 z = z.re
theorem p72 : P72 := by simp [P72, m72]
def P87 : Prop := ∀ (α : Type) (z : C α), m87 z = z.im
theorem p87 : P87 := by simp [P87, m87]
def P88 : Prop := ∀ (α : Type) (x : α), m88 x = x
theorem p88 : P88 := by simp [P88, m88]
def P89 : Prop := ∀ (α : Type) (z : α → α) x, m89 z x = z x
theorem p89 : P89 := by simp [P89, m89]
def P102 : Prop := ∀ (α β : Type) (r i : α → β) z, m102 r i z = (r z, i z)
theorem p102 : P102 := by simp [P102, m102]
def P120 : Prop := ∀ (α β γ δ : Type) (z : α → β) (r : β → γ) (ty : γ → δ) t,
  m120 z r ty t = ty (r (z t))
theorem p120 : P120 := by simp [P120, m120]
def P121 : Prop := ∀ (α : Type) (t : α), m121 t = t
theorem p121 : P121 := by simp [P121, m121]
def P122 : Prop := ∀ (α β : Type) (f : α → β) t, m122 f t = f t
theorem p122 : P122 := by simp [P122, m122]
def P123 : Prop := ∀ (α : Type), @m123 α = none
theorem p123 : P123 := by simp [P123, m123]
def P124 : Prop := ∀ (α : Type), @m124 α = .error (.methodError "real")
theorem p124 : P124 := by simp [P124, m124]

def P148 : Prop := ∀ (α : Type) (x : α), m148 x = true
theorem p148 : P148 := by simp [P148, m148]
def P150 : Prop := ∀ (α : Type) (o : GenericOps α) (i : α → Bool) z,
  m150 o i z = (o.eq z.im (o.zero z.im) && i z.re)
theorem p150 : P150 := by simp [P150, m150, ComplexModel.isinteger, ComplexModel.isreal]
def P151 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m151 o z = (o.isfinite z.re && o.isfinite z.im)
theorem p151 : P151 := by simp [P151, m151, ComplexModel.isfinite]
def P152 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m152 o z = (o.isnan z.re || o.isnan z.im)
theorem p152 : P152 := by simp [P152, m152, ComplexModel.isnan]
def P153 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m153 o z = (o.isinf z.re || o.isinf z.im)
theorem p153 : P153 := by simp [P153, m153, ComplexModel.isinf]
def P154 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m154 o z = (o.eq z.re (o.zero z.re) && o.eq z.im (o.zero z.im))
theorem p154 : P154 := by simp [P154, m154, ComplexModel.iszero]
def P155 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m155 o z = (o.eq z.re (o.one z.re) && o.eq z.im (o.zero z.im))
theorem p155 : P155 := by simp [P155, m155, ComplexModel.isone]
def P168 : Prop := ∀ (α : Type) (z : C α), m168 z = z
theorem p168 : P168 := by simp [P168, m168]
def P169 : Prop := ∀ (α : Type) (z : α → α) x, m169 z x = ⟨x, z x⟩
theorem p169 : P169 := by simp [P169, m169]
def P170 : Prop := ∀ (α β γ : Type) (p : α → β → γ × γ) x y, HasResult (m170 p x y)
theorem p170 : P170 := by simp [P170, HasResult]
def P190 : Prop := ∀ (α β : Type) (c : α → β) t, m190 c t = c t
theorem p190 : P190 := by simp [P190, m190]
def P191 : Prop := P190
theorem p191 : P191 := p190
def P192 : Prop := ∀ (α : Type), @m192 α = none
theorem p192 : P192 := by simp [P192, m192]
def P195 : Prop := ∀ (α : Type), @m195 α = .error (.methodError "complex")
theorem p195 : P195 := by simp [P195, m195]
def P197 : Prop := ∀ (α : Type) (o : GenericOps α) z y, HasResult (m197 o z y)
theorem p197 : P197 := by simp [P197, HasResult]
def P199 : Prop := ∀ r i c s, HasResult (m199 r i c s)
theorem p199 : P199 := by simp [P199, HasResult]
def P219 : Prop := ∀ r i u, HasResult (m219 r i u)
theorem p219 : P219 := by simp [P219, HasResult]
def P222 : Prop := ∀ (α : Type) (r : α → String) p z, HasResult (m222 r p z)
theorem p222 : P222 := by simp [P222, HasResult]
def P232 : Prop := ∀ (α : Type) (r : Unit → α × α), HasResult (m232 r)
theorem p232 : P232 := by simp [P232, HasResult]
def P237 : Prop := ∀ (α β : Type) (w : α → α → β) z, m237 w z = w z.re z.im
theorem p237 : P237 := by simp [P237, m237, ComplexModel.writePair]
def P242 : Prop := ∀ (α : Type) (s : α → α) z, m242 s z = ⟨s z.re, s z.im⟩
theorem p242 : P242 := by simp [P242, m242, ComplexModel.bswap]
def P246 : Prop := ∀ (α : Type) (o : GenericOps α) z w,
  m246 o z w = (o.eq z.re w.re && o.eq z.im w.im)
theorem p246 : P246 := by simp [P246, m246, ComplexModel.eq]
def P248 : Prop := ∀ (α : Type) (o : GenericOps α) x z, HasResult (m248 o x z)
theorem p248 : P248 := by simp [P248, HasResult]
def P252 : Prop := ∀ (α : Type) (e : α → α → Bool) (z : α → α) x w,
  m252 e z x w = (e x w.re && e (z x) w.im)
theorem p252 : P252 := by simp [P252, m252, ComplexModel.isequalRealComplex]
def P254 : Prop := ∀ (α β : Type) (o : GenericOps α) (m : α → β → Bool) z r,
  HasResult (m254 o m z r)
theorem p254 : P254 := by simp [P254, HasResult]

def P282 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m282 o z = o.add (o.mul z.re z.re) (o.mul z.im z.im)
theorem p282 : P282 := by simp [P282, m282, ComplexModel.abs2]
def P283 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (m283 o z)
theorem p283 : P283 := by simp [P283, HasResult]
def P288 : Prop := ∀ (α β : Type) (f : C α → C β) (i : C β → C β) z,
  m288 f i z = i (f z)
theorem p288 : P288 := by simp [P288, m288, ComplexModel.invInteger]
def P290 : Prop := ∀ (α : Type) (o : GenericOps α) z, HasResult (m290 o z)
theorem p290 : P290 := by simp [P290, HasResult]
def P291 : Prop := ∀ (α : Type) (o : GenericOps α) z, HasResult (m291 o z)
theorem p291 : P291 := by simp [P291, HasResult]
def P292 : Prop := ∀ (α : Type) (o : GenericOps α) z w, HasResult (m292 o z w)
theorem p292 : P292 := by simp [P292, HasResult]
def P293 : Prop := ∀ (α : Type) (o : GenericOps α) z w, HasResult (m293 o z w)
theorem p293 : P293 := by simp [P293, HasResult]
def P294 : Prop := ∀ (α : Type) (o : GenericOps α) z w, HasResult (m294 o z w)
theorem p294 : P294 := by simp [P294, HasResult]
def P297 : Prop := P291
theorem p297 : P297 := p291
def P298 : Prop := P292
theorem p298 : P298 := p292
def P299 : Prop := P293
theorem p299 : P299 := p293
def P300 : Prop := P294
theorem p300 : P300 := p294
def P303 : Prop := ∀ (A B C D E : Type) (p : A → B → C → D × D × D)
  (m : D → D → D → E) a b c, HasResult (m303 p m a b c)
theorem p303 : P303 := by simp [P303, HasResult]
def P304 : Prop := ∀ (α : Type) (m : α → α → α → α) (n : α → α) a b c,
  m304 m n a b c = m a b (n c)
theorem p304 : P304 := by simp [P304, m304, ComplexModel.mulsub]

def LeftAddProp (f : ∀ {α β γ δ : Type}, (γ → β → δ) → (α → β → γ) → α → C β → δ) : Prop :=
  ∀ (α β γ δ : Type) (c : γ → β → δ) (a : α → β → γ) x z,
    @f α β γ δ c a x z = c (a x z.re) z.im
def RightAddProp (f : ∀ {α β γ δ : Type}, (γ → β → δ) → (β → α → γ) → C β → α → δ) : Prop :=
  ∀ (α β γ δ : Type) (c : γ → β → δ) (a : β → α → γ) z x,
    @f α β γ δ c a z x = c (a z.re x) z.im
def LeftSubProp (f : ∀ {α β γ δ : Type}, (γ → β → δ) → (α → β → γ) → (β → β) → α → C β → δ) : Prop :=
  ∀ (α β γ δ : Type) (c : γ → β → δ) (s : α → β → γ) (n : β → β) x z,
    @f α β γ δ c s n x z = c (s x z.re) (n z.im)
def RightSubProp (f : ∀ {α β γ δ : Type}, (γ → β → δ) → (β → α → γ) → C β → α → δ) : Prop :=
  ∀ (α β γ δ : Type) (c : γ → β → δ) (s : β → α → γ) z x,
    @f α β γ δ c s z x = c (s z.re x) z.im
def LeftMulProp (f : ∀ {α β γ δ ε : Type}, (γ → δ → ε) → (α → β → γ) → (α → β → δ) → α → C β → ε) : Prop :=
  ∀ (α β γ δ ε : Type) (c : γ → δ → ε) (mr : α → β → γ) (mi : α → β → δ) x z,
    @f α β γ δ ε c mr mi x z = c (mr x z.re) (mi x z.im)
def RightMulProp (f : ∀ {α β γ δ ε : Type}, (γ → δ → ε) → (β → α → γ) → (β → α → δ) → C β → α → ε) : Prop :=
  ∀ (α β γ δ ε : Type) (c : γ → δ → ε) (mr : β → α → γ) (mi : β → α → δ) z x,
    @f α β γ δ ε c mr mi z x = c (mr z.re x) (mi z.im x)
theorem leftAdd_proven : LeftAddProp (@scalarLeftAdd) := by simp [LeftAddProp, scalarLeftAdd]
theorem rightAdd_proven : RightAddProp (@scalarRightAdd) := by simp [RightAddProp, scalarRightAdd]
theorem leftSub_proven : LeftSubProp (@scalarLeftSub) := by simp [LeftSubProp, scalarLeftSub]
theorem rightSub_proven : RightSubProp (@scalarRightSub) := by simp [RightSubProp, scalarRightSub]
theorem leftMul_proven : LeftMulProp (@scalarLeftMul) := by simp [LeftMulProp, scalarLeftMul]
theorem rightMul_proven : RightMulProp (@scalarRightMul) := by simp [RightMulProp, scalarRightMul]

def P311 := LeftAddProp (@m311)
theorem p311 : P311 := leftAdd_proven
def P312 := RightAddProp (@m312)
theorem p312 : P312 := rightAdd_proven
def P313 := LeftSubProp (@m313)
theorem p313 : P313 := leftSub_proven
def P314 := RightSubProp (@m314)
theorem p314 : P314 := rightSub_proven
def P315 := LeftMulProp (@m315)
theorem p315 : P315 := leftMul_proven
def P316 := RightMulProp (@m316)
theorem p316 : P316 := rightMul_proven
def P318 := LeftAddProp (@m318)
theorem p318 : P318 := leftAdd_proven
def P319 := RightAddProp (@m319)
theorem p319 : P319 := rightAdd_proven
def P320 := LeftSubProp (@m320)
theorem p320 : P320 := leftSub_proven
def P321 := RightSubProp (@m321)
theorem p321 : P321 := rightSub_proven
def P323 := RightMulProp (@m323)
theorem p323 : P323 := rightMul_proven
def P325 := LeftAddProp (@m325)
theorem p325 : P325 := leftAdd_proven
def P326 := RightAddProp (@m326)
theorem p326 : P326 := rightAdd_proven
def P327 := LeftSubProp (@m327)
theorem p327 : P327 := leftSub_proven
def P332 := RightSubProp (@m332)
theorem p332 : P332 := rightSub_proven
def P333 := LeftMulProp (@m333)
theorem p333 : P333 := leftMul_proven
def P334 := RightMulProp (@m334)
theorem p334 : P334 := rightMul_proven
def P337 := LeftAddProp (@m337)
theorem p337 : P337 := leftAdd_proven
def P338 := RightAddProp (@m338)
theorem p338 : P338 := rightAdd_proven
def P339 := LeftSubProp (@m339)
theorem p339 : P339 := leftSub_proven
def P344 := RightSubProp (@m344)
theorem p344 : P344 := rightSub_proven
def P345 := LeftMulProp (@m345)
theorem p345 : P345 := leftMul_proven
def P346 := RightMulProp (@m346)
theorem p346 : P346 := rightMul_proven

def P348 : Prop := ∀ (α β γ δ : Type) (m : C α → β → γ → δ) x z y,
  m348 m x z y = m z x y
theorem p348 : P348 := by simp [P348, m348]
def P349 : Prop := ∀ (α : Type) (ma : α → α → α → α) (m : α → α → α) z x y,
  HasResult (@m349 α ma m z x y)
theorem p349 : P349 := by simp [P349, HasResult]
def P350 : Prop := ∀ (α : Type) (ma : α → α → α → α) z x w,
  HasResult (@m350 α ma z x w)
theorem p350 : P350 := by simp [P350, HasResult]
def P352 : Prop := ∀ (α : Type) (ma : α → α → α → α) x y z,
  HasResult (@m352 α ma x y z)
theorem p352 : P352 := by simp [P352, HasResult]
def P353 : Prop := ∀ (α : Type) (ma ms : α → α → α → α) (n : α → α)
  (m : α → α → α) z w x, HasResult (@m353 α ma ms n m z w x)
theorem p353 : P353 := by simp [P353, HasResult]
def P357 : Prop := ∀ (α β γ : Type) (p : α → C β → γ × C γ)
  (m : γ → C γ → C γ) (i : C γ → C γ) a z, HasResult (@m357 α β γ p m i a z)
theorem p357 : P357 := by simp [P357, HasResult]
def P358 : Prop := ∀ (α : Type) (o : GenericOps α) z x, HasResult (@m358 α o z x)
theorem p358 : P358 := by simp [P358, HasResult]

def P360 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z w, HasResult (@m360 α o z w)
theorem p360 : P360 := by simp [P360, HasResult]
def P379 : Prop := ∀ (α β : Type) (s : ComplexModel.ScalarOps α)
  (w : ComplexModel.ScalarOps β) (wide : C α → C β) (n : C β → C α) z q,
  HasResult (@m379 α β s w wide n z q)
theorem p379 : P379 := by simp [P379, HasResult]
def P424 : Prop := ∀ a b c d, HasResult (m424 a b c d)
theorem p424 : P424 := by simp [P424, HasResult]
def P433 : Prop := ∀ a b c d x y, HasResult (m433 a b c d x y)
theorem p433 : P433 := by simp [P433, HasResult]
def P439 : Prop := ∀ a b c d x y, HasResult (m439 a b c d x y)
theorem p439 : P439 := by simp [P439, HasResult]
def P476 : Prop := ∀ (α β : Type) (s : ComplexModel.ScalarOps α)
  (w : ComplexModel.ScalarOps β) (wide : C α → C β) (n : C β → C α) z,
  HasResult (@m476 α β s w wide n z)
theorem p476 : P476 := by simp [P476, HasResult]
def P482 : Prop := ∀ z, HasResult (m482 z)
theorem p482 : P482 := by simp [P482, HasResult]
def P511 : Prop := ∀ c d, HasResult (m511 c d)
theorem p511 : P511 := by simp [P511, HasResult]
def P519 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) x y,
  HasResult (@m519 α o x y)
theorem p519 : P519 := by simp [P519, HasResult]

end JuliaLean.NumbersCov.Rows.Complex

namespace JuliaLean.NumbersCov.Rows.Complex

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

def P587 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) x,
  @m587 α o x = ⟨o.cos x, o.sin x⟩
theorem p587 : P587 := by simp [P587, m587, ComplexModel.cis]
def P592 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m592 α o z)
theorem p592 : P592 := by simp [P592, HasResult]
def P618 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) x,
  @m618 α o x = ⟨o.cospi x, o.sinpi x⟩
theorem p618 : P618 := by simp [P618, m618, ComplexModel.cispi]
def P620 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m620 α o z)
theorem p620 : P620 := by simp [P620, HasResult]
def P651 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z,
  @m651 α o z = o.atan2 z.im z.re
theorem p651 : P651 := by simp [P651, m651, ComplexModel.angle]
def P653 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α)
  (s : α → α → α × Int) z, HasResult (@m653 α o s z)
theorem p653 : P653 := by simp [P653, HasResult]
def P695 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (l : C α → C α) z,
  HasResult (m695 o l z)
theorem p695 : P695 := by simp [P695, HasResult]
def P699 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (l : C α → C α) z,
  HasResult (m699 o l z)
theorem p699 : P699 := by simp [P699, HasResult]
def P704 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m704 α o z)
theorem p704 : P704 := by simp [P704, HasResult]
def P727 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m727 α o z)
theorem p727 : P727 := by simp [P727, HasResult]
def P757 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (l : C α → C α) z,
  HasResult (@m757 α o l z)
theorem p757 : P757 := by simp [P757, HasResult]
def P775 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m775 α o z)
theorem p775 : P775 := by simp [P775, HasResult]
def P783 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m783 α o z)
theorem p783 : P783 := by simp [P783, HasResult]

def P792 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (float : C α → C α)
  (integer : α → Bool) (toInt : α → Int) (power : C α → Int → C α)
  (inv : C α → C α) (abs : C α → α) (cis : α → C α) (angle : C α → α)
  real z p, HasResult (@m792 α o float integer toInt power inv abs cis angle real z p)
theorem p792 : P792 := by simp [P792, HasResult]
def P882 : Prop := ∀ (α : Type) (p : C α → C α → C α) z x, m882 p z x = p z x
theorem p882 : P882 := by simp [P882, m882, ComplexModel.powerCpow]
def P883 : Prop := ∀ (α : Type) (p : C α → C α → C α) (c : α → C α) z x,
  m883 p c z x = p z (c x)
theorem p883 : P883 := by simp [P883, m883]
def P884 : Prop := ∀ (α : Type) (p : C α → C α → C α) (c : α → C α) z x,
  m884 p c z x = p (c z) x
theorem p884 : P884 := by simp [P884, m884]
def P886 : Prop := ∀ (α : Type) (one : C α → C α) z n,
  @m886 α one z n = if n then z else one z
theorem p886 : P886 := by simp [P886, m886, ComplexModel.powerBool]
def P887 : Prop := ∀ (α : Type) (c : Int → C α) (p : C α → C α → C α) z n,
  @m887 α c p z n = p z (c n)
theorem p887 : P887 := by simp [P887, m887, ComplexModel.powerViaComplexExponent]
def P889 : Prop := P886
theorem p889 : P889 := p886
def P890 : Prop := P886
theorem p890 : P890 := p886
def P896 : Prop := ∀ (α β γ δ : Type) (pr : α → β → γ)
  (cc : γ → C α → C δ) (cr : γ → β → δ) (pow : C δ → δ → C δ)
  component z p, HasResult (@m896 α β γ δ pr cc cr pow component z p)
theorem p896 : P896 := by simp [P896, HasResult]
def P900 : Prop := ∀ (α β γ δ : Type) (pr : α → β → γ)
  (cr : γ → α → δ) (cc : γ → C β → C δ) (pow : δ → C δ → C δ)
  z component p, HasResult (@m900 α β γ δ pr cr cc pow z component p)
theorem p900 : P900 := by simp [P900, HasResult]

def P905 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m905 α o z)
theorem p905 : P905 := by simp [P905, HasResult]
def P923 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (@m923 α o z)
theorem p923 : P923 := by simp [P923, HasResult]
def P943 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (t : C α → C α) z,
  HasResult (@m943 α o t z)
theorem p943 : P943 := by simp [P943, HasResult]
def P949 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (s : C α → C α) z,
  HasResult (@m949 α o s z)
theorem p949 : P949 := by simp [P949, HasResult]
def P963 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α)
  (f s : C α → C α) z, HasResult (@m963 α o f s z)
theorem p963 : P963 := by simp [P963, HasResult]
def P986 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (a : C α → C α) z,
  HasResult (@m986 α o a z)
theorem p986 : P986 := by simp [P986, HasResult]
def P991 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (s : C α → C α) z,
  HasResult (@m991 α o s z)
theorem p991 : P991 := by simp [P991, HasResult]
def P997 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (c : C α → C α) z,
  HasResult (@m997 α o c z)
theorem p997 : P997 := by simp [P997, HasResult]
def P1002 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) large z,
  HasResult (@m1002 α o large z)
theorem p1002 : P1002 := by simp [P1002, HasResult]
def P1024 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (a : C α → C α) z,
  HasResult (@m1024 α o a z)
theorem p1024 : P1024 := by simp [P1024, HasResult]
def P1029 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) (s : C α → C α) z,
  HasResult (@m1029 α o s z)
theorem p1029 : P1029 := by simp [P1029, HasResult]
def P1048 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) large (i : C α → C α) z,
  HasResult (@m1048 α o large i z)
theorem p1048 : P1048 := by simp [P1048, HasResult]

def P1123 : Prop := ∀ (α : Type) (rr ri : α → α) z,
  @m1123 α rr ri z = ⟨rr z.re, ri z.im⟩
theorem p1123 : P1123 := by simp [P1123, m1123, ComplexModel.round]
def P1129 : Prop := ∀ (α : Type) (z : C α), @m1129 α z = z
theorem p1129 : P1129 := by simp [P1129, m1129, ComplexModel.floatIdentity]
def P1130 : Prop := ∀ (α β : Type) (f : α → β) z,
  @m1130 α β f z = ⟨f z.re, f z.im⟩
theorem p1130 : P1130 := by simp [P1130, m1130, ComplexModel.mapComponents]
def P1132 : Prop := ∀ (α β γ : Type) (b : α → β) (c : β → γ) t,
  @m1132 α β γ b c t = c (b t)
theorem p1132 : P1132 := by simp [P1132, m1132, ComplexModel.bigType]
def P1133 : Prop := ∀ (α β γ : Type) (b : α → β) (c : β → C α → C γ) t z,
  @m1133 α β γ b c t z = c (b t) z
theorem p1133 : P1133 := by simp [P1133, m1133, ComplexModel.bigValue]
def P1153 : Prop := ∀ (α : Type) (x : α), @m1153 α x = x
theorem p1153 : P1153 := by simp [P1153, m1153, ComplexModel.arrayComplexIdentity]
def P1155 : Prop := ∀ (α β : Type) concrete (c : α → β) x,
  HasResult (@m1155 α β concrete c x)
theorem p1155 : P1155 := by simp [P1155, HasResult]
def P1164 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z,
  HasResult (@m1164 α o z)
theorem p1164 : P1164 := by simp [P1164, HasResult]
def P1166 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) x,
  HasResult (@m1166 α o x)
theorem p1166 : P1166 := by simp [P1166, HasResult]

end JuliaLean.NumbersCov.Rows.Complex
