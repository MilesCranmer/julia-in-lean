import JuliaLean.base.rational
import JuliaLean.Proofs.base.number.numberscov_common

namespace JuliaLean.NumbersCov

open JuliaLean

/-! ## `base/rational.jl` -/

open JuliaLean.IntArith.Rational

def RationalConstructionMethods : Prop :=
  (∀ (t : IntTy) (n d : JInt t), ofInts n d = construct t n d) ∧
  (∀ (t : IntTy) (n : JInt t), ofInt n = Rat.mk n (JInt.lit t 1)) ∧
  (∀ (t : IntTy) (x : Rat t), numerator x = x.num ∧ denominator x = x.den) ∧
  (∀ (t : IntTy) (n d : JInt t), ∃ r, checkedDen n d = r) ∧
  (∀ (t s : IntTy) (n d : JInt s), ∃ r, construct t n d = r) ∧
  (∀ (t s : IntTy) (x : Rat s), ∃ r, convertRat t x = r) ∧
  (∀ (t : IntTy), ∃ lo hi, RationalModel.typemin t = lo ∧ RationalModel.typemax t = hi)

theorem rationalConstructionMethods_proven : RationalConstructionMethods := by
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  constructor
  · intros; exact ⟨rfl, rfl⟩
  constructor
  · intros; exact ⟨_, rfl⟩
  constructor
  · intros; exact ⟨_, rfl⟩
  constructor
  · intros; exact ⟨_, rfl⟩
  · intro t; exact ⟨_, _, rfl, rfl⟩

def RationalIOAndComplexDivision : Prop :=
  (∀ (α : Type) (render : α → String) (isOne : α → Bool) (typed : Bool) (n d : α),
    RationalModel.showRat render isOne typed n d =
      if isOne d && typed then render n else render n ++ "//" ++ render d) ∧
  (∀ (α β : Type) (write : α → α → β) (n d : α),
    RationalModel.writePair write n d = write n d) ∧
  (∀ (α β γ δ ε : Type) (exactInv : RationalModel.Pair α → RationalModel.Pair α × β)
      (mul : γ → RationalModel.Pair α → δ) (ratDiv : δ → β → ε)
      (x : γ) (y : RationalModel.Pair α),
    RationalModel.divByComplex exactInv mul ratDiv x y =
      let p := exactInv y; ratDiv (mul x p.1) p.2)

theorem rationalIOAndComplexDivision_proven : RationalIOAndComplexDivision := by
  simp [RationalIOAndComplexDivision, RationalModel.showRat, RationalModel.writePair,
    RationalModel.divByComplex]

def RationalPromotionAndPowers : Prop :=
  (∀ (α β γ δ : Type) (promote : α → β → γ) (ratType : γ → δ) (a : α) (b : β),
    RationalModel.promoteComponent promote ratType a b = ratType (promote a b)) ∧
  (∀ (α β : Type) (f : α → β) (z : RationalModel.Pair α),
    RationalModel.rationalizeComplex f z = ⟨f z.re, f z.im⟩) ∧
  (∀ (α β γ δ : Type) (div : α → α → β) (pow : γ → β → δ)
      (x : γ) (n d : α),
    RationalModel.powerRationalExponent div pow x n d = pow x (div n d)) ∧
  (∀ (t : IntTy) (x : JuliaLean.Float.F64),
    (∃ r, JuliaLean.Promotion.rationalize t x = r) ∧
    (∃ r, JuliaLean.Promotion.rationalOfF64 t x = r))

theorem rationalPromotionAndPowers_proven : RationalPromotionAndPowers := by
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  · intros; exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

def RationalArithmeticMethods : Prop :=
  (∀ (t : IntTy) (x y : Rat t),
    mul x y = do
      let p ← divgcd x.num y.den
      let q ← divgcd x.den y.num
      let n ← JuliaLean.IntArith.Checked.checkedMul p.1 q.2
      let d ← JuliaLean.IntArith.Checked.checkedMul q.1 p.2
      return ⟨n, d⟩) ∧
  (∀ (t : IntTy) (x : Rat t), inv x = checkedDen x.den x.num) ∧
  (∀ (t : IntTy) (x y : Rat t),
    (∃ r, add x y = r) ∧ (∃ r, sub x y = r) ∧
    (∃ r, rem x y = r) ∧ (∃ r, mod x y = r)) ∧
  (∀ (t : IntTy) (x : Rat t), ∃ r, neg x = r)

theorem rationalArithmeticMethods_proven : RationalArithmeticMethods := by
  constructor
  · intro t x y; rfl
  constructor
  · intros; rfl
  constructor
  · intro t x y
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · intro t x; exact ⟨_, rfl⟩

def RationalComparisonMethods : Prop :=
  (∀ (t : IntTy) (x y : Rat t), eq x y =
    (decide (x.den.val = y.den.val) && decide (x.num.val = y.num.val))) ∧
  (∀ (t : IntTy) (x : Rat t), RationalModel.isinteger x = (x.den.val == 1) ∧
    RationalModel.iszero x = (x.num.val == 0) ∧
    RationalModel.isone x = (x.num.val == 1 && x.den.val == 1)) ∧
  (∀ (t s : IntTy) (x : Rat t) (y : Rat s),
    (∃ r, lt x y = r) ∧ (∃ r, le x y = r) ∧ (∃ r, cmp @lt x y = r)) ∧
  (∀ (t s : IntTy) (x : Rat t) (y : JInt s),
    eqInt x y = (decide (x.den.val = 1) && decide (x.num.val = y.val)))

theorem rationalComparisonMethods_proven : RationalComparisonMethods := by
  constructor
  · intros; rfl
  constructor
  · intros
    simp [RationalModel.isinteger, RationalModel.iszero, RationalModel.isone]
  constructor
  · intros; exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · intros; rfl

def RationalRoundingMethods : Prop :=
  (∀ (t : IntTy) (x y : Rat t), fld x y = quotient x y .down) ∧
  (∀ (t : IntTy) (x y : Rat t), cld x y = quotient x y .up) ∧
  (∀ (t : IntTy) (x : Rat t), trunc t x = round t x .toZero)

theorem rationalRoundingMethods_proven : RationalRoundingMethods := by
  simp [RationalRoundingMethods, fld, cld, trunc]

def RationalIntegerTolerance : Prop :=
  (∀ x, RationalModel.rationalizeIntegerDefault x = ⟨x, 1⟩) ∧
  ∀ (t : IntTy) (x tol : Int), 0 ≤ tol →
      (∃ q, t.min ≤ q ∧ q ≤ t.max ∧ Int.natAbs (x - q) ≤ tol.toNat) →
      (RationalModel.rationalizeInteger t x tol).den ≠ 0

theorem rationalizeIntegerWithinTolerance_refuted : ¬ RationalIntegerTolerance := by
  intro h
  have bad := h.2 .i8 128 1 (by decide) ⟨127, by decide, by decide, by decide⟩
  exact bad (by decide)

def RationalAccessAndRange : Prop :=
  (∀ (t : IntTy) (x : Rat t), RationalModel.decompose x = (x.num.val, 0, x.den.val)) ∧
  (∀ (t : IntTy) (first last : Rat t),
    RationalModel.rangeLength first last = do
      let d ← JInt.div (last.num - first.num + first.den) first.den
      return d)

theorem rationalAccessAndRange_proven : RationalAccessAndRange := by
  simp [RationalAccessAndRange, RationalModel.decompose, RationalModel.rangeLength]

def RationalNumberTheoryMethods : Prop :=
  (∀ (α : Type) (gcd lcm : α → α → α) (x y : α × α),
    RationalModel.gcd gcd lcm x y = (gcd x.1 y.1, lcm x.2 y.2) ∧
    RationalModel.lcm gcd lcm x y = (lcm x.1 y.1, gcd x.2 y.2)) ∧
  (∀ (t : IntTy) (x : Rat t), RationalModel.decompose x = (x.num.val, 0, x.den.val)) ∧
  (∀ (t : IntTy) (x : Rat t) (h : JuliaLean.Promotion.HTerm),
    ∃ r, JuliaLean.Promotion.hashRat64 x h = r) ∧
  (∀ (t : IntTy) (first last : Rat t) (empty : Bool),
    ∃ r, RationalModel.checkedRangeLength first last empty = r)

theorem rationalNumberTheoryMethods_proven : RationalNumberTheoryMethods := by
  constructor
  · intros; exact ⟨rfl, rfl⟩
  constructor
  · intros; rfl
  constructor
  · intros; exact ⟨_, rfl⟩
  · intros; exact ⟨_, rfl⟩

def RationalConstructionFaithful : Prop :=
  (∀ (t : IntTy) (n d : JInt t), RationalModel.unsafeRat n d = Rat.mk n d) ∧
  (∀ (t s : IntTy) (n : JInt t) (d : JInt s),
    (∃ r, RationalModel.unsafeMixed n d = r) ∧
    (∃ r, RationalModel.checkedDenMixed n d = r)) ∧
  (∀ (α : Type) (name : String), RationalModel.throwZero (α := α) name =
    .error (.argumentError name)) ∧
  (∀ (t s u : IntTy) (n : JInt s) (d : JInt u), ∃ r, construct t n d = r) ∧
  (∀ (t s : IntTy) (n : JInt t) (d : JInt s), ∃ r, ofMixedInts n d = r) ∧
  (∀ (t : IntTy) (n : JInt t), ofInt n = ⟨n, JInt.lit t 1⟩) ∧
  (∀ (t s : IntTy) (n : JInt t) (d : JInt s), ∃ r, divgcd n d = r) ∧
  (∀ (t s : IntTy) (x : Rat s), ∃ r, convertRat t x = r) ∧
  (∀ (t : IntTy) (x : Rat t),
    (∃ r, RationalModel.boolOfRat x = r) ∧
    (∀ target, ∃ r, RationalModel.intOfRat target x = r) ∧
    numerator x = x.num ∧ denominator x = x.den) ∧
  (∀ (α : Type) (one : α → α) (x : α),
    RationalModel.numeratorIntegral x = x ∧
    RationalModel.denominatorIntegral one x = one x) ∧
  (∀ (α β : Type) (den : α → β) (lcm : β → β → β)
      (real imag : α → α) (z : α), RationalModel.denominatorComplex den lcm real imag z =
        lcm (den (real z)) (den (imag z))) ∧
  (∀ (α β γ : Type) (num den : α → β) (mul div : β → β → β)
      (complex : β → β → γ) (real imag : α → α) z common,
    ∃ r, RationalModel.numeratorComplex num den mul div complex real imag z common = r)

theorem rationalConstructionFaithful_proven : RationalConstructionFaithful := by
  simp [RationalConstructionFaithful, RationalModel.unsafeRat, RationalModel.throwZero,
    ofInt, numerator, denominator, RationalModel.numeratorIntegral,
    RationalModel.denominatorIntegral, RationalModel.denominatorComplex]

def RationalIOComplexDivisionFaithful : Prop :=
  (∀ (t : IntTy) (n d : JInt t), ofInts n d = construct t n d) ∧
  (∀ (t : IntTy) (x : Rat t) (y : JInt t), ∃ r, divInt x y = r) ∧
  (∀ (t : IntTy) (x : JInt t) (y : Rat t), ∃ r, intDiv x y = r) ∧
  (∀ (t : IntTy) (x y : Rat t), ∃ r, div x y = r) ∧
  (∀ (t : IntTy) (z : RationalModel.Pair (JInt t)),
    ∃ r, RationalModel.complexExactInvInt z = r) ∧
  (∀ (α β γ δ ε : Type) (exactInv : RationalModel.Pair α → RationalModel.Pair α × β)
      (mul : γ → RationalModel.Pair α → δ) (ratDiv : δ → β → ε)
      (x : γ) (y : RationalModel.Pair α),
    RationalModel.divByComplex exactInv mul ratDiv x y =
      let p := exactInv y; ratDiv (mul x p.1) p.2) ∧
  (∀ (α β γ : Type) (ratDiv : α → β → γ) (z : RationalModel.Pair α) y,
    RationalModel.complexDivReal ratDiv z y =
      ⟨ratDiv z.re y, ratDiv z.im y⟩) ∧
  (∀ (t : IntTy) (x y : RationalModel.Pair (JInt t)),
    ∃ r, RationalModel.complexIntDiv x y = r) ∧
  (∀ (α β γ : Type) (broadcast : α → β → γ) (xs : α) (y : β),
    RationalModel.arrayExactDiv broadcast xs y = broadcast xs y) ∧
  (∀ (α : Type) (render : α → String) (isOne : α → Bool)
      (typed : Bool) (n d : α), RationalModel.showRat render isOne typed n d =
        if isOne d && typed then render n else render n ++ "//" ++ render d) ∧
  (∀ (α β : Type) (read : Unit → α × α) (write : α → α → β) (n d : α),
    RationalModel.readPair read = read () ∧ RationalModel.writePair write n d = write n d) ∧
  (∀ (α β : Type) (parse : String → α) (construct : α → α → β) parts,
    ∃ r, RationalModel.parseParts parse construct parts = r)

theorem rationalIOComplexDivisionFaithful_proven : RationalIOComplexDivisionFaithful := by
  simp [RationalIOComplexDivisionFaithful, ofInts, RationalModel.divByComplex,
    RationalModel.complexDivReal, RationalModel.arrayExactDiv,
    RationalModel.showRat, RationalModel.readPair,
    RationalModel.writePair]

def RationalPromotionPowersFaithful : Prop :=
  (∀ (t : IntTy) (x : Rat t), JuliaLean.Promotion.ratToF64 x =
    JuliaLean.Float.F64.div (JuliaLean.Float.F64.ofJInt x.num)
      (JuliaLean.Float.F64.ofJInt x.den)) ∧
  (∀ (α β γ : Type) (first : α → β) (second : β → γ) (x : α),
    RationalModel.convertVia first second x = second (first x)) ∧
  (∀ (α β γ : Type) (big : α → β) (unsafeCtor : β → β → γ) (n d : α),
    RationalModel.bigRat big unsafeCtor n d = unsafeCtor (big n) (big d)) ∧
  (∀ (α β γ δ : Type) (promote : α → β → γ) (ratType : γ → δ) (a : α) (b : β),
    RationalModel.promoteComponent promote ratType a b = ratType (promote a b)) ∧
  (∀ (α β γ : Type) (widen : α → β) (ratType : β → γ) (a : α),
    RationalModel.widenType widen ratType a = ratType (widen a)) ∧
  (∀ (α β : Type) (float : α → β) t,
    RationalModel.floatType float t = float t) ∧
  (∀ (α : Type),
    RationalModel.throwNegateUnsigned (α := α) =
      .error (.overflowError "cannot negate unsigned number") ∧
    RationalModel.bottomRationalize (α := α) = .error (.methodError "rationalize")) ∧
  (∀ (t : IntTy) (x : JuliaLean.Float.F64),
    (∃ r, JuliaLean.Promotion.rationalize t x = r) ∧
    (∃ r, JuliaLean.Promotion.rationalOfF64 t x = r)) ∧
  (∀ (α β : Type) (rationalize : α → β) (z : RationalModel.Pair α),
    RationalModel.rationalizeComplex rationalize z =
      ⟨rationalize z.re, rationalize z.im⟩) ∧
  (∀ (α β : Type) (convert : α → Jl β) (rf : Unit → Jl β) (x : α)
      (un fit tol : Bool), ∃ r, RationalModel.rationalizeRat convert rf x un fit tol = r) ∧
  (∀ (α β γ δ : Type) (div : α → α → β) (pow : γ → β → δ)
      (x : γ) (n d : α),
    RationalModel.powerRationalExponent div pow x n d = pow x (div n d)) ∧
  (∀ (α : Type) (one : RationalModel.Pair α → RationalModel.Pair α)
      (z : RationalModel.Pair α) (n : Bool),
    RationalModel.powerBool one z n = if n then z else one z) ∧
  (∀ (α : Type) (nonnegative : Int → Bool) (pow : α → Int → α)
      (inverse : α → α) (x : α) (n : Int),
    RationalModel.powerInteger nonnegative pow inverse x n =
      if nonnegative n then pow x n else pow (inverse x) (-n)) ∧
  (∀ (α : Type) (sub mul div add : α → α → α) (j d a b : α),
    RationalModel.lerpi sub mul div add j d a b =
      add (div (mul (sub d j) a) d) (div (mul j b) d)) ∧
  (∀ (t : IntTy) (x : Rat t), RationalModel.iszero x = (x.num.val == 0) ∧
    RationalModel.isone x = (x.num.val == 1 && x.den.val == 1))

theorem rationalPromotionPowersFaithful_proven : RationalPromotionPowersFaithful := by
  simp [RationalPromotionPowersFaithful, JuliaLean.Promotion.ratToF64,
    RationalModel.convertVia, RationalModel.bigRat, RationalModel.promoteComponent,
    RationalModel.widenType, RationalModel.rationalizeComplex,
    RationalModel.floatType, RationalModel.throwNegateUnsigned,
    RationalModel.bottomRationalize,
    RationalModel.powerRationalExponent, RationalModel.powerBool,
    RationalModel.powerInteger, RationalModel.lerpi, RationalModel.iszero,
    RationalModel.isone]

def RationalArithmeticFaithful : Prop :=
  (∀ (t : IntTy) (x : Rat t),
    RationalModel.sign x =
      ⟨JInt.lit t (if x.num.val < 0 then -1 else if x.num.val > 0 then 1 else 0),
       JInt.lit t 1⟩ ∧
    RationalModel.signbit x = decide (x.num.val < 0) ∧
    (∃ r, abs x = r) ∧ pos x = ⟨x.num, x.den⟩ ∧
    RationalModel.negUnchecked x = ⟨-x.num, x.den⟩ ∧
    RationalModel.negWrap x = ⟨-x.num, x.den⟩ ∧
    (∃ r, neg x = r)) ∧
  (∀ t, RationalModel.typemin t =
      (if t.signed then ⟨JInt.lit t (-1), JInt.lit t 0⟩
       else ⟨JInt.lit t 0, JInt.lit t 1⟩) ∧
    RationalModel.typemax t = ⟨JInt.lit t 1, JInt.lit t 0⟩) ∧
  (∀ (t : IntTy) (ispow2 : JInt t → Bool) (x : Rat t),
    RationalModel.ispow2 ispow2 x = (ispow2 x.num && ispow2 x.den) ∧
    RationalModel.isinteger x = (x.den.val == 1)) ∧
  (∀ (t : IntTy) (x y : Rat t),
    (∃ r, add x y = r) ∧ (∃ r, sub x y = r) ∧
    (∃ r, RationalModel.addWrap x y = r) ∧
    (∃ r, RationalModel.subWrap x y = r) ∧
    (∃ r, rem x y = r) ∧ (∃ r, mod x y = r) ∧
    (∃ r, mul x y = r) ∧ (∃ r, div x y = r) ∧
    (∃ r, inv x = r)) ∧
  (∀ (t : IntTy) (x : Rat t) (y : JInt t),
    (∀ op, ∃ r, withInt op x y = r) ∧
    (∀ op, ∃ r, intWith op y x = r) ∧
    (∀ op, ∃ r, intRemainder op y x = r) ∧
    (∃ r, mulInt x y = r) ∧ (∃ r, divInt x y = r) ∧
    (∃ r, intMul y x = r) ∧ (∃ r, intDiv y x = r)) ∧
  (∀ (t s : IntTy) (x : Rat t) (y : JInt s),
    (∃ r, addIntMixed x y = r) ∧ (∃ r, subIntMixed x y = r) ∧
    (∃ r, remIntMixed x y = r) ∧ (∃ r, modIntMixed x y = r) ∧
    (∃ r, mulIntMixed x y = r) ∧ (∃ r, divIntMixed x y = r) ∧
    (∃ r, intAddMixed y x = r) ∧ (∃ r, intSubMixed y x = r) ∧
    (∃ r, intRemMixed y x = r) ∧ (∃ r, intModMixed y x = r) ∧
    (∃ r, intMulMixed y x = r) ∧ (∃ r, intDivMixed y x = r)) ∧
  (∀ (t : IntTy) (b : Bool) (x : Rat t),
    RationalModel.boolMul b x = if b then x else ⟨JInt.lit t 0, JInt.lit t 1⟩) ∧
  (∀ (t : IntTy) (x y z : Rat t), ∃ r, RationalModel.fma x y z = r)

theorem rationalArithmeticFaithful_proven : RationalArithmeticFaithful := by
  simp [RationalArithmeticFaithful, RationalModel.sign, RationalModel.signbit,
    pos, RationalModel.negUnchecked, RationalModel.negWrap, RationalModel.typemin,
    RationalModel.typemax, RationalModel.ispow2, RationalModel.isinteger,
    RationalModel.boolMul]

def RationalComparisonFaithful : Prop :=
  (∀ (t s : IntTy) (x : Rat t) (y : Rat s),
    (∃ r, eq x y = r) ∧ (∃ r, lt x y = r) ∧ (∃ r, le x y = r) ∧
    (∃ r, cmp @lt x y = r)) ∧
  (∀ (t s : IntTy) (x : Rat t) (y : JInt s),
    (∃ r, eqInt x y = r) ∧ (∃ r, ltInt x y = r) ∧
    (∃ r, intLt y x = r) ∧ (∃ r, leInt x y = r) ∧
    (∃ r, intLe y x = r)) ∧
  (∀ (f : JuliaLean.Promotion.Fmt) (t : IntTy) (x : Rat t)
      (y : JuliaLean.Promotion.Fl f),
    (∃ r, JuliaLean.Promotion.ltRF x y = r) ∧
    (∃ r, JuliaLean.Promotion.leRF x y = r) ∧
    (∃ r, JuliaLean.Promotion.ltFR y x = r) ∧
    (∃ r, JuliaLean.Promotion.leFR y x = r) ∧
    (∃ r, JuliaLean.Promotion.cmpRF x y = r) ∧
    (∃ r, JuliaLean.Promotion.cmpFR y x = r)) ∧
  (∀ (α β : Type) (isreal : RationalModel.Pair α → Bool) (eq : α → β → Bool)
      (z : RationalModel.Pair α) (x : β),
    RationalModel.eqComplex isreal eq z x = (isreal z && eq z.re x)) ∧
  (∀ (α β γ : Type) (finite : α → Bool) (ones : β → Nat)
      (ldexp : α → Int → α) (top : β → Int) (eqFI : α → γ → Bool)
      (divide : γ → β → α) (eqF : α → α → Bool) x n d,
    RationalModel.eqFloat finite ones ldexp top eqFI divide eqF x n d =
      if finite x then ones d == 1 && eqFI (ldexp x (top d)) n
      else eqF x (divide n d))

theorem rationalComparisonFaithful_proven : RationalComparisonFaithful := by
  simp [RationalComparisonFaithful, RationalModel.eqComplex, RationalModel.eqFloat]

def RationalRoundingFaithful : Prop :=
  (∀ (t : IntTy) (x y : Rat t) mode,
    (∃ r, quotient x y mode = r) ∧
    (∃ r, quotientInt x x.num mode = r) ∧
    (∃ r, intQuotient x.num y mode = r)) ∧
  (∀ (t s : IntTy) (x : Rat t) (y : Rat s) mode,
    (∃ r, quotientMixed x y mode = r) ∧
    (∃ r, fldMixed x y = r) ∧ (∃ r, cldMixed x y = r)) ∧
  (∀ (t s : IntTy) (x : Rat t) (y : JInt s),
    (∀ op, ∃ r, quotientIntMixed op x y = r) ∧
    (∀ op, ∃ r, intQuotientMixed op y x = r)) ∧
  (∀ (t target : IntTy) (x : Rat t) mode,
    (∃ r, round target x mode = r) ∧
    (∃ r, trunc target x = r) ∧ (∃ r, floor target x = r) ∧
    (∃ r, ceil target x = r)) ∧
  (∀ (α β : Type) targetInt denominatorFalse (convert : α → Jl β) x,
    RationalModel.roundBool targetInt denominatorFalse convert x =
      if denominatorFalse && targetInt then .error .divideError else convert x)

theorem rationalRoundingFaithful_proven : RationalRoundingFaithful := by
  simp [RationalRoundingFaithful, RationalModel.roundBool]

def RationalNumberTheoryFaithful : Prop :=
  (∀ (t : IntTy) (x y : Rat t),
    (∃ r, RationalModel.gcdRat x y = r) ∧
    (∃ r, RationalModel.lcmRat x y = r) ∧
    (∃ r, RationalModel.gcdxRat x y = r) ∧
    (∃ r, RationalModel.idivRat x y = r)) ∧
  (∀ (t : IntTy) (x : Rat t), RationalModel.decompose x = (x.num.val, 0, x.den.val)) ∧
  (∀ (t : IntTy) (x : Rat t) h, ∃ r, JuliaLean.Promotion.hashRat64 x h = r) ∧
  (∀ (t : IntTy) (first last : Rat t) (empty : Bool),
    (∃ r, RationalModel.rangeLength first last = r) ∧
    (∃ r, RationalModel.checkedRangeLength first last empty = r))

theorem rationalNumberTheoryFaithful_proven : RationalNumberTheoryFaithful := by
  simp [RationalNumberTheoryFaithful, RationalModel.decompose]


end JuliaLean.NumbersCov

namespace JuliaLean.NumbersCov.Rows.Rational

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows
open JuliaLean.IntArith.Rational

def P14 : Prop := ∀ (t : IntTy) (n d : JInt t), m14 n d = Rat.mk n d
theorem p14 : P14 := by simp [P14, m14, RationalModel.unsafeRat]
def P17 : Prop := P14
theorem p17 : P17 := p14
def P18 : Prop := ∀ (t s : IntTy) (n : JInt t) (d : JInt s), HasResult (m18 n d)
theorem p18 : P18 := by simp [P18, HasResult]
def P20 : Prop := ∀ (t : IntTy) (n d : JInt t), HasResult (m20 n d)
theorem p20 : P20 := by simp [P20, HasResult]
def P27 : Prop := P20
theorem p27 : P27 := p20
def P28 : Prop := ∀ (t s : IntTy) (n : JInt t) (d : JInt s), HasResult (m28 n d)
theorem p28 : P28 := by simp [P28, HasResult]
def P30 : Prop := ∀ (α : Type) n, @m30 α n = .error (.argumentError n)
theorem p30 : P30 := by simp [P30, m30, RationalModel.throwZero]
def P48 : Prop := ∀ (t : IntTy) (n d : JInt t), HasResult (m48 n d)
theorem p48 : P48 := by simp [P48, HasResult]
def P49 : Prop := ∀ (t s : IntTy) (n : JInt t) (d : JInt s), HasResult (m49 n d)
theorem p49 : P49 := by simp [P49, HasResult]
def P50 : Prop := ∀ (t : IntTy) (n : JInt t), m50 n = ⟨n, JInt.lit t 1⟩
theorem p50 : P50 := by simp [P50, m50, ofInt]
def P59 : Prop := ∀ (t s : IntTy) (x : JInt t) (y : JInt s), HasResult (m59 x y)
theorem p59 : P59 := by simp [P59, HasResult]

def P91 : Prop := P48
theorem p91 : P91 := p48
def P93 : Prop := ∀ (t : IntTy) (x : Rat t) y, HasResult (m93 x y)
theorem p93 : P93 := by simp [P93, HasResult]
def P102 : Prop := ∀ (t : IntTy) (x : JInt t) y, HasResult (m102 x y)
theorem p102 : P102 := by simp [P102, HasResult]
def P106 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (m106 x y)
theorem p106 : P106 := by simp [P106, HasResult]
def P116 : Prop := ∀ (α β γ : Type) (d : α → β → γ) z y,
  m116 d z y = ⟨d z.re y, d z.im y⟩
theorem p116 : P116 := by simp [P116, m116, RationalModel.complexDivReal]
def P120 : Prop := ∀ (α : Type) (inf : α → Bool)
  (zero conj : RationalModel.Pair α → RationalModel.Pair α) (a : RationalModel.Pair α → α) z,
  HasResult (m120 inf zero conj a z)
theorem p120 : P120 := by simp [P120, HasResult]
def P129 : Prop := ∀ (t : IntTy) (z : RationalModel.Pair (JInt t)), HasResult (@m129 t z)
theorem p129 : P129 := by simp [P129, HasResult]
def P137 : Prop := ∀ (α β γ δ ε : Type) (i : RationalModel.Pair α → RationalModel.Pair α × β)
  (m : γ → RationalModel.Pair α → δ) (d : δ → β → ε) x y,
  HasResult (m137 i m d x y)
theorem p137 : P137 := by simp [P137, HasResult]
def P141 : Prop := ∀ (t : IntTy) (x : JInt t) y, HasResult (m141 x y)
theorem p141 : P141 := by simp [P141, HasResult]
def P144 : Prop := ∀ (t : IntTy) (x y : RationalModel.Pair (JInt t)), HasResult (@m144 t x y)
theorem p144 : P144 := by simp [P144, HasResult]
def P154 : Prop := ∀ (α β γ : Type) (b : α → β → γ) x y, m154 b x y = b x y
theorem p154 : P154 := by simp [P154, m154, RationalModel.arrayExactDiv]
def P156 : Prop := ∀ (α : Type) (r : α → String) (o : α → Bool) t n d,
  HasResult (m156 r o t n d)
theorem p156 : P156 := by simp [P156, HasResult]
def P167 : Prop := ∀ (α : Type) (r : Unit → α × α), m167 r = r ()
theorem p167 : P167 := by simp [P167, m167, RationalModel.readPair]
def P172 : Prop := ∀ (α β : Type) (w : α → α → β) n d, m172 w n d = w n d
theorem p172 : P172 := by simp [P172, m172, RationalModel.writePair]
def P175 : Prop := ∀ (α β : Type) (p : String → α) (c : α → α → β) parts,
  HasResult (m175 p c parts)
theorem p175 : P175 := by simp [P175, HasResult]

def P190 : Prop := ∀ (s : IntTy) target (x : Rat s), HasResult (m190 target x)
theorem p190 : P190 := by simp [P190, HasResult]
def P193 : Prop := ∀ t x, HasResult (m193 t x)
theorem p193 : P193 := by simp [P193, HasResult]
def P197 : Prop := ∀ (t : IntTy) (x : Rat t), m197 x = x
theorem p197 : P197 := by simp [P197, m197]
def P199 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (@m199 t x)
theorem p199 : P199 := by simp [P199, HasResult]
def P201 : Prop := ∀ target (t : IntTy) (x : Rat t), HasResult (@m201 target t x)
theorem p201 : P201 := by simp [P201, HasResult]

def P204 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (m204 x)
theorem p204 : P204 := by simp [P204, HasResult]
def P205 : Prop := ∀ (A B P C D : Type) (pr : A → B → P) (ca : P → A → C)
  (cb : P → B → C) (div : C → C → C) (out : C → D) t s n d,
  HasResult (m205 pr ca cb div out t s n d)
theorem p205 : P205 := by simp [P205, HasResult]
def P211 : Prop := ∀ (α β γ : Type) (a : α → β) (b : β → γ) x,
  m211 a b x = b (a x)
theorem p211 : P211 := by simp [P211, m211]
def P213 : Prop := ∀ (α β γ : Type) (a : α → β) (b : β → γ) x,
  m213 a b x = b (a x)
theorem p213 : P213 := by simp [P213, m213]
def P223 : Prop := ∀ t x, HasResult (m223 t x)
theorem p223 : P223 := by simp [P223, HasResult]
def P224 : Prop := ∀ (α β : Type) (c : α → β) x, m224 c x = c x
theorem p224 : P224 := by simp [P224, m224]
def P226 : Prop := ∀ (α β γ : Type) (b : α → β) (u : β → β → γ) n d,
  m226 b u n d = u (b n) (b d)
theorem p226 : P226 := by simp [P226, m226]
def P228 : Prop := ∀ (α β : Type) (c : α → β) z, m228 c z = c z
theorem p228 : P228 := by simp [P228, m228]
def P230 : Prop := ∀ (α β γ δ : Type) (p : α → β → γ) (r : γ → δ) t s,
  m230 p r t s = r (p t s)
theorem p230 : P230 := by simp [P230, m230]
def P231 : Prop := P230
theorem p231 : P231 := p230
def P232 : Prop := ∀ (α β γ : Type) (p : α → β → γ) t s, m232 p t s = p t s
theorem p232 : P232 := by simp [P232, m232]
def P234 : Prop := ∀ (α β γ : Type) (w : α → β) (r : β → γ) t,
  m234 w r t = r (w t)
theorem p234 : P234 := by simp [P234, m234]
def P236 : Prop := ∀ (α : Type), @m236 α = .error (.overflowError "cannot negate unsigned number")
theorem p236 : P236 := by simp [P236, m236]

def P321 : Prop := ∀ (α β : Type) (r : α → β) x, m321 r x = r x
theorem p321 : P321 := by simp [P321, m321]
def P322 : Prop := ∀ (α β : Type) (r : α → β) z,
  m322 r z = ⟨r z.re, r z.im⟩
theorem p322 : P322 := by simp [P322, m322, RationalModel.rationalizeComplex]
def P323 : Prop := P322
theorem p323 : P323 := p322
def P324 : Prop := ∀ (α β γ : Type) (r : α → β → γ) x t, m324 r x t = r x t
theorem p324 : P324 := by simp [P324, m324]
def P325 : Prop := ∀ (α β : Type) (r : α → β) x, m325 r x = r x
theorem p325 : P325 := by simp [P325, m325]
def P326 : Prop := ∀ (α β : Type) (c : α → Jl β) (r : Unit → Jl β) x u f t,
  HasResult (m326 c r x u f t)
theorem p326 : P326 := by simp [P326, HasResult]
def P334 : Prop := ∀ x, m334 x = ⟨x, 1⟩
theorem p334 : P334 := by simp [P334, m334, RationalModel.rationalizeIntegerDefault]
def P343 : Prop := ∀ (α : Type), @m343 α = .error (.methodError "rationalize")
theorem p343 : P343 := by simp [P343, m343]

def P360 : Prop := ∀ (α : Type) (x : α), m360 x = x
theorem p360 : P360 := by simp [P360, m360, RationalModel.numeratorIntegral]
def P361 : Prop := ∀ (t : IntTy) (x : Rat t), @m361 t x = x.num
theorem p361 : P361 := by simp [P361, m361, numerator]
def P362 : Prop := ∀ (α β γ : Type) (n d : α → β) (m q : β → β → β)
  (c : β → β → γ) (r i : α → α) z x, HasResult (m362 n d m q c r i z x)
theorem p362 : P362 := by simp [P362, HasResult]
def P383 : Prop := ∀ (α : Type) (o : α → α) x, m383 o x = o x
theorem p383 : P383 := by simp [P383, m383, RationalModel.denominatorIntegral]
def P384 : Prop := ∀ (t : IntTy) (x : Rat t), @m384 t x = x.den
theorem p384 : P384 := by simp [P384, m384, denominator]
def P385 : Prop := ∀ (α β : Type) (d : α → β) (l : β → β → β)
  (r i : α → α) z, m385 d l r i z = l (d (r z)) (d (i z))
theorem p385 : P385 := by simp [P385, m385, RationalModel.denominatorComplex]

def P628 : Prop := ∀ (α : Type) (p : Int → Bool) (pow : α → Int → α) (i : α → α) x n,
  HasResult (m628 p pow i x n)
theorem p628 : P628 := by simp [P628, HasResult]
def P632 : Prop := ∀ (α β γ δ : Type) (d : α → α → β) (p : γ → β → δ) x n q,
  m632 d p x n q = p x (d n q)
theorem p632 : P632 := by simp [P632, m632, RationalModel.powerRationalExponent]
def P633 : Prop := P632
theorem p633 : P633 := p632
def P634 : Prop := ∀ (α β γ δ : Type) (c : α → β) (p : γ → β → δ) z x,
  m634 c p z x = p z (c x)
theorem p634 : P634 := by simp [P634, m634]
def P636 : Prop := ∀ (α : Type) (one : RationalModel.Pair α → RationalModel.Pair α) z n,
  m636 one z n = if n then z else one z
theorem p636 : P636 := by simp [P636, m636, RationalModel.powerBool]
def P637 : Prop := ∀ (α : Type) (p : α → Int → α) (i : α → α) x n,
  m637 p i x n = if n ≥ 0 then p x n else p (i x) (-n)
theorem p637 : P637 := by simp [P637, m637]
def P641 : Prop := ∀ (t : IntTy) (x : Rat t), m641 x = (x.num.val == 0)
theorem p641 : P641 := by simp [P641, m641, RationalModel.iszero]
def P642 : Prop := ∀ (t : IntTy) (x : Rat t), m642 x = (x.num.val == 1 && x.den.val == 1)
theorem p642 : P642 := by simp [P642, m642, RationalModel.isone]
def P644 : Prop := ∀ (α : Type) (s m d a : α → α → α) j n x y,
  HasResult (m644 s m d a j n x y)
theorem p644 : P644 := by simp [P644, HasResult]
def P648 : Prop := ∀ (α β : Type) (f : α → β) t, m648 f t = f t
theorem p648 : P648 := by simp [P648, m648]

def P387 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (m387 x)
theorem p387 : P387 := by simp [P387, HasResult]
def P388 : Prop := ∀ (t : IntTy) (x : Rat t), m388 x = decide (x.num.val < 0)
theorem p388 : P388 := by simp [P388, m388, RationalModel.signbit]
def P390 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (@m390 t x)
theorem p390 : P390 := by simp [P390, HasResult]
def P392 : Prop := ∀ t, HasResult (m392 t)
theorem p392 : P392 := by simp [P392, HasResult]
def P393 : Prop := ∀ t, HasResult (m393 t)
theorem p393 : P393 := by simp [P393, HasResult]
def P394 : Prop := ∀ t, m394 t = ⟨JInt.lit t 1, JInt.lit t 0⟩
theorem p394 : P394 := by simp [P394, m394, RationalModel.typemax]
def P396 : Prop := ∀ (t : IntTy) (x : Rat t), m396 x = (x.den.val == 1)
theorem p396 : P396 := by simp [P396, m396, RationalModel.isinteger]
def P397 : Prop := ∀ (t : IntTy) (p : JInt t → Bool) x,
  m397 p x = (p x.num && p x.den)
theorem p397 : P397 := by simp [P397, m397, RationalModel.ispow2]
def P399 : Prop := ∀ (t : IntTy) (x : Rat t), @m399 t x = ⟨x.num, x.den⟩
theorem p399 : P399 := by simp [P399, m399, pos]
def P400 : Prop := ∀ (t : IntTy) (x : Rat t), @m400 t x = ⟨-x.num, x.den⟩
theorem p400 : P400 := by simp [P400, m400, RationalModel.negUnchecked]
def P402 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (@m402 t x)
theorem p402 : P402 := by simp [P402, HasResult]
def P406 : Prop := ∀ (α : Type) n, @m406 α n = .error (.overflowError n)
theorem p406 : P406 := by simp [P406, m406]
def P408 : Prop := P402
theorem p408 : P408 := p402
def P413 : Prop := ∀ (t : IntTy) (x : Rat t), @m413 t x = ⟨-x.num, x.den⟩
theorem p413 : P413 := by simp [P413, m413, RationalModel.negWrap]
def P424 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m424 t x y)
theorem p424 : P424 := by simp [P424, HasResult]
def P442 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m442 t x y)
theorem p442 : P442 := by simp [P442, HasResult]
def P453 : Prop := ∀ (t : IntTy) (op : JInt t → JInt t → Jl (JInt t)) x y,
  HasResult (m453 op x y)
theorem p453 : P453 := by simp [P453, HasResult]
def P462 : Prop := ∀ (t : IntTy) op (x : Rat t) (y : JInt t), HasResult (@m462 t op x y)
theorem p462 : P462 := by simp [P462, HasResult]
def P469 : Prop := ∀ (t : IntTy) op (y : JInt t) (x : Rat t), HasResult (@m469 t op y x)
theorem p469 : P469 := by simp [P469, HasResult]
def P476 : Prop := ∀ (t : IntTy) op (y : JInt t) (x : Rat t), HasResult (@m476 t op y x)
theorem p476 : P476 := by simp [P476, HasResult]
def P482 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m482 t x y)
theorem p482 : P482 := by simp [P482, HasResult]
def P487 : Prop := ∀ (t : IntTy) (x : Rat t) y, HasResult (@m487 t x y)
theorem p487 : P487 := by simp [P487, HasResult]
def P491 : Prop := ∀ (t : IntTy) y (x : Rat t), HasResult (@m491 t y x)
theorem p491 : P491 := by simp [P491, HasResult]
def P497 : Prop := ∀ (t : IntTy) b (x : Rat t), HasResult (@m497 t b x)
theorem p497 : P497 := by simp [P497, HasResult]
def P500 : Prop := ∀ (t : IntTy) (x : Rat t) b, HasResult (m500 x b)
theorem p500 : P500 := by simp [P500, HasResult]
def P501 : Prop := ∀ (t : IntTy) (x : Rat t) y, HasResult (@m501 t x y)
theorem p501 : P501 := by simp [P501, HasResult]
def P502 : Prop := ∀ (t : IntTy) x (y : Rat t), HasResult (@m502 t x y)
theorem p502 : P502 := by simp [P502, HasResult]
def P503 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (@m503 t x)
theorem p503 : P503 := by simp [P503, HasResult]
def P505 : Prop := ∀ (t : IntTy) (x y z : Rat t), HasResult (@m505 t x y z)
theorem p505 : P505 := by simp [P505, HasResult]

def P507 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m507 t s x y)
theorem p507 : P507 := by simp [P507, HasResult]
def P508 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m508 t s x y)
theorem p508 : P508 := by simp [P508, HasResult]
def P510 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m510 t s x y)
theorem p510 : P510 := by simp [P510, HasResult]
def P514 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : JInt s), HasResult (@m514 t s x y)
theorem p514 : P514 := by simp [P514, HasResult]
def P515 : Prop := ∀ (t s : IntTy) (x : JInt t) (y : Rat s), HasResult (m515 x y)
theorem p515 : P515 := by simp [P515, HasResult]
def P516 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : JInt s), HasResult (@m516 t s x y)
theorem p516 : P516 := by simp [P516, HasResult]
def P517 : Prop := ∀ (t s : IntTy) (x : JInt t) (y : Rat s), HasResult (@m517 t s x y)
theorem p517 : P517 := by simp [P517, HasResult]
def P518 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : JInt s), HasResult (@m518 t s x y)
theorem p518 : P518 := by simp [P518, HasResult]
def P519 : Prop := ∀ (t s : IntTy) (x : JInt t) (y : Rat s), HasResult (@m519 t s x y)
theorem p519 : P519 := by simp [P519, HasResult]
def P521 : Prop := ∀ (α β γ : Type) (finite : α → Bool) (ones : β → Nat)
  (ld : α → Int → α) (top : β → Int) (eqi : α → γ → Bool)
  (div : γ → β → α) (eqf : α → α → Bool) x n d,
  HasResult (@m521 α β γ finite ones ld top eqi div eqf x n d)
theorem p521 : P521 := by simp [P521, HasResult]
def P529 : Prop := ∀ (α β : Type) (eq : α → β → Bool) x y, m529 eq y x = eq x y
theorem p529 : P529 := by simp [P529, m529]
def P533 : Prop := ∀ (α β γ : Type) (r : α → β → γ) x y, m533 r x y = r x y
theorem p533 : P533 := by simp [P533, m533]
def P583 : Prop := ∀ (α β : Type) (real : RationalModel.Pair α → Bool)
  (eq : α → β → Bool) z x, HasResult (@m583 α β real eq z x)
theorem p583 : P583 := by simp [P583, HasResult]
def P584 : Prop := P583
theorem p584 : P584 := p583

def P586 : Prop := ∀ (t : IntTy) (x : Rat t) y mode, HasResult (@m586 t x y mode)
theorem p586 : P586 := by simp [P586, HasResult]
def P590 : Prop := ∀ (t : IntTy) x (y : Rat t) mode, HasResult (@m590 t x y mode)
theorem p590 : P590 := by simp [P590, HasResult]
def P594 : Prop := ∀ (t : IntTy) (x y : Rat t) mode, HasResult (@m594 t x y mode)
theorem p594 : P594 := by simp [P594, HasResult]
def P602 : Prop := P594
theorem p602 : P602 := p594
def P606 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m606 t s x y .toZero)
theorem p606 : P606 := by simp [P606, HasResult]
def P607 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m607 t s x y)
theorem p607 : P607 := by simp [P607, HasResult]
def P608 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m608 t s x y)
theorem p608 : P608 := by simp [P608, HasResult]
def P612 : Prop := ∀ (t : IntTy) (x : Rat t) mode, HasResult (m612 x mode)
theorem p612 : P612 := by simp [P612, HasResult]
def P614 : Prop := ∀ target (t : IntTy) (x : Rat t) mode, HasResult (@m614 target t x mode)
theorem p614 : P614 := by simp [P614, HasResult]
def P621 : Prop := ∀ (α β : Type) a b (c : α → Jl β) x, HasResult (@m621 α β a b c x)
theorem p621 : P621 := by simp [P621, HasResult]

def P650 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m650 t x y)
theorem p650 : P650 := by simp [P650, HasResult]
def P656 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m656 t x y)
theorem p656 : P656 := by simp [P656, HasResult]
def P662 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m662 t x y)
theorem p662 : P662 := by simp [P662, HasResult]
def P670 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m670 t x y)
theorem p670 : P670 := by simp [P670, HasResult]
def P678 : Prop := ∀ (t : IntTy) (x : Rat t), @m678 t x = (x.num.val, 0, x.den.val)
theorem p678 : P678 := by simp [P678, m678, RationalModel.decompose]
def P679 : Prop := ∀ (t : IntTy) (x : Rat t) h, HasResult (@m679 t x h)
theorem p679 : P679 := by simp [P679, HasResult]
def P707 : Prop := ∀ (t : IntTy) (f l : Rat t), HasResult (@m707 t f l)
theorem p707 : P707 := by simp [P707, HasResult]
def P713 : Prop := ∀ (t : IntTy) (f l : Rat t) e, HasResult (@m713 t f l e)
theorem p713 : P713 := by simp [P713, HasResult]

end JuliaLean.NumbersCov.Rows.Rational
