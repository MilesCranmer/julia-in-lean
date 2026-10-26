import JuliaLean.NumbersCov.Rows.Common

namespace JuliaLean.NumbersCov.Rows.Rational

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows
open JuliaLean.IntArith.Rational

def m14 {t} (n d : JInt t) := RationalModel.unsafeRat n d
def P14 : Prop := ∀ (t : IntTy) (n d : JInt t), m14 n d = Rat.mk n d
theorem p14 : P14 := by simp [P14, m14, RationalModel.unsafeRat]
def m17 := @m14
def P17 : Prop := P14
theorem p17 : P17 := p14
def m18 {t s} (n : JInt t) (d : JInt s) := RationalModel.unsafeMixed n d
def P18 : Prop := ∀ (t s : IntTy) (n : JInt t) (d : JInt s), HasResult (m18 n d)
theorem p18 : P18 := by simp [P18, HasResult]
def m20 {t} (n d : JInt t) := checkedDen n d
def P20 : Prop := ∀ (t : IntTy) (n d : JInt t), HasResult (m20 n d)
theorem p20 : P20 := by simp [P20, HasResult]
def m27 := @m20
def P27 : Prop := P20
theorem p27 : P27 := p20
def m28 {t s} (n : JInt t) (d : JInt s) := RationalModel.checkedDenMixed n d
def P28 : Prop := ∀ (t s : IntTy) (n : JInt t) (d : JInt s), HasResult (m28 n d)
theorem p28 : P28 := by simp [P28, HasResult]
def m30 (name : String) : Jl α := RationalModel.throwZero name
def P30 : Prop := ∀ (α : Type) n, @m30 α n = .error (.argumentError n)
theorem p30 : P30 := by simp [P30, m30, RationalModel.throwZero]
def m48 {t} (n d : JInt t) := ofInts n d
def P48 : Prop := ∀ (t : IntTy) (n d : JInt t), HasResult (m48 n d)
theorem p48 : P48 := by simp [P48, HasResult]
def m49 {t s} (n : JInt t) (d : JInt s) := ofMixedInts n d
def P49 : Prop := ∀ (t s : IntTy) (n : JInt t) (d : JInt s), HasResult (m49 n d)
theorem p49 : P49 := by simp [P49, HasResult]
def m50 {t} (n : JInt t) := ofInt n
def P50 : Prop := ∀ (t : IntTy) (n : JInt t), m50 n = ⟨n, JInt.lit t 1⟩
theorem p50 : P50 := by simp [P50, m50, ofInt]
def m59 {t s} (x : JInt t) (y : JInt s) := divgcd x y
def P59 : Prop := ∀ (t s : IntTy) (x : JInt t) (y : JInt s), HasResult (m59 x y)
theorem p59 : P59 := by simp [P59, HasResult]

def m91 := @m48
def P91 : Prop := P48
theorem p91 : P91 := p48
def m93 {t} (x : Rat t) (y : JInt t) := divInt x y
def P93 : Prop := ∀ (t : IntTy) (x : Rat t) y, HasResult (m93 x y)
theorem p93 : P93 := by simp [P93, HasResult]
def m102 {t} (x : JInt t) (y : Rat t) := intDiv x y
def P102 : Prop := ∀ (t : IntTy) (x : JInt t) y, HasResult (m102 x y)
theorem p102 : P102 := by simp [P102, HasResult]
def m106 {t} (x y : Rat t) := div x y
def P106 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (m106 x y)
theorem p106 : P106 := by simp [P106, HasResult]
def m116 (ratDiv : α → β → γ) (z : RationalModel.Pair α) y :=
  RationalModel.complexDivReal ratDiv z y
def P116 : Prop := ∀ (α β γ : Type) (d : α → β → γ) z y,
  m116 d z y = ⟨d z.re y, d z.im y⟩
theorem p116 : P116 := by simp [P116, m116, RationalModel.complexDivReal]
def m120 (isinf : α → Bool) (zero conj : RationalModel.Pair α → RationalModel.Pair α)
    (abs2 : RationalModel.Pair α → α) z :=
  RationalModel.complexExactInv isinf zero id conj abs2 z
def P120 : Prop := ∀ (α : Type) (inf : α → Bool)
  (zero conj : RationalModel.Pair α → RationalModel.Pair α) (a : RationalModel.Pair α → α) z,
  HasResult (m120 inf zero conj a z)
theorem p120 : P120 := by simp [P120, HasResult]
def m129 := @RationalModel.complexExactInvInt
def P129 : Prop := ∀ (t : IntTy) (z : RationalModel.Pair (JInt t)), HasResult (@m129 t z)
theorem p129 : P129 := by simp [P129, HasResult]
def m137 (exactInv : RationalModel.Pair α → RationalModel.Pair α × β)
    (mul : γ → RationalModel.Pair α → δ) (ratDiv : δ → β → ε) x y :=
  RationalModel.divByComplex exactInv mul ratDiv x y
def P137 : Prop := ∀ (α β γ δ ε : Type) (i : RationalModel.Pair α → RationalModel.Pair α × β)
  (m : γ → RationalModel.Pair α → δ) (d : δ → β → ε) x y,
  HasResult (m137 i m d x y)
theorem p137 : P137 := by simp [P137, HasResult]
def m141 {t} (x : JInt t) (y : RationalModel.Pair (JInt t)) :=
  RationalModel.complexIntDiv ⟨x, JInt.lit t 0⟩ y
def P141 : Prop := ∀ (t : IntTy) (x : JInt t) y, HasResult (m141 x y)
theorem p141 : P141 := by simp [P141, HasResult]
def m144 := @RationalModel.complexIntDiv
def P144 : Prop := ∀ (t : IntTy) (x y : RationalModel.Pair (JInt t)), HasResult (@m144 t x y)
theorem p144 : P144 := by simp [P144, HasResult]
def m154 (broadcast : α → β → γ) x y := RationalModel.arrayExactDiv broadcast x y
def P154 : Prop := ∀ (α β γ : Type) (b : α → β → γ) x y, m154 b x y = b x y
theorem p154 : P154 := by simp [P154, m154, RationalModel.arrayExactDiv]
def m156 (render : α → String) (one : α → Bool) typed n d :=
  RationalModel.showRat render one typed n d
def P156 : Prop := ∀ (α : Type) (r : α → String) (o : α → Bool) t n d,
  HasResult (m156 r o t n d)
theorem p156 : P156 := by simp [P156, HasResult]
def m167 (read : Unit → α × α) := RationalModel.readPair read
def P167 : Prop := ∀ (α : Type) (r : Unit → α × α), m167 r = r ()
theorem p167 : P167 := by simp [P167, m167, RationalModel.readPair]
def m172 (write : α → α → β) n d := RationalModel.writePair write n d
def P172 : Prop := ∀ (α β : Type) (w : α → α → β) n d, m172 w n d = w n d
theorem p172 : P172 := by simp [P172, m172, RationalModel.writePair]
def m175 (parse : String → α) (construct : α → α → β) parts :=
  RationalModel.parseParts parse construct parts
def P175 : Prop := ∀ (α β : Type) (p : String → α) (c : α → α → β) parts,
  HasResult (m175 p c parts)
theorem p175 : P175 := by simp [P175, HasResult]

def m190 (target : IntTy) (x : Rat s) := convertRat target x
def P190 : Prop := ∀ (s : IntTy) target (x : Rat s), HasResult (m190 target x)
theorem p190 : P190 := by simp [P190, HasResult]
def m193 (target : IntTy) (x : Int) : Jl (Rat target) := do
  let n ← JInt.convert target x
  return ⟨n, JInt.lit target 1⟩
def P193 : Prop := ∀ t x, HasResult (m193 t x)
theorem p193 : P193 := by simp [P193, HasResult]
def m197 (x : Rat t) := x
def P197 : Prop := ∀ (t : IntTy) (x : Rat t), m197 x = x
theorem p197 : P197 := by simp [P197, m197]
def m199 := @RationalModel.boolOfRat
def P199 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (@m199 t x)
theorem p199 : P199 := by simp [P199, HasResult]
def m201 := @RationalModel.intOfRat
def P201 : Prop := ∀ target (t : IntTy) (x : Rat t), HasResult (@m201 target t x)
theorem p201 : P201 := by simp [P201, HasResult]

def m204 {t} (x : Rat t) := JuliaLean.Promotion.ratToF64 x
def P204 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (m204 x)
theorem p204 : P204 := by simp [P204, HasResult]
def m205 (promote : A → B → P) (convertA : P → A → C) (convertB : P → B → C)
    (div : C → C → C) (out : C → D) t s n d :=
  let p := promote t s
  out (div (convertA p n) (convertB p d))
def P205 : Prop := ∀ (A B P C D : Type) (pr : A → B → P) (ca : P → A → C)
  (cb : P → B → C) (div : C → C → C) (out : C → D) t s n d,
  HasResult (m205 pr ca cb div out t s n d)
theorem p205 : P205 := by simp [P205, HasResult]
def m211 (to32 : α → β) (to16 : β → γ) x := to16 (to32 x)
def P211 : Prop := ∀ (α β γ : Type) (a : α → β) (b : β → γ) x,
  m211 a b x = b (a x)
theorem p211 : P211 := by simp [P211, m211]
def m213 (to64 : α → β) (to16 : β → γ) x := to16 (to64 x)
def P213 : Prop := ∀ (α β γ : Type) (a : α → β) (b : β → γ) x,
  m213 a b x = b (a x)
theorem p213 : P213 := by simp [P213, m213]
def m223 := @JuliaLean.Promotion.rationalOfF64
def P223 : Prop := ∀ t x, HasResult (m223 t x)
theorem p223 : P223 := by simp [P223, HasResult]
def m224 (convert : α → β) x := convert x
def P224 : Prop := ∀ (α β : Type) (c : α → β) x, m224 c x = c x
theorem p224 : P224 := by simp [P224, m224]
def m226 (big : α → β) (unsafeCtor : β → β → γ) n d := unsafeCtor (big n) (big d)
def P226 : Prop := ∀ (α β γ : Type) (b : α → β) (u : β → β → γ) n d,
  m226 b u n d = u (b n) (b d)
theorem p226 : P226 := by simp [P226, m226]
def m228 (convert : α → β) z := convert z
def P228 : Prop := ∀ (α β : Type) (c : α → β) z, m228 c z = c z
theorem p228 : P228 := by simp [P228, m228]
def m230 (promote : α → β → γ) (ratType : γ → δ) t s := ratType (promote t s)
def P230 : Prop := ∀ (α β γ δ : Type) (p : α → β → γ) (r : γ → δ) t s,
  m230 p r t s = r (p t s)
theorem p230 : P230 := by simp [P230, m230]
def m231 := @m230
def P231 : Prop := P230
theorem p231 : P231 := p230
def m232 (promote : α → β → γ) t s := promote t s
def P232 : Prop := ∀ (α β γ : Type) (p : α → β → γ) t s, m232 p t s = p t s
theorem p232 : P232 := by simp [P232, m232]
def m234 (widen : α → β) (ratType : β → γ) t := ratType (widen t)
def P234 : Prop := ∀ (α β γ : Type) (w : α → β) (r : β → γ) t,
  m234 w r t = r (w t)
theorem p234 : P234 := by simp [P234, m234]
def m236 : Jl α := .error (.overflowError "cannot negate unsigned number")
def P236 : Prop := ∀ (α : Type), @m236 α = .error (.overflowError "cannot negate unsigned number")
theorem p236 : P236 := by simp [P236, m236]

def m321 (rationalize : α → β) x := rationalize x
def P321 : Prop := ∀ (α β : Type) (r : α → β) x, m321 r x = r x
theorem p321 : P321 := by simp [P321, m321]
def m322 (rationalize : α → β) (z : RationalModel.Pair α) :=
  RationalModel.rationalizeComplex rationalize z
def P322 : Prop := ∀ (α β : Type) (r : α → β) z,
  m322 r z = ⟨r z.re, r z.im⟩
theorem p322 : P322 := by simp [P322, m322, RationalModel.rationalizeComplex]
def m323 := @m322
def P323 : Prop := P322
theorem p323 : P323 := p322
def m324 (rationalize : α → β → γ) x tol := rationalize x tol
def P324 : Prop := ∀ (α β γ : Type) (r : α → β → γ) x t, m324 r x t = r x t
theorem p324 : P324 := by simp [P324, m324]
def m325 (rationalize : α → β) x := rationalize x
def P325 : Prop := ∀ (α β : Type) (r : α → β) x, m325 r x = r x
theorem p325 : P325 := by simp [P325, m325]
def m326 (convert : α → Jl β) (ratFloat : Unit → Jl β) x un fit tol :=
  RationalModel.rationalizeRat convert ratFloat x un fit tol
def P326 : Prop := ∀ (α β : Type) (c : α → Jl β) (r : Unit → Jl β) x u f t,
  HasResult (m326 c r x u f t)
theorem p326 : P326 := by simp [P326, HasResult]
def m334 (x : Int) := RationalModel.rationalizeIntegerDefault x
def P334 : Prop := ∀ x, m334 x = ⟨x, 1⟩
theorem p334 : P334 := by simp [P334, m334, RationalModel.rationalizeIntegerDefault]
def m343 : Jl α := .error (.methodError "rationalize")
def P343 : Prop := ∀ (α : Type), @m343 α = .error (.methodError "rationalize")
theorem p343 : P343 := by simp [P343, m343]

def m360 (x : α) := RationalModel.numeratorIntegral x
def P360 : Prop := ∀ (α : Type) (x : α), m360 x = x
theorem p360 : P360 := by simp [P360, m360, RationalModel.numeratorIntegral]
def m361 := @numerator
def P361 : Prop := ∀ (t : IntTy) (x : Rat t), @m361 t x = x.num
theorem p361 : P361 := by simp [P361, m361, numerator]
def m362 (num den : α → β) (mul div : β → β → β) (complex : β → β → γ)
    (real imag : α → α) z common :=
  RationalModel.numeratorComplex num den mul div complex real imag z common
def P362 : Prop := ∀ (α β γ : Type) (n d : α → β) (m q : β → β → β)
  (c : β → β → γ) (r i : α → α) z x, HasResult (m362 n d m q c r i z x)
theorem p362 : P362 := by simp [P362, HasResult]
def m383 (one : α → α) x := RationalModel.denominatorIntegral one x
def P383 : Prop := ∀ (α : Type) (o : α → α) x, m383 o x = o x
theorem p383 : P383 := by simp [P383, m383, RationalModel.denominatorIntegral]
def m384 := @denominator
def P384 : Prop := ∀ (t : IntTy) (x : Rat t), @m384 t x = x.den
theorem p384 : P384 := by simp [P384, m384, denominator]
def m385 (den : α → β) (lcm : β → β → β) (real imag : α → α) z :=
  RationalModel.denominatorComplex den lcm real imag z
def P385 : Prop := ∀ (α β : Type) (d : α → β) (l : β → β → β)
  (r i : α → α) z, m385 d l r i z = l (d (r z)) (d (i z))
theorem p385 : P385 := by simp [P385, m385, RationalModel.denominatorComplex]

def m628 (nonneg : Int → Bool) (pow : α → Int → α) (inv : α → α) x n :=
  RationalModel.powerInteger nonneg pow inv x n
def P628 : Prop := ∀ (α : Type) (p : Int → Bool) (pow : α → Int → α) (i : α → α) x n,
  HasResult (m628 p pow i x n)
theorem p628 : P628 := by simp [P628, HasResult]
def m632 (div : α → α → β) (pow : γ → β → δ) x n d :=
  RationalModel.powerRationalExponent div pow x n d
def P632 : Prop := ∀ (α β γ δ : Type) (d : α → α → β) (p : γ → β → δ) x n q,
  m632 d p x n q = p x (d n q)
theorem p632 : P632 := by simp [P632, m632, RationalModel.powerRationalExponent]
def m633 := @m632
def P633 : Prop := P632
theorem p633 : P633 := p632
def m634 (convert : α → β) (pow : γ → β → δ) z p := pow z (convert p)
def P634 : Prop := ∀ (α β γ δ : Type) (c : α → β) (p : γ → β → δ) z x,
  m634 c p z x = p z (c x)
theorem p634 : P634 := by simp [P634, m634]
def m636 (one : RationalModel.Pair α → RationalModel.Pair α) z n :=
  RationalModel.powerBool one z n
def P636 : Prop := ∀ (α : Type) (one : RationalModel.Pair α → RationalModel.Pair α) z n,
  m636 one z n = if n then z else one z
theorem p636 : P636 := by simp [P636, m636, RationalModel.powerBool]
def m637 (power : α → Int → α) (inv : α → α) x n :=
  if n ≥ 0 then power x n else power (inv x) (-n)
def P637 : Prop := ∀ (α : Type) (p : α → Int → α) (i : α → α) x n,
  m637 p i x n = if n ≥ 0 then p x n else p (i x) (-n)
theorem p637 : P637 := by simp [P637, m637]
def m641 {t} (x : Rat t) := RationalModel.iszero x
def P641 : Prop := ∀ (t : IntTy) (x : Rat t), m641 x = (x.num.val == 0)
theorem p641 : P641 := by simp [P641, m641, RationalModel.iszero]
def m642 {t} (x : Rat t) := RationalModel.isone x
def P642 : Prop := ∀ (t : IntTy) (x : Rat t), m642 x = (x.num.val == 1 && x.den.val == 1)
theorem p642 : P642 := by simp [P642, m642, RationalModel.isone]
def m644 (sub mul div add : α → α → α) j d a b := RationalModel.lerpi sub mul div add j d a b
def P644 : Prop := ∀ (α : Type) (s m d a : α → α → α) j n x y,
  HasResult (m644 s m d a j n x y)
theorem p644 : P644 := by simp [P644, HasResult]
def m648 (float : α → β) t := float t
def P648 : Prop := ∀ (α β : Type) (f : α → β) t, m648 f t = f t
theorem p648 : P648 := by simp [P648, m648]

def m387 {t} (x : Rat t) := RationalModel.sign x
def P387 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (m387 x)
theorem p387 : P387 := by simp [P387, HasResult]
def m388 {t} (x : Rat t) := RationalModel.signbit x
def P388 : Prop := ∀ (t : IntTy) (x : Rat t), m388 x = decide (x.num.val < 0)
theorem p388 : P388 := by simp [P388, m388, RationalModel.signbit]
def m390 := @abs
def P390 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (@m390 t x)
theorem p390 : P390 := by simp [P390, HasResult]
def m392 (t : IntTy) := RationalModel.typemin t
def P392 : Prop := ∀ t, HasResult (m392 t)
theorem p392 : P392 := by simp [P392, HasResult]
def m393 := m392
def P393 : Prop := ∀ t, HasResult (m393 t)
theorem p393 : P393 := by simp [P393, HasResult]
def m394 (t : IntTy) := RationalModel.typemax t
def P394 : Prop := ∀ t, m394 t = ⟨JInt.lit t 1, JInt.lit t 0⟩
theorem p394 : P394 := by simp [P394, m394, RationalModel.typemax]
def m396 {t} (x : Rat t) := RationalModel.isinteger x
def P396 : Prop := ∀ (t : IntTy) (x : Rat t), m396 x = (x.den.val == 1)
theorem p396 : P396 := by simp [P396, m396, RationalModel.isinteger]
def m397 {t} (pow2 : JInt t → Bool) (x : Rat t) := RationalModel.ispow2 pow2 x
def P397 : Prop := ∀ (t : IntTy) (p : JInt t → Bool) x,
  m397 p x = (p x.num && p x.den)
theorem p397 : P397 := by simp [P397, m397, RationalModel.ispow2]
def m399 := @pos
def P399 : Prop := ∀ (t : IntTy) (x : Rat t), @m399 t x = ⟨x.num, x.den⟩
theorem p399 : P399 := by simp [P399, m399, pos]
def m400 := @RationalModel.negUnchecked
def P400 : Prop := ∀ (t : IntTy) (x : Rat t), @m400 t x = ⟨-x.num, x.den⟩
theorem p400 : P400 := by simp [P400, m400, RationalModel.negUnchecked]
def m402 := @neg
def P402 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (@m402 t x)
theorem p402 : P402 := by simp [P402, HasResult]
def m406 (name : String) : Jl α := .error (.overflowError name)
def P406 : Prop := ∀ (α : Type) n, @m406 α n = .error (.overflowError n)
theorem p406 : P406 := by simp [P406, m406]
def m408 := @neg
def P408 : Prop := P402
theorem p408 : P408 := p402
def m413 := @RationalModel.negWrap
def P413 : Prop := ∀ (t : IntTy) (x : Rat t), @m413 t x = ⟨-x.num, x.den⟩
theorem p413 : P413 := by simp [P413, m413, RationalModel.negWrap]
def m424 := @RationalModel.addWrap
def P424 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m424 t x y)
theorem p424 : P424 := by simp [P424, HasResult]
def m442 := @RationalModel.subWrap
def P442 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m442 t x y)
theorem p442 : P442 := by simp [P442, HasResult]
def m453 {t} (op : JInt t → JInt t → Jl (JInt t)) (x y : Rat t) :=
  do
    let p ← divgcd x.den y.den
    let a ← JuliaLean.IntArith.Checked.checkedMul x.num p.2
    let b ← JuliaLean.IntArith.Checked.checkedMul y.num p.1
    let n ← op a b
    let d ← JuliaLean.IntArith.Checked.checkedMul x.den p.2
    ofInts n d
def P453 : Prop := ∀ (t : IntTy) (op : JInt t → JInt t → Jl (JInt t)) x y,
  HasResult (m453 op x y)
theorem p453 : P453 := by simp [P453, HasResult]
def m462 := @withInt
def P462 : Prop := ∀ (t : IntTy) op (x : Rat t) (y : JInt t), HasResult (@m462 t op x y)
theorem p462 : P462 := by simp [P462, HasResult]
def m469 := @intWith
def P469 : Prop := ∀ (t : IntTy) op (y : JInt t) (x : Rat t), HasResult (@m469 t op y x)
theorem p469 : P469 := by simp [P469, HasResult]
def m476 := @intRemainder
def P476 : Prop := ∀ (t : IntTy) op (y : JInt t) (x : Rat t), HasResult (@m476 t op y x)
theorem p476 : P476 := by simp [P476, HasResult]
def m482 := @mul
def P482 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m482 t x y)
theorem p482 : P482 := by simp [P482, HasResult]
def m487 := @mulInt
def P487 : Prop := ∀ (t : IntTy) (x : Rat t) y, HasResult (@m487 t x y)
theorem p487 : P487 := by simp [P487, HasResult]
def m491 := @intMul
def P491 : Prop := ∀ (t : IntTy) y (x : Rat t), HasResult (@m491 t y x)
theorem p491 : P491 := by simp [P491, HasResult]
def m497 := @RationalModel.boolMul
def P497 : Prop := ∀ (t : IntTy) b (x : Rat t), HasResult (@m497 t b x)
theorem p497 : P497 := by simp [P497, HasResult]
def m500 {t} (x : Rat t) b := RationalModel.boolMul b x
def P500 : Prop := ∀ (t : IntTy) (x : Rat t) b, HasResult (m500 x b)
theorem p500 : P500 := by simp [P500, HasResult]
def m501 := @divInt
def P501 : Prop := ∀ (t : IntTy) (x : Rat t) y, HasResult (@m501 t x y)
theorem p501 : P501 := by simp [P501, HasResult]
def m502 := @intDiv
def P502 : Prop := ∀ (t : IntTy) x (y : Rat t), HasResult (@m502 t x y)
theorem p502 : P502 := by simp [P502, HasResult]
def m503 := @inv
def P503 : Prop := ∀ (t : IntTy) (x : Rat t), HasResult (@m503 t x)
theorem p503 : P503 := by simp [P503, HasResult]
def m505 := @RationalModel.fma
def P505 : Prop := ∀ (t : IntTy) (x y z : Rat t), HasResult (@m505 t x y z)
theorem p505 : P505 := by simp [P505, HasResult]

def m507 := @eq
def P507 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m507 t s x y)
theorem p507 : P507 := by simp [P507, HasResult]
def m508 := @lt
def P508 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m508 t s x y)
theorem p508 : P508 := by simp [P508, HasResult]
def m510 := @le
def P510 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m510 t s x y)
theorem p510 : P510 := by simp [P510, HasResult]
def m514 := @eqInt
def P514 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : JInt s), HasResult (@m514 t s x y)
theorem p514 : P514 := by simp [P514, HasResult]
def m515 {t s} (x : JInt t) (y : Rat s) := eqInt y x
def P515 : Prop := ∀ (t s : IntTy) (x : JInt t) (y : Rat s), HasResult (m515 x y)
theorem p515 : P515 := by simp [P515, HasResult]
def m516 := @ltInt
def P516 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : JInt s), HasResult (@m516 t s x y)
theorem p516 : P516 := by simp [P516, HasResult]
def m517 := @intLt
def P517 : Prop := ∀ (t s : IntTy) (x : JInt t) (y : Rat s), HasResult (@m517 t s x y)
theorem p517 : P517 := by simp [P517, HasResult]
def m518 := @leInt
def P518 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : JInt s), HasResult (@m518 t s x y)
theorem p518 : P518 := by simp [P518, HasResult]
def m519 := @intLe
def P519 : Prop := ∀ (t s : IntTy) (x : JInt t) (y : Rat s), HasResult (@m519 t s x y)
theorem p519 : P519 := by simp [P519, HasResult]
def m521 := @RationalModel.eqFloat
def P521 : Prop := ∀ (α β γ : Type) (finite : α → Bool) (ones : β → Nat)
  (ld : α → Int → α) (top : β → Int) (eqi : α → γ → Bool)
  (div : γ → β → α) (eqf : α → α → Bool) x n d,
  HasResult (@m521 α β γ finite ones ld top eqi div eqf x n d)
theorem p521 : P521 := by simp [P521, HasResult]
def m529 (eq : α → β → Bool) x y := eq y x
def P529 : Prop := ∀ (α β : Type) (eq : α → β → Bool) x y, m529 eq y x = eq x y
theorem p529 : P529 := by simp [P529, m529]
def m533 (rel : α → β → γ) x y := rel x y
def P533 : Prop := ∀ (α β γ : Type) (r : α → β → γ) x y, m533 r x y = r x y
theorem p533 : P533 := by simp [P533, m533]
def m583 := @RationalModel.eqComplex
def P583 : Prop := ∀ (α β : Type) (real : RationalModel.Pair α → Bool)
  (eq : α → β → Bool) z x, HasResult (@m583 α β real eq z x)
theorem p583 : P583 := by simp [P583, HasResult]
def m584 := @RationalModel.eqComplex
def P584 : Prop := P583
theorem p584 : P584 := p583

def m586 := @quotientInt
def P586 : Prop := ∀ (t : IntTy) (x : Rat t) y mode, HasResult (@m586 t x y mode)
theorem p586 : P586 := by simp [P586, HasResult]
def m590 := @intQuotient
def P590 : Prop := ∀ (t : IntTy) x (y : Rat t) mode, HasResult (@m590 t x y mode)
theorem p590 : P590 := by simp [P590, HasResult]
def m594 := @quotient
def P594 : Prop := ∀ (t : IntTy) (x y : Rat t) mode, HasResult (@m594 t x y mode)
theorem p594 : P594 := by simp [P594, HasResult]
def m602 := @quotient
def P602 : Prop := P594
theorem p602 : P602 := p594
def m606 := @quotientMixed
def P606 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m606 t s x y .toZero)
theorem p606 : P606 := by simp [P606, HasResult]
def m607 := @fldMixed
def P607 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m607 t s x y)
theorem p607 : P607 := by simp [P607, HasResult]
def m608 := @cldMixed
def P608 : Prop := ∀ (t s : IntTy) (x : Rat t) (y : Rat s), HasResult (@m608 t s x y)
theorem p608 : P608 := by simp [P608, HasResult]
def m612 {t} (x : Rat t) mode := round t x mode
def P612 : Prop := ∀ (t : IntTy) (x : Rat t) mode, HasResult (m612 x mode)
theorem p612 : P612 := by simp [P612, HasResult]
def m614 := @round
def P614 : Prop := ∀ target (t : IntTy) (x : Rat t) mode, HasResult (@m614 target t x mode)
theorem p614 : P614 := by simp [P614, HasResult]
def m621 := @RationalModel.roundBool
def P621 : Prop := ∀ (α β : Type) a b (c : α → Jl β) x, HasResult (@m621 α β a b c x)
theorem p621 : P621 := by simp [P621, HasResult]

def m650 := @RationalModel.gcdRat
def P650 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m650 t x y)
theorem p650 : P650 := by simp [P650, HasResult]
def m656 := @RationalModel.lcmRat
def P656 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m656 t x y)
theorem p656 : P656 := by simp [P656, HasResult]
def m662 := @RationalModel.gcdxRat
def P662 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m662 t x y)
theorem p662 : P662 := by simp [P662, HasResult]
def m670 := @RationalModel.idivRat
def P670 : Prop := ∀ (t : IntTy) (x y : Rat t), HasResult (@m670 t x y)
theorem p670 : P670 := by simp [P670, HasResult]
def m678 := @RationalModel.decompose
def P678 : Prop := ∀ (t : IntTy) (x : Rat t), @m678 t x = (x.num.val, 0, x.den.val)
theorem p678 : P678 := by simp [P678, m678, RationalModel.decompose]
def m679 := @JuliaLean.Promotion.hashRat64
def P679 : Prop := ∀ (t : IntTy) (x : Rat t) h, HasResult (@m679 t x h)
theorem p679 : P679 := by simp [P679, HasResult]
def m707 := @RationalModel.rangeLength
def P707 : Prop := ∀ (t : IntTy) (f l : Rat t), HasResult (@m707 t f l)
theorem p707 : P707 := by simp [P707, HasResult]
def m713 := @RationalModel.checkedRangeLength
def P713 : Prop := ∀ (t : IntTy) (f l : Rat t) e, HasResult (@m713 t f l e)
theorem p713 : P713 := by simp [P713, HasResult]

end JuliaLean.NumbersCov.Rows.Rational
