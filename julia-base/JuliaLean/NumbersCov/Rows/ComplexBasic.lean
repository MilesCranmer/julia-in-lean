import JuliaLean.NumbersCov.Rows.Common

namespace JuliaLean.NumbersCov.Rows.Complex

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

abbrev C := ComplexModel.Cx

def m17 (promote : α → β → γ × γ) x y := ComplexModel.constructPromoted promote x y
def P17 : Prop := ∀ (α β γ : Type) (p : α → β → γ × γ) x y, HasResult (m17 p x y)
theorem p17 : P17 := by simp [P17, HasResult]
def m18 (zero : α → α) x := ComplexModel.Cx.mk x (zero x)
def P18 : Prop := ∀ (α : Type) (z : α → α) x, m18 z x = ⟨x, z x⟩
theorem p18 : P18 := by simp [P18, m18]
def m42 (convert : α → β) (zero : β) x := ComplexModel.Cx.mk (convert x) zero
def P42 : Prop := ∀ (α β : Type) (c : α → β) z x, m42 c z x = ⟨c x, z⟩
theorem p42 : P42 := by simp [P42, m42]
def m43 (convert : α → β) (z : C α) := ComplexModel.Cx.mk (convert z.re) (convert z.im)
def P43 : Prop := ∀ (α β : Type) (c : α → β) z, m43 c z = ⟨c z.re, c z.im⟩
theorem p43 : P43 := by simp [P43, m43]
def m44 (isreal : C α → Bool) (convert : α → β) name z :=
  ComplexModel.realConvert isreal convert name z
def P44 : Prop := ∀ (α β : Type) (r : C α → Bool) (c : α → β) n z,
  HasResult (m44 r c n z)
theorem p44 : P44 := by simp [P44, HasResult]
def m47 (z : C α) := z
def P47 : Prop := ∀ (α : Type) (z : C α), m47 z = z
theorem p47 : P47 := by simp [P47, m47]
def m49 (promote : α → β → γ) (complexType : γ → δ) t s := complexType (promote t s)
def P49 : Prop := ∀ (α β γ δ : Type) (p : α → β → γ) (c : γ → δ) t s,
  m49 p c t s = c (p t s)
theorem p49 : P49 := by simp [P49, m49]
def m51 := @m49
def P51 : Prop := P49
theorem p51 : P51 := p49
def m54 (widen : α → β) (complexType : β → γ) t := complexType (widen t)
def P54 : Prop := ∀ (α β γ : Type) (w : α → β) (c : β → γ) t,
  m54 w c t = c (w t)
theorem p54 : P54 := by simp [P54, m54]
def m56 (complexType : α → β) t := complexType t
def P56 : Prop := ∀ (α β : Type) (c : α → β) t, m56 c t = c t
theorem p56 : P56 := by simp [P56, m56]
def m57 (float : α → β) (complexType : β → γ) t := complexType (float t)
def P57 : Prop := ∀ (α β γ : Type) (f : α → β) (c : β → γ) t,
  m57 f c t = c (f t)
theorem p57 : P57 := by simp [P57, m57]
def m72 (z : C α) := z.re
def P72 : Prop := ∀ (α : Type) (z : C α), m72 z = z.re
theorem p72 : P72 := by simp [P72, m72]
def m87 (z : C α) := z.im
def P87 : Prop := ∀ (α : Type) (z : C α), m87 z = z.im
theorem p87 : P87 := by simp [P87, m87]
def m88 (x : α) := x
def P88 : Prop := ∀ (α : Type) (x : α), m88 x = x
theorem p88 : P88 := by simp [P88, m88]
def m89 (zero : α → α) x := zero x
def P89 : Prop := ∀ (α : Type) (z : α → α) x, m89 z x = z x
theorem p89 : P89 := by simp [P89, m89]
def m102 (real imag : α → β) z := (real z, imag z)
def P102 : Prop := ∀ (α β : Type) (r i : α → β) z, m102 r i z = (r z, i z)
theorem p102 : P102 := by simp [P102, m102]
def m120 (zero : α → β) (real : β → γ) (typeOf : γ → δ) t := typeOf (real (zero t))
def P120 : Prop := ∀ (α β γ δ : Type) (z : α → β) (r : β → γ) (ty : γ → δ) t,
  m120 z r ty t = ty (r (z t))
theorem p120 : P120 := by simp [P120, m120]
def m121 (t : α) := t
def P121 : Prop := ∀ (α : Type) (t : α), m121 t = t
theorem p121 : P121 := by simp [P121, m121]
def m122 (fieldType : α → β) t := fieldType t
def P122 : Prop := ∀ (α β : Type) (f : α → β) t, m122 f t = f t
theorem p122 : P122 := by simp [P122, m122]
def m123 : Option α := none
def P123 : Prop := ∀ (α : Type), @m123 α = none
theorem p123 : P123 := by simp [P123, m123]
def m124 : Jl α := .error (.methodError "real")
def P124 : Prop := ∀ (α : Type), @m124 α = .error (.methodError "real")
theorem p124 : P124 := by simp [P124, m124]

def m148 (_ : α) := true
def P148 : Prop := ∀ (α : Type) (x : α), m148 x = true
theorem p148 : P148 := by simp [P148, m148]
def m150 (o : GenericOps α) (integer : α → Bool) z := ComplexModel.isinteger o integer z
def P150 : Prop := ∀ (α : Type) (o : GenericOps α) (i : α → Bool) z,
  m150 o i z = (o.eq z.im (o.zero z.im) && i z.re)
theorem p150 : P150 := by simp [P150, m150, ComplexModel.isinteger, ComplexModel.isreal]
def m151 (o : GenericOps α) z := ComplexModel.isfinite o z
def P151 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m151 o z = (o.isfinite z.re && o.isfinite z.im)
theorem p151 : P151 := by simp [P151, m151, ComplexModel.isfinite]
def m152 (o : GenericOps α) z := ComplexModel.isnan o z
def P152 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m152 o z = (o.isnan z.re || o.isnan z.im)
theorem p152 : P152 := by simp [P152, m152, ComplexModel.isnan]
def m153 (o : GenericOps α) z := ComplexModel.isinf o z
def P153 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m153 o z = (o.isinf z.re || o.isinf z.im)
theorem p153 : P153 := by simp [P153, m153, ComplexModel.isinf]
def m154 (o : GenericOps α) z := ComplexModel.iszero o z
def P154 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m154 o z = (o.eq z.re (o.zero z.re) && o.eq z.im (o.zero z.im))
theorem p154 : P154 := by simp [P154, m154, ComplexModel.iszero]
def m155 (o : GenericOps α) z := ComplexModel.isone o z
def P155 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m155 o z = (o.eq z.re (o.one z.re) && o.eq z.im (o.zero z.im))
theorem p155 : P155 := by simp [P155, m155, ComplexModel.isone]
def m168 (z : C α) := z
def P168 : Prop := ∀ (α : Type) (z : C α), m168 z = z
theorem p168 : P168 := by simp [P168, m168]
def m169 (zero : α → α) x := ComplexModel.Cx.mk x (zero x)
def P169 : Prop := ∀ (α : Type) (z : α → α) x, m169 z x = ⟨x, z x⟩
theorem p169 : P169 := by simp [P169, m169]
def m170 (promote : α → β → γ × γ) x y := ComplexModel.constructPromoted promote x y
def P170 : Prop := ∀ (α β γ : Type) (p : α → β → γ × γ) x y, HasResult (m170 p x y)
theorem p170 : P170 := by simp [P170, HasResult]
def m190 (complexType : α → β) t := complexType t
def P190 : Prop := ∀ (α β : Type) (c : α → β) t, m190 c t = c t
theorem p190 : P190 := by simp [P190, m190]
def m191 := @m190
def P191 : Prop := P190
theorem p191 : P191 := p190
def m192 : Option α := none
def P192 : Prop := ∀ (α : Type), @m192 α = none
theorem p192 : P192 := by simp [P192, m192]
def m195 : Jl α := .error (.methodError "complex")
def P195 : Prop := ∀ (α : Type), @m195 α = .error (.methodError "complex")
theorem p195 : P195 := by simp [P195, m195]
def m197 (o : GenericOps α) z y := ComplexModel.flipsign o z y
def P197 : Prop := ∀ (α : Type) (o : GenericOps α) z y, HasResult (m197 o z y)
theorem p197 : P197 := by simp [P197, HasResult]
def m199 realText imagText compact star := ComplexModel.showParts realText imagText compact star
def P199 : Prop := ∀ r i c s, HasResult (m199 r i c s)
theorem p199 : P199 := by simp [P199, HasResult]
def m219 re im isUnit := ComplexModel.showBool isUnit re im
def P219 : Prop := ∀ r i u, HasResult (m219 r i u)
theorem p219 : P219 := by simp [P219, HasResult]
def m222 (render : α → String) parens z := ComplexModel.showUnquoted render parens z
def P222 : Prop := ∀ (α : Type) (r : α → String) p z, HasResult (m222 r p z)
theorem p222 : P222 := by simp [P222, HasResult]
def m232 (read : Unit → α × α) := ComplexModel.readPair read
def P232 : Prop := ∀ (α : Type) (r : Unit → α × α), HasResult (m232 r)
theorem p232 : P232 := by simp [P232, HasResult]
def m237 (write : α → α → β) z := ComplexModel.writePair write z
def P237 : Prop := ∀ (α β : Type) (w : α → α → β) z, m237 w z = w z.re z.im
theorem p237 : P237 := by simp [P237, m237, ComplexModel.writePair]
def m242 (swap : α → α) z := ComplexModel.bswap swap z
def P242 : Prop := ∀ (α : Type) (s : α → α) z, m242 s z = ⟨s z.re, s z.im⟩
theorem p242 : P242 := by simp [P242, m242, ComplexModel.bswap]
def m246 (o : GenericOps α) z w := ComplexModel.eq o z w
def P246 : Prop := ∀ (α : Type) (o : GenericOps α) z w,
  m246 o z w = (o.eq z.re w.re && o.eq z.im w.im)
theorem p246 : P246 := by simp [P246, m246, ComplexModel.eq]
def m248 (o : GenericOps α) x z := ComplexModel.eqRealLeft o x z
def P248 : Prop := ∀ (α : Type) (o : GenericOps α) x z, HasResult (m248 o x z)
theorem p248 : P248 := by simp [P248, HasResult]
def m252 (eq : α → α → Bool) (zero : α → α) x z := ComplexModel.isequalRealComplex eq zero x z
def P252 : Prop := ∀ (α : Type) (e : α → α → Bool) (z : α → α) x w,
  m252 e z x w = (e x w.re && e (z x) w.im)
theorem p252 : P252 := by simp [P252, m252, ComplexModel.isequalRealComplex]
def m254 (o : GenericOps α) (mem : α → β → Bool) z r := ComplexModel.memRealRange o mem z r
def P254 : Prop := ∀ (α β : Type) (o : GenericOps α) (m : α → β → Bool) z r,
  HasResult (m254 o m z r)
theorem p254 : P254 := by simp [P254, HasResult]

def m282 (o : GenericOps α) z := ComplexModel.abs2 o z
def P282 : Prop := ∀ (α : Type) (o : GenericOps α) z,
  m282 o z = o.add (o.mul z.re z.re) (o.mul z.im z.im)
theorem p282 : P282 := by simp [P282, m282, ComplexModel.abs2]
def m283 (o : ComplexModel.ScalarOps α) z := ComplexModel.invGeneric o z
def P283 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z, HasResult (m283 o z)
theorem p283 : P283 := by simp [P283, HasResult]
def m288 (float : C α → C β) (inv : C β → C β) z := ComplexModel.invInteger float inv z
def P288 : Prop := ∀ (α β : Type) (f : C α → C β) (i : C β → C β) z,
  m288 f i z = i (f z)
theorem p288 : P288 := by simp [P288, m288, ComplexModel.invInteger]
def m290 (o : GenericOps α) z := ComplexModel.pos o z
def P290 : Prop := ∀ (α : Type) (o : GenericOps α) z, HasResult (m290 o z)
theorem p290 : P290 := by simp [P290, HasResult]
def m291 (o : GenericOps α) z := ComplexModel.neg o z
def P291 : Prop := ∀ (α : Type) (o : GenericOps α) z, HasResult (m291 o z)
theorem p291 : P291 := by simp [P291, HasResult]
def m292 (o : GenericOps α) z w := ComplexModel.add o z w
def P292 : Prop := ∀ (α : Type) (o : GenericOps α) z w, HasResult (m292 o z w)
theorem p292 : P292 := by simp [P292, HasResult]
def m293 (o : GenericOps α) z w := ComplexModel.sub o z w
def P293 : Prop := ∀ (α : Type) (o : GenericOps α) z w, HasResult (m293 o z w)
theorem p293 : P293 := by simp [P293, HasResult]
def m294 (o : GenericOps α) z w := ComplexModel.mul o z w
def P294 : Prop := ∀ (α : Type) (o : GenericOps α) z w, HasResult (m294 o z w)
theorem p294 : P294 := by simp [P294, HasResult]
def m297 := @m291
def P297 : Prop := P291
theorem p297 : P297 := p291
def m298 := @m292
def P298 : Prop := P292
theorem p298 : P298 := p292
def m299 := @m293
def P299 : Prop := P293
theorem p299 : P299 := p293
def m300 := @m294
def P300 : Prop := P294
theorem p300 : P300 := p294
def m303 {A B C D E : Type} (promote : A → B → C → D × D × D)
    (mulsub : D → D → D → E) (a : A) (b : B) (c : C) :=
  ComplexModel.mulsubPromoted promote mulsub a b c
def P303 : Prop := ∀ (A B C D E : Type) (p : A → B → C → D × D × D)
  (m : D → D → D → E) a b c, HasResult (m303 p m a b c)
theorem p303 : P303 := by simp [P303, HasResult]
def m304 {α : Type} (muladd : α → α → α → α) (neg : α → α) (a b c : α) :=
  ComplexModel.mulsub muladd neg a b c
def P304 : Prop := ∀ (α : Type) (m : α → α → α → α) (n : α → α) a b c,
  m304 m n a b c = m a b (n c)
theorem p304 : P304 := by simp [P304, m304, ComplexModel.mulsub]

def scalarLeftAdd {α β γ δ : Type} (complex : γ → β → δ) (add : α → β → γ) x (z : C β) :=
  complex (add x z.re) z.im
def scalarRightAdd {α β γ δ : Type} (complex : γ → β → δ) (add : β → α → γ) (z : C β) x :=
  complex (add z.re x) z.im
def scalarLeftSub {α β γ δ : Type} (complex : γ → β → δ) (sub : α → β → γ) (neg : β → β) x (z : C β) :=
  complex (sub x z.re) (neg z.im)
def scalarRightSub {α β γ δ : Type} (complex : γ → β → δ) (sub : β → α → γ) (z : C β) x :=
  complex (sub z.re x) z.im
def scalarLeftMul {α β γ δ ε : Type} (complex : γ → δ → ε) (mulR : α → β → γ) (mulI : α → β → δ) x (z : C β) :=
  complex (mulR x z.re) (mulI x z.im)
def scalarRightMul {α β γ δ ε : Type} (complex : γ → δ → ε) (mulR : β → α → γ) (mulI : β → α → δ) (z : C β) x :=
  complex (mulR z.re x) (mulI z.im x)

def m311 := @scalarLeftAdd
def m312 := @scalarRightAdd
def m313 := @scalarLeftSub
def m314 := @scalarRightSub
def m315 := @scalarLeftMul
def m316 := @scalarRightMul
def m318 := @scalarLeftAdd
def m319 := @scalarRightAdd
def m320 := @scalarLeftSub
def m321 := @scalarRightSub
def m323 := @scalarRightMul
def m325 := @scalarLeftAdd
def m326 := @scalarRightAdd
def m327 := @scalarLeftSub
def m332 := @scalarRightSub
def m333 := @scalarLeftMul
def m334 := @scalarRightMul
def m337 := @scalarLeftAdd
def m338 := @scalarRightAdd
def m339 := @scalarLeftSub
def m344 := @scalarRightSub
def m345 := @scalarLeftMul
def m346 := @scalarRightMul

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

def m348 (muladd : C α → β → γ → δ) (x : β) (z : C α) (y : γ) := muladd z x y
def P348 : Prop := ∀ (α β γ δ : Type) (m : C α → β → γ → δ) x z y,
  m348 m x z y = m z x y
theorem p348 : P348 := by simp [P348, m348]
def m349 := @ComplexModel.muladdComplexReal
def P349 : Prop := ∀ (α : Type) (ma : α → α → α → α) (m : α → α → α) z x y,
  HasResult (@m349 α ma m z x y)
theorem p349 : P349 := by simp [P349, HasResult]
def m350 := @ComplexModel.muladdComplexScalar
def P350 : Prop := ∀ (α : Type) (ma : α → α → α → α) z x w,
  HasResult (@m350 α ma z x w)
theorem p350 : P350 := by simp [P350, HasResult]
def m352 := @ComplexModel.muladdRealRealComplex
def P352 : Prop := ∀ (α : Type) (ma : α → α → α → α) x y z,
  HasResult (@m352 α ma x y z)
theorem p352 : P352 := by simp [P352, HasResult]
def m353 := @ComplexModel.muladdComplexComplexReal
def P353 : Prop := ∀ (α : Type) (ma ms : α → α → α → α) (n : α → α)
  (m : α → α → α) z w x, HasResult (@m353 α ma ms n m z w x)
theorem p353 : P353 := by simp [P353, HasResult]
def m357 := @ComplexModel.realDivComplex
def P357 : Prop := ∀ (α β γ : Type) (p : α → C β → γ × C γ)
  (m : γ → C γ → C γ) (i : C γ → C γ) a z, HasResult (@m357 α β γ p m i a z)
theorem p357 : P357 := by simp [P357, HasResult]
def m358 := @ComplexModel.divReal
def P358 : Prop := ∀ (α : Type) (o : GenericOps α) z x, HasResult (@m358 α o z x)
theorem p358 : P358 := by simp [P358, HasResult]

def m360 := @ComplexModel.divGeneric
def P360 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) z w, HasResult (@m360 α o z w)
theorem p360 : P360 := by simp [P360, HasResult]
def m379 := @ComplexModel.divSmall
def P379 : Prop := ∀ (α β : Type) (s : ComplexModel.ScalarOps α)
  (w : ComplexModel.ScalarOps β) (wide : C α → C β) (n : C β → C α) z q,
  HasResult (@m379 α β s w wide n z q)
theorem p379 : P379 := by simp [P379, HasResult]
def m424 := @JuliaLean.Complex.CF64.cdiv
def P424 : Prop := ∀ a b c d, HasResult (m424 a b c d)
theorem p424 : P424 := by simp [P424, HasResult]
def m433 := @JuliaLean.Complex.CF64.scalingCdiv
def P433 : Prop := ∀ a b c d x y, HasResult (m433 a b c d x y)
theorem p433 : P433 := by simp [P433, HasResult]
def m439 := @JuliaLean.Complex.CF64.scaleargsCdiv
def P439 : Prop := ∀ a b c d x y, HasResult (m439 a b c d x y)
theorem p439 : P439 := by simp [P439, HasResult]
def m476 := @ComplexModel.invSmall
def P476 : Prop := ∀ (α β : Type) (s : ComplexModel.ScalarOps α)
  (w : ComplexModel.ScalarOps β) (wide : C α → C β) (n : C β → C α) z,
  HasResult (@m476 α β s w wide n z)
theorem p476 : P476 := by simp [P476, HasResult]
def m482 := @JuliaLean.Complex.CF64.inv
def P482 : Prop := ∀ z, HasResult (m482 z)
theorem p482 : P482 := by simp [P482, HasResult]
def m511 := @JuliaLean.Complex.CF64.robustCinv
def P511 : Prop := ∀ c d, HasResult (m511 c d)
theorem p511 : P511 := by simp [P511, HasResult]
def m519 := @ComplexModel.ssqs
def P519 : Prop := ∀ (α : Type) (o : ComplexModel.ScalarOps α) x y,
  HasResult (@m519 α o x y)
theorem p519 : P519 := by simp [P519, HasResult]

end JuliaLean.NumbersCov.Rows.Complex
