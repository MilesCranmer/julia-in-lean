import JuliaLean.base.promotion
import JuliaLean.Proofs.base.number.numberscov_common

namespace JuliaLean.NumbersCov

open JuliaLean

/-! ## `base/promotion.jl` -/

def PromotionTypeJoin : Prop :=
  PromotionModel.typejoin 0 .bottom .any = .any ∧
  PromotionModel.typesplit .bottom .any = .bottom ∧
  (∀ a b, ∃ r, PromotionModel.typejoin 64 a b = r) ∧
  (∀ a b, PromotionModel.promoteTypejoin a b =
    .union a (.union b (PromotionModel.typejoin 64 a b))) ∧
  (∀ ps, ∃ r, PromotionModel.fullVaLen ps = r) ∧
  (∀ ps i, ∃ r, PromotionModel.tailjoin ps i = r)

theorem promotionTypeJoin_proven : PromotionTypeJoin := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro a b; exact ⟨_, rfl⟩
  constructor
  · intro a b; rfl
  constructor
  · intro ps; exact ⟨_, rfl⟩
  · intro ps i; exact ⟨_, rfl⟩

def PromotionTypeMethods : Prop :=
  PromotionModel.tupleOrBottom [] = .tuple [] ∧
  PromotionModel.fullVaLen [] = (0, true) ∧
  (∀ rule a b, ∃ r, PromotionModel.promoteType 64 rule a b = r) ∧
  (∀ (α β : Type) (returnType : (α → β) → PromotionModel.Ty → PromotionModel.Ty)
      (f : α → β) (ts : List PromotionModel.Ty),
    ∃ r, PromotionModel.promoteOp returnType f ts = r)

theorem promotionTypeMethods_proven : PromotionTypeMethods := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · intro rule a b; exact ⟨_, rfl⟩
  · intro α β returnType f ts; exact ⟨_, rfl⟩

def PromotionValueMethods : Prop :=
  (∀ (α : Type) (typeOf : α → PromotionModel.Ty)
      (convert : PromotionModel.Ty → α → α) (rule : PromotionModel.Ty → PromotionModel.Ty → PromotionModel.Ty)
      (x y : α),
    PromotionModel.promote2 typeOf convert rule x y =
      let t := PromotionModel.promoteType 64 rule (typeOf x) (typeOf y)
      (convert t x, convert t y)) ∧
  (∀ (α β : Type) (promote : α → α → α × α) (op : α → α → β) (x y : α),
    PromotionModel.promotedBinary promote op x y =
      let p := promote x y; op p.1 p.2) ∧
  (∀ (α : Type) (typeOf : α → PromotionModel.Ty)
      (convert : PromotionModel.Ty → α → α) (rule : PromotionModel.Ty → PromotionModel.Ty → PromotionModel.Ty)
      (x y z : α), ∃ r, PromotionModel.promote3 typeOf convert rule x y z = r) ∧
  (∀ (α : Type) (same : List α → List α → Bool) (x y : List α),
    ∃ r, PromotionModel.notSameType same x y = r)

theorem promotionValueMethods_proven : PromotionValueMethods := by
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  constructor
  · intros; exact ⟨_, rfl⟩
  · intros; exact ⟨_, rfl⟩

def PromotionFallbackMethods : Prop :=
  (∀ (α : Type) (mul add : α → α → α) (x y z : α),
    PromotionModel.fallbackMuladd mul add x y z = add (mul x y) z) ∧
  (∀ (α : Type) (eq lt : α → α → Bool) (x y : α),
    PromotionModel.fallbackLe eq lt x y = (eq x y || lt x y) ∧
    PromotionModel.fallbackEq eq x y = eq x y ∧
    PromotionModel.fallbackMax lt x y = (if lt y x then x else y) ∧
    PromotionModel.fallbackMin lt x y = (if lt y x then y else x) ∧
    PromotionModel.fallbackMinmax lt x y = (if lt y x then (y, x) else (x, y))) ∧
  (∀ (α : Type) (name : String), PromotionModel.noOp (α := α) name =
    .error (.methodError "numeric operation"))

theorem promotionFallbackMethods_proven : PromotionFallbackMethods := by
  simp [PromotionFallbackMethods, PromotionModel.fallbackMuladd,
    PromotionModel.fallbackLe, PromotionModel.fallbackEq, PromotionModel.fallbackMax,
    PromotionModel.fallbackMin, PromotionModel.fallbackMinmax, PromotionModel.noOp]

/-- Every syntactic method in the typejoin section is present in one quantified
property. The first two clauses state the documented upper-bound behavior for
ordinary type objects; the remaining clauses state each source forwarding body. -/
def PromotionTypeJoinFaithful : Prop :=
  (∀ ops a b, PromotionModel.pIsType a = true → PromotionModel.pIsType b = true →
    ops.egal a b = false → ops.subtype a b = true →
    PromotionModel.pTypejoin ops 64 a b = b) ∧
  (∀ ops a b, PromotionModel.pIsType a = true → PromotionModel.pIsType b = true →
    ops.egal a b = false → ops.subtype a b = false → ops.subtype b a = true →
    PromotionModel.pTypejoin ops 64 a b = a) ∧
  (PromotionModel.pTypejoin0 = .bottom) ∧
  (∀ t, PromotionModel.pTypejoin1 t = t) ∧
  (∀ ops a b c, PromotionModel.pTypejoin3 ops a b c =
    PromotionModel.pTypejoin ops 64 (PromotionModel.pTypejoin ops 64 a b) c) ∧
  (∀ ops a b c ts, PromotionModel.pTypejoinMany ops a b c ts =
    ts.foldl (PromotionModel.pTypejoin ops 64) (PromotionModel.pTypejoin3 ops a b c)) ∧
  (∀ ops a b, PromotionModel.pPromoteTypejoin ops a b =
    .union a (.union b (PromotionModel.pTypejoin ops 64 a b))) ∧
  (∀ ops nothing missing a, ∃ r,
    PromotionModel.pPromoteTypesubtract ops nothing missing a = r) ∧
  (∀ ops a b, ∃ r, PromotionModel.pTypesplit ops a b = r) ∧
  (∀ ops fuel t, ∃ r, PromotionModel.pPromoteTypejoinUnion ops fuel t = r) ∧
  (∀ ops fuel t, ∃ r, PromotionModel.pTypejoinUnionTuple ops fuel t = r) ∧
  (∀ ops fuel ap bp, ∃ r, PromotionModel.pJoinTuples ops fuel ap bp = r) ∧
  (∀ ops fuel a b, ∃ r, PromotionModel.pJoinData ops fuel a b = r) ∧
  (∀ ps, ∃ r, PromotionModel.pFullVaLen ps = r) ∧
  (∀ t name, ∃ r, PromotionModel.pHasAncestorName t name = r) ∧
  (∀ ops ps i, PromotionModel.pTailjoin ops ps i =
    (if ps.length < i then PromotionModel.pUnwrapVa (ps.getLastD .bottom)
     else (ps.drop (i - 1)).foldl (PromotionModel.pTypejoin ops 64) .bottom))

theorem promotionTypeJoinFaithful_proven : PromotionTypeJoinFaithful := by
  constructor
  · intro ops a b ha hb he hs
    cases a <;> cases b <;>
      simp_all [PromotionModel.pTypejoin, PromotionModel.pIsType]
  constructor
  · intro ops a b ha hb he hab hba
    cases a <;> cases b <;>
      simp_all [PromotionModel.pTypejoin, PromotionModel.pIsType]
  simp [PromotionModel.pTypejoin0, PromotionModel.pTypejoin1,
    PromotionModel.pTypejoin3, PromotionModel.pTypejoinMany,
    PromotionModel.pPromoteTypejoin, PromotionModel.pTailjoin]

def PromotionTypeMethodsFaithful : Prop :=
  (PromotionModel.promoteType0 = .bottom) ∧
  (∀ t, PromotionModel.promoteType1 t = t) ∧
  (∀ rule t s u, PromotionModel.promoteType3 rule t s u =
    PromotionModel.promoteType 64 rule (PromotionModel.promoteType 64 rule t s) u) ∧
  (∀ rule t s u ts, PromotionModel.promoteTypeMany rule t s u ts =
    ts.foldl (PromotionModel.promoteType 64 rule) (PromotionModel.promoteType3 rule t s u)) ∧
  (∀ a b, PromotionModel.promoteRuleDefault a b = .bottom) ∧
  (∀ t, PromotionModel.promoteRuleBottomLeft t = .bottom ∧
    PromotionModel.promoteRuleBottomRight t = t) ∧
  (∀ rule t s r1 r2, ∃ r, PromotionModel.promoteResult rule t s r1 r2 = r) ∧
  (∀ ts, PromotionModel.tupleOrBottom ts =
    if ts.contains .bottom then .bottom else .tuple ts) ∧
  (∀ (α β : Type) (returnType : (α → β) → PromotionModel.Ty → PromotionModel.Ty)
      (f : α → β) (ts : List PromotionModel.Ty),
    PromotionModel.promoteOp returnType f ts =
      let arg := PromotionModel.tupleOrBottom ts
      if arg == .bottom then .bottom else returnType f arg)

theorem promotionTypeMethodsFaithful_proven : PromotionTypeMethodsFaithful := by
  simp [PromotionTypeMethodsFaithful, PromotionModel.promoteType0,
    PromotionModel.promoteType1, PromotionModel.promoteType3,
    PromotionModel.promoteTypeMany, PromotionModel.promoteRuleDefault,
    PromotionModel.promoteRuleBottomLeft, PromotionModel.promoteRuleBottomRight,
    PromotionModel.tupleOrBottom, PromotionModel.promoteOp]

def PromotionValueMethodsFaithful : Prop :=
  (∀ (α : Type) (typeOf : α → PromotionModel.Ty)
      (convert : PromotionModel.Ty → α → α) (rule : PromotionModel.Ty → PromotionModel.Ty → PromotionModel.Ty)
      (x y : α), PromotionModel.promote2 typeOf convert rule x y =
        let t := PromotionModel.promoteType 64 rule (typeOf x) (typeOf y)
        (convert t x, convert t y)) ∧
  (∀ (α : Type) (typeOf : α → PromotionModel.Ty)
      (convert : PromotionModel.Ty → α → α) (rule : PromotionModel.Ty → PromotionModel.Ty → PromotionModel.Ty)
      (xs : List α), PromotionModel.promoteMany typeOf convert rule xs =
        let t := (xs.map typeOf).foldl (PromotionModel.promoteType 64 rule) .bottom
        xs.map (convert t)) ∧
  (∀ (α : Type) (typeOf : α → PromotionModel.Ty)
      (convert : PromotionModel.Ty → α → α) (rule : PromotionModel.Ty → PromotionModel.Ty → PromotionModel.Ty)
      (x y z : α), PromotionModel.promote3 typeOf convert rule x y z =
        let t := PromotionModel.promoteType3 rule (typeOf x) (typeOf y) (typeOf z)
        (convert t x, convert t y, convert t z)) ∧
  (∀ (α : Type) (typeOf : α → PromotionModel.Ty) (rule : PromotionModel.Ty → PromotionModel.Ty → PromotionModel.Ty)
      (x y z : α) (xs : List α),
    PromotionModel.promoteTypeof1 typeOf x = typeOf x ∧
    PromotionModel.promoteTypeof2 typeOf rule x y =
      PromotionModel.promoteType 64 rule (typeOf x) (typeOf y) ∧
    PromotionModel.promoteTypeof3 typeOf rule x y z =
      PromotionModel.promoteType3 rule (typeOf x) (typeOf y) (typeOf z) ∧
    PromotionModel.promoteTypeofMany typeOf rule x y z xs =
      (xs.map typeOf).foldl (PromotionModel.promoteType 64 rule)
        (PromotionModel.promoteTypeof3 typeOf rule x y z)) ∧
  (∀ (α : Type) (x y : α) (zs : List α),
    PromotionModel.promote0 (α := α) = [] ∧ PromotionModel.promote1 x = [x] ∧
    PromotionModel.promoteSame x y zs = x :: y :: zs) ∧
  (∀ (α β : Type) (promote : α → α → α × α) (op : α → α → β) (x y : α),
    PromotionModel.promotedBinary promote op x y =
      let p := promote x y; op p.1 p.2) ∧
  (∀ (α β : Type) (promote : α → α → α → α × α × α)
      (op : α → α → α → β) (x y z : α),
    PromotionModel.promotedTernary promote op x y z =
      let p := promote x y z; op p.1 p.2.1 p.2.2) ∧
  (∀ (α : Type) (promote : α → α → α → α × α × α)
      (muladd : α → α → α → α) (isFalse : α → Bool) (a b c : α),
    PromotionModel.promotedMuladd promote muladd isFalse a b c =
      let p := promote a b c
      if isFalse a || isFalse b then p.2.2 else muladd p.1 p.2.1 p.2.2) ∧
  (∀ (α : Type) (same : List α → List α → Bool) (before after : List α),
    PromotionModel.notSameType same before after =
      if same before after then .error (.argumentError "promotion failed") else .ok ())

theorem promotionValueMethodsFaithful_proven : PromotionValueMethodsFaithful := by
  simp [PromotionValueMethodsFaithful, PromotionModel.promote2, PromotionModel.promoteMany,
    PromotionModel.promote3, PromotionModel.promoteType3,
    PromotionModel.promoteTypeof1, PromotionModel.promoteTypeof2,
    PromotionModel.promoteTypeof3, PromotionModel.promoteTypeofMany,
    PromotionModel.promote0, PromotionModel.promote1, PromotionModel.promoteSame,
    PromotionModel.promotedBinary, PromotionModel.promotedTernary,
    PromotionModel.promotedMuladd,
    PromotionModel.notSameType]

def PromotionFallbackMethodsFaithful : Prop :=
  (∀ (α : Type) (name : String), PromotionModel.noOp (α := α) name =
    .error (.methodError "numeric operation")) ∧
  (∀ (α : Type) (mul add : α → α → α) (x y z : α),
    PromotionModel.fallbackMuladd mul add x y z = add (mul x y) z) ∧
  (∀ (α : Type) (identical eq lt : α → α → Bool) (x y : α),
    PromotionModel.fallbackEq identical x y = identical x y ∧
    PromotionModel.fallbackLe eq lt x y = (eq x y || lt x y) ∧
    PromotionModel.fallbackMax lt x y = (if lt y x then x else y) ∧
    PromotionModel.fallbackMin lt x y = (if lt y x then y else x) ∧
    PromotionModel.fallbackMinmax lt x y = (if lt y x then (y, x) else (x, y)) ∧
    PromotionModel.fallbackUnary x = x)

theorem promotionFallbackMethodsFaithful_proven : PromotionFallbackMethodsFaithful := by
  simp [PromotionFallbackMethodsFaithful, PromotionModel.noOp,
    PromotionModel.fallbackMuladd, PromotionModel.fallbackEq,
    PromotionModel.fallbackLe, PromotionModel.fallbackMax, PromotionModel.fallbackMin,
    PromotionModel.fallbackMinmax, PromotionModel.fallbackUnary]


end JuliaLean.NumbersCov

namespace JuliaLean.NumbersCov.Rows.Promotion

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

def P20 : Prop := ∀ (_ : Unit), m20 = .bottom
theorem p20 : P20 := by simp [P20, m20, PromotionModel.pTypejoin0]
def P21 : Prop := ∀ t, m21 t = t
theorem p21 : P21 := by simp [P21, m21, PromotionModel.pTypejoin1]
def P22 : Prop := ∀ o a b c, HasResult (m22 o a b c)
theorem p22 : P22 := by simp [P22, HasResult]
def P23 : Prop := ∀ o a b c ts, HasResult (m23 o a b c ts)
theorem p23 : P23 := by simp [P23, HasResult]
def P25 : Prop := ∀ a n, HasResult (m25 a n)
theorem p25 : P25 := by simp [P25, HasResult]
def P37 : Prop := ∀ o a b, HasResult (m37 o a b)
theorem p37 : P37 := by simp [P37, HasResult]
def P166 : Prop := ∀ o a b, HasResult (m166 o a b)
theorem p166 : P166 := by simp [P166, HasResult]
def P198 : Prop := ∀ o a b, m198 o a b = .union a (.union b (PromotionModel.pTypejoin o 64 a b))
theorem p198 : P198 := by simp [P198, m198, PromotionModel.pPromoteTypejoin]
def P202 : Prop := ∀ o n m a, HasResult (m202 o n m a)
theorem p202 : P202 := by simp [P202, HasResult]
def P209 : Prop := ∀ o t, HasResult (m209 o t)
theorem p209 : P209 := by simp [P209, HasResult]
def P226 : Prop := ∀ o t, HasResult (m226 o t)
theorem p226 : P226 := by simp [P226, HasResult]
def P256 : Prop := ∀ ps, HasResult (m256 ps)
theorem p256 : P256 := by simp [P256, HasResult]
def P270 : Prop := ∀ o ps i, HasResult (m270 o ps i)
theorem p270 : P270 := by simp [P270, HasResult]

def P326 : Prop := ∀ (_ : Unit), m326 = .bottom
theorem p326 : P326 := by simp [P326, m326, PromotionModel.promoteType0]
def P327 : Prop := ∀ t, m327 t = t
theorem p327 : P327 := by simp [P327, m327, PromotionModel.promoteType1]
def P328 : Prop := ∀ rule t s u, HasResult (m328 rule t s u)
theorem p328 : P328 := by simp [P328, HasResult]
def P329 : Prop := ∀ rule t s u ts, HasResult (m329 rule t s u ts)
theorem p329 : P329 := by simp [P329, HasResult]
def P331 : Prop := ∀ (_ : Unit), m331 = .bottom
theorem p331 : P331 := by simp [P331, m331]
def P332 : Prop := ∀ t, m332 t = t
theorem p332 : P332 := by simp [P332, m332]
def P333 : Prop := ∀ t, m333 t = t
theorem p333 : P333 := by simp [P333, m333, m332]
def P334 : Prop := ∀ t, m334 t = t
theorem p334 : P334 := by simp [P334, m334, m332]
def P336 : Prop := ∀ rule t s, HasResult (m336 rule t s)
theorem p336 : P336 := by simp [P336, HasResult]
def P355 : Prop := ∀ a b, m355 a b = .bottom
theorem p355 : P355 := by simp [P355, m355]
def P358 : Prop := ∀ xs, m358 xs = .bottom
theorem p358 : P358 := by simp [P358, m358]
def P359 : Prop := ∀ xs, m359 xs = .bottom
theorem p359 : P359 := by simp [P359, m359, m358]
def P360 : Prop := ∀ t xs, m360 t xs = t
theorem p360 : P360 := by simp [P360, m360]
def P361 : Prop := ∀ t xs, m361 t xs = t
theorem p361 : P361 := by simp [P361, m361, m360]
def P363 : Prop := ∀ (rule : Ty → Ty → Ty) t s a b, HasResult (m363 rule t s a b)
theorem p363 : P363 := by simp [P363, HasResult]
def P366 : Prop := ∀ (rule : Ty → Ty → Ty) t s, HasResult (m366 rule t s)
theorem p366 : P366 := by simp [P366, HasResult]

def P397 : Prop := ∀ (α : Type) (t : α → Ty) (c : Ty → α → α) r x y,
  HasResult (m397 t c r x y)
theorem p397 : P397 := by simp [P397, HasResult]
def P402 : Prop := ∀ (α : Type) (t : α → Ty) (x : α), m402 t x = t x
theorem p402 : P402 := by simp [P402, m402, PromotionModel.promoteTypeof1]
def P403 : Prop := ∀ (α : Type) (t : α → Ty) r x y, HasResult (m403 t r x y)
theorem p403 : P403 := by simp [P403, HasResult]
def P404 : Prop := ∀ (α : Type) (t : α → Ty) r x y z, HasResult (m404 t r x y z)
theorem p404 : P404 := by simp [P404, HasResult]
def P405 : Prop := ∀ (α : Type) (t : α → Ty) r x y z xs, HasResult (m405 t r x y z xs)
theorem p405 : P405 := by simp [P405, HasResult]
def P406 : Prop := ∀ (α : Type) (t : α → Ty) (c : Ty → α → α) r x y z,
  HasResult (@m406 α t c r x y z)
theorem p406 : P406 := by simp [P406, HasResult]
def P411 : Prop := ∀ (α : Type) (t : α → Ty) (c : Ty → α → α) r x y zs,
  HasResult (m411 t c r x y zs)
theorem p411 : P411 := by simp [P411, HasResult]
def P420 : Prop := ∀ (α : Type), @m420 α = []
theorem p420 : P420 := by simp [P420, m420]
def P421 : Prop := ∀ (α : Type) (x : α), m421 x = [x]
theorem p421 : P421 := by simp [P421, m421]
def P423 : Prop := ∀ (α : Type) (p : α → α → α × α) (s : (α × α) → (α × α) → Bool) x y,
  HasResult (m423 p s x y)
theorem p423 : P423 := by simp [P423, HasResult]
def P429 : Prop := ∀ (α : Type) (p : α → α → α → α × α × α)
  (s : (α × α × α) → (α × α × α) → Bool) x y z, HasResult (m429 p s x y z)
theorem p429 : P429 := by simp [P429, HasResult]
def P435 : Prop := ∀ (α : Type) (p : List α → List α) (s : List α → List α → Bool) xs,
  HasResult (m435 p s xs)
theorem p435 : P435 := by simp [P435, HasResult]
def P441 : Prop := ∀ (α : Type) (x y : α) zs, m441 x y zs = x :: y :: zs
theorem p441 : P441 := by simp [P441, m441, PromotionModel.promoteSame]
def P443 : Prop := ∀ (α : Type) (x y : α), m443 x y = .error (.argumentError "promotion failed")
theorem p443 : P443 := by simp [P443, m443]
def P445 : Prop := ∀ (α β : Type) (x : α) (y : β), m445 x y = ()
theorem p445 : P445 := by simp [P445, m445]
def P447 : Prop := ∀ (α β : Type) (r : α → String) (x : α), HasResult (@m447 α β r x)
theorem p447 : P447 := by simp [P447, HasResult]

def Forward2Prop (f : ∀ {α β : Type}, (α → α → α × α) → (α → α → β) → α → α → β) : Prop :=
  ∀ (α β : Type) (p : α → α → α × α) (op : α → α → β) x y,
    @f α β p op x y = let q := p x y
op q.1 q.2
theorem forward2_proven : Forward2Prop (@forward2) := by simp [Forward2Prop, forward2]
def P454 := Forward2Prop (@m454)
theorem p454 : P454 := forward2_proven
def P455 := Forward2Prop (@m455)
theorem p455 : P455 := forward2_proven
def P456 := Forward2Prop (@m456)
theorem p456 : P456 := forward2_proven
def P457 := Forward2Prop (@m457)
theorem p457 : P457 := forward2_proven
def P459 := Forward2Prop (@m459)
theorem p459 : P459 := forward2_proven
def P460 := Forward2Prop (@m460)
theorem p460 : P460 := forward2_proven
def P461 := Forward2Prop (@m461)
theorem p461 : P461 := forward2_proven
def P507 := Forward2Prop (@m507)
theorem p507 : P507 := forward2_proven
def P516 := Forward2Prop (@m516)
theorem p516 : P516 := forward2_proven
def P517 := Forward2Prop (@m517)
theorem p517 : P517 := forward2_proven
def P518 := Forward2Prop (@m518)
theorem p518 : P518 := forward2_proven
def P520 := Forward2Prop (@m520)
theorem p520 : P520 := forward2_proven
def P521 := Forward2Prop (@m521)
theorem p521 : P521 := forward2_proven
def P522 := Forward2Prop (@m522)
theorem p522 : P522 := forward2_proven
def P523 := Forward2Prop (@m523)
theorem p523 : P523 := forward2_proven
def P525 := Forward2Prop (@m525)
theorem p525 : P525 := forward2_proven
def P526 := Forward2Prop (@m526)
theorem p526 : P526 := forward2_proven
def P527 := Forward2Prop (@m527)
theorem p527 : P527 := forward2_proven

def P509 : Prop := ∀ (α β : Type) (p : α → α → α → α × α × α)
  (op : α → α → α → β) x y z, HasResult (m509 p op x y z)
theorem p509 : P509 := by simp [P509, HasResult]
def P510 : Prop := ∀ (α : Type) (p : α → α → α → α × α × α)
  (m : α → α → α → α) (f : α → Bool) a b c, HasResult (m510 p m f a b c)
theorem p510 : P510 := by simp [P510, HasResult]
def P529 : Prop := ∀ (ts : List Ty), HasResult (m529 ts)
theorem p529 : P529 := by simp [P529, HasResult]
def P641 : Prop := ∀ (α β : Type) (r : (α → β) → Ty → Ty)
  (f : α → β) (ts : List Ty), HasResult (m641 r f ts)
theorem p641 : P641 := by simp [P641, HasResult]

def NoOpProp (f : ∀ {α : Type}, String → Jl α) : Prop :=
  ∀ (α : Type) n, @f α n = .error (.methodError n)
theorem noOp_proven : NoOpProp (@noOp) := by simp [NoOpProp, noOp]
def P650 := NoOpProp (@m650)
theorem p650 : P650 := noOp_proven
def P651 := NoOpProp (@m651)
theorem p651 : P651 := noOp_proven
def P652 := NoOpProp (@m652)
theorem p652 : P652 := noOp_proven
def P653 := NoOpProp (@m653)
theorem p653 : P653 := noOp_proven
def P654 := NoOpProp (@m654)
theorem p654 : P654 := noOp_proven
def P655 := NoOpProp (@m655)
theorem p655 : P655 := noOp_proven
def P657 := NoOpProp (@m657)
theorem p657 : P657 := noOp_proven
def P661 := NoOpProp (@m661)
theorem p661 : P661 := noOp_proven
def P662 := NoOpProp (@m662)
theorem p662 : P662 := noOp_proven
def P663 := NoOpProp (@m663)
theorem p663 : P663 := noOp_proven
def P666 := NoOpProp (@m666)
theorem p666 : P666 := noOp_proven
def P669 := NoOpProp (@m669)
theorem p669 : P669 := noOp_proven
def P670 := NoOpProp (@m670)
theorem p670 : P670 := noOp_proven
def P680 := NoOpProp (@m680)
theorem p680 : P680 := noOp_proven

def P658 : Prop := ∀ (α : Type) (mul add : α → α → α) x y z, m658 mul add x y z = add (mul x y) z
theorem p658 : P658 := by simp [P658, m658]
def P659 : Prop := P658
theorem p659 : P659 := p658
def P665 : Prop := ∀ (α : Type) (eq : α → α → Bool) x y, m665 eq x y = eq x y
theorem p665 : P665 := by simp [P665, m665]
def P667 : Prop := ∀ (α : Type) (eq lt : α → α → Bool) x y, m667 eq lt x y = (eq x y || lt x y)
theorem p667 : P667 := by simp [P667, m667]
def P672 : Prop := ∀ (α : Type) (x : α), m672 x = x
theorem p672 : P672 := by simp [P672, m672]
def P673 := P672
theorem p673 : P673 := p672
def P674 : Prop := ∀ (α : Type) (x : α), m674 x = (x, x)
theorem p674 : P674 := by simp [P674, m674]
def P676 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y, m676 lt x y = if lt y x then x else y
theorem p676 : P676 := by simp [P676, m676]
def P677 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y, m677 lt x y = if lt y x then y else x
theorem p677 : P677 := by simp [P677, m677]
def P678 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y, m678 lt x y = if lt y x then (y, x) else (x, y)
theorem p678 : P678 := by simp [P678, m678]

end JuliaLean.NumbersCov.Rows.Promotion
