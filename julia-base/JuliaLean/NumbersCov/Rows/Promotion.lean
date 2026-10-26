import JuliaLean.NumbersCov.Rows.Common

namespace JuliaLean.NumbersCov.Rows.Promotion

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

abbrev PT := PromotionModel.PType
abbrev POps := PromotionModel.PTypeOps
abbrev Ty := PromotionModel.Ty

def m20 : PT := PromotionModel.pTypejoin0
def P20 : Prop := ∀ (_ : Unit), m20 = .bottom
theorem p20 : P20 := by simp [P20, m20, PromotionModel.pTypejoin0]
def m21 (t : PT) := PromotionModel.pTypejoin1 t
def P21 : Prop := ∀ t, m21 t = t
theorem p21 : P21 := by simp [P21, m21, PromotionModel.pTypejoin1]
def m22 (o : POps) a b c := PromotionModel.pTypejoin3 o a b c
def P22 : Prop := ∀ o a b c, HasResult (m22 o a b c)
theorem p22 : P22 := by simp [P22, HasResult]
def m23 (o : POps) a b c ts := PromotionModel.pTypejoinMany o a b c ts
def P23 : Prop := ∀ o a b c ts, HasResult (m23 o a b c ts)
theorem p23 : P23 := by simp [P23, HasResult]
def m25 (a : PT) name := PromotionModel.pHasAncestorName a name
def P25 : Prop := ∀ a n, HasResult (m25 a n)
theorem p25 : P25 := by simp [P25, HasResult]
def m37 (o : POps) a b := PromotionModel.pTypejoin o 64 a b
def P37 : Prop := ∀ o a b, HasResult (m37 o a b)
theorem p37 : P37 := by simp [P37, HasResult]
def m166 (o : POps) a b := PromotionModel.pTypesplit o a b
def P166 : Prop := ∀ o a b, HasResult (m166 o a b)
theorem p166 : P166 := by simp [P166, HasResult]
def m198 (o : POps) a b := PromotionModel.pPromoteTypejoin o a b
def P198 : Prop := ∀ o a b, m198 o a b = .union a (.union b (PromotionModel.pTypejoin o 64 a b))
theorem p198 : P198 := by simp [P198, m198, PromotionModel.pPromoteTypejoin]
def m202 (o : POps) nothing missing a := PromotionModel.pPromoteTypesubtract o nothing missing a
def P202 : Prop := ∀ o n m a, HasResult (m202 o n m a)
theorem p202 : P202 := by simp [P202, HasResult]
def m209 (o : POps) t := PromotionModel.pPromoteTypejoinUnion o 64 t
def P209 : Prop := ∀ o t, HasResult (m209 o t)
theorem p209 : P209 := by simp [P209, HasResult]
def m226 (o : POps) t := PromotionModel.pTypejoinUnionTuple o 64 t
def P226 : Prop := ∀ o t, HasResult (m226 o t)
theorem p226 : P226 := by simp [P226, HasResult]
def m256 ps := PromotionModel.pFullVaLen ps
def P256 : Prop := ∀ ps, HasResult (m256 ps)
theorem p256 : P256 := by simp [P256, HasResult]
def m270 (o : POps) ps i := PromotionModel.pTailjoin o ps i
def P270 : Prop := ∀ o ps i, HasResult (m270 o ps i)
theorem p270 : P270 := by simp [P270, HasResult]

def m326 : Ty := PromotionModel.promoteType0
def P326 : Prop := ∀ (_ : Unit), m326 = .bottom
theorem p326 : P326 := by simp [P326, m326, PromotionModel.promoteType0]
def m327 (t : Ty) := PromotionModel.promoteType1 t
def P327 : Prop := ∀ t, m327 t = t
theorem p327 : P327 := by simp [P327, m327, PromotionModel.promoteType1]
def m328 rule t s u := PromotionModel.promoteType3 rule t s u
def P328 : Prop := ∀ rule t s u, HasResult (m328 rule t s u)
theorem p328 : P328 := by simp [P328, HasResult]
def m329 rule t s u ts := PromotionModel.promoteTypeMany rule t s u ts
def P329 : Prop := ∀ rule t s u ts, HasResult (m329 rule t s u ts)
theorem p329 : P329 := by simp [P329, HasResult]
def m331 : Ty := .bottom
def P331 : Prop := ∀ (_ : Unit), m331 = .bottom
theorem p331 : P331 := by simp [P331, m331]
def m332 (t : Ty) := t
def P332 : Prop := ∀ t, m332 t = t
theorem p332 : P332 := by simp [P332, m332]
def m333 := m332
def P333 : Prop := ∀ t, m333 t = t
theorem p333 : P333 := by simp [P333, m333, m332]
def m334 := m332
def P334 : Prop := ∀ t, m334 t = t
theorem p334 : P334 := by simp [P334, m334, m332]
def m336 rule t s := PromotionModel.promoteType 64 rule t s
def P336 : Prop := ∀ rule t s, HasResult (m336 rule t s)
theorem p336 : P336 := by simp [P336, HasResult]
def m355 (_ _ : Ty) : Ty := .bottom
def P355 : Prop := ∀ a b, m355 a b = .bottom
theorem p355 : P355 := by simp [P355, m355]
def m358 (_ : List Ty) : Ty := .bottom
def P358 : Prop := ∀ xs, m358 xs = .bottom
theorem p358 : P358 := by simp [P358, m358]
def m359 := m358
def P359 : Prop := ∀ xs, m359 xs = .bottom
theorem p359 : P359 := by simp [P359, m359, m358]
def m360 (t : Ty) (_ : List Ty) := t
def P360 : Prop := ∀ t xs, m360 t xs = t
theorem p360 : P360 := by simp [P360, m360]
def m361 := m360
def P361 : Prop := ∀ t xs, m361 t xs = t
theorem p361 : P361 := by simp [P361, m361, m360]
def m363 (rule : Ty → Ty → Ty) (_t _s a b : Ty) := PromotionModel.promoteType 64 rule a b
def P363 : Prop := ∀ (rule : Ty → Ty → Ty) t s a b, HasResult (m363 rule t s a b)
theorem p363 : P363 := by simp [P363, HasResult]
def m366 (_rule : Ty → Ty → Ty) (t s : Ty) := PromotionModel.typejoin 64 t s
def P366 : Prop := ∀ (rule : Ty → Ty → Ty) t s, HasResult (m366 rule t s)
theorem p366 : P366 := by simp [P366, HasResult]

def m397 (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (x y : α) := PromotionModel.promote2 typeOf convert rule x y
def P397 : Prop := ∀ (α : Type) (t : α → Ty) (c : Ty → α → α) r x y,
  HasResult (m397 t c r x y)
theorem p397 : P397 := by simp [P397, HasResult]
def m402 (typeOf : α → Ty) (x : α) := PromotionModel.promoteTypeof1 typeOf x
def P402 : Prop := ∀ (α : Type) (t : α → Ty) (x : α), m402 t x = t x
theorem p402 : P402 := by simp [P402, m402, PromotionModel.promoteTypeof1]
def m403 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y : α) :=
  PromotionModel.promoteTypeof2 typeOf rule x y
def P403 : Prop := ∀ (α : Type) (t : α → Ty) r x y, HasResult (m403 t r x y)
theorem p403 : P403 := by simp [P403, HasResult]
def m404 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y z : α) :=
  PromotionModel.promoteTypeof3 typeOf rule x y z
def P404 : Prop := ∀ (α : Type) (t : α → Ty) r x y z, HasResult (m404 t r x y z)
theorem p404 : P404 := by simp [P404, HasResult]
def m405 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y z : α) (xs : List α) :=
  PromotionModel.promoteTypeofMany typeOf rule x y z xs
def P405 : Prop := ∀ (α : Type) (t : α → Ty) r x y z xs, HasResult (m405 t r x y z xs)
theorem p405 : P405 := by simp [P405, HasResult]
def m406 := @PromotionModel.promote3
def P406 : Prop := ∀ (α : Type) (t : α → Ty) (c : Ty → α → α) r x y z,
  HasResult (@m406 α t c r x y z)
theorem p406 : P406 := by simp [P406, HasResult]
def m411 (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (x y : α) (zs : List α) := PromotionModel.promoteMany typeOf convert rule (x :: y :: zs)
def P411 : Prop := ∀ (α : Type) (t : α → Ty) (c : Ty → α → α) r x y zs,
  HasResult (m411 t c r x y zs)
theorem p411 : P411 := by simp [P411, HasResult]
def m420 : List α := []
def P420 : Prop := ∀ (α : Type), @m420 α = []
theorem p420 : P420 := by simp [P420, m420]
def m421 (x : α) := [x]
def P421 : Prop := ∀ (α : Type) (x : α), m421 x = [x]
theorem p421 : P421 := by simp [P421, m421]
def m423 (promote : α → α → α × α) (same : (α × α) → (α × α) → Bool)
    (x y : α) : Jl (α × α) :=
  let p := promote x y
  if same (x, y) p then .error (.argumentError "promotion failed") else .ok p
def P423 : Prop := ∀ (α : Type) (p : α → α → α × α) (s : (α × α) → (α × α) → Bool) x y,
  HasResult (m423 p s x y)
theorem p423 : P423 := by simp [P423, HasResult]
def m429 (promote : α → α → α → α × α × α)
    (same : (α × α × α) → (α × α × α) → Bool)
    (x y z : α) : Jl (α × α × α) :=
  let p := promote x y z
  if same (x, y, z) p then .error (.argumentError "promotion failed") else .ok p
def P429 : Prop := ∀ (α : Type) (p : α → α → α → α × α × α)
  (s : (α × α × α) → (α × α × α) → Bool) x y z, HasResult (m429 p s x y z)
theorem p429 : P429 := by simp [P429, HasResult]
def m435 (promote : List α → List α) (same : List α → List α → Bool)
    (xs : List α) : Jl (List α) :=
  let p := promote xs
  if same xs p then .error (.argumentError "promotion failed") else .ok p
def P435 : Prop := ∀ (α : Type) (p : List α → List α) (s : List α → List α → Bool) xs,
  HasResult (m435 p s xs)
theorem p435 : P435 := by simp [P435, HasResult]
def m441 (x y : α) (zs : List α) := PromotionModel.promoteSame x y zs
def P441 : Prop := ∀ (α : Type) (x y : α) zs, m441 x y zs = x :: y :: zs
theorem p441 : P441 := by simp [P441, m441, PromotionModel.promoteSame]
def m443 (_x _y : α) : Jl Unit := .error (.argumentError "promotion failed")
def P443 : Prop := ∀ (α : Type) (x y : α), m443 x y = .error (.argumentError "promotion failed")
theorem p443 : P443 := by simp [P443, m443]
def m445 (_x : α) (_y : β) : Unit := ()
def P445 : Prop := ∀ (α β : Type) (x : α) (y : β), m445 x y = ()
theorem p445 : P445 := by simp [P445, m445]
def m447 (renderTypes : α → String) (x : α) : Jl β := .error (.argumentError (renderTypes x))
def P447 : Prop := ∀ (α β : Type) (r : α → String) (x : α), HasResult (@m447 α β r x)
theorem p447 : P447 := by simp [P447, HasResult]

def forward2 (promote : α → α → α × α) (op : α → α → β) x y :=
  let p := promote x y
  op p.1 p.2
def m454 := @forward2
def m455 := @forward2
def m456 := @forward2
def m457 := @forward2
def m459 := @forward2
def m460 := @forward2
def m461 := @forward2
def m507 := @forward2
def m516 := @forward2
def m517 := @forward2
def m518 := @forward2
def m520 := @forward2
def m521 := @forward2
def m522 := @forward2
def m523 := @forward2
def m525 := @forward2
def m526 := @forward2
def m527 := @forward2

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

def m509 (promote : α → α → α → α × α × α) (op : α → α → α → β)
    (x y z : α) := PromotionModel.promotedTernary promote op x y z
def P509 : Prop := ∀ (α β : Type) (p : α → α → α → α × α × α)
  (op : α → α → α → β) x y z, HasResult (m509 p op x y z)
theorem p509 : P509 := by simp [P509, HasResult]
def m510 (promote : α → α → α → α × α × α) (muladd : α → α → α → α)
    (isFalse : α → Bool) (a b c : α) :=
  PromotionModel.promotedMuladd promote muladd isFalse a b c
def P510 : Prop := ∀ (α : Type) (p : α → α → α → α × α × α)
  (m : α → α → α → α) (f : α → Bool) a b c, HasResult (m510 p m f a b c)
theorem p510 : P510 := by simp [P510, HasResult]
def m529 (ts : List Ty) := PromotionModel.tupleOrBottom ts
def P529 : Prop := ∀ (ts : List Ty), HasResult (m529 ts)
theorem p529 : P529 := by simp [P529, HasResult]
def m641 (returnType : (α → β) → Ty → Ty) (f : α → β) (ts : List Ty) :=
  PromotionModel.promoteOp returnType f ts
def P641 : Prop := ∀ (α β : Type) (r : (α → β) → Ty → Ty)
  (f : α → β) (ts : List Ty), HasResult (m641 r f ts)
theorem p641 : P641 := by simp [P641, HasResult]

def noOp (name : String) : Jl α := .error (.methodError name)
def m650 := @noOp
def m651 := @noOp
def m652 := @noOp
def m653 := @noOp
def m654 := @noOp
def m655 := @noOp
def m657 := @noOp
def m661 := @noOp
def m662 := @noOp
def m663 := @noOp
def m666 := @noOp
def m669 := @noOp
def m670 := @noOp
def m680 := @noOp
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

def m658 (mul add : α → α → α) x y z := add (mul x y) z
def P658 : Prop := ∀ (α : Type) (mul add : α → α → α) x y z, m658 mul add x y z = add (mul x y) z
theorem p658 : P658 := by simp [P658, m658]
def m659 := @m658
def P659 : Prop := P658
theorem p659 : P659 := p658
def m665 (identical : α → α → Bool) x y := identical x y
def P665 : Prop := ∀ (α : Type) (eq : α → α → Bool) x y, m665 eq x y = eq x y
theorem p665 : P665 := by simp [P665, m665]
def m667 (eq lt : α → α → Bool) x y := eq x y || lt x y
def P667 : Prop := ∀ (α : Type) (eq lt : α → α → Bool) x y, m667 eq lt x y = (eq x y || lt x y)
theorem p667 : P667 := by simp [P667, m667]
def m672 (x : α) := x
def P672 : Prop := ∀ (α : Type) (x : α), m672 x = x
theorem p672 : P672 := by simp [P672, m672]
def m673 := @m672
def P673 := P672
theorem p673 : P673 := p672
def m674 (x : α) := (x, x)
def P674 : Prop := ∀ (α : Type) (x : α), m674 x = (x, x)
theorem p674 : P674 := by simp [P674, m674]
def m676 (lt : α → α → Bool) x y := if lt y x then x else y
def P676 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y, m676 lt x y = if lt y x then x else y
theorem p676 : P676 := by simp [P676, m676]
def m677 (lt : α → α → Bool) x y := if lt y x then y else x
def P677 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y, m677 lt x y = if lt y x then y else x
theorem p677 : P677 := by simp [P677, m677]
def m678 (lt : α → α → Bool) x y := if lt y x then (y, x) else (x, y)
def P678 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y, m678 lt x y = if lt y x then (y, x) else (x, y)
theorem p678 : P678 := by simp [P678, m678]

end JuliaLean.NumbersCov.Rows.Promotion
