import JuliaLean.base.operators
import JuliaLean.Proofs.base.number.numberscov_common

namespace JuliaLean.NumbersCov

open JuliaLean

/-! ## `base/operators.jl` -/

def OperatorTypeReflection : Prop :=
  (∀ (α β : Type) (compute : α → Unit) (super : α → β) (t : α),
    OperatorModel.supertypeData compute super t = super t) ∧
  (∀ (α β γ : Type) (isSuper : γ → Bool) (supertype : α → β)
      (getfield : α → γ → β) (t : α) (s : γ),
    OperatorModel.getpropertyData isSuper supertype getfield t s =
      if isSuper s then supertype t else getfield t s) ∧
  (∀ (α β γ : Type) (wrap : α → β → γ) (supertype : β → β) (v : α) (body : β),
    OperatorModel.supertypeUnionAll wrap supertype v body = wrap v (supertype body)) ∧
  (∀ (α : Type) (anyType : α), OperatorModel.supertypeTypeEq anyType = anyType) ∧
  (∀ (α β : Type) (typeOf : α → β) (p : α),
    OperatorModel.supertypeTypeEgal typeOf p = typeOf p)

theorem operatorTypeReflection_proven : OperatorTypeReflection := by
  simp [OperatorTypeReflection, OperatorModel.supertypeData, OperatorModel.getpropertyData,
    OperatorModel.supertypeUnionAll, OperatorModel.supertypeTypeEq,
    OperatorModel.supertypeTypeEgal]

def OperatorComparisonMethods : Prop :=
  (∀ (α : Type) (o : OperatorModel.FloatOrder α) (x y : α),
    OperatorModel.isequalFloat o x y =
      ((o.isnan x && o.isnan y) ||
       ((o.signbit x == o.signbit y) && o.eq x y)) ∧
    OperatorModel.islessFloat o x y =
      ((!o.isnan x && (o.isnan y || (o.signbit x && !o.signbit y))) || o.lt x y)) ∧
  (∀ (α : Type) (lt eq : α → α → Bool) (x y : α),
    OperatorModel.isequal eq x y = eq x y ∧
    OperatorModel.ne eq x y = !eq x y ∧
    OperatorModel.ltFallback lt x y = lt x y ∧
    OperatorModel.gtFallback lt x y = lt y x ∧
    OperatorModel.leFallback lt eq x y = (lt x y || eq x y) ∧
    OperatorModel.geFallback (OperatorModel.leFallback lt eq) x y =
      (lt y x || eq y x) ∧
    OperatorModel.cmp lt x y = (if lt x y then -1 else if lt y x then 1 else 0) ∧
    OperatorModel.min lt x y = (if lt y x then y else x) ∧
    OperatorModel.max lt x y = (if lt y x then x else y) ∧
    OperatorModel.minmax lt x y = (if lt y x then (y, x) else (x, y))) ∧
  (∀ (α β γ : Type) (eq : α → α → β) (not : β → γ) x y,
    OperatorModel.neGeneric eq not x y = not (eq x y)) ∧
  (∀ (α β γ δ : Type) (lt : α → α → β) (eq : α → α → γ)
      (bitOr : β → γ → δ) x y,
    OperatorModel.leGeneric lt eq bitOr x y = bitOr (lt x y) (eq x y)) ∧
  (∀ (α β : Type) (le : α → α → β) x y,
    OperatorModel.geGeneric le x y = le y x) ∧
  (∀ (α : Type) (o : OperatorModel.FloatOrder α) (x y : α),
    OperatorModel.signequal o x y = (o.signbit x == o.signbit y) ∧
    OperatorModel.signless o x y = (o.signbit x && !o.signbit y)) ∧
  (∀ (α : Type) (lt eq : α → α → Bool) (a b : α × α),
    OperatorModel.pairIsless lt eq a b =
      (lt a.1 b.1 || (eq a.1 b.1 && lt a.2 b.2))) ∧
  (∀ (α β : Type) (isnan : α → Bool) (x : α) (a : α) (b : β),
    OperatorModel.isunordered x = false ∧
    OperatorModel.isunorderedFloat isnan x = isnan x ∧
    OperatorModel.typeVarTypeEqual a b = false) ∧
  (∀ (α : Type) (typesEqual : α → α → Bool) (a b : α),
    OperatorModel.typeEqual typesEqual a b = typesEqual a b)

theorem operatorComparisonMethods_proven : OperatorComparisonMethods := by
  simp [OperatorComparisonMethods, OperatorModel.isequalFloat, OperatorModel.islessFloat,
    OperatorModel.signequal, OperatorModel.signless, OperatorModel.isequal, OperatorModel.ne,
    OperatorModel.neGeneric,
    OperatorModel.ltFallback, OperatorModel.gtFallback, OperatorModel.leFallback,
    OperatorModel.leGeneric, OperatorModel.geFallback, OperatorModel.geGeneric,
    OperatorModel.cmp, OperatorModel.min, OperatorModel.max,
    OperatorModel.minmax, OperatorModel.pairIsless, OperatorModel.isunordered,
    OperatorModel.isunorderedFloat, OperatorModel.typeVarTypeEqual,
    OperatorModel.typeEqual]

def OperatorFolds : Prop :=
  ∀ (α : Type) (op : α → α → α) (a b c : α) (xs : List α),
    OperatorModel.identity a = a ∧
    OperatorModel.afoldl op a xs = xs.foldl op a ∧
    OperatorModel.nary op a b c xs = xs.foldl op (op (op a b) c)

theorem operatorFolds_proven : OperatorFolds := by
  simp [OperatorFolds, OperatorModel.identity, OperatorModel.afoldl, OperatorModel.nary]

def OperatorShiftDispatch : Prop :=
  (∀ (α : Type) (shift : α → Int → α) (zero negOne : α) (nonnegative : α → Bool)
      (x : α) (c : Int),
    OperatorModel.shiftLeftInteger shift zero negOne nonnegative x c =
      if OperatorModel.intMin ≤ c && c ≤ OperatorModel.intMax then shift x c
      else if nonnegative x || 0 ≤ c then shift zero 0 else negOne) ∧
  (∀ (α : Type) (shift : α → Int → α) (zero : α) (x : α) (c : Int),
    OperatorModel.shiftUnsignedRightInteger shift zero x c =
      if OperatorModel.intMin ≤ c && c ≤ OperatorModel.intMax then shift x c else shift zero 0) ∧
  (∀ (α : Type) (forward backward : α → Nat → α) (x : α) (c : Int),
    OperatorModel.shiftSignedCount forward backward x c =
      if 0 ≤ c then forward x c.toNat else backward x (-c).toNat) ∧
  (∀ (α : Type) (shift : α → Int → α) (zero negOne : α)
      (nonnegative : α → Bool) (x : α) (c : Int),
    OperatorModel.shiftRightInteger shift zero negOne nonnegative x c =
      (if OperatorModel.intMin ≤ c && c ≤ OperatorModel.intMax then shift x c
       else if nonnegative x || c < 0 then shift zero 0 else negOne)) ∧
  (∀ (α : Type) (shift : α → Int → α) (zero negOne : α)
      (nonnegative : α → Bool) (x : α) (c : Int) (isUInt : Bool),
    OperatorModel.shiftRightGenericCount shift zero negOne nonnegative x c isUInt =
      if isUInt then .error (.methodError ">>")
      else .ok (OperatorModel.shiftRightInteger shift zero negOne nonnegative x c)) ∧
  (∀ (α : Type) (fn : α → Nat → α) (zero x : α) (c : Nat) (isUInt : Bool),
    OperatorModel.shiftUnsignedCount fn zero x c isUInt =
      (if isUInt then .error (.methodError "shift")
       else if c ≤ 2^64 - 1 then .ok (fn x c) else .ok (fn zero 0)))

theorem operatorShiftDispatch_proven : OperatorShiftDispatch := by
  simp [OperatorShiftDispatch, OperatorModel.shiftLeftInteger,
    OperatorModel.shiftUnsignedRightInteger, OperatorModel.shiftSignedCount,
    OperatorModel.shiftRightInteger, OperatorModel.shiftRightGenericCount,
    OperatorModel.shiftUnsignedCount]

def OperatorModularAndWiden : Prop :=
  (∀ (α : Type) (mod : α → α → α) (iszero : α → Bool) (x y : α),
    OperatorModel.mod1 mod iszero x y =
      let m := mod x y; if iszero m then y else m) ∧
  (∀ (α : Type) (adj : α → α) (div : α → α → α) (x y : α),
    OperatorModel.leftDiv adj div x y = adj (div (adj y) (adj x))) ∧
  (∀ (α β γ : Type) (cld : α → α → β) (mod1 : α → α → γ) (x y : α),
    OperatorModel.cldmod1 cld mod1 x y = (cld x y, mod1 x y)) ∧
  (∀ (α β γ : Type) (fld1 : α → α → β) (mod1 : α → α → γ) (x y : α),
    OperatorModel.fldmod1 fld1 mod1 x y = (fld1 x y, mod1 x y)) ∧
  (∀ (α β γ : Type) (widenType : α → β) (convert : β → α → γ)
      (typeOf : α → α) (x : α),
    OperatorModel.widenValue widenType convert typeOf x =
      convert (widenType (typeOf x)) x) ∧
  (∀ (α : Type) (name : String),
    OperatorModel.widenTypeError (α := α) name = .error (.methodError name))

theorem operatorModularAndWiden_proven : OperatorModularAndWiden := by
  simp [OperatorModularAndWiden, OperatorModel.mod1, OperatorModel.leftDiv,
    OperatorModel.cldmod1, OperatorModel.fldmod1, OperatorModel.widenValue,
    OperatorModel.widenTypeError]

def OperatorFunctionAdapters : Prop :=
  (∀ (α β : Type) (x : α) (f : α → β), OperatorModel.pipe x f = f x) ∧
  (∀ (α β : Type) (typeOf : α → β) (x : α),
    OperatorModel.stableTypeof typeOf x = typeOf x) ∧
  (∀ (α β : Type) (hasFree : α → Bool) (typeTag dataType : β) (t : α),
    OperatorModel.stableTypeofType hasFree typeTag dataType t =
      if !hasFree t then typeTag else dataType) ∧
  (∀ (α β : Type) (r : OperatorModel.Returns α) (args : List β),
    r.call args = r.value) ∧
  (∀ (α : Type) (value : α),
    OperatorModel.returnsTyped value = ⟨value⟩ ∧
    OperatorModel.returnsStable value = ⟨value⟩) ∧
  (∀ (α : Type) (fs : List (α → α)) (x : α),
    OperatorModel.callComposed fs x = fs.foldr (fun f x => f x) x) ∧
  (∀ (α : Type) (c : OperatorModel.Composed α) (x : α),
    c.call x = OperatorModel.callComposed c.functions x ∧
    OperatorModel.unwrapComposed c = c.functions) ∧
  (∀ (α : Type) (f g : α → α) (hs : List (α → α)),
    OperatorModel.compose1 f = ⟨[f]⟩ ∧
    OperatorModel.compose2 f g = ⟨[f, g]⟩ ∧
    OperatorModel.composeMany f g hs = ⟨f :: g :: hs⟩ ∧
    OperatorModel.unwrapSingle f = [f]) ∧
  (∀ (α β : Type) (f : List α → β) (args : List α),
    OperatorModel.constructorCall f args = f args ∧
    OperatorModel.maybeConstructorType f args = f args ∧
    OperatorModel.maybeConstructorValue f args = f args) ∧
  (∀ (α : Type) (render showPart : α → String) (nested : Bool) (outer inner : α),
    OperatorModel.showComposed render showPart nested outer inner =
      (if nested then render outer else showPart outer) ++ " ∘ " ++ showPart inner) ∧
  (∀ (α : Type) (render : α → String) (isOperator isNested : Bool) x,
    OperatorModel.showComposedPart render isOperator isNested x =
      if isOperator || isNested then "(" ++ render x ++ ")" else render x) ∧
  (∀ (α : Type) (f : α → Bool) (x : α),
    OperatorModel.negatePredicate f x = !f x ∧
    OperatorModel.doubleNegationInner f x = f x) ∧
  (∀ (α β : Type) (n : Option Int) (f : List α → β) (x : α),
    ∃ r, OperatorModel.Fix.make n f x = r) ∧
  (∀ (α β : Type) (fix : OperatorModel.Fix α β) (args : List α),
    ∃ r, fix.call args = r) ∧
  (∀ (α β : Type) (f : α → α → β) (fixed arg : α),
    OperatorModel.fix1Call f fixed arg = f fixed arg ∧
    OperatorModel.fix2Call f fixed arg = f arg fixed ∧
    OperatorModel.fix2 f fixed arg = f arg fixed) ∧
  (∀ (α β : Type) (renderF : (List α → β) → String) (render : α → String)
      (fix : OperatorModel.Fix α β), ∃ s, OperatorModel.showFix renderF render fix = s) ∧
  (∀ (α β : Type) (f : List α → β) (args : List α),
    (OperatorModel.splat f).call args = f args ∧
    OperatorModel.unsplat f args = f args ∧
    OperatorModel.unsplatSplat (OperatorModel.splat f) args = f args ∧
    OperatorModel.splatUnsplat f args = f args) ∧
  (∀ (α β : Type) (render : (List α → β) → String) (s : OperatorModel.Splat α β),
    OperatorModel.showSplat render s = "splat(" ++ render s.f ++ ")") ∧
  (∀ (α β : Type) (f : α → β) (x : α), OperatorModel.tap f x = x) ∧
  (∀ (α : Type) (render : α → String) (inner : α),
    OperatorModel.showNegatedComposed render inner = "!" ++ render inner)

theorem operatorFunctionAdapters_proven : OperatorFunctionAdapters := by
  simp [OperatorFunctionAdapters, OperatorModel.pipe, OperatorModel.stableTypeof,
    OperatorModel.stableTypeofType, OperatorModel.Returns.call,
    OperatorModel.returnsTyped, OperatorModel.returnsStable,
    OperatorModel.callComposed, OperatorModel.Composed.call, OperatorModel.unwrapComposed,
    OperatorModel.compose1, OperatorModel.compose2, OperatorModel.composeMany,
    OperatorModel.unwrapSingle, OperatorModel.constructorCall, OperatorModel.maybeConstructorType,
    OperatorModel.maybeConstructorValue, OperatorModel.showComposed,
    OperatorModel.showComposedPart,
    OperatorModel.negatePredicate, OperatorModel.doubleNegationInner,
    OperatorModel.fix1Call, OperatorModel.fix2Call, OperatorModel.fix2,
    OperatorModel.splat, OperatorModel.Splat.call, OperatorModel.unsplat,
    OperatorModel.unsplatSplat, OperatorModel.splatUnsplat, OperatorModel.showSplat,
    OperatorModel.tap, OperatorModel.showNegatedComposed]

def OperatorMembership : Prop :=
  (∀ (α : Type) (eq : α → α → OperatorModel.Truth) (x : α),
    OperatorModel.mem eq x [] = .false) ∧
  (∀ (α : Type) (eq : α → α → OperatorModel.Truth) (x y : α) (ys : List α),
    OperatorModel.mem eq x (y :: ys) =
      OperatorModel.Truth.or (eq y x) (OperatorModel.mem eq x ys)) ∧
  (∀ (α β : Type) (m : α → β → OperatorModel.Truth) (x : α) (ys : β),
    OperatorModel.notMem m x ys = (m x ys).not ∧
    OperatorModel.contains m ys x = m x ys ∧
    OperatorModel.notContains m ys x = (m x ys).not ∧
    OperatorModel.fixSecond m ys x = m x ys)

theorem operatorMembership_proven : OperatorMembership := by
  simp [OperatorMembership, OperatorModel.mem, OperatorModel.notMem,
    OperatorModel.contains, OperatorModel.notContains, OperatorModel.fixSecond]


end JuliaLean.NumbersCov

namespace JuliaLean.NumbersCov.Rows.Operators

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

def P86 : Prop := ∀ (α β : Type) (compute : α → Unit) (super : α → β) t,
  m86 compute super t = super t
theorem p86 : P86 := by simp [P86, m86]

def P95 : Prop := ∀ (α β σ : Type) (isSuper : σ → Bool) (super : α → β)
  (field : α → σ → β) t s, m95 isSuper super field t s =
    if isSuper s then super t else field t s
theorem p95 : P95 := by simp [P95, m95]

def P102 : Prop := ∀ (α β γ : Type) (wrap : α → β → γ) (super : β → β) v body,
  m102 wrap super v body = wrap v (super body)
theorem p102 : P102 := by simp [P102, m102]
def P104 : Prop := ∀ (α : Type) (x : α), m104 x = x
theorem p104 : P104 := by simp [P104, m104]
def P105 : Prop := ∀ (α β : Type) (f : α → β) x, m105 f x = f x
theorem p105 : P105 := by simp [P105, m105]

def P196 : Prop := ∀ (α β : Type) (eq : α → β → Bool) x y, m196 eq x y = eq x y
theorem p196 : P196 := by simp [P196, m196]
def P198 : Prop := ∀ (α : Type) (f : α → Bool) x y, m198 f x y = (f x == f y)
theorem p198 : P198 := by simp [P198, m198]
def P199 : Prop := ∀ (α : Type) (f : α → Bool) x y, m199 f x y = (f x && !f y)
theorem p199 : P199 := by simp [P199, m199]
def P201 : Prop := ∀ (α : Type) (nan sign : α → Bool) (eq : α → α → Bool) x y,
  m201 nan sign eq x y = ((nan x && nan y) || ((sign x == sign y) && eq x y))
theorem p201 : P201 := by simp [P201, m201]
def P202 : Prop := ∀ (α β : Type) (na : α → Bool) (nb : β → Bool)
  (sa : α → Bool) (sb : β → Bool) (eq : α → β → Bool) x y,
  m202 na nb sa sb eq x y = ((na x && nb y) || ((sa x == sb y) && eq x y))
theorem p202 : P202 := by simp [P202, m202]
def P240 : Prop := ∀ (α : Type) (nan sign : α → Bool) (lt : α → α → Bool) x y,
  m240 nan sign lt x y = ((!nan x && (nan y || (sign x && !sign y))) || lt x y)
theorem p240 : P240 := by simp [P240, m240]
def P248 : Prop := ∀ (α : Type) (lt eq : α → α → Bool) a b,
  m248 lt eq a b = (lt a.1 b.1 || (eq a.1 b.1 && lt a.2 b.2))
theorem p248 : P248 := by simp [P248, m248]
def P309 : Prop := ∀ (α : Type) (x : α), m309 x = false
theorem p309 : P309 := by simp [P309, m309]
def P310 : Prop := ∀ (α : Type) (f : α → Bool) x, m310 f x = f x
theorem p310 : P310 := by simp [P310, m310]
def P313 : Prop := ∀ (α : Type) (f : α → α → Bool) x y, m313 f x y = f x y
theorem p313 : P313 := by simp [P313, m313]
def P314 : Prop := ∀ (α β : Type) (x : α) (y : β), m314 x y = false
theorem p314 : P314 := by simp [P314, m314]
def P315 : Prop := ∀ (α β : Type) (x : α) (y : β), @m315 α β x y = false
theorem p315 : P315 := by simp [P315, m315, m314]
def P338 : Prop := ∀ (α β γ δ : Type) (eq : α → β → γ) (n : γ → δ) x y,
  m338 eq n x y = n (eq x y)
theorem p338 : P338 := by simp [P338, m338]
def P417 : Prop := ∀ (α β : Type) (f : α → β → Bool) x y, m417 f x y = f x y
theorem p417 : P417 := by simp [P417, m417]
def P443 : Prop := ∀ (α β : Type) (f : β → α → Bool) x y, m443 f x y = f y x
theorem p443 : P443 := by simp [P443, m443]
def P467 : Prop := ∀ (α β γ δ ε : Type) (lt : α → β → γ) (eq : α → β → δ)
  (or : γ → δ → ε) x y, m467 lt eq or x y = or (lt x y) (eq x y)
theorem p467 : P467 := by simp [P467, m467]
def P499 : Prop := ∀ (α β γ : Type) (le : β → α → γ) x y, m499 le x y = le y x
theorem p499 : P499 := by simp [P499, m499]
def P526 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y,
  m526 lt x y = if lt x y then -1 else if lt y x then 1 else 0
theorem p526 : P526 := by simp [P526, m526]
def P534 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y,
  m534 lt x y = if lt x y then -1 else if lt y x then 1 else 0
theorem p534 : P534 := by simp [P534, m534]
def P588 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y,
  m588 lt x y = if lt y x then (y, x) else (x, y)
theorem p588 : P588 := by simp [P588, m588]

def P605 : Prop := ∀ (α : Type) (x : α), m605 x = x
theorem p605 : P605 := by simp [P605, m605]
def P607 : Prop := ∀ (α : Type) (x : α), @m607 α x = x
theorem p607 : P607 := by simp [P607, m607, m605]
def P608 : Prop := ∀ (α : Type) (x : α), @m608 α x = x
theorem p608 : P608 := by simp [P608, m608, m605]
def P609 : Prop := ∀ (α : Type) (x : α), @m609 α x = x
theorem p609 : P609 := by simp [P609, m609, m605]
def P610 : Prop := ∀ (α : Type) (x : α), @m610 α x = x
theorem p610 : P610 := by simp [P610, m610, m605]
def P611 : Prop := ∀ (α : Type) (x : α), @m611 α x = x
theorem p611 : P611 := by simp [P611, m611, m605]
def P622 : Prop := ∀ (α : Type) (op : α → α → α) a, m622 op a = a
theorem p622 : P622 := by simp [P622, m622]
def P623 : Prop := ∀ (α : Type) (op : α → α → α) a bs, m623 op a bs = bs.foldl op a
theorem p623 : P623 := by simp [P623, m623]
def P671 : Prop := ∀ (α : Type) (op : α → α → α) a b c xs,
  m671 op a b c xs = xs.foldl op (op (op a b) c)
theorem p671 : P671 := by simp [P671, m671]

def P709 : Prop := ∀ (α : Type) (adj : α → α) (div : α → α → α) x y,
  m709 adj div x y = adj (div (adj y) (adj x))
theorem p709 : P709 := by simp [P709, m709]

def P735 : Prop := ∀ (α : Type) (sh : α → Int → α) (z n : α) (p : α → Bool) x c,
  HasResult (m735 sh z n p x c)
theorem p735 : P735 := by simp [P735, HasResult]
def P741 : Prop := ∀ (α : Type) (sh : α → Nat → α) z x c u, HasResult (m741 sh z x c u)
theorem p741 : P741 := by simp [P741, HasResult]
def P748 : Prop := ∀ (α : Type) (l r : α → Nat → α) x c, HasResult (m748 l r x c)
theorem p748 : P748 := by simp [P748, HasResult]
def P780 : Prop := ∀ (α : Type) (sh : α → Int → α) z n (p : α → Bool) x c u,
  HasResult (m780 sh z n p x c u)
theorem p780 : P780 := by simp [P780, HasResult]
def P789 : Prop := ∀ (α : Type) (r l : α → Nat → α) x c, HasResult (m789 r l x c)
theorem p789 : P789 := by simp [P789, HasResult]
def P818 : Prop := ∀ (α : Type) (sh : α → Int → α) z x c, HasResult (m818 sh z x c)
theorem p818 : P818 := by simp [P818, HasResult]
def P822 : Prop := ∀ (α : Type) (sh : α → Nat → α) z x c u, HasResult (m822 sh z x c u)
theorem p822 : P822 := by simp [P822, HasResult]
def P829 : Prop := ∀ (α : Type) (r l : α → Nat → α) x c, HasResult (m829 r l x c)
theorem p829 : P829 := by simp [P829, HasResult]

def P914 : Prop := ∀ (α : Type) (mod : α → α → α) (z : α → Bool) x y,
  m914 mod z x y = let m := mod x y; if z m then y else m
theorem p914 : P914 := by simp [P914, m914, OperatorModel.mod1]
def P943 : Prop := ∀ (α β γ : Type) (c : α → α → β) (m : α → α → γ) x y,
  m943 c m x y = (c x y, m x y)
theorem p943 : P943 := by simp [P943, m943]
def P952 : Prop := ∀ (α β γ : Type) (f : α → α → β) (m : α → α → γ) x y,
  m952 f m x y = (f x y, m x y)
theorem p952 : P952 := by simp [P952, m952]
def P975 : Prop := ∀ (α β γ δ : Type) (t : α → β) (w : β → γ) (c : γ → α → δ) x,
  m975 t w c x = c (w (t x)) x
theorem p975 : P975 := by simp [P975, m975]
def P976 : Prop := ∀ (α : Type) n, @m976 α n = .error (.methodError n)
theorem p976 : P976 := by simp [P976, m976]
def P977 : Prop := ∀ (α : Type) n, @m977 α n = .error (.methodError n)
theorem p977 : P977 := by simp [P977, m977, m976]

def P1001 : Prop := ∀ (α β : Type) (x : α) (f : α → β), m1001 x f = f x
theorem p1001 : P1001 := by simp [P1001, m1001]
def P1003 : Prop := ∀ (α β : Type) (f : α → β) x, m1003 f x = f x
theorem p1003 : P1003 := by simp [P1003, m1003]
def P1004 : Prop := ∀ (α β : Type) (h : α → Bool) (t d : β) x,
  m1004 h t d x = if !h x then t else d
theorem p1004 : P1004 := by simp [P1004, m1004]

def P1031 : Prop := ∀ (α : Type) (v : α), m1031 v = ReturnsF.mk v
theorem p1031 : P1031 := by simp [P1031, m1031]
def P1032 : Prop := ∀ (α : Type) (v : α), @m1032 α v = ReturnsF.mk v
theorem p1032 : P1032 := by simp [P1032, m1032, m1031]
def P1035 : Prop := ∀ (α β γ : Type) (r : ReturnsF α) (a : β) (k : γ), m1035 r a k = r.value
theorem p1035 : P1035 := by simp [P1035, m1035]

def P1121 : Prop := ∀ (O I : Type) (o : O) (i : I), m1121 o i = ComposedF.mk o i
theorem p1121 : P1121 := by simp [P1121, m1121]
def P1122 : Prop := ∀ (O I : Type) (o : O) (i : I), @m1122 O I o i = ComposedF.mk o i
theorem p1122 : P1122 := by simp [P1122, m1122, m1121]
def P1125 : Prop := ∀ (O I F X K Y : Type) (u : ComposedF O I → F)
  (call : F → X → K → Y) (c : ComposedF O I) (a : X) (k : K),
  m1125 u call c a k = call (u c) a k
theorem p1125 : P1125 := by simp [P1125, m1125]
def P1126 : Prop := ∀ (O I F : Type) (uo : O → List F) (ui : I → List F) (c : ComposedF O I),
  m1126 uo ui c = uo c.outer ++ ui c.inner
theorem p1126 : P1126 := by simp [P1126, m1126]
def P1127 : Prop := ∀ (α β : Type) (f : α → β) (x : α), m1127 f x = [f x]
theorem p1127 : P1127 := by simp [P1127, m1127]
def P1128 : Prop := ∀ (F A B Fs X K : Type) (h : F → A → B) (t : Fs → X → K → A)
  (fh : F) (ft : Fs) (x : X) (k : K), m1128 h t fh ft x k = h fh (t ft x k)
theorem p1128 : P1128 := by simp [P1128, m1128]
def P1129 : Prop := ∀ (F X K Y : Type) (c : F → X → K → Y)
  (f : F) (x : X) (k : K), m1129 c f x k = c f x k
theorem p1129 : P1129 := by simp [P1129, m1129]
def P1132 : Prop := ∀ (F A K Y : Type) (c : F → A → K → Y)
  (f : F) (a : A) (k : K), m1132 c f a k = c f a k
theorem p1132 : P1132 := by simp [P1132, m1132]
def P1133 : Prop := ∀ (F C : Type) (w : F → C) (f : F), m1133 w f = w f
theorem p1133 : P1133 := by simp [P1133, m1133]
def P1134 : Prop := ∀ (F : Type) (f : F), m1134 f = f
theorem p1134 : P1134 := by simp [P1134, m1134]
def P1136 : Prop := ∀ (F : Type) (f : F), m1136 f = f
theorem p1136 : P1136 := by simp [P1136, m1136]
def P1137 : Prop := ∀ (O I : Type) (f : O) (g : I), m1137 f g = ComposedF.mk f g
theorem p1137 : P1137 := by simp [P1137, m1137]
def P1138 : Prop := ∀ (A B C H R : Type) (c2 : A → B → C) (cr : C → H → R)
  (f : A) (g : B) (rest : H),
  m1138 c2 cr f g rest = cr (c2 f g) rest
theorem p1138 : P1138 := by simp [P1138, m1138]
def P1140 : Prop := ∀ (α β : Type) (s p : α → String) (q : β → String)
  (n : Bool) (o : α) (i : β),
  m1140 s p q n o i = (if n then s o else p o) ++ " ∘ " ++ q i
theorem p1140 : P1140 := by simp [P1140, m1140]
def P1147 : Prop := ∀ (α : Type) (s : α → String) (x : α), m1147 s x = "!" ++ s x
theorem p1147 : P1147 := by simp [P1147, m1147]
def P1152 : Prop := ∀ (α : Type) (s : α → String) (x : α), m1152 s x = s x
theorem p1152 : P1152 := by simp [P1152, m1152]
def P1154 : Prop := ∀ (α : Type) (op : α → Bool) (s : α → String) (x : α),
  m1154 op s x = if op x then "(" ++ s x ++ ")" else s x
theorem p1154 : P1154 := by simp [P1154, m1154]
def P1156 : Prop := ∀ (α : Type) (s : α → String) (x : α), m1156 s x = "(" ++ s x ++ ")"
theorem p1156 : P1156 := by simp [P1156, m1156]
def P1158 : Prop := ∀ (α : Type) (s : α → String) (x : α), @m1158 α s x = s x
theorem p1158 : P1158 := by simp [P1158, m1158, m1152]
def P1182 : Prop := ∀ (α : Type) (f : α → Bool) x, m1182 f x = !f x
theorem p1182 : P1182 := by simp [P1182, m1182]
def P1183 : Prop := ∀ (F : Type) (f : F), m1183 f = f
theorem p1183 : P1183 := by simp [P1183, m1183]

def P1206 : Prop := ∀ (F X : Type) (n : Option Int) (f : F) (x : X), HasResult (m1206 n f x)
theorem p1206 : P1206 := by simp [P1206, HasResult]
def P1216 : Prop := ∀ (F X Args L R K Y : Type) (n m : Int) (s : Args → Int → L × R)
  (c : F → L → X → R → K → Y) (f : FixF F X) (a : Args) (k : K),
  HasResult (m1216 n m s c f a k)
theorem p1216 : P1216 := by simp [P1216, HasResult]
def P1223 : Prop := ∀ (F X A K Y : Type) (c : F → X → A → K → Y)
  (f : FixF F X) (a : A) (k : K),
  m1223 c f a k = c f.f f.x a k
theorem p1223 : P1223 := by simp [P1223, m1223]
def P1224 : Prop := ∀ (F X A K Y : Type) (c : F → A → X → K → Y)
  (f : FixF F X) (a : A) (k : K),
  m1224 c f a k = c f.f a f.x k
theorem p1224 : P1224 := by simp [P1224, m1224]
def P1226 : Prop := ∀ (F X : Type) (sf : F → String) (sx : X → String)
  (n : Int) (f : FixF F X),
  HasResult (m1226 sf sx n f)
theorem p1226 : P1226 := by simp [P1226, HasResult]

def P1259 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1259 α β γ f x y = f y x
theorem p1259 : P1259 := by simp [P1259, m1259, fixSecond]
def P1270 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1270 α β γ f x y = f y x
theorem p1270 : P1270 := by simp [P1270, m1270, fixSecond]
def P1283 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1283 α β γ f x y = f y x
theorem p1283 : P1283 := by simp [P1283, m1283, fixSecond]
def P1296 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1296 α β γ f x y = f y x
theorem p1296 : P1296 := by simp [P1296, m1296, fixSecond]
def P1309 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1309 α β γ f x y = f y x
theorem p1309 : P1309 := by simp [P1309, m1309, fixSecond]
def P1322 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1322 α β γ f x y = f y x
theorem p1322 : P1322 := by simp [P1322, m1322, fixSecond]
def P1335 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1335 α β γ f x y = f y x
theorem p1335 : P1335 := by simp [P1335, m1335, fixSecond]

def P1366 : Prop := ∀ (F : Type) (f : F), m1366 f = SplatF.mk f
theorem p1366 : P1366 := by simp [P1366, m1366]
def P1384 : Prop := ∀ (F : Type) (f : F), @m1384 F f = SplatF.mk f
theorem p1384 : P1384 := by simp [P1384, m1384, m1366]
def P1386 : Prop := ∀ (F Args Y : Type) (a : F → Args → Y)
  (s : SplatF F) (x : Args), m1386 a s x = a s.f x
theorem p1386 : P1386 := by simp [P1386, m1386]
def P1387 : Prop := ∀ (F : Type) (render : F → String) (x : SplatF F),
  m1387 render x = "splat(" ++ render x.f ++ ")"
theorem p1387 : P1387 := by simp [P1387, m1387]
def P1415 : Prop := ∀ (F T C : Type) (c : F → T → C) f t, m1415 c f t = c f t
theorem p1415 : P1415 := by simp [P1415, m1415]
def P1416 : Prop := ∀ (F : Type) (s : SplatF F), m1416 s = s.f
theorem p1416 : P1416 := by simp [P1416, m1416]
def P1417 : Prop := ∀ (F : Type) (f : F), m1417 f = f
theorem p1417 : P1417 := by simp [P1417, m1417]
def P1438 : Prop := ∀ (α β : Type) (f : α → β) x, m1438 f x = x
theorem p1438 : P1438 := by simp [P1438, m1438]

def P1453 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1453 α β γ f x y = f y x
theorem p1453 : P1453 := by simp [P1453, m1453, fixSecond]
def P1455 : Prop := ∀ (α γ I X : Type) (a : (α → γ) → I → γ) (e : X → α → γ) x i,
  m1455 a e x i = a (e x) i
theorem p1455 : P1455 := by simp [P1455, m1455]
def P1477 : Prop := ∀ (α β γ δ : Type) (m : α → β → γ) (n : γ → δ) x y,
  m1477 m n x y = n (m x y)
theorem p1477 : P1477 := by simp [P1477, m1477]
def P1478 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1478 α β γ f x y = f y x
theorem p1478 : P1478 := by simp [P1478, m1478, fixSecond]
def P1486 : Prop := ∀ (α β γ : Type) (m : α → β → γ) x y, m1486 m y x = m x y
theorem p1486 : P1486 := by simp [P1486, m1486]
def P1497 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1497 α β γ f x y = f y x
theorem p1497 : P1497 := by simp [P1497, m1497, fixSecond]
def P1499 : Prop := ∀ (α β γ δ : Type) (c : β → α → γ) (n : γ → δ) x y,
  m1499 c n y x = n (c y x)
theorem p1499 : P1499 := by simp [P1499, m1499]
def P1500 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1500 α β γ f x y = f y x
theorem p1500 : P1500 := by simp [P1500, m1500, fixSecond]

end JuliaLean.NumbersCov.Rows.Operators
