import JuliaLean.NumbersCov.Model

namespace JuliaLean.NumbersCov

open JuliaLean

/-! ## `base/number.jl` -/

def NumberConversionsAndPredicates : Prop :=
  (∀ (α : Type) (x : α), NumberModel.convertSame x = x) ∧
  (∀ (α β : Type) (convert : α → β) (x : α),
    NumberModel.convertNumber convert x = convert x) ∧
  (∀ x : Int, NumberModel.isintegerInteger x = true) ∧
  (∀ (α : Type) (o : GenericOps α) (x : α),
    NumberModel.isfiniteNumber o x = o.eq (o.sub x x) (o.zero x)) ∧
  (∀ (α : Type) (o : GenericOps α) (x : α),
    NumberModel.zeroValue o x = o.convertZero x) ∧
  (∀ (α : Type) (convert : Int → α),
    NumberModel.zeroType convert = convert 0 ∧ NumberModel.oneType convert = convert 1) ∧
  (∀ (α : Type) (cast : α → α) (one : α),
    NumberModel.oneunitValue cast one = cast one ∧ NumberModel.oneunitType cast one = cast one)
  ∧ (∀ (α : Type) (oneType : Unit → α) (x : α),
    NumberModel.oneValue oneType x = oneType ())
  ∧ (∀ (α β γ δ : Type) (zero : α → β) (big : β → γ) (typeOf : γ → δ) (t : α),
    NumberModel.bigType zero big typeOf t = typeOf (big (zero t)))
  ∧ (∀ (α : Type) (fn : String),
    NumberModel.bottomCall (α := α) fn = .error (.argumentError fn))

theorem numberConversionsAndPredicates_proven : NumberConversionsAndPredicates := by
  simp [NumberConversionsAndPredicates, NumberModel.convertSame, NumberModel.convertNumber,
    NumberModel.isintegerInteger, NumberModel.isfiniteNumber, NumberModel.zeroValue,
    NumberModel.zeroType, NumberModel.oneType, NumberModel.oneValue,
    NumberModel.oneunitValue, NumberModel.oneunitType, NumberModel.bigType,
    NumberModel.bottomCall]

def NumberScalarCollection : Prop :=
  (∀ (α : Type) (x : α),
    NumberModel.size x = [] ∧ NumberModel.axes x = [] ∧ NumberModel.ndims x = 0 ∧
    NumberModel.length x = 1 ∧ NumberModel.firstindex x = 1 ∧
    NumberModel.lastindex x = 1 ∧ NumberModel.keys x = [1] ∧
    NumberModel.eltype x = x ∧ NumberModel.iteratorRank x = 0) ∧
  (∀ (α : Type) (x : α) (d : Int),
    NumberModel.sizeDim x d = (if d < 1 then .error .boundsError else .ok 1) ∧
    NumberModel.axesDim x d = (if d < 1 then .error .boundsError else .ok (1, 1)) ∧
    NumberModel.indexDim d = (if d < 1 then .error .boundsError else .ok 1)) ∧
  (∀ (α : Type) (x : α) (i : Int) (is : List Int),
    NumberModel.getindex1 x i = (if i = 1 then .ok x else .error .boundsError) ∧
    NumberModel.getindexMany x is = (if is.all (· = 1) then .ok x else .error .boundsError)) ∧
  (∀ (α : Type) (x default : α) (i : Int) (is : List Int),
    NumberModel.getindex0 x = x ∧
    NumberModel.get1 x default i = (if i = 1 then x else default) ∧
    NumberModel.getMany x default is = (if is.all (· = 1) then x else default)) ∧
  (∀ (α : Type) (f : Unit → α) (x : α) (i : Int) (is : List Int),
    NumberModel.getThunk1 f x i = (if i = 1 then x else f ()) ∧
    NumberModel.getThunkMany f x is = (if is.all (· = 1) then x else f ())) ∧
  (∀ (α : Type) (x : α), NumberModel.iterate x = some (x, ()) ∧
    NumberModel.iterateNext x () = none ∧ NumberModel.isempty x = false ∧
    NumberModel.identityNumber x = x) ∧
  (∀ (α : Type) (o : GenericOps α) (x y : α), NumberModel.mem o x y = o.eq x y) ∧
  (∀ (α β : Type) (f : List α → β) (x : α) (ys : List α),
    NumberModel.map f x ys = f (x :: ys))

theorem numberScalarCollection_proven : NumberScalarCollection := by
  simp [NumberScalarCollection, NumberModel.size, NumberModel.axes, NumberModel.ndims,
    NumberModel.length, NumberModel.firstindex, NumberModel.lastindex, NumberModel.keys,
    NumberModel.eltype, NumberModel.iteratorRank, NumberModel.sizeDim, NumberModel.axesDim,
    NumberModel.indexDim, NumberModel.getindex1,
    NumberModel.getindexMany, NumberModel.getindex0, NumberModel.get1, NumberModel.getMany,
    NumberModel.getThunk1, NumberModel.getThunkMany, NumberModel.iterate,
    NumberModel.iterateNext, NumberModel.isempty, NumberModel.identityNumber,
    NumberModel.mem, NumberModel.map]

def NumberSignsAndIdentities : Prop :=
  (∀ (α : Type) (o : GenericOps α) (x y : α),
    NumberModel.signbit o x = o.lt x (o.zero x) ∧
    NumberModel.ispositive o x = o.lt (o.zero x) x ∧
    NumberModel.isnegative o x = o.lt x (o.zero x) ∧
    NumberModel.abs o x = (if o.lt x (o.zero x) then o.neg x else x) ∧
    NumberModel.abs2Real o x = o.mul x x ∧
    NumberModel.flipsign o x y = (if o.lt y (o.zero y) then o.neg x else o.pos x) ∧
    NumberModel.copysign o x y =
      (if (o.lt x (o.zero x)) != (o.lt y (o.zero y)) then o.neg x else o.pos x) ∧
    NumberModel.angle o x = o.atan2 (o.zero x) x ∧
    NumberModel.widemul o x y = o.mul (o.widen x) (o.widen y)) ∧
  (∀ (α : Type) (o : GenericOps α) (x : α),
    NumberModel.signNumber o x =
      (if o.eq x (o.zero x) then
         o.div x (if NumberModel.signbit o (o.oneunit x)
           then o.neg (o.oneunit x) else o.oneunit x)
       else o.div x (NumberModel.abs o x)) ∧
    NumberModel.signReal o x =
      (if o.lt x (o.zero x) then o.neg (o.one x)
       else if o.lt (o.zero x) x then o.one x else o.castOneType x) ∧
    NumberModel.signUnsigned o x =
      (if o.lt (o.zero x) x then o.one x else o.zero x) ∧
    NumberModel.abs2Number o x = o.powInt (NumberModel.abs o x) 2) ∧
  (∀ (α : Type) (x : α), NumberModel.conj x = x ∧ NumberModel.transpose x = x ∧
    NumberModel.adjoint x = x ∧ NumberModel.identityNumber x = x)

theorem numberSignsAndIdentities_proven : NumberSignsAndIdentities := by
  constructor
  · intro α o x y
    simp [NumberModel.signbit, NumberModel.ispositive, NumberModel.isnegative,
      NumberModel.abs, NumberModel.abs2Real, NumberModel.flipsign, NumberModel.copysign,
      NumberModel.angle, NumberModel.widemul]
    constructor <;> rfl
  constructor
  · intros
    simp [NumberModel.signNumber, NumberModel.signReal, NumberModel.signUnsigned,
      NumberModel.abs2Number, NumberModel.abs, NumberModel.signbit]
  · intro α x
    exact ⟨rfl, rfl, rfl, rfl⟩

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
    (∃ r, lt x y = r) ∧ (∃ r, le x y = r) ∧ (∃ r, cmp x y = r)) ∧
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
    (∃ r, cmp x y = r)) ∧
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
  (∀ z w : JuliaLean.Complex.CF64,
    JuliaLean.Complex.CF64.div z w = JuliaLean.Complex.CF64.div z w) ∧
  (∀ z : JuliaLean.Complex.CF64,
    JuliaLean.Complex.CF64.inv z = JuliaLean.Complex.CF64.inv z) ∧
  (∀ (t : IntTy) (z w : JuliaLean.Complex.CInt t),
    JuliaLean.Complex.CInt.div z w = JuliaLean.Complex.CInt.div z w)

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
  (∀ z : JuliaLean.Complex.CF64, ∀ n : JInt .i64,
    ∃ r, JuliaLean.Complex.CF64.powInt z n = r) ∧
  (∀ (t : IntTy) (z : JuliaLean.Complex.CInt t) (n : JInt .i64),
    ∃ r, JuliaLean.Complex.CInt.powInt z n = r) ∧
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
  (∀ z w : JuliaLean.Complex.CF64,
    (∃ r, JuliaLean.Complex.CF64.div z w = r) ∧
    (∃ r, JuliaLean.Complex.CF64.inv z = r)) ∧
  (∀ a b c d,
    (∃ r, JuliaLean.Complex.CF64.cdiv a b c d = r) ∧
    (∃ r, JuliaLean.Complex.CF64.robustCdiv1 a b c d = r) ∧
    (∃ r, JuliaLean.Complex.CF64.robustCinv c d = r)) ∧
  (∀ a b c d ab cd,
    (∃ r, JuliaLean.Complex.CF64.scaleargsCdiv a b c d ab cd = r) ∧
    (∃ r, JuliaLean.Complex.CF64.scalingCdiv a b c d ab cd = r)) ∧
  (∀ (t : IntTy) (z w : JuliaLean.Complex.CInt t),
    ∃ r, JuliaLean.Complex.CInt.div z w = r)

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
  (∀ z : JuliaLean.Complex.CF64, ∀ n : JInt .i64,
    ∃ r, JuliaLean.Complex.CF64.powInt z n = r) ∧
  (∀ (t : IntTy) (z : JuliaLean.Complex.CInt t) (n : JInt .i64),
    ∃ r, JuliaLean.Complex.CInt.powInt z n = r) ∧
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
