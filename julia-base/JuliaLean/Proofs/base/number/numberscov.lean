import JuliaLean.base.number
import JuliaLean.Proofs.base.number.numberscov_common

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


end JuliaLean.NumbersCov

namespace JuliaLean.NumbersCov.Rows.Number

open JuliaLean JuliaLean.Registry JuliaLean.NumbersCov
open JuliaLean.NumbersCov.Rows

def P6 : Prop := ∀ (α : Type) (x : α), m6 x = x
theorem p6 : P6 := by simp [P6, m6, NumberModel.convertSame]

def P7 : Prop := ∀ (α β : Type) (convert : α → β) x, m7 convert x = convert x
theorem p7 : P7 := by simp [P7, m7, NumberModel.convertNumber]

def P22 : Prop := ∀ x, m22 x = true
theorem p22 : P22 := by simp [P22, m22, NumberModel.isintegerInteger]

def P84 : Prop := ∀ (α : Type) (o : GenericOps α) x,
  m84 o x = o.eq (o.sub x x) (o.zero x)
theorem p84 : P84 := by simp [P84, m84, NumberModel.isfiniteNumber]

def P86 : Prop := ∀ (α : Type) (x : α), m86 x = []
theorem p86 : P86 := by simp [P86, m86, NumberModel.size]

def P87 : Prop := ∀ (α : Type) (x : α) d,
  m87 x d = if d < 1 then .error .boundsError else .ok 1
theorem p87 : P87 := by simp [P87, m87, NumberModel.sizeDim]

def P88 : Prop := ∀ (α : Type) (x : α), m88 x = []
theorem p88 : P88 := by simp [P88, m88, NumberModel.axes]

def P89 : Prop := ∀ (α : Type) (x : α) d,
  m89 x d = if d < 1 then .error .boundsError else .ok (1, 1)
theorem p89 : P89 := by simp [P89, m89, NumberModel.axesDim]

def P90 : Prop := ∀ (α : Type) (tag : α), m90 tag = tag
theorem p90 : P90 := by simp [P90, m90, NumberModel.eltype]

def P91 : Prop := ∀ (α : Type) (x : α), m91 x = 0
theorem p91 : P91 := by simp [P91, m91, NumberModel.ndims]

def P92 : Prop := ∀ (α : Type) (tag : α), m92 tag = 0
theorem p92 : P92 := by simp [P92, m92, NumberModel.ndims]

def P93 : Prop := ∀ (α : Type) (x : α), m93 x = 1
theorem p93 : P93 := by simp [P93, m93, NumberModel.length]

def P94 : Prop := ∀ (α : Type) (x : α), m94 x = 1
theorem p94 : P94 := by simp [P94, m94, NumberModel.firstindex]

def P95 : Prop := ∀ (α : Type) (x : α) d,
  m95 x d = if d < 1 then .error .boundsError else .ok 1
theorem p95 : P95 := by simp [P95, m95, NumberModel.indexDim]

def P96 : Prop := ∀ (α : Type) (x : α), m96 x = 1
theorem p96 : P96 := by simp [P96, m96, NumberModel.lastindex]

def P97 : Prop := ∀ (α : Type) (x : α) d,
  m97 x d = if d < 1 then .error .boundsError else .ok 1
theorem p97 : P97 := by simp [P97, m97, NumberModel.indexDim]

def P98 : Prop := ∀ (α : Type) (tag : α), m98 tag = 0
theorem p98 : P98 := by simp [P98, m98, NumberModel.iteratorRank]

def P99 : Prop := ∀ (α : Type) (x : α), m99 x = [1]
theorem p99 : P99 := by simp [P99, m99, NumberModel.keys]

def P101 : Prop := ∀ (α : Type) (x : α), m101 x = x
theorem p101 : P101 := by simp [P101, m101, NumberModel.getindex0]

def P102 : Prop := ∀ (α : Type) (x : α) i,
  m102 x i = if i = 1 then .ok x else .error .boundsError
theorem p102 : P102 := by simp [P102, m102, NumberModel.getindex1]

def P107 : Prop := ∀ (α : Type) (x : α) is,
  m107 x is = if is.all (· = 1) then .ok x else .error .boundsError
theorem p107 : P107 := by simp [P107, m107, NumberModel.getindexMany]

def P112 : Prop := ∀ (α : Type) (x default : α) i,
  m112 x default i = if i = 1 then x else default
theorem p112 : P112 := by simp [P112, m112, NumberModel.get1]

def P113 : Prop := ∀ (α : Type) (x default : α) is,
  m113 x default is = if is.all (· = 1) then x else default
theorem p113 : P113 := by simp [P113, m113, NumberModel.getMany]

def P114 : Prop := ∀ (α : Type) (f : Unit → α) x i,
  m114 f x i = if i = 1 then x else f ()
theorem p114 : P114 := by simp [P114, m114, NumberModel.getThunk1]

def P115 : Prop := ∀ (α : Type) (f : Unit → α) x is,
  m115 f x is = if is.all (· = 1) then x else f ()
theorem p115 : P115 := by simp [P115, m115, NumberModel.getThunkMany]

def P117 : Prop := ∀ (α : Type) (x : α), m117 x = x
theorem p117 : P117 := by simp [P117, m117, NumberModel.identityNumber]
def P118 : Prop := ∀ (α : Type) (x : α), @m118 α x = x
theorem p118 : P118 := by simp [P118, m118, m117, NumberModel.identityNumber]
def P119 : Prop := ∀ (α : Type) (x : α), @m119 α x = x
theorem p119 : P119 := by simp [P119, m119, m117, NumberModel.identityNumber]

def P165 : Prop := ∀ (α : Type) (o : GenericOps α) x, m165 o x = o.lt (o.zero x) x
theorem p165 : P165 := by simp [P165, m165, NumberModel.ispositive]
def P187 : Prop := ∀ (α : Type) (o : GenericOps α) x, m187 o x = o.lt x (o.zero x)
theorem p187 : P187 := by simp [P187, m187, NumberModel.isnegative]

def P211 : Prop := ∀ (α : Type) (o : GenericOps α) x, HasResult (m211 o x)
theorem p211 : P211 := by simp [P211, HasResult]
def P212 : Prop := ∀ (α : Type) (o : GenericOps α) x, HasResult (m212 o x)
theorem p212 : P212 := by simp [P212, HasResult]
def P213 : Prop := ∀ (α : Type) (o : GenericOps α) x, HasResult (m213 o x)
theorem p213 : P213 := by simp [P213, HasResult]

def P238 : Prop := ∀ (α : Type) (o : GenericOps α) x, m238 o x = o.powInt (NumberModel.abs o x) 2
theorem p238 : P238 := by simp [P238, m238, NumberModel.abs2Number]
def P239 : Prop := ∀ (α : Type) (o : GenericOps α) x, m239 o x = o.mul x x
theorem p239 : P239 := by simp [P239, m239, NumberModel.abs2Real]
def P255 : Prop := ∀ (α : Type) (o : GenericOps α) x y,
  m255 o x y = if NumberModel.signbit o y then o.neg x else o.pos x
theorem p255 : P255 := by simp [P255, m255, NumberModel.flipsign]
def P271 : Prop := ∀ (α : Type) (o : GenericOps α) x y,
  m271 o x y = if NumberModel.signbit o x != NumberModel.signbit o y then o.neg x else o.pos x
theorem p271 : P271 := by simp [P271, m271, NumberModel.copysign]

def P273 : Prop := ∀ (α : Type) (x : α), m273 x = x
theorem p273 : P273 := by simp [P273, m273, NumberModel.conj]
def P274 : Prop := ∀ (α : Type) (x : α), m274 x = x
theorem p274 : P274 := by simp [P274, m274, NumberModel.transpose]
def P275 : Prop := ∀ (α : Type) (x : α), m275 x = x
theorem p275 : P275 := by simp [P275, m275, NumberModel.adjoint, NumberModel.conj]
def P276 : Prop := ∀ (α : Type) (o : GenericOps α) x, m276 o x = o.atan2 (o.zero x) x
theorem p276 : P276 := by simp [P276, m276, NumberModel.angle]
def P327 : Prop := ∀ (α : Type) (o : GenericOps α) x y,
  m327 o x y = o.mul (o.widen x) (o.widen y)
theorem p327 : P327 := by simp [P327, m327, NumberModel.widemul]

def P329 : Prop := ∀ (α : Type) (x : α), m329 x = some (x, ())
theorem p329 : P329 := by simp [P329, m329, NumberModel.iterate]
def P330 : Prop := ∀ (α : Type) (x : α) state, m330 x state = none
theorem p330 : P330 := by simp [P330, m330, NumberModel.iterateNext]
def P331 : Prop := ∀ (α : Type) (x : α), m331 x = false
theorem p331 : P331 := by simp [P331, m331, NumberModel.isempty]
def P332 : Prop := ∀ (α : Type) (o : GenericOps α) x y, m332 o x y = o.eq x y
theorem p332 : P332 := by simp [P332, m332, NumberModel.mem]
def P334 : Prop := ∀ (α β : Type) (f : List α → β) x ys, m334 f x ys = f (x :: ys)
theorem p334 : P334 := by simp [P334, m334, NumberModel.map]

def P363 : Prop := ∀ (α : Type) (o : GenericOps α) x, m363 o x = o.convertZero x
theorem p363 : P363 := by simp [P363, m363, NumberModel.zeroValue]
def P364 : Prop := ∀ (α : Type) (convert : Int → α), m364 convert = convert 0
theorem p364 : P364 := by simp [P364, m364, NumberModel.zeroType]
def P365 : Prop := ∀ (α : Type) fn, @m365 α fn = .error (.argumentError fn)
theorem p365 : P365 := by simp [P365, m365, NumberModel.bottomCall]
def P405 : Prop := ∀ (α : Type) (convert : Int → α), m405 convert = convert 1
theorem p405 : P405 := by simp [P405, m405, NumberModel.oneType]
def P406 : Prop := ∀ (α : Type) (oneType : Unit → α) x, m406 oneType x = oneType ()
theorem p406 : P406 := by simp [P406, m406, NumberModel.oneValue]
def P407 : Prop := ∀ (α : Type) fn, @m407 α fn = .error (.argumentError fn)
theorem p407 : P407 := by simp [P407, m407, m365, NumberModel.bottomCall]
def P430 : Prop := ∀ (α : Type) (cast : α → α) one, m430 cast one = cast one
theorem p430 : P430 := by simp [P430, m430, NumberModel.oneunitValue]
def P431 : Prop := ∀ (α : Type) (cast : α → α) one, m431 cast one = cast one
theorem p431 : P431 := by simp [P431, m431, NumberModel.oneunitType]
def P432 : Prop := ∀ (α : Type) fn, @m432 α fn = .error (.argumentError fn)
theorem p432 : P432 := by simp [P432, m432, m365, NumberModel.bottomCall]
def P452 : Prop := ∀ (α β γ δ : Type) (zero : α → β) (big : β → γ)
  (typeOf : γ → δ) t, m452 zero big typeOf t = typeOf (big (zero t))
theorem p452 : P452 := by simp [P452, m452, NumberModel.bigType]
def P453 : Prop := ∀ (α : Type) fn, @m453 α fn = .error (.argumentError fn)
theorem p453 : P453 := by simp [P453, m453, m365, NumberModel.bottomCall]

end JuliaLean.NumbersCov.Rows.Number
