import JuliaLean.NumbersCov.Rows.Common
import JuliaLean.Registry.Types

namespace JuliaLean.NumbersCov.Rows.Number

open JuliaLean JuliaLean.Registry JuliaLean.NumbersCov
open JuliaLean.NumbersCov.Rows

def m6 (x : α) : α := NumberModel.convertSame x
def P6 : Prop := ∀ (α : Type) (x : α), m6 x = x
theorem p6 : P6 := by simp [P6, m6, NumberModel.convertSame]

def m7 (convert : α → β) (x : α) : β := NumberModel.convertNumber convert x
def P7 : Prop := ∀ (α β : Type) (convert : α → β) x, m7 convert x = convert x
theorem p7 : P7 := by simp [P7, m7, NumberModel.convertNumber]

def m22 (x : Int) : Bool := NumberModel.isintegerInteger x
def P22 : Prop := ∀ x, m22 x = true
theorem p22 : P22 := by simp [P22, m22, NumberModel.isintegerInteger]

def m84 (o : GenericOps α) (x : α) : Bool := NumberModel.isfiniteNumber o x
def P84 : Prop := ∀ (α : Type) (o : GenericOps α) x,
  m84 o x = o.eq (o.sub x x) (o.zero x)
theorem p84 : P84 := by simp [P84, m84, NumberModel.isfiniteNumber]

def m86 (x : α) := NumberModel.size x
def P86 : Prop := ∀ (α : Type) (x : α), m86 x = []
theorem p86 : P86 := by simp [P86, m86, NumberModel.size]

def m87 (x : α) (d : Int) := NumberModel.sizeDim x d
def P87 : Prop := ∀ (α : Type) (x : α) d,
  m87 x d = if d < 1 then .error .boundsError else .ok 1
theorem p87 : P87 := by simp [P87, m87, NumberModel.sizeDim]

def m88 (x : α) := NumberModel.axes x
def P88 : Prop := ∀ (α : Type) (x : α), m88 x = []
theorem p88 : P88 := by simp [P88, m88, NumberModel.axes]

def m89 (x : α) (d : Int) := NumberModel.axesDim x d
def P89 : Prop := ∀ (α : Type) (x : α) d,
  m89 x d = if d < 1 then .error .boundsError else .ok (1, 1)
theorem p89 : P89 := by simp [P89, m89, NumberModel.axesDim]

def m90 (tag : α) := NumberModel.eltype tag
def P90 : Prop := ∀ (α : Type) (tag : α), m90 tag = tag
theorem p90 : P90 := by simp [P90, m90, NumberModel.eltype]

def m91 (x : α) := NumberModel.ndims x
def P91 : Prop := ∀ (α : Type) (x : α), m91 x = 0
theorem p91 : P91 := by simp [P91, m91, NumberModel.ndims]

def m92 (tag : α) := NumberModel.ndims tag
def P92 : Prop := ∀ (α : Type) (tag : α), m92 tag = 0
theorem p92 : P92 := by simp [P92, m92, NumberModel.ndims]

def m93 (x : α) := NumberModel.length x
def P93 : Prop := ∀ (α : Type) (x : α), m93 x = 1
theorem p93 : P93 := by simp [P93, m93, NumberModel.length]

def m94 (x : α) := NumberModel.firstindex x
def P94 : Prop := ∀ (α : Type) (x : α), m94 x = 1
theorem p94 : P94 := by simp [P94, m94, NumberModel.firstindex]

def m95 (_x : α) (d : Int) := NumberModel.indexDim d
def P95 : Prop := ∀ (α : Type) (x : α) d,
  m95 x d = if d < 1 then .error .boundsError else .ok 1
theorem p95 : P95 := by simp [P95, m95, NumberModel.indexDim]

def m96 (x : α) := NumberModel.lastindex x
def P96 : Prop := ∀ (α : Type) (x : α), m96 x = 1
theorem p96 : P96 := by simp [P96, m96, NumberModel.lastindex]

def m97 (_x : α) (d : Int) := NumberModel.indexDim d
def P97 : Prop := ∀ (α : Type) (x : α) d,
  m97 x d = if d < 1 then .error .boundsError else .ok 1
theorem p97 : P97 := by simp [P97, m97, NumberModel.indexDim]

def m98 (tag : α) := NumberModel.iteratorRank tag
def P98 : Prop := ∀ (α : Type) (tag : α), m98 tag = 0
theorem p98 : P98 := by simp [P98, m98, NumberModel.iteratorRank]

def m99 (x : α) := NumberModel.keys x
def P99 : Prop := ∀ (α : Type) (x : α), m99 x = [1]
theorem p99 : P99 := by simp [P99, m99, NumberModel.keys]

def m101 (x : α) := NumberModel.getindex0 x
def P101 : Prop := ∀ (α : Type) (x : α), m101 x = x
theorem p101 : P101 := by simp [P101, m101, NumberModel.getindex0]

def m102 (x : α) (i : Int) := NumberModel.getindex1 x i
def P102 : Prop := ∀ (α : Type) (x : α) i,
  m102 x i = if i = 1 then .ok x else .error .boundsError
theorem p102 : P102 := by simp [P102, m102, NumberModel.getindex1]

def m107 (x : α) (is : List Int) := NumberModel.getindexMany x is
def P107 : Prop := ∀ (α : Type) (x : α) is,
  m107 x is = if is.all (· = 1) then .ok x else .error .boundsError
theorem p107 : P107 := by simp [P107, m107, NumberModel.getindexMany]

def m112 (x default : α) (i : Int) := NumberModel.get1 x default i
def P112 : Prop := ∀ (α : Type) (x default : α) i,
  m112 x default i = if i = 1 then x else default
theorem p112 : P112 := by simp [P112, m112, NumberModel.get1]

def m113 (x default : α) (is : List Int) := NumberModel.getMany x default is
def P113 : Prop := ∀ (α : Type) (x default : α) is,
  m113 x default is = if is.all (· = 1) then x else default
theorem p113 : P113 := by simp [P113, m113, NumberModel.getMany]

def m114 (f : Unit → α) (x : α) (i : Int) := NumberModel.getThunk1 f x i
def P114 : Prop := ∀ (α : Type) (f : Unit → α) x i,
  m114 f x i = if i = 1 then x else f ()
theorem p114 : P114 := by simp [P114, m114, NumberModel.getThunk1]

def m115 (f : Unit → α) (x : α) (is : List Int) := NumberModel.getThunkMany f x is
def P115 : Prop := ∀ (α : Type) (f : Unit → α) x is,
  m115 f x is = if is.all (· = 1) then x else f ()
theorem p115 : P115 := by simp [P115, m115, NumberModel.getThunkMany]

def m117 (x : α) := NumberModel.identityNumber x
def P117 : Prop := ∀ (α : Type) (x : α), m117 x = x
theorem p117 : P117 := by simp [P117, m117, NumberModel.identityNumber]
def m118 := @m117
def P118 : Prop := ∀ (α : Type) (x : α), @m118 α x = x
theorem p118 : P118 := by simp [P118, m118, m117, NumberModel.identityNumber]
def m119 := @m117
def P119 : Prop := ∀ (α : Type) (x : α), @m119 α x = x
theorem p119 : P119 := by simp [P119, m119, m117, NumberModel.identityNumber]

def m165 (o : GenericOps α) (x : α) := NumberModel.ispositive o x
def P165 : Prop := ∀ (α : Type) (o : GenericOps α) x, m165 o x = o.lt (o.zero x) x
theorem p165 : P165 := by simp [P165, m165, NumberModel.ispositive]
def m187 (o : GenericOps α) (x : α) := NumberModel.isnegative o x
def P187 : Prop := ∀ (α : Type) (o : GenericOps α) x, m187 o x = o.lt x (o.zero x)
theorem p187 : P187 := by simp [P187, m187, NumberModel.isnegative]

def m211 (o : GenericOps α) (x : α) := NumberModel.signNumber o x
def P211 : Prop := ∀ (α : Type) (o : GenericOps α) x, HasResult (m211 o x)
theorem p211 : P211 := by simp [P211, HasResult]
def m212 (o : GenericOps α) (x : α) := NumberModel.signReal o x
def P212 : Prop := ∀ (α : Type) (o : GenericOps α) x, HasResult (m212 o x)
theorem p212 : P212 := by simp [P212, HasResult]
def m213 (o : GenericOps α) (x : α) := NumberModel.signUnsigned o x
def P213 : Prop := ∀ (α : Type) (o : GenericOps α) x, HasResult (m213 o x)
theorem p213 : P213 := by simp [P213, HasResult]

def m238 (o : GenericOps α) (x : α) := NumberModel.abs2Number o x
def P238 : Prop := ∀ (α : Type) (o : GenericOps α) x, m238 o x = o.powInt (NumberModel.abs o x) 2
theorem p238 : P238 := by simp [P238, m238, NumberModel.abs2Number]
def m239 (o : GenericOps α) (x : α) := NumberModel.abs2Real o x
def P239 : Prop := ∀ (α : Type) (o : GenericOps α) x, m239 o x = o.mul x x
theorem p239 : P239 := by simp [P239, m239, NumberModel.abs2Real]
def m255 (o : GenericOps α) (x y : α) := NumberModel.flipsign o x y
def P255 : Prop := ∀ (α : Type) (o : GenericOps α) x y,
  m255 o x y = if NumberModel.signbit o y then o.neg x else o.pos x
theorem p255 : P255 := by simp [P255, m255, NumberModel.flipsign]
def m271 (o : GenericOps α) (x y : α) := NumberModel.copysign o x y
def P271 : Prop := ∀ (α : Type) (o : GenericOps α) x y,
  m271 o x y = if NumberModel.signbit o x != NumberModel.signbit o y then o.neg x else o.pos x
theorem p271 : P271 := by simp [P271, m271, NumberModel.copysign]

def m273 (x : α) := NumberModel.conj x
def P273 : Prop := ∀ (α : Type) (x : α), m273 x = x
theorem p273 : P273 := by simp [P273, m273, NumberModel.conj]
def m274 (x : α) := NumberModel.transpose x
def P274 : Prop := ∀ (α : Type) (x : α), m274 x = x
theorem p274 : P274 := by simp [P274, m274, NumberModel.transpose]
def m275 (x : α) := NumberModel.adjoint x
def P275 : Prop := ∀ (α : Type) (x : α), m275 x = x
theorem p275 : P275 := by simp [P275, m275, NumberModel.adjoint, NumberModel.conj]
def m276 (o : GenericOps α) (x : α) := NumberModel.angle o x
def P276 : Prop := ∀ (α : Type) (o : GenericOps α) x, m276 o x = o.atan2 (o.zero x) x
theorem p276 : P276 := by simp [P276, m276, NumberModel.angle]
def m327 (o : GenericOps α) (x y : α) := NumberModel.widemul o x y
def P327 : Prop := ∀ (α : Type) (o : GenericOps α) x y,
  m327 o x y = o.mul (o.widen x) (o.widen y)
theorem p327 : P327 := by simp [P327, m327, NumberModel.widemul]

def m329 (x : α) := NumberModel.iterate x
def P329 : Prop := ∀ (α : Type) (x : α), m329 x = some (x, ())
theorem p329 : P329 := by simp [P329, m329, NumberModel.iterate]
def m330 (x : α) (state : Unit) := NumberModel.iterateNext x state
def P330 : Prop := ∀ (α : Type) (x : α) state, m330 x state = none
theorem p330 : P330 := by simp [P330, m330, NumberModel.iterateNext]
def m331 (x : α) := NumberModel.isempty x
def P331 : Prop := ∀ (α : Type) (x : α), m331 x = false
theorem p331 : P331 := by simp [P331, m331, NumberModel.isempty]
def m332 (o : GenericOps α) (x y : α) := NumberModel.mem o x y
def P332 : Prop := ∀ (α : Type) (o : GenericOps α) x y, m332 o x y = o.eq x y
theorem p332 : P332 := by simp [P332, m332, NumberModel.mem]
def m334 (f : List α → β) (x : α) (ys : List α) := NumberModel.map f x ys
def P334 : Prop := ∀ (α β : Type) (f : List α → β) x ys, m334 f x ys = f (x :: ys)
theorem p334 : P334 := by simp [P334, m334, NumberModel.map]

def m363 (o : GenericOps α) (x : α) := NumberModel.zeroValue o x
def P363 : Prop := ∀ (α : Type) (o : GenericOps α) x, m363 o x = o.convertZero x
theorem p363 : P363 := by simp [P363, m363, NumberModel.zeroValue]
def m364 (convert : Int → α) := NumberModel.zeroType convert
def P364 : Prop := ∀ (α : Type) (convert : Int → α), m364 convert = convert 0
theorem p364 : P364 := by simp [P364, m364, NumberModel.zeroType]
def m365 (fn : String) : Jl α := NumberModel.bottomCall fn
def P365 : Prop := ∀ (α : Type) fn, @m365 α fn = .error (.argumentError fn)
theorem p365 : P365 := by simp [P365, m365, NumberModel.bottomCall]
def m405 (convert : Int → α) := NumberModel.oneType convert
def P405 : Prop := ∀ (α : Type) (convert : Int → α), m405 convert = convert 1
theorem p405 : P405 := by simp [P405, m405, NumberModel.oneType]
def m406 (oneType : Unit → α) (x : α) := NumberModel.oneValue oneType x
def P406 : Prop := ∀ (α : Type) (oneType : Unit → α) x, m406 oneType x = oneType ()
theorem p406 : P406 := by simp [P406, m406, NumberModel.oneValue]
def m407 := @m365
def P407 : Prop := ∀ (α : Type) fn, @m407 α fn = .error (.argumentError fn)
theorem p407 : P407 := by simp [P407, m407, m365, NumberModel.bottomCall]
def m430 (cast : α → α) (one : α) := NumberModel.oneunitValue cast one
def P430 : Prop := ∀ (α : Type) (cast : α → α) one, m430 cast one = cast one
theorem p430 : P430 := by simp [P430, m430, NumberModel.oneunitValue]
def m431 (cast : α → α) (one : α) := NumberModel.oneunitType cast one
def P431 : Prop := ∀ (α : Type) (cast : α → α) one, m431 cast one = cast one
theorem p431 : P431 := by simp [P431, m431, NumberModel.oneunitType]
def m432 := @m365
def P432 : Prop := ∀ (α : Type) fn, @m432 α fn = .error (.argumentError fn)
theorem p432 : P432 := by simp [P432, m432, m365, NumberModel.bottomCall]
def m452 (zero : α → β) (big : β → γ) (typeOf : γ → δ) (t : α) :=
  NumberModel.bigType zero big typeOf t
def P452 : Prop := ∀ (α β γ δ : Type) (zero : α → β) (big : β → γ)
  (typeOf : γ → δ) t, m452 zero big typeOf t = typeOf (big (zero t))
theorem p452 : P452 := by simp [P452, m452, NumberModel.bigType]
def m453 := @m365
def P453 : Prop := ∀ (α : Type) fn, @m453 α fn = .error (.argumentError fn)
theorem p453 : P453 := by simp [P453, m453, m365, NumberModel.bottomCall]

end JuliaLean.NumbersCov.Rows.Number
