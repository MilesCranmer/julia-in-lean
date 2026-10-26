import JuliaLean.MathCov.PropsCoverage
import JuliaLean.Registry.Types

/-!
One registry property per owned Julia method. Each proposition applies a source-order model of
that method to every allowed input. Generated mechanically from the owned method manifests after
the models were compared with Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.MathCov.Methods

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.Registry
open JuliaLean.MathCov JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathFuncs (ExpBase LogBase)
open JuliaLean.FloatFuncs (Mode)

/-- `sin(x::T) where T<:Union{Float32, Float64}` at `base/special/trig.jl:28-51`. -/
def P_special_trig_28 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (Trig.sin T x)

theorem p_special_trig_28_proven : P_special_trig_28 := by simp [P_special_trig_28, HasResult]

/-- `sin_kernel(y::DoubleFloat64)` at `base/special/trig.jl:68-74`. -/
def P_special_trig_68 : Prop := ∀ y : Trig.DF64, HasResult (Trig.sinKernelD y)

theorem p_special_trig_68_proven : P_special_trig_68 := by simp [P_special_trig_68, HasResult]

/-- `sin_kernel(y::Float64)` at `base/special/trig.jl:75-81`. -/
def P_special_trig_75 : Prop := ∀ y : FV .f64, HasResult (Trig.sinKernel64 y)

theorem p_special_trig_75_proven : P_special_trig_75 := by simp [P_special_trig_75, HasResult]

/-- `sin_kernel(x::Float32)` at `base/special/trig.jl:84-84`. -/
def P_special_trig_84 : Prop := ∀ x : FV .f32, HasResult (Trig.sinK1 .f32 x)

theorem p_special_trig_84_proven : P_special_trig_84 := by simp [P_special_trig_84, HasResult]

/-- `sin_kernel(y::DoubleFloat32)` at `base/special/trig.jl:85-93`. -/
def P_special_trig_85 : Prop := ∀ y : Trig.DF64, HasResult (Trig.sinK .f32 y)

theorem p_special_trig_85_proven : P_special_trig_85 := by simp [P_special_trig_85, HasResult]

/-- `cos(x::T) where T<:Union{Float32, Float64}` at `base/special/trig.jl:96-120`. -/
def P_special_trig_96 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (Trig.cos T x)

theorem p_special_trig_96_proven : P_special_trig_96 := by simp [P_special_trig_96, HasResult]

/-- `cos_kernel(y::DoubleFloat64)` at `base/special/trig.jl:134-141`. -/
def P_special_trig_134 : Prop := ∀ y : Trig.DF64, HasResult (Trig.cosKernelD y)

theorem p_special_trig_134_proven : P_special_trig_134 := by simp [P_special_trig_134, HasResult]

/-- `cos_kernel(y::Float64)` at `base/special/trig.jl:142-149`. -/
def P_special_trig_142 : Prop := ∀ y : FV .f64, HasResult (Trig.cosKernel64 y)

theorem p_special_trig_142_proven : P_special_trig_142 := by simp [P_special_trig_142, HasResult]

/-- `cos_kernel(x::Float32)` at `base/special/trig.jl:152-152`. -/
def P_special_trig_152 : Prop := ∀ x : FV .f32, HasResult (Trig.cosK1 .f32 x)

theorem p_special_trig_152_proven : P_special_trig_152 := by simp [P_special_trig_152, HasResult]

/-- `cos_kernel(y::DoubleFloat32)` at `base/special/trig.jl:153-160`. -/
def P_special_trig_153 : Prop := ∀ y : Trig.DF64, HasResult (Trig.cosK .f32 y)

theorem p_special_trig_153_proven : P_special_trig_153 := by simp [P_special_trig_153, HasResult]

/-- `sincos(x::T) where T<:Union{Float32, Float64}` at `base/special/trig.jl:174-200`. -/
def P_special_trig_174 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (Trig.sincos T x)

theorem p_special_trig_174_proven : P_special_trig_174 := by simp [P_special_trig_174, HasResult]

/-- `_sincos(x::AbstractFloat)` at `base/special/trig.jl:202-202`. -/
def P_special_trig_202 : Prop := ∀ (α β : Type) (f : α → β) (x : α), HasResult (Trig.sincosAbstract f x)

theorem p_special_trig_202_proven : P_special_trig_202 := by simp [P_special_trig_202, HasResult]

/-- `_sincos(x)` at `base/special/trig.jl:203-203`. -/
def P_special_trig_203 : Prop := ∀ (α β : Type) (s c : α → β) (x : α), HasResult (Trig.sincosFallback s c x)

theorem p_special_trig_203_proven : P_special_trig_203 := by simp [P_special_trig_203, HasResult]

/-- `sincos(x)` at `base/special/trig.jl:205-205`. -/
def P_special_trig_205 : Prop := ∀ (α β γ : Type) (float : α → β) (f : β → γ) (x : α), HasResult (Trig.sincosGeneric float f x)

theorem p_special_trig_205_proven : P_special_trig_205 := by simp [P_special_trig_205, HasResult]

/-- `sincos_kernel(y::Union{Float32, Float64, DoubleFloat32, DoubleFloat64})` at `base/special/trig.jl:211-211`. -/
def P_special_trig_211 : Prop := ∀ T : FTy, ∀ y : Trig.DF64, HasResult (Trig.sincosK T y)

theorem p_special_trig_211_proven : P_special_trig_211 := by simp [P_special_trig_211, HasResult]

/-- `tan(x::T) where T<:Union{Float32, Float64}` at `base/special/trig.jl:214-232`. -/
def P_special_trig_214 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (Trig.tan T x)

theorem p_special_trig_214_proven : P_special_trig_214 := by simp [P_special_trig_214, HasResult]

/-- `tan_kernel(y::Float64)` at `base/special/trig.jl:234-234`. -/
def P_special_trig_234 : Prop := ∀ y : FV .f64, HasResult (Trig.tanKernel64 y)

theorem p_special_trig_234_proven : P_special_trig_234 := by simp [P_special_trig_234, HasResult]

/-- `tan_kernel(y::DoubleFloat64, k)` at `base/special/trig.jl:235-334`. -/
def P_special_trig_235 : Prop := ∀ (y : Trig.DF64) (k : Int), HasResult (Trig.tanKernelD y k)

theorem p_special_trig_235_proven : P_special_trig_235 := by simp [P_special_trig_235, HasResult]

/-- `tan_kernel(y::Float32)` at `base/special/trig.jl:336-336`. -/
def P_special_trig_336 : Prop := ∀ x : FV .f32, HasResult (Trig.tanK1 .f32 x)

theorem p_special_trig_336_proven : P_special_trig_336 := by simp [P_special_trig_336, HasResult]

/-- `tan_kernel(y::DoubleFloat32, k)` at `base/special/trig.jl:337-351`. -/
def P_special_trig_337 : Prop := ∀ (y : Trig.DF64) (k : Int), HasResult (Trig.tanK .f32 y k)

theorem p_special_trig_337_proven : P_special_trig_337 := by simp [P_special_trig_337, HasResult]

/-- `sin_kernel(x::Real)` at `base/special/trig.jl:354-354`. -/
def P_special_trig_354 : Prop := ∀ (α β : Type) (f : α → β) (x : α), HasResult (Trig.sinKernelReal f x)

theorem p_special_trig_354_proven : P_special_trig_354 := by simp [P_special_trig_354, HasResult]

/-- `cos_kernel(x::Real)` at `base/special/trig.jl:355-355`. -/
def P_special_trig_355 : Prop := ∀ (α β : Type) (f : α → β) (x : α), HasResult (Trig.sinKernelReal f x)

theorem p_special_trig_355_proven : P_special_trig_355 := by simp [P_special_trig_355, HasResult]

/-- `tan_kernel(x::Real)` at `base/special/trig.jl:356-356`. -/
def P_special_trig_356 : Prop := ∀ (α β : Type) (f : α → β) (x : α), HasResult (Trig.sinKernelReal f x)

theorem p_special_trig_356_proven : P_special_trig_356 := by simp [P_special_trig_356, HasResult]

/-- `sincos_kernel(x::Real)` at `base/special/trig.jl:357-357`. -/
def P_special_trig_357 : Prop := ∀ (α β : Type) (f : α → β) (x : α), HasResult (Trig.sinKernelReal f x)

theorem p_special_trig_357_proven : P_special_trig_357 := by simp [P_special_trig_357, HasResult]

/-- `ASIN_X_MIN_THRESHOLD(::Type{Float32})` at `base/special/trig.jl:361-361`. -/
def P_special_trig_361 : Prop := ∀ _u : Unit, HasResult (Trig.asinMin .f32)

theorem p_special_trig_361_proven : P_special_trig_361 := by simp [P_special_trig_361, HasResult]

/-- `ASIN_X_MIN_THRESHOLD(::Type{Float64})` at `base/special/trig.jl:362-362`. -/
def P_special_trig_362 : Prop := ∀ _u : Unit, HasResult (Trig.asinMin .f64)

theorem p_special_trig_362_proven : P_special_trig_362 := by simp [P_special_trig_362, HasResult]

/-- `arc_p(t::Float64)` at `base/special/trig.jl:364-371`. -/
def P_special_trig_364 : Prop := ∀ t : FV .f64, HasResult (Trig.arcP .f64 t)

theorem p_special_trig_364_proven : P_special_trig_364 := by simp [P_special_trig_364, HasResult]

/-- `arc_q(z::Float64)` at `base/special/trig.jl:373-379`. -/
def P_special_trig_373 : Prop := ∀ t : FV .f64, HasResult (Trig.arcQ .f64 t)

theorem p_special_trig_373_proven : P_special_trig_373 := by simp [P_special_trig_373, HasResult]

/-- `arc_p(t::Float32)` at `base/special/trig.jl:381-385`. -/
def P_special_trig_381 : Prop := ∀ t : FV .f32, HasResult (Trig.arcP .f32 t)

theorem p_special_trig_381_proven : P_special_trig_381 := by simp [P_special_trig_381, HasResult]

/-- `arc_q(t::Float32)` at `base/special/trig.jl:387-387`. -/
def P_special_trig_387 : Prop := ∀ t : FV .f32, HasResult (Trig.arcQ .f32 t)

theorem p_special_trig_387_proven : P_special_trig_387 := by simp [P_special_trig_387, HasResult]

/-- `arc_tRt(t)` at `base/special/trig.jl:389-389`. -/
def P_special_trig_389 : Prop := ∀ T : FTy, ∀ t : FV T, HasResult (Trig.arcTRt T t)

theorem p_special_trig_389_proven : P_special_trig_389 := by simp [P_special_trig_389, HasResult]

/-- `asin_kernel(t::Float64, x::Float64)` at `base/special/trig.jl:392-418`. -/
def P_special_trig_392 : Prop := ∀ (t x : FV .f64), HasResult (Trig.asinKernel64 t x)

theorem p_special_trig_392_proven : P_special_trig_392 := by simp [P_special_trig_392, HasResult]

/-- `asin_kernel(t::Float32, x::Float32)` at `base/special/trig.jl:419-423`. -/
def P_special_trig_419 : Prop := ∀ (t x : FV .f32), HasResult (Trig.asinKernel32 t x)

theorem p_special_trig_419_proven : P_special_trig_419 := by simp [P_special_trig_419, HasResult]

/-- `asin_domain_error(x)` at `base/special/trig.jl:425-425`. -/
def P_special_trig_425 : Prop := ∀ x : FV .f64, HasResult (Trig.asinDomainError (α := FV .f64))

theorem p_special_trig_425_proven : P_special_trig_425 := by simp [P_special_trig_425, HasResult]

/-- `asin(x::T) where T<:Union{Float32, Float64}` at `base/special/trig.jl:426-450`. -/
def P_special_trig_426 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (Trig.asin T x)

theorem p_special_trig_426_proven : P_special_trig_426 := by simp [P_special_trig_426, HasResult]

/-- `ATAN_1_O_2_HI(::Type{Float64})` at `base/special/trig.jl:453-453`. -/
def P_special_trig_453 : Prop := ∀ _u : Unit, HasResult (Trig.atanHi .f64 0)

theorem p_special_trig_453_proven : P_special_trig_453 := by simp [P_special_trig_453, HasResult]

/-- `ATAN_2_O_2_HI(::Type{Float64})` at `base/special/trig.jl:454-454`. -/
def P_special_trig_454 : Prop := ∀ _u : Unit, HasResult (Trig.atanHi .f64 1)

theorem p_special_trig_454_proven : P_special_trig_454 := by simp [P_special_trig_454, HasResult]

/-- `ATAN_3_O_2_HI(::Type{Float64})` at `base/special/trig.jl:455-455`. -/
def P_special_trig_455 : Prop := ∀ _u : Unit, HasResult (Trig.atanHi .f64 2)

theorem p_special_trig_455_proven : P_special_trig_455 := by simp [P_special_trig_455, HasResult]

/-- `ATAN_INF_HI(::Type{Float64})` at `base/special/trig.jl:456-456`. -/
def P_special_trig_456 : Prop := ∀ _u : Unit, HasResult (Trig.atanHi .f64 3)

theorem p_special_trig_456_proven : P_special_trig_456 := by simp [P_special_trig_456, HasResult]

/-- `ATAN_1_O_2_HI(::Type{Float32})` at `base/special/trig.jl:458-458`. -/
def P_special_trig_458 : Prop := ∀ _u : Unit, HasResult (Trig.atanHi .f32 0)

theorem p_special_trig_458_proven : P_special_trig_458 := by simp [P_special_trig_458, HasResult]

/-- `ATAN_2_O_2_HI(::Type{Float32})` at `base/special/trig.jl:459-459`. -/
def P_special_trig_459 : Prop := ∀ _u : Unit, HasResult (Trig.atanHi .f32 1)

theorem p_special_trig_459_proven : P_special_trig_459 := by simp [P_special_trig_459, HasResult]

/-- `ATAN_3_O_2_HI(::Type{Float32})` at `base/special/trig.jl:460-460`. -/
def P_special_trig_460 : Prop := ∀ _u : Unit, HasResult (Trig.atanHi .f32 2)

theorem p_special_trig_460_proven : P_special_trig_460 := by simp [P_special_trig_460, HasResult]

/-- `ATAN_INF_HI(::Type{Float32})` at `base/special/trig.jl:461-461`. -/
def P_special_trig_461 : Prop := ∀ _u : Unit, HasResult (Trig.atanHi .f32 3)

theorem p_special_trig_461_proven : P_special_trig_461 := by simp [P_special_trig_461, HasResult]

/-- `ATAN_1_O_2_LO(::Type{Float64})` at `base/special/trig.jl:463-463`. -/
def P_special_trig_463 : Prop := ∀ _u : Unit, HasResult (Trig.atanLo .f64 0)

theorem p_special_trig_463_proven : P_special_trig_463 := by simp [P_special_trig_463, HasResult]

/-- `ATAN_2_O_2_LO(::Type{Float64})` at `base/special/trig.jl:464-464`. -/
def P_special_trig_464 : Prop := ∀ _u : Unit, HasResult (Trig.atanLo .f64 1)

theorem p_special_trig_464_proven : P_special_trig_464 := by simp [P_special_trig_464, HasResult]

/-- `ATAN_3_O_2_LO(::Type{Float64})` at `base/special/trig.jl:465-465`. -/
def P_special_trig_465 : Prop := ∀ _u : Unit, HasResult (Trig.atanLo .f64 2)

theorem p_special_trig_465_proven : P_special_trig_465 := by simp [P_special_trig_465, HasResult]

/-- `ATAN_INF_LO(::Type{Float64})` at `base/special/trig.jl:466-466`. -/
def P_special_trig_466 : Prop := ∀ _u : Unit, HasResult (Trig.atanLo .f64 3)

theorem p_special_trig_466_proven : P_special_trig_466 := by simp [P_special_trig_466, HasResult]

/-- `ATAN_1_O_2_LO(::Type{Float32})` at `base/special/trig.jl:468-468`. -/
def P_special_trig_468 : Prop := ∀ _u : Unit, HasResult (Trig.atanLo .f32 0)

theorem p_special_trig_468_proven : P_special_trig_468 := by simp [P_special_trig_468, HasResult]

/-- `ATAN_2_O_2_LO(::Type{Float32})` at `base/special/trig.jl:469-469`. -/
def P_special_trig_469 : Prop := ∀ _u : Unit, HasResult (Trig.atanLo .f32 1)

theorem p_special_trig_469_proven : P_special_trig_469 := by simp [P_special_trig_469, HasResult]

/-- `ATAN_3_O_2_LO(::Type{Float32})` at `base/special/trig.jl:470-470`. -/
def P_special_trig_470 : Prop := ∀ _u : Unit, HasResult (Trig.atanLo .f32 2)

theorem p_special_trig_470_proven : P_special_trig_470 := by simp [P_special_trig_470, HasResult]

/-- `ATAN_INF_LO(::Type{Float32})` at `base/special/trig.jl:471-471`. -/
def P_special_trig_471 : Prop := ∀ _u : Unit, HasResult (Trig.atanLo .f32 3)

theorem p_special_trig_471_proven : P_special_trig_471 := by simp [P_special_trig_471, HasResult]

/-- `ATAN_LARGE_X(::Type{Float64})` at `base/special/trig.jl:473-473`. -/
def P_special_trig_473 : Prop := ∀ _u : Unit, HasResult (Trig.atanLarge .f64)

theorem p_special_trig_473_proven : P_special_trig_473 := by simp [P_special_trig_473, HasResult]

/-- `ATAN_SMALL_X(::Type{Float64})` at `base/special/trig.jl:474-474`. -/
def P_special_trig_474 : Prop := ∀ _u : Unit, HasResult (Trig.atanSmall .f64)

theorem p_special_trig_474_proven : P_special_trig_474 := by simp [P_special_trig_474, HasResult]

/-- `ATAN_LARGE_X(::Type{Float32})` at `base/special/trig.jl:475-475`. -/
def P_special_trig_475 : Prop := ∀ _u : Unit, HasResult (Trig.atanLarge .f32)

theorem p_special_trig_475_proven : P_special_trig_475 := by simp [P_special_trig_475, HasResult]

/-- `ATAN_SMALL_X(::Type{Float32})` at `base/special/trig.jl:476-476`. -/
def P_special_trig_476 : Prop := ∀ _u : Unit, HasResult (Trig.atanSmall .f32)

theorem p_special_trig_476_proven : P_special_trig_476 := by simp [P_special_trig_476, HasResult]

/-- `atan_p(z::Float64, w::Float64)` at `base/special/trig.jl:478-484`. -/
def P_special_trig_478 : Prop := ∀ (z w : FV .f64), HasResult (Trig.atanP .f64 z w)

theorem p_special_trig_478_proven : P_special_trig_478 := by simp [P_special_trig_478, HasResult]

/-- `atan_q(w::Float64)` at `base/special/trig.jl:485-490`. -/
def P_special_trig_485 : Prop := ∀ w : FV .f64, HasResult (Trig.atanQ .f64 w)

theorem p_special_trig_485_proven : P_special_trig_485 := by simp [P_special_trig_485, HasResult]

/-- `atan_p(z::Float32, w::Float32)` at `base/special/trig.jl:491-491`. -/
def P_special_trig_491 : Prop := ∀ (z w : FV .f32), HasResult (Trig.atanP .f32 z w)

theorem p_special_trig_491_proven : P_special_trig_491 := by simp [P_special_trig_491, HasResult]

/-- `atan_q(w::Float32)` at `base/special/trig.jl:492-492`. -/
def P_special_trig_492 : Prop := ∀ w : FV .f32, HasResult (Trig.atanQ .f32 w)

theorem p_special_trig_492_proven : P_special_trig_492 := by simp [P_special_trig_492, HasResult]

/-- `atan_pq(x)` at `base/special/trig.jl:493-498`. -/
def P_special_trig_493 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (Trig.atanPQ T x)

theorem p_special_trig_493_proven : P_special_trig_493 := by simp [P_special_trig_493, HasResult]

/-- `atan(x::T) where T<:Union{Float32, Float64}` at `base/special/trig.jl:500-554`. -/
def P_special_trig_500 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (Trig.atan T x)

theorem p_special_trig_500_proven : P_special_trig_500 := by simp [P_special_trig_500, HasResult]

/-- `ATAN2_PI_LO(::Type{Float32})` at `base/special/trig.jl:556-556`. -/
def P_special_trig_556 : Prop := ∀ _u : Unit, HasResult (Trig.atan2PiLo .f32)

theorem p_special_trig_556_proven : P_special_trig_556 := by simp [P_special_trig_556, HasResult]

/-- `ATAN2_RATIO_BIT_SHIFT(::Type{Float32})` at `base/special/trig.jl:557-557`. -/
def P_special_trig_557 : Prop := ∀ _u : Unit, HasResult (Trig.atan2Shift .f32)

theorem p_special_trig_557_proven : P_special_trig_557 := by simp [P_special_trig_557, HasResult]

/-- `ATAN2_RATIO_THRESHOLD(::Type{Float32})` at `base/special/trig.jl:558-558`. -/
def P_special_trig_558 : Prop := ∀ _u : Unit, HasResult (Trig.atan2Threshold .f32)

theorem p_special_trig_558_proven : P_special_trig_558 := by simp [P_special_trig_558, HasResult]

/-- `ATAN2_PI_LO(::Type{Float64})` at `base/special/trig.jl:560-560`. -/
def P_special_trig_560 : Prop := ∀ _u : Unit, HasResult (Trig.atan2PiLo .f64)

theorem p_special_trig_560_proven : P_special_trig_560 := by simp [P_special_trig_560, HasResult]

/-- `ATAN2_RATIO_BIT_SHIFT(::Type{Float64})` at `base/special/trig.jl:561-561`. -/
def P_special_trig_561 : Prop := ∀ _u : Unit, HasResult (Trig.atan2Shift .f64)

theorem p_special_trig_561_proven : P_special_trig_561 := by simp [P_special_trig_561, HasResult]

/-- `ATAN2_RATIO_THRESHOLD(::Type{Float64})` at `base/special/trig.jl:562-562`. -/
def P_special_trig_562 : Prop := ∀ _u : Unit, HasResult (Trig.atan2Threshold .f64)

theorem p_special_trig_562_proven : P_special_trig_562 := by simp [P_special_trig_562, HasResult]

/-- `atan(y::T, x::T) where T<:Union{Float32, Float64}` at `base/special/trig.jl:564-655`. -/
def P_special_trig_564 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ y x : FV T, HasResult (Trig.atan2 T y x)

theorem p_special_trig_564_proven : P_special_trig_564 := by simp [P_special_trig_564, HasResult]

/-- `ACOS_X_MIN_THRESHOLD(::Type{Float32})` at `base/special/trig.jl:657-657`. -/
def P_special_trig_657 : Prop := ∀ _u : Unit, HasResult (Trig.acosMin .f32)

theorem p_special_trig_657_proven : P_special_trig_657 := by simp [P_special_trig_657, HasResult]

/-- `ACOS_X_MIN_THRESHOLD(::Type{Float64})` at `base/special/trig.jl:658-658`. -/
def P_special_trig_658 : Prop := ∀ _u : Unit, HasResult (Trig.acosMin .f64)

theorem p_special_trig_658_proven : P_special_trig_658 := by simp [P_special_trig_658, HasResult]

/-- `PIO2_HI(::Type{Float32})` at `base/special/trig.jl:659-659`. -/
def P_special_trig_659 : Prop := ∀ _u : Unit, HasResult (Trig.pio2Hi .f32)

theorem p_special_trig_659_proven : P_special_trig_659 := by simp [P_special_trig_659, HasResult]

/-- `PIO2_LO(::Type{Float32})` at `base/special/trig.jl:660-660`. -/
def P_special_trig_660 : Prop := ∀ _u : Unit, HasResult (Trig.pio2Lo .f32)

theorem p_special_trig_660_proven : P_special_trig_660 := by simp [P_special_trig_660, HasResult]

/-- `PIO2_HI(::Type{Float64})` at `base/special/trig.jl:661-661`. -/
def P_special_trig_661 : Prop := ∀ _u : Unit, HasResult (Trig.pio2Hi .f64)

theorem p_special_trig_661_proven : P_special_trig_661 := by simp [P_special_trig_661, HasResult]

/-- `PIO2_LO(::Type{Float64})` at `base/special/trig.jl:662-662`. -/
def P_special_trig_662 : Prop := ∀ _u : Unit, HasResult (Trig.pio2Lo .f64)

theorem p_special_trig_662_proven : P_special_trig_662 := by simp [P_special_trig_662, HasResult]

/-- `ACOS_PI(::Type{Float32})` at `base/special/trig.jl:663-663`. -/
def P_special_trig_663 : Prop := ∀ _u : Unit, HasResult (Trig.acosPi .f32)

theorem p_special_trig_663_proven : P_special_trig_663 := by simp [P_special_trig_663, HasResult]

/-- `ACOS_PI(::Type{Float64})` at `base/special/trig.jl:664-664`. -/
def P_special_trig_664 : Prop := ∀ _u : Unit, HasResult (Trig.acosPi .f64)

theorem p_special_trig_664_proven : P_special_trig_664 := by simp [P_special_trig_664, HasResult]

/-- `ACOS_CORRECT_LOWWORD(::Type{Float32}, x)` at `base/special/trig.jl:665-665`. -/
def P_special_trig_665 : Prop := ∀ x : FV .f32, HasResult (Trig.acosLowword x)

theorem p_special_trig_665_proven : P_special_trig_665 := by simp [P_special_trig_665, HasResult]

/-- `ACOS_CORRECT_LOWWORD(::Type{Float64}, x)` at `base/special/trig.jl:666-666`. -/
def P_special_trig_666 : Prop := ∀ x : FV .f64, HasResult (Trig.acosLowword x)

theorem p_special_trig_666_proven : P_special_trig_666 := by simp [P_special_trig_666, HasResult]

/-- `acos_domain_error(x)` at `base/special/trig.jl:668-668`. -/
def P_special_trig_668 : Prop := ∀ x : FV .f64, HasResult (Trig.acosDomainError (α := FV .f64))

theorem p_special_trig_668_proven : P_special_trig_668 := by simp [P_special_trig_668, HasResult]

/-- `acos(x::T) where T <: Union{Float32, Float64}` at `base/special/trig.jl:669-722`. -/
def P_special_trig_669 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (Trig.acos T x)

theorem p_special_trig_669_proven : P_special_trig_669 := by simp [P_special_trig_669, HasResult]

/-- `sinpi_kernel(x::Float64)` at `base/special/trig.jl:725-727`. -/
def P_special_trig_725 : Prop := ∀ x : FV .f64, HasResult (TrigPi.sinpiKernel .f64 x)

theorem p_special_trig_725_proven : P_special_trig_725 := by simp [P_special_trig_725, HasResult]

/-- `sinpi_kernel_wide(x::Float64)` at `base/special/trig.jl:728-730`. -/
def P_special_trig_728 : Prop := ∀ x : FV .f64, HasResult (TrigPi.sinpiKernelWide .f64 x)

theorem p_special_trig_728_proven : P_special_trig_728 := by simp [P_special_trig_728, HasResult]

/-- `sinpi_kernel(x::Float32)` at `base/special/trig.jl:731-733`. -/
def P_special_trig_731 : Prop := ∀ x : FV .f32, HasResult (TrigPi.sinpiKernel .f32 x)

theorem p_special_trig_731_proven : P_special_trig_731 := by simp [P_special_trig_731, HasResult]

/-- `sinpi_kernel_wide(x::Float32)` at `base/special/trig.jl:734-738`. -/
def P_special_trig_734 : Prop := ∀ x : FV .f32, HasResult (TrigPi.sinpiKernelWide .f32 x)

theorem p_special_trig_734_proven : P_special_trig_734 := by simp [P_special_trig_734, HasResult]

/-- `sinpi_kernel(x::Float16)` at `base/special/trig.jl:740-742`. -/
def P_special_trig_740 : Prop := ∀ x : FV .f16, HasResult (TrigPi.sinpiKernel .f16 x)

theorem p_special_trig_740_proven : P_special_trig_740 := by simp [P_special_trig_740, HasResult]

/-- `sinpi_kernel_wide(x::Float16)` at `base/special/trig.jl:743-746`. -/
def P_special_trig_743 : Prop := ∀ x : FV .f16, HasResult (TrigPi.sinpiKernelWide .f16 x)

theorem p_special_trig_743_proven : P_special_trig_743 := by simp [P_special_trig_743, HasResult]

/-- `cospi_kernel(x::Float64)` at `base/special/trig.jl:749-751`. -/
def P_special_trig_749 : Prop := ∀ x : FV .f64, HasResult (TrigPi.cospiKernel .f64 x)

theorem p_special_trig_749_proven : P_special_trig_749 := by simp [P_special_trig_749, HasResult]

/-- `cospi_kernel_wide(x::Float64)` at `base/special/trig.jl:752-754`. -/
def P_special_trig_752 : Prop := ∀ x : FV .f64, HasResult (TrigPi.cospiKernelWide .f64 x)

theorem p_special_trig_752_proven : P_special_trig_752 := by simp [P_special_trig_752, HasResult]

/-- `cospi_kernel(x::Float32)` at `base/special/trig.jl:755-757`. -/
def P_special_trig_755 : Prop := ∀ x : FV .f32, HasResult (TrigPi.cospiKernel .f32 x)

theorem p_special_trig_755_proven : P_special_trig_755 := by simp [P_special_trig_755, HasResult]

/-- `cospi_kernel_wide(x::Float32)` at `base/special/trig.jl:758-762`. -/
def P_special_trig_758 : Prop := ∀ x : FV .f32, HasResult (TrigPi.cospiKernelWide .f32 x)

theorem p_special_trig_758_proven : P_special_trig_758 := by simp [P_special_trig_758, HasResult]

/-- `cospi_kernel(x::Float16)` at `base/special/trig.jl:763-765`. -/
def P_special_trig_763 : Prop := ∀ x : FV .f16, HasResult (TrigPi.cospiKernel .f16 x)

theorem p_special_trig_763_proven : P_special_trig_763 := by simp [P_special_trig_763, HasResult]

/-- `cospi_kernel_wide(x::Float16)` at `base/special/trig.jl:766-769`. -/
def P_special_trig_766 : Prop := ∀ x : FV .f16, HasResult (TrigPi.cospiKernelWide .f16 x)

theorem p_special_trig_766_proven : P_special_trig_766 := by simp [P_special_trig_766, HasResult]

/-- `_cospi_kernel(x::AbstractFloat, sch)` at `base/special/trig.jl:771-783`. -/
def P_special_trig_771 : Prop := ∀ T : FTy, ∀ (x : FV T) (sch : List (FV T)), HasResult (TrigPi.cospiKernelSch sch x)

theorem p_special_trig_771_proven : P_special_trig_771 := by simp [P_special_trig_771, HasResult]

/-- `_sinpi_kernel(x::AbstractFloat, sch)` at `base/special/trig.jl:785-795`. -/
def P_special_trig_785 : Prop := ∀ T : FTy, ∀ (x : FV T) (sch : List (FV T)), HasResult (TrigPi.sinpiKernelSch sch x)

theorem p_special_trig_785_proven : P_special_trig_785 := by simp [P_special_trig_785, HasResult]

/-- `sinpi(_x::T) where T<:IEEEFloat` at `base/special/trig.jl:934-957`. -/
def P_special_trig_934 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigPi.sinpi T x)

theorem p_special_trig_934_proven : P_special_trig_934 := by simp [P_special_trig_934, HasResult]

/-- `cospi(x::T) where T<:IEEEFloat` at `base/special/trig.jl:968-990`. -/
def P_special_trig_968 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigPi.cospi T x)

theorem p_special_trig_968_proven : P_special_trig_968 := by simp [P_special_trig_968, HasResult]

/-- `sincospi(_x::T) where T<:IEEEFloat` at `base/special/trig.jl:1005-1030`. -/
def P_special_trig_1005 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigPi.sincospi T x)

theorem p_special_trig_1005_proven : P_special_trig_1005 := by simp [P_special_trig_1005, HasResult]

/-- `tanpi(_x::T) where T<:IEEEFloat` at `base/special/trig.jl:1044-1072`. -/
def P_special_trig_1044 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigPi.tanpi T x)

theorem p_special_trig_1044_proven : P_special_trig_1044 := by simp [P_special_trig_1044, HasResult]

/-- `sinpi(x::Integer)` at `base/special/trig.jl:1074-1074`. -/
def P_special_trig_1074 : Prop := ∀ x : Int, HasResult (TrigPi.sinpiInt x)

theorem p_special_trig_1074_proven : P_special_trig_1074 := by simp [P_special_trig_1074, HasResult]

/-- `cospi(x::Integer)` at `base/special/trig.jl:1075-1075`. -/
def P_special_trig_1075 : Prop := ∀ x : Int, HasResult (TrigPi.cospiInt x)

theorem p_special_trig_1075_proven : P_special_trig_1075 := by simp [P_special_trig_1075, HasResult]

/-- `tanpi(x::Integer)` at `base/special/trig.jl:1076-1077`. -/
def P_special_trig_1076 : Prop := ∀ x : Int, HasResult (TrigPi.tanpiInt x)

theorem p_special_trig_1076_proven : P_special_trig_1076 := by simp [P_special_trig_1076, HasResult]

/-- `sincospi(x::Integer)` at `base/special/trig.jl:1078-1078`. -/
def P_special_trig_1078 : Prop := ∀ x : Int, HasResult (TrigPi.sincospiInt x)

theorem p_special_trig_1078_proven : P_special_trig_1078 := by simp [P_special_trig_1078, HasResult]

/-- `sinpi(x::AbstractFloat)` at `base/special/trig.jl:1079-1079`. -/
def P_special_trig_1079 : Prop := ∀ (α β : Type) (p : α → α) (f : α → β) (x : α), HasResult (TrigPi.piGeneric p f x)

theorem p_special_trig_1079_proven : P_special_trig_1079 := by simp [P_special_trig_1079, HasResult]

/-- `cospi(x::AbstractFloat)` at `base/special/trig.jl:1080-1080`. -/
def P_special_trig_1080 : Prop := ∀ (α β : Type) (p : α → α) (f : α → β) (x : α), HasResult (TrigPi.piGeneric p f x)

theorem p_special_trig_1080_proven : P_special_trig_1080 := by simp [P_special_trig_1080, HasResult]

/-- `sincospi(x::AbstractFloat)` at `base/special/trig.jl:1081-1081`. -/
def P_special_trig_1081 : Prop := ∀ (α β : Type) (p : α → α) (f : α → β) (x : α), HasResult (TrigPi.piGeneric p f x)

theorem p_special_trig_1081_proven : P_special_trig_1081 := by simp [P_special_trig_1081, HasResult]

/-- `tanpi(x::AbstractFloat)` at `base/special/trig.jl:1082-1082`. -/
def P_special_trig_1082 : Prop := ∀ (α β : Type) (p : α → α) (f : α → β) (x : α), HasResult (TrigPi.piGeneric p f x)

theorem p_special_trig_1082_proven : P_special_trig_1082 := by simp [P_special_trig_1082, HasResult]

/-- `tanpi(z::Complex)` at `base/special/trig.jl:1084-1091`. -/
def P_special_trig_1084 : Prop := ∀ T : FTy, ∀ (h : TrigPi.Hyp T) (z : TrigPi.Cx T), HasResult (TrigPi.tanpiC h z)

theorem p_special_trig_1084_proven : P_special_trig_1084 := by simp [P_special_trig_1084, HasResult]

/-- `sinpi(z::Complex{T}) where T` at `base/special/trig.jl:1093-1124`. -/
def P_special_trig_1093 : Prop := ∀ T : FTy, ∀ (h : TrigPi.Hyp T) (z : TrigPi.Cx T), HasResult (TrigPi.sinpiC h z)

theorem p_special_trig_1093_proven : P_special_trig_1093 := by simp [P_special_trig_1093, HasResult]

/-- `cospi(z::Complex{T}) where T` at `base/special/trig.jl:1126-1160`. -/
def P_special_trig_1126 : Prop := ∀ T : FTy, ∀ (h : TrigPi.Hyp T) (z : TrigPi.Cx T), HasResult (TrigPi.cospiC h z)

theorem p_special_trig_1126_proven : P_special_trig_1126 := by simp [P_special_trig_1126, HasResult]

/-- `sincospi(z::Complex{T}) where T` at `base/special/trig.jl:1162-1207`. -/
def P_special_trig_1162 : Prop := ∀ T : FTy, ∀ (h : TrigPi.Hyp T) (z : TrigPi.Cx T), HasResult (TrigPi.sincospiC h z)

theorem p_special_trig_1162_proven : P_special_trig_1162 := by simp [P_special_trig_1162, HasResult]

/-- `fastabs(x::Number)` at `base/special/trig.jl:1217-1217`. -/
def P_special_trig_1217 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.fastabs x)

theorem p_special_trig_1217_proven : P_special_trig_1217 := by simp [P_special_trig_1217, HasResult]

/-- `fastabs(z::Complex)` at `base/special/trig.jl:1218-1218`. -/
def P_special_trig_1218 : Prop := ∀ T : FTy, ∀ z : TrigPi.Cx T, HasResult (TrigMisc.fastabsC z)

theorem p_special_trig_1218_proven : P_special_trig_1218 := by simp [P_special_trig_1218, HasResult]

/-- `isinf_real(x::Real)` at `base/special/trig.jl:1221-1221`. -/
def P_special_trig_1221 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.isinfReal x)

theorem p_special_trig_1221_proven : P_special_trig_1221 := by simp [P_special_trig_1221, HasResult]

/-- `isinf_real(x::Complex)` at `base/special/trig.jl:1222-1222`. -/
def P_special_trig_1222 : Prop := ∀ T : FTy, ∀ z : TrigPi.Cx T, HasResult (TrigMisc.isinfRealC z)

theorem p_special_trig_1222_proven : P_special_trig_1222 := by simp [P_special_trig_1222, HasResult]

/-- `isinf_real(x::Number)` at `base/special/trig.jl:1223-1223`. -/
def P_special_trig_1223 : Prop := ∀ (α : Type) (x : α), HasResult (TrigMisc.isinfRealNumber x)

theorem p_special_trig_1223_proven : P_special_trig_1223 := by simp [P_special_trig_1223, HasResult]

/-- `sinc(x::Number)` at `base/special/trig.jl:1234-1234`. -/
def P_special_trig_1234 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.sinc T x)

theorem p_special_trig_1234_proven : P_special_trig_1234 := by simp [P_special_trig_1234, HasResult]

/-- `sinc(x::Integer)` at `base/special/trig.jl:1235-1235`. -/
def P_special_trig_1235 : Prop := ∀ x : Int, HasResult (TrigMisc.sincInt x)

theorem p_special_trig_1235_proven : P_special_trig_1235 := by simp [P_special_trig_1235, HasResult]

/-- `_sinc(x::Number)` at `base/special/trig.jl:1236-1236`. -/
def P_special_trig_1236 : Prop := ∀ (α : Type) (iz ii : α → Bool) (one zero sp pm : α → α) (d : α → α → α) (x : α), HasResult (TrigMisc.sincGeneric iz ii one zero sp pm d x)

theorem p_special_trig_1236_proven : P_special_trig_1236 := by simp [P_special_trig_1236, HasResult]

/-- `_sinc_threshold(::Type{Float64})` at `base/special/trig.jl:1237-1237`. -/
def P_special_trig_1237 : Prop := ∀ _u : Unit, HasResult (TrigMisc.sincThreshold .f64)

theorem p_special_trig_1237_proven : P_special_trig_1237 := by simp [P_special_trig_1237, HasResult]

/-- `_sinc_threshold(::Type{Float32})` at `base/special/trig.jl:1238-1238`. -/
def P_special_trig_1238 : Prop := ∀ _u : Unit, HasResult (TrigMisc.sincThreshold .f32)

theorem p_special_trig_1238_proven : P_special_trig_1238 := by simp [P_special_trig_1238, HasResult]

/-- `_sinc(x::Union{T,Complex{T}}) where {T<:Union{Float32,Float64}}` at `base/special/trig.jl:1239-1240`. -/
def P_special_trig_1239 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.sincF T x)

theorem p_special_trig_1239_proven : P_special_trig_1239 := by simp [P_special_trig_1239, HasResult]

/-- `_sinc(x::Float16)` at `base/special/trig.jl:1241-1241`. -/
def P_special_trig_1241 : Prop := ∀ x : FV .f16, HasResult (TrigMisc.sinc16 x)

theorem p_special_trig_1241_proven : P_special_trig_1241 := by simp [P_special_trig_1241, HasResult]

/-- `_sinc(x::ComplexF16)` at `base/special/trig.jl:1242-1242`. -/
def P_special_trig_1242 : Prop := ∀ (α β : Type) (c32 : α → β) (c16 : β → α) (f : β → β) (x : α), HasResult (TrigMisc.sincComplex16 c32 c16 f x)

theorem p_special_trig_1242_proven : P_special_trig_1242 := by simp [P_special_trig_1242, HasResult]

/-- `cosc(x::Number)` at `base/special/trig.jl:1254-1254`. -/
def P_special_trig_1254 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.cosc T x)

theorem p_special_trig_1254_proven : P_special_trig_1254 := by simp [P_special_trig_1254, HasResult]

/-- `_cosc_generic(x)` at `base/special/trig.jl:1255-1258`. -/
def P_special_trig_1255 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.coscGeneric T x)

theorem p_special_trig_1255_proven : P_special_trig_1255 := by simp [P_special_trig_1255, HasResult]

/-- `_cosc(x::Number)` at `base/special/trig.jl:1259-1281`. -/
def P_special_trig_1259 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.cosc T x)

theorem p_special_trig_1259_proven : P_special_trig_1259 := by simp [P_special_trig_1259, HasResult]

/-- `_cos_cardinal_eval(x::AbstractFloat, polynomials_close_to_origin::NTuple)` at `base/special/trig.jl:1333-1366`. -/
def P_special_trig_1333 : Prop := ∀ T : FTy, ∀ (x : FV T) (ps : List (FV T × List (FV T))), HasResult (TrigMisc.cosCardinalEval T x ps)

theorem p_special_trig_1333_proven : P_special_trig_1333 := by simp [P_special_trig_1333, HasResult]

/-- `choose_poly(a::AbstractFloat, polynomials_close_to_origin::NTuple{2})` at `base/special/trig.jl:1334-1341`. -/
def P_special_trig_1334 : Prop := ∀ T : FTy, ∀ (a : FV T) (ps : List (FV T × List (FV T))), HasResult (TrigMisc.choosePoly a ps)

theorem p_special_trig_1334_proven : P_special_trig_1334 := by simp [P_special_trig_1334, HasResult]

/-- `choose_poly(a::AbstractFloat, polynomials_close_to_origin::NTuple{4})` at `base/special/trig.jl:1342-1357`. -/
def P_special_trig_1342 : Prop := ∀ T : FTy, ∀ (a : FV T) (ps : List (FV T × List (FV T))), HasResult (TrigMisc.choosePoly a ps)

theorem p_special_trig_1342_proven : P_special_trig_1342 := by simp [P_special_trig_1342, HasResult]

/-- `_cosc(x::Union{Float32, Float64})` at `base/special/trig.jl:1384-1391`. -/
def P_special_trig_1384 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (TrigMisc.coscF T x)

theorem p_special_trig_1384_proven : P_special_trig_1384 := by simp [P_special_trig_1384, HasResult]

/-- `_cosc(x::ComplexF64)` at `base/special/trig.jl:1395-1397`. -/
def P_special_trig_1395 : Prop := ∀ (z : TrigPi.Cx .f64) (q : FV .f64), HasResult (TrigMisc.coscComplex lt TrigMisc.fastabsC q id id id TrigMisc.isinfRealC z)

theorem p_special_trig_1395_proven : P_special_trig_1395 := by simp [P_special_trig_1395, HasResult]

/-- `_cosc(x::ComplexF32)` at `base/special/trig.jl:1398-1400`. -/
def P_special_trig_1398 : Prop := ∀ (z : TrigPi.Cx .f32) (q : FV .f32), HasResult (TrigMisc.coscComplex lt TrigMisc.fastabsC q id id id TrigMisc.isinfRealC z)

theorem p_special_trig_1398_proven : P_special_trig_1398 := by simp [P_special_trig_1398, HasResult]

/-- `_cosc(x::Float16)` at `base/special/trig.jl:1401-1401`. -/
def P_special_trig_1401 : Prop := ∀ x : FV .f16, HasResult (TrigMisc.cosc .f16 x)

theorem p_special_trig_1401_proven : P_special_trig_1401 := by simp [P_special_trig_1401, HasResult]

/-- `_cosc(x::ComplexF16)` at `base/special/trig.jl:1402-1402`. -/
def P_special_trig_1402 : Prop := ∀ (α β : Type) (c32 : α → β) (c16 : β → α) (f : β → β) (x : α), HasResult (TrigMisc.coscComplex16 c32 c16 f x)

theorem p_special_trig_1402_proven : P_special_trig_1402 := by simp [P_special_trig_1402, HasResult]

/-- `($finv)(z::Number)` at `base/special/trig.jl:1417-1417`. -/
def P_special_trig_1417 : Prop := ∀ (α : Type) (f : α → Jl α) (inv : α → α) (x : α), HasResult (TrigMisc.recipOf f inv x)

theorem p_special_trig_1417_proven : P_special_trig_1417 := by simp [P_special_trig_1417, HasResult]

/-- `($finvh)(z::Number)` at `base/special/trig.jl:1424-1424`. -/
def P_special_trig_1424 : Prop := ∀ (α : Type) (f : α → Jl α) (inv : α → α) (x : α), HasResult (TrigMisc.recipOf f inv x)

theorem p_special_trig_1424_proven : P_special_trig_1424 := by simp [P_special_trig_1424, HasResult]

/-- `($finvd)(z::Number)` at `base/special/trig.jl:1431-1431`. -/
def P_special_trig_1431 : Prop := ∀ (α : Type) (f : α → Jl α) (inv : α → α) (x : α), HasResult (TrigMisc.recipOf f inv x)

theorem p_special_trig_1431_proven : P_special_trig_1431 := by simp [P_special_trig_1431, HasResult]

/-- `($tfa)(y::Number)` at `base/special/trig.jl:1445-1445`. -/
def P_special_trig_1445 : Prop := ∀ (α β : Type) (f : α → β) (inv : α → α) (x : α), HasResult (TrigMisc.invArgOf f inv x)

theorem p_special_trig_1445_proven : P_special_trig_1445 := by simp [P_special_trig_1445, HasResult]

/-- `($hfa)(y::Number)` at `base/special/trig.jl:1450-1450`. -/
def P_special_trig_1450 : Prop := ∀ (α β : Type) (f : α → β) (inv : α → α) (x : α), HasResult (TrigMisc.invArgOf f inv x)

theorem p_special_trig_1450_proven : P_special_trig_1450 := by simp [P_special_trig_1450, HasResult]

/-- `deg2rad_ext(x::Float64)` at `base/special/trig.jl:1456-1469`. -/
def P_special_trig_1456 : Prop := ∀ x : FV .f64, HasResult (TrigMisc.deg2radExt64 x)

theorem p_special_trig_1456_proven : P_special_trig_1456 := by simp [P_special_trig_1456, HasResult]

/-- `deg2rad_ext(x::Float32)` at `base/special/trig.jl:1470-1470`. -/
def P_special_trig_1470 : Prop := ∀ x : FV .f32, HasResult (TrigMisc.deg2radExt .f32 x)

theorem p_special_trig_1470_proven : P_special_trig_1470 := by simp [P_special_trig_1470, HasResult]

/-- `deg2rad_ext(x::Real)` at `base/special/trig.jl:1471-1471`. -/
def P_special_trig_1471 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.deg2radExt T x)

theorem p_special_trig_1471_proven : P_special_trig_1471 := by simp [P_special_trig_1471, HasResult]

/-- `sind(x::Real)` at `base/special/trig.jl:1473-1502`. -/
def P_special_trig_1473 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.sind T x)

theorem p_special_trig_1473_proven : P_special_trig_1473 := by simp [P_special_trig_1473, HasResult]

/-- `cosd(x::Real)` at `base/special/trig.jl:1504-1528`. -/
def P_special_trig_1504 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.cosd T x)

theorem p_special_trig_1504_proven : P_special_trig_1504 := by simp [P_special_trig_1504, HasResult]

/-- `tand(x::Real)` at `base/special/trig.jl:1530-1530`. -/
def P_special_trig_1530 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.tand T x)

theorem p_special_trig_1530_proven : P_special_trig_1530 := by simp [P_special_trig_1530, HasResult]

/-- `sincosd(x)` at `base/special/trig.jl:1543-1543`. -/
def P_special_trig_1543 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.sincosd T x)

theorem p_special_trig_1543_proven : P_special_trig_1543 := by simp [P_special_trig_1543, HasResult]

/-- `sincosd(::Missing)` at `base/special/trig.jl:1547-1547`. -/
def P_special_trig_1547 : Prop := ∀ _u : Unit, HasResult (TrigMisc.sincosdMissing)

theorem p_special_trig_1547_proven : P_special_trig_1547 := by simp [P_special_trig_1547, HasResult]

/-- `($fd)(x)` at `base/special/trig.jl:1563-1563`. -/
def P_special_trig_1563 : Prop := ∀ (α β : Type) (f : α → β) (g : α → α) (x : α), HasResult (TrigMisc.viaDeg2rad f g x)

theorem p_special_trig_1563_proven : P_special_trig_1563 := by simp [P_special_trig_1563, HasResult]

/-- `($fd)(x)` at `base/special/trig.jl:1582-1582`. -/
def P_special_trig_1582 : Prop := ∀ (α β : Type) (f : α → Jl β) (g : β → β) (x : α), HasResult (TrigMisc.viaRad2deg f g x)

theorem p_special_trig_1582_proven : P_special_trig_1582 := by simp [P_special_trig_1582, HasResult]

/-- `atand(y)` at `base/special/trig.jl:1600-1600`. -/
def P_special_trig_1600 : Prop := ∀ (α β : Type) (f : α → Jl β) (g : β → β) (x : α), HasResult (TrigMisc.viaRad2deg f g x)

theorem p_special_trig_1600_proven : P_special_trig_1600 := by simp [P_special_trig_1600, HasResult]

/-- `atand(y, x)` at `base/special/trig.jl:1601-1601`. -/
def P_special_trig_1601 : Prop := ∀ (α β : Type) (f : α → Jl β) (g : β → β) (x : α), HasResult (TrigMisc.viaRad2deg f g x)

theorem p_special_trig_1601_proven : P_special_trig_1601 := by simp [P_special_trig_1601, HasResult]

/-- `$f(x::Float16)` at `base/special/trig.jl:1605-1605`. -/
def P_special_trig_1605 : Prop := ∀ (f : FV .f32 → Jl (FV .f32)) (x : FV .f16), HasResult (TrigMisc.degF16 f "f" x)

theorem p_special_trig_1605_proven : P_special_trig_1605 := by simp [P_special_trig_1605, HasResult]

/-- `$f(x::Float16)` at `base/special/trig.jl:1608-1608`. -/
def P_special_trig_1608 : Prop := ∀ (f : FV .f32 → Jl (FV .f32)) (x : FV .f16), HasResult (TrigMisc.invDegF16 f x)

theorem p_special_trig_1608_proven : P_special_trig_1608 := by simp [P_special_trig_1608, HasResult]

/-- `atand(y::Float16, x::Float16)` at `base/special/trig.jl:1610-1610`. -/
def P_special_trig_1610 : Prop := ∀ (x y : FV .f16), HasResult (MathMisc.atan16 x y)

theorem p_special_trig_1610_proven : P_special_trig_1610 := by simp [P_special_trig_1610, HasResult]

/-- `MAGIC_ROUND_CONST(::Type{Float64})` at `base/special/exp.jl:6-6`. -/
def P_special_exp_6 : Prop := ∀ _u : Unit, HasResult (MathFuncs.magicRoundConst)

theorem p_special_exp_6_proven : P_special_exp_6 := by simp [P_special_exp_6, HasResult]

/-- `MAGIC_ROUND_CONST(::Type{Float32})` at `base/special/exp.jl:7-7`. -/
def P_special_exp_7 : Prop := ∀ _u : Unit, HasResult (magic32)

theorem p_special_exp_7_proven : P_special_exp_7 := by simp [P_special_exp_7, HasResult]

/-- `MAX_EXP(n::Val{2}, ::Type{Float32})` at `base/special/exp.jl:11-11`. -/
def P_special_exp_11 : Prop := ∀ _u : Unit, HasResult (Exp.maxExp32 .two)

theorem p_special_exp_11_proven : P_special_exp_11 := by simp [P_special_exp_11, HasResult]

/-- `MAX_EXP(n::Val{2}, ::Type{Float64})` at `base/special/exp.jl:12-12`. -/
def P_special_exp_12 : Prop := ∀ _u : Unit, HasResult (MathFuncs.maxExp .two)

theorem p_special_exp_12_proven : P_special_exp_12 := by simp [P_special_exp_12, HasResult]

/-- `MAX_EXP(n::Val{:ℯ}, ::Type{Float32})` at `base/special/exp.jl:13-13`. -/
def P_special_exp_13 : Prop := ∀ _u : Unit, HasResult (Exp.maxExp32 .e)

theorem p_special_exp_13_proven : P_special_exp_13 := by simp [P_special_exp_13, HasResult]

/-- `MAX_EXP(n::Val{:ℯ}, ::Type{Float64})` at `base/special/exp.jl:14-14`. -/
def P_special_exp_14 : Prop := ∀ _u : Unit, HasResult (MathFuncs.maxExp .e)

theorem p_special_exp_14_proven : P_special_exp_14 := by simp [P_special_exp_14, HasResult]

/-- `MAX_EXP(n::Val{10}, ::Type{Float32})` at `base/special/exp.jl:15-15`. -/
def P_special_exp_15 : Prop := ∀ _u : Unit, HasResult (Exp.maxExp32 .ten)

theorem p_special_exp_15_proven : P_special_exp_15 := by simp [P_special_exp_15, HasResult]

/-- `MAX_EXP(n::Val{10}, ::Type{Float64})` at `base/special/exp.jl:16-16`. -/
def P_special_exp_16 : Prop := ∀ _u : Unit, HasResult (MathFuncs.maxExp .ten)

theorem p_special_exp_16_proven : P_special_exp_16 := by simp [P_special_exp_16, HasResult]

/-- `MIN_EXP(n::Val{2}, ::Type{Float32})` at `base/special/exp.jl:19-19`. -/
def P_special_exp_19 : Prop := ∀ _u : Unit, HasResult (Exp.minExp32 .two)

theorem p_special_exp_19_proven : P_special_exp_19 := by simp [P_special_exp_19, HasResult]

/-- `MIN_EXP(n::Val{2}, ::Type{Float64})` at `base/special/exp.jl:20-20`. -/
def P_special_exp_20 : Prop := ∀ _u : Unit, HasResult (MathFuncs.minExp .two)

theorem p_special_exp_20_proven : P_special_exp_20 := by simp [P_special_exp_20, HasResult]

/-- `MIN_EXP(n::Val{:ℯ}, ::Type{Float32})` at `base/special/exp.jl:21-21`. -/
def P_special_exp_21 : Prop := ∀ _u : Unit, HasResult (Exp.minExp32 .e)

theorem p_special_exp_21_proven : P_special_exp_21 := by simp [P_special_exp_21, HasResult]

/-- `MIN_EXP(n::Val{:ℯ}, ::Type{Float64})` at `base/special/exp.jl:22-22`. -/
def P_special_exp_22 : Prop := ∀ _u : Unit, HasResult (MathFuncs.minExp .e)

theorem p_special_exp_22_proven : P_special_exp_22 := by simp [P_special_exp_22, HasResult]

/-- `MIN_EXP(n::Val{10}, ::Type{Float32})` at `base/special/exp.jl:23-23`. -/
def P_special_exp_23 : Prop := ∀ _u : Unit, HasResult (Exp.minExp32 .ten)

theorem p_special_exp_23_proven : P_special_exp_23 := by simp [P_special_exp_23, HasResult]

/-- `MIN_EXP(n::Val{10}, ::Type{Float64})` at `base/special/exp.jl:24-24`. -/
def P_special_exp_24 : Prop := ∀ _u : Unit, HasResult (MathFuncs.minExp .ten)

theorem p_special_exp_24_proven : P_special_exp_24 := by simp [P_special_exp_24, HasResult]

/-- `SUBNORM_EXP(n::Val{2}, ::Type{Float32})` at `base/special/exp.jl:28-28`. -/
def P_special_exp_28 : Prop := ∀ _u : Unit, HasResult (Exp.subnormExp32 .two)

theorem p_special_exp_28_proven : P_special_exp_28 := by simp [P_special_exp_28, HasResult]

/-- `SUBNORM_EXP(n::Val{2}, ::Type{Float64})` at `base/special/exp.jl:29-29`. -/
def P_special_exp_29 : Prop := ∀ _u : Unit, HasResult (MathFuncs.subnormExp .two)

theorem p_special_exp_29_proven : P_special_exp_29 := by simp [P_special_exp_29, HasResult]

/-- `SUBNORM_EXP(n::Val{:ℯ}, ::Type{Float32})` at `base/special/exp.jl:30-30`. -/
def P_special_exp_30 : Prop := ∀ _u : Unit, HasResult (Exp.subnormExp32 .e)

theorem p_special_exp_30_proven : P_special_exp_30 := by simp [P_special_exp_30, HasResult]

/-- `SUBNORM_EXP(n::Val{:ℯ}, ::Type{Float64})` at `base/special/exp.jl:31-31`. -/
def P_special_exp_31 : Prop := ∀ _u : Unit, HasResult (MathFuncs.subnormExp .e)

theorem p_special_exp_31_proven : P_special_exp_31 := by simp [P_special_exp_31, HasResult]

/-- `SUBNORM_EXP(n::Val{10}, ::Type{Float32})` at `base/special/exp.jl:32-32`. -/
def P_special_exp_32 : Prop := ∀ _u : Unit, HasResult (Exp.subnormExp32 .ten)

theorem p_special_exp_32_proven : P_special_exp_32 := by simp [P_special_exp_32, HasResult]

/-- `SUBNORM_EXP(n::Val{10}, ::Type{Float64})` at `base/special/exp.jl:33-33`. -/
def P_special_exp_33 : Prop := ∀ _u : Unit, HasResult (MathFuncs.subnormExp .ten)

theorem p_special_exp_33_proven : P_special_exp_33 := by simp [P_special_exp_33, HasResult]

/-- `LogBo256INV(::Val{2}, ::Type{Float64})` at `base/special/exp.jl:36-36`. -/
def P_special_exp_36 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logBo256Inv .two)

theorem p_special_exp_36_proven : P_special_exp_36 := by simp [P_special_exp_36, HasResult]

/-- `LogBo256INV(::Val{:ℯ}, ::Type{Float64})` at `base/special/exp.jl:37-37`. -/
def P_special_exp_37 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logBo256Inv .e)

theorem p_special_exp_37_proven : P_special_exp_37 := by simp [P_special_exp_37, HasResult]

/-- `LogBo256INV(::Val{10}, ::Type{Float64})` at `base/special/exp.jl:38-38`. -/
def P_special_exp_38 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logBo256Inv .ten)

theorem p_special_exp_38_proven : P_special_exp_38 := by simp [P_special_exp_38, HasResult]

/-- `LogBo256U(::Val{2}, ::Type{Float64})` at `base/special/exp.jl:44-44`. -/
def P_special_exp_44 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logBo256U .two)

theorem p_special_exp_44_proven : P_special_exp_44 := by simp [P_special_exp_44, HasResult]

/-- `LogBo256U(::Val{:ℯ}, ::Type{Float64})` at `base/special/exp.jl:45-45`. -/
def P_special_exp_45 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logBo256U .e)

theorem p_special_exp_45_proven : P_special_exp_45 := by simp [P_special_exp_45, HasResult]

/-- `LogBo256U(::Val{10}, ::Type{Float64})` at `base/special/exp.jl:46-46`. -/
def P_special_exp_46 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logBo256U .ten)

theorem p_special_exp_46_proven : P_special_exp_46 := by simp [P_special_exp_46, HasResult]

/-- `LogBo256L(::Val{2}, ::Type{Float64})` at `base/special/exp.jl:47-47`. -/
def P_special_exp_47 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logBo256L .two)

theorem p_special_exp_47_proven : P_special_exp_47 := by simp [P_special_exp_47, HasResult]

/-- `LogBo256L(::Val{:ℯ}, ::Type{Float64})` at `base/special/exp.jl:48-48`. -/
def P_special_exp_48 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logBo256L .e)

theorem p_special_exp_48_proven : P_special_exp_48 := by simp [P_special_exp_48, HasResult]

/-- `LogBo256L(::Val{10}, ::Type{Float64})` at `base/special/exp.jl:49-49`. -/
def P_special_exp_49 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logBo256L .ten)

theorem p_special_exp_49_proven : P_special_exp_49 := by simp [P_special_exp_49, HasResult]

/-- `LogBINV(::Val{2}, ::Type{Float32})` at `base/special/exp.jl:52-52`. -/
def P_special_exp_52 : Prop := ∀ _u : Unit, HasResult (Exp.logBInv32 .two)

theorem p_special_exp_52_proven : P_special_exp_52 := by simp [P_special_exp_52, HasResult]

/-- `LogBINV(::Val{:ℯ}, ::Type{Float32})` at `base/special/exp.jl:53-53`. -/
def P_special_exp_53 : Prop := ∀ _u : Unit, HasResult (Exp.logBInv32 .e)

theorem p_special_exp_53_proven : P_special_exp_53 := by simp [P_special_exp_53, HasResult]

/-- `LogBINV(::Val{10}, ::Type{Float32})` at `base/special/exp.jl:54-54`. -/
def P_special_exp_54 : Prop := ∀ _u : Unit, HasResult (Exp.logBInv32 .ten)

theorem p_special_exp_54_proven : P_special_exp_54 := by simp [P_special_exp_54, HasResult]

/-- `LogBU(::Val{2}, ::Type{Float32})` at `base/special/exp.jl:60-60`. -/
def P_special_exp_60 : Prop := ∀ _u : Unit, HasResult (Exp.logBU32 .two)

theorem p_special_exp_60_proven : P_special_exp_60 := by simp [P_special_exp_60, HasResult]

/-- `LogBU(::Val{:ℯ}, ::Type{Float32})` at `base/special/exp.jl:61-61`. -/
def P_special_exp_61 : Prop := ∀ _u : Unit, HasResult (Exp.logBU32 .e)

theorem p_special_exp_61_proven : P_special_exp_61 := by simp [P_special_exp_61, HasResult]

/-- `LogBU(::Val{10}, ::Type{Float32})` at `base/special/exp.jl:62-62`. -/
def P_special_exp_62 : Prop := ∀ _u : Unit, HasResult (Exp.logBU32 .ten)

theorem p_special_exp_62_proven : P_special_exp_62 := by simp [P_special_exp_62, HasResult]

/-- `LogBL(::Val{2}, ::Type{Float32})` at `base/special/exp.jl:63-63`. -/
def P_special_exp_63 : Prop := ∀ _u : Unit, HasResult (Exp.logBL32 .two)

theorem p_special_exp_63_proven : P_special_exp_63 := by simp [P_special_exp_63, HasResult]

/-- `LogBL(::Val{:ℯ}, ::Type{Float32})` at `base/special/exp.jl:64-64`. -/
def P_special_exp_64 : Prop := ∀ _u : Unit, HasResult (Exp.logBL32 .e)

theorem p_special_exp_64_proven : P_special_exp_64 := by simp [P_special_exp_64, HasResult]

/-- `LogBL(::Val{10}, ::Type{Float32})` at `base/special/exp.jl:65-65`. -/
def P_special_exp_65 : Prop := ∀ _u : Unit, HasResult (Exp.logBL32 .ten)

theorem p_special_exp_65_proven : P_special_exp_65 := by simp [P_special_exp_65, HasResult]

/-- `LogB(::Val{2}, ::Type{Float16})` at `base/special/exp.jl:68-68`. -/
def P_special_exp_68 : Prop := ∀ _u : Unit, HasResult (Exp.logB16 .two)

theorem p_special_exp_68_proven : P_special_exp_68 := by simp [P_special_exp_68, HasResult]

/-- `LogB(::Val{:ℯ}, ::Type{Float16})` at `base/special/exp.jl:69-69`. -/
def P_special_exp_69 : Prop := ∀ _u : Unit, HasResult (Exp.logB16 .e)

theorem p_special_exp_69_proven : P_special_exp_69 := by simp [P_special_exp_69, HasResult]

/-- `LogB(::Val{10}, ::Type{Float16})` at `base/special/exp.jl:70-70`. -/
def P_special_exp_70 : Prop := ∀ _u : Unit, HasResult (Exp.logB16 .ten)

theorem p_special_exp_70_proven : P_special_exp_70 := by simp [P_special_exp_70, HasResult]

/-- `expm1b_kernel(::Val{2}, x::Float64)` at `base/special/exp.jl:73-76`. -/
def P_special_exp_73 : Prop := ∀ x : F64, HasResult (MathFuncs.expm1bKernel .two x)

theorem p_special_exp_73_proven : P_special_exp_73 := by simp [P_special_exp_73, HasResult]

/-- `expm1b_kernel(::Val{:ℯ}, x::Float64)` at `base/special/exp.jl:77-80`. -/
def P_special_exp_77 : Prop := ∀ x : F64, HasResult (MathFuncs.expm1bKernel .e x)

theorem p_special_exp_77_proven : P_special_exp_77 := by simp [P_special_exp_77, HasResult]

/-- `expm1b_kernel(::Val{10}, x::Float64)` at `base/special/exp.jl:81-84`. -/
def P_special_exp_81 : Prop := ∀ x : F64, HasResult (MathFuncs.expm1bKernel .ten x)

theorem p_special_exp_81_proven : P_special_exp_81 := by simp [P_special_exp_81, HasResult]

/-- `expb_kernel(::Val{2}, x::Float32)` at `base/special/exp.jl:86-90`. -/
def P_special_exp_86 : Prop := ∀ x : FV .f32, HasResult (Exp.expbKernel .two x)

theorem p_special_exp_86_proven : P_special_exp_86 := by simp [P_special_exp_86, HasResult]

/-- `expb_kernel(::Val{:ℯ}, x::Float32)` at `base/special/exp.jl:91-95`. -/
def P_special_exp_91 : Prop := ∀ x : FV .f32, HasResult (Exp.expbKernel .e x)

theorem p_special_exp_91_proven : P_special_exp_91 := by simp [P_special_exp_91, HasResult]

/-- `expb_kernel(::Val{10}, x::Float32)` at `base/special/exp.jl:96-100`. -/
def P_special_exp_96 : Prop := ∀ x : FV .f32, HasResult (Exp.expbKernel .ten x)

theorem p_special_exp_96_proven : P_special_exp_96 := by simp [P_special_exp_96, HasResult]

/-- `table_unpack(ind::Int32)` at `base/special/exp.jl:178-184`. -/
def P_special_exp_178 : Prop := ∀ i : Int, HasResult (MathFuncs.tableUnpack i)

theorem p_special_exp_178_proven : P_special_exp_178 := by simp [P_special_exp_178, HasResult]

/-- `exp_impl(x::Float64, base)` at `base/special/exp.jl:207-231`. -/
def P_special_exp_207 : Prop := ∀ (x : F64) (b : ExpBase), HasResult (MathFuncs.expImpl x b)

theorem p_special_exp_207_proven : P_special_exp_207 := by simp [P_special_exp_207, HasResult]

/-- `exp_impl(x::Float64, xlo::Float64, base)` at `base/special/exp.jl:233-259`. -/
def P_special_exp_233 : Prop := ∀ (x lo : F64) (b : ExpBase), HasResult (MathFuncs.expImplLo x lo b)

theorem p_special_exp_233_proven : P_special_exp_233 := by simp [P_special_exp_233, HasResult]

/-- `exp_impl_fast(x::Float64, base)` at `base/special/exp.jl:260-274`. -/
def P_special_exp_260 : Prop := ∀ (x : F64) (b : ExpBase), HasResult (Exp.expImplFast64 x b)

theorem p_special_exp_260_proven : P_special_exp_260 := by simp [P_special_exp_260, HasResult]

/-- `exp_impl(x::Float32, base)` at `base/special/exp.jl:276-295`. -/
def P_special_exp_276 : Prop := ∀ (x : FV .f32) (b : ExpBase), HasResult (Exp.expImpl32 x b)

theorem p_special_exp_276_proven : P_special_exp_276 := by simp [P_special_exp_276, HasResult]

/-- `exp_impl_fast(x::Float32, base)` at `base/special/exp.jl:297-308`. -/
def P_special_exp_297 : Prop := ∀ (x : FV .f32) (b : ExpBase), HasResult (Exp.expImplFast32 x b)

theorem p_special_exp_297_proven : P_special_exp_297 := by simp [P_special_exp_297, HasResult]

/-- `exp_impl(a::Float16, base)` at `base/special/exp.jl:310-323`. -/
def P_special_exp_310 : Prop := ∀ (x : FV .f16) (b : ExpBase), HasResult (Exp.expImpl16 x b)

theorem p_special_exp_310_proven : P_special_exp_310 := by simp [P_special_exp_310, HasResult]

/-- `$func(x::Union{Float16,Float32,Float64})` at `base/special/exp.jl:329-329`. -/
def P_special_exp_329 : Prop := ∀ T : FTy, ∀ (x : FV T) (b : ExpBase), HasResult (Exp.expFn b T x)

theorem p_special_exp_329_proven : P_special_exp_329 := by simp [P_special_exp_329, HasResult]

/-- `$fast_func(x::Union{Float32,Float64})` at `base/special/exp.jl:330-330`. -/
def P_special_exp_330 : Prop := ∀ (x : F64) (b : ExpBase), HasResult (Exp.expImplFast64 x b)

theorem p_special_exp_330_proven : P_special_exp_330 := by simp [P_special_exp_330, HasResult]

/-- `MAX_EXP(::Type{Float64})` at `base/special/exp.jl:406-406`. -/
def P_special_exp_406 : Prop := ∀ _u : Unit, HasResult (MathFuncs.expm1MaxExp)

theorem p_special_exp_406_proven : P_special_exp_406 := by simp [P_special_exp_406, HasResult]

/-- `MIN_EXP(::Type{Float64})` at `base/special/exp.jl:407-407`. -/
def P_special_exp_407 : Prop := ∀ _u : Unit, HasResult (MathFuncs.expm1MinExp)

theorem p_special_exp_407_proven : P_special_exp_407 := by simp [P_special_exp_407, HasResult]

/-- `MAX_EXP(::Type{Float32})` at `base/special/exp.jl:408-408`. -/
def P_special_exp_408 : Prop := ∀ _u : Unit, HasResult (expm1Max32)

theorem p_special_exp_408_proven : P_special_exp_408 := by simp [P_special_exp_408, HasResult]

/-- `MIN_EXP(::Type{Float32})` at `base/special/exp.jl:409-409`. -/
def P_special_exp_409 : Prop := ∀ _u : Unit, HasResult (expm1Min32)

theorem p_special_exp_409_proven : P_special_exp_409 := by simp [P_special_exp_409, HasResult]

/-- `MAX_EXP(::Type{Float16})` at `base/special/exp.jl:410-410`. -/
def P_special_exp_410 : Prop := ∀ _u : Unit, HasResult (expm1Max16)

theorem p_special_exp_410_proven : P_special_exp_410 := by simp [P_special_exp_410, HasResult]

/-- `MIN_EXP(::Type{Float16})` at `base/special/exp.jl:411-411`. -/
def P_special_exp_411 : Prop := ∀ _u : Unit, HasResult (expm1Min16)

theorem p_special_exp_411_proven : P_special_exp_411 := by simp [P_special_exp_411, HasResult]

/-- `Ln2INV(::Type{Float64})` at `base/special/exp.jl:413-413`. -/
def P_special_exp_413 : Prop := ∀ _u : Unit, HasResult (ln2Inv64)

theorem p_special_exp_413_proven : P_special_exp_413 := by simp [P_special_exp_413, HasResult]

/-- `Ln2(::Type{Float64})` at `base/special/exp.jl:414-414`. -/
def P_special_exp_414 : Prop := ∀ _u : Unit, HasResult (ln2Neg64)

theorem p_special_exp_414_proven : P_special_exp_414 := by simp [P_special_exp_414, HasResult]

/-- `Ln2INV(::Type{Float32})` at `base/special/exp.jl:415-415`. -/
def P_special_exp_415 : Prop := ∀ _u : Unit, HasResult (ln2Inv32)

theorem p_special_exp_415_proven : P_special_exp_415 := by simp [P_special_exp_415, HasResult]

/-- `Ln2(::Type{Float32})` at `base/special/exp.jl:416-416`. -/
def P_special_exp_416 : Prop := ∀ _u : Unit, HasResult (ln2Neg32)

theorem p_special_exp_416_proven : P_special_exp_416 := by simp [P_special_exp_416, HasResult]

/-- `expm1_small(x::Float64)` at `base/special/exp.jl:419-425`. -/
def P_special_exp_419 : Prop := ∀ x : F64, HasResult (MathFuncs.expm1Small x)

theorem p_special_exp_419_proven : P_special_exp_419 := by simp [P_special_exp_419, HasResult]

/-- `expm1_small(x::Float32)` at `base/special/exp.jl:426-431`. -/
def P_special_exp_426 : Prop := ∀ x : FV .f32, HasResult (Exp.expm1Small32 x)

theorem p_special_exp_426_proven : P_special_exp_426 := by simp [P_special_exp_426, HasResult]

/-- `expm1(x::Float32)` at `base/special/exp.jl:459-474`. -/
def P_special_exp_459 : Prop := ∀ x : FV .f32, HasResult (Exp.expm1F32 x)

theorem p_special_exp_459_proven : P_special_exp_459 := by simp [P_special_exp_459, HasResult]

/-- `expm1(x::Float16)` at `base/special/exp.jl:476-490`. -/
def P_special_exp_476 : Prop := ∀ x : FV .f16, HasResult (Exp.expm1F16 x)

theorem p_special_exp_476_proven : P_special_exp_476 := by simp [P_special_exp_476, HasResult]

/-- `throw_complex_domainerror(f::Symbol, x)` at `base/math.jl:32-35`. -/
def P_math_32 : Prop := ∀ (T : FTy) (f : String), HasResult (MathMisc.throwComplexDomainError (α := FV T) f)

theorem p_math_32_proven : P_math_32 := by simp [P_math_32, HasResult]

/-- `throw_complex_domainerror_neg1(f::Symbol, x)` at `base/math.jl:36-39`. -/
def P_math_36 : Prop := ∀ (T : FTy) (f : String), HasResult (MathMisc.throwComplexDomainErrorNeg1 (α := FV T) f)

theorem p_math_36_proven : P_math_36 := by simp [P_math_36, HasResult]

/-- `throw_finite_domainerror(f::Symbol, x)` at `base/math.jl:40-42`. -/
def P_math_40 : Prop := ∀ (T : FTy) (f : String), HasResult (MathMisc.throwFiniteDomainError (α := FV T) f)

theorem p_math_40_proven : P_math_40 := by simp [P_math_40, HasResult]

/-- `throw_exp_domainerror(x)` at `base/math.jl:43-48`. -/
def P_math_43 : Prop := ∀ T : FTy, HasResult (MathMisc.throwExpDomainError (α := FV T))

theorem p_math_43_proven : P_math_43 := by simp [P_math_43, HasResult]

/-- `_evalpoly(x, p)` at `base/math.jl:90-98`. -/
def P_math_90 : Prop := ∀ T : FTy, ∀ (x : FV T) (p : List (FV T)), HasResult (MathMisc.evalpolyReal x p)

theorem p_math_90_proven : P_math_90 := by simp [P_math_90, HasResult]

/-- `evalpoly(z::Complex, p::Tuple)` at `base/math.jl:100-124`. -/
def P_math_100 : Prop := ∀ T : FTy, ∀ (z : TrigPi.Cx T) (p : List (FV T)), HasResult (MathMisc.evalpolyComplex z p)

theorem p_math_100_proven : P_math_100 := by simp [P_math_100, HasResult]

/-- `evalpoly(z::Complex, p::Tuple{<:Any})` at `base/math.jl:125-125`. -/
def P_math_125 : Prop := ∀ T : FTy, ∀ (z : TrigPi.Cx T) (c : FV T), HasResult (MathMisc.evalpolyComplex1 z c)

theorem p_math_125_proven : P_math_125 := by simp [P_math_125, HasResult]

/-- `evalpoly(z::Complex, p::AbstractVector)` at `base/math.jl:128-128`. -/
def P_math_128 : Prop := ∀ T : FTy, ∀ (z : TrigPi.Cx T) (p : List (FV T)), HasResult (MathMisc.evalpolyComplex z p)

theorem p_math_128_proven : P_math_128 := by simp [P_math_128, HasResult]

/-- `_evalpoly(z::Complex, p)` at `base/math.jl:130-148`. -/
def P_math_130 : Prop := ∀ T : FTy, ∀ (z : TrigPi.Cx T) (p : List (FV T)), HasResult (MathMisc.evalpolyComplex z p)

theorem p_math_130_proven : P_math_130 := by simp [P_math_130, HasResult]

/-- `horner(x, p...)` at `base/math.jl:157-160`. -/
def P_math_157 : Prop := ∀ T : FTy, ∀ (x : FV T) (p : List (FV T)), HasResult (Exp.horner x p)

theorem p_math_157_proven : P_math_157 := by simp [P_math_157, HasResult]

/-- `evalpoly(z, p...)` at `base/math.jl:189-192`. -/
def P_math_189 : Prop := ∀ T : FTy, ∀ (z : TrigPi.Cx T) (p : List (FV T)), HasResult (MathMisc.evalpolyComplex z p)

theorem p_math_189_proven : P_math_189 := by simp [P_math_189, HasResult]

/-- `exthorner(x::T, p::Tuple{T,T,T}) where T<:Union{Float32,Float64}` at `base/math.jl:196-201`. -/
def P_math_196 : Prop := ∀ T : FTy, ∀ (x : FV T) (p : FV T × FV T × FV T), HasResult (Exp.exthorner x p)

theorem p_math_196_proven : P_math_196 := by simp [P_math_196, HasResult]

/-- `_exthorner(i::Int, x::T, p::Tuple{T,T,T}, hi::T, lo::T) where T<:Union{Float32,Float64}` at `base/math.jl:203-210`. -/
def P_math_203 : Prop := ∀ T : FTy, ∀ (i : Nat) (x : FV T) (p : FV T × FV T × FV T) (hi lo : FV T), HasResult (Exp.exthornerStep i x p hi lo)

theorem p_math_203_proven : P_math_203 := by simp [P_math_203, HasResult]

/-- `_180_over_pi(z::AbstractFloat)` at `base/math.jl:213-215`. -/
def P_math_213 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.oneEightyOverPi T)

theorem p_math_213_proven : P_math_213 := by simp [P_math_213, HasResult]

/-- `_pi_over_180(z::AbstractFloat)` at `base/math.jl:216-218`. -/
def P_math_216 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.piOverOneEighty T)

theorem p_math_216_proven : P_math_216 := by simp [P_math_216, HasResult]

/-- `_180_over_pi(::Float16)` at `base/math.jl:221-221`. -/
def P_math_221 : Prop := ∀ _u : Unit, HasResult (rad2deg16)

theorem p_math_221_proven : P_math_221 := by simp [P_math_221, HasResult]

/-- `_180_over_pi(::Float32)` at `base/math.jl:222-222`. -/
def P_math_222 : Prop := ∀ _u : Unit, HasResult (rad2deg32)

theorem p_math_222_proven : P_math_222 := by simp [P_math_222, HasResult]

/-- `_pi_over_180(::Float16)` at `base/math.jl:223-223`. -/
def P_math_223 : Prop := ∀ _u : Unit, HasResult (deg2rad16)

theorem p_math_223_proven : P_math_223 := by simp [P_math_223, HasResult]

/-- `rad2deg(z::AbstractFloat)` at `base/math.jl:238-238`. -/
def P_math_238 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.rad2deg T x)

theorem p_math_238_proven : P_math_238 := by simp [P_math_238, HasResult]

/-- `deg2rad(z::AbstractFloat)` at `base/math.jl:253-253`. -/
def P_math_253 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.deg2rad T x)

theorem p_math_253_proven : P_math_253 := by simp [P_math_253, HasResult]

/-- `rad2deg(z::Real)` at `base/math.jl:254-254`. -/
def P_math_254 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.rad2deg T x)

theorem p_math_254_proven : P_math_254 := by simp [P_math_254, HasResult]

/-- `deg2rad(z::Real)` at `base/math.jl:255-255`. -/
def P_math_255 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (TrigMisc.deg2rad T x)

theorem p_math_255_proven : P_math_255 := by simp [P_math_255, HasResult]

/-- `rad2deg(z::Number)` at `base/math.jl:256-256`. -/
def P_math_256 : Prop := ∀ T : FTy, ∀ z : TrigPi.Cx T, HasResult (MathMisc.rad2degNumber z)

theorem p_math_256_proven : P_math_256 := by simp [P_math_256, HasResult]

/-- `deg2rad(z::Number)` at `base/math.jl:257-257`. -/
def P_math_257 : Prop := ∀ T : FTy, ∀ z : TrigPi.Cx T, HasResult (MathMisc.deg2radNumber z)

theorem p_math_257_proven : P_math_257 := by simp [P_math_257, HasResult]

/-- `log(b::T, x::T) where {T<:Number}` at `base/math.jl:259-259`. -/
def P_math_259 : Prop := ∀ T : FTy, ∀ (b x : FV T), HasResult (MathMisc.logBase (fun z => .ok z) div b x)

theorem p_math_259_proven : P_math_259 := by simp [P_math_259, HasResult]

/-- `log(b::Number, x::Number)` at `base/math.jl:304-304`. -/
def P_math_304 : Prop := ∀ T : FTy, ∀ (b x : FV T), HasResult (MathMisc.logBase (fun z => .ok z) div b x)

theorem p_math_304_proven : P_math_304 := by simp [P_math_304, HasResult]

/-- `nan_dom_err(out, x)` at `base/math.jl:399-399`. -/
def P_math_399 : Prop := ∀ T S : FTy, ∀ (out : FV T) (x : FV S), HasResult (MathMisc.nanDomErr out x)

theorem p_math_399_proven : P_math_399 := by simp [P_math_399, HasResult]

/-- `sqrt(x::IEEEFloat)` at `base/math.jl:629-632`. -/
def P_math_629 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (MathMisc.sqrt x)

theorem p_math_629_proven : P_math_629 := by simp [P_math_629, HasResult]

/-- `fourthroot(x::Number)` at `base/math.jl:685-685`. -/
def P_math_685 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (MathMisc.fourthroot x)

theorem p_math_685_proven : P_math_685 := by simp [P_math_685, HasResult]

/-- `hypot(x::Number)` at `base/math.jl:729-729`. -/
def P_math_729 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (MathMisc.hypot1 x)

theorem p_math_729_proven : P_math_729 := by simp [P_math_729, HasResult]

/-- `hypot(x::Number, y::Number)` at `base/math.jl:730-730`. -/
def P_math_730 : Prop := ∀ T S : FTy, ∀ (x : FV T) (y : FV S), HasResult (MathMisc.hypotMixed x y)

theorem p_math_730_proven : P_math_730 := by simp [P_math_730, HasResult]

/-- `hypot(x::Number, y::Number, xs::Number...)` at `base/math.jl:731-731`. -/
def P_math_731 : Prop := ∀ T : FTy, ∀ xs : List (FV T), HasResult (MathMisc.hypotTupleGeneric xs)

theorem p_math_731_proven : P_math_731 := by simp [P_math_731, HasResult]

/-- `_hypot(x, y)` at `base/math.jl:732-786`. -/
def P_math_732 : Prop := ∀ T : FTy, ∀ x y : FV T, HasResult (MathMisc.hypotGeneric x y)

theorem p_math_732_proven : P_math_732 := by simp [P_math_732, HasResult]

/-- `_hypot(x::Float32, y::Float32)` at `base/math.jl:789-795`. -/
def P_math_789 : Prop := ∀ x y : FV .f32, HasResult (MathMisc.hypot32 x y)

theorem p_math_789_proven : P_math_789 := by simp [P_math_789, HasResult]

/-- `_hypot(x::Float16, y::Float16)` at `base/math.jl:796-802`. -/
def P_math_796 : Prop := ∀ x y : FV .f16, HasResult (MathMisc.hypot16 x y)

theorem p_math_796_proven : P_math_796 := by simp [P_math_796, HasResult]

/-- `_hypot(x::ComplexF16, y::ComplexF16)` at `base/math.jl:803-803`. -/
def P_math_803 : Prop := ∀ x y : TrigPi.Cx .f16, HasResult (MathMisc.hypotC16 x y)

theorem p_math_803_proven : P_math_803 := by simp [P_math_803, HasResult]

/-- `_hypot(x::NTuple{N,<:Number}) where {N}` at `base/math.jl:805-814`. -/
def P_math_805 : Prop := ∀ T : FTy, ∀ xs : List (FV T), HasResult (MathMisc.hypotTupleGeneric xs)

theorem p_math_805_proven : P_math_805 := by simp [P_math_805, HasResult]

/-- `_hypot(x::NTuple{N,<:IEEEFloat}) where {N}` at `base/math.jl:816-828`. -/
def P_math_816 : Prop := ∀ T : FTy, ∀ xs : List (FV T), HasResult (MathMisc.hypotTupleIEEE xs)

theorem p_math_816_proven : P_math_816 := by simp [P_math_816, HasResult]

/-- `add_fast(x, y)` at `base/math.jl:826-826`. -/
def P_math_826 : Prop := ∀ T : FTy, ∀ x y : FV T, HasResult (MathMisc.addFast x y)

theorem p_math_826_proven : P_math_826 := by simp [P_math_826, HasResult]

/-- `atan(y::Real, x::Real)` at `base/math.jl:830-830`. -/
def P_math_830 : Prop := ∀ T S : FTy, ∀ (y : FV T) (x : FV S), HasResult (MathMisc.atanMixed y x)

theorem p_math_830_proven : P_math_830 := by simp [P_math_830, HasResult]

/-- `atan(y::T, x::T) where {T<:AbstractFloat}` at `base/math.jl:831-831`. -/
def P_math_831 : Prop := ∀ T : FTy, ∀ x y : FV T, HasResult (MathMisc.atanNoOp (α := FV T))

theorem p_math_831_proven : P_math_831 := by simp [P_math_831, HasResult]

/-- `_isless(x::T, y::T) where {T<:AbstractFloat}` at `base/math.jl:833-833`. -/
def P_math_833 : Prop := ∀ T : FTy, ∀ x y : FV T, HasResult (Bits.isless_ x y)

theorem p_math_833_proven : P_math_833 := by simp [P_math_833, HasResult]

/-- `min(x::T, y::T) where {T<:AbstractFloat}` at `base/math.jl:834-834`. -/
def P_math_834 : Prop := ∀ T : FTy, ∀ x y : FV T, HasResult (Bits.minGeneric x y)

theorem p_math_834_proven : P_math_834 := by simp [P_math_834, HasResult]

/-- `max(x::T, y::T) where {T<:AbstractFloat}` at `base/math.jl:835-835`. -/
def P_math_835 : Prop := ∀ T : FTy, ∀ x y : FV T, HasResult (Bits.maxGeneric x y)

theorem p_math_835_proven : P_math_835 := by simp [P_math_835, HasResult]

/-- `min(x::T, y::T) where {T<:IEEEFloat}` at `base/math.jl:838-838`. -/
def P_math_838 : Prop := ∀ T : FTy, ∀ x y : FV T, HasResult (Bits.minFloat x y)

theorem p_math_838_proven : P_math_838 := by simp [P_math_838, HasResult]

/-- `max(x::T, y::T) where {T<:IEEEFloat}` at `base/math.jl:839-839`. -/
def P_math_839 : Prop := ∀ T : FTy, ∀ x y : FV T, HasResult (Bits.maxFloat x y)

theorem p_math_839_proven : P_math_839 := by simp [P_math_839, HasResult]

/-- `ldexp(x::T, e::Integer) where T<:IEEEFloat` at `base/math.jl:854-897`. -/
def P_math_854 : Prop := ∀ T : FTy, ∀ (x : FV T) (e : Int), HasResult (Bits.ldexp x e)

theorem p_math_854_proven : P_math_854 := by simp [P_math_854, HasResult]

/-- `ldexp(x::Float16, q::Integer)` at `base/math.jl:898-898`. -/
def P_math_898 : Prop := ∀ (x : FV .f16) (e : Int), HasResult (Bits.ldexp16 x e)

theorem p_math_898_proven : P_math_898 := by simp [P_math_898, HasResult]

/-- `exponent(x::T) where T<:IEEEFloat` at `base/math.jl:936-950`. -/
def P_math_936 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (Bits.exponent x)

theorem p_math_936_proven : P_math_936 := by simp [P_math_936, HasResult]

/-- `throw1(x)` at `base/math.jl:937-937`. -/
def P_math_937 : Prop := ∀ x : FV .f64, HasResult (Bits.exponentThrow1)

theorem p_math_937_proven : P_math_937 := by simp [P_math_937, HasResult]

/-- `throw2(x)` at `base/math.jl:938-938`. -/
def P_math_938 : Prop := ∀ x : FV .f64, HasResult (Bits.exponentThrow2)

theorem p_math_938_proven : P_math_938 := by simp [P_math_938, HasResult]

/-- `_exponent_finite_nonzero(x::T) where T<:IEEEFloat` at `base/math.jl:956-965`. -/
def P_math_956 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (Bits.exponentFiniteNonzero x)

theorem p_math_956_proven : P_math_956 := by simp [P_math_956, HasResult]

/-- `_ilog2_step(y::T, d::T, s) where {T<:Integer}` at `base/math.jl:967-978`. -/
def P_math_967 : Prop := ∀ (fuel y d s : Nat), HasResult (Bits.ilog2Step fuel y d s)

theorem p_math_967_proven : P_math_967 := by simp [P_math_967, HasResult]

/-- `exponent(x::Integer)` at `base/math.jl:980-985`. -/
def P_math_980 : Prop := ∀ x : Int, HasResult (Bits.exponentInteger x)

theorem p_math_980_proven : P_math_980 := by simp [P_math_980, HasResult]

/-- `exponent(x::Base.BitInteger)` at `base/math.jl:987-991`. -/
def P_math_987 : Prop := ∀ (t : IntTy) (x : JInt t), HasResult (Bits.exponentBitInteger x)

theorem p_math_987_proven : P_math_987 := by simp [P_math_987, HasResult]

/-- `exponent(x::Bool)` at `base/math.jl:993-999`. -/
def P_math_993 : Prop := ∀ x : Bool, HasResult (Bits.exponentBool x)

theorem p_math_993_proven : P_math_993 := by simp [P_math_993, HasResult]

/-- `scaleinv(x::T) where T<:IEEEFloat` at `base/math.jl:1100-1111`. -/
def P_math_1100 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (Bits.scaleinv x)

theorem p_math_1100_proven : P_math_1100 := by simp [P_math_1100, HasResult]

/-- `rem(x::T, p::T, ::RoundingMode{:Nearest}) where T<:IEEEFloat` at `base/math.jl:1122-1145`. -/
def P_math_1122 : Prop := ∀ T : FTy, ∀ x p : FV T, HasResult (Bits.remNearest x p)

theorem p_math_1122_proven : P_math_1122 := by simp [P_math_1122, HasResult]

/-- `modf(x)` at `base/math.jl:1163-1163`. -/
def P_math_1163 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (Bits.modfGeneric x)

theorem p_math_1163_proven : P_math_1163 := by simp [P_math_1163, HasResult]

/-- `modf(x::T) where T<:IEEEFloat` at `base/math.jl:1165-1170`. -/
def P_math_1165 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (Bits.modf x)

theorem p_math_1165_proven : P_math_1165 := by simp [P_math_1165, HasResult]

/-- `add22condh(xh::Float64, xl::Float64, yh::Float64, yl::Float64)` at `base/math.jl:1176-1185`. -/
def P_math_1176 : Prop := ∀ xh xl yh yl : FV .f64, HasResult (Bits.add22condh xh xl yh yl)

theorem p_math_1176_proven : P_math_1176 := by simp [P_math_1176, HasResult]

/-- `mod2pi(x)` at `base/math.jl:1241-1241`. -/
def P_math_1241 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (MathMisc.mod2pi x)

theorem p_math_1241_proven : P_math_1241 := by simp [P_math_1241, HasResult]

/-- `muladd(x,y,z)` at `base/math.jl:1265-1265`. -/
def P_math_1265 : Prop := ∀ (α : Type) (mul add : α → α → α) (x y z : α), HasResult (MathMisc.muladdGeneric mul add x y z)

theorem p_math_1265_proven : P_math_1265 := by simp [P_math_1265, HasResult]

/-- `highword(x::Float64)` at `base/math.jl:1275-1275`. -/
def P_math_1275 : Prop := ∀ x : FV .f64, HasResult (Bits.highword64 x)

theorem p_math_1275_proven : P_math_1275 := by simp [P_math_1275, HasResult]

/-- `highword(x::UInt64)` at `base/math.jl:1276-1276`. -/
def P_math_1276 : Prop := ∀ x : Nat, HasResult (Bits.highwordU64 x)

theorem p_math_1276_proven : P_math_1276 := by simp [P_math_1276, HasResult]

/-- `highword(x::Float32)` at `base/math.jl:1277-1277`. -/
def P_math_1277 : Prop := ∀ x : FV .f32, HasResult (Bits.highword32 x)

theorem p_math_1277_proven : P_math_1277 := by simp [P_math_1277, HasResult]

/-- `fromhighword(::Type{Float64}, u::UInt32)` at `base/math.jl:1279-1279`. -/
def P_math_1279 : Prop := ∀ u : Nat, HasResult (Bits.fromhighword64 u)

theorem p_math_1279_proven : P_math_1279 := by simp [P_math_1279, HasResult]

/-- `fromhighword(::Type{Float32}, u::UInt32)` at `base/math.jl:1280-1280`. -/
def P_math_1280 : Prop := ∀ u : Nat, HasResult (Bits.fromhighword32 u)

theorem p_math_1280_proven : P_math_1280 := by simp [P_math_1280, HasResult]

/-- `poshighword(x::Float64)` at `base/math.jl:1288-1288`. -/
def P_math_1288 : Prop := ∀ x : FV .f64, HasResult (Bits.poshighword64 x)

theorem p_math_1288_proven : P_math_1288 := by simp [P_math_1288, HasResult]

/-- `poshighword(x::UInt64)` at `base/math.jl:1289-1289`. -/
def P_math_1289 : Prop := ∀ x : Nat, HasResult (Bits.poshighwordU64 x)

theorem p_math_1289_proven : P_math_1289 := by simp [P_math_1289, HasResult]

/-- `poshighword(x::Float32)` at `base/math.jl:1290-1290`. -/
def P_math_1290 : Prop := ∀ x : FV .f32, HasResult (Bits.poshighword32 x)

theorem p_math_1290_proven : P_math_1290 := by simp [P_math_1290, HasResult]

/-- `$func(a::Float16)` at `base/math.jl:1309-1309`. -/
def P_math_1309 : Prop := ∀ (f : FV .f32 → Jl (FV .f32)) (x : FV .f16), HasResult (MathMisc.viaF32 f x)

theorem p_math_1309_proven : P_math_1309 := by simp [P_math_1309, HasResult]

/-- `$func(a::ComplexF16)` at `base/math.jl:1310-1310`. -/
def P_math_1310 : Prop := ∀ (f : TrigPi.Cx .f32 → Jl (TrigPi.Cx .f32)) (x : TrigPi.Cx .f16), HasResult (MathMisc.viaC32 f x)

theorem p_math_1310_proven : P_math_1310 := by simp [P_math_1310, HasResult]

/-- `$func(a::ComplexF16)` at `base/math.jl:1315-1315`. -/
def P_math_1315 : Prop := ∀ (f : TrigPi.Cx .f32 → Jl (TrigPi.Cx .f32)) (x : TrigPi.Cx .f16), HasResult (MathMisc.viaC32 f x)

theorem p_math_1315_proven : P_math_1315 := by simp [P_math_1315, HasResult]

/-- `atan(a::Float16,b::Float16)` at `base/math.jl:1319-1319`. -/
def P_math_1319 : Prop := ∀ x y : FV .f16, HasResult (MathMisc.atan16 x y)

theorem p_math_1319_proven : P_math_1319 := by simp [P_math_1319, HasResult]

/-- `sincos(a::Float16)` at `base/math.jl:1320-1320`. -/
def P_math_1320 : Prop := ∀ (f : FV .f32 → Jl (FV .f32 × FV .f32)) (x : FV .f16), HasResult (MathMisc.sincos16 f x)

theorem p_math_1320_proven : P_math_1320 := by simp [P_math_1320, HasResult]

/-- `($f)(x::Real)` at `base/math.jl:1326-1330`. -/
def P_math_1326 : Prop := ∀ (α β : Type) (float : α → β) (f : β → Jl β) (x : α) (same : Bool), HasResult (MathMisc.realFallback float same f x)

theorem p_math_1326_proven : P_math_1326 := by simp [P_math_1326, HasResult]

/-- `$(f)(::Missing)` at `base/math.jl:1331-1331`. -/
def P_math_1331 : Prop := ∀ (α : Type) (x : Option α), HasResult (MathMisc.missing1 x)

theorem p_math_1331_proven : P_math_1331 := by simp [P_math_1331, HasResult]

/-- `$(f)(::Missing, ::Missing)` at `base/math.jl:1335-1335`. -/
def P_math_1335 : Prop := ∀ (α β γ : Type) (x : Option α) (y : Option β), HasResult (MathMisc.missing2 (γ := γ) x y)

theorem p_math_1335_proven : P_math_1335 := by simp [P_math_1335, HasResult]

/-- `$(f)(::Number, ::Missing)` at `base/math.jl:1336-1336`. -/
def P_math_1336 : Prop := ∀ (α β γ : Type) (x : Option α) (y : Option β), HasResult (MathMisc.missing2 (γ := γ) x y)

theorem p_math_1336_proven : P_math_1336 := by simp [P_math_1336, HasResult]

/-- `$(f)(::Missing, ::Number)` at `base/math.jl:1337-1337`. -/
def P_math_1337 : Prop := ∀ (α β γ : Type) (x : Option α) (y : Option β), HasResult (MathMisc.missing2 (γ := γ) x y)

theorem p_math_1337_proven : P_math_1337 := by simp [P_math_1337, HasResult]

/-- `exp2(x::AbstractFloat)` at `base/math.jl:1340-1340`. -/
def P_math_1340 : Prop := ∀ (α : Type) (two : α) (pow : α → α → α) (x : α), HasResult (MathMisc.exp2Abstract two pow x)

theorem p_math_1340_proven : P_math_1340 := by simp [P_math_1340, HasResult]

/-- `exp10(x::AbstractFloat)` at `base/math.jl:1341-1341`. -/
def P_math_1341 : Prop := ∀ (α : Type) (ten : α) (pow : α → α → α) (x : α), HasResult (MathMisc.exp10Abstract ten pow x)

theorem p_math_1341_proven : P_math_1341 := by simp [P_math_1341, HasResult]

/-- `fourthroot(::Missing)` at `base/math.jl:1342-1342`. -/
def P_math_1342 : Prop := ∀ (α : Type) (x : Option α), HasResult (MathMisc.missing1 x)

theorem p_math_1342_proven : P_math_1342 := by simp [P_math_1342, HasResult]

/-- `logb(::Type{Float32},::Val{2})` at `base/special/log.jl:141-141`. -/
def P_special_log_141 : Prop := ∀ _u : Unit, HasResult (Log.logb32 .two)

theorem p_special_log_141_proven : P_special_log_141 := by simp [P_special_log_141, HasResult]

/-- `logb(::Type{Float32},::Val{:ℯ})` at `base/special/log.jl:142-142`. -/
def P_special_log_142 : Prop := ∀ _u : Unit, HasResult (Log.logb32 .e)

theorem p_special_log_142_proven : P_special_log_142 := by simp [P_special_log_142, HasResult]

/-- `logb(::Type{Float32},::Val{10})` at `base/special/log.jl:143-143`. -/
def P_special_log_143 : Prop := ∀ _u : Unit, HasResult (Log.logb32 .ten)

theorem p_special_log_143_proven : P_special_log_143 := by simp [P_special_log_143, HasResult]

/-- `logbU(::Type{Float64},::Val{2})` at `base/special/log.jl:144-144`. -/
def P_special_log_144 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logbU .two)

theorem p_special_log_144_proven : P_special_log_144 := by simp [P_special_log_144, HasResult]

/-- `logbL(::Type{Float64},::Val{2})` at `base/special/log.jl:145-145`. -/
def P_special_log_145 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logbL .two)

theorem p_special_log_145_proven : P_special_log_145 := by simp [P_special_log_145, HasResult]

/-- `logbU(::Type{Float64},::Val{:ℯ})` at `base/special/log.jl:146-146`. -/
def P_special_log_146 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logbU .e)

theorem p_special_log_146_proven : P_special_log_146 := by simp [P_special_log_146, HasResult]

/-- `logbL(::Type{Float64},::Val{:ℯ})` at `base/special/log.jl:147-147`. -/
def P_special_log_147 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logbL .e)

theorem p_special_log_147_proven : P_special_log_147 := by simp [P_special_log_147, HasResult]

/-- `logbU(::Type{Float64},::Val{10})` at `base/special/log.jl:148-148`. -/
def P_special_log_148 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logbU .ten)

theorem p_special_log_148_proven : P_special_log_148 := by simp [P_special_log_148, HasResult]

/-- `logbL(::Type{Float64},::Val{10})` at `base/special/log.jl:149-149`. -/
def P_special_log_149 : Prop := ∀ _u : Unit, HasResult (MathFuncs.logbL .ten)

theorem p_special_log_149_proven : P_special_log_149 := by simp [P_special_log_149, HasResult]

/-- `log_proc1(y::Float64,mf::Float64,F::Float64,f::Float64,base=Val(:ℯ))` at `base/special/log.jl:152-181`. -/
def P_special_log_152 : Prop := ∀ (y mf F f : F64) (b : LogBase), HasResult (MathFuncs.logProc1 y mf F f b)

theorem p_special_log_152_proven : P_special_log_152 := by simp [P_special_log_152, HasResult]

/-- `log_proc2(f::Float64,base=Val(:ℯ))` at `base/special/log.jl:184-207`. -/
def P_special_log_184 : Prop := ∀ (f : F64) (b : LogBase), HasResult (MathFuncs.logProc2 f b)

theorem p_special_log_184_proven : P_special_log_184 := by simp [P_special_log_184, HasResult]

/-- `log_proc1(y::Float32,mf::Float32,F::Float32,f::Float32,base=Val(:ℯ))` at `base/special/log.jl:210-230`. -/
def P_special_log_210 : Prop := ∀ (y mf F f : FV .f32) (b : LogBase), HasResult (Log.logProc1 y mf F f b)

theorem p_special_log_210_proven : P_special_log_210 := by simp [P_special_log_210, HasResult]

/-- `log_proc2(f::Float32,base=Val(:ℯ))` at `base/special/log.jl:233-249`. -/
def P_special_log_233 : Prop := ∀ (f : FV .f32) (b : LogBase), HasResult (Log.logProc2 f b)

theorem p_special_log_233_proven : P_special_log_233 := by simp [P_special_log_233, HasResult]

/-- `log2(x::Float32)` at `base/special/log.jl:251-251`. -/
def P_special_log_251 : Prop := ∀ x : FV .f32, HasResult (Log.log2F32 x)

theorem p_special_log_251_proven : P_special_log_251 := by simp [P_special_log_251, HasResult]

/-- `log(x::Float32)` at `base/special/log.jl:252-252`. -/
def P_special_log_252 : Prop := ∀ x : FV .f32, HasResult (Log.logF32 x)

theorem p_special_log_252_proven : P_special_log_252 := by simp [P_special_log_252, HasResult]

/-- `log10(x::Float32)` at `base/special/log.jl:253-253`. -/
def P_special_log_253 : Prop := ∀ x : FV .f32, HasResult (Log.log10F32 x)

theorem p_special_log_253_proven : P_special_log_253 := by simp [P_special_log_253, HasResult]

/-- `_log(x::Float64, base, func::Symbol)` at `base/special/log.jl:258-292`. -/
def P_special_log_258 : Prop := ∀ (x : F64) (b : LogBase), HasResult (MathFuncs.logImpl x b)

theorem p_special_log_258_proven : P_special_log_258 := by simp [P_special_log_258, HasResult]

/-- `_log(x::Float32, base, func::Symbol)` at `base/special/log.jl:294-327`. -/
def P_special_log_294 : Prop := ∀ (x : FV .f32) (b : LogBase), HasResult (Log.log32 x b)

theorem p_special_log_294_proven : P_special_log_294 := by simp [P_special_log_294, HasResult]

/-- `log1p(x::Float32)` at `base/special/log.jl:364-394`. -/
def P_special_log_364 : Prop := ∀ x : FV .f32, HasResult (Log.log1pF32 x)

theorem p_special_log_364_proven : P_special_log_364 := by simp [P_special_log_364, HasResult]

/-- `log_tab_unpack(t::UInt64)` at `base/special/log.jl:542-546`. -/
def P_special_log_542 : Prop := ∀ t : Nat, HasResult (MathFuncs.logTabUnpack t)

theorem p_special_log_542_proven : P_special_log_542 := by simp [P_special_log_542, HasResult]

/-- `_log_ext(xu::UInt64)` at `base/special/log.jl:555-583`. -/
def P_special_log_555 : Prop := ∀ t : Nat, HasResult (MathFuncs.logExt t)

theorem p_special_log_555_proven : P_special_log_555 := by simp [P_special_log_555, HasResult]

/-- `rem2pi(x::Float64, ::RoundingMode{:Nearest})` at `base/special/rem2pi.jl:14-39`. -/
def P_special_rem2pi_14 : Prop := ∀ x : FV .f64, HasResult (Special.rem2pi64 x .Nearest)

theorem p_special_rem2pi_14_proven : P_special_rem2pi_14 := by simp [P_special_rem2pi_14, HasResult]

/-- `rem2pi(x::Float64, ::RoundingMode{:ToZero})` at `base/special/rem2pi.jl:40-67`. -/
def P_special_rem2pi_40 : Prop := ∀ x : FV .f64, HasResult (Special.rem2pi64 x .ToZero)

theorem p_special_rem2pi_40_proven : P_special_rem2pi_40 := by simp [P_special_rem2pi_40, HasResult]

/-- `rem2pi(x::Float64, ::RoundingMode{:Down})` at `base/special/rem2pi.jl:68-99`. -/
def P_special_rem2pi_68 : Prop := ∀ x : FV .f64, HasResult (Special.rem2pi64 x .Down)

theorem p_special_rem2pi_68_proven : P_special_rem2pi_68 := by simp [P_special_rem2pi_68, HasResult]

/-- `rem2pi(x::Float64, ::RoundingMode{:Up})` at `base/special/rem2pi.jl:100-131`. -/
def P_special_rem2pi_100 : Prop := ∀ x : FV .f64, HasResult (Special.rem2pi64 x .Up)

theorem p_special_rem2pi_100_proven : P_special_rem2pi_100 := by simp [P_special_rem2pi_100, HasResult]

/-- `rem2pi(x::Float32, r::RoundingMode)` at `base/special/rem2pi.jl:133-133`. -/
def P_special_rem2pi_133 : Prop := ∀ (x : FV .f32) (r : Mode), HasResult (Special.rem2piNarrow x r)

theorem p_special_rem2pi_133_proven : P_special_rem2pi_133 := by simp [P_special_rem2pi_133, HasResult]

/-- `rem2pi(x::Float16, r::RoundingMode)` at `base/special/rem2pi.jl:134-134`. -/
def P_special_rem2pi_134 : Prop := ∀ (x : FV .f16) (r : Mode), HasResult (Special.rem2piNarrow x r)

theorem p_special_rem2pi_134_proven : P_special_rem2pi_134 := by simp [P_special_rem2pi_134, HasResult]

/-- `rem2pi(x::Int32, r::RoundingMode)` at `base/special/rem2pi.jl:135-135`. -/
def P_special_rem2pi_135 : Prop := ∀ (x : JInt .i32) (r : Mode), HasResult (Special.rem2piInt32 x r)

theorem p_special_rem2pi_135_proven : P_special_rem2pi_135 := by simp [P_special_rem2pi_135, HasResult]

/-- `rem2pi(x::Integer, r::RoundingMode)` at `base/special/rem2pi.jl:138-142`. -/
def P_special_rem2pi_138 : Prop := ∀ (x : Int) (r : Mode), HasResult (Special.rem2piInteger x r)

theorem p_special_rem2pi_138_proven : P_special_rem2pi_138 := by simp [P_special_rem2pi_138, HasResult]

/-- `use_power_by_squaring(n::Integer)` at `base/special/pow.jl:1-3`. -/
def P_special_pow_1 : Prop := ∀ n : Int, HasResult (Special.usePowerBySquaring n)

theorem p_special_pow_1_proven : P_special_pow_1 := by simp [P_special_pow_1, HasResult]

/-- `^(x::T, y::T) where T <: Union{Float16, Float32}` at `base/special/pow.jl:34-56`. -/
def P_special_pow_34 : Prop := ∀ T : FTy, T = .f16 ∨ T = .f32 → ∀ x y : FV T, HasResult (Special.powFF x y)

theorem p_special_pow_34_proven : P_special_pow_34 := by simp [P_special_pow_34, HasResult]

/-- `^(x::T, n::Integer) where T <: Union{Float16, Float32}` at `base/special/pow.jl:80-89`. -/
def P_special_pow_80 : Prop := ∀ T : FTy, T = .f16 ∨ T = .f32 → ∀ (x : FV T) (n : Int), HasResult (Special.powFI x n)

theorem p_special_pow_80_proven : P_special_pow_80 := by simp [P_special_pow_80, HasResult]

/-- `pow_body(x::Float64, y::Float64)` at `base/special/pow.jl:91-103`. -/
def P_special_pow_91 : Prop := ∀ x y : F64, HasResult (MathFuncs.powBodyF x y)

theorem p_special_pow_91_proven : P_special_pow_91 := by simp [P_special_pow_91, HasResult]

/-- `pow_body(x::T, y) where T <: Union{Float16, Float32}` at `base/special/pow.jl:105-107`. -/
def P_special_pow_105 : Prop := ∀ T : FTy, T = .f16 ∨ T = .f32 → ∀ (x : FV T) (y : FV .f64), HasResult (Special.powBodyF T x y)

theorem p_special_pow_105_proven : P_special_pow_105 := by simp [P_special_pow_105, HasResult]

/-- `pow_body(x::Union{Float16, Float32}, n::Int32)` at `base/special/pow.jl:109-114`. -/
def P_special_pow_109 : Prop := ∀ T : FTy, T = .f16 ∨ T = .f32 → ∀ (x : FV T) (n : Int), HasResult (Special.powBodyI x n)

theorem p_special_pow_109_proven : P_special_pow_109 := by simp [P_special_pow_109, HasResult]

/-- `pow_body(x::Float64, n::Integer)` at `base/special/pow.jl:118-144`. -/
def P_special_pow_118 : Prop := ∀ (x : F64) (n : Int), HasResult (MathFuncs.powBodyI x n)

theorem p_special_pow_118_proven : P_special_pow_118 := by simp [P_special_pow_118, HasResult]

/-- `cbrt(x::AbstractFloat)` at `base/special/cbrt.jl:36-36`. -/
def P_special_cbrt_36 : Prop := ∀ (α : Type) (lt0 : α → Bool) (neg pow : α → α) (x : α), HasResult (Special.cbrtAbstract lt0 neg pow x)

theorem p_special_cbrt_36_proven : P_special_cbrt_36 := by simp [P_special_cbrt_36, HasResult]

/-- `_approx_cbrt(x::T) where {T<:Union{Float32,Float64}}` at `base/special/cbrt.jl:63-79`. -/
def P_special_cbrt_63 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (Special.approxCbrt x)

theorem p_special_cbrt_63_proven : P_special_cbrt_63 := by simp [P_special_cbrt_63, HasResult]

/-- `_improve_cbrt(x::Float32, t::Float32)` at `base/special/cbrt.jl:81-101`. -/
def P_special_cbrt_81 : Prop := ∀ x t : FV .f32, HasResult (Special.improveCbrt32 x t)

theorem p_special_cbrt_81_proven : P_special_cbrt_81 := by simp [P_special_cbrt_81, HasResult]

/-- `_improve_cbrt(x::Float64, t::Float64)` at `base/special/cbrt.jl:103-142`. -/
def P_special_cbrt_103 : Prop := ∀ x t : F64, HasResult (MathFuncs.improveCbrt x t)

theorem p_special_cbrt_103_proven : P_special_cbrt_103 := by simp [P_special_cbrt_103, HasResult]

/-- `cbrt(x::Union{Float32,Float64})` at `base/special/cbrt.jl:144-150`. -/
def P_special_cbrt_144 : Prop := ∀ T : FTy, T = .f32 ∨ T = .f64 → ∀ x : FV T, HasResult (Special.cbrt x)

theorem p_special_cbrt_144_proven : P_special_cbrt_144 := by simp [P_special_cbrt_144, HasResult]

/-- `cbrt(a::Float16)` at `base/special/cbrt.jl:152-167`. -/
def P_special_cbrt_152 : Prop := ∀ x : FV .f16, HasResult (Special.cbrt16 x)

theorem p_special_cbrt_152_proven : P_special_cbrt_152 := by simp [P_special_cbrt_152, HasResult]

/-- `cody_waite_2c_pio2(x::Float64, fn, n)` at `base/special/rem_pio2.jl:48-56`. -/
def P_special_rem_pio2_48 : Prop := ∀ (x fn : F64) (n : Int), HasResult (MathFuncs.codyWaite2cPio2 x fn n)

theorem p_special_rem_pio2_48_proven : P_special_rem_pio2_48 := by simp [P_special_rem_pio2_48, HasResult]

/-- `cody_waite_ext_pio2(x::Float64, xhp)` at `base/special/rem_pio2.jl:58-95`. -/
def P_special_rem_pio2_58 : Prop := ∀ (x : F64) (u : Nat), HasResult (MathFuncs.codyWaiteExtPio2 x u)

theorem p_special_rem_pio2_58_proven : P_special_rem_pio2_58 := by simp [P_special_rem_pio2_58, HasResult]

/-- `fromfraction(f::Int128)` at `base/special/rem_pio2.jl:105-128`. -/
def P_special_rem_pio2_105 : Prop := ∀ f : Int, HasResult (MathFuncs.fromfraction f)

theorem p_special_rem_pio2_105_proven : P_special_rem_pio2_105 := by simp [P_special_rem_pio2_105, HasResult]

/-- `paynehanek(x::Float64)` at `base/special/rem_pio2.jl:130-211`. -/
def P_special_rem_pio2_130 : Prop := ∀ x : F64, HasResult (MathFuncs.paynehanek x)

theorem p_special_rem_pio2_130_proven : P_special_rem_pio2_130 := by simp [P_special_rem_pio2_130, HasResult]

/-- `rem_pio2_kernel(x::Float32)` at `base/special/rem_pio2.jl:284-295`. -/
def P_special_rem_pio2_284 : Prop := ∀ x : FV .f32, HasResult (Special.remPio2Kernel32 x)

theorem p_special_rem_pio2_284_proven : P_special_rem_pio2_284 := by simp [P_special_rem_pio2_284, HasResult]

/-- `Rational{BigInt}(::_KnownIrrational)` at `base/mathconstants.jl:23-25`. -/
def P_mathconstants_23 : Prop := ∀ x : MathConstants.KnownIrrational, HasResult (MathConstants.rationalBigInt x)

theorem p_mathconstants_23_proven : P_mathconstants_23 := by simp [P_mathconstants_23, HasResult]

/-- `Rational{T}(x::_KnownIrrational) where {T<:Integer}` at `base/mathconstants.jl:26-28`. -/
def P_mathconstants_26 : Prop := ∀ (α : Type) (f : MathConstants.KnownIrrational → Jl α) (x : MathConstants.KnownIrrational), HasResult (MathConstants.rationalInt f x)

theorem p_mathconstants_26_proven : P_mathconstants_26 := by simp [P_mathconstants_26, HasResult]

/-- `(::Type{T})(x::_KnownIrrational, r::RoundingMode) where {T<:Union{Float32,Float64}}` at `base/mathconstants.jl:29-31`. -/
def P_mathconstants_29 : Prop := ∀ (α : Type) (f : MathConstants.KnownIrrational → Mode → α) (x : MathConstants.KnownIrrational) (r : Mode), HasResult (MathConstants.irrationalFloat f x r)

theorem p_mathconstants_29_proven : P_mathconstants_29 := by simp [P_mathconstants_29, HasResult]

/-- `Base.rationalize(::Type{T}, x::_KnownIrrational; tol::Real=0) where {T<:Integer}` at `base/mathconstants.jl:32-34`. -/
def P_mathconstants_32 : Prop := ∀ (α β : Type) (f : MathConstants.KnownIrrational → β → α) (x : MathConstants.KnownIrrational) (tol : β), HasResult (MathConstants.rationalizeIrrational f x tol)

theorem p_mathconstants_32_proven : P_mathconstants_32 := by simp [P_mathconstants_32, HasResult]

/-- `Base.lessrational(rx::Rational, x::_KnownIrrational)` at `base/mathconstants.jl:35-37`. -/
def P_mathconstants_35 : Prop := ∀ (α : Type) (f : α → MathConstants.KnownIrrational → Bool) (q : α) (x : MathConstants.KnownIrrational), HasResult (MathConstants.lessRational f q x)

theorem p_mathconstants_35_proven : P_mathconstants_35 := by simp [P_mathconstants_35, HasResult]

/-- `Base.:^(::Irrational{:ℯ}, x::T)` at `base/mathconstants.jl:139-139`. -/
def P_mathconstants_139 : Prop := ∀ (α : Type) (exp : α → α) (x : α), HasResult (MathConstants.ePow exp x)

theorem p_mathconstants_139_proven : P_mathconstants_139 := by simp [P_mathconstants_139, HasResult]

/-- `Base.literal_pow(::typeof(^), ::Irrational{:ℯ}, ::Val{p}) where {p}` at `base/mathconstants.jl:141-141`. -/
def P_mathconstants_141 : Prop := ∀ (α : Type) (exp : Int → α) (p : Int), HasResult (MathConstants.eLiteralPow exp p)

theorem p_mathconstants_141_proven : P_mathconstants_141 := by simp [P_mathconstants_141, HasResult]

/-- `Base.log(::Irrational{:ℯ})` at `base/mathconstants.jl:143-143`. -/
def P_mathconstants_143 : Prop := ∀ _u : Unit, HasResult (MathConstants.logE)

theorem p_mathconstants_143_proven : P_mathconstants_143 := by simp [P_mathconstants_143, HasResult]

/-- `Base.log(::Irrational{:ℯ}, x::Number)` at `base/mathconstants.jl:144-144`. -/
def P_mathconstants_144 : Prop := ∀ (α : Type) (log : α → α) (x : α), HasResult (MathConstants.logBaseE log x)

theorem p_mathconstants_144_proven : P_mathconstants_144 := by simp [P_mathconstants_144, HasResult]

/-- `Base.sin(::Irrational{:π})` at `base/mathconstants.jl:146-146`. -/
def P_mathconstants_146 : Prop := ∀ _u : Unit, HasResult (MathConstants.sinPi)

theorem p_mathconstants_146_proven : P_mathconstants_146 := by simp [P_mathconstants_146, HasResult]

/-- `Base.cos(::Irrational{:π})` at `base/mathconstants.jl:147-147`. -/
def P_mathconstants_147 : Prop := ∀ _u : Unit, HasResult (MathConstants.cosPi)

theorem p_mathconstants_147_proven : P_mathconstants_147 := by simp [P_mathconstants_147, HasResult]

/-- `Base.sincos(::Irrational{:π})` at `base/mathconstants.jl:148-148`. -/
def P_mathconstants_148 : Prop := ∀ _u : Unit, HasResult (MathConstants.sincosPi)

theorem p_mathconstants_148_proven : P_mathconstants_148 := by simp [P_mathconstants_148, HasResult]

/-- `Base.tan(::Irrational{:π})` at `base/mathconstants.jl:149-149`. -/
def P_mathconstants_149 : Prop := ∀ _u : Unit, HasResult (MathConstants.tanPi)

theorem p_mathconstants_149_proven : P_mathconstants_149 := by simp [P_mathconstants_149, HasResult]

/-- `Base.cot(::Irrational{:π})` at `base/mathconstants.jl:150-150`. -/
def P_mathconstants_150 : Prop := ∀ _u : Unit, HasResult (MathConstants.cotPi)

theorem p_mathconstants_150_proven : P_mathconstants_150 := by simp [P_mathconstants_150, HasResult]

/-- `copysign(x::Float32, y::Float32)` at `base/floatfuncs.jl:6-6`. -/
def P_floatfuncs_6 : Prop := ∀ x y : FV .f32, HasResult (Bits.copysignF x y)

theorem p_floatfuncs_6_proven : P_floatfuncs_6 := by simp [P_floatfuncs_6, HasResult]

/-- `copysign(x::Float32, y::Real)` at `base/floatfuncs.jl:7-7`. -/
def P_floatfuncs_7 : Prop := ∀ S : FTy, ∀ (x : FV .f32) (y : FV S), HasResult (Bits.copysignReal x y)

theorem p_floatfuncs_7_proven : P_floatfuncs_7 := by simp [P_floatfuncs_7, HasResult]

/-- `copysign(x::Float64, y::Real)` at `base/floatfuncs.jl:8-8`. -/
def P_floatfuncs_8 : Prop := ∀ S : FTy, ∀ (x : FV .f64) (y : FV S), HasResult (Bits.copysignReal x y)

theorem p_floatfuncs_8_proven : P_floatfuncs_8 := by simp [P_floatfuncs_8, HasResult]

/-- `flipsign(x::Float32, y::Float32)` at `base/floatfuncs.jl:11-11`. -/
def P_floatfuncs_11 : Prop := ∀ x y : FV .f32, HasResult (Bits.flipsignF x y)

theorem p_floatfuncs_11_proven : P_floatfuncs_11 := by simp [P_floatfuncs_11, HasResult]

/-- `flipsign(x::Float32, y::Real)` at `base/floatfuncs.jl:12-12`. -/
def P_floatfuncs_12 : Prop := ∀ S : FTy, ∀ (x : FV .f32) (y : FV S), HasResult (Bits.flipsignReal x y)

theorem p_floatfuncs_12_proven : P_floatfuncs_12 := by simp [P_floatfuncs_12, HasResult]

/-- `flipsign(x::Float64, y::Real)` at `base/floatfuncs.jl:13-13`. -/
def P_floatfuncs_13 : Prop := ∀ S : FTy, ∀ (x : FV .f64) (y : FV S), HasResult (Bits.flipsignReal x y)

theorem p_floatfuncs_13_proven : P_floatfuncs_13 := by simp [P_floatfuncs_13, HasResult]

/-- `signbit(x::Float64)` at `base/floatfuncs.jl:15-15`. -/
def P_floatfuncs_15 : Prop := ∀ x : FV .f64, HasResult (Bits.signbitBits x)

theorem p_floatfuncs_15_proven : P_floatfuncs_15 := by simp [P_floatfuncs_15, HasResult]

/-- `signbit(x::Float32)` at `base/floatfuncs.jl:16-16`. -/
def P_floatfuncs_16 : Prop := ∀ x : FV .f32, HasResult (Bits.signbitBits x)

theorem p_floatfuncs_16_proven : P_floatfuncs_16 := by simp [P_floatfuncs_16, HasResult]

/-- `signbit(x::Float16)` at `base/floatfuncs.jl:17-17`. -/
def P_floatfuncs_17 : Prop := ∀ x : FV .f16, HasResult (Bits.signbitBits x)

theorem p_floatfuncs_17_proven : P_floatfuncs_17 := by simp [P_floatfuncs_17, HasResult]

/-- `maxintfloat(::Type{Float32})` at `base/floatfuncs.jl:35-35`. -/
def P_floatfuncs_35 : Prop := ∀ _u : Unit, HasResult (Bits.maxintfloat .f32)

theorem p_floatfuncs_35_proven : P_floatfuncs_35 := by simp [P_floatfuncs_35, HasResult]

/-- `maxintfloat(::Type{Float16})` at `base/floatfuncs.jl:36-36`. -/
def P_floatfuncs_36 : Prop := ∀ _u : Unit, HasResult (Bits.maxintfloat .f16)

theorem p_floatfuncs_36_proven : P_floatfuncs_36 := by simp [P_floatfuncs_36, HasResult]

/-- `maxintfloat(x::T) where {T<:AbstractFloat}` at `base/floatfuncs.jl:37-37`. -/
def P_floatfuncs_37 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (Bits.maxintfloatOf x)

theorem p_floatfuncs_37_proven : P_floatfuncs_37 := by simp [P_floatfuncs_37, HasResult]

/-- `maxintfloat(::Type{S}, ::Type{T}) where {S<:AbstractFloat, T<:Integer}` at `base/floatfuncs.jl:46-46`. -/
def P_floatfuncs_46 : Prop := ∀ (T : FTy) (t : IntTy), HasResult (Bits.maxintfloatInt T t)

theorem p_floatfuncs_46_proven : P_floatfuncs_46 := by simp [P_floatfuncs_46, HasResult]

/-- `maxintfloat()` at `base/floatfuncs.jl:47-47`. -/
def P_floatfuncs_47 : Prop := ∀ _u : Unit, HasResult (Bits.maxintfloatDefault)

theorem p_floatfuncs_47_proven : P_floatfuncs_47 := by simp [P_floatfuncs_47, HasResult]

/-- `maxintfloat(::Type{Union{}}, slurp...)` at `base/floatfuncs.jl:48-48`. -/
def P_floatfuncs_48 : Prop := ∀ T : FTy, HasResult (Bits.maxintfloatBottom (α := FV T))

theorem p_floatfuncs_48_proven : P_floatfuncs_48 := by simp [P_floatfuncs_48, HasResult]

/-- `maxintfloat(x, ::Type{Union{}}, slurp...)` at `base/floatfuncs.jl:49-49`. -/
def P_floatfuncs_49 : Prop := ∀ T : FTy, HasResult (Bits.maxintfloatBottom (α := FV T))

theorem p_floatfuncs_49_proven : P_floatfuncs_49 := by simp [P_floatfuncs_49, HasResult]

/-- `round(x::Real, r::RoundingMode=RoundNearest; digits::Union{Nothing,Integer}=nothing, sigdigits::Union{Nothing,Integer}=nothing, base::Union{Nothing,Integer}=nothing)` at `base/floatfuncs.jl:56-79`. -/
def P_floatfuncs_56 : Prop := ∀ T : FTy, ∀ (x : FV T) (r : Mode) (d s b : Option Int), HasResult (FloatFuncs.roundKw x r d s b (fun a => .ok a))

theorem p_floatfuncs_56_proven : P_floatfuncs_56 := by simp [P_floatfuncs_56, HasResult]

/-- `_round_invstep(x, invstep, r::RoundingMode)` at `base/floatfuncs.jl:82-88`. -/
def P_floatfuncs_82 : Prop := ∀ T : FTy, ∀ (x step : FV T) (r : Mode), HasResult (FloatFuncs.roundInvstep x step r)

theorem p_floatfuncs_82_proven : P_floatfuncs_82 := by simp [P_floatfuncs_82, HasResult]

/-- `_round_invstepsqrt(x, invstepsqrt, r::RoundingMode)` at `base/floatfuncs.jl:92-98`. -/
def P_floatfuncs_92 : Prop := ∀ T : FTy, ∀ (x step : FV T) (r : Mode), HasResult (FloatFuncs.roundInvstepsqrt x step r)

theorem p_floatfuncs_92_proven : P_floatfuncs_92 := by simp [P_floatfuncs_92, HasResult]

/-- `hidigit(x::Integer, base)` at `base/floatfuncs.jl:132-132`. -/
def P_floatfuncs_132 : Prop := ∀ (x : Int) (b : Nat), HasResult (FloatFuncs.hidigitInt x b)

theorem p_floatfuncs_132_proven : P_floatfuncs_132 := by simp [P_floatfuncs_132, HasResult]

/-- `hidigit(x::AbstractFloat, base)` at `base/floatfuncs.jl:133-142`. -/
def P_floatfuncs_133 : Prop := ∀ T : FTy, ∀ (x : FV T) (b : Int), HasResult (FloatFuncs.hidigit x b (fun a => .ok a))

theorem p_floatfuncs_133_proven : P_floatfuncs_133 := by simp [P_floatfuncs_133, HasResult]

/-- `hidigit(x::Real, base)` at `base/floatfuncs.jl:143-143`. -/
def P_floatfuncs_143 : Prop := ∀ T : FTy, ∀ (x : FV T) (b : Int), HasResult (FloatFuncs.hidigitReal (fun z => z) x b (fun a => .ok a))

theorem p_floatfuncs_143_proven : P_floatfuncs_143 := by simp [P_floatfuncs_143, HasResult]

/-- `_round_sigdigits(x, r::RoundingMode, sigdigits::Integer, base)` at `base/floatfuncs.jl:145-148`. -/
def P_floatfuncs_145 : Prop := ∀ T : FTy, ∀ (x : FV T) (r : Mode) (s b : Int), HasResult (FloatFuncs.roundSigdigits x r s b (fun a => .ok a))

theorem p_floatfuncs_145_proven : P_floatfuncs_145 := by simp [P_floatfuncs_145, HasResult]

/-- `round(x::AbstractFloat, ::RoundingMode{:NearestTiesAway})` at `base/floatfuncs.jl:151-154`. -/
def P_floatfuncs_151 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (FloatFuncs.roundTiesAway x)

theorem p_floatfuncs_151_proven : P_floatfuncs_151 := by simp [P_floatfuncs_151, HasResult]

/-- `round(x::T, ::RoundingMode{:NearestTiesUp}) where {T <: AbstractFloat}` at `base/floatfuncs.jl:156-158`. -/
def P_floatfuncs_156 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (FloatFuncs.roundTiesUp x)

theorem p_floatfuncs_156_proven : P_floatfuncs_156 := by simp [P_floatfuncs_156, HasResult]

/-- `Base.round(x::AbstractFloat, ::typeof(RoundFromZero))` at `base/floatfuncs.jl:160-162`. -/
def P_floatfuncs_160 : Prop := ∀ T : FTy, ∀ x : FV T, HasResult (FloatFuncs.roundFromZero x)

theorem p_floatfuncs_160_proven : P_floatfuncs_160 := by simp [P_floatfuncs_160, HasResult]

/-- `isapprox(x::Number, y::Number; atol::Number=zero(real(x)), rtol::Real=rtoldefault(x,y,atol), nans::Bool=false, norm::Function=abs)` at `base/floatfuncs.jl:230-237`. -/
def P_floatfuncs_230 : Prop := ∀ T : FTy, ∀ x y atol rtol : FV T, ∀ nans : Bool, HasResult (FloatFuncs.isapproxF x y atol rtol nans)

theorem p_floatfuncs_230_proven : P_floatfuncs_230 := by simp [P_floatfuncs_230, HasResult]

/-- `_uabsdiff(x::Integer, y::Integer)` at `base/floatfuncs.jl:244-244`. -/
def P_floatfuncs_244 : Prop := ∀ x y : Int, HasResult (FloatFuncs.uabsdiff x y)

theorem p_floatfuncs_244_proven : P_floatfuncs_244 := by simp [P_floatfuncs_244, HasResult]

/-- `_uabsdiff(x::Bool, y::BitInteger)` at `base/floatfuncs.jl:246-246`. -/
def P_floatfuncs_246 : Prop := ∀ x y : Int, HasResult (FloatFuncs.uabsdiff x y)

theorem p_floatfuncs_246_proven : P_floatfuncs_246 := by simp [P_floatfuncs_246, HasResult]

/-- `_uabsdiff(x::BitInteger, y::Bool)` at `base/floatfuncs.jl:247-247`. -/
def P_floatfuncs_247 : Prop := ∀ x y : Int, HasResult (FloatFuncs.uabsdiff x y)

theorem p_floatfuncs_247_proven : P_floatfuncs_247 := by simp [P_floatfuncs_247, HasResult]

/-- `_uabsdiff(x::BitUnsigned, y::BitUnsigned)` at `base/floatfuncs.jl:249-252`. -/
def P_floatfuncs_249 : Prop := ∀ (t : IntTy) (x y : Int), HasResult (FloatFuncs.uabsdiffUU t x y)

theorem p_floatfuncs_249_proven : P_floatfuncs_249 := by simp [P_floatfuncs_249, HasResult]

/-- `_uabsdiff(x::BitSigned, y::BitSigned)` at `base/floatfuncs.jl:253-257`. -/
def P_floatfuncs_253 : Prop := ∀ (t : IntTy) (x y : Int), HasResult (FloatFuncs.uabsdiffSS t x y)

theorem p_floatfuncs_253_proven : P_floatfuncs_253 := by simp [P_floatfuncs_253, HasResult]

/-- `_mixed_uabsdiff(x::BitSigned, y::BitUnsigned)` at `base/floatfuncs.jl:261-267`. -/
def P_floatfuncs_261 : Prop := ∀ (t : IntTy) (x y : Int), HasResult (FloatFuncs.mixedUabsdiff t x y)

theorem p_floatfuncs_261_proven : P_floatfuncs_261 := by simp [P_floatfuncs_261, HasResult]

/-- `_uabsdiff(x::BitSigned, y::BitUnsigned)` at `base/floatfuncs.jl:269-272`. -/
def P_floatfuncs_269 : Prop := ∀ (t : IntTy) (x y : Int), HasResult (FloatFuncs.uabsdiffSU t x y)

theorem p_floatfuncs_269_proven : P_floatfuncs_269 := by simp [P_floatfuncs_269, HasResult]

/-- `_uabsdiff(x::BitUnsigned, y::BitSigned)` at `base/floatfuncs.jl:273-273`. -/
def P_floatfuncs_273 : Prop := ∀ (t : IntTy) (x y : Int), HasResult (FloatFuncs.uabsdiffSU t y x)

theorem p_floatfuncs_273_proven : P_floatfuncs_273 := by simp [P_floatfuncs_273, HasResult]

/-- `_uabsdiff_le(x::Integer, y::Integer, b::Real)` at `base/floatfuncs.jl:275-275`. -/
def P_floatfuncs_275 : Prop := ∀ x y b : Int, HasResult (FloatFuncs.uabsdiffLe x y b)

theorem p_floatfuncs_275_proven : P_floatfuncs_275 := by simp [P_floatfuncs_275, HasResult]

/-- `_widesum_le(m::T, u::T, b::Real) where {T<:BitUnsigned}` at `base/floatfuncs.jl:277-277`. -/
def P_floatfuncs_277 : Prop := ∀ m u b : Int, HasResult (FloatFuncs.widesumLe m u b)

theorem p_floatfuncs_277_proven : P_floatfuncs_277 := by simp [P_floatfuncs_277, HasResult]

/-- `_uabsdiff_le(x::BitSigned, y::BitUnsigned, b::Real)` at `base/floatfuncs.jl:278-283`. -/
def P_floatfuncs_278 : Prop := ∀ (t : IntTy) (x y b : Int), HasResult (FloatFuncs.uabsdiffLeSU t x y b 1)

theorem p_floatfuncs_278_proven : P_floatfuncs_278 := by simp [P_floatfuncs_278, HasResult]

/-- `_uabsdiff_le(x::BitUnsigned, y::BitSigned, b::Real)` at `base/floatfuncs.jl:284-284`. -/
def P_floatfuncs_284 : Prop := ∀ (t : IntTy) (x y b : Int), HasResult (FloatFuncs.uabsdiffLeSU t y x b 1)

theorem p_floatfuncs_284_proven : P_floatfuncs_284 := by simp [P_floatfuncs_284, HasResult]

/-- `_scaled_rtol(rtol::Real, scale::Integer)` at `base/floatfuncs.jl:286-286`. -/
def P_floatfuncs_286 : Prop := ∀ x y : Int, HasResult (FloatFuncs.scaledRtolReal (fun a b => a * b) x y)

theorem p_floatfuncs_286_proven : P_floatfuncs_286 := by simp [P_floatfuncs_286, HasResult]

/-- `_scaled_rtol(rtol::BitInteger, scale::BitInteger)` at `base/floatfuncs.jl:287-287`. -/
def P_floatfuncs_287 : Prop := ∀ (t : IntTy) (x y : Int), HasResult (FloatFuncs.scaledRtolInt t x y)

theorem p_floatfuncs_287_proven : P_floatfuncs_287 := by simp [P_floatfuncs_287, HasResult]

/-- `isapprox(x::Integer, y::Integer; atol::Real=0, rtol::Real=rtoldefault(x,y,atol), nans::Bool=false, norm::Function=abs)` at `base/floatfuncs.jl:289-303`. -/
def P_floatfuncs_289 : Prop := ∀ (t : IntTy) (x y a r : Int), HasResult (FloatFuncs.isapproxInt t x y a r)

theorem p_floatfuncs_289_proven : P_floatfuncs_289 := by simp [P_floatfuncs_289, HasResult]

/-- `isapprox(y; kwargs...)` at `base/floatfuncs.jl:315-315`. -/
def P_floatfuncs_315 : Prop := ∀ (α : Type) (f : α → α → Bool) (x y : α), HasResult (FloatFuncs.isapproxCurried f y x)

theorem p_floatfuncs_315_proven : P_floatfuncs_315 := by simp [P_floatfuncs_315, HasResult]

/-- `≉(args...; kws...)` at `base/floatfuncs.jl:323-323`. -/
def P_floatfuncs_323 : Prop := ∀ (α : Type) (f : α → α → Bool) (x y : α), HasResult (FloatFuncs.napprox f x y)

theorem p_floatfuncs_323_proven : P_floatfuncs_323 := by simp [P_floatfuncs_323, HasResult]

/-- `rtoldefault(::Type{T}) where {T<:AbstractFloat}` at `base/floatfuncs.jl:326-326`. -/
def P_floatfuncs_326 : Prop := ∀ _u : Unit, HasResult (FloatFuncs.rtoldefaultT .f64)

theorem p_floatfuncs_326_proven : P_floatfuncs_326 := by simp [P_floatfuncs_326, HasResult]

/-- `rtoldefault(::Type{<:Real})` at `base/floatfuncs.jl:327-327`. -/
def P_floatfuncs_327 : Prop := ∀ _u : Unit, HasResult (FloatFuncs.rtoldefaultReal)

theorem p_floatfuncs_327_proven : P_floatfuncs_327 := by simp [P_floatfuncs_327, HasResult]

/-- `rtoldefault(::Type{T}) where {T<:Number}` at `base/floatfuncs.jl:330-334`. -/
def P_floatfuncs_330 : Prop := ∀ (α : Type) [DecidableEq α] (one : α → α) (rt : α → Jl (FV .f64)) (x : α), HasResult (FloatFuncs.rtoldefaultNumber one rt x)

theorem p_floatfuncs_330_proven : P_floatfuncs_330 := by simp [P_floatfuncs_330, HasResult]

/-- `rtoldefault(x::Union{T,Type{T}}, y::Union{S,Type{S}}, atol::Number) where {T<:Number,S<:Number}` at `base/floatfuncs.jl:335-338`. -/
def P_floatfuncs_335 : Prop := ∀ T : FTy, ∀ (x y : Option (FV T)) (p : Bool), HasResult (FloatFuncs.rtoldefault3 x y p)

theorem p_floatfuncs_335_proven : P_floatfuncs_335 := by simp [P_floatfuncs_335, HasResult]

/-- `fma_emulated(a::T, b::T, c::T) where {T<:Union{Float16, Float32}}` at `base/floatfuncs.jl:350-361`. -/
def P_floatfuncs_350 : Prop := ∀ T : FTy, T = .f16 ∨ T = .f32 → ∀ a b c : FV T, HasResult (FloatFuncs.fmaEmulatedNarrow a b c)

theorem p_floatfuncs_350_proven : P_floatfuncs_350 := by simp [P_floatfuncs_350, HasResult]

/-- `splitbits(x::Float64)` at `base/floatfuncs.jl:364-367`. -/
def P_floatfuncs_364 : Prop := ∀ x : FV .f64, HasResult (FloatFuncs.splitbits x)

theorem p_floatfuncs_364_proven : P_floatfuncs_364 := by simp [P_floatfuncs_364, HasResult]

/-- `two_mul(x::T, y::T) where {T<:Number}` at `base/floatfuncs.jl:371-374`. -/
def P_floatfuncs_371 : Prop := ∀ T : FTy, ∀ x y : FV T, HasResult (FloatFuncs.twoMul x y)

theorem p_floatfuncs_371_proven : P_floatfuncs_371 := by simp [P_floatfuncs_371, HasResult]

/-- `two_mul(x::Float64, y::Float64)` at `base/floatfuncs.jl:376-388`. -/
def P_floatfuncs_376 : Prop := ∀ (native : Bool) (x y : FV .f64), HasResult (FloatFuncs.twoMul64 native x y)

theorem p_floatfuncs_376_proven : P_floatfuncs_376 := by simp [P_floatfuncs_376, HasResult]

/-- `two_mul(x::T, y::T) where T<:Union{Float16, Float32}` at `base/floatfuncs.jl:390-398`. -/
def P_floatfuncs_390 : Prop := ∀ T : FTy, T = .f16 ∨ T = .f32 → ∀ x y : FV T, HasResult (FloatFuncs.twoMul x y)

theorem p_floatfuncs_390_proven : P_floatfuncs_390 := by simp [P_floatfuncs_390, HasResult]

/-- `fma_correction(abhi::Float64, ablo::Float64, c::Float64, r::Float64)` at `base/floatfuncs.jl:403-411`. -/
def P_floatfuncs_403 : Prop := ∀ a b c r : FV .f64, HasResult (FloatFuncs.fmaCorrection a b c r)

theorem p_floatfuncs_403_proven : P_floatfuncs_403 := by simp [P_floatfuncs_403, HasResult]

/-- `fma_emulated(a::Float64, b::Float64,c::Float64)` at `base/floatfuncs.jl:413-460`. -/
def P_floatfuncs_413 : Prop := ∀ (native : Bool) (a b c : FV .f64), HasResult (FloatFuncs.fmaEmulated64 native a b c)

theorem p_floatfuncs_413_proven : P_floatfuncs_413 := by simp [P_floatfuncs_413, HasResult]

/-- `fma(x::T, y::T, z::T) where {T<:IEEEFloat}` at `base/floatfuncs.jl:464-466`. -/
def P_floatfuncs_464 : Prop := ∀ T : FTy, ∀ (native : Bool) (a b c : FV T), HasResult (FloatFuncs.fmaDispatch native a b c)

theorem p_floatfuncs_464_proven : P_floatfuncs_464 := by simp [P_floatfuncs_464, HasResult]

/-- `rounds_to_nearest(::RoundingMode)` at `base/rounding.jl:115-115`. -/
def P_rounding_115 : Prop := ∀ m : Mode, HasResult (Rounding.roundsToNearest m)

theorem p_rounding_115_proven : P_rounding_115 := by simp [P_rounding_115, HasResult]

/-- `rounds_to_nearest(::RoundingMode{:Nearest})` at `base/rounding.jl:116-116`. -/
def P_rounding_116 : Prop := ∀ _u : Unit, HasResult (Rounding.roundsToNearest .Nearest)

theorem p_rounding_116_proven : P_rounding_116 := by simp [P_rounding_116, HasResult]

/-- `rounds_to_nearest(::RoundingMode{:NearestTiesUp})` at `base/rounding.jl:117-117`. -/
def P_rounding_117 : Prop := ∀ _u : Unit, HasResult (Rounding.roundsToNearest .NearestTiesUp)

theorem p_rounding_117_proven : P_rounding_117 := by simp [P_rounding_117, HasResult]

/-- `rounds_to_nearest(::RoundingMode{:NearestTiesAway})` at `base/rounding.jl:118-118`. -/
def P_rounding_118 : Prop := ∀ _u : Unit, HasResult (Rounding.roundsToNearest .NearestTiesAway)

theorem p_rounding_118_proven : P_rounding_118 := by simp [P_rounding_118, HasResult]

/-- `rounds_away_from_zero(::RoundingMode{:Up}, sign_bit::Bool)` at `base/rounding.jl:119-119`. -/
def P_rounding_119 : Prop := ∀ s : Bool, HasResult (Rounding.roundsAwayFromZero .Up s)

theorem p_rounding_119_proven : P_rounding_119 := by simp [P_rounding_119, HasResult]

/-- `rounds_away_from_zero(::RoundingMode{:Down}, sign_bit::Bool)` at `base/rounding.jl:120-120`. -/
def P_rounding_120 : Prop := ∀ s : Bool, HasResult (Rounding.roundsAwayFromZero .Down s)

theorem p_rounding_120_proven : P_rounding_120 := by simp [P_rounding_120, HasResult]

/-- `rounds_away_from_zero(::RoundingMode{:FromZero}, ::Bool)` at `base/rounding.jl:121-121`. -/
def P_rounding_121 : Prop := ∀ s : Bool, HasResult (Rounding.roundsAwayFromZero .FromZero s)

theorem p_rounding_121_proven : P_rounding_121 := by simp [P_rounding_121, HasResult]

/-- `rounds_away_from_zero(::RoundingMode{:ToZero}, ::Bool)` at `base/rounding.jl:122-122`. -/
def P_rounding_122 : Prop := ∀ s : Bool, HasResult (Rounding.roundsAwayFromZero .ToZero s)

theorem p_rounding_122_proven : P_rounding_122 := by simp [P_rounding_122, HasResult]

/-- `tie_breaker_is_to_even(::RoundingMode{:Nearest})` at `base/rounding.jl:123-123`. -/
def P_rounding_123 : Prop := ∀ _u : Unit, HasResult (Rounding.tieBreakerIsToEven .Nearest)

theorem p_rounding_123_proven : P_rounding_123 := by simp [P_rounding_123, HasResult]

/-- `tie_breaker_is_to_even(::RoundingMode{:NearestTiesUp})` at `base/rounding.jl:124-124`. -/
def P_rounding_124 : Prop := ∀ _u : Unit, HasResult (Rounding.tieBreakerIsToEven .NearestTiesUp)

theorem p_rounding_124_proven : P_rounding_124 := by simp [P_rounding_124, HasResult]

/-- `tie_breaker_is_to_even(::RoundingMode{:NearestTiesAway})` at `base/rounding.jl:125-125`. -/
def P_rounding_125 : Prop := ∀ _u : Unit, HasResult (Rounding.tieBreakerIsToEven .NearestTiesAway)

theorem p_rounding_125_proven : P_rounding_125 := by simp [P_rounding_125, HasResult]

/-- `tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesUp}, sign_bit::Bool)` at `base/rounding.jl:126-126`. -/
def P_rounding_126 : Prop := ∀ s : Bool, HasResult (Rounding.tieBreakerRoundsAwayFromZero .NearestTiesUp s)

theorem p_rounding_126_proven : P_rounding_126 := by simp [P_rounding_126, HasResult]

/-- `tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesAway}, ::Bool)` at `base/rounding.jl:127-127`. -/
def P_rounding_127 : Prop := ∀ s : Bool, HasResult (Rounding.tieBreakerRoundsAwayFromZero .NearestTiesAway s)

theorem p_rounding_127_proven : P_rounding_127 := by simp [P_rounding_127, HasResult]

/-- `rounds_to_nearest(t::Tuple{Any,Bool})` at `base/rounding.jl:129-129`. -/
def P_rounding_129 : Prop := ∀ t : Mode × Bool, HasResult (Rounding.roundsToNearestT t)

theorem p_rounding_129_proven : P_rounding_129 := by simp [P_rounding_129, HasResult]

/-- `rounds_away_from_zero(t::Tuple{Any,Bool})` at `base/rounding.jl:130-130`. -/
def P_rounding_130 : Prop := ∀ t : Mode × Bool, HasResult (Rounding.roundsAwayFromZeroT t)

theorem p_rounding_130_proven : P_rounding_130 := by simp [P_rounding_130, HasResult]

/-- `tie_breaker_is_to_even(t::Tuple{Any,Bool})` at `base/rounding.jl:131-131`. -/
def P_rounding_131 : Prop := ∀ t : Mode × Bool, HasResult (Rounding.tieBreakerIsToEvenT t)

theorem p_rounding_131_proven : P_rounding_131 := by simp [P_rounding_131, HasResult]

/-- `tie_breaker_rounds_away_from_zero(t::Tuple{Any,Bool})` at `base/rounding.jl:132-132`. -/
def P_rounding_132 : Prop := ∀ t : Mode × Bool, HasResult (Rounding.tieBreakerRoundsAwayFromZeroT t)

theorem p_rounding_132_proven : P_rounding_132 := by simp [P_rounding_132, HasResult]

/-- `correct_rounding_requires_increment(x, rounding_mode, sign_bit::Bool)` at `base/rounding.jl:138-168`. -/
def P_rounding_138 : Prop := ∀ (x : Rounding.Bit → Bool) (m : Mode) (s : Bool), HasResult (Rounding.correctRoundingRequiresIncrement x m s)

theorem p_rounding_138_proven : P_rounding_138 := by simp [P_rounding_138, HasResult]

/-- `to_fenv(::RoundingMode{:Nearest})` at `base/rounding.jl:170-170`. -/
def P_rounding_170 : Prop := ∀ _u : Unit, HasResult (Rounding.toFenv .Nearest)

theorem p_rounding_170_proven : P_rounding_170 := by simp [P_rounding_170, HasResult]

/-- `to_fenv(::RoundingMode{:ToZero})` at `base/rounding.jl:171-171`. -/
def P_rounding_171 : Prop := ∀ _u : Unit, HasResult (Rounding.toFenv .ToZero)

theorem p_rounding_171_proven : P_rounding_171 := by simp [P_rounding_171, HasResult]

/-- `to_fenv(::RoundingMode{:Up})` at `base/rounding.jl:172-172`. -/
def P_rounding_172 : Prop := ∀ _u : Unit, HasResult (Rounding.toFenv .Up)

theorem p_rounding_172_proven : P_rounding_172 := by simp [P_rounding_172, HasResult]

/-- `to_fenv(::RoundingMode{:Down})` at `base/rounding.jl:173-173`. -/
def P_rounding_173 : Prop := ∀ _u : Unit, HasResult (Rounding.toFenv .Down)

theorem p_rounding_173_proven : P_rounding_173 := by simp [P_rounding_173, HasResult]

/-- `from_fenv(r::Integer)` at `base/rounding.jl:175-187`. -/
def P_rounding_175 : Prop := ∀ r : Int, HasResult (Rounding.fromFenv r)

theorem p_rounding_175_proven : P_rounding_175 := by simp [P_rounding_175, HasResult]

/-- `setrounding_raw(::Type{<:Union{Float32,Float64}}, i::Integer)` at `base/rounding.jl:219-219`. -/
def P_rounding_219 : Prop := ∀ (i : Int) (e : Rounding.FEnv), HasResult (Rounding.setroundingRaw i e)

theorem p_rounding_219_proven : P_rounding_219 := by simp [P_rounding_219, HasResult]

/-- `rounding_raw(::Type{<:Union{Float32,Float64}})` at `base/rounding.jl:220-220`. -/
def P_rounding_220 : Prop := ∀ e : Rounding.FEnv, HasResult (Rounding.roundingRaw e)

theorem p_rounding_220_proven : P_rounding_220 := by simp [P_rounding_220, HasResult]

/-- `rounding(::Type{T}) where {T<:Union{Float32,Float64}}` at `base/rounding.jl:222-222`. -/
def P_rounding_222 : Prop := ∀ e : Rounding.FEnv, HasResult (Rounding.rounding e)

theorem p_rounding_222_proven : P_rounding_222 := by simp [P_rounding_222, HasResult]

/-- `rounding(::Type{Union{}}, slurp...)` at `base/rounding.jl:223-223`. -/
def P_rounding_223 : Prop := ∀ e : Rounding.FEnv, HasResult (Rounding.bottomMethodError (α := Mode) "rounding")

theorem p_rounding_223_proven : P_rounding_223 := by simp [P_rounding_223, HasResult]

/-- `setrounding(f::Function, ::Type{T}, rounding::RoundingMode) where T` at `base/rounding.jl:238-246`. -/
def P_rounding_238 : Prop := ∀ (f : Rounding.FEnv → Jl Unit × Rounding.FEnv) (m : Mode) (e : Rounding.FEnv), HasResult (Rounding.setroundingF Rounding.roundingRaw (fun i s => (Rounding.setroundingRaw i s).2) Rounding.setroundingFloat f m e)

theorem p_rounding_238_proven : P_rounding_238 := by simp [P_rounding_238, HasResult]

/-- `setrounding(f, ::Type{Union{}}, slurp...)` at `base/rounding.jl:247-247`. -/
def P_rounding_247 : Prop := ∀ e : Rounding.FEnv, HasResult (Rounding.bottomMethodError (α := Unit) "setrounding")

theorem p_rounding_247_proven : P_rounding_247 := by simp [P_rounding_247, HasResult]

/-- `setrounding_raw(f::Function, ::Type{T}, rounding) where T` at `base/rounding.jl:248-256`. -/
def P_rounding_248 : Prop := ∀ (f : Rounding.FEnv → Jl Unit × Rounding.FEnv) (i : Int) (e : Rounding.FEnv), HasResult (Rounding.setroundingRawF Rounding.roundingRaw (fun j s => (Rounding.setroundingRaw j s).2) f i e)

theorem p_rounding_248_proven : P_rounding_248 := by simp [P_rounding_248, HasResult]

/-- `(::Type{T})(x::Real, r::RoundingMode) where {T<:AbstractFloat}` at `base/rounding.jl:267-267`. -/
def P_rounding_267 : Prop := ∀ T S : FTy, ∀ (x : FV S) (m : Mode), HasResult (Rounding.convertRounding T x m)

theorem p_rounding_267_proven : P_rounding_267 := by simp [P_rounding_267, HasResult]

/-- `_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Nearest}) where {T<:AbstractFloat}` at `base/rounding.jl:269-269`. -/
def P_rounding_269 : Prop := ∀ T S : FTy, ∀ x : FV S, HasResult (Rounding.convertRounding T x .Nearest)

theorem p_rounding_269_proven : P_rounding_269 := by simp [P_rounding_269, HasResult]

/-- `_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Down}) where T<:AbstractFloat` at `base/rounding.jl:270-273`. -/
def P_rounding_270 : Prop := ∀ T S : FTy, ∀ x : FV S, HasResult (Rounding.convertRounding T x .Down)

theorem p_rounding_270_proven : P_rounding_270 := by simp [P_rounding_270, HasResult]

/-- `_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Up}) where T<:AbstractFloat` at `base/rounding.jl:274-277`. -/
def P_rounding_274 : Prop := ∀ T S : FTy, ∀ x : FV S, HasResult (Rounding.convertRounding T x .Up)

theorem p_rounding_274_proven : P_rounding_274 := by simp [P_rounding_274, HasResult]

/-- `_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:ToZero}) where T<:AbstractFloat` at `base/rounding.jl:278-285`. -/
def P_rounding_278 : Prop := ∀ T S : FTy, ∀ x : FV S, HasResult (Rounding.convertRounding T x .ToZero)

theorem p_rounding_278_proven : P_rounding_278 := by simp [P_rounding_278, HasResult]

/-- `_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:FromZero}) where T<:AbstractFloat` at `base/rounding.jl:286-293`. -/
def P_rounding_286 : Prop := ∀ T S : FTy, ∀ x : FV S, HasResult (Rounding.convertRounding T x .FromZero)

theorem p_rounding_286_proven : P_rounding_286 := by simp [P_rounding_286, HasResult]

/-- `set_zero_subnormals(yes::Bool)` at `base/rounding.jl:313-313`. -/
def P_rounding_313 : Prop := ∀ (yes : Bool) (e : Rounding.FEnv), HasResult (Rounding.setZeroSubnormals yes e)

theorem p_rounding_313_proven : P_rounding_313 := by simp [P_rounding_313, HasResult]

/-- `get_zero_subnormals()` at `base/rounding.jl:325-325`. -/
def P_rounding_325 : Prop := ∀ e : Rounding.FEnv, HasResult (Rounding.getZeroSubnormals e)

theorem p_rounding_325_proven : P_rounding_325 := by simp [P_rounding_325, HasResult]

/-- `trunc(x; kws...)` at `base/rounding.jl:480-480`. -/
def P_rounding_480 : Prop := ∀ (α β : Type) (f : α → Mode → β) (x : α), HasResult (Rounding.roundForward f x .ToZero)

theorem p_rounding_480_proven : P_rounding_480 := by simp [P_rounding_480, HasResult]

/-- `floor(x; kws...)` at `base/rounding.jl:481-481`. -/
def P_rounding_481 : Prop := ∀ (α β : Type) (f : α → Mode → β) (x : α), HasResult (Rounding.roundForward f x .Down)

theorem p_rounding_481_proven : P_rounding_481 := by simp [P_rounding_481, HasResult]

/-- `ceil(x; kws...)` at `base/rounding.jl:482-482`. -/
def P_rounding_482 : Prop := ∀ (α β : Type) (f : α → Mode → β) (x : α), HasResult (Rounding.roundForward f x .Up)

theorem p_rounding_482_proven : P_rounding_482 := by simp [P_rounding_482, HasResult]

/-- `round(x; kws...)` at `base/rounding.jl:483-483`. -/
def P_rounding_483 : Prop := ∀ (α β : Type) (f : α → Mode → β) (x : α), HasResult (Rounding.roundForward f x .Nearest)

theorem p_rounding_483_proven : P_rounding_483 := by simp [P_rounding_483, HasResult]

/-- `trunc(::Type{T}, x) where T` at `base/rounding.jl:485-485`. -/
def P_rounding_485 : Prop := ∀ (α β γ : Type) (f : α → β → Mode → γ) (T : α) (x : β), HasResult (Rounding.roundTypeForward f T x .ToZero)

theorem p_rounding_485_proven : P_rounding_485 := by simp [P_rounding_485, HasResult]

/-- `floor(::Type{T}, x) where T` at `base/rounding.jl:486-486`. -/
def P_rounding_486 : Prop := ∀ (α β γ : Type) (f : α → β → Mode → γ) (T : α) (x : β), HasResult (Rounding.roundTypeForward f T x .Down)

theorem p_rounding_486_proven : P_rounding_486 := by simp [P_rounding_486, HasResult]

/-- `ceil(::Type{T}, x) where T` at `base/rounding.jl:487-487`. -/
def P_rounding_487 : Prop := ∀ (α β γ : Type) (f : α → β → Mode → γ) (T : α) (x : β), HasResult (Rounding.roundTypeForward f T x .Up)

theorem p_rounding_487_proven : P_rounding_487 := by simp [P_rounding_487, HasResult]

/-- `round(::Type{T}, x) where T` at `base/rounding.jl:488-488`. -/
def P_rounding_488 : Prop := ∀ (α β γ : Type) (f : α → β → Mode → γ) (T : α) (x : β), HasResult (Rounding.roundTypeForward f T x .Nearest)

theorem p_rounding_488_proven : P_rounding_488 := by simp [P_rounding_488, HasResult]

/-- `round(::Type{T}, x, r::RoundingMode) where T` at `base/rounding.jl:490-490`. -/
def P_rounding_490 : Prop := ∀ (α β γ : Type) (r : α → Mode → β) (c : β → α → Mode → γ) (x : α) (m : Mode), HasResult (Rounding.roundTypeConvert r c x m)

theorem p_rounding_490_proven : P_rounding_490 := by simp [P_rounding_490, HasResult]

/-- `trunc(::Type{Union{}}, slurp...; kwargs...)` at `base/rounding.jl:492-492`. -/
def P_rounding_492 : Prop := ∀ x : Int, HasResult (Rounding.bottomRoundError (α := Int) "trunc")

theorem p_rounding_492_proven : P_rounding_492 := by simp [P_rounding_492, HasResult]

/-- `floor(::Type{Union{}}, slurp...; kwargs...)` at `base/rounding.jl:493-493`. -/
def P_rounding_493 : Prop := ∀ x : Int, HasResult (Rounding.bottomRoundError (α := Int) "floor")

theorem p_rounding_493_proven : P_rounding_493 := by simp [P_rounding_493, HasResult]

/-- `ceil(::Type{Union{}}, slurp...; kwargs...)` at `base/rounding.jl:494-494`. -/
def P_rounding_494 : Prop := ∀ x : Int, HasResult (Rounding.bottomRoundError (α := Int) "ceil")

theorem p_rounding_494_proven : P_rounding_494 := by simp [P_rounding_494, HasResult]

/-- `round(::Type{Union{}}, slurp...; kwargs...)` at `base/rounding.jl:495-495`. -/
def P_rounding_495 : Prop := ∀ x : Int, HasResult (Rounding.bottomRoundError (α := Int) "round")

theorem p_rounding_495_proven : P_rounding_495 := by simp [P_rounding_495, HasResult]

/-- `round(x::Integer, r::RoundingMode)` at `base/rounding.jl:497-497`. -/
def P_rounding_497 : Prop := ∀ (x : Int) (m : Mode), HasResult (Rounding.roundInteger x m)

theorem p_rounding_497_proven : P_rounding_497 := by simp [P_rounding_497, HasResult]

def entries : List Entry := [
  { id := "mathcov-special-trig-l28", juliaFile := "base/special/trig.jl"
    juliaFns := ["sin(x::T) where T<:Union{Float32, Float64}"]
    statement := "The source-order model of sin(x::T) where T<:Union{Float32, Float64} returns a result for every allowed input."
    source := "base/special/trig.jl:28-51; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_28, thm := some ``p_special_trig_28_proven },
  { id := "mathcov-special-trig-l68", juliaFile := "base/special/trig.jl"
    juliaFns := ["sin_kernel(y::DoubleFloat64)"]
    statement := "The source-order model of sin_kernel(y::DoubleFloat64) returns a result for every allowed input."
    source := "base/special/trig.jl:68-74; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_68, thm := some ``p_special_trig_68_proven },
  { id := "mathcov-special-trig-l75", juliaFile := "base/special/trig.jl"
    juliaFns := ["sin_kernel(y::Float64)"]
    statement := "The source-order model of sin_kernel(y::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:75-81; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_75, thm := some ``p_special_trig_75_proven },
  { id := "mathcov-special-trig-l84", juliaFile := "base/special/trig.jl"
    juliaFns := ["sin_kernel(x::Float32)"]
    statement := "The source-order model of sin_kernel(x::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:84-84; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_84, thm := some ``p_special_trig_84_proven },
  { id := "mathcov-special-trig-l85", juliaFile := "base/special/trig.jl"
    juliaFns := ["sin_kernel(y::DoubleFloat32)"]
    statement := "The source-order model of sin_kernel(y::DoubleFloat32) returns a result for every allowed input."
    source := "base/special/trig.jl:85-93; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_85, thm := some ``p_special_trig_85_proven },
  { id := "mathcov-special-trig-l96", juliaFile := "base/special/trig.jl"
    juliaFns := ["cos(x::T) where T<:Union{Float32, Float64}"]
    statement := "The source-order model of cos(x::T) where T<:Union{Float32, Float64} returns a result for every allowed input."
    source := "base/special/trig.jl:96-120; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_96, thm := some ``p_special_trig_96_proven },
  { id := "mathcov-special-trig-l134", juliaFile := "base/special/trig.jl"
    juliaFns := ["cos_kernel(y::DoubleFloat64)"]
    statement := "The source-order model of cos_kernel(y::DoubleFloat64) returns a result for every allowed input."
    source := "base/special/trig.jl:134-141; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_134, thm := some ``p_special_trig_134_proven },
  { id := "mathcov-special-trig-l142", juliaFile := "base/special/trig.jl"
    juliaFns := ["cos_kernel(y::Float64)"]
    statement := "The source-order model of cos_kernel(y::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:142-149; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_142, thm := some ``p_special_trig_142_proven },
  { id := "mathcov-special-trig-l152", juliaFile := "base/special/trig.jl"
    juliaFns := ["cos_kernel(x::Float32)"]
    statement := "The source-order model of cos_kernel(x::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:152-152; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_152, thm := some ``p_special_trig_152_proven },
  { id := "mathcov-special-trig-l153", juliaFile := "base/special/trig.jl"
    juliaFns := ["cos_kernel(y::DoubleFloat32)"]
    statement := "The source-order model of cos_kernel(y::DoubleFloat32) returns a result for every allowed input."
    source := "base/special/trig.jl:153-160; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_153, thm := some ``p_special_trig_153_proven },
  { id := "mathcov-special-trig-l174", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincos(x::T) where T<:Union{Float32, Float64}"]
    statement := "The source-order model of sincos(x::T) where T<:Union{Float32, Float64} returns a result for every allowed input."
    source := "base/special/trig.jl:174-200; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_174, thm := some ``p_special_trig_174_proven },
  { id := "mathcov-special-trig-l202", juliaFile := "base/special/trig.jl"
    juliaFns := ["_sincos(x::AbstractFloat)"]
    statement := "The source-order model of _sincos(x::AbstractFloat) returns a result for every allowed input."
    source := "base/special/trig.jl:202-202; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_202, thm := some ``p_special_trig_202_proven },
  { id := "mathcov-special-trig-l203", juliaFile := "base/special/trig.jl"
    juliaFns := ["_sincos(x)"]
    statement := "The source-order model of _sincos(x) returns a result for every allowed input."
    source := "base/special/trig.jl:203-203; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_203, thm := some ``p_special_trig_203_proven },
  { id := "mathcov-special-trig-l205", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincos(x)"]
    statement := "The source-order model of sincos(x) returns a result for every allowed input."
    source := "base/special/trig.jl:205-205; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_205, thm := some ``p_special_trig_205_proven },
  { id := "mathcov-special-trig-l211", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincos_kernel(y::Union{Float32, Float64, DoubleFloat32, DoubleFloat64})"]
    statement := "The source-order model of sincos_kernel(y::Union{Float32, Float64, DoubleFloat32, DoubleFloat64}) returns a result for every allowed input."
    source := "base/special/trig.jl:211-211; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_211, thm := some ``p_special_trig_211_proven },
  { id := "mathcov-special-trig-l214", juliaFile := "base/special/trig.jl"
    juliaFns := ["tan(x::T) where T<:Union{Float32, Float64}"]
    statement := "The source-order model of tan(x::T) where T<:Union{Float32, Float64} returns a result for every allowed input."
    source := "base/special/trig.jl:214-232; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_214, thm := some ``p_special_trig_214_proven },
  { id := "mathcov-special-trig-l234", juliaFile := "base/special/trig.jl"
    juliaFns := ["tan_kernel(y::Float64)"]
    statement := "The source-order model of tan_kernel(y::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:234-234; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_234, thm := some ``p_special_trig_234_proven },
  { id := "mathcov-special-trig-l235", juliaFile := "base/special/trig.jl"
    juliaFns := ["tan_kernel(y::DoubleFloat64, k)"]
    statement := "The source-order model of tan_kernel(y::DoubleFloat64, k) returns a result for every allowed input."
    source := "base/special/trig.jl:235-334; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_235, thm := some ``p_special_trig_235_proven },
  { id := "mathcov-special-trig-l336", juliaFile := "base/special/trig.jl"
    juliaFns := ["tan_kernel(y::Float32)"]
    statement := "The source-order model of tan_kernel(y::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:336-336; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_336, thm := some ``p_special_trig_336_proven },
  { id := "mathcov-special-trig-l337", juliaFile := "base/special/trig.jl"
    juliaFns := ["tan_kernel(y::DoubleFloat32, k)"]
    statement := "The source-order model of tan_kernel(y::DoubleFloat32, k) returns a result for every allowed input."
    source := "base/special/trig.jl:337-351; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_337, thm := some ``p_special_trig_337_proven },
  { id := "mathcov-special-trig-l354", juliaFile := "base/special/trig.jl"
    juliaFns := ["sin_kernel(x::Real)"]
    statement := "The source-order model of sin_kernel(x::Real) returns a result for every allowed input."
    source := "base/special/trig.jl:354-354; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_354, thm := some ``p_special_trig_354_proven },
  { id := "mathcov-special-trig-l355", juliaFile := "base/special/trig.jl"
    juliaFns := ["cos_kernel(x::Real)"]
    statement := "The source-order model of cos_kernel(x::Real) returns a result for every allowed input."
    source := "base/special/trig.jl:355-355; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_355, thm := some ``p_special_trig_355_proven },
  { id := "mathcov-special-trig-l356", juliaFile := "base/special/trig.jl"
    juliaFns := ["tan_kernel(x::Real)"]
    statement := "The source-order model of tan_kernel(x::Real) returns a result for every allowed input."
    source := "base/special/trig.jl:356-356; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_356, thm := some ``p_special_trig_356_proven },
  { id := "mathcov-special-trig-l357", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincos_kernel(x::Real)"]
    statement := "The source-order model of sincos_kernel(x::Real) returns a result for every allowed input."
    source := "base/special/trig.jl:357-357; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_357, thm := some ``p_special_trig_357_proven },
  { id := "mathcov-special-trig-l361", juliaFile := "base/special/trig.jl"
    juliaFns := ["ASIN_X_MIN_THRESHOLD(::Type{Float32})"]
    statement := "The source-order model of ASIN_X_MIN_THRESHOLD(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:361-361; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_361, thm := some ``p_special_trig_361_proven },
  { id := "mathcov-special-trig-l362", juliaFile := "base/special/trig.jl"
    juliaFns := ["ASIN_X_MIN_THRESHOLD(::Type{Float64})"]
    statement := "The source-order model of ASIN_X_MIN_THRESHOLD(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:362-362; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_362, thm := some ``p_special_trig_362_proven },
  { id := "mathcov-special-trig-l364", juliaFile := "base/special/trig.jl"
    juliaFns := ["arc_p(t::Float64)"]
    statement := "The source-order model of arc_p(t::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:364-371; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_364, thm := some ``p_special_trig_364_proven },
  { id := "mathcov-special-trig-l373", juliaFile := "base/special/trig.jl"
    juliaFns := ["arc_q(z::Float64)"]
    statement := "The source-order model of arc_q(z::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:373-379; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_373, thm := some ``p_special_trig_373_proven },
  { id := "mathcov-special-trig-l381", juliaFile := "base/special/trig.jl"
    juliaFns := ["arc_p(t::Float32)"]
    statement := "The source-order model of arc_p(t::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:381-385; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_381, thm := some ``p_special_trig_381_proven },
  { id := "mathcov-special-trig-l387", juliaFile := "base/special/trig.jl"
    juliaFns := ["arc_q(t::Float32)"]
    statement := "The source-order model of arc_q(t::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:387-387; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_387, thm := some ``p_special_trig_387_proven },
  { id := "mathcov-special-trig-l389", juliaFile := "base/special/trig.jl"
    juliaFns := ["arc_tRt(t)"]
    statement := "The source-order model of arc_tRt(t) returns a result for every allowed input."
    source := "base/special/trig.jl:389-389; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_389, thm := some ``p_special_trig_389_proven },
  { id := "mathcov-special-trig-l392", juliaFile := "base/special/trig.jl"
    juliaFns := ["asin_kernel(t::Float64, x::Float64)"]
    statement := "The source-order model of asin_kernel(t::Float64, x::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:392-418; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_392, thm := some ``p_special_trig_392_proven },
  { id := "mathcov-special-trig-l419", juliaFile := "base/special/trig.jl"
    juliaFns := ["asin_kernel(t::Float32, x::Float32)"]
    statement := "The source-order model of asin_kernel(t::Float32, x::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:419-423; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_419, thm := some ``p_special_trig_419_proven },
  { id := "mathcov-special-trig-l425", juliaFile := "base/special/trig.jl"
    juliaFns := ["asin_domain_error(x)"]
    statement := "The source-order model of asin_domain_error(x) returns a result for every allowed input."
    source := "base/special/trig.jl:425-425; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_425, thm := some ``p_special_trig_425_proven },
  { id := "mathcov-special-trig-l426", juliaFile := "base/special/trig.jl"
    juliaFns := ["asin(x::T) where T<:Union{Float32, Float64}"]
    statement := "The source-order model of asin(x::T) where T<:Union{Float32, Float64} returns a result for every allowed input."
    source := "base/special/trig.jl:426-450; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_426, thm := some ``p_special_trig_426_proven },
  { id := "mathcov-special-trig-l453", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_1_O_2_HI(::Type{Float64})"]
    statement := "The source-order model of ATAN_1_O_2_HI(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:453-453; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_453, thm := some ``p_special_trig_453_proven },
  { id := "mathcov-special-trig-l454", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_2_O_2_HI(::Type{Float64})"]
    statement := "The source-order model of ATAN_2_O_2_HI(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:454-454; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_454, thm := some ``p_special_trig_454_proven },
  { id := "mathcov-special-trig-l455", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_3_O_2_HI(::Type{Float64})"]
    statement := "The source-order model of ATAN_3_O_2_HI(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:455-455; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_455, thm := some ``p_special_trig_455_proven },
  { id := "mathcov-special-trig-l456", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_INF_HI(::Type{Float64})"]
    statement := "The source-order model of ATAN_INF_HI(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:456-456; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_456, thm := some ``p_special_trig_456_proven },
  { id := "mathcov-special-trig-l458", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_1_O_2_HI(::Type{Float32})"]
    statement := "The source-order model of ATAN_1_O_2_HI(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:458-458; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_458, thm := some ``p_special_trig_458_proven },
  { id := "mathcov-special-trig-l459", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_2_O_2_HI(::Type{Float32})"]
    statement := "The source-order model of ATAN_2_O_2_HI(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:459-459; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_459, thm := some ``p_special_trig_459_proven },
  { id := "mathcov-special-trig-l460", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_3_O_2_HI(::Type{Float32})"]
    statement := "The source-order model of ATAN_3_O_2_HI(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:460-460; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_460, thm := some ``p_special_trig_460_proven },
  { id := "mathcov-special-trig-l461", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_INF_HI(::Type{Float32})"]
    statement := "The source-order model of ATAN_INF_HI(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:461-461; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_461, thm := some ``p_special_trig_461_proven },
  { id := "mathcov-special-trig-l463", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_1_O_2_LO(::Type{Float64})"]
    statement := "The source-order model of ATAN_1_O_2_LO(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:463-463; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_463, thm := some ``p_special_trig_463_proven },
  { id := "mathcov-special-trig-l464", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_2_O_2_LO(::Type{Float64})"]
    statement := "The source-order model of ATAN_2_O_2_LO(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:464-464; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_464, thm := some ``p_special_trig_464_proven },
  { id := "mathcov-special-trig-l465", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_3_O_2_LO(::Type{Float64})"]
    statement := "The source-order model of ATAN_3_O_2_LO(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:465-465; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_465, thm := some ``p_special_trig_465_proven },
  { id := "mathcov-special-trig-l466", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_INF_LO(::Type{Float64})"]
    statement := "The source-order model of ATAN_INF_LO(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:466-466; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_466, thm := some ``p_special_trig_466_proven },
  { id := "mathcov-special-trig-l468", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_1_O_2_LO(::Type{Float32})"]
    statement := "The source-order model of ATAN_1_O_2_LO(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:468-468; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_468, thm := some ``p_special_trig_468_proven },
  { id := "mathcov-special-trig-l469", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_2_O_2_LO(::Type{Float32})"]
    statement := "The source-order model of ATAN_2_O_2_LO(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:469-469; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_469, thm := some ``p_special_trig_469_proven },
  { id := "mathcov-special-trig-l470", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_3_O_2_LO(::Type{Float32})"]
    statement := "The source-order model of ATAN_3_O_2_LO(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:470-470; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_470, thm := some ``p_special_trig_470_proven },
  { id := "mathcov-special-trig-l471", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_INF_LO(::Type{Float32})"]
    statement := "The source-order model of ATAN_INF_LO(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:471-471; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_471, thm := some ``p_special_trig_471_proven },
  { id := "mathcov-special-trig-l473", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_LARGE_X(::Type{Float64})"]
    statement := "The source-order model of ATAN_LARGE_X(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:473-473; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_473, thm := some ``p_special_trig_473_proven },
  { id := "mathcov-special-trig-l474", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_SMALL_X(::Type{Float64})"]
    statement := "The source-order model of ATAN_SMALL_X(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:474-474; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_474, thm := some ``p_special_trig_474_proven },
  { id := "mathcov-special-trig-l475", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_LARGE_X(::Type{Float32})"]
    statement := "The source-order model of ATAN_LARGE_X(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:475-475; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_475, thm := some ``p_special_trig_475_proven },
  { id := "mathcov-special-trig-l476", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN_SMALL_X(::Type{Float32})"]
    statement := "The source-order model of ATAN_SMALL_X(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:476-476; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_476, thm := some ``p_special_trig_476_proven },
  { id := "mathcov-special-trig-l478", juliaFile := "base/special/trig.jl"
    juliaFns := ["atan_p(z::Float64, w::Float64)"]
    statement := "The source-order model of atan_p(z::Float64, w::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:478-484; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_478, thm := some ``p_special_trig_478_proven },
  { id := "mathcov-special-trig-l485", juliaFile := "base/special/trig.jl"
    juliaFns := ["atan_q(w::Float64)"]
    statement := "The source-order model of atan_q(w::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:485-490; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_485, thm := some ``p_special_trig_485_proven },
  { id := "mathcov-special-trig-l491", juliaFile := "base/special/trig.jl"
    juliaFns := ["atan_p(z::Float32, w::Float32)"]
    statement := "The source-order model of atan_p(z::Float32, w::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:491-491; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_491, thm := some ``p_special_trig_491_proven },
  { id := "mathcov-special-trig-l492", juliaFile := "base/special/trig.jl"
    juliaFns := ["atan_q(w::Float32)"]
    statement := "The source-order model of atan_q(w::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:492-492; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_492, thm := some ``p_special_trig_492_proven },
  { id := "mathcov-special-trig-l493", juliaFile := "base/special/trig.jl"
    juliaFns := ["atan_pq(x)"]
    statement := "The source-order model of atan_pq(x) returns a result for every allowed input."
    source := "base/special/trig.jl:493-498; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_493, thm := some ``p_special_trig_493_proven },
  { id := "mathcov-special-trig-l500", juliaFile := "base/special/trig.jl"
    juliaFns := ["atan(x::T) where T<:Union{Float32, Float64}"]
    statement := "The source-order model of atan(x::T) where T<:Union{Float32, Float64} returns a result for every allowed input."
    source := "base/special/trig.jl:500-554; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_500, thm := some ``p_special_trig_500_proven },
  { id := "mathcov-special-trig-l556", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN2_PI_LO(::Type{Float32})"]
    statement := "The source-order model of ATAN2_PI_LO(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:556-556; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_556, thm := some ``p_special_trig_556_proven },
  { id := "mathcov-special-trig-l557", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN2_RATIO_BIT_SHIFT(::Type{Float32})"]
    statement := "The source-order model of ATAN2_RATIO_BIT_SHIFT(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:557-557; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_557, thm := some ``p_special_trig_557_proven },
  { id := "mathcov-special-trig-l558", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN2_RATIO_THRESHOLD(::Type{Float32})"]
    statement := "The source-order model of ATAN2_RATIO_THRESHOLD(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:558-558; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_558, thm := some ``p_special_trig_558_proven },
  { id := "mathcov-special-trig-l560", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN2_PI_LO(::Type{Float64})"]
    statement := "The source-order model of ATAN2_PI_LO(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:560-560; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_560, thm := some ``p_special_trig_560_proven },
  { id := "mathcov-special-trig-l561", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN2_RATIO_BIT_SHIFT(::Type{Float64})"]
    statement := "The source-order model of ATAN2_RATIO_BIT_SHIFT(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:561-561; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_561, thm := some ``p_special_trig_561_proven },
  { id := "mathcov-special-trig-l562", juliaFile := "base/special/trig.jl"
    juliaFns := ["ATAN2_RATIO_THRESHOLD(::Type{Float64})"]
    statement := "The source-order model of ATAN2_RATIO_THRESHOLD(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:562-562; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_562, thm := some ``p_special_trig_562_proven },
  { id := "mathcov-special-trig-l564", juliaFile := "base/special/trig.jl"
    juliaFns := ["atan(y::T, x::T) where T<:Union{Float32, Float64}"]
    statement := "The source-order model of atan(y::T, x::T) where T<:Union{Float32, Float64} returns a result for every allowed input."
    source := "base/special/trig.jl:564-655; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_564, thm := some ``p_special_trig_564_proven },
  { id := "mathcov-special-trig-l657", juliaFile := "base/special/trig.jl"
    juliaFns := ["ACOS_X_MIN_THRESHOLD(::Type{Float32})"]
    statement := "The source-order model of ACOS_X_MIN_THRESHOLD(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:657-657; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_657, thm := some ``p_special_trig_657_proven },
  { id := "mathcov-special-trig-l658", juliaFile := "base/special/trig.jl"
    juliaFns := ["ACOS_X_MIN_THRESHOLD(::Type{Float64})"]
    statement := "The source-order model of ACOS_X_MIN_THRESHOLD(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:658-658; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_658, thm := some ``p_special_trig_658_proven },
  { id := "mathcov-special-trig-l659", juliaFile := "base/special/trig.jl"
    juliaFns := ["PIO2_HI(::Type{Float32})"]
    statement := "The source-order model of PIO2_HI(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:659-659; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_659, thm := some ``p_special_trig_659_proven },
  { id := "mathcov-special-trig-l660", juliaFile := "base/special/trig.jl"
    juliaFns := ["PIO2_LO(::Type{Float32})"]
    statement := "The source-order model of PIO2_LO(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:660-660; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_660, thm := some ``p_special_trig_660_proven },
  { id := "mathcov-special-trig-l661", juliaFile := "base/special/trig.jl"
    juliaFns := ["PIO2_HI(::Type{Float64})"]
    statement := "The source-order model of PIO2_HI(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:661-661; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_661, thm := some ``p_special_trig_661_proven },
  { id := "mathcov-special-trig-l662", juliaFile := "base/special/trig.jl"
    juliaFns := ["PIO2_LO(::Type{Float64})"]
    statement := "The source-order model of PIO2_LO(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:662-662; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_662, thm := some ``p_special_trig_662_proven },
  { id := "mathcov-special-trig-l663", juliaFile := "base/special/trig.jl"
    juliaFns := ["ACOS_PI(::Type{Float32})"]
    statement := "The source-order model of ACOS_PI(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:663-663; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_663, thm := some ``p_special_trig_663_proven },
  { id := "mathcov-special-trig-l664", juliaFile := "base/special/trig.jl"
    juliaFns := ["ACOS_PI(::Type{Float64})"]
    statement := "The source-order model of ACOS_PI(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:664-664; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_664, thm := some ``p_special_trig_664_proven },
  { id := "mathcov-special-trig-l665", juliaFile := "base/special/trig.jl"
    juliaFns := ["ACOS_CORRECT_LOWWORD(::Type{Float32}, x)"]
    statement := "The source-order model of ACOS_CORRECT_LOWWORD(::Type{Float32}, x) returns a result for every allowed input."
    source := "base/special/trig.jl:665-665; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_665, thm := some ``p_special_trig_665_proven },
  { id := "mathcov-special-trig-l666", juliaFile := "base/special/trig.jl"
    juliaFns := ["ACOS_CORRECT_LOWWORD(::Type{Float64}, x)"]
    statement := "The source-order model of ACOS_CORRECT_LOWWORD(::Type{Float64}, x) returns a result for every allowed input."
    source := "base/special/trig.jl:666-666; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_666, thm := some ``p_special_trig_666_proven },
  { id := "mathcov-special-trig-l668", juliaFile := "base/special/trig.jl"
    juliaFns := ["acos_domain_error(x)"]
    statement := "The source-order model of acos_domain_error(x) returns a result for every allowed input."
    source := "base/special/trig.jl:668-668; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_668, thm := some ``p_special_trig_668_proven },
  { id := "mathcov-special-trig-l669", juliaFile := "base/special/trig.jl"
    juliaFns := ["acos(x::T) where T <: Union{Float32, Float64}"]
    statement := "The source-order model of acos(x::T) where T <: Union{Float32, Float64} returns a result for every allowed input."
    source := "base/special/trig.jl:669-722; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_669, thm := some ``p_special_trig_669_proven },
  { id := "mathcov-special-trig-l725", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi_kernel(x::Float64)"]
    statement := "The source-order model of sinpi_kernel(x::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:725-727; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_725, thm := some ``p_special_trig_725_proven },
  { id := "mathcov-special-trig-l728", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi_kernel_wide(x::Float64)"]
    statement := "The source-order model of sinpi_kernel_wide(x::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:728-730; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_728, thm := some ``p_special_trig_728_proven },
  { id := "mathcov-special-trig-l731", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi_kernel(x::Float32)"]
    statement := "The source-order model of sinpi_kernel(x::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:731-733; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_731, thm := some ``p_special_trig_731_proven },
  { id := "mathcov-special-trig-l734", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi_kernel_wide(x::Float32)"]
    statement := "The source-order model of sinpi_kernel_wide(x::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:734-738; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_734, thm := some ``p_special_trig_734_proven },
  { id := "mathcov-special-trig-l740", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi_kernel(x::Float16)"]
    statement := "The source-order model of sinpi_kernel(x::Float16) returns a result for every allowed input."
    source := "base/special/trig.jl:740-742; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_740, thm := some ``p_special_trig_740_proven },
  { id := "mathcov-special-trig-l743", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi_kernel_wide(x::Float16)"]
    statement := "The source-order model of sinpi_kernel_wide(x::Float16) returns a result for every allowed input."
    source := "base/special/trig.jl:743-746; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_743, thm := some ``p_special_trig_743_proven },
  { id := "mathcov-special-trig-l749", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi_kernel(x::Float64)"]
    statement := "The source-order model of cospi_kernel(x::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:749-751; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_749, thm := some ``p_special_trig_749_proven },
  { id := "mathcov-special-trig-l752", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi_kernel_wide(x::Float64)"]
    statement := "The source-order model of cospi_kernel_wide(x::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:752-754; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_752, thm := some ``p_special_trig_752_proven },
  { id := "mathcov-special-trig-l755", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi_kernel(x::Float32)"]
    statement := "The source-order model of cospi_kernel(x::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:755-757; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_755, thm := some ``p_special_trig_755_proven },
  { id := "mathcov-special-trig-l758", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi_kernel_wide(x::Float32)"]
    statement := "The source-order model of cospi_kernel_wide(x::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:758-762; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_758, thm := some ``p_special_trig_758_proven },
  { id := "mathcov-special-trig-l763", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi_kernel(x::Float16)"]
    statement := "The source-order model of cospi_kernel(x::Float16) returns a result for every allowed input."
    source := "base/special/trig.jl:763-765; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_763, thm := some ``p_special_trig_763_proven },
  { id := "mathcov-special-trig-l766", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi_kernel_wide(x::Float16)"]
    statement := "The source-order model of cospi_kernel_wide(x::Float16) returns a result for every allowed input."
    source := "base/special/trig.jl:766-769; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_766, thm := some ``p_special_trig_766_proven },
  { id := "mathcov-special-trig-l771", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cospi_kernel(x::AbstractFloat, sch)"]
    statement := "The source-order model of _cospi_kernel(x::AbstractFloat, sch) returns a result for every allowed input."
    source := "base/special/trig.jl:771-783; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_771, thm := some ``p_special_trig_771_proven },
  { id := "mathcov-special-trig-l785", juliaFile := "base/special/trig.jl"
    juliaFns := ["_sinpi_kernel(x::AbstractFloat, sch)"]
    statement := "The source-order model of _sinpi_kernel(x::AbstractFloat, sch) returns a result for every allowed input."
    source := "base/special/trig.jl:785-795; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_785, thm := some ``p_special_trig_785_proven },
  { id := "mathcov-special-trig-l934", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi(_x::T) where T<:IEEEFloat"]
    statement := "The source-order model of sinpi(_x::T) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/special/trig.jl:934-957; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_934, thm := some ``p_special_trig_934_proven },
  { id := "mathcov-special-trig-l968", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi(x::T) where T<:IEEEFloat"]
    statement := "The source-order model of cospi(x::T) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/special/trig.jl:968-990; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_968, thm := some ``p_special_trig_968_proven },
  { id := "mathcov-special-trig-l1005", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincospi(_x::T) where T<:IEEEFloat"]
    statement := "The source-order model of sincospi(_x::T) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/special/trig.jl:1005-1030; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1005, thm := some ``p_special_trig_1005_proven },
  { id := "mathcov-special-trig-l1044", juliaFile := "base/special/trig.jl"
    juliaFns := ["tanpi(_x::T) where T<:IEEEFloat"]
    statement := "The source-order model of tanpi(_x::T) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/special/trig.jl:1044-1072; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1044, thm := some ``p_special_trig_1044_proven },
  { id := "mathcov-special-trig-l1074", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi(x::Integer)"]
    statement := "The source-order model of sinpi(x::Integer) returns a result for every allowed input."
    source := "base/special/trig.jl:1074-1074; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1074, thm := some ``p_special_trig_1074_proven },
  { id := "mathcov-special-trig-l1075", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi(x::Integer)"]
    statement := "The source-order model of cospi(x::Integer) returns a result for every allowed input."
    source := "base/special/trig.jl:1075-1075; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1075, thm := some ``p_special_trig_1075_proven },
  { id := "mathcov-special-trig-l1076", juliaFile := "base/special/trig.jl"
    juliaFns := ["tanpi(x::Integer)"]
    statement := "The source-order model of tanpi(x::Integer) returns a result for every allowed input."
    source := "base/special/trig.jl:1076-1077; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1076, thm := some ``p_special_trig_1076_proven },
  { id := "mathcov-special-trig-l1078", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincospi(x::Integer)"]
    statement := "The source-order model of sincospi(x::Integer) returns a result for every allowed input."
    source := "base/special/trig.jl:1078-1078; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1078, thm := some ``p_special_trig_1078_proven },
  { id := "mathcov-special-trig-l1079", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi(x::AbstractFloat)"]
    statement := "The source-order model of sinpi(x::AbstractFloat) returns a result for every allowed input."
    source := "base/special/trig.jl:1079-1079; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1079, thm := some ``p_special_trig_1079_proven },
  { id := "mathcov-special-trig-l1080", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi(x::AbstractFloat)"]
    statement := "The source-order model of cospi(x::AbstractFloat) returns a result for every allowed input."
    source := "base/special/trig.jl:1080-1080; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1080, thm := some ``p_special_trig_1080_proven },
  { id := "mathcov-special-trig-l1081", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincospi(x::AbstractFloat)"]
    statement := "The source-order model of sincospi(x::AbstractFloat) returns a result for every allowed input."
    source := "base/special/trig.jl:1081-1081; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1081, thm := some ``p_special_trig_1081_proven },
  { id := "mathcov-special-trig-l1082", juliaFile := "base/special/trig.jl"
    juliaFns := ["tanpi(x::AbstractFloat)"]
    statement := "The source-order model of tanpi(x::AbstractFloat) returns a result for every allowed input."
    source := "base/special/trig.jl:1082-1082; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1082, thm := some ``p_special_trig_1082_proven },
  { id := "mathcov-special-trig-l1084", juliaFile := "base/special/trig.jl"
    juliaFns := ["tanpi(z::Complex)"]
    statement := "The source-order model of tanpi(z::Complex) returns a result for every allowed input."
    source := "base/special/trig.jl:1084-1091; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1084, thm := some ``p_special_trig_1084_proven },
  { id := "mathcov-special-trig-l1093", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinpi(z::Complex{T}) where T"]
    statement := "The source-order model of sinpi(z::Complex{T}) where T returns a result for every allowed input."
    source := "base/special/trig.jl:1093-1124; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1093, thm := some ``p_special_trig_1093_proven },
  { id := "mathcov-special-trig-l1126", juliaFile := "base/special/trig.jl"
    juliaFns := ["cospi(z::Complex{T}) where T"]
    statement := "The source-order model of cospi(z::Complex{T}) where T returns a result for every allowed input."
    source := "base/special/trig.jl:1126-1160; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1126, thm := some ``p_special_trig_1126_proven },
  { id := "mathcov-special-trig-l1162", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincospi(z::Complex{T}) where T"]
    statement := "The source-order model of sincospi(z::Complex{T}) where T returns a result for every allowed input."
    source := "base/special/trig.jl:1162-1207; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1162, thm := some ``p_special_trig_1162_proven },
  { id := "mathcov-special-trig-l1217", juliaFile := "base/special/trig.jl"
    juliaFns := ["fastabs(x::Number)"]
    statement := "The source-order model of fastabs(x::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1217-1217; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1217, thm := some ``p_special_trig_1217_proven },
  { id := "mathcov-special-trig-l1218", juliaFile := "base/special/trig.jl"
    juliaFns := ["fastabs(z::Complex)"]
    statement := "The source-order model of fastabs(z::Complex) returns a result for every allowed input."
    source := "base/special/trig.jl:1218-1218; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1218, thm := some ``p_special_trig_1218_proven },
  { id := "mathcov-special-trig-l1221", juliaFile := "base/special/trig.jl"
    juliaFns := ["isinf_real(x::Real)"]
    statement := "The source-order model of isinf_real(x::Real) returns a result for every allowed input."
    source := "base/special/trig.jl:1221-1221; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1221, thm := some ``p_special_trig_1221_proven },
  { id := "mathcov-special-trig-l1222", juliaFile := "base/special/trig.jl"
    juliaFns := ["isinf_real(x::Complex)"]
    statement := "The source-order model of isinf_real(x::Complex) returns a result for every allowed input."
    source := "base/special/trig.jl:1222-1222; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1222, thm := some ``p_special_trig_1222_proven },
  { id := "mathcov-special-trig-l1223", juliaFile := "base/special/trig.jl"
    juliaFns := ["isinf_real(x::Number)"]
    statement := "The source-order model of isinf_real(x::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1223-1223; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1223, thm := some ``p_special_trig_1223_proven },
  { id := "mathcov-special-trig-l1234", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinc(x::Number)"]
    statement := "The source-order model of sinc(x::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1234-1234; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1234, thm := some ``p_special_trig_1234_proven },
  { id := "mathcov-special-trig-l1235", juliaFile := "base/special/trig.jl"
    juliaFns := ["sinc(x::Integer)"]
    statement := "The source-order model of sinc(x::Integer) returns a result for every allowed input."
    source := "base/special/trig.jl:1235-1235; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1235, thm := some ``p_special_trig_1235_proven },
  { id := "mathcov-special-trig-l1236", juliaFile := "base/special/trig.jl"
    juliaFns := ["_sinc(x::Number)"]
    statement := "The source-order model of _sinc(x::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1236-1236; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1236, thm := some ``p_special_trig_1236_proven },
  { id := "mathcov-special-trig-l1237", juliaFile := "base/special/trig.jl"
    juliaFns := ["_sinc_threshold(::Type{Float64})"]
    statement := "The source-order model of _sinc_threshold(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:1237-1237; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1237, thm := some ``p_special_trig_1237_proven },
  { id := "mathcov-special-trig-l1238", juliaFile := "base/special/trig.jl"
    juliaFns := ["_sinc_threshold(::Type{Float32})"]
    statement := "The source-order model of _sinc_threshold(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/trig.jl:1238-1238; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1238, thm := some ``p_special_trig_1238_proven },
  { id := "mathcov-special-trig-l1239", juliaFile := "base/special/trig.jl"
    juliaFns := ["_sinc(x::Union{T,Complex{T}}) where {T<:Union{Float32,Float64}}"]
    statement := "The source-order model of _sinc(x::Union{T,Complex{T}}) where {T<:Union{Float32,Float64}} returns a result for every allowed input."
    source := "base/special/trig.jl:1239-1240; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1239, thm := some ``p_special_trig_1239_proven },
  { id := "mathcov-special-trig-l1241", juliaFile := "base/special/trig.jl"
    juliaFns := ["_sinc(x::Float16)"]
    statement := "The source-order model of _sinc(x::Float16) returns a result for every allowed input."
    source := "base/special/trig.jl:1241-1241; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1241, thm := some ``p_special_trig_1241_proven },
  { id := "mathcov-special-trig-l1242", juliaFile := "base/special/trig.jl"
    juliaFns := ["_sinc(x::ComplexF16)"]
    statement := "The source-order model of _sinc(x::ComplexF16) returns a result for every allowed input."
    source := "base/special/trig.jl:1242-1242; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1242, thm := some ``p_special_trig_1242_proven },
  { id := "mathcov-special-trig-l1254", juliaFile := "base/special/trig.jl"
    juliaFns := ["cosc(x::Number)"]
    statement := "The source-order model of cosc(x::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1254-1254; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1254, thm := some ``p_special_trig_1254_proven },
  { id := "mathcov-special-trig-l1255", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cosc_generic(x)"]
    statement := "The source-order model of _cosc_generic(x) returns a result for every allowed input."
    source := "base/special/trig.jl:1255-1258; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1255, thm := some ``p_special_trig_1255_proven },
  { id := "mathcov-special-trig-l1259", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cosc(x::Number)"]
    statement := "The source-order model of _cosc(x::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1259-1281; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1259, thm := some ``p_special_trig_1259_proven },
  { id := "mathcov-special-trig-l1333", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cos_cardinal_eval(x::AbstractFloat, polynomials_close_to_origin::NTuple)"]
    statement := "The source-order model of _cos_cardinal_eval(x::AbstractFloat, polynomials_close_to_origin::NTuple) returns a result for every allowed input."
    source := "base/special/trig.jl:1333-1366; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1333, thm := some ``p_special_trig_1333_proven },
  { id := "mathcov-special-trig-l1334", juliaFile := "base/special/trig.jl"
    juliaFns := ["choose_poly(a::AbstractFloat, polynomials_close_to_origin::NTuple{2})"]
    statement := "The source-order model of choose_poly(a::AbstractFloat, polynomials_close_to_origin::NTuple{2}) returns a result for every allowed input."
    source := "base/special/trig.jl:1334-1341; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1334, thm := some ``p_special_trig_1334_proven },
  { id := "mathcov-special-trig-l1342", juliaFile := "base/special/trig.jl"
    juliaFns := ["choose_poly(a::AbstractFloat, polynomials_close_to_origin::NTuple{4})"]
    statement := "The source-order model of choose_poly(a::AbstractFloat, polynomials_close_to_origin::NTuple{4}) returns a result for every allowed input."
    source := "base/special/trig.jl:1342-1357; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1342, thm := some ``p_special_trig_1342_proven },
  { id := "mathcov-special-trig-l1384", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cosc(x::Union{Float32, Float64})"]
    statement := "The source-order model of _cosc(x::Union{Float32, Float64}) returns a result for every allowed input."
    source := "base/special/trig.jl:1384-1391; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1384, thm := some ``p_special_trig_1384_proven },
  { id := "mathcov-special-trig-l1395", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cosc(x::ComplexF64)"]
    statement := "The source-order model of _cosc(x::ComplexF64) returns a result for every allowed input."
    source := "base/special/trig.jl:1395-1397; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1395, thm := some ``p_special_trig_1395_proven },
  { id := "mathcov-special-trig-l1398", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cosc(x::ComplexF32)"]
    statement := "The source-order model of _cosc(x::ComplexF32) returns a result for every allowed input."
    source := "base/special/trig.jl:1398-1400; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1398, thm := some ``p_special_trig_1398_proven },
  { id := "mathcov-special-trig-l1401", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cosc(x::Float16)"]
    statement := "The source-order model of _cosc(x::Float16) returns a result for every allowed input."
    source := "base/special/trig.jl:1401-1401; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1401, thm := some ``p_special_trig_1401_proven },
  { id := "mathcov-special-trig-l1402", juliaFile := "base/special/trig.jl"
    juliaFns := ["_cosc(x::ComplexF16)"]
    statement := "The source-order model of _cosc(x::ComplexF16) returns a result for every allowed input."
    source := "base/special/trig.jl:1402-1402; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1402, thm := some ``p_special_trig_1402_proven },
  { id := "mathcov-special-trig-l1417", juliaFile := "base/special/trig.jl"
    juliaFns := ["($finv)(z::Number)"]
    statement := "The source-order model of ($finv)(z::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1417-1417; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1417, thm := some ``p_special_trig_1417_proven },
  { id := "mathcov-special-trig-l1424", juliaFile := "base/special/trig.jl"
    juliaFns := ["($finvh)(z::Number)"]
    statement := "The source-order model of ($finvh)(z::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1424-1424; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1424, thm := some ``p_special_trig_1424_proven },
  { id := "mathcov-special-trig-l1431", juliaFile := "base/special/trig.jl"
    juliaFns := ["($finvd)(z::Number)"]
    statement := "The source-order model of ($finvd)(z::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1431-1431; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1431, thm := some ``p_special_trig_1431_proven },
  { id := "mathcov-special-trig-l1445", juliaFile := "base/special/trig.jl"
    juliaFns := ["($tfa)(y::Number)"]
    statement := "The source-order model of ($tfa)(y::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1445-1445; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1445, thm := some ``p_special_trig_1445_proven },
  { id := "mathcov-special-trig-l1450", juliaFile := "base/special/trig.jl"
    juliaFns := ["($hfa)(y::Number)"]
    statement := "The source-order model of ($hfa)(y::Number) returns a result for every allowed input."
    source := "base/special/trig.jl:1450-1450; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1450, thm := some ``p_special_trig_1450_proven },
  { id := "mathcov-special-trig-l1456", juliaFile := "base/special/trig.jl"
    juliaFns := ["deg2rad_ext(x::Float64)"]
    statement := "The source-order model of deg2rad_ext(x::Float64) returns a result for every allowed input."
    source := "base/special/trig.jl:1456-1469; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1456, thm := some ``p_special_trig_1456_proven },
  { id := "mathcov-special-trig-l1470", juliaFile := "base/special/trig.jl"
    juliaFns := ["deg2rad_ext(x::Float32)"]
    statement := "The source-order model of deg2rad_ext(x::Float32) returns a result for every allowed input."
    source := "base/special/trig.jl:1470-1470; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1470, thm := some ``p_special_trig_1470_proven },
  { id := "mathcov-special-trig-l1471", juliaFile := "base/special/trig.jl"
    juliaFns := ["deg2rad_ext(x::Real)"]
    statement := "The source-order model of deg2rad_ext(x::Real) returns a result for every allowed input."
    source := "base/special/trig.jl:1471-1471; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1471, thm := some ``p_special_trig_1471_proven },
  { id := "mathcov-special-trig-l1473", juliaFile := "base/special/trig.jl"
    juliaFns := ["sind(x::Real)"]
    statement := "The source-order model of sind(x::Real) returns a result for every allowed input."
    source := "base/special/trig.jl:1473-1502; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1473, thm := some ``p_special_trig_1473_proven },
  { id := "mathcov-special-trig-l1504", juliaFile := "base/special/trig.jl"
    juliaFns := ["cosd(x::Real)"]
    statement := "The source-order model of cosd(x::Real) returns a result for every allowed input."
    source := "base/special/trig.jl:1504-1528; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1504, thm := some ``p_special_trig_1504_proven },
  { id := "mathcov-special-trig-l1530", juliaFile := "base/special/trig.jl"
    juliaFns := ["tand(x::Real)"]
    statement := "The source-order model of tand(x::Real) returns a result for every allowed input."
    source := "base/special/trig.jl:1530-1530; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1530, thm := some ``p_special_trig_1530_proven },
  { id := "mathcov-special-trig-l1543", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincosd(x)"]
    statement := "The source-order model of sincosd(x) returns a result for every allowed input."
    source := "base/special/trig.jl:1543-1543; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1543, thm := some ``p_special_trig_1543_proven },
  { id := "mathcov-special-trig-l1547", juliaFile := "base/special/trig.jl"
    juliaFns := ["sincosd(::Missing)"]
    statement := "The source-order model of sincosd(::Missing) returns a result for every allowed input."
    source := "base/special/trig.jl:1547-1547; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1547, thm := some ``p_special_trig_1547_proven },
  { id := "mathcov-special-trig-l1563", juliaFile := "base/special/trig.jl"
    juliaFns := ["($fd)(x)"]
    statement := "The source-order model of ($fd)(x) returns a result for every allowed input."
    source := "base/special/trig.jl:1563-1563; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1563, thm := some ``p_special_trig_1563_proven },
  { id := "mathcov-special-trig-l1582", juliaFile := "base/special/trig.jl"
    juliaFns := ["($fd)(x)"]
    statement := "The source-order model of ($fd)(x) returns a result for every allowed input."
    source := "base/special/trig.jl:1582-1582; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1582, thm := some ``p_special_trig_1582_proven },
  { id := "mathcov-special-trig-l1600", juliaFile := "base/special/trig.jl"
    juliaFns := ["atand(y)"]
    statement := "The source-order model of atand(y) returns a result for every allowed input."
    source := "base/special/trig.jl:1600-1600; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1600, thm := some ``p_special_trig_1600_proven },
  { id := "mathcov-special-trig-l1601", juliaFile := "base/special/trig.jl"
    juliaFns := ["atand(y, x)"]
    statement := "The source-order model of atand(y, x) returns a result for every allowed input."
    source := "base/special/trig.jl:1601-1601; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1601, thm := some ``p_special_trig_1601_proven },
  { id := "mathcov-special-trig-l1605", juliaFile := "base/special/trig.jl"
    juliaFns := ["$f(x::Float16)"]
    statement := "The source-order model of $f(x::Float16) returns a result for every allowed input."
    source := "base/special/trig.jl:1605-1605; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1605, thm := some ``p_special_trig_1605_proven },
  { id := "mathcov-special-trig-l1608", juliaFile := "base/special/trig.jl"
    juliaFns := ["$f(x::Float16)"]
    statement := "The source-order model of $f(x::Float16) returns a result for every allowed input."
    source := "base/special/trig.jl:1608-1608; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1608, thm := some ``p_special_trig_1608_proven },
  { id := "mathcov-special-trig-l1610", juliaFile := "base/special/trig.jl"
    juliaFns := ["atand(y::Float16, x::Float16)"]
    statement := "The source-order model of atand(y::Float16, x::Float16) returns a result for every allowed input."
    source := "base/special/trig.jl:1610-1610; method body and totality invariant"
    status := .proven, prop := ``P_special_trig_1610, thm := some ``p_special_trig_1610_proven },
  { id := "mathcov-special-exp-l6", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAGIC_ROUND_CONST(::Type{Float64})"]
    statement := "The source-order model of MAGIC_ROUND_CONST(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:6-6; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_6, thm := some ``p_special_exp_6_proven },
  { id := "mathcov-special-exp-l7", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAGIC_ROUND_CONST(::Type{Float32})"]
    statement := "The source-order model of MAGIC_ROUND_CONST(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:7-7; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_7, thm := some ``p_special_exp_7_proven },
  { id := "mathcov-special-exp-l11", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP(n::Val{2}, ::Type{Float32})"]
    statement := "The source-order model of MAX_EXP(n::Val{2}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:11-11; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_11, thm := some ``p_special_exp_11_proven },
  { id := "mathcov-special-exp-l12", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP(n::Val{2}, ::Type{Float64})"]
    statement := "The source-order model of MAX_EXP(n::Val{2}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:12-12; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_12, thm := some ``p_special_exp_12_proven },
  { id := "mathcov-special-exp-l13", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP(n::Val{:ℯ}, ::Type{Float32})"]
    statement := "The source-order model of MAX_EXP(n::Val{:ℯ}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:13-13; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_13, thm := some ``p_special_exp_13_proven },
  { id := "mathcov-special-exp-l14", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP(n::Val{:ℯ}, ::Type{Float64})"]
    statement := "The source-order model of MAX_EXP(n::Val{:ℯ}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:14-14; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_14, thm := some ``p_special_exp_14_proven },
  { id := "mathcov-special-exp-l15", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP(n::Val{10}, ::Type{Float32})"]
    statement := "The source-order model of MAX_EXP(n::Val{10}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:15-15; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_15, thm := some ``p_special_exp_15_proven },
  { id := "mathcov-special-exp-l16", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP(n::Val{10}, ::Type{Float64})"]
    statement := "The source-order model of MAX_EXP(n::Val{10}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:16-16; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_16, thm := some ``p_special_exp_16_proven },
  { id := "mathcov-special-exp-l19", juliaFile := "base/special/exp.jl"
    juliaFns := ["MIN_EXP(n::Val{2}, ::Type{Float32})"]
    statement := "The source-order model of MIN_EXP(n::Val{2}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:19-19; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_19, thm := some ``p_special_exp_19_proven },
  { id := "mathcov-special-exp-l20", juliaFile := "base/special/exp.jl"
    juliaFns := ["MIN_EXP(n::Val{2}, ::Type{Float64})"]
    statement := "The source-order model of MIN_EXP(n::Val{2}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:20-20; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_20, thm := some ``p_special_exp_20_proven },
  { id := "mathcov-special-exp-l21", juliaFile := "base/special/exp.jl"
    juliaFns := ["MIN_EXP(n::Val{:ℯ}, ::Type{Float32})"]
    statement := "The source-order model of MIN_EXP(n::Val{:ℯ}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:21-21; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_21, thm := some ``p_special_exp_21_proven },
  { id := "mathcov-special-exp-l22", juliaFile := "base/special/exp.jl"
    juliaFns := ["MIN_EXP(n::Val{:ℯ}, ::Type{Float64})"]
    statement := "The source-order model of MIN_EXP(n::Val{:ℯ}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:22-22; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_22, thm := some ``p_special_exp_22_proven },
  { id := "mathcov-special-exp-l23", juliaFile := "base/special/exp.jl"
    juliaFns := ["MIN_EXP(n::Val{10}, ::Type{Float32})"]
    statement := "The source-order model of MIN_EXP(n::Val{10}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:23-23; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_23, thm := some ``p_special_exp_23_proven },
  { id := "mathcov-special-exp-l24", juliaFile := "base/special/exp.jl"
    juliaFns := ["MIN_EXP(n::Val{10}, ::Type{Float64})"]
    statement := "The source-order model of MIN_EXP(n::Val{10}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:24-24; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_24, thm := some ``p_special_exp_24_proven },
  { id := "mathcov-special-exp-l28", juliaFile := "base/special/exp.jl"
    juliaFns := ["SUBNORM_EXP(n::Val{2}, ::Type{Float32})"]
    statement := "The source-order model of SUBNORM_EXP(n::Val{2}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:28-28; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_28, thm := some ``p_special_exp_28_proven },
  { id := "mathcov-special-exp-l29", juliaFile := "base/special/exp.jl"
    juliaFns := ["SUBNORM_EXP(n::Val{2}, ::Type{Float64})"]
    statement := "The source-order model of SUBNORM_EXP(n::Val{2}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:29-29; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_29, thm := some ``p_special_exp_29_proven },
  { id := "mathcov-special-exp-l30", juliaFile := "base/special/exp.jl"
    juliaFns := ["SUBNORM_EXP(n::Val{:ℯ}, ::Type{Float32})"]
    statement := "The source-order model of SUBNORM_EXP(n::Val{:ℯ}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:30-30; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_30, thm := some ``p_special_exp_30_proven },
  { id := "mathcov-special-exp-l31", juliaFile := "base/special/exp.jl"
    juliaFns := ["SUBNORM_EXP(n::Val{:ℯ}, ::Type{Float64})"]
    statement := "The source-order model of SUBNORM_EXP(n::Val{:ℯ}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:31-31; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_31, thm := some ``p_special_exp_31_proven },
  { id := "mathcov-special-exp-l32", juliaFile := "base/special/exp.jl"
    juliaFns := ["SUBNORM_EXP(n::Val{10}, ::Type{Float32})"]
    statement := "The source-order model of SUBNORM_EXP(n::Val{10}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:32-32; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_32, thm := some ``p_special_exp_32_proven },
  { id := "mathcov-special-exp-l33", juliaFile := "base/special/exp.jl"
    juliaFns := ["SUBNORM_EXP(n::Val{10}, ::Type{Float64})"]
    statement := "The source-order model of SUBNORM_EXP(n::Val{10}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:33-33; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_33, thm := some ``p_special_exp_33_proven },
  { id := "mathcov-special-exp-l36", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256INV(::Val{2}, ::Type{Float64})"]
    statement := "The source-order model of LogBo256INV(::Val{2}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:36-36; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_36, thm := some ``p_special_exp_36_proven },
  { id := "mathcov-special-exp-l37", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256INV(::Val{:ℯ}, ::Type{Float64})"]
    statement := "The source-order model of LogBo256INV(::Val{:ℯ}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:37-37; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_37, thm := some ``p_special_exp_37_proven },
  { id := "mathcov-special-exp-l38", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256INV(::Val{10}, ::Type{Float64})"]
    statement := "The source-order model of LogBo256INV(::Val{10}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:38-38; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_38, thm := some ``p_special_exp_38_proven },
  { id := "mathcov-special-exp-l44", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256U(::Val{2}, ::Type{Float64})"]
    statement := "The source-order model of LogBo256U(::Val{2}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:44-44; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_44, thm := some ``p_special_exp_44_proven },
  { id := "mathcov-special-exp-l45", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256U(::Val{:ℯ}, ::Type{Float64})"]
    statement := "The source-order model of LogBo256U(::Val{:ℯ}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:45-45; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_45, thm := some ``p_special_exp_45_proven },
  { id := "mathcov-special-exp-l46", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256U(::Val{10}, ::Type{Float64})"]
    statement := "The source-order model of LogBo256U(::Val{10}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:46-46; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_46, thm := some ``p_special_exp_46_proven },
  { id := "mathcov-special-exp-l47", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256L(::Val{2}, ::Type{Float64})"]
    statement := "The source-order model of LogBo256L(::Val{2}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:47-47; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_47, thm := some ``p_special_exp_47_proven },
  { id := "mathcov-special-exp-l48", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256L(::Val{:ℯ}, ::Type{Float64})"]
    statement := "The source-order model of LogBo256L(::Val{:ℯ}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:48-48; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_48, thm := some ``p_special_exp_48_proven },
  { id := "mathcov-special-exp-l49", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBo256L(::Val{10}, ::Type{Float64})"]
    statement := "The source-order model of LogBo256L(::Val{10}, ::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:49-49; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_49, thm := some ``p_special_exp_49_proven },
  { id := "mathcov-special-exp-l52", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBINV(::Val{2}, ::Type{Float32})"]
    statement := "The source-order model of LogBINV(::Val{2}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:52-52; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_52, thm := some ``p_special_exp_52_proven },
  { id := "mathcov-special-exp-l53", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBINV(::Val{:ℯ}, ::Type{Float32})"]
    statement := "The source-order model of LogBINV(::Val{:ℯ}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:53-53; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_53, thm := some ``p_special_exp_53_proven },
  { id := "mathcov-special-exp-l54", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBINV(::Val{10}, ::Type{Float32})"]
    statement := "The source-order model of LogBINV(::Val{10}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:54-54; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_54, thm := some ``p_special_exp_54_proven },
  { id := "mathcov-special-exp-l60", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBU(::Val{2}, ::Type{Float32})"]
    statement := "The source-order model of LogBU(::Val{2}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:60-60; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_60, thm := some ``p_special_exp_60_proven },
  { id := "mathcov-special-exp-l61", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBU(::Val{:ℯ}, ::Type{Float32})"]
    statement := "The source-order model of LogBU(::Val{:ℯ}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:61-61; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_61, thm := some ``p_special_exp_61_proven },
  { id := "mathcov-special-exp-l62", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBU(::Val{10}, ::Type{Float32})"]
    statement := "The source-order model of LogBU(::Val{10}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:62-62; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_62, thm := some ``p_special_exp_62_proven },
  { id := "mathcov-special-exp-l63", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBL(::Val{2}, ::Type{Float32})"]
    statement := "The source-order model of LogBL(::Val{2}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:63-63; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_63, thm := some ``p_special_exp_63_proven },
  { id := "mathcov-special-exp-l64", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBL(::Val{:ℯ}, ::Type{Float32})"]
    statement := "The source-order model of LogBL(::Val{:ℯ}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:64-64; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_64, thm := some ``p_special_exp_64_proven },
  { id := "mathcov-special-exp-l65", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogBL(::Val{10}, ::Type{Float32})"]
    statement := "The source-order model of LogBL(::Val{10}, ::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:65-65; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_65, thm := some ``p_special_exp_65_proven },
  { id := "mathcov-special-exp-l68", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogB(::Val{2}, ::Type{Float16})"]
    statement := "The source-order model of LogB(::Val{2}, ::Type{Float16}) returns a result for every allowed input."
    source := "base/special/exp.jl:68-68; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_68, thm := some ``p_special_exp_68_proven },
  { id := "mathcov-special-exp-l69", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogB(::Val{:ℯ}, ::Type{Float16})"]
    statement := "The source-order model of LogB(::Val{:ℯ}, ::Type{Float16}) returns a result for every allowed input."
    source := "base/special/exp.jl:69-69; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_69, thm := some ``p_special_exp_69_proven },
  { id := "mathcov-special-exp-l70", juliaFile := "base/special/exp.jl"
    juliaFns := ["LogB(::Val{10}, ::Type{Float16})"]
    statement := "The source-order model of LogB(::Val{10}, ::Type{Float16}) returns a result for every allowed input."
    source := "base/special/exp.jl:70-70; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_70, thm := some ``p_special_exp_70_proven },
  { id := "mathcov-special-exp-l73", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1b_kernel(::Val{2}, x::Float64)"]
    statement := "The source-order model of expm1b_kernel(::Val{2}, x::Float64) returns a result for every allowed input."
    source := "base/special/exp.jl:73-76; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_73, thm := some ``p_special_exp_73_proven },
  { id := "mathcov-special-exp-l77", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1b_kernel(::Val{:ℯ}, x::Float64)"]
    statement := "The source-order model of expm1b_kernel(::Val{:ℯ}, x::Float64) returns a result for every allowed input."
    source := "base/special/exp.jl:77-80; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_77, thm := some ``p_special_exp_77_proven },
  { id := "mathcov-special-exp-l81", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1b_kernel(::Val{10}, x::Float64)"]
    statement := "The source-order model of expm1b_kernel(::Val{10}, x::Float64) returns a result for every allowed input."
    source := "base/special/exp.jl:81-84; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_81, thm := some ``p_special_exp_81_proven },
  { id := "mathcov-special-exp-l86", juliaFile := "base/special/exp.jl"
    juliaFns := ["expb_kernel(::Val{2}, x::Float32)"]
    statement := "The source-order model of expb_kernel(::Val{2}, x::Float32) returns a result for every allowed input."
    source := "base/special/exp.jl:86-90; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_86, thm := some ``p_special_exp_86_proven },
  { id := "mathcov-special-exp-l91", juliaFile := "base/special/exp.jl"
    juliaFns := ["expb_kernel(::Val{:ℯ}, x::Float32)"]
    statement := "The source-order model of expb_kernel(::Val{:ℯ}, x::Float32) returns a result for every allowed input."
    source := "base/special/exp.jl:91-95; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_91, thm := some ``p_special_exp_91_proven },
  { id := "mathcov-special-exp-l96", juliaFile := "base/special/exp.jl"
    juliaFns := ["expb_kernel(::Val{10}, x::Float32)"]
    statement := "The source-order model of expb_kernel(::Val{10}, x::Float32) returns a result for every allowed input."
    source := "base/special/exp.jl:96-100; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_96, thm := some ``p_special_exp_96_proven },
  { id := "mathcov-special-exp-l178", juliaFile := "base/special/exp.jl"
    juliaFns := ["table_unpack(ind::Int32)"]
    statement := "The source-order model of table_unpack(ind::Int32) returns a result for every allowed input."
    source := "base/special/exp.jl:178-184; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_178, thm := some ``p_special_exp_178_proven },
  { id := "mathcov-special-exp-l207", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl(x::Float64, base)"]
    statement := "The source-order model of exp_impl(x::Float64, base) returns a result for every allowed input."
    source := "base/special/exp.jl:207-231; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_207, thm := some ``p_special_exp_207_proven },
  { id := "mathcov-special-exp-l233", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl(x::Float64, xlo::Float64, base)"]
    statement := "The source-order model of exp_impl(x::Float64, xlo::Float64, base) returns a result for every allowed input."
    source := "base/special/exp.jl:233-259; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_233, thm := some ``p_special_exp_233_proven },
  { id := "mathcov-special-exp-l260", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl_fast(x::Float64, base)"]
    statement := "The source-order model of exp_impl_fast(x::Float64, base) returns a result for every allowed input."
    source := "base/special/exp.jl:260-274; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_260, thm := some ``p_special_exp_260_proven },
  { id := "mathcov-special-exp-l276", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl(x::Float32, base)"]
    statement := "The source-order model of exp_impl(x::Float32, base) returns a result for every allowed input."
    source := "base/special/exp.jl:276-295; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_276, thm := some ``p_special_exp_276_proven },
  { id := "mathcov-special-exp-l297", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl_fast(x::Float32, base)"]
    statement := "The source-order model of exp_impl_fast(x::Float32, base) returns a result for every allowed input."
    source := "base/special/exp.jl:297-308; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_297, thm := some ``p_special_exp_297_proven },
  { id := "mathcov-special-exp-l310", juliaFile := "base/special/exp.jl"
    juliaFns := ["exp_impl(a::Float16, base)"]
    statement := "The source-order model of exp_impl(a::Float16, base) returns a result for every allowed input."
    source := "base/special/exp.jl:310-323; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_310, thm := some ``p_special_exp_310_proven },
  { id := "mathcov-special-exp-l329", juliaFile := "base/special/exp.jl"
    juliaFns := ["$func(x::Union{Float16,Float32,Float64})"]
    statement := "The source-order model of $func(x::Union{Float16,Float32,Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:329-329; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_329, thm := some ``p_special_exp_329_proven },
  { id := "mathcov-special-exp-l330", juliaFile := "base/special/exp.jl"
    juliaFns := ["$fast_func(x::Union{Float32,Float64})"]
    statement := "The source-order model of $fast_func(x::Union{Float32,Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:330-330; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_330, thm := some ``p_special_exp_330_proven },
  { id := "mathcov-special-exp-l406", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP(::Type{Float64})"]
    statement := "The source-order model of MAX_EXP(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:406-406; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_406, thm := some ``p_special_exp_406_proven },
  { id := "mathcov-special-exp-l407", juliaFile := "base/special/exp.jl"
    juliaFns := ["MIN_EXP(::Type{Float64})"]
    statement := "The source-order model of MIN_EXP(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:407-407; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_407, thm := some ``p_special_exp_407_proven },
  { id := "mathcov-special-exp-l408", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP(::Type{Float32})"]
    statement := "The source-order model of MAX_EXP(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:408-408; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_408, thm := some ``p_special_exp_408_proven },
  { id := "mathcov-special-exp-l409", juliaFile := "base/special/exp.jl"
    juliaFns := ["MIN_EXP(::Type{Float32})"]
    statement := "The source-order model of MIN_EXP(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:409-409; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_409, thm := some ``p_special_exp_409_proven },
  { id := "mathcov-special-exp-l410", juliaFile := "base/special/exp.jl"
    juliaFns := ["MAX_EXP(::Type{Float16})"]
    statement := "The source-order model of MAX_EXP(::Type{Float16}) returns a result for every allowed input."
    source := "base/special/exp.jl:410-410; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_410, thm := some ``p_special_exp_410_proven },
  { id := "mathcov-special-exp-l411", juliaFile := "base/special/exp.jl"
    juliaFns := ["MIN_EXP(::Type{Float16})"]
    statement := "The source-order model of MIN_EXP(::Type{Float16}) returns a result for every allowed input."
    source := "base/special/exp.jl:411-411; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_411, thm := some ``p_special_exp_411_proven },
  { id := "mathcov-special-exp-l413", juliaFile := "base/special/exp.jl"
    juliaFns := ["Ln2INV(::Type{Float64})"]
    statement := "The source-order model of Ln2INV(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:413-413; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_413, thm := some ``p_special_exp_413_proven },
  { id := "mathcov-special-exp-l414", juliaFile := "base/special/exp.jl"
    juliaFns := ["Ln2(::Type{Float64})"]
    statement := "The source-order model of Ln2(::Type{Float64}) returns a result for every allowed input."
    source := "base/special/exp.jl:414-414; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_414, thm := some ``p_special_exp_414_proven },
  { id := "mathcov-special-exp-l415", juliaFile := "base/special/exp.jl"
    juliaFns := ["Ln2INV(::Type{Float32})"]
    statement := "The source-order model of Ln2INV(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:415-415; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_415, thm := some ``p_special_exp_415_proven },
  { id := "mathcov-special-exp-l416", juliaFile := "base/special/exp.jl"
    juliaFns := ["Ln2(::Type{Float32})"]
    statement := "The source-order model of Ln2(::Type{Float32}) returns a result for every allowed input."
    source := "base/special/exp.jl:416-416; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_416, thm := some ``p_special_exp_416_proven },
  { id := "mathcov-special-exp-l419", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1_small(x::Float64)"]
    statement := "The source-order model of expm1_small(x::Float64) returns a result for every allowed input."
    source := "base/special/exp.jl:419-425; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_419, thm := some ``p_special_exp_419_proven },
  { id := "mathcov-special-exp-l426", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1_small(x::Float32)"]
    statement := "The source-order model of expm1_small(x::Float32) returns a result for every allowed input."
    source := "base/special/exp.jl:426-431; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_426, thm := some ``p_special_exp_426_proven },
  { id := "mathcov-special-exp-l459", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1(x::Float32)"]
    statement := "The source-order model of expm1(x::Float32) returns a result for every allowed input."
    source := "base/special/exp.jl:459-474; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_459, thm := some ``p_special_exp_459_proven },
  { id := "mathcov-special-exp-l476", juliaFile := "base/special/exp.jl"
    juliaFns := ["expm1(x::Float16)"]
    statement := "The source-order model of expm1(x::Float16) returns a result for every allowed input."
    source := "base/special/exp.jl:476-490; method body and totality invariant"
    status := .proven, prop := ``P_special_exp_476, thm := some ``p_special_exp_476_proven },
  { id := "mathcov-math-l32", juliaFile := "base/math.jl"
    juliaFns := ["throw_complex_domainerror(f::Symbol, x)"]
    statement := "The source-order model of throw_complex_domainerror(f::Symbol, x) returns a result for every allowed input."
    source := "base/math.jl:32-35; method body and totality invariant"
    status := .proven, prop := ``P_math_32, thm := some ``p_math_32_proven },
  { id := "mathcov-math-l36", juliaFile := "base/math.jl"
    juliaFns := ["throw_complex_domainerror_neg1(f::Symbol, x)"]
    statement := "The source-order model of throw_complex_domainerror_neg1(f::Symbol, x) returns a result for every allowed input."
    source := "base/math.jl:36-39; method body and totality invariant"
    status := .proven, prop := ``P_math_36, thm := some ``p_math_36_proven },
  { id := "mathcov-math-l40", juliaFile := "base/math.jl"
    juliaFns := ["throw_finite_domainerror(f::Symbol, x)"]
    statement := "The source-order model of throw_finite_domainerror(f::Symbol, x) returns a result for every allowed input."
    source := "base/math.jl:40-42; method body and totality invariant"
    status := .proven, prop := ``P_math_40, thm := some ``p_math_40_proven },
  { id := "mathcov-math-l43", juliaFile := "base/math.jl"
    juliaFns := ["throw_exp_domainerror(x)"]
    statement := "The source-order model of throw_exp_domainerror(x) returns a result for every allowed input."
    source := "base/math.jl:43-48; method body and totality invariant"
    status := .proven, prop := ``P_math_43, thm := some ``p_math_43_proven },
  { id := "mathcov-math-l90", juliaFile := "base/math.jl"
    juliaFns := ["_evalpoly(x, p)"]
    statement := "The source-order model of _evalpoly(x, p) returns a result for every allowed input."
    source := "base/math.jl:90-98; method body and totality invariant"
    status := .proven, prop := ``P_math_90, thm := some ``p_math_90_proven },
  { id := "mathcov-math-l100", juliaFile := "base/math.jl"
    juliaFns := ["evalpoly(z::Complex, p::Tuple)"]
    statement := "The source-order model of evalpoly(z::Complex, p::Tuple) returns a result for every allowed input."
    source := "base/math.jl:100-124; method body and totality invariant"
    status := .proven, prop := ``P_math_100, thm := some ``p_math_100_proven },
  { id := "mathcov-math-l125", juliaFile := "base/math.jl"
    juliaFns := ["evalpoly(z::Complex, p::Tuple{<:Any})"]
    statement := "The source-order model of evalpoly(z::Complex, p::Tuple{<:Any}) returns a result for every allowed input."
    source := "base/math.jl:125-125; method body and totality invariant"
    status := .proven, prop := ``P_math_125, thm := some ``p_math_125_proven },
  { id := "mathcov-math-l128", juliaFile := "base/math.jl"
    juliaFns := ["evalpoly(z::Complex, p::AbstractVector)"]
    statement := "The source-order model of evalpoly(z::Complex, p::AbstractVector) returns a result for every allowed input."
    source := "base/math.jl:128-128; method body and totality invariant"
    status := .proven, prop := ``P_math_128, thm := some ``p_math_128_proven },
  { id := "mathcov-math-l130", juliaFile := "base/math.jl"
    juliaFns := ["_evalpoly(z::Complex, p)"]
    statement := "The source-order model of _evalpoly(z::Complex, p) returns a result for every allowed input."
    source := "base/math.jl:130-148; method body and totality invariant"
    status := .proven, prop := ``P_math_130, thm := some ``p_math_130_proven },
  { id := "mathcov-math-l157", juliaFile := "base/math.jl"
    juliaFns := ["horner(x, p...)"]
    statement := "The source-order model of horner(x, p...) returns a result for every allowed input."
    source := "base/math.jl:157-160; method body and totality invariant"
    status := .proven, prop := ``P_math_157, thm := some ``p_math_157_proven },
  { id := "mathcov-math-l189", juliaFile := "base/math.jl"
    juliaFns := ["evalpoly(z, p...)"]
    statement := "The source-order model of evalpoly(z, p...) returns a result for every allowed input."
    source := "base/math.jl:189-192; method body and totality invariant"
    status := .proven, prop := ``P_math_189, thm := some ``p_math_189_proven },
  { id := "mathcov-math-l196", juliaFile := "base/math.jl"
    juliaFns := ["exthorner(x::T, p::Tuple{T,T,T}) where T<:Union{Float32,Float64}"]
    statement := "The source-order model of exthorner(x::T, p::Tuple{T,T,T}) where T<:Union{Float32,Float64} returns a result for every allowed input."
    source := "base/math.jl:196-201; method body and totality invariant"
    status := .proven, prop := ``P_math_196, thm := some ``p_math_196_proven },
  { id := "mathcov-math-l203", juliaFile := "base/math.jl"
    juliaFns := ["_exthorner(i::Int, x::T, p::Tuple{T,T,T}, hi::T, lo::T) where T<:Union{Float32,Float64}"]
    statement := "The source-order model of _exthorner(i::Int, x::T, p::Tuple{T,T,T}, hi::T, lo::T) where T<:Union{Float32,Float64} returns a result for every allowed input."
    source := "base/math.jl:203-210; method body and totality invariant"
    status := .proven, prop := ``P_math_203, thm := some ``p_math_203_proven },
  { id := "mathcov-math-l213", juliaFile := "base/math.jl"
    juliaFns := ["_180_over_pi(z::AbstractFloat)"]
    statement := "The source-order model of _180_over_pi(z::AbstractFloat) returns a result for every allowed input."
    source := "base/math.jl:213-215; method body and totality invariant"
    status := .proven, prop := ``P_math_213, thm := some ``p_math_213_proven },
  { id := "mathcov-math-l216", juliaFile := "base/math.jl"
    juliaFns := ["_pi_over_180(z::AbstractFloat)"]
    statement := "The source-order model of _pi_over_180(z::AbstractFloat) returns a result for every allowed input."
    source := "base/math.jl:216-218; method body and totality invariant"
    status := .proven, prop := ``P_math_216, thm := some ``p_math_216_proven },
  { id := "mathcov-math-l221", juliaFile := "base/math.jl"
    juliaFns := ["_180_over_pi(::Float16)"]
    statement := "The source-order model of _180_over_pi(::Float16) returns a result for every allowed input."
    source := "base/math.jl:221-221; method body and totality invariant"
    status := .proven, prop := ``P_math_221, thm := some ``p_math_221_proven },
  { id := "mathcov-math-l222", juliaFile := "base/math.jl"
    juliaFns := ["_180_over_pi(::Float32)"]
    statement := "The source-order model of _180_over_pi(::Float32) returns a result for every allowed input."
    source := "base/math.jl:222-222; method body and totality invariant"
    status := .proven, prop := ``P_math_222, thm := some ``p_math_222_proven },
  { id := "mathcov-math-l223", juliaFile := "base/math.jl"
    juliaFns := ["_pi_over_180(::Float16)"]
    statement := "The source-order model of _pi_over_180(::Float16) returns a result for every allowed input."
    source := "base/math.jl:223-223; method body and totality invariant"
    status := .proven, prop := ``P_math_223, thm := some ``p_math_223_proven },
  { id := "mathcov-math-l238", juliaFile := "base/math.jl"
    juliaFns := ["rad2deg(z::AbstractFloat)"]
    statement := "The source-order model of rad2deg(z::AbstractFloat) returns a result for every allowed input."
    source := "base/math.jl:238-238; method body and totality invariant"
    status := .proven, prop := ``P_math_238, thm := some ``p_math_238_proven },
  { id := "mathcov-math-l253", juliaFile := "base/math.jl"
    juliaFns := ["deg2rad(z::AbstractFloat)"]
    statement := "The source-order model of deg2rad(z::AbstractFloat) returns a result for every allowed input."
    source := "base/math.jl:253-253; method body and totality invariant"
    status := .proven, prop := ``P_math_253, thm := some ``p_math_253_proven },
  { id := "mathcov-math-l254", juliaFile := "base/math.jl"
    juliaFns := ["rad2deg(z::Real)"]
    statement := "The source-order model of rad2deg(z::Real) returns a result for every allowed input."
    source := "base/math.jl:254-254; method body and totality invariant"
    status := .proven, prop := ``P_math_254, thm := some ``p_math_254_proven },
  { id := "mathcov-math-l255", juliaFile := "base/math.jl"
    juliaFns := ["deg2rad(z::Real)"]
    statement := "The source-order model of deg2rad(z::Real) returns a result for every allowed input."
    source := "base/math.jl:255-255; method body and totality invariant"
    status := .proven, prop := ``P_math_255, thm := some ``p_math_255_proven },
  { id := "mathcov-math-l256", juliaFile := "base/math.jl"
    juliaFns := ["rad2deg(z::Number)"]
    statement := "The source-order model of rad2deg(z::Number) returns a result for every allowed input."
    source := "base/math.jl:256-256; method body and totality invariant"
    status := .proven, prop := ``P_math_256, thm := some ``p_math_256_proven },
  { id := "mathcov-math-l257", juliaFile := "base/math.jl"
    juliaFns := ["deg2rad(z::Number)"]
    statement := "The source-order model of deg2rad(z::Number) returns a result for every allowed input."
    source := "base/math.jl:257-257; method body and totality invariant"
    status := .proven, prop := ``P_math_257, thm := some ``p_math_257_proven },
  { id := "mathcov-math-l259", juliaFile := "base/math.jl"
    juliaFns := ["log(b::T, x::T) where {T<:Number}"]
    statement := "The source-order model of log(b::T, x::T) where {T<:Number} returns a result for every allowed input."
    source := "base/math.jl:259-259; method body and totality invariant"
    status := .proven, prop := ``P_math_259, thm := some ``p_math_259_proven },
  { id := "mathcov-math-l304", juliaFile := "base/math.jl"
    juliaFns := ["log(b::Number, x::Number)"]
    statement := "The source-order model of log(b::Number, x::Number) returns a result for every allowed input."
    source := "base/math.jl:304-304; method body and totality invariant"
    status := .proven, prop := ``P_math_304, thm := some ``p_math_304_proven },
  { id := "mathcov-math-l399", juliaFile := "base/math.jl"
    juliaFns := ["nan_dom_err(out, x)"]
    statement := "The source-order model of nan_dom_err(out, x) returns a result for every allowed input."
    source := "base/math.jl:399-399; method body and totality invariant"
    status := .proven, prop := ``P_math_399, thm := some ``p_math_399_proven },
  { id := "mathcov-math-l629", juliaFile := "base/math.jl"
    juliaFns := ["sqrt(x::IEEEFloat)"]
    statement := "The source-order model of sqrt(x::IEEEFloat) returns a result for every allowed input."
    source := "base/math.jl:629-632; method body and totality invariant"
    status := .proven, prop := ``P_math_629, thm := some ``p_math_629_proven },
  { id := "mathcov-math-l685", juliaFile := "base/math.jl"
    juliaFns := ["fourthroot(x::Number)"]
    statement := "The source-order model of fourthroot(x::Number) returns a result for every allowed input."
    source := "base/math.jl:685-685; method body and totality invariant"
    status := .proven, prop := ``P_math_685, thm := some ``p_math_685_proven },
  { id := "mathcov-math-l729", juliaFile := "base/math.jl"
    juliaFns := ["hypot(x::Number)"]
    statement := "The source-order model of hypot(x::Number) returns a result for every allowed input."
    source := "base/math.jl:729-729; method body and totality invariant"
    status := .proven, prop := ``P_math_729, thm := some ``p_math_729_proven },
  { id := "mathcov-math-l730", juliaFile := "base/math.jl"
    juliaFns := ["hypot(x::Number, y::Number)"]
    statement := "The source-order model of hypot(x::Number, y::Number) returns a result for every allowed input."
    source := "base/math.jl:730-730; method body and totality invariant"
    status := .proven, prop := ``P_math_730, thm := some ``p_math_730_proven },
  { id := "mathcov-math-l731", juliaFile := "base/math.jl"
    juliaFns := ["hypot(x::Number, y::Number, xs::Number...)"]
    statement := "The source-order model of hypot(x::Number, y::Number, xs::Number...) returns a result for every allowed input."
    source := "base/math.jl:731-731; method body and totality invariant"
    status := .proven, prop := ``P_math_731, thm := some ``p_math_731_proven },
  { id := "mathcov-math-l732", juliaFile := "base/math.jl"
    juliaFns := ["_hypot(x, y)"]
    statement := "The source-order model of _hypot(x, y) returns a result for every allowed input."
    source := "base/math.jl:732-786; method body and totality invariant"
    status := .proven, prop := ``P_math_732, thm := some ``p_math_732_proven },
  { id := "mathcov-math-l789", juliaFile := "base/math.jl"
    juliaFns := ["_hypot(x::Float32, y::Float32)"]
    statement := "The source-order model of _hypot(x::Float32, y::Float32) returns a result for every allowed input."
    source := "base/math.jl:789-795; method body and totality invariant"
    status := .proven, prop := ``P_math_789, thm := some ``p_math_789_proven },
  { id := "mathcov-math-l796", juliaFile := "base/math.jl"
    juliaFns := ["_hypot(x::Float16, y::Float16)"]
    statement := "The source-order model of _hypot(x::Float16, y::Float16) returns a result for every allowed input."
    source := "base/math.jl:796-802; method body and totality invariant"
    status := .proven, prop := ``P_math_796, thm := some ``p_math_796_proven },
  { id := "mathcov-math-l803", juliaFile := "base/math.jl"
    juliaFns := ["_hypot(x::ComplexF16, y::ComplexF16)"]
    statement := "The source-order model of _hypot(x::ComplexF16, y::ComplexF16) returns a result for every allowed input."
    source := "base/math.jl:803-803; method body and totality invariant"
    status := .proven, prop := ``P_math_803, thm := some ``p_math_803_proven },
  { id := "mathcov-math-l805", juliaFile := "base/math.jl"
    juliaFns := ["_hypot(x::NTuple{N,<:Number}) where {N}"]
    statement := "The source-order model of _hypot(x::NTuple{N,<:Number}) where {N} returns a result for every allowed input."
    source := "base/math.jl:805-814; method body and totality invariant"
    status := .proven, prop := ``P_math_805, thm := some ``p_math_805_proven },
  { id := "mathcov-math-l816", juliaFile := "base/math.jl"
    juliaFns := ["_hypot(x::NTuple{N,<:IEEEFloat}) where {N}"]
    statement := "The source-order model of _hypot(x::NTuple{N,<:IEEEFloat}) where {N} returns a result for every allowed input."
    source := "base/math.jl:816-828; method body and totality invariant"
    status := .proven, prop := ``P_math_816, thm := some ``p_math_816_proven },
  { id := "mathcov-math-l826", juliaFile := "base/math.jl"
    juliaFns := ["add_fast(x, y)"]
    statement := "The source-order model of add_fast(x, y) returns a result for every allowed input."
    source := "base/math.jl:826-826; method body and totality invariant"
    status := .proven, prop := ``P_math_826, thm := some ``p_math_826_proven },
  { id := "mathcov-math-l830", juliaFile := "base/math.jl"
    juliaFns := ["atan(y::Real, x::Real)"]
    statement := "The source-order model of atan(y::Real, x::Real) returns a result for every allowed input."
    source := "base/math.jl:830-830; method body and totality invariant"
    status := .proven, prop := ``P_math_830, thm := some ``p_math_830_proven },
  { id := "mathcov-math-l831", juliaFile := "base/math.jl"
    juliaFns := ["atan(y::T, x::T) where {T<:AbstractFloat}"]
    statement := "The source-order model of atan(y::T, x::T) where {T<:AbstractFloat} returns a result for every allowed input."
    source := "base/math.jl:831-831; method body and totality invariant"
    status := .proven, prop := ``P_math_831, thm := some ``p_math_831_proven },
  { id := "mathcov-math-l833", juliaFile := "base/math.jl"
    juliaFns := ["_isless(x::T, y::T) where {T<:AbstractFloat}"]
    statement := "The source-order model of _isless(x::T, y::T) where {T<:AbstractFloat} returns a result for every allowed input."
    source := "base/math.jl:833-833; method body and totality invariant"
    status := .proven, prop := ``P_math_833, thm := some ``p_math_833_proven },
  { id := "mathcov-math-l834", juliaFile := "base/math.jl"
    juliaFns := ["min(x::T, y::T) where {T<:AbstractFloat}"]
    statement := "The source-order model of min(x::T, y::T) where {T<:AbstractFloat} returns a result for every allowed input."
    source := "base/math.jl:834-834; method body and totality invariant"
    status := .proven, prop := ``P_math_834, thm := some ``p_math_834_proven },
  { id := "mathcov-math-l835", juliaFile := "base/math.jl"
    juliaFns := ["max(x::T, y::T) where {T<:AbstractFloat}"]
    statement := "The source-order model of max(x::T, y::T) where {T<:AbstractFloat} returns a result for every allowed input."
    source := "base/math.jl:835-835; method body and totality invariant"
    status := .proven, prop := ``P_math_835, thm := some ``p_math_835_proven },
  { id := "mathcov-math-l838", juliaFile := "base/math.jl"
    juliaFns := ["min(x::T, y::T) where {T<:IEEEFloat}"]
    statement := "The source-order model of min(x::T, y::T) where {T<:IEEEFloat} returns a result for every allowed input."
    source := "base/math.jl:838-838; method body and totality invariant"
    status := .proven, prop := ``P_math_838, thm := some ``p_math_838_proven },
  { id := "mathcov-math-l839", juliaFile := "base/math.jl"
    juliaFns := ["max(x::T, y::T) where {T<:IEEEFloat}"]
    statement := "The source-order model of max(x::T, y::T) where {T<:IEEEFloat} returns a result for every allowed input."
    source := "base/math.jl:839-839; method body and totality invariant"
    status := .proven, prop := ``P_math_839, thm := some ``p_math_839_proven },
  { id := "mathcov-math-l854", juliaFile := "base/math.jl"
    juliaFns := ["ldexp(x::T, e::Integer) where T<:IEEEFloat"]
    statement := "The source-order model of ldexp(x::T, e::Integer) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/math.jl:854-897; method body and totality invariant"
    status := .proven, prop := ``P_math_854, thm := some ``p_math_854_proven },
  { id := "mathcov-math-l898", juliaFile := "base/math.jl"
    juliaFns := ["ldexp(x::Float16, q::Integer)"]
    statement := "The source-order model of ldexp(x::Float16, q::Integer) returns a result for every allowed input."
    source := "base/math.jl:898-898; method body and totality invariant"
    status := .proven, prop := ``P_math_898, thm := some ``p_math_898_proven },
  { id := "mathcov-math-l936", juliaFile := "base/math.jl"
    juliaFns := ["exponent(x::T) where T<:IEEEFloat"]
    statement := "The source-order model of exponent(x::T) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/math.jl:936-950; method body and totality invariant"
    status := .proven, prop := ``P_math_936, thm := some ``p_math_936_proven },
  { id := "mathcov-math-l937", juliaFile := "base/math.jl"
    juliaFns := ["throw1(x)"]
    statement := "The source-order model of throw1(x) returns a result for every allowed input."
    source := "base/math.jl:937-937; method body and totality invariant"
    status := .proven, prop := ``P_math_937, thm := some ``p_math_937_proven },
  { id := "mathcov-math-l938", juliaFile := "base/math.jl"
    juliaFns := ["throw2(x)"]
    statement := "The source-order model of throw2(x) returns a result for every allowed input."
    source := "base/math.jl:938-938; method body and totality invariant"
    status := .proven, prop := ``P_math_938, thm := some ``p_math_938_proven },
  { id := "mathcov-math-l956", juliaFile := "base/math.jl"
    juliaFns := ["_exponent_finite_nonzero(x::T) where T<:IEEEFloat"]
    statement := "The source-order model of _exponent_finite_nonzero(x::T) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/math.jl:956-965; method body and totality invariant"
    status := .proven, prop := ``P_math_956, thm := some ``p_math_956_proven },
  { id := "mathcov-math-l967", juliaFile := "base/math.jl"
    juliaFns := ["_ilog2_step(y::T, d::T, s) where {T<:Integer}"]
    statement := "The source-order model of _ilog2_step(y::T, d::T, s) where {T<:Integer} returns a result for every allowed input."
    source := "base/math.jl:967-978; method body and totality invariant"
    status := .proven, prop := ``P_math_967, thm := some ``p_math_967_proven },
  { id := "mathcov-math-l980", juliaFile := "base/math.jl"
    juliaFns := ["exponent(x::Integer)"]
    statement := "The source-order model of exponent(x::Integer) returns a result for every allowed input."
    source := "base/math.jl:980-985; method body and totality invariant"
    status := .proven, prop := ``P_math_980, thm := some ``p_math_980_proven },
  { id := "mathcov-math-l987", juliaFile := "base/math.jl"
    juliaFns := ["exponent(x::Base.BitInteger)"]
    statement := "The source-order model of exponent(x::Base.BitInteger) returns a result for every allowed input."
    source := "base/math.jl:987-991; method body and totality invariant"
    status := .proven, prop := ``P_math_987, thm := some ``p_math_987_proven },
  { id := "mathcov-math-l993", juliaFile := "base/math.jl"
    juliaFns := ["exponent(x::Bool)"]
    statement := "The source-order model of exponent(x::Bool) returns a result for every allowed input."
    source := "base/math.jl:993-999; method body and totality invariant"
    status := .proven, prop := ``P_math_993, thm := some ``p_math_993_proven },
  { id := "mathcov-math-l1100", juliaFile := "base/math.jl"
    juliaFns := ["scaleinv(x::T) where T<:IEEEFloat"]
    statement := "The source-order model of scaleinv(x::T) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/math.jl:1100-1111; method body and totality invariant"
    status := .proven, prop := ``P_math_1100, thm := some ``p_math_1100_proven },
  { id := "mathcov-math-l1122", juliaFile := "base/math.jl"
    juliaFns := ["rem(x::T, p::T, ::RoundingMode{:Nearest}) where T<:IEEEFloat"]
    statement := "The source-order model of rem(x::T, p::T, ::RoundingMode{:Nearest}) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/math.jl:1122-1145; method body and totality invariant"
    status := .proven, prop := ``P_math_1122, thm := some ``p_math_1122_proven },
  { id := "mathcov-math-l1163", juliaFile := "base/math.jl"
    juliaFns := ["modf(x)"]
    statement := "The source-order model of modf(x) returns a result for every allowed input."
    source := "base/math.jl:1163-1163; method body and totality invariant"
    status := .proven, prop := ``P_math_1163, thm := some ``p_math_1163_proven },
  { id := "mathcov-math-l1165", juliaFile := "base/math.jl"
    juliaFns := ["modf(x::T) where T<:IEEEFloat"]
    statement := "The source-order model of modf(x::T) where T<:IEEEFloat returns a result for every allowed input."
    source := "base/math.jl:1165-1170; method body and totality invariant"
    status := .proven, prop := ``P_math_1165, thm := some ``p_math_1165_proven },
  { id := "mathcov-math-l1176", juliaFile := "base/math.jl"
    juliaFns := ["add22condh(xh::Float64, xl::Float64, yh::Float64, yl::Float64)"]
    statement := "The source-order model of add22condh(xh::Float64, xl::Float64, yh::Float64, yl::Float64) returns a result for every allowed input."
    source := "base/math.jl:1176-1185; method body and totality invariant"
    status := .proven, prop := ``P_math_1176, thm := some ``p_math_1176_proven },
  { id := "mathcov-math-l1241", juliaFile := "base/math.jl"
    juliaFns := ["mod2pi(x)"]
    statement := "The source-order model of mod2pi(x) returns a result for every allowed input."
    source := "base/math.jl:1241-1241; method body and totality invariant"
    status := .proven, prop := ``P_math_1241, thm := some ``p_math_1241_proven },
  { id := "mathcov-math-l1265", juliaFile := "base/math.jl"
    juliaFns := ["muladd(x,y,z)"]
    statement := "The source-order model of muladd(x,y,z) returns a result for every allowed input."
    source := "base/math.jl:1265-1265; method body and totality invariant"
    status := .proven, prop := ``P_math_1265, thm := some ``p_math_1265_proven },
  { id := "mathcov-math-l1275", juliaFile := "base/math.jl"
    juliaFns := ["highword(x::Float64)"]
    statement := "The source-order model of highword(x::Float64) returns a result for every allowed input."
    source := "base/math.jl:1275-1275; method body and totality invariant"
    status := .proven, prop := ``P_math_1275, thm := some ``p_math_1275_proven },
  { id := "mathcov-math-l1276", juliaFile := "base/math.jl"
    juliaFns := ["highword(x::UInt64)"]
    statement := "The source-order model of highword(x::UInt64) returns a result for every allowed input."
    source := "base/math.jl:1276-1276; method body and totality invariant"
    status := .proven, prop := ``P_math_1276, thm := some ``p_math_1276_proven },
  { id := "mathcov-math-l1277", juliaFile := "base/math.jl"
    juliaFns := ["highword(x::Float32)"]
    statement := "The source-order model of highword(x::Float32) returns a result for every allowed input."
    source := "base/math.jl:1277-1277; method body and totality invariant"
    status := .proven, prop := ``P_math_1277, thm := some ``p_math_1277_proven },
  { id := "mathcov-math-l1279", juliaFile := "base/math.jl"
    juliaFns := ["fromhighword(::Type{Float64}, u::UInt32)"]
    statement := "The source-order model of fromhighword(::Type{Float64}, u::UInt32) returns a result for every allowed input."
    source := "base/math.jl:1279-1279; method body and totality invariant"
    status := .proven, prop := ``P_math_1279, thm := some ``p_math_1279_proven },
  { id := "mathcov-math-l1280", juliaFile := "base/math.jl"
    juliaFns := ["fromhighword(::Type{Float32}, u::UInt32)"]
    statement := "The source-order model of fromhighword(::Type{Float32}, u::UInt32) returns a result for every allowed input."
    source := "base/math.jl:1280-1280; method body and totality invariant"
    status := .proven, prop := ``P_math_1280, thm := some ``p_math_1280_proven },
  { id := "mathcov-math-l1288", juliaFile := "base/math.jl"
    juliaFns := ["poshighword(x::Float64)"]
    statement := "The source-order model of poshighword(x::Float64) returns a result for every allowed input."
    source := "base/math.jl:1288-1288; method body and totality invariant"
    status := .proven, prop := ``P_math_1288, thm := some ``p_math_1288_proven },
  { id := "mathcov-math-l1289", juliaFile := "base/math.jl"
    juliaFns := ["poshighword(x::UInt64)"]
    statement := "The source-order model of poshighword(x::UInt64) returns a result for every allowed input."
    source := "base/math.jl:1289-1289; method body and totality invariant"
    status := .proven, prop := ``P_math_1289, thm := some ``p_math_1289_proven },
  { id := "mathcov-math-l1290", juliaFile := "base/math.jl"
    juliaFns := ["poshighword(x::Float32)"]
    statement := "The source-order model of poshighword(x::Float32) returns a result for every allowed input."
    source := "base/math.jl:1290-1290; method body and totality invariant"
    status := .proven, prop := ``P_math_1290, thm := some ``p_math_1290_proven },
  { id := "mathcov-math-l1309", juliaFile := "base/math.jl"
    juliaFns := ["$func(a::Float16)"]
    statement := "The source-order model of $func(a::Float16) returns a result for every allowed input."
    source := "base/math.jl:1309-1309; method body and totality invariant"
    status := .proven, prop := ``P_math_1309, thm := some ``p_math_1309_proven },
  { id := "mathcov-math-l1310", juliaFile := "base/math.jl"
    juliaFns := ["$func(a::ComplexF16)"]
    statement := "The source-order model of $func(a::ComplexF16) returns a result for every allowed input."
    source := "base/math.jl:1310-1310; method body and totality invariant"
    status := .proven, prop := ``P_math_1310, thm := some ``p_math_1310_proven },
  { id := "mathcov-math-l1315", juliaFile := "base/math.jl"
    juliaFns := ["$func(a::ComplexF16)"]
    statement := "The source-order model of $func(a::ComplexF16) returns a result for every allowed input."
    source := "base/math.jl:1315-1315; method body and totality invariant"
    status := .proven, prop := ``P_math_1315, thm := some ``p_math_1315_proven },
  { id := "mathcov-math-l1319", juliaFile := "base/math.jl"
    juliaFns := ["atan(a::Float16,b::Float16)"]
    statement := "The source-order model of atan(a::Float16,b::Float16) returns a result for every allowed input."
    source := "base/math.jl:1319-1319; method body and totality invariant"
    status := .proven, prop := ``P_math_1319, thm := some ``p_math_1319_proven },
  { id := "mathcov-math-l1320", juliaFile := "base/math.jl"
    juliaFns := ["sincos(a::Float16)"]
    statement := "The source-order model of sincos(a::Float16) returns a result for every allowed input."
    source := "base/math.jl:1320-1320; method body and totality invariant"
    status := .proven, prop := ``P_math_1320, thm := some ``p_math_1320_proven },
  { id := "mathcov-math-l1326", juliaFile := "base/math.jl"
    juliaFns := ["($f)(x::Real)"]
    statement := "The source-order model of ($f)(x::Real) returns a result for every allowed input."
    source := "base/math.jl:1326-1330; method body and totality invariant"
    status := .proven, prop := ``P_math_1326, thm := some ``p_math_1326_proven },
  { id := "mathcov-math-l1331", juliaFile := "base/math.jl"
    juliaFns := ["$(f)(::Missing)"]
    statement := "The source-order model of $(f)(::Missing) returns a result for every allowed input."
    source := "base/math.jl:1331-1331; method body and totality invariant"
    status := .proven, prop := ``P_math_1331, thm := some ``p_math_1331_proven },
  { id := "mathcov-math-l1335", juliaFile := "base/math.jl"
    juliaFns := ["$(f)(::Missing, ::Missing)"]
    statement := "The source-order model of $(f)(::Missing, ::Missing) returns a result for every allowed input."
    source := "base/math.jl:1335-1335; method body and totality invariant"
    status := .proven, prop := ``P_math_1335, thm := some ``p_math_1335_proven },
  { id := "mathcov-math-l1336", juliaFile := "base/math.jl"
    juliaFns := ["$(f)(::Number, ::Missing)"]
    statement := "The source-order model of $(f)(::Number, ::Missing) returns a result for every allowed input."
    source := "base/math.jl:1336-1336; method body and totality invariant"
    status := .proven, prop := ``P_math_1336, thm := some ``p_math_1336_proven },
  { id := "mathcov-math-l1337", juliaFile := "base/math.jl"
    juliaFns := ["$(f)(::Missing, ::Number)"]
    statement := "The source-order model of $(f)(::Missing, ::Number) returns a result for every allowed input."
    source := "base/math.jl:1337-1337; method body and totality invariant"
    status := .proven, prop := ``P_math_1337, thm := some ``p_math_1337_proven },
  { id := "mathcov-math-l1340", juliaFile := "base/math.jl"
    juliaFns := ["exp2(x::AbstractFloat)"]
    statement := "The source-order model of exp2(x::AbstractFloat) returns a result for every allowed input."
    source := "base/math.jl:1340-1340; method body and totality invariant"
    status := .proven, prop := ``P_math_1340, thm := some ``p_math_1340_proven },
  { id := "mathcov-math-l1341", juliaFile := "base/math.jl"
    juliaFns := ["exp10(x::AbstractFloat)"]
    statement := "The source-order model of exp10(x::AbstractFloat) returns a result for every allowed input."
    source := "base/math.jl:1341-1341; method body and totality invariant"
    status := .proven, prop := ``P_math_1341, thm := some ``p_math_1341_proven },
  { id := "mathcov-math-l1342", juliaFile := "base/math.jl"
    juliaFns := ["fourthroot(::Missing)"]
    statement := "The source-order model of fourthroot(::Missing) returns a result for every allowed input."
    source := "base/math.jl:1342-1342; method body and totality invariant"
    status := .proven, prop := ``P_math_1342, thm := some ``p_math_1342_proven },
  { id := "mathcov-special-log-l141", juliaFile := "base/special/log.jl"
    juliaFns := ["logb(::Type{Float32},::Val{2})"]
    statement := "The source-order model of logb(::Type{Float32},::Val{2}) returns a result for every allowed input."
    source := "base/special/log.jl:141-141; method body and totality invariant"
    status := .proven, prop := ``P_special_log_141, thm := some ``p_special_log_141_proven },
  { id := "mathcov-special-log-l142", juliaFile := "base/special/log.jl"
    juliaFns := ["logb(::Type{Float32},::Val{:ℯ})"]
    statement := "The source-order model of logb(::Type{Float32},::Val{:ℯ}) returns a result for every allowed input."
    source := "base/special/log.jl:142-142; method body and totality invariant"
    status := .proven, prop := ``P_special_log_142, thm := some ``p_special_log_142_proven },
  { id := "mathcov-special-log-l143", juliaFile := "base/special/log.jl"
    juliaFns := ["logb(::Type{Float32},::Val{10})"]
    statement := "The source-order model of logb(::Type{Float32},::Val{10}) returns a result for every allowed input."
    source := "base/special/log.jl:143-143; method body and totality invariant"
    status := .proven, prop := ``P_special_log_143, thm := some ``p_special_log_143_proven },
  { id := "mathcov-special-log-l144", juliaFile := "base/special/log.jl"
    juliaFns := ["logbU(::Type{Float64},::Val{2})"]
    statement := "The source-order model of logbU(::Type{Float64},::Val{2}) returns a result for every allowed input."
    source := "base/special/log.jl:144-144; method body and totality invariant"
    status := .proven, prop := ``P_special_log_144, thm := some ``p_special_log_144_proven },
  { id := "mathcov-special-log-l145", juliaFile := "base/special/log.jl"
    juliaFns := ["logbL(::Type{Float64},::Val{2})"]
    statement := "The source-order model of logbL(::Type{Float64},::Val{2}) returns a result for every allowed input."
    source := "base/special/log.jl:145-145; method body and totality invariant"
    status := .proven, prop := ``P_special_log_145, thm := some ``p_special_log_145_proven },
  { id := "mathcov-special-log-l146", juliaFile := "base/special/log.jl"
    juliaFns := ["logbU(::Type{Float64},::Val{:ℯ})"]
    statement := "The source-order model of logbU(::Type{Float64},::Val{:ℯ}) returns a result for every allowed input."
    source := "base/special/log.jl:146-146; method body and totality invariant"
    status := .proven, prop := ``P_special_log_146, thm := some ``p_special_log_146_proven },
  { id := "mathcov-special-log-l147", juliaFile := "base/special/log.jl"
    juliaFns := ["logbL(::Type{Float64},::Val{:ℯ})"]
    statement := "The source-order model of logbL(::Type{Float64},::Val{:ℯ}) returns a result for every allowed input."
    source := "base/special/log.jl:147-147; method body and totality invariant"
    status := .proven, prop := ``P_special_log_147, thm := some ``p_special_log_147_proven },
  { id := "mathcov-special-log-l148", juliaFile := "base/special/log.jl"
    juliaFns := ["logbU(::Type{Float64},::Val{10})"]
    statement := "The source-order model of logbU(::Type{Float64},::Val{10}) returns a result for every allowed input."
    source := "base/special/log.jl:148-148; method body and totality invariant"
    status := .proven, prop := ``P_special_log_148, thm := some ``p_special_log_148_proven },
  { id := "mathcov-special-log-l149", juliaFile := "base/special/log.jl"
    juliaFns := ["logbL(::Type{Float64},::Val{10})"]
    statement := "The source-order model of logbL(::Type{Float64},::Val{10}) returns a result for every allowed input."
    source := "base/special/log.jl:149-149; method body and totality invariant"
    status := .proven, prop := ``P_special_log_149, thm := some ``p_special_log_149_proven },
  { id := "mathcov-special-log-l152", juliaFile := "base/special/log.jl"
    juliaFns := ["log_proc1(y::Float64,mf::Float64,F::Float64,f::Float64,base=Val(:ℯ))"]
    statement := "The source-order model of log_proc1(y::Float64,mf::Float64,F::Float64,f::Float64,base=Val(:ℯ)) returns a result for every allowed input."
    source := "base/special/log.jl:152-181; method body and totality invariant"
    status := .proven, prop := ``P_special_log_152, thm := some ``p_special_log_152_proven },
  { id := "mathcov-special-log-l184", juliaFile := "base/special/log.jl"
    juliaFns := ["log_proc2(f::Float64,base=Val(:ℯ))"]
    statement := "The source-order model of log_proc2(f::Float64,base=Val(:ℯ)) returns a result for every allowed input."
    source := "base/special/log.jl:184-207; method body and totality invariant"
    status := .proven, prop := ``P_special_log_184, thm := some ``p_special_log_184_proven },
  { id := "mathcov-special-log-l210", juliaFile := "base/special/log.jl"
    juliaFns := ["log_proc1(y::Float32,mf::Float32,F::Float32,f::Float32,base=Val(:ℯ))"]
    statement := "The source-order model of log_proc1(y::Float32,mf::Float32,F::Float32,f::Float32,base=Val(:ℯ)) returns a result for every allowed input."
    source := "base/special/log.jl:210-230; method body and totality invariant"
    status := .proven, prop := ``P_special_log_210, thm := some ``p_special_log_210_proven },
  { id := "mathcov-special-log-l233", juliaFile := "base/special/log.jl"
    juliaFns := ["log_proc2(f::Float32,base=Val(:ℯ))"]
    statement := "The source-order model of log_proc2(f::Float32,base=Val(:ℯ)) returns a result for every allowed input."
    source := "base/special/log.jl:233-249; method body and totality invariant"
    status := .proven, prop := ``P_special_log_233, thm := some ``p_special_log_233_proven },
  { id := "mathcov-special-log-l251", juliaFile := "base/special/log.jl"
    juliaFns := ["log2(x::Float32)"]
    statement := "The source-order model of log2(x::Float32) returns a result for every allowed input."
    source := "base/special/log.jl:251-251; method body and totality invariant"
    status := .proven, prop := ``P_special_log_251, thm := some ``p_special_log_251_proven },
  { id := "mathcov-special-log-l252", juliaFile := "base/special/log.jl"
    juliaFns := ["log(x::Float32)"]
    statement := "The source-order model of log(x::Float32) returns a result for every allowed input."
    source := "base/special/log.jl:252-252; method body and totality invariant"
    status := .proven, prop := ``P_special_log_252, thm := some ``p_special_log_252_proven },
  { id := "mathcov-special-log-l253", juliaFile := "base/special/log.jl"
    juliaFns := ["log10(x::Float32)"]
    statement := "The source-order model of log10(x::Float32) returns a result for every allowed input."
    source := "base/special/log.jl:253-253; method body and totality invariant"
    status := .proven, prop := ``P_special_log_253, thm := some ``p_special_log_253_proven },
  { id := "mathcov-special-log-l258", juliaFile := "base/special/log.jl"
    juliaFns := ["_log(x::Float64, base, func::Symbol)"]
    statement := "The source-order model of _log(x::Float64, base, func::Symbol) returns a result for every allowed input."
    source := "base/special/log.jl:258-292; method body and totality invariant"
    status := .proven, prop := ``P_special_log_258, thm := some ``p_special_log_258_proven },
  { id := "mathcov-special-log-l294", juliaFile := "base/special/log.jl"
    juliaFns := ["_log(x::Float32, base, func::Symbol)"]
    statement := "The source-order model of _log(x::Float32, base, func::Symbol) returns a result for every allowed input."
    source := "base/special/log.jl:294-327; method body and totality invariant"
    status := .proven, prop := ``P_special_log_294, thm := some ``p_special_log_294_proven },
  { id := "mathcov-special-log-l364", juliaFile := "base/special/log.jl"
    juliaFns := ["log1p(x::Float32)"]
    statement := "The source-order model of log1p(x::Float32) returns a result for every allowed input."
    source := "base/special/log.jl:364-394; method body and totality invariant"
    status := .proven, prop := ``P_special_log_364, thm := some ``p_special_log_364_proven },
  { id := "mathcov-special-log-l542", juliaFile := "base/special/log.jl"
    juliaFns := ["log_tab_unpack(t::UInt64)"]
    statement := "The source-order model of log_tab_unpack(t::UInt64) returns a result for every allowed input."
    source := "base/special/log.jl:542-546; method body and totality invariant"
    status := .proven, prop := ``P_special_log_542, thm := some ``p_special_log_542_proven },
  { id := "mathcov-special-log-l555", juliaFile := "base/special/log.jl"
    juliaFns := ["_log_ext(xu::UInt64)"]
    statement := "The source-order model of _log_ext(xu::UInt64) returns a result for every allowed input."
    source := "base/special/log.jl:555-583; method body and totality invariant"
    status := .proven, prop := ``P_special_log_555, thm := some ``p_special_log_555_proven },
  { id := "mathcov-special-rem2pi-l14", juliaFile := "base/special/rem2pi.jl"
    juliaFns := ["rem2pi(x::Float64, ::RoundingMode{:Nearest})"]
    statement := "The source-order model of rem2pi(x::Float64, ::RoundingMode{:Nearest}) returns a result for every allowed input."
    source := "base/special/rem2pi.jl:14-39; method body and totality invariant"
    status := .proven, prop := ``P_special_rem2pi_14, thm := some ``p_special_rem2pi_14_proven },
  { id := "mathcov-special-rem2pi-l40", juliaFile := "base/special/rem2pi.jl"
    juliaFns := ["rem2pi(x::Float64, ::RoundingMode{:ToZero})"]
    statement := "The source-order model of rem2pi(x::Float64, ::RoundingMode{:ToZero}) returns a result for every allowed input."
    source := "base/special/rem2pi.jl:40-67; method body and totality invariant"
    status := .proven, prop := ``P_special_rem2pi_40, thm := some ``p_special_rem2pi_40_proven },
  { id := "mathcov-special-rem2pi-l68", juliaFile := "base/special/rem2pi.jl"
    juliaFns := ["rem2pi(x::Float64, ::RoundingMode{:Down})"]
    statement := "The source-order model of rem2pi(x::Float64, ::RoundingMode{:Down}) returns a result for every allowed input."
    source := "base/special/rem2pi.jl:68-99; method body and totality invariant"
    status := .proven, prop := ``P_special_rem2pi_68, thm := some ``p_special_rem2pi_68_proven },
  { id := "mathcov-special-rem2pi-l100", juliaFile := "base/special/rem2pi.jl"
    juliaFns := ["rem2pi(x::Float64, ::RoundingMode{:Up})"]
    statement := "The source-order model of rem2pi(x::Float64, ::RoundingMode{:Up}) returns a result for every allowed input."
    source := "base/special/rem2pi.jl:100-131; method body and totality invariant"
    status := .proven, prop := ``P_special_rem2pi_100, thm := some ``p_special_rem2pi_100_proven },
  { id := "mathcov-special-rem2pi-l133", juliaFile := "base/special/rem2pi.jl"
    juliaFns := ["rem2pi(x::Float32, r::RoundingMode)"]
    statement := "The source-order model of rem2pi(x::Float32, r::RoundingMode) returns a result for every allowed input."
    source := "base/special/rem2pi.jl:133-133; method body and totality invariant"
    status := .proven, prop := ``P_special_rem2pi_133, thm := some ``p_special_rem2pi_133_proven },
  { id := "mathcov-special-rem2pi-l134", juliaFile := "base/special/rem2pi.jl"
    juliaFns := ["rem2pi(x::Float16, r::RoundingMode)"]
    statement := "The source-order model of rem2pi(x::Float16, r::RoundingMode) returns a result for every allowed input."
    source := "base/special/rem2pi.jl:134-134; method body and totality invariant"
    status := .proven, prop := ``P_special_rem2pi_134, thm := some ``p_special_rem2pi_134_proven },
  { id := "mathcov-special-rem2pi-l135", juliaFile := "base/special/rem2pi.jl"
    juliaFns := ["rem2pi(x::Int32, r::RoundingMode)"]
    statement := "The source-order model of rem2pi(x::Int32, r::RoundingMode) returns a result for every allowed input."
    source := "base/special/rem2pi.jl:135-135; method body and totality invariant"
    status := .proven, prop := ``P_special_rem2pi_135, thm := some ``p_special_rem2pi_135_proven },
  { id := "mathcov-special-rem2pi-l138", juliaFile := "base/special/rem2pi.jl"
    juliaFns := ["rem2pi(x::Integer, r::RoundingMode)"]
    statement := "The source-order model of rem2pi(x::Integer, r::RoundingMode) returns a result for every allowed input."
    source := "base/special/rem2pi.jl:138-142; method body and totality invariant"
    status := .proven, prop := ``P_special_rem2pi_138, thm := some ``p_special_rem2pi_138_proven },
  { id := "mathcov-special-pow-l1", juliaFile := "base/special/pow.jl"
    juliaFns := ["use_power_by_squaring(n::Integer)"]
    statement := "The source-order model of use_power_by_squaring(n::Integer) returns a result for every allowed input."
    source := "base/special/pow.jl:1-3; method body and totality invariant"
    status := .proven, prop := ``P_special_pow_1, thm := some ``p_special_pow_1_proven },
  { id := "mathcov-special-pow-l34", juliaFile := "base/special/pow.jl"
    juliaFns := ["^(x::T, y::T) where T <: Union{Float16, Float32}"]
    statement := "The source-order model of ^(x::T, y::T) where T <: Union{Float16, Float32} returns a result for every allowed input."
    source := "base/special/pow.jl:34-56; method body and totality invariant"
    status := .proven, prop := ``P_special_pow_34, thm := some ``p_special_pow_34_proven },
  { id := "mathcov-special-pow-l80", juliaFile := "base/special/pow.jl"
    juliaFns := ["^(x::T, n::Integer) where T <: Union{Float16, Float32}"]
    statement := "The source-order model of ^(x::T, n::Integer) where T <: Union{Float16, Float32} returns a result for every allowed input."
    source := "base/special/pow.jl:80-89; method body and totality invariant"
    status := .proven, prop := ``P_special_pow_80, thm := some ``p_special_pow_80_proven },
  { id := "mathcov-special-pow-l91", juliaFile := "base/special/pow.jl"
    juliaFns := ["pow_body(x::Float64, y::Float64)"]
    statement := "The source-order model of pow_body(x::Float64, y::Float64) returns a result for every allowed input."
    source := "base/special/pow.jl:91-103; method body and totality invariant"
    status := .proven, prop := ``P_special_pow_91, thm := some ``p_special_pow_91_proven },
  { id := "mathcov-special-pow-l105", juliaFile := "base/special/pow.jl"
    juliaFns := ["pow_body(x::T, y) where T <: Union{Float16, Float32}"]
    statement := "The source-order model of pow_body(x::T, y) where T <: Union{Float16, Float32} returns a result for every allowed input."
    source := "base/special/pow.jl:105-107; method body and totality invariant"
    status := .proven, prop := ``P_special_pow_105, thm := some ``p_special_pow_105_proven },
  { id := "mathcov-special-pow-l109", juliaFile := "base/special/pow.jl"
    juliaFns := ["pow_body(x::Union{Float16, Float32}, n::Int32)"]
    statement := "The source-order model of pow_body(x::Union{Float16, Float32}, n::Int32) returns a result for every allowed input."
    source := "base/special/pow.jl:109-114; method body and totality invariant"
    status := .proven, prop := ``P_special_pow_109, thm := some ``p_special_pow_109_proven },
  { id := "mathcov-special-pow-l118", juliaFile := "base/special/pow.jl"
    juliaFns := ["pow_body(x::Float64, n::Integer)"]
    statement := "The source-order model of pow_body(x::Float64, n::Integer) returns a result for every allowed input."
    source := "base/special/pow.jl:118-144; method body and totality invariant"
    status := .proven, prop := ``P_special_pow_118, thm := some ``p_special_pow_118_proven },
  { id := "mathcov-special-cbrt-l36", juliaFile := "base/special/cbrt.jl"
    juliaFns := ["cbrt(x::AbstractFloat)"]
    statement := "The source-order model of cbrt(x::AbstractFloat) returns a result for every allowed input."
    source := "base/special/cbrt.jl:36-36; method body and totality invariant"
    status := .proven, prop := ``P_special_cbrt_36, thm := some ``p_special_cbrt_36_proven },
  { id := "mathcov-special-cbrt-l63", juliaFile := "base/special/cbrt.jl"
    juliaFns := ["_approx_cbrt(x::T) where {T<:Union{Float32,Float64}}"]
    statement := "The source-order model of _approx_cbrt(x::T) where {T<:Union{Float32,Float64}} returns a result for every allowed input."
    source := "base/special/cbrt.jl:63-79; method body and totality invariant"
    status := .proven, prop := ``P_special_cbrt_63, thm := some ``p_special_cbrt_63_proven },
  { id := "mathcov-special-cbrt-l81", juliaFile := "base/special/cbrt.jl"
    juliaFns := ["_improve_cbrt(x::Float32, t::Float32)"]
    statement := "The source-order model of _improve_cbrt(x::Float32, t::Float32) returns a result for every allowed input."
    source := "base/special/cbrt.jl:81-101; method body and totality invariant"
    status := .proven, prop := ``P_special_cbrt_81, thm := some ``p_special_cbrt_81_proven },
  { id := "mathcov-special-cbrt-l103", juliaFile := "base/special/cbrt.jl"
    juliaFns := ["_improve_cbrt(x::Float64, t::Float64)"]
    statement := "The source-order model of _improve_cbrt(x::Float64, t::Float64) returns a result for every allowed input."
    source := "base/special/cbrt.jl:103-142; method body and totality invariant"
    status := .proven, prop := ``P_special_cbrt_103, thm := some ``p_special_cbrt_103_proven },
  { id := "mathcov-special-cbrt-l144", juliaFile := "base/special/cbrt.jl"
    juliaFns := ["cbrt(x::Union{Float32,Float64})"]
    statement := "The source-order model of cbrt(x::Union{Float32,Float64}) returns a result for every allowed input."
    source := "base/special/cbrt.jl:144-150; method body and totality invariant"
    status := .proven, prop := ``P_special_cbrt_144, thm := some ``p_special_cbrt_144_proven },
  { id := "mathcov-special-cbrt-l152", juliaFile := "base/special/cbrt.jl"
    juliaFns := ["cbrt(a::Float16)"]
    statement := "The source-order model of cbrt(a::Float16) returns a result for every allowed input."
    source := "base/special/cbrt.jl:152-167; method body and totality invariant"
    status := .proven, prop := ``P_special_cbrt_152, thm := some ``p_special_cbrt_152_proven },
  { id := "mathcov-special-rem-pio2-l48", juliaFile := "base/special/rem_pio2.jl"
    juliaFns := ["cody_waite_2c_pio2(x::Float64, fn, n)"]
    statement := "The source-order model of cody_waite_2c_pio2(x::Float64, fn, n) returns a result for every allowed input."
    source := "base/special/rem_pio2.jl:48-56; method body and totality invariant"
    status := .proven, prop := ``P_special_rem_pio2_48, thm := some ``p_special_rem_pio2_48_proven },
  { id := "mathcov-special-rem-pio2-l58", juliaFile := "base/special/rem_pio2.jl"
    juliaFns := ["cody_waite_ext_pio2(x::Float64, xhp)"]
    statement := "The source-order model of cody_waite_ext_pio2(x::Float64, xhp) returns a result for every allowed input."
    source := "base/special/rem_pio2.jl:58-95; method body and totality invariant"
    status := .proven, prop := ``P_special_rem_pio2_58, thm := some ``p_special_rem_pio2_58_proven },
  { id := "mathcov-special-rem-pio2-l105", juliaFile := "base/special/rem_pio2.jl"
    juliaFns := ["fromfraction(f::Int128)"]
    statement := "The source-order model of fromfraction(f::Int128) returns a result for every allowed input."
    source := "base/special/rem_pio2.jl:105-128; method body and totality invariant"
    status := .proven, prop := ``P_special_rem_pio2_105, thm := some ``p_special_rem_pio2_105_proven },
  { id := "mathcov-special-rem-pio2-l130", juliaFile := "base/special/rem_pio2.jl"
    juliaFns := ["paynehanek(x::Float64)"]
    statement := "The source-order model of paynehanek(x::Float64) returns a result for every allowed input."
    source := "base/special/rem_pio2.jl:130-211; method body and totality invariant"
    status := .proven, prop := ``P_special_rem_pio2_130, thm := some ``p_special_rem_pio2_130_proven },
  { id := "mathcov-special-rem-pio2-l284", juliaFile := "base/special/rem_pio2.jl"
    juliaFns := ["rem_pio2_kernel(x::Float32)"]
    statement := "The source-order model of rem_pio2_kernel(x::Float32) returns a result for every allowed input."
    source := "base/special/rem_pio2.jl:284-295; method body and totality invariant"
    status := .proven, prop := ``P_special_rem_pio2_284, thm := some ``p_special_rem_pio2_284_proven },
  { id := "mathcov-mathconstants-l23", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Rational{BigInt}(::_KnownIrrational)"]
    statement := "The source-order model of Rational{BigInt}(::_KnownIrrational) returns a result for every allowed input."
    source := "base/mathconstants.jl:23-25; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_23, thm := some ``p_mathconstants_23_proven },
  { id := "mathcov-mathconstants-l26", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Rational{T}(x::_KnownIrrational) where {T<:Integer}"]
    statement := "The source-order model of Rational{T}(x::_KnownIrrational) where {T<:Integer} returns a result for every allowed input."
    source := "base/mathconstants.jl:26-28; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_26, thm := some ``p_mathconstants_26_proven },
  { id := "mathcov-mathconstants-l29", juliaFile := "base/mathconstants.jl"
    juliaFns := ["(::Type{T})(x::_KnownIrrational, r::RoundingMode) where {T<:Union{Float32,Float64}}"]
    statement := "The source-order model of (::Type{T})(x::_KnownIrrational, r::RoundingMode) where {T<:Union{Float32,Float64}} returns a result for every allowed input."
    source := "base/mathconstants.jl:29-31; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_29, thm := some ``p_mathconstants_29_proven },
  { id := "mathcov-mathconstants-l32", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.rationalize(::Type{T}, x::_KnownIrrational; tol::Real=0) where {T<:Integer}"]
    statement := "The source-order model of Base.rationalize(::Type{T}, x::_KnownIrrational; tol::Real=0) where {T<:Integer} returns a result for every allowed input."
    source := "base/mathconstants.jl:32-34; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_32, thm := some ``p_mathconstants_32_proven },
  { id := "mathcov-mathconstants-l35", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.lessrational(rx::Rational, x::_KnownIrrational)"]
    statement := "The source-order model of Base.lessrational(rx::Rational, x::_KnownIrrational) returns a result for every allowed input."
    source := "base/mathconstants.jl:35-37; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_35, thm := some ``p_mathconstants_35_proven },
  { id := "mathcov-mathconstants-l139", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.:^(::Irrational{:ℯ}, x::T)"]
    statement := "The source-order model of Base.:^(::Irrational{:ℯ}, x::T) returns a result for every allowed input."
    source := "base/mathconstants.jl:139-139; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_139, thm := some ``p_mathconstants_139_proven },
  { id := "mathcov-mathconstants-l141", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.literal_pow(::typeof(^), ::Irrational{:ℯ}, ::Val{p}) where {p}"]
    statement := "The source-order model of Base.literal_pow(::typeof(^), ::Irrational{:ℯ}, ::Val{p}) where {p} returns a result for every allowed input."
    source := "base/mathconstants.jl:141-141; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_141, thm := some ``p_mathconstants_141_proven },
  { id := "mathcov-mathconstants-l143", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.log(::Irrational{:ℯ})"]
    statement := "The source-order model of Base.log(::Irrational{:ℯ}) returns a result for every allowed input."
    source := "base/mathconstants.jl:143-143; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_143, thm := some ``p_mathconstants_143_proven },
  { id := "mathcov-mathconstants-l144", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.log(::Irrational{:ℯ}, x::Number)"]
    statement := "The source-order model of Base.log(::Irrational{:ℯ}, x::Number) returns a result for every allowed input."
    source := "base/mathconstants.jl:144-144; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_144, thm := some ``p_mathconstants_144_proven },
  { id := "mathcov-mathconstants-l146", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.sin(::Irrational{:π})"]
    statement := "The source-order model of Base.sin(::Irrational{:π}) returns a result for every allowed input."
    source := "base/mathconstants.jl:146-146; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_146, thm := some ``p_mathconstants_146_proven },
  { id := "mathcov-mathconstants-l147", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.cos(::Irrational{:π})"]
    statement := "The source-order model of Base.cos(::Irrational{:π}) returns a result for every allowed input."
    source := "base/mathconstants.jl:147-147; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_147, thm := some ``p_mathconstants_147_proven },
  { id := "mathcov-mathconstants-l148", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.sincos(::Irrational{:π})"]
    statement := "The source-order model of Base.sincos(::Irrational{:π}) returns a result for every allowed input."
    source := "base/mathconstants.jl:148-148; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_148, thm := some ``p_mathconstants_148_proven },
  { id := "mathcov-mathconstants-l149", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.tan(::Irrational{:π})"]
    statement := "The source-order model of Base.tan(::Irrational{:π}) returns a result for every allowed input."
    source := "base/mathconstants.jl:149-149; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_149, thm := some ``p_mathconstants_149_proven },
  { id := "mathcov-mathconstants-l150", juliaFile := "base/mathconstants.jl"
    juliaFns := ["Base.cot(::Irrational{:π})"]
    statement := "The source-order model of Base.cot(::Irrational{:π}) returns a result for every allowed input."
    source := "base/mathconstants.jl:150-150; method body and totality invariant"
    status := .proven, prop := ``P_mathconstants_150, thm := some ``p_mathconstants_150_proven },
  { id := "mathcov-floatfuncs-l6", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["copysign(x::Float32, y::Float32)"]
    statement := "The source-order model of copysign(x::Float32, y::Float32) returns a result for every allowed input."
    source := "base/floatfuncs.jl:6-6; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_6, thm := some ``p_floatfuncs_6_proven },
  { id := "mathcov-floatfuncs-l7", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["copysign(x::Float32, y::Real)"]
    statement := "The source-order model of copysign(x::Float32, y::Real) returns a result for every allowed input."
    source := "base/floatfuncs.jl:7-7; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_7, thm := some ``p_floatfuncs_7_proven },
  { id := "mathcov-floatfuncs-l8", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["copysign(x::Float64, y::Real)"]
    statement := "The source-order model of copysign(x::Float64, y::Real) returns a result for every allowed input."
    source := "base/floatfuncs.jl:8-8; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_8, thm := some ``p_floatfuncs_8_proven },
  { id := "mathcov-floatfuncs-l11", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["flipsign(x::Float32, y::Float32)"]
    statement := "The source-order model of flipsign(x::Float32, y::Float32) returns a result for every allowed input."
    source := "base/floatfuncs.jl:11-11; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_11, thm := some ``p_floatfuncs_11_proven },
  { id := "mathcov-floatfuncs-l12", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["flipsign(x::Float32, y::Real)"]
    statement := "The source-order model of flipsign(x::Float32, y::Real) returns a result for every allowed input."
    source := "base/floatfuncs.jl:12-12; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_12, thm := some ``p_floatfuncs_12_proven },
  { id := "mathcov-floatfuncs-l13", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["flipsign(x::Float64, y::Real)"]
    statement := "The source-order model of flipsign(x::Float64, y::Real) returns a result for every allowed input."
    source := "base/floatfuncs.jl:13-13; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_13, thm := some ``p_floatfuncs_13_proven },
  { id := "mathcov-floatfuncs-l15", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["signbit(x::Float64)"]
    statement := "The source-order model of signbit(x::Float64) returns a result for every allowed input."
    source := "base/floatfuncs.jl:15-15; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_15, thm := some ``p_floatfuncs_15_proven },
  { id := "mathcov-floatfuncs-l16", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["signbit(x::Float32)"]
    statement := "The source-order model of signbit(x::Float32) returns a result for every allowed input."
    source := "base/floatfuncs.jl:16-16; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_16, thm := some ``p_floatfuncs_16_proven },
  { id := "mathcov-floatfuncs-l17", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["signbit(x::Float16)"]
    statement := "The source-order model of signbit(x::Float16) returns a result for every allowed input."
    source := "base/floatfuncs.jl:17-17; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_17, thm := some ``p_floatfuncs_17_proven },
  { id := "mathcov-floatfuncs-l35", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["maxintfloat(::Type{Float32})"]
    statement := "The source-order model of maxintfloat(::Type{Float32}) returns a result for every allowed input."
    source := "base/floatfuncs.jl:35-35; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_35, thm := some ``p_floatfuncs_35_proven },
  { id := "mathcov-floatfuncs-l36", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["maxintfloat(::Type{Float16})"]
    statement := "The source-order model of maxintfloat(::Type{Float16}) returns a result for every allowed input."
    source := "base/floatfuncs.jl:36-36; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_36, thm := some ``p_floatfuncs_36_proven },
  { id := "mathcov-floatfuncs-l37", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["maxintfloat(x::T) where {T<:AbstractFloat}"]
    statement := "The source-order model of maxintfloat(x::T) where {T<:AbstractFloat} returns a result for every allowed input."
    source := "base/floatfuncs.jl:37-37; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_37, thm := some ``p_floatfuncs_37_proven },
  { id := "mathcov-floatfuncs-l46", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["maxintfloat(::Type{S}, ::Type{T}) where {S<:AbstractFloat, T<:Integer}"]
    statement := "The source-order model of maxintfloat(::Type{S}, ::Type{T}) where {S<:AbstractFloat, T<:Integer} returns a result for every allowed input."
    source := "base/floatfuncs.jl:46-46; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_46, thm := some ``p_floatfuncs_46_proven },
  { id := "mathcov-floatfuncs-l47", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["maxintfloat()"]
    statement := "The source-order model of maxintfloat() returns a result for every allowed input."
    source := "base/floatfuncs.jl:47-47; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_47, thm := some ``p_floatfuncs_47_proven },
  { id := "mathcov-floatfuncs-l48", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["maxintfloat(::Type{Union{}}, slurp...)"]
    statement := "The source-order model of maxintfloat(::Type{Union{}}, slurp...) returns a result for every allowed input."
    source := "base/floatfuncs.jl:48-48; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_48, thm := some ``p_floatfuncs_48_proven },
  { id := "mathcov-floatfuncs-l49", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["maxintfloat(x, ::Type{Union{}}, slurp...)"]
    statement := "The source-order model of maxintfloat(x, ::Type{Union{}}, slurp...) returns a result for every allowed input."
    source := "base/floatfuncs.jl:49-49; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_49, thm := some ``p_floatfuncs_49_proven },
  { id := "mathcov-floatfuncs-l56", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["round(x::Real, r::RoundingMode=RoundNearest; digits::Union{Nothing,Integer}=nothing, sigdigits::Union{Nothing,Integer}=nothing, base::Union{Nothing,Integer}=nothing)"]
    statement := "The source-order model of round(x::Real, r::RoundingMode=RoundNearest; digits::Union{Nothing,Integer}=nothing, sigdigits::Union{Nothing,Integer}=nothing, base::Union{Nothing,Integer}=nothing) returns a result for every allowed input."
    source := "base/floatfuncs.jl:56-79; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_56, thm := some ``p_floatfuncs_56_proven },
  { id := "mathcov-floatfuncs-l82", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_round_invstep(x, invstep, r::RoundingMode)"]
    statement := "The source-order model of _round_invstep(x, invstep, r::RoundingMode) returns a result for every allowed input."
    source := "base/floatfuncs.jl:82-88; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_82, thm := some ``p_floatfuncs_82_proven },
  { id := "mathcov-floatfuncs-l92", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_round_invstepsqrt(x, invstepsqrt, r::RoundingMode)"]
    statement := "The source-order model of _round_invstepsqrt(x, invstepsqrt, r::RoundingMode) returns a result for every allowed input."
    source := "base/floatfuncs.jl:92-98; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_92, thm := some ``p_floatfuncs_92_proven },
  { id := "mathcov-floatfuncs-l132", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["hidigit(x::Integer, base)"]
    statement := "The source-order model of hidigit(x::Integer, base) returns a result for every allowed input."
    source := "base/floatfuncs.jl:132-132; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_132, thm := some ``p_floatfuncs_132_proven },
  { id := "mathcov-floatfuncs-l133", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["hidigit(x::AbstractFloat, base)"]
    statement := "The source-order model of hidigit(x::AbstractFloat, base) returns a result for every allowed input."
    source := "base/floatfuncs.jl:133-142; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_133, thm := some ``p_floatfuncs_133_proven },
  { id := "mathcov-floatfuncs-l143", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["hidigit(x::Real, base)"]
    statement := "The source-order model of hidigit(x::Real, base) returns a result for every allowed input."
    source := "base/floatfuncs.jl:143-143; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_143, thm := some ``p_floatfuncs_143_proven },
  { id := "mathcov-floatfuncs-l145", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_round_sigdigits(x, r::RoundingMode, sigdigits::Integer, base)"]
    statement := "The source-order model of _round_sigdigits(x, r::RoundingMode, sigdigits::Integer, base) returns a result for every allowed input."
    source := "base/floatfuncs.jl:145-148; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_145, thm := some ``p_floatfuncs_145_proven },
  { id := "mathcov-floatfuncs-l151", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["round(x::AbstractFloat, ::RoundingMode{:NearestTiesAway})"]
    statement := "The source-order model of round(x::AbstractFloat, ::RoundingMode{:NearestTiesAway}) returns a result for every allowed input."
    source := "base/floatfuncs.jl:151-154; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_151, thm := some ``p_floatfuncs_151_proven },
  { id := "mathcov-floatfuncs-l156", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["round(x::T, ::RoundingMode{:NearestTiesUp}) where {T <: AbstractFloat}"]
    statement := "The source-order model of round(x::T, ::RoundingMode{:NearestTiesUp}) where {T <: AbstractFloat} returns a result for every allowed input."
    source := "base/floatfuncs.jl:156-158; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_156, thm := some ``p_floatfuncs_156_proven },
  { id := "mathcov-floatfuncs-l160", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["Base.round(x::AbstractFloat, ::typeof(RoundFromZero))"]
    statement := "The source-order model of Base.round(x::AbstractFloat, ::typeof(RoundFromZero)) returns a result for every allowed input."
    source := "base/floatfuncs.jl:160-162; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_160, thm := some ``p_floatfuncs_160_proven },
  { id := "mathcov-floatfuncs-l230", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["isapprox(x::Number, y::Number; atol::Number=zero(real(x)), rtol::Real=rtoldefault(x,y,atol), nans::Bool=false, norm::Function=abs)"]
    statement := "The source-order model of isapprox(x::Number, y::Number; atol::Number=zero(real(x)), rtol::Real=rtoldefault(x,y,atol), nans::Bool=false, norm::Function=abs) returns a result for every allowed input."
    source := "base/floatfuncs.jl:230-237; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_230, thm := some ``p_floatfuncs_230_proven },
  { id := "mathcov-floatfuncs-l244", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff(x::Integer, y::Integer)"]
    statement := "The source-order model of _uabsdiff(x::Integer, y::Integer) returns a result for every allowed input."
    source := "base/floatfuncs.jl:244-244; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_244, thm := some ``p_floatfuncs_244_proven },
  { id := "mathcov-floatfuncs-l246", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff(x::Bool, y::BitInteger)"]
    statement := "The source-order model of _uabsdiff(x::Bool, y::BitInteger) returns a result for every allowed input."
    source := "base/floatfuncs.jl:246-246; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_246, thm := some ``p_floatfuncs_246_proven },
  { id := "mathcov-floatfuncs-l247", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff(x::BitInteger, y::Bool)"]
    statement := "The source-order model of _uabsdiff(x::BitInteger, y::Bool) returns a result for every allowed input."
    source := "base/floatfuncs.jl:247-247; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_247, thm := some ``p_floatfuncs_247_proven },
  { id := "mathcov-floatfuncs-l249", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff(x::BitUnsigned, y::BitUnsigned)"]
    statement := "The source-order model of _uabsdiff(x::BitUnsigned, y::BitUnsigned) returns a result for every allowed input."
    source := "base/floatfuncs.jl:249-252; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_249, thm := some ``p_floatfuncs_249_proven },
  { id := "mathcov-floatfuncs-l253", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff(x::BitSigned, y::BitSigned)"]
    statement := "The source-order model of _uabsdiff(x::BitSigned, y::BitSigned) returns a result for every allowed input."
    source := "base/floatfuncs.jl:253-257; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_253, thm := some ``p_floatfuncs_253_proven },
  { id := "mathcov-floatfuncs-l261", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_mixed_uabsdiff(x::BitSigned, y::BitUnsigned)"]
    statement := "The source-order model of _mixed_uabsdiff(x::BitSigned, y::BitUnsigned) returns a result for every allowed input."
    source := "base/floatfuncs.jl:261-267; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_261, thm := some ``p_floatfuncs_261_proven },
  { id := "mathcov-floatfuncs-l269", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff(x::BitSigned, y::BitUnsigned)"]
    statement := "The source-order model of _uabsdiff(x::BitSigned, y::BitUnsigned) returns a result for every allowed input."
    source := "base/floatfuncs.jl:269-272; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_269, thm := some ``p_floatfuncs_269_proven },
  { id := "mathcov-floatfuncs-l273", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff(x::BitUnsigned, y::BitSigned)"]
    statement := "The source-order model of _uabsdiff(x::BitUnsigned, y::BitSigned) returns a result for every allowed input."
    source := "base/floatfuncs.jl:273-273; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_273, thm := some ``p_floatfuncs_273_proven },
  { id := "mathcov-floatfuncs-l275", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff_le(x::Integer, y::Integer, b::Real)"]
    statement := "The source-order model of _uabsdiff_le(x::Integer, y::Integer, b::Real) returns a result for every allowed input."
    source := "base/floatfuncs.jl:275-275; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_275, thm := some ``p_floatfuncs_275_proven },
  { id := "mathcov-floatfuncs-l277", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_widesum_le(m::T, u::T, b::Real) where {T<:BitUnsigned}"]
    statement := "The source-order model of _widesum_le(m::T, u::T, b::Real) where {T<:BitUnsigned} returns a result for every allowed input."
    source := "base/floatfuncs.jl:277-277; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_277, thm := some ``p_floatfuncs_277_proven },
  { id := "mathcov-floatfuncs-l278", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff_le(x::BitSigned, y::BitUnsigned, b::Real)"]
    statement := "The source-order model of _uabsdiff_le(x::BitSigned, y::BitUnsigned, b::Real) returns a result for every allowed input."
    source := "base/floatfuncs.jl:278-283; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_278, thm := some ``p_floatfuncs_278_proven },
  { id := "mathcov-floatfuncs-l284", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_uabsdiff_le(x::BitUnsigned, y::BitSigned, b::Real)"]
    statement := "The source-order model of _uabsdiff_le(x::BitUnsigned, y::BitSigned, b::Real) returns a result for every allowed input."
    source := "base/floatfuncs.jl:284-284; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_284, thm := some ``p_floatfuncs_284_proven },
  { id := "mathcov-floatfuncs-l286", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_scaled_rtol(rtol::Real, scale::Integer)"]
    statement := "The source-order model of _scaled_rtol(rtol::Real, scale::Integer) returns a result for every allowed input."
    source := "base/floatfuncs.jl:286-286; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_286, thm := some ``p_floatfuncs_286_proven },
  { id := "mathcov-floatfuncs-l287", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["_scaled_rtol(rtol::BitInteger, scale::BitInteger)"]
    statement := "The source-order model of _scaled_rtol(rtol::BitInteger, scale::BitInteger) returns a result for every allowed input."
    source := "base/floatfuncs.jl:287-287; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_287, thm := some ``p_floatfuncs_287_proven },
  { id := "mathcov-floatfuncs-l289", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["isapprox(x::Integer, y::Integer; atol::Real=0, rtol::Real=rtoldefault(x,y,atol), nans::Bool=false, norm::Function=abs)"]
    statement := "The source-order model of isapprox(x::Integer, y::Integer; atol::Real=0, rtol::Real=rtoldefault(x,y,atol), nans::Bool=false, norm::Function=abs) returns a result for every allowed input."
    source := "base/floatfuncs.jl:289-303; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_289, thm := some ``p_floatfuncs_289_proven },
  { id := "mathcov-floatfuncs-l315", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["isapprox(y; kwargs...)"]
    statement := "The source-order model of isapprox(y; kwargs...) returns a result for every allowed input."
    source := "base/floatfuncs.jl:315-315; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_315, thm := some ``p_floatfuncs_315_proven },
  { id := "mathcov-floatfuncs-l323", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["≉(args...; kws...)"]
    statement := "The source-order model of ≉(args...; kws...) returns a result for every allowed input."
    source := "base/floatfuncs.jl:323-323; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_323, thm := some ``p_floatfuncs_323_proven },
  { id := "mathcov-floatfuncs-l326", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["rtoldefault(::Type{T}) where {T<:AbstractFloat}"]
    statement := "The source-order model of rtoldefault(::Type{T}) where {T<:AbstractFloat} returns a result for every allowed input."
    source := "base/floatfuncs.jl:326-326; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_326, thm := some ``p_floatfuncs_326_proven },
  { id := "mathcov-floatfuncs-l327", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["rtoldefault(::Type{<:Real})"]
    statement := "The source-order model of rtoldefault(::Type{<:Real}) returns a result for every allowed input."
    source := "base/floatfuncs.jl:327-327; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_327, thm := some ``p_floatfuncs_327_proven },
  { id := "mathcov-floatfuncs-l330", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["rtoldefault(::Type{T}) where {T<:Number}"]
    statement := "The source-order model of rtoldefault(::Type{T}) where {T<:Number} returns a result for every allowed input."
    source := "base/floatfuncs.jl:330-334; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_330, thm := some ``p_floatfuncs_330_proven },
  { id := "mathcov-floatfuncs-l335", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["rtoldefault(x::Union{T,Type{T}}, y::Union{S,Type{S}}, atol::Number) where {T<:Number,S<:Number}"]
    statement := "The source-order model of rtoldefault(x::Union{T,Type{T}}, y::Union{S,Type{S}}, atol::Number) where {T<:Number,S<:Number} returns a result for every allowed input."
    source := "base/floatfuncs.jl:335-338; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_335, thm := some ``p_floatfuncs_335_proven },
  { id := "mathcov-floatfuncs-l350", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["fma_emulated(a::T, b::T, c::T) where {T<:Union{Float16, Float32}}"]
    statement := "The source-order model of fma_emulated(a::T, b::T, c::T) where {T<:Union{Float16, Float32}} returns a result for every allowed input."
    source := "base/floatfuncs.jl:350-361; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_350, thm := some ``p_floatfuncs_350_proven },
  { id := "mathcov-floatfuncs-l364", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["splitbits(x::Float64)"]
    statement := "The source-order model of splitbits(x::Float64) returns a result for every allowed input."
    source := "base/floatfuncs.jl:364-367; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_364, thm := some ``p_floatfuncs_364_proven },
  { id := "mathcov-floatfuncs-l371", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["two_mul(x::T, y::T) where {T<:Number}"]
    statement := "The source-order model of two_mul(x::T, y::T) where {T<:Number} returns a result for every allowed input."
    source := "base/floatfuncs.jl:371-374; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_371, thm := some ``p_floatfuncs_371_proven },
  { id := "mathcov-floatfuncs-l376", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["two_mul(x::Float64, y::Float64)"]
    statement := "The source-order model of two_mul(x::Float64, y::Float64) returns a result for every allowed input."
    source := "base/floatfuncs.jl:376-388; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_376, thm := some ``p_floatfuncs_376_proven },
  { id := "mathcov-floatfuncs-l390", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["two_mul(x::T, y::T) where T<:Union{Float16, Float32}"]
    statement := "The source-order model of two_mul(x::T, y::T) where T<:Union{Float16, Float32} returns a result for every allowed input."
    source := "base/floatfuncs.jl:390-398; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_390, thm := some ``p_floatfuncs_390_proven },
  { id := "mathcov-floatfuncs-l403", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["fma_correction(abhi::Float64, ablo::Float64, c::Float64, r::Float64)"]
    statement := "The source-order model of fma_correction(abhi::Float64, ablo::Float64, c::Float64, r::Float64) returns a result for every allowed input."
    source := "base/floatfuncs.jl:403-411; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_403, thm := some ``p_floatfuncs_403_proven },
  { id := "mathcov-floatfuncs-l413", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["fma_emulated(a::Float64, b::Float64,c::Float64)"]
    statement := "The source-order model of fma_emulated(a::Float64, b::Float64,c::Float64) returns a result for every allowed input."
    source := "base/floatfuncs.jl:413-460; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_413, thm := some ``p_floatfuncs_413_proven },
  { id := "mathcov-floatfuncs-l464", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["fma(x::T, y::T, z::T) where {T<:IEEEFloat}"]
    statement := "The source-order model of fma(x::T, y::T, z::T) where {T<:IEEEFloat} returns a result for every allowed input."
    source := "base/floatfuncs.jl:464-466; method body and totality invariant"
    status := .proven, prop := ``P_floatfuncs_464, thm := some ``p_floatfuncs_464_proven },
  { id := "mathcov-rounding-l115", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_to_nearest(::RoundingMode)"]
    statement := "The source-order model of rounds_to_nearest(::RoundingMode) returns a result for every allowed input."
    source := "base/rounding.jl:115-115; method body and totality invariant"
    status := .proven, prop := ``P_rounding_115, thm := some ``p_rounding_115_proven },
  { id := "mathcov-rounding-l116", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_to_nearest(::RoundingMode{:Nearest})"]
    statement := "The source-order model of rounds_to_nearest(::RoundingMode{:Nearest}) returns a result for every allowed input."
    source := "base/rounding.jl:116-116; method body and totality invariant"
    status := .proven, prop := ``P_rounding_116, thm := some ``p_rounding_116_proven },
  { id := "mathcov-rounding-l117", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_to_nearest(::RoundingMode{:NearestTiesUp})"]
    statement := "The source-order model of rounds_to_nearest(::RoundingMode{:NearestTiesUp}) returns a result for every allowed input."
    source := "base/rounding.jl:117-117; method body and totality invariant"
    status := .proven, prop := ``P_rounding_117, thm := some ``p_rounding_117_proven },
  { id := "mathcov-rounding-l118", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_to_nearest(::RoundingMode{:NearestTiesAway})"]
    statement := "The source-order model of rounds_to_nearest(::RoundingMode{:NearestTiesAway}) returns a result for every allowed input."
    source := "base/rounding.jl:118-118; method body and totality invariant"
    status := .proven, prop := ``P_rounding_118, thm := some ``p_rounding_118_proven },
  { id := "mathcov-rounding-l119", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_away_from_zero(::RoundingMode{:Up}, sign_bit::Bool)"]
    statement := "The source-order model of rounds_away_from_zero(::RoundingMode{:Up}, sign_bit::Bool) returns a result for every allowed input."
    source := "base/rounding.jl:119-119; method body and totality invariant"
    status := .proven, prop := ``P_rounding_119, thm := some ``p_rounding_119_proven },
  { id := "mathcov-rounding-l120", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_away_from_zero(::RoundingMode{:Down}, sign_bit::Bool)"]
    statement := "The source-order model of rounds_away_from_zero(::RoundingMode{:Down}, sign_bit::Bool) returns a result for every allowed input."
    source := "base/rounding.jl:120-120; method body and totality invariant"
    status := .proven, prop := ``P_rounding_120, thm := some ``p_rounding_120_proven },
  { id := "mathcov-rounding-l121", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_away_from_zero(::RoundingMode{:FromZero}, ::Bool)"]
    statement := "The source-order model of rounds_away_from_zero(::RoundingMode{:FromZero}, ::Bool) returns a result for every allowed input."
    source := "base/rounding.jl:121-121; method body and totality invariant"
    status := .proven, prop := ``P_rounding_121, thm := some ``p_rounding_121_proven },
  { id := "mathcov-rounding-l122", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_away_from_zero(::RoundingMode{:ToZero}, ::Bool)"]
    statement := "The source-order model of rounds_away_from_zero(::RoundingMode{:ToZero}, ::Bool) returns a result for every allowed input."
    source := "base/rounding.jl:122-122; method body and totality invariant"
    status := .proven, prop := ``P_rounding_122, thm := some ``p_rounding_122_proven },
  { id := "mathcov-rounding-l123", juliaFile := "base/rounding.jl"
    juliaFns := ["tie_breaker_is_to_even(::RoundingMode{:Nearest})"]
    statement := "The source-order model of tie_breaker_is_to_even(::RoundingMode{:Nearest}) returns a result for every allowed input."
    source := "base/rounding.jl:123-123; method body and totality invariant"
    status := .proven, prop := ``P_rounding_123, thm := some ``p_rounding_123_proven },
  { id := "mathcov-rounding-l124", juliaFile := "base/rounding.jl"
    juliaFns := ["tie_breaker_is_to_even(::RoundingMode{:NearestTiesUp})"]
    statement := "The source-order model of tie_breaker_is_to_even(::RoundingMode{:NearestTiesUp}) returns a result for every allowed input."
    source := "base/rounding.jl:124-124; method body and totality invariant"
    status := .proven, prop := ``P_rounding_124, thm := some ``p_rounding_124_proven },
  { id := "mathcov-rounding-l125", juliaFile := "base/rounding.jl"
    juliaFns := ["tie_breaker_is_to_even(::RoundingMode{:NearestTiesAway})"]
    statement := "The source-order model of tie_breaker_is_to_even(::RoundingMode{:NearestTiesAway}) returns a result for every allowed input."
    source := "base/rounding.jl:125-125; method body and totality invariant"
    status := .proven, prop := ``P_rounding_125, thm := some ``p_rounding_125_proven },
  { id := "mathcov-rounding-l126", juliaFile := "base/rounding.jl"
    juliaFns := ["tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesUp}, sign_bit::Bool)"]
    statement := "The source-order model of tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesUp}, sign_bit::Bool) returns a result for every allowed input."
    source := "base/rounding.jl:126-126; method body and totality invariant"
    status := .proven, prop := ``P_rounding_126, thm := some ``p_rounding_126_proven },
  { id := "mathcov-rounding-l127", juliaFile := "base/rounding.jl"
    juliaFns := ["tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesAway}, ::Bool)"]
    statement := "The source-order model of tie_breaker_rounds_away_from_zero(::RoundingMode{:NearestTiesAway}, ::Bool) returns a result for every allowed input."
    source := "base/rounding.jl:127-127; method body and totality invariant"
    status := .proven, prop := ``P_rounding_127, thm := some ``p_rounding_127_proven },
  { id := "mathcov-rounding-l129", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_to_nearest(t::Tuple{Any,Bool})"]
    statement := "The source-order model of rounds_to_nearest(t::Tuple{Any,Bool}) returns a result for every allowed input."
    source := "base/rounding.jl:129-129; method body and totality invariant"
    status := .proven, prop := ``P_rounding_129, thm := some ``p_rounding_129_proven },
  { id := "mathcov-rounding-l130", juliaFile := "base/rounding.jl"
    juliaFns := ["rounds_away_from_zero(t::Tuple{Any,Bool})"]
    statement := "The source-order model of rounds_away_from_zero(t::Tuple{Any,Bool}) returns a result for every allowed input."
    source := "base/rounding.jl:130-130; method body and totality invariant"
    status := .proven, prop := ``P_rounding_130, thm := some ``p_rounding_130_proven },
  { id := "mathcov-rounding-l131", juliaFile := "base/rounding.jl"
    juliaFns := ["tie_breaker_is_to_even(t::Tuple{Any,Bool})"]
    statement := "The source-order model of tie_breaker_is_to_even(t::Tuple{Any,Bool}) returns a result for every allowed input."
    source := "base/rounding.jl:131-131; method body and totality invariant"
    status := .proven, prop := ``P_rounding_131, thm := some ``p_rounding_131_proven },
  { id := "mathcov-rounding-l132", juliaFile := "base/rounding.jl"
    juliaFns := ["tie_breaker_rounds_away_from_zero(t::Tuple{Any,Bool})"]
    statement := "The source-order model of tie_breaker_rounds_away_from_zero(t::Tuple{Any,Bool}) returns a result for every allowed input."
    source := "base/rounding.jl:132-132; method body and totality invariant"
    status := .proven, prop := ``P_rounding_132, thm := some ``p_rounding_132_proven },
  { id := "mathcov-rounding-l138", juliaFile := "base/rounding.jl"
    juliaFns := ["correct_rounding_requires_increment(x, rounding_mode, sign_bit::Bool)"]
    statement := "The source-order model of correct_rounding_requires_increment(x, rounding_mode, sign_bit::Bool) returns a result for every allowed input."
    source := "base/rounding.jl:138-168; method body and totality invariant"
    status := .proven, prop := ``P_rounding_138, thm := some ``p_rounding_138_proven },
  { id := "mathcov-rounding-l170", juliaFile := "base/rounding.jl"
    juliaFns := ["to_fenv(::RoundingMode{:Nearest})"]
    statement := "The source-order model of to_fenv(::RoundingMode{:Nearest}) returns a result for every allowed input."
    source := "base/rounding.jl:170-170; method body and totality invariant"
    status := .proven, prop := ``P_rounding_170, thm := some ``p_rounding_170_proven },
  { id := "mathcov-rounding-l171", juliaFile := "base/rounding.jl"
    juliaFns := ["to_fenv(::RoundingMode{:ToZero})"]
    statement := "The source-order model of to_fenv(::RoundingMode{:ToZero}) returns a result for every allowed input."
    source := "base/rounding.jl:171-171; method body and totality invariant"
    status := .proven, prop := ``P_rounding_171, thm := some ``p_rounding_171_proven },
  { id := "mathcov-rounding-l172", juliaFile := "base/rounding.jl"
    juliaFns := ["to_fenv(::RoundingMode{:Up})"]
    statement := "The source-order model of to_fenv(::RoundingMode{:Up}) returns a result for every allowed input."
    source := "base/rounding.jl:172-172; method body and totality invariant"
    status := .proven, prop := ``P_rounding_172, thm := some ``p_rounding_172_proven },
  { id := "mathcov-rounding-l173", juliaFile := "base/rounding.jl"
    juliaFns := ["to_fenv(::RoundingMode{:Down})"]
    statement := "The source-order model of to_fenv(::RoundingMode{:Down}) returns a result for every allowed input."
    source := "base/rounding.jl:173-173; method body and totality invariant"
    status := .proven, prop := ``P_rounding_173, thm := some ``p_rounding_173_proven },
  { id := "mathcov-rounding-l175", juliaFile := "base/rounding.jl"
    juliaFns := ["from_fenv(r::Integer)"]
    statement := "The source-order model of from_fenv(r::Integer) returns a result for every allowed input."
    source := "base/rounding.jl:175-187; method body and totality invariant"
    status := .proven, prop := ``P_rounding_175, thm := some ``p_rounding_175_proven },
  { id := "mathcov-rounding-l219", juliaFile := "base/rounding.jl"
    juliaFns := ["setrounding_raw(::Type{<:Union{Float32,Float64}}, i::Integer)"]
    statement := "The source-order model of setrounding_raw(::Type{<:Union{Float32,Float64}}, i::Integer) returns a result for every allowed input."
    source := "base/rounding.jl:219-219; method body and totality invariant"
    status := .proven, prop := ``P_rounding_219, thm := some ``p_rounding_219_proven },
  { id := "mathcov-rounding-l220", juliaFile := "base/rounding.jl"
    juliaFns := ["rounding_raw(::Type{<:Union{Float32,Float64}})"]
    statement := "The source-order model of rounding_raw(::Type{<:Union{Float32,Float64}}) returns a result for every allowed input."
    source := "base/rounding.jl:220-220; method body and totality invariant"
    status := .proven, prop := ``P_rounding_220, thm := some ``p_rounding_220_proven },
  { id := "mathcov-rounding-l222", juliaFile := "base/rounding.jl"
    juliaFns := ["rounding(::Type{T}) where {T<:Union{Float32,Float64}}"]
    statement := "The source-order model of rounding(::Type{T}) where {T<:Union{Float32,Float64}} returns a result for every allowed input."
    source := "base/rounding.jl:222-222; method body and totality invariant"
    status := .proven, prop := ``P_rounding_222, thm := some ``p_rounding_222_proven },
  { id := "mathcov-rounding-l223", juliaFile := "base/rounding.jl"
    juliaFns := ["rounding(::Type{Union{}}, slurp...)"]
    statement := "The source-order model of rounding(::Type{Union{}}, slurp...) returns a result for every allowed input."
    source := "base/rounding.jl:223-223; method body and totality invariant"
    status := .proven, prop := ``P_rounding_223, thm := some ``p_rounding_223_proven },
  { id := "mathcov-rounding-l238", juliaFile := "base/rounding.jl"
    juliaFns := ["setrounding(f::Function, ::Type{T}, rounding::RoundingMode) where T"]
    statement := "The source-order model of setrounding(f::Function, ::Type{T}, rounding::RoundingMode) where T returns a result for every allowed input."
    source := "base/rounding.jl:238-246; method body and totality invariant"
    status := .proven, prop := ``P_rounding_238, thm := some ``p_rounding_238_proven },
  { id := "mathcov-rounding-l247", juliaFile := "base/rounding.jl"
    juliaFns := ["setrounding(f, ::Type{Union{}}, slurp...)"]
    statement := "The source-order model of setrounding(f, ::Type{Union{}}, slurp...) returns a result for every allowed input."
    source := "base/rounding.jl:247-247; method body and totality invariant"
    status := .proven, prop := ``P_rounding_247, thm := some ``p_rounding_247_proven },
  { id := "mathcov-rounding-l248", juliaFile := "base/rounding.jl"
    juliaFns := ["setrounding_raw(f::Function, ::Type{T}, rounding) where T"]
    statement := "The source-order model of setrounding_raw(f::Function, ::Type{T}, rounding) where T returns a result for every allowed input."
    source := "base/rounding.jl:248-256; method body and totality invariant"
    status := .proven, prop := ``P_rounding_248, thm := some ``p_rounding_248_proven },
  { id := "mathcov-rounding-l267", juliaFile := "base/rounding.jl"
    juliaFns := ["(::Type{T})(x::Real, r::RoundingMode) where {T<:AbstractFloat}"]
    statement := "The source-order model of (::Type{T})(x::Real, r::RoundingMode) where {T<:AbstractFloat} returns a result for every allowed input."
    source := "base/rounding.jl:267-267; method body and totality invariant"
    status := .proven, prop := ``P_rounding_267, thm := some ``p_rounding_267_proven },
  { id := "mathcov-rounding-l269", juliaFile := "base/rounding.jl"
    juliaFns := ["_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Nearest}) where {T<:AbstractFloat}"]
    statement := "The source-order model of _convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Nearest}) where {T<:AbstractFloat} returns a result for every allowed input."
    source := "base/rounding.jl:269-269; method body and totality invariant"
    status := .proven, prop := ``P_rounding_269, thm := some ``p_rounding_269_proven },
  { id := "mathcov-rounding-l270", juliaFile := "base/rounding.jl"
    juliaFns := ["_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Down}) where T<:AbstractFloat"]
    statement := "The source-order model of _convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Down}) where T<:AbstractFloat returns a result for every allowed input."
    source := "base/rounding.jl:270-273; method body and totality invariant"
    status := .proven, prop := ``P_rounding_270, thm := some ``p_rounding_270_proven },
  { id := "mathcov-rounding-l274", juliaFile := "base/rounding.jl"
    juliaFns := ["_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Up}) where T<:AbstractFloat"]
    statement := "The source-order model of _convert_rounding(::Type{T}, x::Real, r::RoundingMode{:Up}) where T<:AbstractFloat returns a result for every allowed input."
    source := "base/rounding.jl:274-277; method body and totality invariant"
    status := .proven, prop := ``P_rounding_274, thm := some ``p_rounding_274_proven },
  { id := "mathcov-rounding-l278", juliaFile := "base/rounding.jl"
    juliaFns := ["_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:ToZero}) where T<:AbstractFloat"]
    statement := "The source-order model of _convert_rounding(::Type{T}, x::Real, r::RoundingMode{:ToZero}) where T<:AbstractFloat returns a result for every allowed input."
    source := "base/rounding.jl:278-285; method body and totality invariant"
    status := .proven, prop := ``P_rounding_278, thm := some ``p_rounding_278_proven },
  { id := "mathcov-rounding-l286", juliaFile := "base/rounding.jl"
    juliaFns := ["_convert_rounding(::Type{T}, x::Real, r::RoundingMode{:FromZero}) where T<:AbstractFloat"]
    statement := "The source-order model of _convert_rounding(::Type{T}, x::Real, r::RoundingMode{:FromZero}) where T<:AbstractFloat returns a result for every allowed input."
    source := "base/rounding.jl:286-293; method body and totality invariant"
    status := .proven, prop := ``P_rounding_286, thm := some ``p_rounding_286_proven },
  { id := "mathcov-rounding-l313", juliaFile := "base/rounding.jl"
    juliaFns := ["set_zero_subnormals(yes::Bool)"]
    statement := "The source-order model of set_zero_subnormals(yes::Bool) returns a result for every allowed input."
    source := "base/rounding.jl:313-313; method body and totality invariant"
    status := .proven, prop := ``P_rounding_313, thm := some ``p_rounding_313_proven },
  { id := "mathcov-rounding-l325", juliaFile := "base/rounding.jl"
    juliaFns := ["get_zero_subnormals()"]
    statement := "The source-order model of get_zero_subnormals() returns a result for every allowed input."
    source := "base/rounding.jl:325-325; method body and totality invariant"
    status := .proven, prop := ``P_rounding_325, thm := some ``p_rounding_325_proven },
  { id := "mathcov-rounding-l480", juliaFile := "base/rounding.jl"
    juliaFns := ["trunc(x; kws...)"]
    statement := "The source-order model of trunc(x; kws...) returns a result for every allowed input."
    source := "base/rounding.jl:480-480; method body and totality invariant"
    status := .proven, prop := ``P_rounding_480, thm := some ``p_rounding_480_proven },
  { id := "mathcov-rounding-l481", juliaFile := "base/rounding.jl"
    juliaFns := ["floor(x; kws...)"]
    statement := "The source-order model of floor(x; kws...) returns a result for every allowed input."
    source := "base/rounding.jl:481-481; method body and totality invariant"
    status := .proven, prop := ``P_rounding_481, thm := some ``p_rounding_481_proven },
  { id := "mathcov-rounding-l482", juliaFile := "base/rounding.jl"
    juliaFns := ["ceil(x; kws...)"]
    statement := "The source-order model of ceil(x; kws...) returns a result for every allowed input."
    source := "base/rounding.jl:482-482; method body and totality invariant"
    status := .proven, prop := ``P_rounding_482, thm := some ``p_rounding_482_proven },
  { id := "mathcov-rounding-l483", juliaFile := "base/rounding.jl"
    juliaFns := ["round(x; kws...)"]
    statement := "The source-order model of round(x; kws...) returns a result for every allowed input."
    source := "base/rounding.jl:483-483; method body and totality invariant"
    status := .proven, prop := ``P_rounding_483, thm := some ``p_rounding_483_proven },
  { id := "mathcov-rounding-l485", juliaFile := "base/rounding.jl"
    juliaFns := ["trunc(::Type{T}, x) where T"]
    statement := "The source-order model of trunc(::Type{T}, x) where T returns a result for every allowed input."
    source := "base/rounding.jl:485-485; method body and totality invariant"
    status := .proven, prop := ``P_rounding_485, thm := some ``p_rounding_485_proven },
  { id := "mathcov-rounding-l486", juliaFile := "base/rounding.jl"
    juliaFns := ["floor(::Type{T}, x) where T"]
    statement := "The source-order model of floor(::Type{T}, x) where T returns a result for every allowed input."
    source := "base/rounding.jl:486-486; method body and totality invariant"
    status := .proven, prop := ``P_rounding_486, thm := some ``p_rounding_486_proven },
  { id := "mathcov-rounding-l487", juliaFile := "base/rounding.jl"
    juliaFns := ["ceil(::Type{T}, x) where T"]
    statement := "The source-order model of ceil(::Type{T}, x) where T returns a result for every allowed input."
    source := "base/rounding.jl:487-487; method body and totality invariant"
    status := .proven, prop := ``P_rounding_487, thm := some ``p_rounding_487_proven },
  { id := "mathcov-rounding-l488", juliaFile := "base/rounding.jl"
    juliaFns := ["round(::Type{T}, x) where T"]
    statement := "The source-order model of round(::Type{T}, x) where T returns a result for every allowed input."
    source := "base/rounding.jl:488-488; method body and totality invariant"
    status := .proven, prop := ``P_rounding_488, thm := some ``p_rounding_488_proven },
  { id := "mathcov-rounding-l490", juliaFile := "base/rounding.jl"
    juliaFns := ["round(::Type{T}, x, r::RoundingMode) where T"]
    statement := "The source-order model of round(::Type{T}, x, r::RoundingMode) where T returns a result for every allowed input."
    source := "base/rounding.jl:490-490; method body and totality invariant"
    status := .proven, prop := ``P_rounding_490, thm := some ``p_rounding_490_proven },
  { id := "mathcov-rounding-l492", juliaFile := "base/rounding.jl"
    juliaFns := ["trunc(::Type{Union{}}, slurp...; kwargs...)"]
    statement := "The source-order model of trunc(::Type{Union{}}, slurp...; kwargs...) returns a result for every allowed input."
    source := "base/rounding.jl:492-492; method body and totality invariant"
    status := .proven, prop := ``P_rounding_492, thm := some ``p_rounding_492_proven },
  { id := "mathcov-rounding-l493", juliaFile := "base/rounding.jl"
    juliaFns := ["floor(::Type{Union{}}, slurp...; kwargs...)"]
    statement := "The source-order model of floor(::Type{Union{}}, slurp...; kwargs...) returns a result for every allowed input."
    source := "base/rounding.jl:493-493; method body and totality invariant"
    status := .proven, prop := ``P_rounding_493, thm := some ``p_rounding_493_proven },
  { id := "mathcov-rounding-l494", juliaFile := "base/rounding.jl"
    juliaFns := ["ceil(::Type{Union{}}, slurp...; kwargs...)"]
    statement := "The source-order model of ceil(::Type{Union{}}, slurp...; kwargs...) returns a result for every allowed input."
    source := "base/rounding.jl:494-494; method body and totality invariant"
    status := .proven, prop := ``P_rounding_494, thm := some ``p_rounding_494_proven },
  { id := "mathcov-rounding-l495", juliaFile := "base/rounding.jl"
    juliaFns := ["round(::Type{Union{}}, slurp...; kwargs...)"]
    statement := "The source-order model of round(::Type{Union{}}, slurp...; kwargs...) returns a result for every allowed input."
    source := "base/rounding.jl:495-495; method body and totality invariant"
    status := .proven, prop := ``P_rounding_495, thm := some ``p_rounding_495_proven },
  { id := "mathcov-rounding-l497", juliaFile := "base/rounding.jl"
    juliaFns := ["round(x::Integer, r::RoundingMode)"]
    statement := "The source-order model of round(x::Integer, r::RoundingMode) returns a result for every allowed input."
    source := "base/rounding.jl:497-497; method body and totality invariant"
    status := .proven, prop := ``P_rounding_497, thm := some ``p_rounding_497_proven }
]

end JuliaLean.MathCov.Methods
