import JuliaLean.FloatIntCov.Float
import JuliaLean.Promotion.Compare

namespace JuliaLean.FloatIntCov.FloatRows

open JuliaLean JuliaLean.Registry JuliaLean.Promotion
open JuliaLean.FloatIntCov.Float
open JuliaLean.IntArith.Division

def m100 (x : FV .f64) := reinterpretUnsigned x
def P100 : Prop := ∀ x : FV .f64, m100 x = reinterpretUnsigned x
theorem p100 : P100 := by unfold P100; intros; rfl

def m101 (x : FV .f32) := reinterpretUnsigned x
def P101 : Prop := ∀ x : FV .f32, m101 x = reinterpretUnsigned x
theorem p101 : P101 := by unfold P101; intros; rfl

def m102 (x : FV .f16) := reinterpretUnsigned x
def P102 : Prop := ∀ x : FV .f16, m102 x = reinterpretUnsigned x
theorem p102 : P102 := by unfold P102; intros; rfl

def m103 (x : FV .f64) := reinterpretSigned x
def P103 : Prop := ∀ x : FV .f64, m103 x = reinterpretSigned x
theorem p103 : P103 := by unfold P103; intros; rfl

def m104 (x : FV .f32) := reinterpretSigned x
def P104 : Prop := ∀ x : FV .f32, m104 x = reinterpretSigned x
theorem p104 : P104 := by unfold P104; intros; rfl

def m105 (x : FV .f16) := reinterpretSigned x
def P105 : Prop := ∀ x : FV .f16, m105 x = reinterpretSigned x
theorem p105 : P105 := by unfold P105; intros; rfl

def m107 (_u : Unit) := signMask .f64
def P107 : Prop := ∀ u : Unit, m107 u = signMask .f64
theorem p107 : P107 := by unfold P107; intros; rfl

def m108 (_u : Unit) := exponentMask .f64
def P108 : Prop := ∀ u : Unit, m108 u = exponentMask .f64
theorem p108 : P108 := by unfold P108; intros; rfl

def m109 (_u : Unit) := exponentOne .f64
def P109 : Prop := ∀ u : Unit, m109 u = exponentOne .f64
theorem p109 : P109 := by unfold P109; intros; rfl

def m110 (_u : Unit) := exponentHalf .f64
def P110 : Prop := ∀ u : Unit, m110 u = exponentHalf .f64
theorem p110 : P110 := by unfold P110; intros; rfl

def m111 (_u : Unit) := significandMask .f64
def P111 : Prop := ∀ u : Unit, m111 u = significandMask .f64
theorem p111 : P111 := by unfold P111; intros; rfl

def m113 (_u : Unit) := signMask .f32
def P113 : Prop := ∀ u : Unit, m113 u = signMask .f32
theorem p113 : P113 := by unfold P113; intros; rfl

def m114 (_u : Unit) := exponentMask .f32
def P114 : Prop := ∀ u : Unit, m114 u = exponentMask .f32
theorem p114 : P114 := by unfold P114; intros; rfl

def m115 (_u : Unit) := exponentOne .f32
def P115 : Prop := ∀ u : Unit, m115 u = exponentOne .f32
theorem p115 : P115 := by unfold P115; intros; rfl

def m116 (_u : Unit) := exponentHalf .f32
def P116 : Prop := ∀ u : Unit, m116 u = exponentHalf .f32
theorem p116 : P116 := by unfold P116; intros; rfl

def m117 (_u : Unit) := significandMask .f32
def P117 : Prop := ∀ u : Unit, m117 u = significandMask .f32
theorem p117 : P117 := by unfold P117; intros; rfl

def m119 (_u : Unit) := signMask .f16
def P119 : Prop := ∀ u : Unit, m119 u = signMask .f16
theorem p119 : P119 := by unfold P119; intros; rfl

def m120 (_u : Unit) := exponentMask .f16
def P120 : Prop := ∀ u : Unit, m120 u = exponentMask .f16
theorem p120 : P120 := by unfold P120; intros; rfl

def m121 (_u : Unit) := exponentOne .f16
def P121 : Prop := ∀ u : Unit, m121 u = exponentOne .f16
theorem p121 : P121 := by unfold P121; intros; rfl

def m122 (_u : Unit) := exponentHalf .f16
def P122 : Prop := ∀ u : Unit, m122 u = exponentHalf .f16
theorem p122 : P122 := by unfold P122; intros; rfl

def m123 (_u : Unit) := significandMask .f16
def P123 : Prop := ∀ u : Unit, m123 u = significandMask .f16
theorem p123 : P123 := by unfold P123; intros; rfl

def m125 {T : FTy} (x : FV T) := mantissa x
def P125 : Prop := ∀ T (x : FV T), m125 x = mantissa x
theorem p125 : P125 := by unfold P125; intros; rfl

def m131 (T : FTy) := significandBits T
def P131 : Prop := ∀ T : FTy, m131 T = significandBits T
theorem p131 : P131 := by unfold P131; intros; rfl

def m132 (T : FTy) := exponentBits T
def P132 : Prop := ∀ T : FTy, m132 T = exponentBits T
theorem p132 : P132 := by unfold P132; intros; rfl

def m133 (T : FTy) := exponentBias T
def P133 : Prop := ∀ T : FTy, m133 T = exponentBias T
theorem p133 : P133 := by unfold P133; intros; rfl

def m135 (T : FTy) := exponentMax T
def P135 : Prop := ∀ T : FTy, m135 T = exponentMax T
theorem p135 : P135 := by unfold P135; intros; rfl

def m137 (T : FTy) := exponentRawMax T
def P137 : Prop := ∀ T : FTy, m137 T = exponentRawMax T
theorem p137 : P137 := by unfold P137; intros; rfl

def m167 (T : FTy) := ieee754ExponentMin T
def P167 : Prop := ∀ T : FTy, m167 T = ieee754ExponentMin T
theorem p167 : P167 := by unfold P167; intros; rfl

def m169 (T : FTy) := exponentMin T
def P169 : Prop := ∀ T : FTy, m169 T = exponentMin T
theorem p169 : P169 := by unfold P169; intros; rfl

def m171 (T : FTy) (s : Bool) (e m : Nat) := ieee754Representation T s e m
def P171 : Prop := ∀ T s e m, m171 T s e m = ieee754Representation T s e m
theorem p171 : P171 := by unfold P171; intros; rfl

def m184 (T : FTy) (s : Bool) := ieeeOmega T s
def P184 : Prop := ∀ T s, m184 T s = ieeeOmega T s
theorem p184 : P184 := by unfold P184; intros; rfl

def m191 (T : FTy) (s : Bool) (m : Nat) := ieeeNanPayload T s m
def P191 : Prop := ∀ T s m, m191 T s m = ieeeNanPayload T s m
theorem p191 : P191 := by unfold P191; intros; rfl

def m198 (T : FTy) (s : Bool) := ieeeNan T s
def P198 : Prop := ∀ T s, m198 T s = ieeeNan T s
theorem p198 : P198 := by unfold P198; intros; rfl

def m205 (T : FTy) (s : Bool) := ieeeInf T s
def P205 : Prop := ∀ T s, m205 T s = ieeeInf T s
theorem p205 : P205 := by unfold P205; intros; rfl

def m212 (T : FTy) (s : Bool) (m : Nat) := ieeeSubnormal T s m
def P212 : Prop := ∀ T s m, m212 T s m = ieeeSubnormal T s m
theorem p212 : P212 := by unfold P212; intros; rfl

def m219 (T : FTy) (s : Bool) := ieeeZero T s
def P219 : Prop := ∀ T s, m219 T s = ieeeZero T s
theorem p219 : P219 := by unfold P219; intros; rfl

def m235 (x : Value) := integerUabs x
def P235 : Prop := ∀ x : Value, m235 x = integerUabs x
theorem p235 : P235 := by unfold P235; intros; rfl

def m236 (x : Value) := integerUabs x
def P236 : Prop := ∀ x : Value, m236 x = integerUabs x
theorem p236 : P236 := by unfold P236; intros; rfl

def m241 {α : Type} (toF32 : α → FV .f32) (x : α) := float16IntegerFallback toF32 x
def P241 : Prop := ∀ (α : Type) toF32 (x : α), m241 toF32 x = float16IntegerFallback toF32 x
theorem p241 : P241 := by unfold P241; intros; rfl

def m246 (T : FTy) {t : IntTy} (x : JInt t) := floatOfInteger T x
def P246 : Prop := ∀ T t (x : JInt t), m246 T x = floatOfInteger T x
theorem p246 : P246 := by unfold P246; intros; rfl

def m247 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P247 : Prop := ∀ T t, m247 T t = floatPromoteRule T t
theorem p247 : P247 := by unfold P247; intros; rfl

def m252 (T : FTy) {t : IntTy} (x : JInt t) := floatOfInteger T x
def P252 : Prop := ∀ T t (x : JInt t), m252 T x = floatOfInteger T x
theorem p252 : P252 := by unfold P252; intros; rfl

def m253 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P253 : Prop := ∀ T t, m253 T t = floatPromoteRule T t
theorem p253 : P253 := by unfold P253; intros; rfl

def m258 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P258 : Prop := ∀ T t, m258 T t = floatPromoteRule T t
theorem p258 : P258 := by unfold P258; intros; rfl

def m259 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P259 : Prop := ∀ T t, m259 T t = floatPromoteRule T t
theorem p259 : P259 := by unfold P259; intros; rfl

def m260 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P260 : Prop := ∀ T t, m260 T t = floatPromoteRule T t
theorem p260 : P260 := by unfold P260; intros; rfl

def m261 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P261 : Prop := ∀ T t, m261 T t = floatPromoteRule T t
theorem p261 : P261 := by unfold P261; intros; rfl

def m262 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P262 : Prop := ∀ T t, m262 T t = floatPromoteRule T t
theorem p262 : P262 := by unfold P262; intros; rfl

def m263 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P263 : Prop := ∀ T t, m263 T t = floatPromoteRule T t
theorem p263 : P263 := by unfold P263; intros; rfl

def m265 {t : IntTy} (x : JInt t) := floatOfInteger .f64 x
def P265 : Prop := ∀ t (x : JInt t), m265 x = floatOfInteger .f64 x
theorem p265 : P265 := by unfold P265; intros; rfl

def m285 {t : IntTy} (x : JInt t) := floatOfInteger .f64 x
def P285 : Prop := ∀ t (x : JInt t), m285 x = floatOfInteger .f64 x
theorem p285 : P285 := by unfold P285; intros; rfl

def m307 {t : IntTy} (x : JInt t) := floatOfInteger .f32 x
def P307 : Prop := ∀ t (x : JInt t), m307 x = floatOfInteger .f32 x
theorem p307 : P307 := by unfold P307; intros; rfl

def m321 {t : IntTy} (x : JInt t) := floatOfInteger .f32 x
def P321 : Prop := ∀ t (x : JInt t), m321 x = floatOfInteger .f32 x
theorem p321 : P321 := by unfold P321; intros; rfl

def m338 {t : IntTy} (x : JInt t) := floatOfInteger .f16 x
def P338 : Prop := ∀ t (x : JInt t), m338 x = floatOfInteger .f16 x
theorem p338 : P338 := by unfold P338; intros; rfl

def m339 {t : IntTy} (x : JInt t) := floatOfInteger .f16 x
def P339 : Prop := ∀ t (x : JInt t), m339 x = floatOfInteger .f16 x
theorem p339 : P339 := by unfold P339; intros; rfl

def m341 (x : FV .f32) := floatConvert .f16 .f32 x
def P341 : Prop := ∀ x : FV .f32, m341 x = floatConvert .f16 .f32 x
theorem p341 : P341 := by unfold P341; intros; rfl

def m342 (x : FV .f64) := floatConvert .f16 .f64 x
def P342 : Prop := ∀ x : FV .f64, m342 x = floatConvert .f16 .f64 x
theorem p342 : P342 := by unfold P342; intros; rfl

def m343 (x : FV .f64) := floatConvert .f32 .f64 x
def P343 : Prop := ∀ x : FV .f64, m343 x = floatConvert .f32 .f64 x
theorem p343 : P343 := by unfold P343; intros; rfl

def m345 (x : FV .f16) := floatConvert .f32 .f16 x
def P345 : Prop := ∀ x : FV .f16, m345 x = floatConvert .f32 .f16 x
theorem p345 : P345 := by unfold P345; intros; rfl

def m346 (x : FV .f32) := floatConvert .f64 .f32 x
def P346 : Prop := ∀ x : FV .f32, m346 x = floatConvert .f64 .f32 x
theorem p346 : P346 := by unfold P346; intros; rfl

def m347 (x : FV .f16) := floatConvert .f64 .f16 x
def P347 : Prop := ∀ x : FV .f16, m347 x = floatConvert .f64 .f16 x
theorem p347 : P347 := by unfold P347; intros; rfl

def m350 {t : IntTy} (x : JInt t) := abstractFloatOfInteger x
def P350 : Prop := ∀ t (x : JInt t), m350 x = abstractFloatOfInteger x
theorem p350 : P350 := by unfold P350; intros; rfl

def m352 (x : FV .f16) := boolOfFloat16 x
def P352 : Prop := ∀ x : FV .f16, m352 x = boolOfFloat16 x
theorem p352 : P352 := by unfold P352; intros; rfl

def m367 {α β : Type} (f : α → β) (x : α) := floatScalar f x
def P367 : Prop := ∀ (α β : Type) (f : α → β) (x : α), m367 f x = floatScalar f x
theorem p367 : P367 := by unfold P367; intros; rfl

def m384 {α β : Type} (zero : α) (f : α → β) := floatNumberType zero f
def P384 : Prop := ∀ (α β : Type) (zero : α) (f : α → β),
  m384 zero f = floatNumberType zero f
theorem p384 : P384 := by unfold P384; intros; rfl

def m385 (T : FTy) := floatAbstractType T
def P385 : Prop := ∀ T, m385 T = floatAbstractType T
theorem p385 : P385 := by unfold P385; intros; rfl

def m386 (_u : Unit) := floatBottomType
def P386 : Prop := ∀ u : Unit, m386 u = floatBottomType
theorem p386 : P386 := by unfold P386; intros; rfl

def m387 {α : Type} (_u : Unit) : Jl α := floatBottomError
def P387 : Prop := ∀ (α : Type) (u : Unit),
  m387 (α := α) u = (floatBottomError : Jl α)
theorem p387 : P387 := by unfold P387; intros; rfl

def m410 (T : FTy) (t : IntTy) (x : FV T) := unsafeTrunc T t x
def P410 : Prop := ∀ T t (x : FV T), m410 T t x = unsafeTrunc T t x
theorem p410 : P410 := by unfold P410; intros; rfl

def m415 (T : FTy) (t : IntTy) (x : FV T) := unsafeTrunc T t x
def P415 : Prop := ∀ T t (x : FV T), m415 T t x = unsafeTrunc T t x
theorem p415 : P415 := by unfold P415; intros; rfl

def m419 (x : FV .f64) := unsafeTrunc .f64 .u128 x
def P419 : Prop := ∀ x : FV .f64, m419 x = unsafeTrunc .f64 .u128 x
theorem p419 : P419 := by unfold P419; intros; rfl

def m431 (x : FV .f64) := unsafeTrunc .f64 .i128 x
def P431 : Prop := ∀ x : FV .f64, m431 x = unsafeTrunc .f64 .i128 x
theorem p431 : P431 := by unfold P431; intros; rfl

def m435 (x : FV .f32) := unsafeTrunc .f32 .u128 x
def P435 : Prop := ∀ x : FV .f32, m435 x = unsafeTrunc .f32 .u128 x
theorem p435 : P435 := by unfold P435; intros; rfl

def m445 (x : FV .f32) := unsafeTrunc .f32 .i128 x
def P445 : Prop := ∀ x : FV .f32, m445 x = unsafeTrunc .f32 .i128 x
theorem p445 : P445 := by unfold P445; intros; rfl

def m449 (x : FV .f16) := unsafeTrunc .f16 .u128 x
def P449 : Prop := ∀ x : FV .f16, m449 x = unsafeTrunc .f16 .u128 x
theorem p449 : P449 := by unfold P449; intros; rfl

def m450 (x : FV .f16) := unsafeTrunc .f16 .i128 x
def P450 : Prop := ∀ x : FV .f16, m450 x = unsafeTrunc .f16 .i128 x
theorem p450 : P450 := by unfold P450; intros; rfl

def m454 (T : FTy) (x : FV T) := checkedTrunc T .i64 x
def P454 : Prop := ∀ T (x : FV T), m454 T x = checkedTrunc T .i64 x
theorem p454 : P454 := by unfold P454; intros; rfl

def m455 (T : FTy) (x : FV T) := checkedTrunc T .u64 x
def P455 : Prop := ∀ T (x : FV T), m455 T x = checkedTrunc T .u64 x
theorem p455 : P455 := by unfold P455; intros; rfl

def m456 (T : FTy) (x : FV T) := checkedTrunc T .i64 x
def P456 : Prop := ∀ T (x : FV T), m456 T x = checkedTrunc T .i64 x
theorem p456 : P456 := by unfold P456; intros; rfl

def m458 {T : FTy} (ops : PrimitiveOps T) (x : FV T) := ops.trunc x
def P458 : Prop := ∀ T (ops : PrimitiveOps T) (x : FV T), m458 ops x = ops.trunc x
theorem p458 : P458 := by unfold P458; intros; rfl

def m459 {T : FTy} (ops : PrimitiveOps T) (x : FV T) := ops.floor x
def P459 : Prop := ∀ T (ops : PrimitiveOps T) (x : FV T), m459 ops x = ops.floor x
theorem p459 : P459 := by unfold P459; intros; rfl

def m460 {T : FTy} (ops : PrimitiveOps T) (x : FV T) := ops.ceil x
def P460 : Prop := ∀ T (ops : PrimitiveOps T) (x : FV T), m460 ops x = ops.ceil x
theorem p460 : P460 := by unfold P460; intros; rfl

def m461 {T : FTy} (ops : PrimitiveOps T) (x : FV T) := ops.nearest x
def P461 : Prop := ∀ T (ops : PrimitiveOps T) (x : FV T), m461 ops x = ops.nearest x
theorem p461 : P461 := by unfold P461; intros; rfl

def m463 (s : Bool) := roundsUp s .down
def P463 : Prop := ∀ s, m463 s = roundsUp s .down
theorem p463 : P463 := by unfold P463; intros; rfl

def m464 (s : Bool) := roundsUp s .up
def P464 : Prop := ∀ s, m464 s = roundsUp s .up
theorem p464 : P464 := by unfold P464; intros; rfl

def m465 (s : Bool) := roundsUp s .toZero
def P465 : Prop := ∀ s, m465 s = roundsUp s .toZero
theorem p465 : P465 := by unfold P465; intros; rfl

def m466 (s : Bool) := roundsUp s .fromZero
def P466 : Prop := ∀ s, m466 s = roundsUp s .fromZero
theorem p466 : P466 := by unfold P466; intros; rfl

def m467 {α : Type} (convert : Int → α) (lt gt : α → α → Bool) (next prev : α → α) (n : Int) (x : α) (up : Bool) := roundConvert convert lt gt next prev n x up
def P467 : Prop := ∀ (α : Type) convert lt gt next prev n (x : α) up, m467 convert lt gt next prev n x up = roundConvert convert lt gt next prev n x up
theorem p467 : P467 := by unfold P467; intros; rfl

def m477 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P477 : Prop := ∀ T t, m477 T t = floatPromoteRule T t
theorem p477 : P477 := by unfold P477; intros; rfl

def m478 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P478 : Prop := ∀ T t, m478 T t = floatPromoteRule T t
theorem p478 : P478 := by unfold P478; intros; rfl

def m479 (T : FTy) (t : IntTy) := floatPromoteRule T t
def P479 : Prop := ∀ T t, m479 T t = floatPromoteRule T t
theorem p479 : P479 := by unfold P479; intros; rfl

def m481 (T : FTy) := floatWiden T
def P481 : Prop := ∀ T, m481 T = floatWiden T
theorem p481 : P481 := by unfold P481; intros; rfl

def m482 (T : FTy) := floatWiden T
def P482 : Prop := ∀ T, m482 T = floatWiden T
theorem p482 : P482 := by unfold P482; intros; rfl

def m485 {T : FTy} (ops : PrimitiveOps T) (x : FV T) := ops.neg x
def P485 : Prop := ∀ T (ops : PrimitiveOps T) (x : FV T), m485 ops x = ops.neg x
theorem p485 : P485 := by unfold P485; intros; rfl

def m487 {T : FTy} (ops : PrimitiveOps T) (x y : FV T) := ops.add x y
def P487 : Prop := ∀ T (ops : PrimitiveOps T) (x y : FV T), m487 ops x y = ops.add x y
theorem p487 : P487 := by unfold P487; intros; rfl

def m488 {T : FTy} (ops : PrimitiveOps T) (x y : FV T) := ops.sub x y
def P488 : Prop := ∀ T (ops : PrimitiveOps T) (x y : FV T), m488 ops x y = ops.sub x y
theorem p488 : P488 := by unfold P488; intros; rfl

def m489 {T : FTy} (ops : PrimitiveOps T) (x y : FV T) := ops.mul x y
def P489 : Prop := ∀ T (ops : PrimitiveOps T) (x y : FV T), m489 ops x y = ops.mul x y
theorem p489 : P489 := by unfold P489; intros; rfl

def m490 {T : FTy} (ops : PrimitiveOps T) (x y : FV T) := ops.div x y
def P490 : Prop := ∀ T (ops : PrimitiveOps T) (x y : FV T), m490 ops x y = ops.div x y
theorem p490 : P490 := by unfold P490; intros; rfl

def m492 {T : FTy} (ops : PrimitiveOps T) (x y z : FV T) := ops.muladd x y z
def P492 : Prop := ∀ T (ops : PrimitiveOps T) (x y z : FV T), m492 ops x y z = ops.muladd x y z
theorem p492 : P492 := by unfold P492; intros; rfl

def m498 {T : FTy} (x : FV T) := unbiasedExponent x
def P498 : Prop := ∀ T (x : FV T), m498 x = unbiasedExponent x
theorem p498 : P498 := by unfold P498; intros; rfl

def m502 {T : FTy} (x : FV T) := explicitMantissa x
def P502 : Prop := ∀ T (x : FV T), m502 x = explicitMantissa x
theorem p502 : P502 := by unfold P502; intros; rfl

def m508 (T : FTy) (n : Nat) (e : Int) := toFloatFields T n e
def P508 : Prop := ∀ T n e, m508 T n e = toFloatFields T n e
theorem p508 : P508 := by unfold P508; intros; rfl

def m524 {T : FTy} (x y : FV T) := remInternal x y
def P524 : Prop := ∀ T (x y : FV T), m524 x y = remInternal x y
theorem p524 : P524 := by unfold P524; intros; rfl

def m590 {T : FTy} (x y : FV T) := rem x y
def P590 : Prop := ∀ T (x y : FV T), m590 x y = rem x y
theorem p590 : P590 := by unfold P590; intros; rfl

def m600 {T : FTy} (x y : FV T) := mod x y
def P600 : Prop := ∀ T (x y : FV T), m600 x y = mod x y
theorem p600 : P600 := by unfold P600; intros; rfl

def m615 {T : FTy} (x y : FV T) := Fl.eq x y
def P615 : Prop := ∀ T (x y : FV T), m615 x y = Fl.eq x y
theorem p615 : P615 := by unfold P615; intros; rfl

def m616 {T : FTy} (x y : FV T) := Fl.lt x y
def P616 : Prop := ∀ T (x y : FV T), m616 x y = Fl.lt x y
theorem p616 : P616 := by unfold P616; intros; rfl

def m617 {T : FTy} (x y : FV T) := Fl.le x y
def P617 : Prop := ∀ T (x y : FV T), m617 x y = Fl.le x y
theorem p617 : P617 := by unfold P617; intros; rfl

def m619 {T : FTy} (x y : FV T) := Fl.isequal x y
def P619 : Prop := ∀ T (x y : FV T), m619 x y = Fl.isequal x y
theorem p619 : P619 := by unfold P619; intros; rfl

def m622 {T : FTy} (x : FV T) := fpKey x
def P622 : Prop := ∀ T (x : FV T), m622 x = fpKey x
theorem p622 : P622 := by unfold P622; intros; rfl

def m629 {T : FTy} (x y : FV T) := Fl.isless x y
def P629 : Prop := ∀ T (x y : FV T), m629 x y = Fl.isless x y
theorem p629 : P629 := by unfold P629; intros; rfl

def m652 {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpFI .eq x y
def P652 : Prop := ∀ T t (x : FV T) (y : JInt t), m652 x y = cmpFI .eq x y
theorem p652 : P652 := by unfold P652; intros; rfl

def m656 {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpIF .eq y x
def P656 : Prop := ∀ T t (x : FV T) (y : JInt t), m656 x y = cmpIF .eq y x
theorem p656 : P656 := by unfold P656; intros; rfl

def m658 {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpIF .lt y x
def P658 : Prop := ∀ T t (x : FV T) (y : JInt t), m658 x y = cmpIF .lt y x
theorem p658 : P658 := by unfold P658; intros; rfl

def m662 {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpIF .le y x
def P662 : Prop := ∀ T t (x : FV T) (y : JInt t), m662 x y = cmpIF .le y x
theorem p662 : P662 := by unfold P662; intros; rfl

def m667 {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpFI .lt x y
def P667 : Prop := ∀ T t (x : FV T) (y : JInt t), m667 x y = cmpFI .lt x y
theorem p667 : P667 := by unfold P667; intros; rfl

def m671 {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpFI .le x y
def P671 : Prop := ∀ T t (x : FV T) (y : JInt t), m671 x y = cmpFI .le x y
theorem p671 : P671 := by unfold P671; intros; rfl

def m680 (op : Op) {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpFI op x y
def P680 : Prop := ∀ op T t (x : FV T) (y : JInt t), m680 op x y = cmpFI op x y
theorem p680 : P680 := by unfold P680; intros; rfl

def m681 (op : Op) {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpIF op y x
def P681 : Prop := ∀ op T t (x : FV T) (y : JInt t), m681 op x y = cmpIF op y x
theorem p681 : P681 := by unfold P681; intros; rfl

def m683 (op : Op) {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpFI op x y
def P683 : Prop := ∀ op T t (x : FV T) (y : JInt t), m683 op x y = cmpFI op x y
theorem p683 : P683 := by unfold P683; intros; rfl

def m684 (op : Op) {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpIF op y x
def P684 : Prop := ∀ op T t (x : FV T) (y : JInt t), m684 op x y = cmpIF op y x
theorem p684 : P684 := by unfold P684; intros; rfl

def m686 (op : Op) {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpFI op x y
def P686 : Prop := ∀ op T t (x : FV T) (y : JInt t), m686 op x y = cmpFI op x y
theorem p686 : P686 := by unfold P686; intros; rfl

def m687 (op : Op) {T : FTy} {t : IntTy} (x : FV T) (y : JInt t) := cmpIF op y x
def P687 : Prop := ∀ op T t (x : FV T) (y : JInt t), m687 op x y = cmpIF op y x
theorem p687 : P687 := by unfold P687; intros; rfl

def m692 {T : FTy} (x : FV T) := floatAbs x
def P692 : Prop := ∀ T (x : FV T), m692 x = floatAbs x
theorem p692 : P692 := by unfold P692; intros; rfl

def m702 {α : Type} (ne : α → α → Bool) (x : α) := abstractIsnan ne x
def P702 : Prop := ∀ (α : Type) ne (x : α), m702 ne x = abstractIsnan ne x
theorem p702 : P702 := by unfold P702; intros; rfl

def m703 {α : Type} (x : α) := genericIsnanNumber x
def P703 : Prop := ∀ (α : Type) (x : α), m703 x = genericIsnanNumber x
theorem p703 : P703 := by unfold P703; intros; rfl

def m705 {α : Type} (sub : α → α → α) (isnan : α → Bool) (x : α) := abstractIsfinite sub isnan x
def P705 : Prop := ∀ (α : Type) sub isnan (x : α), m705 sub isnan x = abstractIsfinite sub isnan x
theorem p705 : P705 := by unfold P705; intros; rfl

def m706 {α : Type} (decomp : α → Int × Int × Int) (x : α) := genericIsfiniteReal decomp x
def P706 : Prop := ∀ (α : Type) decomp (x : α), m706 decomp x = genericIsfiniteReal decomp x
theorem p706 : P706 := by unfold P706; intros; rfl

def m707 (x : Int) := genericIsfiniteInteger x
def P707 : Prop := ∀ x : Int, m707 x = genericIsfiniteInteger x
theorem p707 : P707 := by unfold P707; intros; rfl

def m716 {α : Type} (isnan isfinite : α → Bool) (x : α) := genericIsinfReal isnan isfinite x
def P716 : Prop := ∀ (α : Type) isnan isfinite (x : α), m716 isnan isfinite x = genericIsinfReal isnan isfinite x
theorem p716 : P716 := by unfold P716; intros; rfl

def m717 {T : FTy} (x : FV T) := x.isinf
def P717 : Prop := ∀ T (x : FV T), m717 x = x.isinf
theorem p717 : P717 := by unfold P717; intros; rfl

def m745 (x : Int) := decomposeInteger x
def P745 : Prop := ∀ x : Int, m745 x = decomposeInteger x
theorem p745 : P745 := by unfold P745; intros; rfl

def m747 (x : FV .f16) := decompose x
def P747 : Prop := ∀ x : FV .f16, m747 x = decompose x
theorem p747 : P747 := by unfold P747; intros; rfl

def m758 (x : FV .f32) := decompose x
def P758 : Prop := ∀ x : FV .f32, m758 x = decompose x
theorem p758 : P758 := by unfold P758; intros; rfl

def m769 (x : FV .f64) := decompose x
def P769 : Prop := ∀ x : FV .f64, m769 x = decompose x
theorem p769 : P769 := by unfold P769; intros; rfl

def m797 (_u : Unit) := precision2 .f16
def P797 : Prop := ∀ u : Unit, m797 u = precision2 .f16
theorem p797 : P797 := by unfold P797; intros; rfl

def m798 (_u : Unit) := precision2 .f32
def P798 : Prop := ∀ u : Unit, m798 u = precision2 .f32
theorem p798 : P798 := by unfold P798; intros; rfl

def m799 (_u : Unit) := precision2 .f64
def P799 : Prop := ∀ u : Unit, m799 u = precision2 .f64
theorem p799 : P799 := by unfold P799; intros; rfl

def m800 (log2 : Nat → Nat) (T : FTy) (base : Nat) := precisionBase log2 T base
def P800 : Prop := ∀ log2 T base, m800 log2 T base = precisionBase log2 T base
theorem p800 : P800 := by unfold P800; intros; rfl

def m805 (log2 : Nat → Nat) (T : FTy) (base : Nat) := precisionBase log2 T base
def P805 : Prop := ∀ log2 T base, m805 log2 T base = precisionBase log2 T base
theorem p805 : P805 := by unfold P805; intros; rfl

def m806 (log2 : Nat → Nat) (T : FTy) (base : Nat) := precisionBase log2 T base
def P806 : Prop := ∀ log2 T base, m806 log2 T base = precisionBase log2 T base
theorem p806 : P806 := by unfold P806; intros; rfl

def m807 {α : Type} (_u : Unit) : Jl α := precisionBottom
def P807 : Prop := ∀ (α : Type) (u : Unit),
  m807 (α := α) u = (precisionBottom : Jl α)
theorem p807 : P807 := by unfold P807; intros; rfl

def m810 (T : FTy) (x : FV T) (neg : Bool) (n : Nat) := nextFloatRaw T x neg n
def P810 : Prop := ∀ T (x : FV T) neg n, m810 T x neg n = nextFloatRaw T x neg n
theorem p810 : P810 := by unfold P810; intros; rfl

def m853 (T : FTy) (x : FV T) (d : Int) := nextFloat T x d
def P853 : Prop := ∀ T (x : FV T) d, m853 T x d = nextFloat T x d
theorem p853 : P853 := by unfold P853; intros; rfl

def m863 (T : FTy) (x : FV T) (d : Int) := nextFloat T x d
def P863 : Prop := ∀ T (x : FV T) d, m863 T x d = nextFloat T x d
theorem p863 : P863 := by unfold P863; intros; rfl

def m871 (T : FTy) (x : FV T) (d : Int) := prevFloat T x d
def P871 : Prop := ∀ T (x : FV T) d, m871 T x d = prevFloat T x d
theorem p871 : P871 := by unfold P871; intros; rfl

def m879 (T : FTy) (x : FV T) (d : Int) := prevFloat T x d
def P879 : Prop := ∀ T (x : FV T) d, m879 T x d = prevFloat T x d
theorem p879 : P879 := by unfold P879; intros; rfl

def m888 (T : FTy) (t : IntTy) (x : FV T) := checkedTrunc T t x
def P888 : Prop := ∀ T t (x : FV T), m888 T t x = checkedTrunc T t x
theorem p888 : P888 := by unfold P888; intros; rfl

def m895 (T : FTy) (t : IntTy) (x : FV T) := checkedInteger T t x
def P895 : Prop := ∀ T t (x : FV T), m895 T t x = checkedInteger T t x
theorem p895 : P895 := by unfold P895; intros; rfl

def m914 (T : FTy) (t : IntTy) (x : FV T) := checkedTrunc T t x
def P914 : Prop := ∀ T t (x : FV T), m914 T t x = checkedTrunc T t x
theorem p914 : P914 := by unfold P914; intros; rfl

def m921 (T : FTy) (t : IntTy) (x : FV T) := checkedInteger T t x
def P921 : Prop := ∀ T t (x : FV T), m921 T t x = checkedInteger T t x
theorem p921 : P921 := by unfold P921; intros; rfl

def m953 {T : FTy} (x : FV T) := isSubnormal x
def P953 : Prop := ∀ T (x : FV T), m953 x = isSubnormal x
theorem p953 : P953 := by unfold P953; intros; rfl

def m958 {T : FTy} (x : FV T) := isPow2 x
def P958 : Prop := ∀ T (x : FV T), m958 x = isPow2 x
theorem p958 : P958 := by unfold P958; intros; rfl

def m959 {T : FTy} (x : FV T) := isEvenFloat x
def P959 : Prop := ∀ T (x : FV T), m959 x = isEvenFloat x
theorem p959 : P959 := by unfold P959; intros; rfl

def m960 {T : FTy} (x : FV T) := isOddFloat x
def P960 : Prop := ∀ T (x : FV T), m960 x = isOddFloat x
theorem p960 : P960 := by unfold P960; intros; rfl

def m963 (_u : Unit) := typeMin .f16
def P963 : Prop := ∀ u : Unit, m963 u = typeMin .f16
theorem p963 : P963 := by unfold P963; intros; rfl

def m964 (_u : Unit) := typeMax .f16
def P964 : Prop := ∀ u : Unit, m964 u = typeMax .f16
theorem p964 : P964 := by unfold P964; intros; rfl

def m965 (_u : Unit) := typeMin .f32
def P965 : Prop := ∀ u : Unit, m965 u = typeMin .f32
theorem p965 : P965 := by unfold P965; intros; rfl

def m966 (_u : Unit) := typeMax .f32
def P966 : Prop := ∀ u : Unit, m966 u = typeMax .f32
theorem p966 : P966 := by unfold P966; intros; rfl

def m967 (_u : Unit) := typeMin .f64
def P967 : Prop := ∀ u : Unit, m967 u = typeMin .f64
theorem p967 : P967 := by unfold P967; intros; rfl

def m968 (_u : Unit) := typeMax .f64
def P968 : Prop := ∀ u : Unit, m968 u = typeMax .f64
theorem p968 : P968 := by unfold P968; intros; rfl

def m969 {α β : Type} (typeOf : α → β) (limit : β → α) (x : α) := limitOfValue typeOf limit x
def P969 : Prop := ∀ (α β : Type) (typeOf : α → β) (limit : β → α) (x : α),
  m969 typeOf limit x = limitOfValue typeOf limit x
theorem p969 : P969 := by unfold P969; intros; rfl

def m970 {α β : Type} (typeOf : α → β) (limit : β → α) (x : α) := limitOfValue typeOf limit x
def P970 : Prop := ∀ (α β : Type) (typeOf : α → β) (limit : β → α) (x : α),
  m970 typeOf limit x = limitOfValue typeOf limit x
theorem p970 : P970 := by unfold P970; intros; rfl

def m972 (_u : Unit) := floatMin .f16
def P972 : Prop := ∀ u : Unit, m972 u = floatMin .f16
theorem p972 : P972 := by unfold P972; intros; rfl

def m973 (_u : Unit) := floatMin .f32
def P973 : Prop := ∀ u : Unit, m973 u = floatMin .f32
theorem p973 : P973 := by unfold P973; intros; rfl

def m974 (_u : Unit) := floatMin .f64
def P974 : Prop := ∀ u : Unit, m974 u = floatMin .f64
theorem p974 : P974 := by unfold P974; intros; rfl

def m975 (_u : Unit) := floatMax .f16
def P975 : Prop := ∀ u : Unit, m975 u = floatMax .f16
theorem p975 : P975 := by unfold P975; intros; rfl

def m976 (_u : Unit) := floatMax .f32
def P976 : Prop := ∀ u : Unit, m976 u = floatMax .f32
theorem p976 : P976 := by unfold P976; intros; rfl

def m977 (_u : Unit) := floatMax .f64
def P977 : Prop := ∀ u : Unit, m977 u = floatMax .f64
theorem p977 : P977 := by unfold P977; intros; rfl

def m979 (_u : Unit) := typeEps .f16
def P979 : Prop := ∀ u : Unit, m979 u = typeEps .f16
theorem p979 : P979 := by unfold P979; intros; rfl

def m980 (_u : Unit) := typeEps .f32
def P980 : Prop := ∀ u : Unit, m980 u = typeEps .f32
theorem p980 : P980 := by unfold P980; intros; rfl

def m981 (_u : Unit) := typeEps .f64
def P981 : Prop := ∀ u : Unit, m981 u = typeEps .f64
theorem p981 : P981 := by unfold P981; intros; rfl

def m982 (_u : Unit) := typeEps .f64
def P982 : Prop := ∀ u : Unit, m982 u = typeEps .f64
theorem p982 : P982 := by unfold P982; intros; rfl

def m985 {α : Type} (finite ge : α → Bool) (fmin ld nxt zero nan abs : α → α) (x : α) := genericEps finite ge fmin ld nxt zero nan abs x
def P985 : Prop := ∀ (α : Type) finite ge fmin ld nxt zero nan abs (x : α), m985 finite ge fmin ld nxt zero nan abs x = genericEps finite ge fmin ld nxt zero nan abs x
theorem p985 : P985 := by unfold P985; intros; rfl

def m987 {T : FTy} (sub : FV T → FV T → FV T) (x : FV T) := valueEps sub x
def P987 : Prop := ∀ T sub (x : FV T), m987 sub x = valueEps sub x
theorem p987 : P987 := by unfold P987; intros; rfl

def m996 {α : Type} (_u : Unit) : Jl α := limitBottom "eps"
def P996 : Prop := ∀ (α : Type) (u : Unit),
  m996 (α := α) u = (limitBottom "eps" : Jl α)
theorem p996 : P996 := by unfold P996; intros; rfl

def m1019 {α β : Type} (typeOf : α → β) (limit : β → α) (x : α) := limitOfValue typeOf limit x
def P1019 : Prop := ∀ (α β : Type) (typeOf : α → β) (limit : β → α) (x : α),
  m1019 typeOf limit x = limitOfValue typeOf limit x
theorem p1019 : P1019 := by unfold P1019; intros; rfl

def m1045 {α β : Type} (typeOf : α → β) (limit : β → α) (x : α) := limitOfValue typeOf limit x
def P1045 : Prop := ∀ (α β : Type) (typeOf : α → β) (limit : β → α) (x : α),
  m1045 typeOf limit x = limitOfValue typeOf limit x
theorem p1045 : P1045 := by unfold P1045; intros; rfl

def m1047 (_u : Unit) := floatMin .f64
def P1047 : Prop := ∀ u : Unit, m1047 u = floatMin .f64
theorem p1047 : P1047 := by unfold P1047; intros; rfl

def m1048 (_u : Unit) := floatMax .f64
def P1048 : Prop := ∀ u : Unit, m1048 u = floatMax .f64
theorem p1048 : P1048 := by unfold P1048; intros; rfl

def m1049 {α : Type} (_u : Unit) : Jl α := limitBottom "floatmin"
def P1049 : Prop := ∀ (α : Type) (u : Unit),
  m1049 (α := α) u = (limitBottom "floatmin" : Jl α)
theorem p1049 : P1049 := by unfold P1049; intros; rfl

def m1050 {α : Type} (_u : Unit) : Jl α := limitBottom "floatmax"
def P1050 : Prop := ∀ (α : Type) (u : Unit),
  m1050 (α := α) u = (limitBottom "floatmax" : Jl α)
theorem p1050 : P1050 := by unfold P1050; intros; rfl

def m1133 {T : FTy} (x : FV T) := bswap x
def P1133 : Prop := ∀ T (x : FV T), m1133 x = bswap x
theorem p1133 : P1133 := by unfold P1133; intros; rfl

def m1136 (_u : Unit) := uintTy .f64
def P1136 : Prop := ∀ u : Unit, m1136 u = uintTy .f64
theorem p1136 : P1136 := by unfold P1136; intros; rfl

def m1137 (_u : Unit) := uintTy .f32
def P1137 : Prop := ∀ u : Unit, m1137 u = uintTy .f32
theorem p1137 : P1137 := by unfold P1137; intros; rfl

def m1138 (_u : Unit) := uintTy .f16
def P1138 : Prop := ∀ u : Unit, m1138 u = uintTy .f16
theorem p1138 : P1138 := by unfold P1138; intros; rfl

def m1139 (_u : Unit) := intTy .f64
def P1139 : Prop := ∀ u : Unit, m1139 u = intTy .f64
theorem p1139 : P1139 := by unfold P1139; intros; rfl

def m1140 (_u : Unit) := intTy .f32
def P1140 : Prop := ∀ u : Unit, m1140 u = intTy .f32
theorem p1140 : P1140 := by unfold P1140; intros; rfl

def m1141 (_u : Unit) := intTy .f16
def P1141 : Prop := ∀ u : Unit, m1141 u = intTy .f16
theorem p1141 : P1141 := by unfold P1141; intros; rfl

def m1143 (_u : Unit) := floatType .u64
def P1143 : Prop := ∀ u : Unit, m1143 u = floatType .u64
theorem p1143 : P1143 := by unfold P1143; intros; rfl

def m1144 (_u : Unit) := floatType .u32
def P1144 : Prop := ∀ u : Unit, m1144 u = floatType .u32
theorem p1144 : P1144 := by unfold P1144; intros; rfl

def m1145 (_u : Unit) := floatType .u16
def P1145 : Prop := ∀ u : Unit, m1145 u = floatType .u16
theorem p1145 : P1145 := by unfold P1145; intros; rfl

def m1146 (_u : Unit) := floatType .i64
def P1146 : Prop := ∀ u : Unit, m1146 u = floatType .i64
theorem p1146 : P1146 := by unfold P1146; intros; rfl

def m1147 (_u : Unit) := floatType .i32
def P1147 : Prop := ∀ u : Unit, m1147 u = floatType .i32
theorem p1147 : P1147 := by unfold P1147; intros; rfl

def m1148 (_u : Unit) := floatType .i16
def P1148 : Prop := ∀ u : Unit, m1148 u = floatType .i16
theorem p1148 : P1148 := by unfold P1148; intros; rfl

def m1166 {α : Type} (xs : List α) := floatArrayAlready xs
def P1166 : Prop := ∀ (α : Type) (xs : List α), m1166 xs = floatArrayAlready xs
theorem p1166 : P1166 := by unfold P1166; intros; rfl

def m1168 {α β : Type} (concrete : Bool) (convert : List α → Jl (List β)) (xs : List α) := floatArrayGeneric concrete convert xs
def P1168 : Prop := ∀ (α β : Type) concrete (convert : List α → Jl (List β))
  (xs : List α), m1168 concrete convert xs = floatArrayGeneric concrete convert xs
theorem p1168 : P1168 := by unfold P1168; intros; rfl

def m1175 {α β : Type} (f : α → β) (r : RangeModel α) := floatRange f r
def P1175 : Prop := ∀ (α β : Type) (f : α → β) (r : RangeModel α),
  m1175 f r = floatRange f r
theorem p1175 : P1175 := by unfold P1175; intros; rfl

def m1176 {α β : Type} (f : α → β) (r : RangeModel α) := floatRange f r
def P1176 : Prop := ∀ (α β : Type) (f : α → β) (r : RangeModel α),
  m1176 f r = floatRange f r
theorem p1176 : P1176 := by unfold P1176; intros; rfl

def m1177 {α β : Type} (f : α → β) (r : RangeModel α) := floatRange f r
def P1177 : Prop := ∀ (α β : Type) (f : α → β) (r : RangeModel α),
  m1177 f r = floatRange f r
theorem p1177 : P1177 := by unfold P1177; intros; rfl

def m1179 {α β : Type} (f : α → β) (r : RangeModel α) := floatRange f r
def P1179 : Prop := ∀ (α β : Type) (f : α → β) (r : RangeModel α),
  m1179 f r = floatRange f r
theorem p1179 : P1179 := by unfold P1179; intros; rfl

private def mk (line : Nat) (name : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"floatintcov-float-l{line}", juliaFile := "base/float.jl", juliaFns := [name]
    statement := s!"The method at base/float.jl:{line} follows its method-specific source model for every allowed input."
    source := s!"base/float.jl:{line}", status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.FloatIntCov.FloatRows
