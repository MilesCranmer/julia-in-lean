import JuliaLean.FloatIntCov.Div

namespace JuliaLean.FloatIntCov.DivRows

open JuliaLean JuliaLean.Registry JuliaLean.Float
open JuliaLean.FloatIntCov.Div
open JuliaLean.IntArith.Division

def m77 {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) := defaultDiv divRound x y
def P77 : Prop := ∀ (α : Type) divRound (x y : α), m77 divRound x y = defaultDiv divRound x y
theorem p77 : P77 := by unfold P77; intros; rfl

def m127 {α : Type} (rem mod : α → α → Jl α) (neg : α → α) (sub mul : α → α → α) (divRound : α → α → Mode → Jl α) (signbit : α → Bool) (x y : α) := genericRemMode rem mod neg sub mul divRound signbit x y .toZero
def P127 : Prop := ∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α), m127 rem mod neg sub mul divRound signbit x y = genericRemMode rem mod neg sub mul divRound signbit x y .toZero
theorem p127 : P127 := by unfold P127; intros; rfl

def m128 {α : Type} (rem mod : α → α → Jl α) (neg : α → α) (sub mul : α → α → α) (divRound : α → α → Mode → Jl α) (signbit : α → Bool) (x y : α) := genericRemMode rem mod neg sub mul divRound signbit x y .down
def P128 : Prop := ∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α), m128 rem mod neg sub mul divRound signbit x y = genericRemMode rem mod neg sub mul divRound signbit x y .down
theorem p128 : P128 := by unfold P128; intros; rfl

def m129 {α : Type} (rem mod : α → α → Jl α) (neg : α → α) (sub mul : α → α → α) (divRound : α → α → Mode → Jl α) (signbit : α → Bool) (x y : α) := genericRemMode rem mod neg sub mul divRound signbit x y .up
def P129 : Prop := ∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α), m129 rem mod neg sub mul divRound signbit x y = genericRemMode rem mod neg sub mul divRound signbit x y .up
theorem p129 : P129 := by unfold P129; intros; rfl

def m130 {α : Type} (rem mod : α → α → Jl α) (neg : α → α) (sub mul : α → α → α) (divRound : α → α → Mode → Jl α) (signbit : α → Bool) (x y : α) := genericRemMode rem mod neg sub mul divRound signbit x y .nearest
def P130 : Prop := ∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α), m130 rem mod neg sub mul divRound signbit x y = genericRemMode rem mod neg sub mul divRound signbit x y .nearest
theorem p130 : P130 := by unfold P130; intros; rfl

def m131 (x y : Value) := remMode x y .nearest
def P131 : Prop := ∀ x y : Value, m131 x y = remMode x y .nearest
theorem p131 : P131 := by unfold P131; intros; rfl

def m132 (x y : Value) := remMode x y .tiesAway
def P132 : Prop := ∀ x y : Value, m132 x y = remMode x y .tiesAway
theorem p132 : P132 := by unfold P132; intros; rfl

def m136 {α : Type} (rem mod : α → α → Jl α) (neg : α → α) (sub mul : α → α → α) (divRound : α → α → Mode → Jl α) (signbit : α → Bool) (x y : α) := genericRemMode rem mod neg sub mul divRound signbit x y .fromZero
def P136 : Prop := ∀ (α : Type) rem mod neg sub mul divRound signbit (x y : α), m136 rem mod neg sub mul divRound signbit x y = genericRemMode rem mod neg sub mul divRound signbit x y .fromZero
theorem p136 : P136 := by unfold P136; intros; rfl

def m139 (x y : F64) (tiesUp : Bool) := floatTieRem x y tiesUp
def P139 : Prop := ∀ x y : F64, ∀ tiesUp : Bool, m139 x y tiesUp = floatTieRem x y tiesUp
theorem p139 : P139 := by unfold P139; intros; rfl

def m196 {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) := divRound x y .down
def P196 : Prop := ∀ (α : Type) divRound (x y : α), m196 divRound x y = divRound x y .down
theorem p196 : P196 := by unfold P196; intros; rfl

def m243 {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) := divRound x y .up
def P243 : Prop := ∀ (α : Type) divRound (x y : α), m243 divRound x y = divRound x y .up
theorem p243 : P243 := by unfold P243; intros; rfl

def m252 {α : Type} (divRound : α → α → Mode → Jl α) (x y : α) := divRound x y .up
def P252 : Prop := ∀ (α : Type) divRound (x y : α), m252 divRound x y = divRound x y .up
theorem p252 : P252 := by unfold P252; intros; rfl

def m273 (x y : Value) := divremMode x y .toZero
def P273 : Prop := ∀ x y : Value, m273 x y = divremMode x y .toZero
theorem p273 : P273 := by unfold P273; intros; rfl

def m276 {α : Type} (div rem fld mod : α → α → Jl α) (divRound remRound : α → α → Mode → Jl α) (x y : α) (mode : Mode) := genericDivrem div rem fld mod divRound remRound x y mode
def P276 : Prop := ∀ (α : Type) div rem fld mod divRound remRound (x y : α) mode, m276 div rem fld mod divRound remRound x y mode = genericDivrem div rem fld mod divRound remRound x y mode
theorem p276 : P276 := by unfold P276; intros; rfl

def m290 (x y : Value) := divremMode x y .toZero
def P290 : Prop := ∀ x y : Value, m290 x y = divremMode x y .toZero
theorem p290 : P290 := by unfold P290; intros; rfl

def m312 (x y : Value) := divremMode x y .down
def P312 : Prop := ∀ x y : Value, m312 x y = divremMode x y .down
theorem p312 : P312 := by unfold P312; intros; rfl

def m326 (x y : Value) := divremMode x y .nearest
def P326 : Prop := ∀ x y : Value, m326 x y = divremMode x y .nearest
theorem p326 : P326 := by unfold P326; intros; rfl

def m342 (x y : Value) := divremMode x y .tiesAway
def P342 : Prop := ∀ x y : Value, m342 x y = divremMode x y .tiesAway
theorem p342 : P342 := by unfold P342; intros; rfl

def m358 (x y : Value) := divremMode x y .tiesUp
def P358 : Prop := ∀ x y : Value, m358 x y = divremMode x y .tiesUp
theorem p358 : P358 := by unfold P358; intros; rfl

def m375 (x y : Value) := divremMode x y .fromZero
def P375 : Prop := ∀ x y : Value, m375 x y = divremMode x y .fromZero
theorem p375 : P375 := by unfold P375; intros; rfl

def m387 (x y : Value) := divremMode x y .down
def P387 : Prop := ∀ x y : Value, m387 x y = divremMode x y .down
theorem p387 : P387 := by unfold P387; intros; rfl

def m391 (x y : Value) := divMode x y .down
def P391 : Prop := ∀ x y : Value, m391 x y = divMode x y .down
theorem p391 : P391 := by unfold P391; intros; rfl

def m395 (x y : Value) := divMode x y .down
def P395 : Prop := ∀ x y : Value, m395 x y = divMode x y .down
theorem p395 : P395 := by unfold P395; intros; rfl

def m400 (x y : Value) := divMode x y .up
def P400 : Prop := ∀ x y : Value, m400 x y = divMode x y .up
theorem p400 : P400 := by unfold P400; intros; rfl

def m404 (x y : Value) := divMode x y .up
def P404 : Prop := ∀ x y : Value, m404 x y = divMode x y .up
theorem p404 : P404 := by unfold P404; intros; rfl

def m409 (x y : Value) := divMode x y .nearest
def P409 : Prop := ∀ x y : Value, m409 x y = divMode x y .nearest
theorem p409 : P409 := by unfold P409; intros; rfl

def m415 (x y : Value) := divMode x y .fromZero
def P415 : Prop := ∀ x y : Value, m415 x y = divMode x y .fromZero
theorem p415 : P415 := by unfold P415; intros; rfl

def m421 (x y : Value) := divMode x y .toZero
def P421 : Prop := ∀ x y : Value, m421 x y = divMode x y .toZero
theorem p421 : P421 := by unfold P421; intros; rfl

def m422 (mode : Mode) (x y : Bool) := boolDiv mode x y
def P422 : Prop := ∀ mode x y, m422 mode x y = boolDiv mode x y
theorem p422 : P422 := by unfold P422; intros; rfl

def m425 (mode : Mode) (x y : Bool) := boolDiv mode x y
def P425 : Prop := ∀ mode x y, m425 mode x y = boolDiv mode x y
theorem p425 : P425 := by unfold P425; intros; rfl

def m427 (mode : Mode) (x y : Bool) := boolDiv mode x y
def P427 : Prop := ∀ mode x y, m427 mode x y = boolDiv mode x y
theorem p427 : P427 := by unfold P427; intros; rfl

def m432 (x y : Value) := divMode x y .down
def P432 : Prop := ∀ x y : Value, m432 x y = divMode x y .down
theorem p432 : P432 := by unfold P432; intros; rfl

def m433 (x y : Value) := divMode x y .up
def P433 : Prop := ∀ x y : Value, m433 x y = divMode x y .up
theorem p433 : P433 := by unfold P433; intros; rfl

def m438 {α : Type} (promote : α → α → α × α) (divRound : α → α → Mode → Jl α) (x y : α) := let p := promote x y; divRound p.1 p.2 .down
def P438 : Prop := ∀ (α : Type) promote divRound (x y : α), m438 promote divRound x y = let p := promote x y; divRound p.1 p.2 .down
theorem p438 : P438 := by unfold P438; intros; rfl

def m439 {α : Type} (promote : α → α → α × α) (divRound : α → α → Mode → Jl α) (x y : α) := let p := promote x y; divRound p.1 p.2 .up
def P439 : Prop := ∀ (α : Type) promote divRound (x y : α), m439 promote divRound x y = let p := promote x y; divRound p.1 p.2 .up
theorem p439 : P439 := by unfold P439; intros; rfl

def m440 (x y : Value) := divMode x y .down
def P440 : Prop := ∀ x y : Value, m440 x y = divMode x y .down
theorem p440 : P440 := by unfold P440; intros; rfl

def m441 (x y : Value) := divMode x y .down
def P441 : Prop := ∀ x y : Value, m441 x y = divMode x y .down
theorem p441 : P441 := by unfold P441; intros; rfl

def m442 (x y : Value) := divMode x y .up
def P442 : Prop := ∀ x y : Value, m442 x y = divMode x y .up
theorem p442 : P442 := by unfold P442; intros; rfl

def m443 (x y : Value) := divMode x y .up
def P443 : Prop := ∀ x y : Value, m443 x y = divMode x y .up
theorem p443 : P443 := by unfold P443; intros; rfl

def m444 {α : Type} (_x _y : α) : Jl α := .error (.methodError "div")
def P444 : Prop := ∀ (α : Type) (x y : α), m444 x y = (Except.error (.methodError "div") : Jl α)
theorem p444 : P444 := by unfold P444; intros; rfl

def m445 {α : Type} (_x _y : α) : Jl α := .error (.methodError "div")
def P445 : Prop := ∀ (α : Type) (x y : α), m445 x y = (Except.error (.methodError "div") : Jl α)
theorem p445 : P445 := by unfold P445; intros; rfl

def m448 {α : Type} (same : Bool) (promote : α → α → α × α) (div divRound : α → α → Mode → Jl α) (x y : α) (mode : Mode) := promotedDiv same promote div divRound x y mode
def P448 : Prop := ∀ (α : Type) same promote div divRound (x y : α) mode, m448 same promote div divRound x y mode = promotedDiv same promote div divRound x y mode
theorem p448 : P448 := by unfold P448; intros; rfl

def m460 (x y : Value) := divMode x y .down
def P460 : Prop := ∀ x y : Value, m460 x y = divMode x y .down
theorem p460 : P460 := by unfold P460; intros; rfl

def m461 (x y : Value) := divMode x y .down
def P461 : Prop := ∀ x y : Value, m461 x y = divMode x y .down
theorem p461 : P461 := by unfold P461; intros; rfl

def m467 (x y : Value) := divMode x y .up
def P467 : Prop := ∀ x y : Value, m467 x y = divMode x y .up
theorem p467 : P467 := by unfold P467; intros; rfl

def m471 (x y : Value) := divMode x y .up
def P471 : Prop := ∀ x y : Value, m471 x y = divMode x y .up
theorem p471 : P471 := by unfold P471; intros; rfl

def m480 (rounder : F64 → Mode → F64) (x y : F64) (mode : Mode) := floatDivMode rounder x y mode
def P480 : Prop := ∀ rounder (x y : F64) mode, m480 rounder x y mode = floatDivMode rounder x y mode
theorem p480 : P480 := by unfold P480; intros; rfl

private def mk (line : Nat) (name : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"floatintcov-div-l{line}", juliaFile := "base/div.jl", juliaFns := [name]
    statement := s!"The method at base/div.jl:{line} follows its method-specific source model for every allowed input."
    source := s!"base/div.jl:{line}", status := .proven, prop, thm := some thm }

def entries : List Entry := [
  mk 77 "div(a, b)" ``P77 ``p77,
  mk 127 "rem(x, y, ::RoundingMode{:ToZero})" ``P127 ``p127,
  mk 128 "rem(x, y, ::RoundingMode{:Down})" ``P128 ``p128,
  mk 129 "rem(x, y, ::RoundingMode{:Up})" ``P129 ``p129,
  mk 130 "rem(x, y, r::RoundingMode{:Nearest})" ``P130 ``p130,
  mk 131 "rem(x::Integer, y::Integer, r::RoundingMode{:Nearest})" ``P131 ``p131,
  mk 132 "rem(x::Integer, y::Integer, rnd::Union{typeof(RoundNearestTiesAway), typeof(RoundNearestTiesUp)})" ``P132 ``p132,
  mk 136 "rem(x, y, ::typeof(RoundFromZero))" ``P136 ``p136,
  mk 139 "rem(x::AbstractFloat, y::AbstractFloat, rnd::Union{typeof(RoundNearestTiesAway), typeof(RoundNearestTiesUp)})" ``P139 ``p139,
  mk 196 "fld(a, b)" ``P196 ``p196,
  mk 243 "cld(a, b)" ``P243 ``p243,
  mk 252 "fld1(a, b)" ``P252 ``p252,
  mk 273 "divrem(x, y)" ``P273 ``p273,
  mk 276 "divrem(a, b, r::RoundingMode)" ``P276 ``p276,
  mk 290 "divrem(a::Integer, b::Integer, r::Union{typeof(RoundUp), typeof(RoundDown), typeof(RoundToZero)})" ``P290 ``p290,
  mk 312 "divrem(a::T, b::T, r::Union{typeof(RoundUp), typeof(RoundDown), typeof(RoundToZero)}) where T<:BitSigned" ``P312 ``p312,
  mk 326 "divrem(x::Integer, y::Integer, rnd::typeof(RoundNearest))" ``P326 ``p326,
  mk 342 "divrem(x::Integer, y::Integer, rnd:: typeof(RoundNearestTiesAway))" ``P342 ``p342,
  mk 358 "divrem(x::Integer, y::Integer, rnd::typeof(RoundNearestTiesUp))" ``P358 ``p358,
  mk 375 "divrem(x, y, ::typeof(RoundFromZero))" ``P375 ``p375,
  mk 387 "fldmod(x, y)" ``P387 ``p387,
  mk 391 "div(x::Signed, y::Unsigned, ::typeof(RoundDown))" ``P391 ``p391,
  mk 395 "div(x::Unsigned, y::Signed, ::typeof(RoundDown))" ``P395 ``p395,
  mk 400 "div(x::Signed, y::Unsigned, ::typeof(RoundUp))" ``P400 ``p400,
  mk 404 "div(x::Unsigned, y::Signed, ::typeof(RoundUp))" ``P404 ``p404,
  mk 409 "div(x::Integer, y::Integer, rnd::Union{typeof(RoundNearest), typeof(RoundNearestTiesAway), typeof(RoundNearestTiesUp)})" ``P409 ``p409,
  mk 415 "div(x::Integer, y::Integer, ::typeof(RoundFromZero))" ``P415 ``p415,
  mk 421 "div(a::T, b::T, ::typeof(RoundToZero)) where {T<:Union{BitSigned, BitUnsigned}}" ``P421 ``p421,
  mk 422 "div(a::Bool, b::Bool, r::RoundingMode)" ``P422 ``p422,
  mk 425 "div(a::Bool, b::Bool, r::$(typeof(rm)))" ``P425 ``p425,
  mk 427 "div(x::Bool, y::Bool, rnd::Union{typeof(RoundNearest), typeof(RoundNearestTiesAway), typeof(RoundNearestTiesUp)})" ``P427 ``p427,
  mk 432 "fld(a::T, b::T) where {T<:Union{Integer,AbstractFloat}}" ``P432 ``p432,
  mk 433 "cld(a::T, b::T) where {T<:Union{Integer,AbstractFloat}}" ``P433 ``p433,
  mk 438 "fld(x::Real, y::Real)" ``P438 ``p438,
  mk 439 "cld(x::Real, y::Real)" ``P439 ``p439,
  mk 440 "fld(x::Signed, y::Unsigned)" ``P440 ``p440,
  mk 441 "fld(x::Unsigned, y::Signed)" ``P441 ``p441,
  mk 442 "cld(x::Signed, y::Unsigned)" ``P442 ``p442,
  mk 443 "cld(x::Unsigned, y::Signed)" ``P443 ``p443,
  mk 444 "fld(x::T, y::T) where {T<:Real}" ``P444 ``p444,
  mk 445 "cld(x::T, y::T) where {T<:Real}" ``P445 ``p445,
  mk 448 "div(x::Real, y::Real, r::RoundingMode)" ``P448 ``p448,
  mk 460 "div(x::T, y::T, ::typeof(RoundDown)) where {T<:Unsigned}" ``P460 ``p460,
  mk 461 "div(x::T, y::T, ::typeof(RoundDown)) where T<:Integer" ``P461 ``p461,
  mk 467 "div(x::T, y::T, ::typeof(RoundUp)) where T<:Unsigned" ``P467 ``p467,
  mk 471 "div(x::T, y::T, ::typeof(RoundUp)) where T<:Integer" ``P471 ``p471,
  mk 480 "div(x::T, y::T, r::RoundingMode) where {T<:AbstractFloat}" ``P480 ``p480
]

end JuliaLean.FloatIntCov.DivRows
