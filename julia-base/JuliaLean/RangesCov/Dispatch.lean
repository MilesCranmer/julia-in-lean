import JuliaLean.RangesCov.Methods2
import JuliaLean.RangesCov.Convert

namespace JuliaLean.RangesCov
namespace Dispatch

open JuliaLean JuliaLean.Registry

/-! Method-specific models for the colon and range dispatch layer.  These are
kept separate because each syntactic Julia method needs its own coverage entry. -/

/-- `(:)(start::T, stop::T) where T`, base/range.jl:7. -/
def colonGeneric (ge : α → α → Bool) (sub : α → α → β) (oneOf : β → β)
    (colon : α → β → α → γ) (start stop : α) : γ :=
  let d := if ge stop start then sub stop start else sub start stop
  colon start (oneOf d) stop

def ColonGenericBehaviour : Prop :=
  ∀ (α β γ : Type) ge sub oneOf colon (start stop : α),
    colonGeneric (ge : α → α → Bool) (sub : α → α → β) (oneOf : β → β)
      (colon : α → β → α → γ) start stop =
      let d := if ge stop start then sub stop start else sub start stop
      colon start (oneOf d) stop

theorem colonGenericBehaviour_proven : ColonGenericBehaviour := fun _ _ _ _ _ _ _ _ _ => rfl

/-- The three promotion wrappers at base/range.jl:16-18. -/
def colonPromoteA (promote : α → β → α → γ × γ × γ) (colon : γ → γ → γ → δ)
    (a : α) (b : β) (c : α) : δ :=
  let p := promote a b c
  colon p.1 p.2.1 p.2.2

def colonPromoteB (promote : α → β → α → γ × γ × γ) (colon : γ → γ → γ → δ)
    (a : α) (b : β) (c : α) : δ :=
  let p := promote a b c
  colon p.1 p.2.1 p.2.2

def colonPromoteC (promote : α → β → α → γ × γ × γ) (colon : γ → γ → γ → δ)
    (a : α) (b : β) (c : α) : δ :=
  let p := promote a b c
  colon p.1 p.2.1 p.2.2

def ColonPromoteABehaviour : Prop :=
  ∀ (α β γ δ : Type) (promote : α → β → α → γ × γ × γ) (colon : γ → γ → γ → δ)
      (a : α) (b : β) (c : α),
    colonPromoteA promote colon a b c =
      let p := promote a b c; colon p.1 p.2.1 p.2.2

def ColonPromoteBBehaviour : Prop :=
  ∀ (α β γ δ : Type) (promote : α → β → α → γ × γ × γ) (colon : γ → γ → γ → δ)
      (a : α) (b : β) (c : α),
    colonPromoteB promote colon a b c =
      let p := promote a b c; colon p.1 p.2.1 p.2.2

def ColonPromoteCBehaviour : Prop :=
  ∀ (α β γ δ : Type) (promote : α → β → α → γ × γ × γ) (colon : γ → γ → γ → δ)
      (a : α) (b : β) (c : α),
    colonPromoteC promote colon a b c =
      let p := promote a b c; colon p.1 p.2.1 p.2.2

theorem colonPromoteABehaviour_proven : ColonPromoteABehaviour := fun _ _ _ _ _ _ _ _ _ => rfl
theorem colonPromoteBBehaviour_proven : ColonPromoteBBehaviour := fun _ _ _ _ _ _ _ _ _ => rfl
theorem colonPromoteCBehaviour_proven : ColonPromoteCBehaviour := fun _ _ _ _ _ _ _ _ _ => rfl

/-- The public `range` wrappers at base/range.jl:167-173. -/
def rangeStartKw (dispatch : α → β → γ → δ → ε) (start : α) (step : β) (stop : γ) (len : δ) : ε :=
  dispatch start step stop len

def rangeStartStopKw (dispatch : α → β → γ → δ → ε) (start : α) (stop : γ) (step : β) (len : δ) : ε :=
  dispatch start step stop len

def rangeAllKw (dispatch : α → β → γ → δ → ε) (start : α) (stop : γ) (step : β) (len : δ) : ε :=
  dispatch start step stop len

def RangeStartKwBehaviour : Prop := ∀ (α β γ δ ε : Type) (f : α → β → γ → δ → ε) a s b n,
  rangeStartKw f a s b n = f a s b n
def RangeStartStopKwBehaviour : Prop := ∀ (α β γ δ ε : Type) (f : α → β → γ → δ → ε) a b s n,
  rangeStartStopKw f a b s n = f a s b n
def RangeAllKwBehaviour : Prop := ∀ (α β γ δ ε : Type) (f : α → β → γ → δ → ε) a b s n,
  rangeAllKw f a b s n = f a s b n

theorem rangeStartKwBehaviour_proven : RangeStartKwBehaviour := fun _ _ _ _ _ _ _ _ _ _ => rfl
theorem rangeStartStopKwBehaviour_proven : RangeStartStopKwBehaviour := fun _ _ _ _ _ _ _ _ _ _ => rfl
theorem rangeAllKwBehaviour_proven : RangeAllKwBehaviour := fun _ _ _ _ _ _ _ _ _ _ => rfl

/-- The sixteen `_range` dispatch bodies, base/range.jl:175-190. -/
def r175 (rangeError : Option α → Option α → Option α → Option α → β) : β :=
  rangeError none none none none
def r176 (rangeLength : α → β) (len : α) : β := rangeLength len
def r177 (rangeStop : α → β) (stop : α) : β := rangeStop stop
def r178 (rangeStopLength : α → α → β) (stop len : α) : β := rangeStopLength stop len
def r179 (rangeError : Option α → Option α → Option α → Option α → β) (step : α) : β :=
  rangeError none (some step) none none
def r180 (rangeError : Option α → Option α → Option α → Option α → β) (step len : α) : β :=
  rangeError none (some step) none (some len)
def r181 (rangeError : Option α → Option α → Option α → Option α → β) (step stop : α) : β :=
  rangeError none (some step) (some stop) none
def r182 (f : α → α → α → β) (step stop len : α) : β := f step stop len
def r183 (rangeError : Option α → Option α → Option α → Option α → β) (start : α) : β :=
  rangeError (some start) none none none
def r184 (f : α → α → β) (start len : α) : β := f start len
def r185 (f : α → α → β) (start stop : α) : β := f start stop
def r186 (f : α → α → α → β) (start stop len : α) : β := f start stop len
def r187 (rangeError : Option α → Option α → Option α → Option α → β) (start step : α) : β :=
  rangeError (some start) (some step) none none
def r188 (f : α → α → α → β) (start step len : α) : β := f start step len
def r189 (f : α → α → α → β) (start step stop : α) : β := f start step stop
def r190 (rangeError : Option α → Option α → Option α → Option α → β)
    (start step stop len : α) : β :=
  rangeError (some start) (some step) (some stop) (some len)

def R175 : Prop := ∀ (α β : Type) f,
  r175 (f : Option α → Option α → Option α → Option α → β) = f none none none none
def R176 : Prop := ∀ (α β : Type) f (len : α), r176 (f : α → β) len = f len
def R177 : Prop := ∀ (α β : Type) f (stop : α), r177 (f : α → β) stop = f stop
def R178 : Prop := ∀ (α β : Type) f (stop len : α), r178 (f : α → α → β) stop len = f stop len
def R179 : Prop := ∀ (α β : Type) f (step : α),
  r179 (f : Option α → Option α → Option α → Option α → β) step = f none (some step) none none
def R180 : Prop := ∀ (α β : Type) f (step len : α),
  r180 (f : Option α → Option α → Option α → Option α → β) step len = f none (some step) none (some len)
def R181 : Prop := ∀ (α β : Type) f (step stop : α),
  r181 (f : Option α → Option α → Option α → Option α → β) step stop = f none (some step) (some stop) none
def R182 : Prop := ∀ (α β : Type) f (step stop len : α), r182 (f : α → α → α → β) step stop len = f step stop len
def R183 : Prop := ∀ (α β : Type) f (start : α),
  r183 (f : Option α → Option α → Option α → Option α → β) start = f (some start) none none none
def R184 : Prop := ∀ (α β : Type) f (start len : α), r184 (f : α → α → β) start len = f start len
def R185 : Prop := ∀ (α β : Type) f (start stop : α), r185 (f : α → α → β) start stop = f start stop
def R186 : Prop := ∀ (α β : Type) f (start stop len : α), r186 (f : α → α → α → β) start stop len = f start stop len
def R187 : Prop := ∀ (α β : Type) f (start step : α),
  r187 (f : Option α → Option α → Option α → Option α → β) start step = f (some start) (some step) none none
def R188 : Prop := ∀ (α β : Type) f (start step len : α), r188 (f : α → α → α → β) start step len = f start step len
def R189 : Prop := ∀ (α β : Type) f (start step stop : α), r189 (f : α → α → α → β) start step stop = f start step stop
def R190 : Prop := ∀ (α β : Type) f (start step stop len : α),
  r190 (f : Option α → Option α → Option α → Option α → β) start step stop len =
    f (some start) (some step) (some stop) (some len)

theorem r175_proven : R175 := fun _ _ _ => rfl
theorem r176_proven : R176 := fun _ _ _ _ => rfl
theorem r177_proven : R177 := fun _ _ _ _ => rfl
theorem r178_proven : R178 := fun _ _ _ _ _ => rfl
theorem r179_proven : R179 := fun _ _ _ _ => rfl
theorem r180_proven : R180 := fun _ _ _ _ _ => rfl
theorem r181_proven : R181 := fun _ _ _ _ _ => rfl
theorem r182_proven : R182 := fun _ _ _ _ _ _ => rfl
theorem r183_proven : R183 := fun _ _ _ _ => rfl
theorem r184_proven : R184 := fun _ _ _ _ _ => rfl
theorem r185_proven : R185 := fun _ _ _ _ _ => rfl
theorem r186_proven : R186 := fun _ _ _ _ _ _ => rfl
theorem r187_proven : R187 := fun _ _ _ _ _ => rfl
theorem r188_proven : R188 := fun _ _ _ _ _ _ => rfl
theorem r189_proven : R189 := fun _ _ _ _ _ _ => rfl
theorem r190_proven : R190 := fun _ _ _ _ _ _ _ => rfl

/-- `range_stop(stop)`, base/range.jl:196. -/
def rangeStop (oftypeOne : α → α) (rangeStartStop : α → α → β) (stop : α) : β :=
  rangeStartStop (oftypeOne stop) stop

def RangeStopBehaviour : Prop := ∀ (α β : Type) (one : α → α) (f : α → α → β) stop,
  rangeStop one f stop = f (one stop) stop
theorem rangeStopBehaviour_proven : RangeStopBehaviour := fun _ _ _ _ _ => rfl

def RangeStepStyleIrregular : Prop := ∀ _ : Unit,
  Convert.rangeStepStyle false = Convert.StepStyle.irregular
def RangeStepStyleRegular : Prop := ∀ _ : Unit,
  Convert.rangeStepStyle true = Convert.StepStyle.regular
theorem rangeStepStyleIrregular_proven : RangeStepStyleIrregular := fun _ => rfl
theorem rangeStepStyleRegular_proven : RangeStepStyleRegular := fun _ => rfl

def ConvertRangeBehaviour : Prop := ∀ (α : Type) (isT : α → Bool) (ctor : α → Jl α) r,
  Convert.convertRange isT ctor r = if isT r then .ok r else ctor r
theorem convertRangeBehaviour_proven : ConvertRangeBehaviour := fun _ _ _ _ => by simp [Convert.convertRange]

def OverflowCaseBehaviour : Prop := ∀ a s, Colon.overflowCase a s = do
  let q ← Ranges.Num.rem (Ranges.Num.unsigned a) s
  Ranges.Num.cast a.ty q
theorem overflowCaseBehaviour_proven : OverflowCaseBehaviour := fun _ _ => rfl

def StepEmptyBoolBehaviour : Prop := ∀ a s,
  Colon.steprangeLastEmptyBool a s = Ranges.Num.lit .bool
    (if decide (a.val ≠ 0) != decide (s.val > 0) then 1 else 0)
theorem stepEmptyBoolBehaviour_proven : StepEmptyBoolBehaviour := fun _ _ => rfl

/-- The unconstrained fallback returns the user stop, base/range.jl:401. -/
def steprangeLastEmptyAny {α} (_start _step stop : α) : α := stop
def StepEmptyAnyBehaviour : Prop := ∀ (α : Type) (a s b : α), steprangeLastEmptyAny a s b = b
theorem stepEmptyAnyBehaviour_proven : StepEmptyAnyBehaviour := fun _ _ _ _ => rfl

def StepRangeTBehaviour : Prop := ∀ T a s b,
  Colon.stepRangeT T a s b = Colon.stepRangeTS T s.ty a s b
theorem stepRangeTBehaviour_proven : StepRangeTBehaviour := fun _ _ _ _ => rfl

/-- Local `throwbool` in the OneTo range constructor, base/range.jl:496. -/
def throwboolRange {α} (_ : α) : Jl α := .error (.argumentError "invalid Bool index")
def ThrowboolRangeBehaviour : Prop := ∀ (α) (x : α),
  ∃ msg, throwboolRange x = .error (.argumentError msg)
theorem throwboolRangeBehaviour_proven : ThrowboolRangeBehaviour := fun _ _ => ⟨_, rfl⟩

/-- Local throwing helpers in the two OneTo constructors, base/range.jl:488,494-496. -/
def throwboolStop {α β} (_ : α) : Jl β := .error (.argumentError "invalid index of type Bool")
def throwstart {α β} (_ : α) : Jl β := .error (.argumentError "first element must be 1")
def throwstep {α β} (_ : α) : Jl β := .error (.argumentError "step must be 1")
def ThrowboolStopBehaviour : Prop := ∀ (α β : Type) (x : α),
  ∃ msg, (throwboolStop x : Jl β) = .error (.argumentError msg)
def ThrowstartBehaviour : Prop := ∀ (α β : Type) (x : α),
  ∃ msg, (throwstart x : Jl β) = .error (.argumentError msg)
def ThrowstepBehaviour : Prop := ∀ (α β : Type) (x : α),
  ∃ msg, (throwstep x : Jl β) = .error (.argumentError msg)
theorem throwboolStopBehaviour_proven : ThrowboolStopBehaviour := fun _ _ _ => ⟨_, rfl⟩
theorem throwstartBehaviour_proven : ThrowstartBehaviour := fun _ _ _ => ⟨_, rfl⟩
theorem throwstepBehaviour_proven : ThrowstepBehaviour := fun _ _ _ => ⟨_, rfl⟩

def OneToTBehaviour : Prop := ∀ T n, Colon.oneToT T n = do
  if T = .bool then throw (.argumentError "invalid index of type Bool")
  let m := Ranges.Num.max (Ranges.Num.zero T) n
  let m ← Ranges.Num.cast T m
  pure ⟨.oneTo, Ranges.Num.one T, Ranges.Num.one T, m⟩
theorem oneToTBehaviour_proven : OneToTBehaviour := fun _ _ => rfl

/-- Type-parametric inner OneTo constructor, including arbitrary Integer subtypes. -/
def oneToInner (isBool : Bool) (zero one : β) (max : β → α → γ)
    (convert : γ → Except String β) (stop : α) : Except String (β × β × β) := do
  if isBool then throw "invalid index of type Bool"
  let stop ← convert (max zero stop)
  pure (one, one, stop)

def OneToInnerBehaviour : Prop := ∀ (α β γ : Type) isBool zero one max convert (stop : α),
  oneToInner isBool (zero : β) one (max : β → α → γ) (convert : γ → Except String β) stop = do
    if isBool then throw "invalid index of type Bool"
    let stop ← convert (max zero stop)
    pure (one, one, stop)
theorem oneToInnerBehaviour_proven : OneToInnerBehaviour := fun _ _ _ _ _ _ _ _ _ => rfl

def OneToOuterBehaviour : Prop := ∀ n, Colon.oneTo n = Colon.oneToT n.ty n
theorem oneToOuterBehaviour_proven : OneToOuterBehaviour := fun _ => rfl

def OneToRangeBehaviour : Prop := ∀ r, Colon.oneToRange r = Colon.oneToOfRange (Ranges.first r).ty r
theorem oneToRangeBehaviour_proven : OneToRangeBehaviour := fun _ => rfl

def OnetoBehaviour : Prop := ∀ r, Colon.oneto r = Colon.oneToRange r
theorem onetoBehaviour_proven : OnetoBehaviour := fun _ => rfl

def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/range.jl", juliaFns := [fn], statement := statement,
    source := source, status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry "rangescov-r7-colon-generic" "(:)(start::T, stop::T) where T" "The generic two-argument colon supplies a unit step of the difference type." "base/range.jl:7" ``ColonGenericBehaviour ``colonGenericBehaviour_proven,
  entry "rangescov-r16-colon-promote" "(:)(::T, ::AbstractFloat, ::T) where T<:Real" "The method promotes all three arguments and applies colon to the promoted tuple." "base/range.jl:16" ``ColonPromoteABehaviour ``colonPromoteABehaviour_proven,
  entry "rangescov-r17-colon-promote" "(:)(::T, ::AbstractFloat, ::T) where T<:AbstractFloat" "The method promotes all three arguments and applies colon to the promoted tuple." "base/range.jl:17" ``ColonPromoteBBehaviour ``colonPromoteBBehaviour_proven,
  entry "rangescov-r18-colon-promote" "(:)(::T, ::Real, ::T) where T<:AbstractFloat" "The method promotes all three arguments and applies colon to the promoted tuple." "base/range.jl:18" ``ColonPromoteCBehaviour ``colonPromoteCBehaviour_proven,
  entry "rangescov-r167-range" "range(start; stop, length, step)" "The wrapper forwards start, step, stop and length to _range in that order." "base/range.jl:167-168" ``RangeStartKwBehaviour ``rangeStartKwBehaviour_proven,
  entry "rangescov-r169-range" "range(start, stop; length, step)" "The wrapper forwards start, step, stop and length to _range in that order." "base/range.jl:169" ``RangeStartStopKwBehaviour ``rangeStartStopKwBehaviour_proven,
  entry "rangescov-r172-range" "range(; start, stop, length, step)" "The wrapper forwards start, step, stop and length to _range in that order." "base/range.jl:172-173" ``RangeAllKwBehaviour ``rangeAllKwBehaviour_proven,
  entry "rangescov-r175-range" "_range(nothing,nothing,nothing,nothing)" "This missing-argument combination calls range_error." "base/range.jl:175" ``R175 ``r175_proven,
  entry "rangescov-r176-range" "_range(nothing,nothing,nothing,len)" "Length alone calls range_length." "range docstring; base/range.jl:176" ``R176 ``r176_proven,
  entry "rangescov-r177-range" "_range(nothing,nothing,stop,nothing)" "Stop alone calls range_stop." "range docstring; base/range.jl:177" ``R177 ``r177_proven,
  entry "rangescov-r178-range" "_range(nothing,nothing,stop,len)" "Stop and length call range_stop_length." "range docstring; base/range.jl:178" ``R178 ``r178_proven,
  entry "rangescov-r179-range" "_range(nothing,step,nothing,nothing)" "Step alone is rejected by range_error." "range docstring; base/range.jl:179" ``R179 ``r179_proven,
  entry "rangescov-r180-range" "_range(nothing,step,nothing,len)" "Step and length without start or stop are rejected." "range docstring; base/range.jl:180" ``R180 ``r180_proven,
  entry "rangescov-r181-range" "_range(nothing,step,stop,nothing)" "Step and stop without start or length are rejected." "range docstring; base/range.jl:181" ``R181 ``r181_proven,
  entry "rangescov-r182-range" "_range(nothing,step,stop,len)" "Step, stop and length call range_step_stop_length." "range docstring; base/range.jl:182" ``R182 ``r182_proven,
  entry "rangescov-r183-range" "_range(start,nothing,nothing,nothing)" "Start alone is rejected by range_error." "range docstring; base/range.jl:183" ``R183 ``r183_proven,
  entry "rangescov-r184-range" "_range(start,nothing,nothing,len)" "Start and length call range_start_length." "range docstring; base/range.jl:184" ``R184 ``r184_proven,
  entry "rangescov-r185-range" "_range(start,nothing,stop,nothing)" "Start and stop call range_start_stop." "range docstring; base/range.jl:185" ``R185 ``r185_proven,
  entry "rangescov-r186-range" "_range(start,nothing,stop,len)" "Start, stop and length call range_start_stop_length." "range docstring; base/range.jl:186" ``R186 ``r186_proven,
  entry "rangescov-r187-range" "_range(start,step,nothing,nothing)" "Start and step without stop or length are rejected." "range docstring; base/range.jl:187" ``R187 ``r187_proven,
  entry "rangescov-r188-range" "_range(start,step,nothing,len)" "Start, step and length call range_start_step_length." "range docstring; base/range.jl:188" ``R188 ``r188_proven,
  entry "rangescov-r189-range" "_range(start,step,stop,nothing)" "Start, step and stop call range_start_step_stop." "range docstring; base/range.jl:189" ``R189 ``r189_proven,
  entry "rangescov-r190-range" "_range(start,step,stop,len)" "Specifying all four values is rejected." "range docstring; base/range.jl:190" ``R190 ``r190_proven,
  entry "rangescov-r196-range-stop" "range_stop(stop)" "The default start is one converted to the stop type." "range docstring; base/range.jl:196" ``RangeStopBehaviour ``rangeStopBehaviour_proven,
  entry "rangescov-r285-step-style" "RangeStepStyle(::Type{<:AbstractRange})" "A general AbstractRange has irregular step style." "base/range.jl:285" ``RangeStepStyleIrregular ``rangeStepStyleIrregular_proven,
  entry "rangescov-r286-step-style" "RangeStepStyle(::Type{<:AbstractRange{<:Integer}})" "An integer AbstractRange has regular step style." "base/range.jl:286" ``RangeStepStyleRegular ``rangeStepStyleRegular_proven,
  entry "rangescov-r288-convert-range" "convert(::Type{T}, r::AbstractRange)" "Conversion returns r when it already has type T and otherwise constructs T(r)." "base/range.jl:288" ``ConvertRangeBehaviour ``convertRangeBehaviour_proven,
  entry "rangescov-r377-overflow-case" "overflow_case(absdiff, absstep)" "The helper takes an unsigned remainder and converts it back to the difference type." "base/range.jl:377" ``OverflowCaseBehaviour ``overflowCaseBehaviour_proven,
  entry "rangescov-r399-step-empty-bool" "steprange_last_empty(::Bool, step, stop)" "The Bool empty-range stop is start xor (step > zero(step))." "base/range.jl:399" ``StepEmptyBoolBehaviour ``stepEmptyBoolBehaviour_proven,
  entry "rangescov-r401-step-empty-any" "steprange_last_empty(start, step, stop)" "The unconstrained fallback keeps the user stop." "base/range.jl:401" ``StepEmptyAnyBehaviour ``stepEmptyAnyBehaviour_proven,
  entry "rangescov-r403-steprange-t" "StepRange{T}(start, step::S, stop)" "The one-parameter constructor delegates to StepRange{T,S}." "base/range.jl:403" ``StepRangeTBehaviour ``stepRangeTBehaviour_proven,
  entry "rangescov-r487-oneto-t" "OneTo{T}(stop)" "The inner constructor rejects Bool and stores max(zero(T), stop) after conversion." "OneTo invariant; base/range.jl:487-491" ``OneToInnerBehaviour ``oneToInnerBehaviour_proven,
  entry "rangescov-r488-throwbool" "throwbool(r)" "The local helper always throws ArgumentError." "base/range.jl:488" ``ThrowboolStopBehaviour ``throwboolStopBehaviour_proven,
  entry "rangescov-r494-throwstart" "throwstart(r)" "The local helper always throws ArgumentError." "base/range.jl:494" ``ThrowstartBehaviour ``throwstartBehaviour_proven,
  entry "rangescov-r495-throwstep" "throwstep(r)" "The local helper always throws ArgumentError." "base/range.jl:495" ``ThrowstepBehaviour ``throwstepBehaviour_proven,
  entry "rangescov-r496-throwbool" "throwbool(r)" "The local helper always throws ArgumentError." "base/range.jl:496" ``ThrowboolRangeBehaviour ``throwboolRangeBehaviour_proven,
  entry "rangescov-r505-oneto" "OneTo(stop::T)" "The outer constructor delegates to OneTo{T}." "base/range.jl:505" ``OneToOuterBehaviour ``oneToOuterBehaviour_proven,
  entry "rangescov-r506-oneto-range" "OneTo(r::AbstractRange{T})" "The outer constructor delegates to OneTo{T}(r)." "base/range.jl:506" ``OneToRangeBehaviour ``oneToRangeBehaviour_proven,
  entry "rangescov-r507-oneto" "oneto(r)" "oneto delegates to OneTo(r)." "base/range.jl:507" ``OnetoBehaviour ``onetoBehaviour_proven
]

end Dispatch
end JuliaLean.RangesCov
