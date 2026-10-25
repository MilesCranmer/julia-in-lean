import JuliaLean.FloatRanges.TwicePrecision

/-!
`StepRangeLen{Float64,TwicePrecision{Float64},TwicePrecision{Float64},Int}` and its
constructors `a:s:b`, `range(a, b; length)`, `range(a; step, length)` and
`range(; stop, step, length)`, from `base/twiceprecision.jl` and `base/range.jl`
at Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.FloatRanges

open JuliaLean.Float

/-- `StepRangeLen{Float64,TwicePrecision{Float64},TwicePrecision{Float64},Int}`,
`base/range.jl:527-531`. -/
structure SRL where
  ref : TP
  step : TP
  len : I64
  offset : I64
  deriving DecidableEq, Repr

namespace SRL

/-- The inner constructor, `base/range.jl:533-543`. -/
def mk' (ref step : TP) (len offset : I64) : Jl SRL :=
  if len.val < 0 then .error (.argumentError "length cannot be negative")
  else if 1 ≤ offset.val ∧ offset.val ≤ max 1 len.val then .ok ⟨ref, step, len, offset⟩
  else .error (.argumentError "StepRangeLen: offset must be in [1,len]")

/-- `length(r)`, `base/range.jl:807`. -/
def length (r : SRL) : I64 := r.len

/-- `unsafe_getindex`, `base/twiceprecision.jl:480-486`. -/
def unsafeGet (r : SRL) (i : I64) : F64 :=
  let u := i - r.offset
  let shift_hi := F64.mul (flt u) r.step.hi
  let shift_lo := F64.mul (flt u) r.step.lo
  let (x_hi, x_lo) := add12 r.ref.hi shift_hi
  F64.add x_hi (F64.add x_lo (F64.add shift_lo r.ref.lo))

/-- `r[i]`: `base/array.jl:3224-3228`, `base/range.jl:952-955`; bounds are
`checkindex(Bool, OneTo(len), i)`, `base/abstractarray.jl:751`. -/
def get (r : SRL) (i : I64) : Jl F64 :=
  if 1 ≤ i.val ∧ i.val ≤ r.len.val then .ok (unsafeGet r i) else .error .boundsError

/-- `first(r)`, `base/range.jl:869`. -/
def first (r : SRL) : F64 := unsafeGet r (i64 1)

/-- `last(r)`, `base/range.jl:878`. -/
def last (r : SRL) : F64 := unsafeGet r r.len

/-- `step(r)`, `base/twiceprecision.jl:438`. -/
def stepF (r : SRL) : F64 := r.step.toF

/-- `reverse(r)`, `base/range.jl:1436-1442`. -/
def reverse (r : SRL) : Jl SRL :=
  mk' r.ref r.step.neg r.len (if r.len.val = 0 then r.offset else r.len - r.offset + i64 1)

/-- `-r`, `base/range.jl:1313-1314`. -/
def neg (r : SRL) : Jl SRL := mk' r.ref.neg r.step.neg r.len r.offset

/-- `x in r`, `base/range.jl:1465-1474`; `round(Integer, x)` is `round(Int, x)`,
`base/float.jl:456`. -/
def contains (r : SRL) (x : F64) : Jl Bool := do
  if r.len.val = 0 then return false
  let f := r.first
  let l := r.last
  if !((F64.le f x && F64.le x l) || (F64.le l x && F64.le x f)) then return false
  if F64.iszero r.stepF then return true
  let n ← F64.roundInt .i64 (F64.div (F64.sub x f) r.stepF)
  let n := n + i64 1
  if !(1 ≤ n.val ∧ n.val ≤ r.len.val) then return false
  let v ← r.get n
  pure (F64.eq v x)

/-- `r .+ x`, `base/broadcast.jl:1192-1193`. -/
def addScalar (r : SRL) (x : F64) : Jl SRL := mk' (r.ref.addF x) r.step r.len r.offset

/-- `r .* x` and `x .* r`, `base/broadcast.jl:1216-1217,1223-1224`. -/
def bcastMul (r : SRL) (x : F64) : Jl SRL := mk' (r.ref.mulF x) (r.step.mulF x) r.len r.offset

/-- `x * r`, `base/twiceprecision.jl:535-536`. -/
def scalarMul (x : F64) (r : SRL) : Jl SRL :=
  mk' (r.ref.mulF x) ((r.step.mulF x).trunc (nbitslen r.len r.offset)) r.len r.offset

end SRL

/-- `steprangelen_hp(Float64, ref::Tuple{Integer,Integer}, step::Tuple{Integer,Integer},
nb, len, offset)`, `base/twiceprecision.jl:342-347`; `TwicePrecision{T}(nd, nb)` is
`twiceprecision(TwicePrecision{T}(nd), nb)`, `base/twiceprecision.jl:227-237`. -/
def hpRatio {t : IntTy} (ref_n ref_d step_n step_d : JInt t) (nb : Int) (len offset : I64) :
    Jl SRL := do
  let ref ← TP.ofRatio ref_n ref_d
  let st ← TP.ofRatio step_n step_d
  SRL.mk' ref (st.trunc nb) len offset

/-- `steprangelen_hp(Float64, ref::F_or_FF, step::F_or_FF, nb, len, offset)`,
`base/twiceprecision.jl:360-365`; a scalar `x` is `TwicePrecision(x, 0.0)` and a pair
`(hi, lo)` is `TwicePrecision(hi, lo)`. -/
def hpFloat (ref step : TP) (nb : Int) (len offset : I64) : Jl SRL :=
  SRL.mk' ref (step.trunc nb) len offset

/-- `floatrange(Float64, start_n, step_n, len, den)`, `base/twiceprecision.jl:380-392`. -/
def floatrange (start_n step_n len den : I64) : Jl SRL := do
  if len.val < 2 ∨ step_n.val = 0 then
    return ← hpRatio start_n den step_n den 0 len (i64 1)
  let q := F64.add (F64.div (flt (-start_n)) (flt step_n)) F64.one
  let r ← F64.roundInt .i64 q
  let imin := iclamp r (i64 1) len
  let ref_n := start_n + (imin - i64 1) * step_n
  hpRatio ref_n den step_n den (nbitslen len imin) len imin

/-- The literal fallback of `(:)`, `base/twiceprecision.jl:422-435`. -/
def colonLiteral (start step stop : F64) : Jl SRL := do
  let lf := F64.div (F64.sub stop start) step
  let len ←
    if F64.lt lf fzero then pure (i64 0)
    else if F64.eq lf fzero then pure (i64 1)
    else do
      let r ← F64.roundInt .i64 lf
      let len := r + i64 1
      let stop' := F64.add start (F64.mul (flt (len - i64 1)) step)
      let over := (if F64.lt start stop && F64.lt stop stop' then 1 else 0) +
        (if F64.lt stop start && F64.lt stop' stop then 1 else 0)
      pure (len - i64 over)
  hpFloat (TP.ofF start) (TP.ofF step) 0 len (i64 1)

/-- The rational branch of `(:)`, `base/twiceprecision.jl:404-419`, entered once
`rat` reproduced all three endpoints; `none` falls through to the literal branch. -/
def colonRational (start step stop : F64) (start_n start_d step_n step_d stop_n stop_d : I64) :
    Jl (Option SRL) := do
  let den ← lcmUnchecked start_d step_d
  if den.val = 0 then return none
  if !F64.le (F64.abs (F64.mul start (flt den))) maxintF then return none
  if !F64.le (F64.abs (F64.mul step (flt den))) maxintF then return none
  let r1 ← JInt.remInt den start_d
  if r1.val ≠ 0 then return none
  let r2 ← JInt.remInt den step_d
  if r2.val ≠ 0 then return none
  let q1 ← JInt.div den start_d
  let start_n := start_n * q1
  let q2 ← JInt.div den step_d
  let step_n := step_n * q2
  let q ← JInt.div (den * stop_n - stop_d * start_n + step_n * stop_d) (step_n * stop_d)
  let len := imax (i64 0) q
  if isbetween start (F64.add start (F64.mul (flt (len - i64 1)) step))
        (F64.add stop (F64.div step (dec 2))) &&
      !isbetween start (F64.add start (F64.mul (flt len) step)) stop then
    return some (← floatrange start_n step_n len den)
  return none

/-- `(:)(start::Float64, step::Float64, stop::Float64)`, `base/twiceprecision.jl:394-436`. -/
def colon (start step stop : F64) : Jl SRL := do
  if F64.eq step fzero then throw (.argumentError "range step cannot be zero")
  let (step_n, step_d) ← rat step
  if step_d.val ≠ 0 && F64.eq (F64.div (flt step_n) (flt step_d)) step then
    let (start_n, start_d) ← rat start
    let (stop_n, stop_d) ← rat stop
    if start_d.val ≠ 0 && stop_d.val ≠ 0 &&
        F64.eq (F64.div (flt start_n) (flt start_d)) start &&
        F64.eq (F64.div (flt stop_n) (flt stop_d)) stop then
      match ← colonRational start step stop start_n start_d step_n step_d stop_n stop_d with
      | some r => return r
      | none => pure ()
  colonLiteral start step stop

/-- `range_start_step_length(a::Float64, st::Float64, len)`,
`base/twiceprecision.jl:450-466`. -/
def rangeStartStepLength (a st : F64) (len : I64) : Jl SRL := do
  let (start_n, start_d) ← rat a
  let (step_n, step_d) ← rat st
  if start_d.val ≠ 0 && step_d.val ≠ 0 &&
      F64.eq (F64.div (flt start_n) (flt start_d)) a &&
      F64.eq (F64.div (flt step_n) (flt step_d)) st then
    let den ← lcmUnchecked start_d step_d
    if F64.le (F64.abs (F64.mul (flt den) a)) maxintF &&
        F64.le (F64.abs (F64.mul (flt den) st)) maxintF then
      let r1 ← JInt.remInt den start_d
      if r1.val = 0 then
        let r2 ← JInt.remInt den step_d
        if r2.val = 0 then
          let q1 ← JInt.div den start_d
          let q2 ← JInt.div den step_d
          return ← floatrange (start_n * q1) (step_n * q2) len den
  hpFloat (TP.ofF a) (TP.ofF st) 0 len (i64 1)

/-- `range_step_stop_length(step::Float64, stop::Float64, len)`,
`base/twiceprecision.jl:474-477`. -/
def rangeStepStopLength (st stop : F64) (len : I64) : Jl SRL := do
  let r ← rangeStartStepLength stop (F64.neg st) len
  r.reverse

/-- `_linspace1(Float64, start, stop, len)`, `base/twiceprecision.jl:737-750`. -/
def linspace1 (start stop : F64) (len : I64) : Jl SRL :=
  if len.val < 0 then .error (.argumentError "negative length")
  else if len.val ≤ 1 then
    if len.val = 1 ∧ !F64.eq start stop then .error (.argumentError "endpoints differ")
    else SRL.mk' ⟨start, fzero⟩ ⟨start, F64.neg stop⟩ len (i64 1)
  else .error (.argumentError "should only be called for len < 2")

/-- `_linspace(Float64, start_n, stop_n, len, den)`, `base/twiceprecision.jl:718-734`,
with the `Int128` (`widen(Int)`) reference numerator and denominator. -/
def linspaceRat (start_n stop_n len den : I64) : Jl SRL := do
  if len.val < 2 then
    return ← linspace1 (F64.div (flt start_n) (flt den)) (F64.div (flt stop_n) (flt den)) len
  if start_n.val = stop_n.val then
    return ← hpRatio start_n den (i64 0) den 0 len (i64 1)
  let tmin := F64.div (flt (-start_n)) (F64.sub (flt stop_n) (flt start_n))
  let r ← F64.roundInt .i64 (F64.add (F64.mul tmin (flt (len - i64 1))) F64.one)
  let imin := iclamp r (i64 1) len
  let w (x : I64) : JInt .i128 := JInt.wrap .i128 x.val
  let start_w := w start_n
  let stop_w := w stop_n
  let ref_num := w (len - imin) * start_w + w (imin - i64 1) * stop_w
  let ref_denom := w (len - i64 1) * w den
  hpRatio ref_num ref_denom (stop_w - start_w) ref_denom (nbitslen len imin) len imin

/-- `_linspace(start::Float64, stop::Float64, len)`, `base/twiceprecision.jl:670-713`. -/
def linspaceFloat (start stop : F64) (len : I64) : Jl SRL := do
  if !(F64.isfinite start && F64.isfinite stop) then
    throw (.argumentError "start and stop must be finite")
  let (Δ, Δfac) :=
    if F64.isfinite (F64.sub stop start) then (F64.sub stop start, i64 1)
    else (F64.sub (F64.div stop (flt len)) (F64.div start (flt len)), len)
  let tmin := F64.div (F64.neg (F64.div start Δ)) (flt Δfac)
  let lenn1 := len - i64 1
  let imin0 ← F64.roundInt .i64 (F64.add (F64.mul tmin (flt lenn1)) F64.one)
  let (imin, ref, step) :=
    if 1 < imin0.val ∧ imin0.val < len.val then
      let t := F64.div (flt (imin0 - i64 1)) (flt lenn1)
      let ref := F64.add (F64.mul (F64.sub F64.one t) start) (F64.mul t stop)
      let step := if (imin0 - i64 1).val < (len - imin0).val
        then F64.div (F64.sub ref start) (flt (imin0 - i64 1))
        else F64.div (F64.sub stop ref) (flt (len - imin0))
      (imin0, ref, step)
    else if imin0.val ≤ 1 then
      (i64 1, start, F64.mul (F64.div Δ (flt lenn1)) (flt Δfac))
    else
      (len, stop, F64.mul (F64.div Δ (flt lenn1)) (flt Δfac))
  if len.val = 2 ∧ !F64.isfinite step then
    return ← hpFloat (TP.ofF start) ⟨F64.neg start, stop⟩ 0 len (i64 1)
  let m := F64.prevfloat F64.floatmax
  let k := flt (imax (imin - i64 1) (len - imin))
  let step_hi_pre := fclamp step
    (fmax (F64.div (F64.neg (F64.add m ref)) k) (F64.div (F64.add (F64.neg m) ref) k))
    (fmin (F64.div (F64.sub m ref) k) (F64.div (F64.add m ref) k))
  let nb := nbitslen len imin
  let step_hi := truncbits step_hi_pre nb
  let (x1_hi, x1_lo) := add12 (F64.mul (flt (i64 1 - imin)) step_hi) ref
  let (x2_hi, x2_lo) := add12 (F64.mul (flt (len - imin)) step_hi) ref
  let a := F64.sub (F64.sub start x1_hi) x1_lo
  let b := F64.sub (F64.sub stop x2_hi) x2_lo
  let step_lo := F64.div (F64.sub b a) (flt (len - i64 1))
  let ref_lo := F64.sub a (F64.mul (flt (i64 1 - imin)) step_lo)
  hpFloat ⟨ref, ref_lo⟩ ⟨step_hi, step_lo⟩ 0 len imin

/-- `range(start, stop; length=len)` for Float64 endpoints:
`range_start_stop_length`, `base/twiceprecision.jl:647-668`. -/
def rangeStartStopLength (start stop : F64) (len : I64) : Jl SRL := do
  if len.val < 2 then return ← linspace1 start stop len
  if F64.eq start stop then return ← hpFloat (TP.ofF start) (TP.ofF fzero) 0 len (i64 1)
  let (_, start_d) ← rat start
  let (_, stop_d) ← rat stop
  if start_d.val ≠ 0 && stop_d.val ≠ 0 then
    let den ← lcmUnchecked start_d stop_d
    if den.val ≠ 0 && F64.le (F64.abs (F64.mul (flt den) start)) maxintF &&
        F64.le (F64.abs (F64.mul (flt den) stop)) maxintF then
      let start_n ← F64.roundInt .i64 (F64.mul (flt den) start)
      let stop_n ← F64.roundInt .i64 (F64.mul (flt den) stop)
      if F64.eq (F64.div (flt start_n) (flt den)) start &&
          F64.eq (F64.div (flt stop_n) (flt den)) stop then
        return ← linspaceRat start_n stop_n len den
  linspaceFloat start stop len

end JuliaLean.FloatRanges
