import JuliaLean.Core
import JuliaLean.Float.Extras

/-!
Dates at master bbfa0ce4150. Counts, fields and every integer intermediate are
Int64, represented by the shared JInt type. Division by positive constants is
exact (its quotient fits); all addition, subtraction and multiplication wrap.
A Date is its Rata Die day count, a DateTime its millisecond count, and a Time
its nanosecond count modulo one day. Error messages are not modelled.
-/

namespace JuliaLean.Dates
open JuliaLean
abbrev I := JInt .i64
def i (n : Int) : I := JInt.lit .i64 n

def qdiv (x : I) (n : Int) : I := JInt.wrap .i64 (x.val.tdiv n)
def qfld (x : I) (n : Int) : I := JInt.wrap .i64 (x.val / n)
def qrem (x : I) (n : Int) : I := JInt.wrap .i64 (x.val.tmod n)
def qmod (x : I) (n : Int) : I := JInt.wrap .i64 (x.val % n)
def qabs (x : I) : I := if x.val < 0 then -x else x

/-- base/operators.jl:914: mod1 uses mod(x,y), avoiding a wrapping x-1. -/
def mod1 (x : I) (n : Int) : I :=
  let m := qmod x n
  if m.val = 0 then i n else m

structure Civil where
  y : I
  m : I
  d : I
  deriving DecidableEq, Repr

/-- stdlib/Dates/src/types.jl:337: remainder divisibility works for negative years. -/
def isleapyear (y : I) : Bool :=
  y.val.tmod 4 == 0 && (y.val.tmod 100 != 0 || y.val.tmod 400 == 0)

/-- stdlib/Dates/src/types.jl:340-341; tuple indexing throws BoundsError. -/
def daysinmonth (y m : I) : Jl I :=
  let ns : List Int := [31,28,31,30,31,30,31,31,30,31,30,31]
  if m.val < 1 ∨ m.val > 12 then .error .boundsError
  else .ok (i (ns[(m.val-1).toNat]! + if m.val = 2 && isleapyear y then 1 else 0))

/-- stdlib/Dates/src/types.jl:324-329, preserving left-to-right wrapping operations. -/
def totaldays (c : Civil) : Jl I := do
  let z := if c.m.val < 3 then c.y - i 1 else c.y
  let ns : List Int := [306,337,0,31,61,92,122,153,184,214,245,275]
  if c.m.val < 1 ∨ c.m.val > 12 then throw .boundsError
  let mdays := i ns[(c.m.val-1).toNat]!
  pure (c.d + mdays + i 365 * z + qfld z 4 - qfld z 100 + qfld z 400 - i 306)

/-- stdlib/Dates/src/accessors.jl:5-9, with distinct fld and truncating div. -/
def yearmonthday (days : I) : Civil :=
  let z := days + i 306
  let h := i 100 * z - i 25
  let a := qfld h 3652425
  let b := a - qfld a 4
  let y := qfld (i 100 * b + h) 36525
  let c := b + z - i 365 * y - qfld y 4
  let m := qdiv (i 5 * c + i 456) 153
  let d := c - qdiv (i 153 * m - i 457) 5
  if m.val > 12 then ⟨y + i 1, m - i 12, d⟩ else ⟨y,m,d⟩

/-- stdlib/Dates/src/types.jl:412-415; no year-range check is present. -/
def validDate (c : Civil) : Jl Unit := do
  if ¬ (0 < c.m.val ∧ c.m.val < 13) then throw (.argumentError "month")
  let ld ← daysinmonth c.y c.m
  if ¬ (0 < c.d.val ∧ c.d.val < (ld + i 1).val) then throw (.argumentError "day")
  pure ()

/-- stdlib/Dates/src/types.jl:406-409. -/
def date (c : Civil) : Jl I := do
  validDate c
  totaldays c

inductive AMPM where
  | am | pm | twentyfour
  deriving DecidableEq, Repr

/-- stdlib/Dates/src/types.jl:360-364. -/
def adjusthour (h : I) (a : AMPM) : I :=
  if a = .twentyfour then h
  else if a = .pm ∧ h.val < 12 then h + i 12
  else if a = .am ∧ h.val = 12 then i 0 else h

structure Clock where
  h : I
  mi : I
  s : I
  ms : I
  us : I := i 0
  ns : I := i 0
  ampm : AMPM := .twentyfour
  deriving DecidableEq, Repr

/-- stdlib/Dates/src/types.jl:383-396, including the special 24:00 case. -/
def validDateTime (c : Civil) (t : Clock) : Jl Unit := do
  validDate c
  if t.ampm = .twentyfour then
    if ¬ ((-1 < t.h.val ∧ t.h.val < 24) ∨
        (t.h.val = 24 ∧ t.mi.val = 0 ∧ t.s.val = 0 ∧ t.ms.val = 0)) then
      throw (.argumentError "hour")
  else if ¬ (0 < t.h.val ∧ t.h.val < 13) then throw (.argumentError "hour")
  if ¬ (-1 < t.mi.val ∧ t.mi.val < 60) then throw (.argumentError "minute")
  if ¬ (-1 < t.s.val ∧ t.s.val < 60) then throw (.argumentError "second")
  if ¬ (-1 < t.ms.val ∧ t.ms.val < 1000) then throw (.argumentError "millisecond")
  pure ()

/-- stdlib/Dates/src/types.jl:374-380; overflow in the millisecond count wraps. -/
def datetime (c : Civil) (t : Clock) : Jl I := do
  validDateTime c t
  let h := adjusthour t.h t.ampm
  let days ← totaldays c
  pure (t.ms + i 1000 * (t.s + i 60 * t.mi + i 3600 * h + i 86400 * days))

/-- stdlib/Dates/src/types.jl:437-451. Master admits a full fraction in ns;
1.13.2 checks ns < 1000 instead and has no combined-subsecond check. -/
def validTime (t : Clock) (release : Bool := false) : Jl Unit := do
  if t.ampm = .twentyfour then
    if ¬ (-1 < t.h.val ∧ t.h.val < 24) then throw (.argumentError "hour")
  else if ¬ (0 < t.h.val ∧ t.h.val < 13) then throw (.argumentError "hour")
  if ¬ (-1 < t.mi.val ∧ t.mi.val < 60) then throw (.argumentError "minute")
  if ¬ (-1 < t.s.val ∧ t.s.val < 60) then throw (.argumentError "second")
  if ¬ (-1 < t.ms.val ∧ t.ms.val < 1000) then throw (.argumentError "millisecond")
  if ¬ (-1 < t.us.val ∧ t.us.val < 1000) then throw (.argumentError "microsecond")
  if ¬ (-1 < t.ns.val ∧ t.ns.val < (if release then 1000 else 1000000000)) then
    throw (.argumentError "nanosecond")
  if !release && ¬ ((i 1000000 * t.ms + i 1000 * t.us + t.ns).val < 1000000000) then
    throw (.argumentError "subsecond")
  pure ()

/-- stdlib/Dates/src/types.jl:191: the inner Time constructor. -/
def timeOfNs (n : I) : I := qmod n 86400000000000

/-- stdlib/Dates/src/types.jl:430-434. -/
def time (t : Clock) (release : Bool := false) : Jl I := do
  validTime t release
  let h := adjusthour t.h t.ampm
  pure (timeOfNs (t.ns + i 1000 * t.us + i 1000000 * t.ms + i 1000000000 * t.s +
    i 60000000000 * t.mi + i 3600000000000 * h))

/-- stdlib/Dates/src/query.jl:86, using base/operators.jl:914. -/
def dayofweek (d : I) : I := mod1 d 7

/-- stdlib/Dates/src/query.jl:106-107. -/
def dayofyear (c : Civil) : Jl I :=
  let ns : List Int := [0,31,59,90,120,151,181,212,243,273,304,334]
  if c.m.val < 1 ∨ c.m.val > 12 then .error .boundsError
  else .ok (i ns[(c.m.val-1).toNat]! + c.d + i (if c.m.val > 2 && isleapyear c.y then 1 else 0))

/-- stdlib/Dates/src/accessors.jl:39-43; abs preserves the source's reflection. -/
def week (days : I) : Jl I := do
  let w := qrem (qdiv (qabs (days - i 1)) 7) 20871
  let w := w + i (if w.val ≥ 10435 then 1 else 0)
  let c := qdiv w 5218
  let w := qrem w 5218
  let ns : List Int := [15,23,3,11]
  if c.val < 0 ∨ c.val > 3 then throw .boundsError
  let w := qrem (w * i 28 + i ns[c.val.toNat]!) 1461
  pure (qdiv w 28 + i 1)

/-- The ISO definition: use the Thursday in the date's week, then count weeks
from its year start. This specification uses exact Int arithmetic for the count. -/
def isoWeek (d : I) : Jl Int := do
  let thursday := d + i (4 - (dayofweek d).val)
  let doy ← dayofyear (yearmonthday thursday)
  pure ((doy.val - 1) / 7 + 1)

/-- stdlib/Dates/src/arithmetic.jl:43-47. -/
def monthwrap (m n : I) : I :=
  let v := mod1 (m+n) 12
  if v.val < 0 then i 12 + v else v
/-- stdlib/Dates/src/arithmetic.jl:47. -/
def yearwrap (y m n : I) : I := y + qfld (m+n-i 1) 12

/-- stdlib/Dates/src/arithmetic.jl:56-61; the same clamp is used by Year addition. -/
def monthParts (c : Civil) (n : I) : Jl Civil := do
  let ny := yearwrap c.y c.m n
  let mm := monthwrap c.m n
  let ld ← daysinmonth ny mm
  pure ⟨ny,mm,if c.d ≤ ld then c.d else ld⟩

/-- stdlib/Dates/src/arithmetic.jl:29-31, before the Date constructor. -/
def yearParts (c : Civil) (n : I) : Jl Civil := do
  let ny := c.y+n
  let ld ← daysinmonth ny c.m
  pure ⟨ny,c.m,if c.d ≤ ld then c.d else ld⟩

/-- stdlib/Dates/src/arithmetic.jl:56-61. -/
def addMonth (d n : I) : Jl I := do date (← monthParts (yearmonthday d) n)
/-- stdlib/Dates/src/arithmetic.jl:69-74: negation also wraps at typemin. -/
def subMonth (d n : I) : Jl I := addMonth d (-n)
/-- stdlib/Dates/src/arithmetic.jl:29-31. -/
def addYear (d n : I) : Jl I := do date (← yearParts (yearmonthday d) n)
/-- stdlib/Dates/src/arithmetic.jl:81. -/
def addDay (d n : I) : I := d+n
/-- stdlib/Dates/src/arithmetic.jl:83, toms(Millisecond) at periods.jl:456. -/
def addMillisecond (d n : I) : I := d+n
/-- stdlib/Dates/src/arithmetic.jl:85, tons(Nanosecond) at periods.jl:464. -/
def addNanosecond (t n : I) : I := timeOfNs (t+n)

/-- stdlib/Dates/src/adjusters.jl:54. -/
def firstdayofweek (d : I) : I := d - dayofweek d + i 1

/-- stdlib/Dates/src/adjusters.jl:201-207, for Date and Day steps. Fuel counts
exactly the tested candidates, including start before the first addition. -/
def adjust (f : I → Bool) (step : I) : Nat → I → Jl I
  | 0, _ => .error (.argumentError "limit")
  | n+1, start => if f start then .ok start else adjust f step n (start+step)

/-- stdlib/Dates/src/adjusters.jl:435-437, for Date and Day steps.
DateFunction's type-check call is discarded; the predicate here is pure. -/
def tonext (f : I → Bool) (d step : I) (limit : Nat) (same : Bool) : Jl I :=
  adjust f step limit (if same then d else d+step)
/-- stdlib/Dates/src/adjusters.jl:455-457, for Date and Day steps. -/
def toprev (f : I → Bool) (d step : I) (limit : Nat) (same : Bool) : Jl I :=
  adjust f step limit (if same then d else d+step)

/-- stdlib/Dates/src/rounding.jl:4. -/
def dateEpoch : I := i (-365)
/-- stdlib/Dates/src/rounding.jl:19, 35, 73-76. -/
def floorDay (d p : I) : Jl I :=
  if p.val < 1 then .error (.domainError "precision")
  else
    let days := d-dateEpoch
    .ok (dateEpoch + (days - qmod days p.val))

/-- stdlib/Dates/src/rounding.jl:233-236. -/
def ceilDay (d p : I) : Jl I := do
  let f ← floorDay d p
  pure (if d = f then f else f+p)
/-- stdlib/Dates/src/rounding.jl:273-276, 312-315. -/
def roundDay (d p : I) : Jl I := do
  let f ← floorDay d p
  let c := if d = f then f else f+p
  pure (if d-f < c-d then f else c)

/-- stdlib/Dates/src/rounding.jl:51-58. -/
def floorMonth (d p : I) : Jl I := do
  if p.val < 1 then throw (.domainError "precision")
  let c := yearmonthday d
  let months := c.y * i 12 + c.m - i 1
  let offset := months - qmod months p.val
  let m := qmod offset 12 + i 1
  let y := qdiv offset 12 - i (if offset.val < 0 ∧ m.val ≠ 1 then 1 else 0)
  date ⟨y,m,i 1⟩

/-- stdlib/Dates/src/rounding.jl:45-48. -/
def floorYear (d p : I) : Jl I :=
  if p.val < 1 then .error (.domainError "precision")
  else let y := (yearmonthday d).y; date ⟨y-qmod y p.val,i 1,i 1⟩

end JuliaLean.Dates
