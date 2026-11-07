import JuliaLean.Core

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

end JuliaLean.Dates
