import JuliaLean.Dates.Model

namespace JuliaLean.Dates
open JuliaLean

/-- The Year/Month slice of CompoundPeriod, stdlib/Dates/src/periods.jl:131-164.
Counts of a type have already been merged by wrapping addition; zeros are
represented by zero fields instead of explicit vector entries. -/
structure CalendarPeriod where
  years : I
  months : I
  deriving DecidableEq, Repr

/-- Julia's signed-divisor mod for the ±12 factors in the second pass.
stdlib/Dates/src/periods.jl:299, base/int.jl:331-351. Its result has the
sign of the divisor; the exact quotient by ±12 always fits Int64. -/
def signedMod (v : I) (n : Int) : I :=
  JInt.wrap .i64 (if n < 0 then -((-v.val) % (-n)) else v.val % n)

/-- stdlib/Dates/src/periods.jl:236-316 specialized to Year and Month.
coarserperiod(Month)=(Year,12), coarserperiod(Year)=(Year,1). The first
pass carries a truncating quotient into Year. The second pass adjusts the
Month remainder to the sign of the largest nonzero period. Omitting zero
vector entries does not change either pass's branches or arithmetic. -/
def canonicalCalendar (p : CalendarPeriod) : CalendarPeriod :=
  let m0 := qrem p.months 12
  let carry := qdiv (p.months-m0) 12
  let y := p.years+carry
  let s : Int := if y.val < 0 then -1 else if y.val > 0 then 1
    else if m0.val < 0 then -1 else if m0.val > 0 then 1 else 0
  if s = 0 then ⟨y,m0⟩
  else
    let m := signedMod m0 (12*s)
    ⟨y+qdiv (m0-m) 12,m⟩

/-- Exact calendar duration, independent of Int64 storage limits. -/
def calendarMonths (p : CalendarPeriod) : Int := 12*p.years.val+p.months.val

end JuliaLean.Dates
