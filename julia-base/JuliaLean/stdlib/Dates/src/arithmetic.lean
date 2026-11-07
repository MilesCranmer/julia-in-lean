import JuliaLean.stdlib.Dates.src.types
import JuliaLean.stdlib.Dates.src.accessors

namespace JuliaLean.Dates
open JuliaLean

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

end JuliaLean.Dates
