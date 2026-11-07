import JuliaLean.stdlib.Dates.src.types
import JuliaLean.stdlib.Dates.src.query

namespace JuliaLean.Dates
open JuliaLean

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

end JuliaLean.Dates
