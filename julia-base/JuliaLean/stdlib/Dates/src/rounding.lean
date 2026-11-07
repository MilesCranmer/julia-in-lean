import JuliaLean.stdlib.Dates.src.types
import JuliaLean.stdlib.Dates.src.accessors

namespace JuliaLean.Dates
open JuliaLean

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
