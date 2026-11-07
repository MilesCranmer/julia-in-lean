import JuliaLean.stdlib.Dates.src.accessors
import JuliaLean.stdlib.Dates.src.query

namespace JuliaLean.Dates
open JuliaLean

/-- The ISO definition: use the Thursday in the date's week, then count weeks
from its year start. This specification uses exact Int arithmetic for the count. -/
def isoWeek (d : I) : Jl Int := do
  let thursday := d + i (4 - (dayofweek d).val)
  let doy ← dayofyear (yearmonthday thursday)
  pure ((doy.val - 1) / 7 + 1)

end JuliaLean.Dates
