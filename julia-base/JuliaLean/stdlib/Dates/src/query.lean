import JuliaLean.stdlib.Dates.src.types

namespace JuliaLean.Dates
open JuliaLean

abbrev Bytes := List Nat

/-- stdlib/Dates/src/query.jl:86, using base/operators.jl:914. -/
def dayofweek (d : I) : I := mod1 d 7

/-- stdlib/Dates/src/query.jl:106-107. -/
def dayofyear (c : Civil) : Jl I :=
  let ns : List Int := [0,31,59,90,120,151,181,212,243,273,304,334]
  if c.m.val < 1 ∨ c.m.val > 12 then .error .boundsError
  else .ok (i ns[(c.m.val-1).toNat]! + c.d + i (if c.m.val > 2 && isleapyear c.y then 1 else 0))

/-- ASCII locale names used by the English/default and custom-locale corpus.
stdlib/Dates/src/query.jl:16-27, 55-79. Case lookup tries exact then lowercase. -/
structure Locale where
  months : List Bytes
  abbr : List Bytes
  deriving DecidableEq

def bytes (s : String) : Bytes := s.toList.map Char.toNat
def english : Locale := ⟨
  ["January","February","March","April","May","June","July","August","September","October","November","December"].map bytes,
  ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"].map bytes⟩
def lowerAscii (s : Bytes) : Bytes := s.map (fun c => if 65 ≤ c ∧ c ≤ 90 then c+32 else c)

def monthNameValue (locale : Locale) (full : Bool) (s : Bytes) : Option I :=
  let names := if full then locale.months else locale.abbr
  let k := names.findIdx? (fun n => n = s || lowerAscii n = lowerAscii s)
  k.map (fun k => i (k+1))

end JuliaLean.Dates
