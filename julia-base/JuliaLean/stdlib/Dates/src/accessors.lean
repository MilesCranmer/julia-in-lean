import JuliaLean.stdlib.Dates.src.types

namespace JuliaLean.Dates
open JuliaLean

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

end JuliaLean.Dates
