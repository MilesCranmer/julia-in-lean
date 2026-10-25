import JuliaLean.FloatRanges.TwicePrecision

/-!
`LinRange{Float64,Int}` from `base/range.jl` at Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.FloatRanges

open JuliaLean.Float

/-- `LinRange{Float64,Int}`, `base/range.jl:591-595`. -/
structure Lin where
  start : F64
  stop : F64
  len : I64
  lendiv : I64
  deriving DecidableEq, Repr

namespace Lin

/-- `LinRange(start, stop, len)`: the inner constructor, `base/range.jl:597-610`,
reached through `base/range.jl:612-623`. -/
def mk' (start stop : F64) (len : I64) : Jl Lin :=
  if len.val < 0 then .error (.argumentError "negative length")
  else if len.val = 1 then
    if F64.eq start stop then .ok ⟨start, stop, len, len⟩
    else .error (.argumentError "endpoints differ")
  else .ok ⟨start, stop, len, imax (len - i64 1) (i64 1)⟩

/-- `lerpi(j, d, a, b)`, `base/range.jl:992-996`. -/
def lerpi (j d : I64) (a b : F64) : F64 :=
  let t := F64.div (flt j) (flt d)
  F64.add (F64.mul (F64.sub F64.one t) a) (F64.mul t b)

/-- `unsafe_getindex`, `base/range.jl:990`. -/
def unsafeGet (r : Lin) (i : I64) : F64 := lerpi (i - i64 1) r.lendiv r.start r.stop

/-- `r[i]`: `base/array.jl:3224-3228`, `base/range.jl:952-955`. -/
def get (r : Lin) (i : I64) : Jl F64 :=
  if 1 ≤ i.val ∧ i.val ≤ r.len.val then .ok (unsafeGet r i) else .error .boundsError

/-- `first(r)`, `base/range.jl:870`. -/
def first (r : Lin) : F64 := r.start

/-- `last(r)`, `base/range.jl:879`. -/
def last (r : Lin) : F64 := r.stop

/-- `step(r)`, `base/range.jl:740`. -/
def stepF (r : Lin) : F64 := F64.div (F64.sub r.stop r.start) (flt r.lendiv)

/-- `reverse(r)`, `base/range.jl:1443`. -/
def reverse (r : Lin) : Jl Lin := mk' r.stop r.start r.len

/-- `-r`, `base/range.jl:1315-1318`. -/
def neg (r : Lin) : Jl Lin := mk' (F64.neg r.start) (F64.neg r.stop) r.len

/-- `x in r`, `base/range.jl:1465-1474`. -/
def contains (r : Lin) (x : F64) : Jl Bool := do
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

/-- `r .+ x`, `base/broadcast.jl:1196`. -/
def addScalar (r : Lin) (x : F64) : Jl Lin := mk' (F64.add r.start x) (F64.add r.stop x) r.len

/-- `r .* x`, `base/broadcast.jl:1225`. -/
def bcastMul (r : Lin) (x : F64) : Jl Lin := mk' (F64.mul r.start x) (F64.mul r.stop x) r.len

end Lin

end JuliaLean.FloatRanges
