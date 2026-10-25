import JuliaLean.BroadcastViews.Shape

/-!
Broadcasting arithmetic over ranges that returns ranges (`base/broadcast.jl:1174-1242`) and the
range constructors it calls (`base/range.jl`, `base/twiceprecision.jl`), master `bbfa0ce4150`.

Each section models one dispatch path; values are `JInt` integers where Julia computes in a
fixed-width integer type.
-/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-! ## `r1 .+ r2` for two ranges -/

/-- A `UnitRange{Int}` `lo:hi`. -/
structure URange where
  lo : I64
  hi : I64
  deriving DecidableEq, Repr

/-- `length(lo:hi)` (exact for the modelled inputs; `checked_length` throws on overflow). -/
def URange.len (r : URange) : Nat := (r.hi.val - r.lo.val + 1).toNat

/-- The elements of `lo:hi`. -/
def URange.elems (r : URange) : List I64 := (List.range r.len).map (fun k : Nat => r.lo + i64 k)

/-- `+(r1::OrdinalRange, r2::OrdinalRange)`, `base/range.jl:1493-1498`: throws `DimensionMismatch`
unless the lengths are equal, else `StepRangeLen(first(r1)+first(r2), step(r1)+step(r2), r1l)`,
whose elements are `(first(r1)+first(r2)) + k*(1+1)`. Reached from
`broadcasted(::DefaultArrayStyle{1}, ::typeof(+), r1::AbstractRange, r2::AbstractRange) = r1 + r2`
(`base/broadcast.jl:1198`). -/
def bcAddRanges (r1 r2 : URange) : R (List I64) :=
  if r1.len = r2.len then
    .ok ((List.range r1.len).map (fun k : Nat => (r1.lo + r2.lo) + i64 k * (i64 1 + i64 1)))
  else .error .dimensionMismatch

/-- Elementwise broadcast of `+` over two vectors (`collect(r1) .+ collect(r2)`): a length-1
argument is expanded (`base/broadcast.jl:531`, `_bcs1`), unequal non-singleton lengths throw. -/
def bcAddVectors (a b : List I64) : R (List I64) :=
  if a.length = b.length then .ok (List.zipWith (· + ·) a b)
  else if a.length = 1 then .ok (b.map (fun y => a.headD (i64 0) + y))
  else if b.length = 1 then .ok (a.map (fun x => x + b.headD (i64 0)))
  else .error .dimensionMismatch

/-! ## `x .\ r` for a `Float64` range -/

/-- The type of the `ref`/`step` fields of a floating-point `StepRangeLen`. -/
inductive RefT where
  | float
  | twicePrecision
  deriving DecidableEq, Repr

/-- The floating-point element types of a colon range. -/
inductive FloatT where
  | f32
  | f64
  deriving DecidableEq, Repr

/-- `start:step:stop` for `start, step, stop :: T<:IEEEFloat`, `base/twiceprecision.jl:394-434`:
both branches end in `floatrange`/`steprangelen_hp(T, ...)`, which builds
`StepRangeLen(TwicePrecision{Float64}(ref), TwicePrecision{Float64}(step), ...)` for `Float64`
(lines 342-347, 360-365) and `StepRangeLen{T}(Float64 ref, Float64 step, ...)` otherwise
(349-353, 367-371). -/
def colonRefT : FloatT → RefT
  | .f64 => .twicePrecision
  | .f32 => .float

/-- `x \ y` for a `Float64` `x` and a field value `y`: `\(x, y) = adjoint(adjoint(y)/adjoint(x))`
(`base/operators.jl:709`); `adjoint(x::Number) = conj(x)` (`base/number.jl:275`) has no method
for `TwicePrecision`, which is not a `Number`. -/
def ldivField : RefT → R RefT
  | .float => .ok .float
  | .twicePrecision => .error .methodError

/-- `broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::StepRangeLen) =
StepRangeLen(x\r.ref, x\r.step, length(r), r.offset)`, `base/broadcast.jl:1236`; returns the
field type of the result. -/
def bcLdivRange (fieldT : RefT) : R RefT := do
  let ref ← ldivField fieldT
  let _step ← ldivField fieldT
  pure ref

/-! ## Unsigned ranges with a floating-point scalar -/

/-- Julia `UInt64`. -/
abbrev U64 := JInt .u64

/-- Round `n / d` (`d ≠ 0`) to the nearest integer, ties to even (`round` with `RoundNearest`). -/
def roundHalfEven (n d : Int) : Int :=
  let n' := if d < 0 then -n else n
  let d' := if d < 0 then -d else d
  let q := n'.fdiv d'
  let r := n' - q * d'
  if 2 * r < d' then q else if 2 * r > d' then q + 1 else if q % 2 = 0 then q else q + 1

/-- `floatrange(Float64, start_n, step_n, len, den = 1)` for an unsigned `len::UInt64`,
`base/twiceprecision.jl:380-392`: `len + 0` stays `UInt64`; for `len ≥ 2` and `step_n ≠ 0`,
`imin = clamp(round(UInt64, -start_n/step_n+1), 1, len)` (throws `InexactError` when the rounded
value is negative) and `ref_n = start_n + (imin-1)*step_n` is computed in `UInt64` (Int operands
promote to `UInt64`). `steprangelen_hp` converts `ref_n::UInt64` with `TwicePrecision{Float64}`,
whose `splitprec` (lines 22-26) throws `InexactError` when `Float64(ref_n)` rounds up to `2^64`
(`ref_n ≥ 2^64 - 2^10`). Returns the exact value of `ref` and the offset `imin`. Valid for
`|start_n|, |step_n| < 2^50`, where the `Float64` quotient rounds like the exact one. -/
def floatrangeU (startN stepN : Int) (len : U64) : R (Int × U64) :=
  if len.val < 2 ∨ stepN = 0 then .ok (startN, JInt.lit .u64 1)
  else
    let k := roundHalfEven (stepN - startN) stepN
    if k < 0 then .error .inexactError
    else
      let imin : U64 := JInt.wrap .u64 (max 1 (min k len.val))
      let refN : U64 := JInt.wrap .u64 (startN + (imin.val - 1) * stepN)
      if refN.val ≥ 2 ^ 64 - 2 ^ 10 then .error .inexactError
      else .ok (refN.val, imin)

/-- `r[i]` for the `StepRangeLen` built by `floatrangeU` (exact value of the `TwicePrecision`
evaluation): `u = oftype(r.offset, i) - r.offset` is a `UInt64` difference
(`base/range.jl:1096`), then `ref + u*step`. -/
def srlElemU (ref : Int) (offset : U64) (stepN : Int) (i : Nat) : Int :=
  ref + (JInt.wrap .u64 ((i : Int) - offset.val)).val * stepN

/-- `r .- x` for `r = a:s:b::StepRange{UInt64,UInt64}` with `length(r) = n` and an integral
`x::Float64`: `range(first(r) - x, step=step(r), length=length(r))` (`base/broadcast.jl:1200`)
→ `range_start_step_length(a - x, Float64(s), n::UInt64)` (`base/twiceprecision.jl:450-465`,
with `rat` giving `(a - x, 1)` and `(s, 1)`) → `floatrange(Float64, a - x, s, n, 1)`.
Returns the exact value of element `i`. -/
def bcSubFloatElem (a s n : U64) (x : Int) (i : Nat) : R Int := do
  let (ref, off) ← floatrangeU (a.val - x) s.val n
  pure (srlElemU ref off s.val i)

/-! ## `.-r` for an unsigned `UnitRange` -/

/-- Julia `UInt8` and `Int8`. -/
abbrev U8 := JInt .u8
abbrev I8 := JInt .i8

/-- A `StepRange{UInt8,Int8}` after construction: `start`, `step`, normalised `stop`. -/
structure SRange8 where
  start : U8
  step : I8
  stop : U8
  deriving DecidableEq, Repr

/-- `steprange_last(start, step, stop)`, `base/range.jl:353-387` (exact: the differences of `UInt8`
values fit), with `steprange_last_empty` (389-397) for an empty range. -/
def steprangeLast (start : U8) (step : I8) (stop : U8) : R U8 :=
  if step.val = 0 then .error .argumentError
  else if stop.val = start.val then .ok stop
  else if (step.val > 0) ≠ (stop.val > start.val) then
    .ok (if step.val > 0 then JInt.wrap .u8 (start.val - 1) else JInt.wrap .u8 (start.val + 1))
  else
    let absdiff := if stop.val > start.val then stop.val - start.val else start.val - stop.val
    let absstep := if stop.val > start.val then step.val else -step.val
    let remain := absdiff % absstep
    .ok (if stop.val > start.val then JInt.wrap .u8 (stop.val - remain) else JInt.wrap .u8 (stop.val + remain))

/-- `start:step:stop` for `UInt8` endpoints and an `Int8` step (`StepRange` constructor). -/
def mkSRange8 (start : U8) (step : I8) (stop : U8) : R SRange8 := do
  let last ← steprangeLast start step stop
  pure ⟨start, step, last⟩

/-- The elements of a `StepRange{UInt8,Int8}`: `length = div(stop - start, step) + 1` when the
range is nonempty (`base/range.jl`, `length(::OrdinalRange)`), elements `start + k*step` in `UInt8`. -/
def SRange8.elems (r : SRange8) : List U8 :=
  let n := (r.stop.val - r.start.val) / r.step.val + 1
  if (r.step.val > 0 ∧ r.stop.val < r.start.val) ∨ (r.step.val < 0 ∧ r.stop.val > r.start.val) then []
  else (List.range n.toNat).map (fun k : Nat => JInt.wrap .u8 (r.start.val + (k : Int) * r.step.val))

/-- `negate(x::Unsigned) = -convert(Signed, x)`, `base/int.jl:97`, for the `UInt8` step `1`. -/
def negateOne8 : I8 := -(JInt.lit .i8 1)

/-- `.-(lo:hi)` for `lo:hi::UnitRange{UInt8}` (`last = hi` when `hi ≥ lo`, else `lo - 1`):
`broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::OrdinalRange) =
range(-first(r), -last(r), step=negate(step(r)))`, `base/broadcast.jl:1179`, with `-x` on `UInt8`
wrapping; `range(a, b; step)` is `a:step:b`. -/
def bcNegU8 (lo hi : U8) : R (List U8) := do
  let last : U8 := if hi.val ≥ lo.val then hi else JInt.wrap .u8 (lo.val - 1)
  let r ← mkSRange8 (-lo) negateOne8 (-last)
  pure r.elems

/-- The elements of `lo:hi::UnitRange{UInt8}`. -/
def urange8Elems (lo hi : U8) : List U8 :=
  (List.range (hi.val - lo.val + 1).toNat).map (fun k : Nat => JInt.wrap .u8 (lo.val + (k : Int)))

end JuliaLean.BroadcastViews
