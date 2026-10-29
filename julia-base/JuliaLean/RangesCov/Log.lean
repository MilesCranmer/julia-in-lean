import JuliaLean.RangesCov.Floats

/-!
`LogRange` and `logrange` of `base/range.jl` (master `bbfa0ce4150`, lines 1592-1725) for
`Float64`. The elementary functions `Math._log_ext` and `Math.exp_impl` used by the
interior elements are parameters: every property below holds for any choice of them.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

namespace Log

/-- A `LogRange{Float64,TwicePrecision{Float64}}`. -/
structure LogR where
  start : F64
  stop : F64
  len : I64
  extra : TP × TP

/-- `_logrange_extra(a::Float64, b::Float64, len::Int)`, base/range.jl:1696-1702:
`(loga/(len-1), logb/(len-1))` with `loga = _log_twice64_unchecked(a)`. -/
def lograngeExtra (logTwice : F64 → TP) (a b : F64) (len : I64) : TP × TP :=
  let la := logTwice a
  let lb := logTwice b
  (la.divF (FloatRanges.flt (len - FloatRanges.i64 1)), lb.divF (FloatRanges.flt (len - FloatRanges.i64 1)))

/-- `_logrange_extra(a::Real, b::Real, len::Int)`, base/range.jl:1691-1695, with
`log(1.0 * a)` in Float64: `(loga/(len-1), logb/(len-1))`. -/
def lograngeExtraGeneric (log : F64 → F64) (a b : F64) (len : I64) : F64 × F64 :=
  let la := log (Float.F64.mul Float.F64.one a)
  let lb := log (Float.F64.mul Float.F64.one b)
  (Float.F64.div la (FloatRanges.flt (len - FloatRanges.i64 1)),
    Float.F64.div lb (FloatRanges.flt (len - FloatRanges.i64 1)))

/-- `LogRange{T}(start::T, stop::T, len::Int)`, base/range.jl:1650-1674, for `T = Float64`
(not an `Integer`, so the first check passes). -/
def logNew (logTwice : F64 → TP) (a b : F64) (len : I64) : Jl LogR :=
  if Float.F64.iszero a || Float.F64.iszero b then
    .error (.domainError "LogRange cannot start or stop at zero")
  else if Float.F64.lt a FloatRanges.fzero || Float.F64.lt b FloatRanges.fzero then
    .error (.domainError "LogRange does not accept negative numbers")
  else if !Float.F64.isfinite a || !Float.F64.isfinite b then
    .error (.domainError "LogRange is only defined for finite start & stop")
  else if len.val < 0 then .error (.argumentError "can't have negative length")
  else if len.val = 1 ∧ Float.F64.eq a b = false then
    .error (.argumentError "endpoints differ, while length is 1")
  else .ok ⟨a, b, len, lograngeExtra logTwice a b len⟩

/-- `LogRange{T}(start::Real, stop::Real, len::Integer)`, base/range.jl:1677-1679, for
`T = Float64`, `Int` endpoints and an `Int` length. -/
def logTOfInt (logTwice : F64 → TP) (a b len : I64) : Jl LogR :=
  logNew logTwice (FloatRanges.flt a) (FloatRanges.flt b) len

/-- `LogRange(start::Real, stop::Real, len::Integer)`, base/range.jl:1680-1683: `T` is
`float(promote_type(...))`, Float64 for `Int` endpoints. -/
def logAuto (logTwice : F64 → TP) (a b len : I64) : Jl LogR := logTOfInt logTwice a b len

/-- `logrange(start, stop, length) = LogRange(start, stop, Int(length))`,
base/range.jl:1592, and its keyword form, base/range.jl:1593. -/
def logrange (logTwice : F64 → TP) (a b len : I64) : Jl LogR := logAuto logTwice a b len

/-- `size(r::LogRange) = (r.len,)`, base/range.jl:1685. -/
def size (r : LogR) : List I64 := [r.len]

/-- `length(r::LogRange) = r.len`, base/range.jl:1686. -/
def length (r : LogR) : I64 := r.len

/-- `first(r::LogRange) = r.start`, base/range.jl:1688. -/
def first (r : LogR) : F64 := r.start

/-- `last(r::LogRange) = r.stop`, base/range.jl:1689. -/
def last (r : LogR) : F64 := r.stop

/-- `getindex(r::LogRange{T}, i::Int)`, base/range.jl:1704-1714:
`logx = (r.len-i) * r.extra[1] + (i-1) * r.extra[2]`, then `T(_exp_allowing_twice64(logx))`. -/
def getindex (expTwice : TP → F64) (r : LogR) (i : I64) : Jl F64 :=
  if ¬ (1 ≤ i.val ∧ i.val ≤ r.len.val) then .error .boundsError
  else if i.val = 1 then .ok r.start
  else if i = r.len then .ok r.stop
  else
    let logx := FloatRanges.TP.add (Twice.mulInt r.extra.1 (r.len - i)) (Twice.mulInt r.extra.2 (i - FloatRanges.i64 1))
    .ok (expTwice logx)

/-- `_exp_allowing_twice64(x::Number) = exp(x)`, base/twiceprecision.jl:794, and
`_exp_allowing_twice64(x::TwicePrecision{Float64}) = Math.exp_impl(x.hi, x.lo, Val(:ℯ))`,
base/twiceprecision.jl:795. -/
def expAllowingTwice64 (exp : F64 → F64) (x : F64) : F64 := exp x
def expAllowingTwiceTP (expImpl : F64 → F64 → F64) (x : TP) : F64 := expImpl x.hi x.lo

/-- `_log_twice64_unchecked(x::Float64)`, base/twiceprecision.jl:798-806: subnormal `x` is
scaled by `2^52`, its sign bit cleared and its exponent field reduced by 52 (wrapping)
before `Math._log_ext`. -/
def logTwice64Unchecked (logExt : Nat → TP) (x : F64) : TP :=
  let xu := Float.F64.toBits x
  let xu := if xu < 2 ^ 52 then
      let y := Float.F64.toBits (Float.F64.mul x (Float.F64.ofBits 0x4330000000000000))
      let y := Nat.land y (2 ^ 63 - 1)
      (y + 2 ^ 64 - (52 * 2 ^ 52)) % 2 ^ 64
    else xu
  logExt xu

/-- `show(io, r::LogRange{T})`, base/range.jl:1716-1725, as the sequence of printed
strings (`showT` prints `T`, `showF` prints an element). -/
def showLog (showT : String) (showF : F64 → String) (r : LogR) : List String :=
  ["LogRange{", showT, "}(", showF r.start, ", ", showF r.stop, ", ", toString r.len.val, ")"]

/-! ### Properties -/

/-- The first and last elements of a constructed `LogRange` are exactly the given endpoints
(LogRange docstring), for every choice of `log` and `exp`. -/
def LogEndpoints : Prop :=
  ∀ (logTwice : F64 → TP) (expTwice : TP → F64) (a b : F64) (n : I64) (r : LogR),
    logNew logTwice a b n = .ok r →
    (1 ≤ n.val → getindex expTwice r (FloatRanges.i64 1) = .ok a) ∧
    (2 ≤ n.val → getindex expTwice r n = .ok b) ∧
    first r = a ∧ last r = b ∧ length r = n ∧ size r = [n]

theorem logNew_fields {logTwice : F64 → TP} {a b : F64} {n : I64} {r : LogR}
    (h : logNew logTwice a b n = .ok r) : r = ⟨a, b, n, lograngeExtra logTwice a b n⟩ := by
  unfold logNew at h
  repeat' split at h
  all_goals first | (cases h; rfl) | (simp only [reduceCtorEq] at h)

theorem logEndpoints_proven : LogEndpoints := by
  intro logTwice expTwice a b n r h
  rw [logNew_fields h]
  have h1 : (FloatRanges.i64 1).val = 1 := by decide
  refine ⟨fun hn => ?_, fun hn => ?_, rfl, rfl, rfl, rfl⟩
  · simp [getindex, h1, hn]
  · have hn1 : ¬ n.val = 1 := by omega
    simp [getindex, hn1, show 1 ≤ n.val by omega]

/-- A `LogRange` cannot start or stop at a negative number: `logrange` throws DomainError
(LogRange constructor contract). -/
def LogDomain : Prop :=
  ∀ (logTwice : F64 → TP) (a b : F64) (n : I64),
    (Float.F64.iszero a = true ∨ Float.F64.lt a FloatRanges.fzero = true ∨ Float.F64.isfinite a = false) →
    ∃ m, logNew logTwice a b n = .error (.domainError m)

theorem logDomain_proven : LogDomain := by
  intro logTwice a b n h
  unfold logNew
  rcases h with h | h | h
  · simp [h]
  · by_cases hz : Float.F64.iszero a = true
    · simp [hz]
    · by_cases hzb : Float.F64.iszero b = true
      · simp [hzb]
      · simp [hz, hzb, h]
  · by_cases hz : Float.F64.iszero a = true
    · simp [hz]
    · by_cases hzb : Float.F64.iszero b = true
      · simp [hzb]
      · by_cases hl : Float.F64.lt a FloatRanges.fzero = true
        · simp [hz, hzb, hl]
        · by_cases hlb : Float.F64.lt b FloatRanges.fzero = true
          · simp [hz, hzb, hlb]
          · simp [hz, hzb, hl, hlb, h]

/-- `LogRange{Float64}(a, b, n)`, `LogRange(a, b, n)` and `logrange(a, b, n)` with `Int`
arguments have first element `Float64(a)`, last element `Float64(b)` and length `n`. -/
def LogOuterConstructors : Prop :=
  ∀ (logTwice : F64 → TP) (a b n : I64) (r : LogR),
    (logTOfInt logTwice a b n = .ok r ∨ logAuto logTwice a b n = .ok r ∨ logrange logTwice a b n = .ok r) →
    first r = FloatRanges.flt a ∧ last r = FloatRanges.flt b ∧ length r = n

theorem logOuterConstructors_proven : LogOuterConstructors := by
  intro logTwice a b n r h
  have h' : logNew logTwice (FloatRanges.flt a) (FloatRanges.flt b) n = .ok r := by
    rcases h with h | h | h <;> exact h
  rw [logNew_fields h']
  exact ⟨rfl, rfl, rfl⟩

/-- `_logrange_extra` divides both logarithms by `len - 1`: the two components are
`log(a)/(len-1)` and `log(b)/(len-1)` for the Float64 and the generic method alike. -/
def LograngeExtraSymmetric : Prop :=
  (∀ (logTwice : F64 → TP) (a b : F64) (len : I64),
    lograngeExtra logTwice a b len = ((lograngeExtra logTwice b a len).2, (lograngeExtra logTwice b a len).1)) ∧
  (∀ (log : F64 → F64) (a b : F64) (len : I64),
    lograngeExtraGeneric log a b len = ((lograngeExtraGeneric log b a len).2, (lograngeExtraGeneric log b a len).1))

theorem lograngeExtraSymmetric_proven : LograngeExtraSymmetric := ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- `repr(r)` of a `LogRange` begins with the module-qualified type name
`Base.LogRange{`, as `repr(Base.OneTo(3)) == "Base.OneTo(3)"` does, since `LogRange` is
not exported (show/repr contract: output parses back to an equal object). -/
def LogRangeShowQualified : Prop :=
  ∀ (showT : String) (showF : F64 → String) (r : LogR),
    (showLog showT showF r).head? = some "Base.LogRange{"

theorem logRangeShowQualified_refuted : ¬ LogRangeShowQualified := by
  intro h
  have := h "Float64" (fun _ => "1.0") ⟨Float.F64.one, Float.F64.one, FloatRanges.i64 1, default⟩
  simp [showLog] at this

def entries : List Entry := []

end Log

end JuliaLean.RangesCov
