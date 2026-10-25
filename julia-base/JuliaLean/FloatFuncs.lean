import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.FloatFuncs.Round
import JuliaLean.FloatFuncs.Isapprox
import JuliaLean.FloatFuncs.Refuted
import JuliaLean.FloatFuncs.Props
import JuliaLean.FloatFuncs.ProofNext
import JuliaLean.FloatFuncs.ProofMisc
import JuliaLean.FloatFuncs.ProofTrunc
import JuliaLean.FloatFuncs.ProofRound
import JuliaLean.FloatFuncs.ProofRoundInt

/-!
`base/floatfuncs.jl`, `base/rounding.jl` and the float methods of `base/div.jl`
(master `bbfa0ce4150`): `round` with every `RoundingMode`, `digits`/`sigdigits`,
rounding to integer and floating-point types, `isapprox`, `nextfloat`/`prevfloat`,
`isinteger`, `maxintfloat`.

* `Round`: `round(x, r)` for the seven modes, `_round_digits`, `hidigit`,
  `round(Float32, x)`.
* `Isapprox`: Float64 and Int64 `isapprox`.
* `Refuted`: failing properties with their counterexamples.
* `Props`: statements proven in `ProofNext`, `ProofMisc`, `ProofTrunc`, `ProofRound`,
  `ProofRoundInt`.
-/

namespace JuliaLean.FloatFuncs

open JuliaLean.Registry

/-- `round(T, x, r)` for integer `T` and every mode other than RoundToZero. -/
theorem roundIntExact_proven : RoundIntExact := roundIntExact_of roundModesExact_proven

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "floatfuncs-nextfloat-iterate", juliaFile := "base/float.jl",
    juliaFns := ["nextfloat(::Float64, ::Integer)", "prevfloat(::Float64, ::Integer)"],
    statement := "nextfloat(x, n) and prevfloat(x, n) equal |n| iterated single steps in the documented direction, for every Float64 x (NaN, infinities, signed zeros) and every integer n, saturating at the infinities.",
    source := "base/float.jl:847-879 (nextfloat/prevfloat docstrings)", status := .proven,
    prop := ``NextfloatIterate, thm := some ``nextfloatIterate_proven },
  { id := "floatfuncs-isapprox-symmetric", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["isapprox(::Float64, ::Float64; atol, rtol, nans)"],
    statement := "isapprox(x, y; atol, rtol, nans) == isapprox(y, x; atol, rtol, nans) for all Float64 x, y, atol, rtol.",
    source := "base/floatfuncs.jl:166-170 (symmetric criterion)", status := .proven,
    prop := ``IsapproxSymmetric, thm := some ``isapproxSymmetric_proven },
  { id := "floatfuncs-isinteger-exact", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["isinteger(::Float64)"],
    statement := "isinteger(x) holds exactly for finite integer-valued Float64 x.",
    source := "base/number.jl isinteger docstring; base/floatfuncs.jl:51", status := .proven,
    prop := ``IsintegerExact, thm := some ``isintegerExact_proven },
  { id := "floatfuncs-maxintfloat-spec", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["maxintfloat(::Type{Float64})"],
    statement := "maxintfloat(Float64) == 2^53, every integer 0..2^53 is a Float64 value, and 2^53+1 is not.",
    source := "base/floatfuncs.jl:23-34 (maxintfloat docstring)", status := .proven,
    prop := ``MaxintfloatSpec, thm := some ``maxintfloatSpec_proven },
  { id := "floatfuncs-trunc-int-exact", juliaFile := "base/float.jl",
    juliaFns := ["trunc(::Type{T}, ::Float64) for the ten BitInteger T", "round(::Type{T}, ::Float64, RoundToZero)"],
    statement := "trunc(T, x) returns the truncation of x when it lies in T's range and throws InexactError otherwise (including NaN and Inf), for every Float64 x and all ten fixed-width integer types.",
    source := "base/rounding.jl:423-424 (trunc docstring)", status := .proven,
    prop := ``TruncIntExact, thm := some ``truncIntExact_proven },
  { id := "floatfuncs-int-convert-exact", juliaFile := "base/float.jl",
    juliaFns := ["(::Type{T})(::Float64) for the ten BitInteger T"],
    statement := "T(x::Float64) returns the integer equal to x and throws InexactError exactly when x is not an integer in T's range.",
    source := "base/float.jl:895-927; convert semantics (base/number.jl)", status := .proven,
    prop := ``IntConvertExact, thm := some ``intConvertExact_proven },
  { id := "floatfuncs-round-modes-exact", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["round(::Float64, ::RoundingMode) for all seven modes"],
    statement := "round(x, r) of a finite Float64 equals the exact integer rounding of x under r, keeps the sign of x, and is finite, for RoundNearest, RoundNearestTiesAway, RoundNearestTiesUp, RoundToZero, RoundFromZero, RoundUp and RoundDown.",
    source := "base/rounding.jl:51-110 (mode docstrings), base/rounding.jl:337", status := .proven,
    prop := ``RoundModesExact, thm := some ``roundModesExact_proven },
  { id := "floatfuncs-round-int-exact", juliaFile := "base/rounding.jl",
    juliaFns := ["round(::Type{T}, ::Float64, ::RoundingMode)", "floor(::Type{T}, ::Float64)", "ceil(::Type{T}, ::Float64)"],
    statement := "round(T, x, r) for the ten fixed-width integer types and every mode other than RoundToZero returns the exact rounding of x and throws InexactError exactly when it is out of T's range (NaN and Inf included).",
    source := "base/rounding.jl:337-339,454-455,471-472", status := .proven,
    prop := ``RoundIntExact, thm := some ``roundIntExact_proven },
  { id := "floatfuncs-round-float-type-double", juliaFile := "base/rounding.jl",
    juliaFns := ["round(::Type{Float32}, ::Float64, ::RoundingMode)", "Base._round_convert"],
    statement := "round(Float32, x::Float64) returns the Float32-representable integer nearest to x.",
    source := "base/rounding.jl:352-354 (round docstring)", status := .refuted,
    prop := ``RoundToF32Nearest, thm := some ``roundToF32Nearest_refuted,
    issue := "none found (queries: round Float32; round Float16; round Float32 double rounding; round to float type nearest; round Float16 RoundNearestTiesAway; _round_convert; PRs: round Float16)",
    notes := "round(Float32, 16777217.3) == 16777216 although 16777218 is closer: round(x) gives 16777217.0, which convert rounds to even. Ties also ignore the mode: round(Float32, 16777217.0, RoundNearestTiesAway) == 16777216. Float16 targets too (round(Float16, 2845.343f0) == 2844). Same in both versions." },
  { id := "floatfuncs-sigdigits-hidigit", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["round(::Float64, ::RoundingMode; sigdigits)", "Base.hidigit"],
    statement := "floor(x; sigdigits=1) is nonzero for every Float64 1 <= x < 1e22.",
    source := "base/rounding.jl:344-345,451-452", status := .refuted,
    prop := ``FloorSigdigitsNonzero, thm := some ``floorSigdigitsNonzero_refuted,
    issue := "none found; related #46596 and #33428 (inexact powers of ten, different cause). Searched issues: sigdigits; hidigit; sigdigits log10; floor sigdigits; floor sigdigits zero; sigdigits power of 10; PRs: hidigit; sigdigits",
    notes := "hidigit(x) = 1 + floor(Int, log10(abs(x))) and log10(prevfloat(1000.0)) == 3.0, so hidigit is 4 and floor(prevfloat(1000.0); sigdigits=1) == 0.0 (also prevfloat(100.0)). round(prevfloat(1000.0); sigdigits=16) == 1000.0. Same in both versions." },
  { id := "floatfuncs-digits-step-underflow", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["round(::Float64, ::RoundingMode; digits)", "Base._round_step"],
    statement := "ceil(x; digits=-k) of a positive finite x is at least 10.0^k (1 <= k <= 22).",
    source := "base/rounding.jl:341-342,468-474", status := .refuted,
    prop := ``CeilDigitsAbove, thm := some ``ceilDigitsAbove_refuted,
    issue := "none found; related #64142 (overflow branch of _round_step) and #63040; open PR #63105 would fix it. Searched issues: ceil digits; round digits subnormal; _round_step; round digits overflow zero; PRs: _round_step; round digits",
    notes := "ceil(5.0e-324; digits=-1) == 0.0: x/10 underflows to 0.0 before RoundUp is applied. Also floor(-5.0e-324; digits=-1) == -0.0 and ceil(1.0e-30; digits=-300) == 0.0. Same in both versions." },
  { id := "floatfuncs-isapprox-int-negative-rtol", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["isapprox(::Int64, ::Int64; atol, rtol)", "Base._scaled_rtol"],
    statement := "isapprox on Int64 arguments with Int64 atol and rtol returns the documented formula, computed exactly, and never throws.",
    source := "base/floatfuncs.jl:166-170 (isapprox docstring)", status := .refuted,
    prop := ``IntIsapproxFormula, thm := some ``intIsapproxFormula_refuted,
    issue := "none found; introduced by #63022 (Exact integer calculation in isapprox). Searched issues: isapprox; isapprox rtol; isapprox InexactError; isapprox integer; PRs: isapprox integer",
    notes := "Master only: isapprox(1, 2; rtol=-1) throws InexactError(:convert, (UInt64, -1)) because _scaled_rtol promotes rtol to UInt64. Julia 1.13.2 returns false." },
  { id := "floatfuncs-sigdigits-idempotent", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["round(::Float64; sigdigits)", "Base._round_digits"],
    statement := "round(round(x; sigdigits=s); sigdigits=s) == round(x; sigdigits=s) for finite x and 1 <= s <= 17.",
    source := "base/rounding.jl:344-345", status := .refuted,
    prop := ``SigdigitsIdempotent, thm := some ``sigdigitsIdempotent_refuted,
    issue := "#46596 (same root cause: 10.0^k is inexact for k > 22). Searched issues: sigdigits; round sigdigits idempotent; Rounding to 3 sigdigits",
    notes := "round(9.526624812270413e-145; sigdigits=1) == 1.0e-144, and round(1.0e-144; sigdigits=1) == 1.0000000000000001e-144: the division by the inexact 10.0^144 moves the result by one ulp. Same in both versions." }
]

end JuliaLean.FloatFuncs
