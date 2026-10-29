import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.ParsePrint.Ryu
import JuliaLean.ParsePrint.RyuProps
import JuliaLean.ParsePrint.IntParse
import JuliaLean.ParsePrint.IntParseProps
import JuliaLean.ParsePrint.IntParseBoundary
import JuliaLean.ParsePrint.IntPrint
import JuliaLean.ParsePrint.IntPrintProps
import JuliaLean.ParsePrint.IntRoundtrip1
import JuliaLean.ParsePrint.IntRoundtrip2
import JuliaLean.ParsePrint.RoundDigits

/-!
Parsing and printing numbers.

* `IntParse`: `parse`/`tryparse` for every `BitInteger` type from UTF-8 bytes
  (`base/parse.jl`, `base/parsers/ints.jl`), including whitespace, signs, `0x`/`0o`/`0b`
  prefixes, bases 2..62 and the decimal fast paths.
* `IntPrint`: `string(n; base, pad)` with the `bin`/`oct`/`dec`/`hex`/`_base` writers,
  `digits`, `digits!` and `bitstring` (`base/intfuncs.jl`), reusing `ndigits` from
  `IntArith.PowersDigits`.
* `Ryu`: `Ryu.writeshortest` on exact binary64 (`base/ryu/shortest.jl`, `utils.jl`),
  including `compact`, `precision`, `hash`, `padexp` and `typed`.
* `RoundDigits`: `round(x; digits)` for negative digit counts (`base/floatfuncs.jl`).

Differential checks against Julia master, all matching: 41,310 `parse`/`tryparse`
rows (all ten types; bases none, 1, 2, 7, 10, 16, 36, 62, 63; edge, random, prefixed,
whitespace and boundary strings), 10,165 `string`/`digits`/`bitstring` rows (all ten
types; bases -63..63 edge set including invalid ones; pads -2, 0, 1, 5, 40), 7,219
Float64 `string`/compact `show` rows (edge bit patterns and random values), 3,564
`round(x, r; digits=-k)` rows (four rounding modes, k from 1 to 308).
`parse(Float64, s)` is pure Julia on master (`base/parsers/floats.jl`,
Clinger/Eisel-Lemire) but is not modelled here; 1.13.2 calls C `jl_try_substrtod`.
-/

namespace JuliaLean.ParsePrint

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := [
  { id := "parseprint-tryparse-nothing-iff-parse-throws", juliaFile := "base/parse.jl"
    juliaFns := ["parse(::Type{<:Integer}, ::AbstractString; base)", "tryparse(::Type{<:Integer}, ::AbstractString; base)"]
    statement := "For every BitInteger type, byte string and valid base, tryparse returns nothing exactly when parse throws, and otherwise both return the same value."
    source := "base/parse.jl:241-254", status := .proven
    prop := ``IntParse.TryparseNothingIffParseThrows, thm := some ``IntParse.tryparseNothingIffParseThrows
    notes := "Both call tryparse_internal/parseint_utf8 on the whole string; the proof shows the shared core (fast decimal path, preamble, prefix handling and checked loop) always terminates with a value or a failure record, and parse throws exactly on the failure. Same structure in 1.13.2 (parseint_preamble on Chars)." },
  { id := "parseprint-parse-overflow-detected", juliaFile := "base/parsers/ints.jl"
    juliaFns := ["parse(::Type{<:Integer}, ::AbstractString; base)", "Parsers.parseint"]
    statement := "For every BitInteger type and base 10 or 16, parsing the spelling of any integer within 16 of typemin, typemax, ±2^64 or ±2^128 returns that integer if it fits and throws otherwise; no wrapped value is returned."
    source := "base/parsers/ints.jl:150-173 (invariant: parse returns the value of the string or throws OverflowError)", status := .proven
    prop := ``IntParse.ParseOverflowDetected, thm := some ``IntParse.parseOverflowDetected
    notes := "Exhaustive decide +kernel over 10 types x 2 bases x 6 centres x 33 offsets (7,920 strings, up to 39 digits). The centres cover the type bounds and the wrap points of the UInt64/UInt128 accumulator. Random long strings were also differential-checked." },
  { id := "parseprint-ryu-compact-lost-digit", juliaFile := "base/ryu/shortest.jl"
    juliaFns := ["Ryu.reduce_shortest", "Ryu.writeshortest", "show(::IO, ::Float64) with :compact"]
    statement := "Compact display of a finite nonzero Float64 is within half a unit in the sixth significant digit of the value (plus the first rounding to shortest)."
    source := "base/ryu/Ryu.jl:46 (compact: output will be limited to 6 significant digits), base/ryu/Ryu.jl:128-136", status := .refuted
    prop := ``Ryu.CompactSixDigits, thm := some ``Ryu.compactSixDigits_refuted
    issue := "none found; related #33185 (closed, different compact rounding regression). Searched issues: compact show float digits; compact float printing; compact 1e16; Ryu compact; maxsignif; reduce_shortest; PRs: compact float; Ryu shortest; writeshortest"
    notes := "1.7562091489257724e16 shows as 1.7562e16 (error 9.1e10 > 5e10). The a_allzero loop in reduce_shortest removes a zero sixth digit after already dropping the rounding digit. Same in both versions." },
  { id := "parseprint-ryu-compact-tie-even", juliaFile := "base/ryu/shortest.jl"
    juliaFns := ["Ryu.reduce_shortest", "show(::IO, ::Float64) with :compact"]
    statement := "Compact display rounds an exact seven-digit tie k*10^e (last digit 5) to the even six-digit neighbour, as reduce_shortest does for smaller values."
    source := "base/ryu/shortest.jl:131-133,174,209 (ties-to-even invariant)", status := .refuted
    prop := ``Ryu.CompactTiesToEven, thm := some ``Ryu.compactTiesToEven_refuted
    issue := "none found. Searched issues: compact tie even; round half even compact; compact float printing; Ryu compact; PRs: compact float; Ryu shortest; writeshortest"
    notes := "1.234565e17 shows as 1.23457e17; 1234565.0 shows as 1.23456e6. The mod-5 test at shortest.jl:59 mixes UInt32 and UInt64 and is never zero for v >= 2^32. Could be read as an unspecified tie rule (maybe intended)." },
  { id := "parseprint-ryu-precision-pow10-overflow", juliaFile := "base/ryu/shortest.jl"
    juliaFns := ["Ryu.writeshortest"]
    statement := "writeshortest with precision p uses fixed notation for x = 10^k exactly whenever k < p."
    source := "base/ryu/shortest.jl:337-338 (branch invariant), base/ryu/Ryu.jl:41", status := .refuted
    prop := ``Ryu.PrecisionFixedPowersOfTen, thm := some ``Ryu.precisionFixedPowersOfTen_refuted
    issue := "none found. Searched issues: writeshortest precision; Ryu precision; writeshortest 1e19; Ryu precision exponent form; PRs: writeshortest; writeshortest precision"
    notes := "With precision 30, 1e18 is fixed but 1e19 and 1e20 use exponent form: 10^(pt - olength) overflows Int. Only direct writeshortest callers pass such precisions. Same in both versions." },
  { id := "parseprint-round-digits-overflow-zero", juliaFile := "base/floatfuncs.jl"
    juliaFns := ["round(::Real, ::RoundingMode; digits, sigdigits)", "Base._round_step"]
    statement := "round(x; digits=-k) of a finite x >= 10^k is never zero (the nearest multiple of 10^k is at least 10^k)."
    source := "base/rounding.jl:341-345", status := .refuted
    prop := ``RoundDigits.RoundDigitsNonzero, thm := some ``RoundDigits.roundDigitsNonzero_refuted
    issue := "none found; open #63105 rewrites round with digits but keeps this branch. Searched issues: round sigdigits floatmax; round digits overflow zero; round floatmax; _round_step; PRs: round sigdigits; _round_step; round digits overflow"
    notes := "round(floatmax(); digits=-308) and round(floatmax(); sigdigits=1) return 0.0: the overflow branch of _round_step returns zero. The model takes the step as the correctly rounded 10^k; Julia's 10.0^k is not correctly rounded for some k (first k = 33) but is for k = 308. Same in both versions." }
]

end JuliaLean.ParsePrint
