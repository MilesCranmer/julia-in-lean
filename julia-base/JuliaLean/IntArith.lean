import JuliaLean.IntArith.Division
import JuliaLean.IntArith.Checked
import JuliaLean.IntArith.NumberTheory
import JuliaLean.IntArith.PowersDigits
import JuliaLean.IntArith.Rational

namespace JuliaLean.IntArith

open JuliaLean.Registry

/-!
Source-faithful fixed-width integer and Rational models for master bbfa0ce4150.

Core validation compared every Int8 and UInt8 operand pair for wrapping
arithmetic, div/rem/fld/cld/mod, and every unary negation and 8-bit remainder
conversion. All 1,050,112 rows matched both Julia 1.13.2 and master.
Further master differential checks matched 1,573,888 checked-arithmetic rows,
935,004 mixed-division rows, 25,512 number-theory rows, and 10,367 Rational rows.

General-base nextpow/prevpow take the numerical logarithm seed explicitly.
GMP calls use their documented mathematical result as an external primitive;
the surrounding conversions, error checks, and sign adjustments are modelled.
-/

/-- Settled properties of integer arithmetic and Rational operations. -/
def entries : List Entry :=
  Division.entries ++ Checked.entries ++ NumberTheory.entries ++
  PowersDigits.entries ++ Rational.entries

end JuliaLean.IntArith
