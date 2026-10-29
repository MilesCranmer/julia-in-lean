import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Promotion.Props
import JuliaLean.Promotion.PromoteType
import JuliaLean.Promotion.Float16
import JuliaLean.Promotion.CompareProofs

/-!
Mixed-type numeric comparison, conversion, promotion and hashing at master `bbfa0ce4150`.

The model was differential-checked against Julia over a corpus of 690 float bit patterns
(Float16/Float32/Float64 boundaries near 2^k for k up to 128, subnormals, signed zeros,
NaNs), 617 integers of all ten types and 706 rationals of all ten component types:
20,671 result rows (every mixed `==`/`<`/`<=`/`isequal`/`isless`/`cmp` between floats and
integers and between floats and rationals, float/integer conversions, `trunc`, `Ti(x)`,
`Float64(::Rational)`, `Rational{T}(::Float64)`, and hash-equality classes) plus 6,170
integer-pair rows. All rows match master; release 1.13.2 differs only in six
`Rational{T}(±2^(bits-1))`/`Rational{T}(2^bits)` rows, where master's `rationalize`
returns `typemax(T)//1` (PR #61297).
-/

namespace JuliaLean.Promotion

open JuliaLean.Registry

/-- Registry entries of this area. -/
def entries : List Entry := []

end JuliaLean.Promotion
