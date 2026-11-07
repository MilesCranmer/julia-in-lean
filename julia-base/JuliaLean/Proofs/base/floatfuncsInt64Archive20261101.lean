import JuliaLean.Bindings.base.floatfuncs
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.floatfuncsInt64Archive20261101

open JuliaLean

/-- For all Int64 operands and Int64 absolute/relative tolerances with norm=abs,
integer isapprox returns the exact equality-or-tolerance formula without an
intermediate conversion error. The integer method ignores the nans keyword.
The mathematical comparison uses unbounded integers solely as observations of
the four fixed-width inputs. No successful-run or nonnegative-tolerance premise
is imposed. The pinned implementation refutes this documented contract when
x=1, y=2, atol=0, rtol=-1, where checked promotion raises InexactError.
Registry ID: floatfuncs-isapprox-int-negative-rtol
Julia source: base/floatfuncs.jl:289-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/floatfuncs.jl:166-181; doc/src/base/math.md:46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def Int64ExactToleranceFormula : Prop :=
  ∀ (x y atol rtol : JInt .i64),
    JuliaLean.base.floatfuncs.isapprox_Integer
      JuliaLean.Bindings.base.floatfuncs.Int64Approx.integerOps x y atol rtol =
      .ok (decide (x.val = y.val ∨
        ((x.val - y.val).natAbs : Int) ≤
          max atol.val (rtol.val * max (x.val.natAbs : Int) (y.val.natAbs : Int))))

end JuliaLean.Proofs.base.floatfuncsInt64Archive20261101

namespace JuliaLean.Proofs.base.floatfuncsInt64Archive20261101
open JuliaLean.Registry
end JuliaLean.Proofs.base.floatfuncsInt64Archive20261101


namespace JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean
open JuliaLean.Proofs.base.floatfuncsInt64Archive20261101

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

/-- Four constructible Int64 values for which the exact contract requires false. -/
theorem floatfuncsInt64NegativeRtolExpected :
    decide ((JInt.lit .i64 (-9223372036854775808)).val = (JInt.lit .i64 0).val ∨
      (((JInt.lit .i64 (-9223372036854775808)).val - (JInt.lit .i64 0).val).natAbs : Int) ≤
        max (JInt.lit .i64 0).val ((JInt.lit .i64 (-1)).val *
          max ((JInt.lit .i64 (-9223372036854775808)).val.natAbs : Int)
            ((JInt.lit .i64 0).val.natAbs : Int))) = false := by
  decide

/-- The pinned implementation does not return the false required by the formula. -/
theorem floatfuncsInt64NegativeRtolMismatch :
    JuliaLean.base.floatfuncs.isapprox_Integer
      JuliaLean.Bindings.base.floatfuncs.Int64Approx.integerOps
      (JInt.lit .i64 (-9223372036854775808)) (JInt.lit .i64 0)
      (JInt.lit .i64 0) (JInt.lit .i64 (-1)) ≠ .ok false := by
  decide

/-- The public formula fails on typemin(Int64), zero, zero, and negative one. -/
theorem FloatfuncsIsapproxIntNegativeRtolV2 :
    ¬ JuliaLean.Proofs.base.floatfuncsInt64Archive20261101.Int64ExactToleranceFormula := by
  intro h
  have he := h (JInt.lit .i64 (-9223372036854775808)) (JInt.lit .i64 0)
    (JInt.lit .i64 0) (JInt.lit .i64 (-1))
  rw [floatfuncsInt64NegativeRtolExpected] at he
  exact floatfuncsInt64NegativeRtolMismatch he

end JuliaLean.ChatGPT.Batch4.Group24

namespace JuliaLean.Proofs.base.floatfuncsInt64Archive20261101

open JuliaLean.Registry
def entries : List Entry := [
  { id := "floatfuncs-isapprox-int-negative-rtol-v2", juliaFile := "base/floatfuncs.jl",
    juliaFns := ["isapprox(::Integer, ::Integer; atol, rtol, norm)"],
    statement := "For every Int64 operand pair and Int64 absolute and relative tolerance, isapprox with norm=abs returns the exact equality-or-tolerance formula without an intermediate conversion error.",
    source := "base/floatfuncs.jl:166-181,289-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .refuted,
    prop := ``JuliaLean.Proofs.base.floatfuncsInt64Archive20261101.Int64ExactToleranceFormula, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.FloatfuncsIsapproxIntNegativeRtolV2 , issue := "bugs/floatfuncs-isapprox-int-negative-rtol.yaml" }
]
end JuliaLean.Proofs.base.floatfuncsInt64Archive20261101
