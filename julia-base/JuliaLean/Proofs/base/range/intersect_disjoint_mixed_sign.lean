import JuliaLean.Proofs.base.range

namespace JuliaLean.Proofs.base.range.IntersectDisjointMixedSign

open JuliaLean JuliaLean.base.range
open JuliaLean.base.int (lit)

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Dispatch of the mixed `UInt8:Int8` colon to `(:)(a::Real, b::Real)`
(`base/range.jl:3`); promotion and checked conversions use the installed bindings. -/
local instance : JColon2 (JInt .u8) (JInt .i8) (UnitRange (JInt .u8)) :=
  ⟨colon_Real_Real⟩

/-- A candidate exception-free mathematical intersection contract. The documented
common-element and promoted-result requirements (`base/abstractset.jl:118-130`)
do not explicitly settle whether conversion of discarded input values may throw.
This candidate is retained without a bug registration. -/
def DisjointMixedUnitIntersection : Prop :=
  ∀ (a b : JInt .i8) (c d : JInt .u8),
    a.val ≤ b.val → c.val ≤ d.val → b.val < c.val →
    ∃ result : UnitRange (JInt .u8),
      intersect_AbstractUnitRange_AbstractUnitRange
        (UnitRange.mk a b) (UnitRange.mk c d) = .ok result ∧
      result.stop.val < result.start.val

/-- The witness ranges are produced by the public same-type colon constructors. -/
theorem witness_constructible :
    colon_T_T_Real (lit .i8 (-2)) (lit .i8 (-1)) =
      .ok (UnitRange.mk (lit .i8 (-2)) (lit .i8 (-1))) ∧
    colon_T_T_Real (lit .u8 1) (lit .u8 2) =
      .ok (UnitRange.mk (lit .u8 1) (lit .u8 2)) := by
  decide

/-- `max(first(r),first(s)):min(last(r),last(s))` (`base/range.jl:1209`)
tries to promote `UInt8(1):Int8(-1)` to `UInt8`, so conversion of the
negative stop fails before an empty range can be constructed. -/
theorem witness_failure :
    intersect_AbstractUnitRange_AbstractUnitRange
      (UnitRange.mk (lit .i8 (-2)) (lit .i8 (-1)))
      (UnitRange.mk (lit .u8 1) (lit .u8 2)) =
      (Except.error (.jl (.inexactError "convert")) : JlX (UnitRange (JInt .u8))) := by
  decide

theorem disjointMixedUnitIntersection_refuted : ¬ DisjointMixedUnitIntersection := by
  intro h
  obtain ⟨result, hresult, _⟩ := h (lit .i8 (-2)) (lit .i8 (-1))
    (lit .u8 1) (lit .u8 2) (by decide) (by decide) (by decide)
  rw [witness_failure] at hresult
  cases hresult

end JuliaLean.Proofs.base.range.IntersectDisjointMixedSign
