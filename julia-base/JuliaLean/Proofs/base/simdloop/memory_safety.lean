import JuliaLean.base.simdloop
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.simdloop.memory_safety
open JuliaLean

def rangeOps (first last : JInt64) :
    JuliaLean.base.simdloop.SimdRangeOps Unit JInt64 JInt64 JlError where
  length := fun _ => pure (last - first + JInt.wrap .i64 1)
  firstindex := fun _ => pure first
  add := fun i j => pure (i + j)
  getindex := fun _ index =>
    if first.val ≤ index.val ∧ index.val ≤ last.val then pure index else .error .boundsError

def SimdIndexInBounds : Prop :=
  ∀ (first last offset outer : JInt64),
    0 ≤ offset.val → offset.val < last.val - first.val + 1 →
    JuliaLean.base.simdloop.simd_index (rangeOps first last) () outer offset =
      .ok (JInt.wrap .i64 (offset.val + first.val))

theorem simdIndexInBounds : SimdIndexInBounds := by
  intro first last offset outer hnonneg hlast
  have hindex : first.val ≤ offset.val + first.val ∧
      offset.val + first.val ≤ last.val := by omega
  have hfirst := first.property
  have hlastRange := last.property
  have hwrap : (JInt.wrap .i64 (offset.val + first.val)).val = offset.val + first.val := by
    change wrapInt .i64 (offset.val + first.val) = _
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    change -9223372036854775808 ≤ first.val ∧ first.val ≤ 9223372036854775807 at hfirst
    change -9223372036854775808 ≤ last.val ∧ last.val ≤ 9223372036854775807 at hlastRange
    omega
  change (if first.val ≤ (JInt.wrap .i64 (offset.val + first.val)).val ∧
      (JInt.wrap .i64 (offset.val + first.val)).val ≤ last.val then
      Except.ok (JInt.wrap .i64 (offset.val + first.val)) else Except.error JlError.boundsError) = _
  rw [hwrap, if_pos hindex]

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-simdloop-index", juliaFile := "base/simdloop.jl"
    juliaFns := ["@simd", "simd_index"]
    statement := "For every valid zero-based inner-loop offset, SIMD range indexing succeeds within the original range's index interval without native-index overflow."
    source := "base/simdloop.jl:39-85,90-120; valid array index interval"
    status := .proven, prop := ``SimdIndexInBounds
    thm := some ``simdIndexInBounds }
]
end JuliaLean.Proofs.base.simdloop.memory_safety
