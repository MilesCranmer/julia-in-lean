import JuliaLean.Proofs.base.subarray.linear_view
import JuliaLean.base.abstractarray

/-!
`strides`/`stride` of a view of an `Array`, `base/subarray.jl:437-446` and
`base/reinterpretarray.jl:204-206`, master `bbfa0ce4150`.
-/

namespace JuliaLean.BroadcastViews

open JuliaLean



/-- `stride(V, k)` returns a value for every view of an `Array` and every dimension `k ≥ 1`, as
`stride(A, k)` does for every `Array` (`base/reinterpretarray.jl:205-206`: `length(A)` past the
last dimension) and for every `AbstractArray` (`base/abstractarray.jl:597-607`: 1 for a
zero-dimensional array). -/
def StrideTotal : Prop :=
  ∀ (ns : List I64) (I : List LIdx) (k : Nat), IdxInBounds ns I → 1 ≤ k → ∃ v, strideSub ns I k = .ok v

/-- `stride(view(zeros(3, 4), 1, 2), 1)` throws `BoundsError`: `strides(V) == ()`. -/
theorem stride_zero_dim : strideSub [i64 3, i64 4] [.scalar (i64 1), .scalar (i64 2)] 1 = .error .boundsError := by
  decide

theorem strideTotal_refuted : ¬ StrideTotal := by
  intro h
  have hb : IdxInBounds [i64 3, i64 4] [.scalar (i64 1), .scalar (i64 2)] := by
    show 1 ≤ (i64 1).val ∧ (i64 1).val ≤ (i64 3).val ∧ (1 ≤ (i64 2).val ∧ (i64 2).val ≤ (i64 4).val ∧ True)
    decide
  obtain ⟨v, hv⟩ := h [i64 3, i64 4] [.scalar (i64 1), .scalar (i64 2)] 1 hb (by decide)
  rw [stride_zero_dim] at hv
  cases hv

end JuliaLean.BroadcastViews
