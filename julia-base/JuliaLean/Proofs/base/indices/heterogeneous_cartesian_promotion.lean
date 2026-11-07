import JuliaLean.base.multidimensional
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.indices.HeterogeneousCartesianPromotion

open JuliaLean
open JuliaLean.base.multidimensional.Models1Group5
open JuliaLean.base.multidimensional.Models1Group5.PromotionMetadata

/-- Array literals contain their supplied values, promoting to a common element
type when one exists and using a heterogeneous array otherwise (manual, Arrays,
"Array literals"). For distinct concrete CartesianIndices types of equal rank,
their supplied Base promotion rule must therefore return a common representation
rather than raise a missing-method error. Every represented axis family can
realize the same small interval `1:2`; this property makes no arithmetic or
allocation-size assumptions. The computation uses the installed closed Base
promotion model, including `indices_promote_type` dispatch. -/
def CompatibleCartesianPromotion : Prop :=
  ∀ (rank : Nat) (left right : List RangeType64),
    (rank : Int) ≤ IntTy.max .i64 →
    left.length = rank → right.length = rank → left ≠ right →
    ∃ result, promoteRegionType64 rank left right = .ok result

/-- The first region uses `(1:2, Base.OneTo(2))`; the second uses `(1:2, 1:2)`.
The method at `base/indices.jl:492` requires a homogeneous tuple type, so the
heterogeneous left tuple is rejected before any range promotion is evaluated. -/
theorem witness_failure :
    promoteRegionType64 2 [.unitRange, .oneTo] [.unitRange, .unitRange] =
      .error ⟨"indices_promote_type",
        [.value (rangeTupleType [.unitRange, .oneTo]),
         .value (rangeTupleType [.unitRange, .unitRange])]⟩ := by
  rfl

theorem compatibleCartesianPromotion_refuted : ¬ CompatibleCartesianPromotion := by
  intro h
  obtain ⟨result, hresult⟩ := h 2 [.unitRange, .oneTo] [.unitRange, .unitRange]
    (by decide) (by decide) (by decide) (by decide)
  rw [witness_failure] at hresult
  cases hresult

open JuliaLean.Registry

def entries : List Entry := [
  { id := "indices-heterogeneous-cartesian-promotion"
    juliaFile := "base/indices.jl"
    juliaFns := ["indices_promote_type", "promote_rule(::Type{CartesianIndices{N,R1}}, ::Type{CartesianIndices{N,R2}})"]
    statement := "Distinct equal-rank CartesianIndices types with built-in Int64 range axes admit promotion without a missing-method error, including heterogeneous axis tuples used by ordinary array literals."
    source := "doc/src/manual/arrays.md, Array literals; base/multidimensional.jl:355-356; base/indices.jl:491-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
    status := .refuted
    prop := ``CompatibleCartesianPromotion
    thm := some ``compatibleCartesianPromotion_refuted
    issue := "repro/indices-heterogeneous-cartesian-promotion.jl" }
]

end JuliaLean.Proofs.base.indices.HeterogeneousCartesianPromotion
