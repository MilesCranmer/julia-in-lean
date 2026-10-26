import JuliaLean.Tuples.Props

/-! Counterexamples for the refuted tuple properties, evaluated by `decide`. -/

namespace JuliaLean.Tuples

open JuliaLean.Float

/-- `Base.split_rest((1,), 1, 2)` returns `((), (1,))`: the element already
consumed by the first `indexed_iterate` is returned again. The `Vector`
method throws `ArgumentError` (one element left, one requested). -/
theorem splitRestAgrees_refuted : ¬ SplitRestAgrees := by
  intro h
  have := h.1 [1] 1 2 (by decide) (by decide) (by decide) (by decide)
  revert this
  decide

/-- The named-tuple method is wrong in the same way:
`Base.split_rest((x=1,), 1, 2) == ((;), (x = 1,))`. -/
theorem splitRestNT_refuted :
    ¬ (SameOutcome (splitRestNT [("x", (1 : Int))] (I64 1) (I64 2))
        (splitRestRef [("x", (1 : Int))] (I64 1) (I64 2))) := by
  decide

/-- Consequence for destructuring: `a, b..., c = (1,)` binds `a = 1, b = (), c = 1`. -/
theorem destructureMid_duplicates : destructureMid [(1 : Int)] = .ok (1, [], 1) := by
  rfl

/-- `Base.split_rest([1], -1)` grows the vector with `resize!` and returns an
uninitialised slot. -/
theorem splitRestPartition_refuted : ¬ SplitRestPartition := by
  intro h
  have hv : splitRestVector [(1 : Int)] (I64 (-1)) (I64 1) = .ok ([some 1, none], []) := by rfl
  have := h [1] (I64 (-1))
  rw [hv] at this
  exact absurd this (by decide)

/-- `haskey((a=1,), Int32(1))` throws `TypeError` from `isdefined`. -/
theorem haskeyInteger_refuted : ¬ HaskeyInteger := by
  intro h
  have := (h [("a", 1)] .i32 (JInt.lit .i32 1) 0).1
  simp [haskeyNT, isdefinedNT] at this

/-- `findall(in([0.0]), (-0.0,))` is empty although `-0.0 in [0.0]`. -/
theorem findallInAgrees_refuted : ¬ FindallInAgrees := by
  intro h
  have := h [F64.zero true] [F64.zero false]
  revert this
  decide

/-- `(10,)[true] == 10`, while `[10][true]` throws `ArgumentError`. -/
theorem boolIndexAgrees_refuted : ¬ BoolIndexAgrees := by
  intro h
  have := (h [10] true 0 0).1
  revert this
  decide

/-- `(10, 20)[false:true]` throws `BoundsError` (it reads `t[0]`), while
`(10, 20)[[false, true]] == (20,)`. -/
theorem boolRangeLogical_refuted : ¬ BoolRangeLogical := by
  intro h
  have := h [10, 20] false 2 (by decide) (by decide)
  revert this
  decide

/-- `()[typemax(UInt)]` throws `InexactError`, while
`Base.setindex((), 0, typemax(UInt))` throws `BoundsError`. -/
theorem getindexBoundsError_refuted : ¬ GetindexBoundsError := by
  intro h
  have := h [] .u64 (JInt.typemax .u64) (by decide)
  revert this
  decide

/-- `prod(()) == 1`, while `prod(identity, ())` throws `ArgumentError`. -/
theorem prodAgrees_refuted : ¬ ProdAgrees := by
  intro h
  have := h []
  revert this
  decide

end JuliaLean.Tuples
