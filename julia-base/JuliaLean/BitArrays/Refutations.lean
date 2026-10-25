import JuliaLean.BitArrays.Properties

/-!
# Counterexamples

Each theorem refutes a property of `Properties.lean` with one concrete input,
evaluated by the kernel. The reproducers `repro/bitarrays-*.jl` run the same
inputs in Julia.
-/

namespace JuliaLean.BitArrays

open BV

private def i64 (x : Int) : JInt64 := JInt.lit .i64 x

/-- `circshift!(falses(0), 1)` throws `DivideError` (`i %= n` with `n = 0`,
`base/bitarray.jl:1421`); `circshift!(Bool[], 1)` returns `Bool[]`. -/
theorem circshiftEmpty :
    kindOf (circshift (ofList []) none (i64 1)) = .error .divide ∧
    kindOf (circshift (ofList []) (some (ofList [])) (i64 1)) = .error .divide := by
  constructor <;> rfl

theorem circshiftAgrees_refuted : ¬ CircshiftAgrees := by
  intro h
  have := (h [] [] (i64 1) (by decide) rfl).1
  rw [circshiftEmpty.1] at this
  cases this

/-- `reverse(falses(0, 7); dims=1)` and `reverse(falses(0, 7); dims=2)` throw
`ArgumentError("step cannot be zero")`: the stride `M * size(A, d)` is zero and
`0:stride:(N-stride)` is built from it (`base/bitarray.jl:1241-1253`). -/
theorem reverseDimsEmpty :
    kindOf (reverseDims (ofList []) [0, 7] (i64 1) 0) = .error .argument ∧
    kindOf (reverseDims (ofList []) [0, 7] (i64 2) 0) = .error .argument := by
  constructor <;> rfl

theorem reverseDimsAgrees_refuted : ¬ ReverseDimsAgrees := by
  intro h
  have := h [] [0, 7] (i64 2) 0 (by decide) rfl (by decide) (by decide)
  rw [reverseDimsEmpty.2] at this
  cases this

/-- `deleteat!(BitVector([0,1,0]), 0:-1)` throws `BoundsError`;
`deleteat!([false,true,false], 0:-1)` deletes nothing. -/
theorem deleteatEmptyRange :
    kindOf (deleteatRange (ofList [false, true, false]) ⟨i64 0, i64 (-1)⟩) = .error .bounds ∧
    (Ref.deleteatRange [false, true, false] ⟨i64 0, i64 (-1)⟩) = .ok [false, true, false] := by
  constructor <;> rfl

theorem deleteatRangeAgrees_refuted : ¬ DeleteatRangeAgrees := by
  intro h
  have := h [false, true, false] ⟨i64 0, i64 (-1)⟩ (by decide) (by decide)
  rw [deleteatEmptyRange.1, deleteatEmptyRange.2] at this
  cases this

/-- `resize!(BitVector(), -1)` throws `BoundsError`; `resize!(Bool[], -1)` throws
`ArgumentError` (`base/array.jl:1575-1576`). -/
theorem resizeNegative : kindOf (resize (ofList []) (i64 (-1)) false 0) = .error .bounds := rfl

theorem resizeAgrees_refuted : ¬ ResizeAgrees := by
  intro h
  have := h [] (i64 (-1)) false 0 (by decide)
  rw [resizeNegative] at this
  exact absurd this.2 (by decide)

/-- `count(trues(128); init=Int8(0))` is `-128`; for `fill(true, 128)` it is `128`. -/
theorem countInt8Wraps :
    (count (ofList (List.replicate 128 true)) (JInt.lit .i8 0)).val = -128 ∧
    Ref.count .i8 (JInt.lit .i8 0) (List.replicate 128 true) = 128 := by
  constructor <;> decide +kernel

theorem countAgrees_refuted : ¬ CountAgrees := by
  intro h
  have := h .i8 (JInt.lit .i8 0) (List.replicate 128 true)
  rw [countInt8Wraps.1, countInt8Wraps.2] at this
  exact absurd this (by decide +kernel)

/-- `B = falses(4); B[trues(4)] = trues(5)` writes all four elements and then throws
`DimensionMismatch`; on a `Vector{Bool}` the throw comes first. -/
theorem setindexMaskWritesBeforeThrow :
    setindexMask (ofList [false, false, false, false]) [true, true, true, true, true]
      (ofList [true, true, true, true]) = (ofList [true, true, true, true], some dimMismatch) ∧
    Ref.setindexMask [false, false, false, false] [true, true, true, true, true]
      [true, true, true, true] = ([false, false, false, false], some dimMismatch) := by
  constructor <;> decide +kernel

theorem setindexMaskAgrees_refuted : ¬ SetindexMaskAgrees := by
  intro h
  have := h [false, false, false, false] [true, true, true, true, true] [true, true, true, true] (by decide)
  simp only [setindexMaskWritesBeforeThrow] at this
  exact absurd this.1 (by decide +kernel)

/-- `M = falses(2, 2); push!(vec(M), true)` sets an unused bit of `M`'s only chunk:
`M` still has four `false` elements but `M == falses(2, 2)` is `false`. -/
theorem vecPushCorruptsParent :
    let p := ((Aliased.vecOf (ofList [false, false, false, false])).onVec (fun v => push v true 0)).parent
    p.toList = [false, false, false, false] ∧
    bitEq p (ofList [false, false, false, false]) = false := by
  decide

/-- `M = falses(65, 1); pop!(vec(M))` deletes `M`'s second chunk: `M` keeps 65
elements stored in one chunk, so `M[65]` reads past the chunk vector. -/
theorem vecPopTruncatesParent :
    let p := ((Aliased.vecOf (ofList (List.replicate 65 false))).onVec
      (fun v => match pop v with | .ok (v', _) => v' | .error _ => v)).parent
    p.len = 65 ∧ p.chunks.length = 1 ∧ numBitChunks p.len = 2 := by
  decide

theorem vecAliasKeepsParentValid_refuted : ¬ VecAliasKeepsParentValid := by
  intro h
  have := (h [false, false, false, false] true 0 (by decide)).1
  exact absurd this (by decide)

/-- `symdiff!(BitSet([1]), [2, 2])` toggles `2` twice and returns `BitSet([1])`;
`symdiff!(Set([1]), [2, 2])` returns `Set([1, 2])`. -/
theorem bitsetSymdiffDuplicate :
    ((BitSetS.ofList [i64 1]).symdiff [i64 2, i64 2]).contains (i64 2) = false := by
  decide

theorem bitSetSymdiffAgrees_refuted : ¬ BitSetSymdiffAgrees := by
  intro h
  have := h [i64 1] [i64 2, i64 2] (i64 2)
  rw [bitsetSymdiffDuplicate] at this
  exact absurd this (by decide)

end JuliaLean.BitArrays
