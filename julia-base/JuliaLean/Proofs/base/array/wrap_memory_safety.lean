import JuliaLean.base.array
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.array.wrap_memory_safety
open JuliaLean JuliaLean.base.array

def WrapMemoryInBounds : Prop :=
  ∀ (capacity : I) (dims : List I),
    0 ≤ capacity.val → capacity.val < 2 ^ 63 - 1 →
    ∀ result,
      wrapMemoryDims (m := Except Error) pure
        (fun memory : I => pure (memory, one))
        (wrapCheck Prod.fst id Prod.snd checkedDims)
        (fun ref dimensions => pure (ref, dimensions)) capacity dims = .ok result →
      (∀ dimension ∈ result.2, 0 ≤ dimension.val) ∧
      ((result.2.map (fun dimension => dimension.val)).prod ≤ capacity.val)

theorem wrapMemoryInBounds_refuted : ¬ WrapMemoryInBounds := by
  intro h
  have bad := h (JInt.wrap .i64 1) [JInt.wrap .i64 (-1)]
    (by decide) (by decide)
    ((JInt.wrap .i64 1, one), [JInt.wrap .i64 (-1)]) rfl
  have impossible := bad.1 (JInt.wrap .i64 (-1)) (by simp)
  change 0 ≤ (-1 : Int) at impossible
  omega

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-array-wrap-memory", juliaFile := "base/array.jl"
    juliaFns := ["wrap(::Type{Array}, ::Memory, dims)", "wrap(::Type{Array}, ::Memory, length)", "wrap(::Type{Array}, ::Memory)"]
    statement := "Wrapping Memory produces an Array with nonnegative dimensions whose element count fits the underlying allocation."
    source := "base/array.jl:3236-3274; base/boot.jl:813"
    status := .refuted, prop := ``WrapMemoryInBounds
    thm := some ``wrapMemoryInBounds_refuted
    issue := "none found (queries: wrap Array negative; Base.wrap negative dims; wrap Memory negative length; wrap checked_dims)"
    notes := "A negative singleton dimension bypasses the Memory constructor's dimension check; covered by multidimcov-wrap-negative-length." }
]
end JuliaLean.Proofs.base.array.wrap_memory_safety
