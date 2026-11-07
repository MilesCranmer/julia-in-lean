import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

def ArrayWrapCorrect : Prop :=
  (∀ checked ref dims, array3241WrapCheck checked ref dims = do
      let memoryLength := ref.memoryLength + JInt.lit .i64 1 - ref.offset
      let length ← checked dims
      if memoryLength < length then throw .dimensionMismatch
      pure ref) ∧
  (∀ length dims product, array3249InvalidWrap length dims product =
      .error .dimensionMismatch) ∧
  (∀ convert check ref dims, array3254WrapRefDims convert check ref dims = do
      let dims ← convert dims
      let ref ← check ref dims
      pure ⟨ref, dims⟩) ∧
  (∀ memoryRef convert check length dims,
      array3260WrapMemoryDims memoryRef convert check length dims = do
      let dims ← convert dims
      let ref ← check (memoryRef length) dims
      pure ⟨ref, dims⟩) ∧
  (∀ convert check ref length, array3265WrapRefLength convert check ref length = do
      let length ← convert length
      let dims := [length]
      let ref ← check ref dims
      pure ⟨ref, dims⟩) ∧
  (∀ memoryRef length, array3275WrapMemory memoryRef length =
      ⟨memoryRef length, [length]⟩)

theorem arrayWrapCorrect : ArrayWrapCorrect := by
  simp [ArrayWrapCorrect, array3241WrapCheck, array3249InvalidWrap,
    array3254WrapRefDims, array3260WrapMemoryDims, array3265WrapRefLength,
    array3275WrapMemory]

end JuliaLean.ArrayCov
