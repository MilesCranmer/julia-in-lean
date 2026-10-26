import JuliaLean.Core

namespace JuliaLean.ArrayCov

structure MemoryRefModel where
  memoryLength : JInt64
  offset : JInt64
  deriving Repr, DecidableEq

structure WrappedArrayModel where
  ref : MemoryRefModel
  dims : List JInt64
  deriving Repr, DecidableEq

inductive WrapError where
  | dimensionMismatch | conversion | invalidDimensions
  deriving Repr, DecidableEq

abbrev WrapJl (α : Type) := Except WrapError α

def array3241WrapCheck (checkedDims : List JInt64 → WrapJl JInt64)
    (ref : MemoryRefModel) (dims : List JInt64) : WrapJl MemoryRefModel := do
  let memoryLength := ref.memoryLength + JInt.lit .i64 1 - ref.offset
  let length ← checkedDims dims
  if memoryLength < length then throw .dimensionMismatch
  pure ref

def array3249InvalidWrap (_length : JInt64) (_dims : List JInt64)
    (_product : JInt64) : WrapJl Unit := .error .dimensionMismatch

def array3254WrapRefDims (convertDims : List Int → WrapJl (List JInt64))
    (wrapCheck : MemoryRefModel → List JInt64 → WrapJl MemoryRefModel)
    (ref : MemoryRefModel) (rawDims : List Int) : WrapJl WrappedArrayModel := do
  let dims ← convertDims rawDims
  let ref ← wrapCheck ref dims
  pure ⟨ref, dims⟩

def array3260WrapMemoryDims (memoryRef : JInt64 → MemoryRefModel)
    (convertDims : List Int → WrapJl (List JInt64))
    (wrapCheck : MemoryRefModel → List JInt64 → WrapJl MemoryRefModel)
    (memoryLength : JInt64) (rawDims : List Int) : WrapJl WrappedArrayModel := do
  let dims ← convertDims rawDims
  let ref ← wrapCheck (memoryRef memoryLength) dims
  pure ⟨ref, dims⟩

def array3265WrapRefLength (convertInt : Int → WrapJl JInt64)
    (wrapCheck : MemoryRefModel → List JInt64 → WrapJl MemoryRefModel)
    (ref : MemoryRefModel) (rawLength : Int) : WrapJl WrappedArrayModel := do
  let length ← convertInt rawLength
  let dims := [length]
  let ref ← wrapCheck ref dims
  pure ⟨ref, dims⟩

def array3275WrapMemory (memoryRef : JInt64 → MemoryRefModel)
    (memoryLength : JInt64) : WrappedArrayModel :=
  let ref := memoryRef memoryLength
  ⟨ref, [memoryLength]⟩

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
