import JuliaLean.base.reshapedarray
import JuliaLean.Core
import JuliaLean.Proofs.base.reshapedarray.coverage_reshaped_simple

namespace JuliaLean.ArrayCov

def ReshapedPointerRoutesCorrect : Prop :=
  (∀ first axes stride range, reshaped358ComputeOffset first axes stride range =
      first range - axes range * stride) ∧
  (∀ sizes step size recurse stride rest range tail,
      reshaped360Substrides sizes step size recurse (stride :: rest) (range :: tail) =
      sizes (stride * step range) (size range) ++ recurse rest tail) ∧
  (∀ contiguous elsize memory unsafeConvert view,
      reshaped368UnsafeConvert contiguous elsize memory unsafeConvert view =
      unsafeConvert view.parent + if contiguous view.parent then
        (view.firstIndex - view.parentFirstIndex) * elsize view.parent
      else memory view.parent view.firstIndices) ∧
  (∀ recurse offset parent, reshaped384OffsetNested recurse offset parent =
      recurse (parent.byteOffset + offset) parent.parent) ∧
  (∀ offset parent, reshaped391OffsetNew offset parent = ⟨offset, parent⟩) ∧
  (∀ unsafeConvert offset, reshaped398UnsafeOffset unsafeConvert offset =
      unsafeConvert offset.parent + offset.byteOffset) ∧
  (∀ convert contiguous elsize memory offset view,
      reshaped402Cconvert convert contiguous elsize memory offset view =
      let parent := convert view.parent
      let delta := if contiguous view.parent then
        (view.firstIndex - view.parentFirstIndex) * elsize view.parent
      else memory view.parent view.firstIndices
      offset delta parent)

theorem reshapedPointerRoutesCorrect : ReshapedPointerRoutesCorrect := by
  simp [ReshapedPointerRoutesCorrect, reshaped358ComputeOffset,
    reshaped360Substrides, reshaped368UnsafeConvert, reshaped384OffsetNested,
    reshaped391OffsetNew, reshaped398UnsafeOffset, reshaped402Cconvert]

def ReshapedStridesCorrect : Prop :=
  (∀ contiguous sizeA sizeP stridesP make merge recurse array,
      reshaped424Strides contiguous sizeA sizeP stridesP make merge recurse array =
      if contiguous array then .ok (make (JInt.lit .i64 1) (sizeA array))
      else
        let parentSize := sizeP array.parent
        let parentStrides := stridesP array.parent
        let (mergedSize, mergedStride, n) := merge parentSize parentStrides
        if n = parentSize.length then .ok (make mergedStride (sizeA array))
        else recurse (sizeA array) (JInt.lit .i64 1) mergedSize mergedStride n
          parentSize parentStrides) ∧
  (∀ reshaped merged, reshaped433StridesEmpty reshaped merged =
      if reshaped = merged then .ok [] else .error .notStrided) ∧
  (∀ merge recurse first tail reshaped mergedSize mergedStride n parentSize parentStrides,
      reshaped437Strides merge recurse (first :: tail) reshaped mergedSize mergedStride n
        parentSize parentStrides = do
        let stride := reshaped * mergedStride
        let reshaped := reshaped * first
        let (mergedSize, mergedStride, n, reshaped) :=
          if !tail.isEmpty && reshaped = mergedSize &&
              tail.getD 0 (JInt.lit .i64 0) != JInt.lit .i64 1 then
            let merged := merge parentSize parentStrides (n + 1)
            (merged.1, merged.2.1, merged.2.2, JInt.lit .i64 1)
          else (mergedSize, mergedStride, n, reshaped)
        let rest ← recurse tail reshaped mergedSize mergedStride n parentSize parentStrides
        pure (stride :: rest)) ∧
  (∀ sizes strides n, reshaped450Merge sizes strides n =
      reshaped450MergeLoop sizes strides n (sizes.length - n))

theorem reshapedStridesCorrect : ReshapedStridesCorrect := by
  simp [ReshapedStridesCorrect, reshaped424Strides, reshaped433StridesEmpty,
    reshaped437Strides, reshaped450Merge]

end JuliaLean.ArrayCov
