import JuliaLean.Core
import JuliaLean.ArrayCov.ReshapedSimple

namespace JuliaLean.ArrayCov

structure ReshapedView where
  parent : List Int
  firstIndex : JInt64
  parentFirstIndex : JInt64
  firstIndices : List JInt64
  deriving Repr, DecidableEq

structure OffsetConvertModel where
  byteOffset : JInt64
  parent : Int
  deriving Repr, DecidableEq

def reshaped358ComputeOffset (firstRange axesFirst : Int → JInt64)
    (stride : JInt64) (range : Int) : JInt64 :=
  firstRange range - axesFirst range * stride

def reshaped360Substrides (sizeToStrides : JInt64 → List JInt64 → List JInt64)
    (step : Int → JInt64) (size : Int → List JInt64)
    (recurse : List JInt64 → List Int → List JInt64)
    (strides : List JInt64) (indices : List Int) : List JInt64 :=
  match strides, indices with
  | stride :: restStrides, range :: restIndices =>
      sizeToStrides (stride * step range) (size range) ++ recurse restStrides restIndices
  | _, _ => recurse strides indices

def reshaped368UnsafeConvert (contiguous : List Int → Bool)
    (elsize : List Int → JInt64)
    (memoryOffset : List Int → List JInt64 → JInt64)
    (unsafeConvert : List Int → JInt64)
    (view : ReshapedView) : JInt64 :=
  let delta := if contiguous view.parent then
    (view.firstIndex - view.parentFirstIndex) * elsize view.parent
  else memoryOffset view.parent view.firstIndices
  unsafeConvert view.parent + delta

def reshaped384OffsetNested (recurse : JInt64 → Int → OffsetConvertModel)
    (byteOffset : JInt64) (parent : OffsetConvertModel) : OffsetConvertModel :=
  recurse (parent.byteOffset + byteOffset) parent.parent

def reshaped391OffsetNew (byteOffset : JInt64) (parent : Int) : OffsetConvertModel :=
  ⟨byteOffset, parent⟩

def reshaped398UnsafeOffset (unsafeConvert : Int → JInt64)
    (offset : OffsetConvertModel) : JInt64 :=
  unsafeConvert offset.parent + offset.byteOffset

def reshaped402Cconvert (cconvert : List Int → Int)
    (contiguous : List Int → Bool) (elsize : List Int → JInt64)
    (memoryOffset : List Int → List JInt64 → JInt64)
    (offsetConvert : JInt64 → Int → OffsetConvertModel)
    (view : ReshapedView) : OffsetConvertModel :=
  let parent := cconvert view.parent
  let delta := if contiguous view.parent then
    (view.firstIndex - view.parentFirstIndex) * elsize view.parent
  else memoryOffset view.parent view.firstIndices
  offsetConvert delta parent

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

inductive ReshapedStrideError where
  | notStrided
  deriving Repr, DecidableEq

abbrev ReshapedStrideJl (α : Type) := Except ReshapedStrideError α

def reshaped424Strides (contiguous : ReshapedValue → Bool)
    (sizeArray : ReshapedValue → List JInt64)
    (sizeParent stridesParent : List Int → List JInt64)
    (sizeToStrides : JInt64 → List JInt64 → List JInt64)
    (merge : List JInt64 → List JInt64 → JInt64 × JInt64 × Nat)
    (recurse : List JInt64 → JInt64 → JInt64 → JInt64 → Nat →
      List JInt64 → List JInt64 → ReshapedStrideJl (List JInt64))
    (array : ReshapedValue) : ReshapedStrideJl (List JInt64) :=
  if contiguous array then .ok (sizeToStrides (JInt.lit .i64 1) (sizeArray array))
  else
    let parentSize := sizeParent array.parent
    let parentStrides := stridesParent array.parent
    let (mergedSize, mergedStride, n) := merge parentSize parentStrides
    if n = parentSize.length then .ok (sizeToStrides mergedStride (sizeArray array))
    else recurse (sizeArray array) (JInt.lit .i64 1) mergedSize mergedStride n
      parentSize parentStrides

def reshaped433StridesEmpty (reshaped mergedSize : JInt64) :
    ReshapedStrideJl (List JInt64) :=
  if reshaped = mergedSize then .ok [] else .error .notStrided

def reshaped437Strides (merge : List JInt64 → List JInt64 → Nat →
      JInt64 × JInt64 × Nat)
    (recurse : List JInt64 → JInt64 → JInt64 → JInt64 → Nat →
      List JInt64 → List JInt64 → ReshapedStrideJl (List JInt64))
    (size : List JInt64) (reshaped mergedSize mergedStride : JInt64)
    (n : Nat) (parentSize parentStrides : List JInt64) : ReshapedStrideJl (List JInt64) :=
  match size with
  | [] => reshaped433StridesEmpty reshaped mergedSize
  | first :: tail => do
      let stride := reshaped * mergedStride
      let reshaped := reshaped * first
      let (mergedSize, mergedStride, n, reshaped) :=
        if !tail.isEmpty && reshaped = mergedSize && tail.getD 0 (JInt.lit .i64 0) != JInt.lit .i64 1 then
          let merged := merge parentSize parentStrides (n + 1)
          (merged.1, merged.2.1, merged.2.2, JInt.lit .i64 1)
        else (mergedSize, mergedStride, n, reshaped)
      let rest ← recurse tail reshaped mergedSize mergedStride n parentSize parentStrides
      pure (stride :: rest)

def reshaped450MergeLoop : List JInt64 → List JInt64 → Nat → Nat →
    JInt64 × JInt64 × Nat
  | sizes, strides, n, 0 =>
      (sizes.getD (n - 1) (JInt.lit .i64 1),
       strides.getD (n - 1) (JInt.lit .i64 1), n)
  | sizes, strides, n, fuel + 1 =>
      let size := sizes.getD (n - 1) (JInt.lit .i64 1)
      let stride := strides.getD (n - 1) (JInt.lit .i64 1)
      if n ≥ sizes.length then (size, stride, n)
      else
        let nextSize := sizes.getD n (JInt.lit .i64 1)
        let nextStride := strides.getD n (JInt.lit .i64 1)
        if size = JInt.lit .i64 1 then
          let sizes := sizes.set (n - 1) nextSize
          let strides := strides.set (n - 1) nextStride
          reshaped450MergeLoop sizes strides (n + 1) fuel
        else if nextStride = stride * size || nextSize = JInt.lit .i64 1 then
          let sizes := sizes.set (n - 1) (size * nextSize)
          reshaped450MergeLoop sizes strides (n + 1) fuel
        else (size, stride, n)

def reshaped450Merge (sizes strides : List JInt64) (n : Nat) :
    JInt64 × JInt64 × Nat :=
  reshaped450MergeLoop sizes strides n (sizes.length - n)

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
