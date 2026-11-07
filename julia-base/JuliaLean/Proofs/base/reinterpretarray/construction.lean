import JuliaLean.base.reinterpretarray

namespace JuliaLean.ArrayCov

def ReinterpretSimpleConstructionCorrect : Prop :=
  (∀ array, reinterpret104Identity array = array) ∧
  (∀ array, reinterpret145ReshapeIdentity array = array) ∧
  (∀ call type array, reinterpret190Nested call type array = call type array.parent) ∧
  (∀ call construct target source parent type array,
      reinterpret191NestedReshape call construct target source parent type array =
      if target = source ∨ target = parent ∨ source = parent then
        call true type array.parent else construct type array) ∧
  (∀ size strides array, reinterpret204Strides size strides array =
      strides (JInt.lit .i64 1) (size array)) ∧
  (∀ contiguous array, reinterpret229Contiguous contiguous array = contiguous array.parent) ∧
  (∀ similar array type dims, reinterpret231Similar similar array type dims =
      similar array.parent type dims) ∧
  (∀ similar parentType dims, reinterpret232SimilarType similar parentType dims =
      similar parentType dims)

theorem reinterpretSimpleConstructionCorrect : ReinterpretSimpleConstructionCorrect := by
  simp [ReinterpretSimpleConstructionCorrect, reinterpret104Identity,
    reinterpret145ReshapeIdentity, reinterpret190Nested, reinterpret191NestedReshape,
    reinterpret204Strides, reinterpret229Contiguous, reinterpret231Similar,
    reinterpret232SimilarType]
def ReinterpretCartesianBasicsCorrect : Prop :=
  (∀ k, reinterpret270CombineStyle k = k) ∧
  (∀ index, reinterpret276ToIndex index = index) ∧
  (∀ k index, reinterpret277NextIndex k index =
      if index.i < k then ⟨index.i + JInt.lit .i64 1, index.j⟩
      else ⟨JInt.lit .i64 1, index.j + JInt.lit .i64 1⟩) ∧
  (∀ k index, reinterpret279PrevIndex k index =
      if JInt.lit .i64 1 < index.i then ⟨index.i - JInt.lit .i64 1, index.j⟩
      else ⟨k, index.j - JInt.lit .i64 1⟩) ∧
  (∀ k indices, reinterpret285IndicesConstructor k indices =
      if JInt.lit .i64 1 < k then .ok ⟨k, indices⟩ else .error .assertionError) ∧
  (∀ each construct k array, reinterpret287EachIndex each construct k array =
      construct k (each 1 array.parent)) ∧
  (∀ iter, reinterpret295IndicesSize iter =
      (iter.k, JInt.lit .i64 iter.indices2.length)) ∧
  (∀ oneto iter, reinterpret296IndicesAxes oneto iter = (oneto iter.k, iter.indices2)) ∧
  (∀ first iter, reinterpret298IndicesFirst first iter =
      ⟨JInt.lit .i64 1, first iter.indices2⟩) ∧
  (∀ last iter, reinterpret299IndicesLast last iter = ⟨iter.k, last iter.indices2⟩) ∧
  (∀ iter, reinterpret324SimdOuter iter = iter.indices2) ∧
  (∀ iter outer, reinterpret325SimdLength iter outer = iter.k) ∧
  (∀ k last i1, reinterpret326SimdIndex k last i1 = ⟨i1 + JInt.lit .i64 1, last⟩) ∧
  (∀ fallback array indices, reinterpret330MaybeReshapeFallback fallback array indices =
      fallback 0 array indices) ∧
  (∀ array indices, reinterpret331MaybeReshapeIdentity array indices = array) ∧
  (∀ each style parent array, reinterpret362EachIndex each style parent array =
      each style (parent array))

theorem reinterpretCartesianBasicsCorrect : ReinterpretCartesianBasicsCorrect := by
  simp [ReinterpretCartesianBasicsCorrect, reinterpret270CombineStyle,
    reinterpret276ToIndex, reinterpret277NextIndex, reinterpret279PrevIndex,
    reinterpret285IndicesConstructor, reinterpret287EachIndex, reinterpret295IndicesSize,
    reinterpret296IndicesAxes, reinterpret298IndicesFirst, reinterpret299IndicesLast,
    reinterpret324SimdOuter, reinterpret325SimdLength, reinterpret326SimdIndex,
    reinterpret330MaybeReshapeFallback, reinterpret331MaybeReshapeIdentity,
    reinterpret362EachIndex]
def ReinterpretMetadataRoutesCorrect : Prop :=
  (∀ array, reinterpret366Parent array = array.parent) ∧
  (∀ ids array, reinterpret367DataIds ids array = ids array.parent) ∧
  (∀ copy call type array, reinterpret368Unalias copy call type array =
      call type (copy array.parent)) ∧
  (∀ copy call type array, reinterpret369UnaliasReshape copy call type array =
      call true type (copy array.parent)) ∧
  (∀ array, reinterpret382SizeZero array = []) ∧
  (∀ array, reinterpret396AxesZero array = []) ∧
  (∀ offset array, reinterpret398HasOffset offset array = offset array.parent) ∧
  (∀ convert source array, reinterpret407Cconvert convert source array =
      convert source array.parent) ∧
  (∀ convert source target array, reinterpret408UnsafeConvert convert source target array =
      ⟨target, convert source array.parent⟩) ∧
  (∀ check parent array, reinterpret422CheckPtrReshaped check parent array =
      check (parent array)) ∧
  (∀ check parent array, reinterpret423CheckPtrSubarray check parent array =
      check (parent array)) ∧
  (∀ array, reinterpret424CheckPtrDense array = true) ∧
  (∀ array, reinterpret425CheckPtrAbstract array = false) ∧
  (∀ first get array, reinterpret427GetZero first get array = get array (first array)) ∧
  (∀ bounds ptr assigned array indices, reinterpret429IsAssigned bounds ptr assigned array indices =
      (bounds array indices && (ptr array || assigned array indices))) ∧
  (∀ assigned array index, reinterpret430IsAssignedCartesian assigned array index =
      assigned array.parent index.j) ∧
  (∀ array indices, reinterpret431AssignedRa array indices = true) ∧
  (∀ first set array value, reinterpret577SetZero first set array value =
      set array value (first array))

theorem reinterpretMetadataRoutesCorrect : ReinterpretMetadataRoutesCorrect := by
  simp [ReinterpretMetadataRoutesCorrect, reinterpret366Parent, reinterpret367DataIds,
    reinterpret368Unalias, reinterpret369UnaliasReshape, reinterpret382SizeZero,
    reinterpret396AxesZero, reinterpret398HasOffset, reinterpret407Cconvert,
    reinterpret408UnsafeConvert, reinterpret422CheckPtrReshaped,
    reinterpret423CheckPtrSubarray, reinterpret424CheckPtrDense,
    reinterpret425CheckPtrAbstract, reinterpret427GetZero, reinterpret429IsAssigned,
    reinterpret430IsAssignedCartesian, reinterpret431AssignedRa, reinterpret577SetZero]

def ReinterpretErrorHelpersCorrect : Prop :=
  (∀ source target culprit, reinterpret14ThrowBits source target culprit =
      if culprit.id = target.id then .error .targetNotBits else .error .sourceNotBits) ∧
  (∀ source target message, reinterpret18ThrowSizeZero source target message =
      .error .zeroDimSize) ∧
  (∀ source target, reinterpret23ThrowSingleton source target = .error .singletonTarget) ∧
  (∀ source target culprit, reinterpret27ThrowBitPadding source target culprit =
      if culprit.id = target.id then .error .targetBitPadding else .error .sourceBitPadding) ∧
  (∀ source target dim, reinterpret74ThrowNonIntegral source target dim = .error .nonIntegral) ∧
  (∀ source target axis, reinterpret80ThrowAxes source target axis = .error .badFirstAxis) ∧
  (∀ source target, reinterpret108ThrowMultiple source target = .error .nonMultiple) ∧
  (∀ array target, reinterpret113ThrowSizeOne array target = .error .wrongFirstAxis) ∧
  (∀ source target, reinterpret119ThrowSingletonSource source target = .error .sourceSingleton)

theorem reinterpretErrorHelpersCorrect : ReinterpretErrorHelpersCorrect := by
  simp [ReinterpretErrorHelpersCorrect, reinterpret14ThrowBits,
    reinterpret18ThrowSizeZero, reinterpret23ThrowSingleton,
    reinterpret27ThrowBitPadding, reinterpret74ThrowNonIntegral,
    reinterpret80ThrowAxes, reinterpret108ThrowMultiple, reinterpret113ThrowSizeOne,
    reinterpret119ThrowSingletonSource]
def ReinterpretConstructorsCorrect : Prop :=
  (∀ subpadding source target array,
      reinterpret73Construct subpadding source target array = do
        if !target.isBits then throw .targetNotBits
        if !source.isBits then throw .sourceNotBits
        if target.hasBitPadding then throw .targetBitPadding
        if source.hasBitPadding then throw .sourceBitPadding
        if array.rank = 0 && target.alignedSize != source.alignedSize then throw .zeroDimSize
        if array.rank != 0 && source.alignedSize != target.alignedSize then
          if target.isSingleton then
            if !source.isSingleton then throw .singletonTarget
          else
            let remainder ← JInt.remInt (array.firstAxis.length * source.alignedSize)
              target.alignedSize |>.mapError fun _ => .nonIntegral
            if remainder.val != 0 then throw .nonIntegral
          if array.firstAxis.first.val != 1 then throw .badFirstAxis
        let readable := subpadding target source
        let writable := subpadding source target
        pure ⟨array, array.rank, source, target, false, readable, writable⟩) ∧
  (∀ subpadding source target array,
      reinterpret107ConstructReshape subpadding source target array = do
        if !target.isBits then throw .targetNotBits
        if !source.isBits then throw .sourceNotBits
        if target.hasBitPadding then throw .targetBitPadding
        if source.hasBitPadding then throw .sourceBitPadding
        let rank ← if source.alignedSize = target.alignedSize then pure array.rank
          else if target.alignedSize < source.alignedSize then do
            if target.isSingleton then throw .singletonTarget
            let remainder ← JInt.remInt source.alignedSize target.alignedSize
              |>.mapError fun _ => .nonMultiple
            if remainder.val != 0 then throw .nonMultiple
            pure (array.rank + 1)
          else do
            if source.isSingleton then throw .sourceSingleton
            let remainder ← JInt.remInt target.alignedSize source.alignedSize
              |>.mapError fun _ => .nonMultiple
            if remainder.val != 0 then throw .nonMultiple
            let rank := array.rank - 1
            if rank < 0 then throw .zeroDimSize
            let expected ← JInt.div target.alignedSize source.alignedSize
              |>.mapError fun _ => .wrongFirstAxis
            if array.firstAxis.first.val != 1 || array.firstAxis.length != expected then
              throw .wrongFirstAxis
            pure rank
        let readable := subpadding target source
        let writable := subpadding source target
        pure ⟨array, rank, source, target, true, readable, writable⟩)

theorem reinterpretConstructorsCorrect : ReinterpretConstructorsCorrect := by
  constructor <;> intros <;> rfl

end JuliaLean.ArrayCov
