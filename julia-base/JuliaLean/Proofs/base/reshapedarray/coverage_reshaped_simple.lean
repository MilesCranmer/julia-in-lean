import JuliaLean.base.reshapedarray
import JuliaLean.Core

namespace JuliaLean.ArrayCov

def ReshapedConstructionCorrect : Prop :=
  (∀ parent dims mi, reshaped10Constructor parent dims mi = ⟨parent, dims, mi⟩) ∧
  (∀ parent iter array, reshaped20IteratorConstructor parent iter array =
      iter (parent array) array.mi) ∧
  (∀ each parent mi, reshaped21Iterator each parent mi = ⟨each parent, mi⟩) ∧
  (∀ length iterator, reshaped35IteratorLength length iterator = length iterator.iter) ∧
  (∀ defined eltype iterator any, reshaped36IteratorEltype defined eltype iterator any =
      if defined iterator then eltype iterator else any) ∧
  (∀ dims length, reshaped38ThrowDimensionMismatch dims length =
      .error .dimensionMismatch)

theorem reshapedConstructionCorrect : ReshapedConstructionCorrect := by
  simp [ReshapedConstructionCorrect, reshaped10Constructor,
    reshaped20IteratorConstructor, reshaped21Iterator, reshaped35IteratorLength,
    reshaped36IteratorEltype, reshaped38ThrowDimensionMismatch]


def ReshapedMetadataCorrect : Prop :=
  (∀ array, reshaped253Size array = array.dims) ∧
  (∀ length array, reshaped254Length length array = length array.parent) ∧
  (∀ similar array type dims, reshaped255Similar similar array type dims =
      similar array.parent type dims) ∧
  (∀ similar parentType dims, reshaped256SimilarType similar parentType dims =
      similar parentType dims) ∧
  (∀ u, reshaped257IndexStyle u = 1) ∧
  (∀ array, reshaped258Parent array = array.parent) ∧
  (∀ size oneto array, reshaped259ParentIndices size oneto array =
      (size array.parent).map oneto) ∧
  (∀ elsize parentType, reshaped260Elsize elsize parentType = elsize parentType) ∧
  (∀ copy array, reshaped262UnaliasCopy copy array =
      ⟨copy array.parent, array.dims, array.mi⟩) ∧
  (∀ ids array, reshaped263DataIds ids array = ids array.parent) ∧
  (∀ alias left right, reshaped265MightAlias alias left right =
      alias left.parent right.parent) ∧
  (∀ alias left right, reshaped267MightAliasSub alias left right = alias left.parent right) ∧
  (∀ alias left right, reshaped268SubMightAlias alias left right = alias left right.parent)

theorem reshapedMetadataCorrect : ReshapedMetadataCorrect := by
  simp [ReshapedMetadataCorrect, reshaped253Size, reshaped254Length,
    reshaped255Similar, reshaped256SimilarType, reshaped257IndexStyle,
    reshaped258Parent, reshaped259ParentIndices, reshaped260Elsize,
    reshaped262UnaliasCopy, reshaped263DataIds, reshaped265MightAlias,
    reshaped267MightAliasSub, reshaped268SubMightAlias]


def ReshapedSimpleRoutesCorrect : Prop :=
  (∀ array value index, reshaped344SetRangeLinear array value index =
      .error .errorException) ∧
  (∀ array value indices, reshaped345SetRangeCartesian array value indices =
      .error .errorException) ∧
  (∀ array value index, reshaped346SetRangeIndex array value index =
      .error .errorException) ∧
  (∀ u, reshaped348SetRangeError u =
      .error .errorException) ∧
  (∀ convert array, reshaped350Cconvert convert array = convert array.parent) ∧
  (∀ convert array, reshaped351UnsafeConvert convert array = convert array.parent) ∧
  (∀ u, reshaped355ViewIndexingSlice u = 1) ∧
  (∀ u, reshaped356ViewIndexingRange u = 1) ∧
  (∀ step stride range, reshaped357ComputeStride step stride range = stride * step range) ∧
  (∀ u, reshaped417ContiguousAbstract u = false) ∧
  (∀ u, reshaped420ContiguousDense u = true) ∧
  (∀ contiguous array, reshaped421ContiguousReshaped contiguous array =
      contiguous array.parent) ∧
  (∀ contiguous parent, reshaped422ContiguousSubarray contiguous parent = contiguous parent) ∧
  (∀ u, reshaped448MergeEmpty u = (1, 1, 0)) ∧
  (∀ size stride, reshaped449MergeOne size stride = (size, stride, 1))

theorem reshapedSimpleRoutesCorrect : ReshapedSimpleRoutesCorrect := by
  simp [ReshapedSimpleRoutesCorrect, reshaped344SetRangeLinear,
    reshaped345SetRangeCartesian, reshaped346SetRangeIndex,
    reshaped348SetRangeError, reshaped350Cconvert, reshaped351UnsafeConvert,
    reshaped355ViewIndexingSlice, reshaped356ViewIndexingRange,
    reshaped357ComputeStride, reshaped417ContiguousAbstract,
    reshaped420ContiguousDense, reshaped421ContiguousReshaped,
    reshaped422ContiguousSubarray, reshaped448MergeEmpty, reshaped449MergeOne]

def ReshapedDelegatesCorrect : Prop :=
  (∀ map reshape f array, reshaped466Map map reshape f array =
      reshape (map f array.parent) array.dims) ∧
  (∀ iterate array, reshaped468Iterate iterate array = iterate array.parent) ∧
  (∀ iterate array state, reshaped469IterateState iterate array state =
      iterate array.parent state) ∧
  (∀ fold f op neutral array, reshaped471Mapfoldl fold f op neutral array =
      fold f op neutral array.parent) ∧
  (∀ fold f op neutral array, reshaped472Mapfoldr fold f op neutral array =
      fold f op neutral array.parent) ∧
  (∀ contains value array, reshaped474In contains value array = contains value array.parent)

theorem reshapedDelegatesCorrect : ReshapedDelegatesCorrect := by
  simp [ReshapedDelegatesCorrect, reshaped466Map, reshaped468Iterate,
    reshaped469IterateState, reshaped471Mapfoldl, reshaped472Mapfoldr, reshaped474In]

end JuliaLean.ArrayCov
