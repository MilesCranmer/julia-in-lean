import JuliaLean.Core

namespace JuliaLean.ArrayCov

structure ReshapedValue where
  parent : List Int
  dims : List Int
  mi : List Int
  deriving Repr, DecidableEq

structure ReshapedIteratorValue where
  iter : List Int
  mi : List Int
  deriving Repr, DecidableEq

inductive ReshapedError where
  | dimensionMismatch
  | errorException
  deriving Repr, DecidableEq

abbrev ReshapedJl (α : Type) := Except ReshapedError α

/-- Outer constructor, `base/reshapedarray.jl:10`. -/
def reshaped10Constructor (parent : List Int) (dims mi : List Int) : ReshapedValue :=
  ⟨parent, dims, mi⟩

/-- Iterator constructor wrapper, `base/reshapedarray.jl:20`. -/
def reshaped20IteratorConstructor
    (parent : ReshapedValue → List Int)
    (rsIterator : List Int → List Int → ReshapedIteratorValue)
    (array : ReshapedValue) : ReshapedIteratorValue :=
  rsIterator (parent array) array.mi

/-- `_rs_iterator`, `base/reshapedarray.jl:21-24`. -/
def reshaped21Iterator (eachIndex : List Int → List Int)
    (parent mi : List Int) : ReshapedIteratorValue :=
  let iter := eachIndex parent
  ⟨iter, mi⟩

/-- Iterator length forwarding, `base/reshapedarray.jl:35`. -/
def reshaped35IteratorLength (length : List Int → Nat)
    (iterator : ReshapedIteratorValue) : Nat := length iterator.iter

/-- Iterator eltype branch, `base/reshapedarray.jl:36`. -/
def reshaped36IteratorEltype (isDefined : Int → Bool) (eltype : Int → Int)
    (iteratorType anyType : Int) : Int :=
  if isDefined iteratorType then eltype iteratorType else anyType

/-- `throw_dmrsa`, `base/reshapedarray.jl:38-39`. -/
def reshaped38ThrowDimensionMismatch (_dims : List Int) (_length : Int) : ReshapedJl Unit :=
  .error .dimensionMismatch

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

/-- `size(A::ReshapedArray)`, `base/reshapedarray.jl:253`. -/
def reshaped253Size (array : ReshapedValue) : List Int := array.dims

/-- `length(A::ReshapedArray)`, `base/reshapedarray.jl:254`. -/
def reshaped254Length (length : List Int → Nat) (array : ReshapedValue) : Nat :=
  length array.parent

/-- `similar(A, eltype, dims)`, `base/reshapedarray.jl:255`. -/
def reshaped255Similar (similar : List Int → Int → List Int → Jl Int)
    (array : ReshapedValue) (elementType : Int) (dims : List Int) : Jl Int :=
  similar array.parent elementType dims

/-- Type-level `similar`, `base/reshapedarray.jl:256`. -/
def reshaped256SimilarType (similar : Int → List Int → Jl Int)
    (parentType : Int) (dims : List Int) : Jl Int := similar parentType dims

/-- Linear index style specialization, `base/reshapedarray.jl:257`. -/
def reshaped257IndexStyle (_ : Unit) : Int := 1

def reshaped258Parent (array : ReshapedValue) : List Int := array.parent

/-- `parentindices`, `base/reshapedarray.jl:259`. -/
def reshaped259ParentIndices (size : List Int → List Int) (oneto : Int → Int)
    (array : ReshapedValue) : List Int :=
  (size array.parent).map oneto

/-- Parent elsize forwarding, `base/reshapedarray.jl:260`. -/
def reshaped260Elsize (elsize : Int → JInt64) (parentType : Int) : JInt64 :=
  elsize parentType

/-- `unaliascopy`, `base/reshapedarray.jl:262`. -/
def reshaped262UnaliasCopy (copy : List Int → List Int)
    (array : ReshapedValue) : ReshapedValue :=
  ⟨copy array.parent, array.dims, array.mi⟩

def reshaped263DataIds (dataids : List Int → List Int)
    (array : ReshapedValue) : List Int := dataids array.parent

def reshaped265MightAlias (mightAlias : List Int → List Int → Bool)
    (left right : ReshapedValue) : Bool := mightAlias left.parent right.parent

def reshaped267MightAliasSub (mightAlias : List Int → List Int → Bool)
    (left : ReshapedValue) (right : List Int) : Bool := mightAlias left.parent right

def reshaped268SubMightAlias (mightAlias : List Int → List Int → Bool)
    (left : List Int) (right : ReshapedValue) : Bool := mightAlias left right.parent

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

/-- `_rs_setindex!_err`, `base/reshapedarray.jl:348`. -/
def reshaped348SetRangeError (_ : Unit) : ReshapedJl Unit :=
  .error .errorException

def reshaped344SetRangeLinear (_array _value _index : Int) : ReshapedJl Unit :=
  reshaped348SetRangeError ()

def reshaped345SetRangeCartesian (_array _value : Int) (_indices : List Int) : ReshapedJl Unit :=
  reshaped348SetRangeError ()

def reshaped346SetRangeIndex (_array _value _parentIndex : Int) : ReshapedJl Unit :=
  reshaped348SetRangeError ()

def reshaped350Cconvert (cconvert : List Int → Int) (array : ReshapedValue) : Int :=
  cconvert array.parent

def reshaped351UnsafeConvert (unsafeConvert : List Int → Int)
    (array : ReshapedValue) : Int := unsafeConvert array.parent

def reshaped355ViewIndexingSlice (_ : Unit) : Int := 1
def reshaped356ViewIndexingRange (_ : Unit) : Int := 1

/-- `compute_stride1`, `base/reshapedarray.jl:357`, with wrapping Int multiplication. -/
def reshaped357ComputeStride (step : Int → JInt64) (stride : JInt64)
    (parentRange : Int) : JInt64 := stride * step parentRange

def reshaped417ContiguousAbstract (_ : Unit) : Bool := false
def reshaped420ContiguousDense (_ : Unit) : Bool := true
def reshaped421ContiguousReshaped (parentContiguous : List Int → Bool)
    (array : ReshapedValue) : Bool := parentContiguous array.parent
def reshaped422ContiguousSubarray (parentContiguous : List Int → Bool)
    (parent : List Int) : Bool := parentContiguous parent

def reshaped448MergeEmpty (_ : Unit) : Int × Int × Int := (1, 1, 0)
def reshaped449MergeOne (size stride : Int) : Int × Int × Int := (size, stride, 1)

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

def reshaped466Map (mapParent : (Int → Int) → List Int → List Int)
    (reshape : List Int → List Int → Jl ReshapedValue)
    (f : Int → Int) (array : ReshapedValue) : Jl ReshapedValue :=
  reshape (mapParent f array.parent) array.dims

def reshaped468Iterate (iterate : List Int → Option (Int × Int))
    (array : ReshapedValue) : Option (Int × Int) := iterate array.parent

def reshaped469IterateState (iterate : List Int → Int → Option (Int × Int))
    (array : ReshapedValue) (state : Int) : Option (Int × Int) :=
  iterate array.parent state

def reshaped471Mapfoldl (mapfold : (Int → Int) → (Int → Int → Int) → Int → List Int → Int)
    (f : Int → Int) (op : Int → Int → Int) (neutral : Int)
    (array : ReshapedValue) : Int := mapfold f op neutral array.parent

def reshaped472Mapfoldr (mapfold : (Int → Int) → (Int → Int → Int) → Int → List Int → Int)
    (f : Int → Int) (op : Int → Int → Int) (neutral : Int)
    (array : ReshapedValue) : Int := mapfold f op neutral array.parent

def reshaped474In (contains : Int → List Int → Bool)
    (value : Int) (array : ReshapedValue) : Bool := contains value array.parent

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
