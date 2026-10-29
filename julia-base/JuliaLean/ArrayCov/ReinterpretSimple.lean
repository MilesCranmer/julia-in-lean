import JuliaLean.Core

namespace JuliaLean.ArrayCov

structure ReinterpretValue where
  parent : List Int
  deriving Repr, DecidableEq

def reinterpret104Identity (array : List Int) : List Int := array
def reinterpret145ReshapeIdentity (array : List Int) : List Int := array

def reinterpret190Nested (reinterpretCall : Int → List Int → Jl ReinterpretValue)
    (type : Int) (array : ReinterpretValue) : Jl ReinterpretValue :=
  reinterpretCall type array.parent

def reinterpret191NestedReshape
    (reinterpretCall : Bool → Int → List Int → Jl ReinterpretValue)
    (construct : Int → ReinterpretValue → Jl ReinterpretValue)
    (targetSize sourceSize parentSize : Nat)
    (type : Int) (array : ReinterpretValue) : Jl ReinterpretValue :=
  if targetSize = sourceSize ∨ targetSize = parentSize ∨ sourceSize = parentSize then
    reinterpretCall true type array.parent
  else construct type array

def reinterpret204Strides (size : ReinterpretValue → List JInt64)
    (sizeToStrides : JInt64 → List JInt64 → List JInt64)
    (array : ReinterpretValue) : List JInt64 :=
  sizeToStrides (JInt.lit .i64 1) (size array)

def reinterpret229Contiguous (parentContiguous : List Int → Bool)
    (array : ReinterpretValue) : Bool := parentContiguous array.parent

def reinterpret231Similar (similar : List Int → Int → List Int → Jl Int)
    (array : ReinterpretValue) (type : Int) (dims : List Int) : Jl Int :=
  similar array.parent type dims

def reinterpret232SimilarType (similar : Int → List Int → Jl Int)
    (parentType : Int) (dims : List Int) : Jl Int := similar parentType dims

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

structure SCartesianIndexModel where
  i : JInt64
  j : JInt64
  deriving Repr, DecidableEq

structure SCartesianIndicesModel where
  k : JInt64
  indices2 : List JInt64
  deriving Repr, DecidableEq

def reinterpret270CombineStyle (k : JInt64) : JInt64 := k
def reinterpret276ToIndex (index : SCartesianIndexModel) : SCartesianIndexModel := index

def reinterpret277NextIndex (k : JInt64) (index : SCartesianIndexModel) : SCartesianIndexModel :=
  if index.i < k then ⟨index.i + JInt.lit .i64 1, index.j⟩
  else ⟨JInt.lit .i64 1, index.j + JInt.lit .i64 1⟩

def reinterpret279PrevIndex (k : JInt64) (index : SCartesianIndexModel) : SCartesianIndexModel :=
  if JInt.lit .i64 1 < index.i then ⟨index.i - JInt.lit .i64 1, index.j⟩
  else ⟨k, index.j - JInt.lit .i64 1⟩

inductive ReinterpretSimpleError where
  | assertionError
  deriving Repr, DecidableEq

abbrev ReinterpretSimpleJl (α : Type) := Except ReinterpretSimpleError α

def reinterpret285IndicesConstructor (k : JInt64) (indices : List JInt64) :
    ReinterpretSimpleJl SCartesianIndicesModel :=
  if JInt.lit .i64 1 < k then .ok ⟨k, indices⟩ else .error .assertionError

def reinterpret287EachIndex (eachIndex : Int → List Int → List JInt64)
    (construct : JInt64 → List JInt64 → ReinterpretSimpleJl SCartesianIndicesModel)
    (k : JInt64) (array : ReinterpretValue) : ReinterpretSimpleJl SCartesianIndicesModel :=
  construct k (eachIndex 1 array.parent)

def reinterpret295IndicesSize (iter : SCartesianIndicesModel) : JInt64 × JInt64 :=
  (iter.k, JInt.lit .i64 iter.indices2.length)

def reinterpret296IndicesAxes (oneTo : JInt64 → List JInt64)
    (iter : SCartesianIndicesModel) : List JInt64 × List JInt64 :=
  (oneTo iter.k, iter.indices2)

def reinterpret298IndicesFirst (first : List JInt64 → JInt64)
    (iter : SCartesianIndicesModel) : SCartesianIndexModel :=
  ⟨JInt.lit .i64 1, first iter.indices2⟩

def reinterpret299IndicesLast (last : List JInt64 → JInt64)
    (iter : SCartesianIndicesModel) : SCartesianIndexModel :=
  ⟨iter.k, last iter.indices2⟩

def reinterpret324SimdOuter (iter : SCartesianIndicesModel) : List JInt64 := iter.indices2
def reinterpret325SimdLength (iter : SCartesianIndicesModel) (_ : Int) : JInt64 := iter.k

def reinterpret326SimdIndex (_k last i1 : JInt64) : SCartesianIndexModel :=
  ⟨i1 + JInt.lit .i64 1, last⟩

def reinterpret330MaybeReshapeFallback
    (fallback : Int → ReinterpretValue → List Int → ReinterpretValue)
    (array : ReinterpretValue) (indices : List Int) : ReinterpretValue :=
  fallback 0 array indices

def reinterpret331MaybeReshapeIdentity (array : ReinterpretValue) (_indices : List Int) : ReinterpretValue :=
  array

def reinterpret362EachIndex (each : Int → ReinterpretValue → List Int)
    (style : Int) (parent : ReinterpretValue → ReinterpretValue)
    (array : ReinterpretValue) : List Int :=
  each style (parent array)

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

def reinterpret366Parent (array : ReinterpretValue) : List Int := array.parent
def reinterpret367DataIds (dataids : List Int → List Int)
    (array : ReinterpretValue) : List Int := dataids array.parent

def reinterpret368Unalias (copy : List Int → List Int)
    (reinterpretCall : Int → List Int → Jl ReinterpretValue)
    (type : Int) (array : ReinterpretValue) : Jl ReinterpretValue :=
  reinterpretCall type (copy array.parent)

def reinterpret369UnaliasReshape (copy : List Int → List Int)
    (reinterpretCall : Bool → Int → List Int → Jl ReinterpretValue)
    (type : Int) (array : ReinterpretValue) : Jl ReinterpretValue :=
  reinterpretCall true type (copy array.parent)

def reinterpret382SizeZero (_ : ReinterpretValue) : List Int := []
def reinterpret396AxesZero (_ : ReinterpretValue) : List Int := []
def reinterpret398HasOffset (hasOffset : List Int → Bool)
    (array : ReinterpretValue) : Bool := hasOffset array.parent

def reinterpret407Cconvert (cconvert : Int → List Int → Int)
    (sourceType : Int) (array : ReinterpretValue) : Int :=
  cconvert sourceType array.parent

structure PointerModel where
  targetType : Int
  address : Int
  deriving Repr, DecidableEq

def reinterpret408UnsafeConvert (unsafeConvert : Int → List Int → Int)
    (sourceType targetType : Int) (array : ReinterpretValue) : PointerModel :=
  ⟨targetType, unsafeConvert sourceType array.parent⟩

def reinterpret422CheckPtrReshaped (check : ReinterpretValue → Bool)
    (parent : ReinterpretValue → ReinterpretValue) (array : ReinterpretValue) : Bool :=
  check (parent array)

def reinterpret423CheckPtrSubarray (check : ReinterpretValue → Bool)
    (parent : ReinterpretValue → ReinterpretValue) (array : ReinterpretValue) : Bool :=
  check (parent array)

def reinterpret424CheckPtrDense (_ : ReinterpretValue) : Bool := true
def reinterpret425CheckPtrAbstract (_ : ReinterpretValue) : Bool := false

def reinterpret427GetZero (firstIndex : ReinterpretValue → Int)
    (getindex : ReinterpretValue → Int → Jl Int) (array : ReinterpretValue) : Jl Int :=
  getindex array (firstIndex array)

def reinterpret429IsAssigned (checkbounds : ReinterpretValue → List Int → Bool)
    (ptrIndexable : ReinterpretValue → Bool)
    (assignedRa : ReinterpretValue → List Int → Bool)
    (array : ReinterpretValue) (indices : List Int) : Bool :=
  checkbounds array indices && (ptrIndexable array || assignedRa array indices)

def reinterpret430IsAssignedCartesian (isassigned : List Int → JInt64 → Bool)
    (array : ReinterpretValue) (index : SCartesianIndexModel) : Bool :=
  isassigned array.parent index.j

def reinterpret431AssignedRa (_array : ReinterpretValue) (_indices : List Int) : Bool := true

def reinterpret577SetZero (firstIndex : ReinterpretValue → Int)
    (setindex : ReinterpretValue → Int → Int → Jl ReinterpretValue)
    (array : ReinterpretValue) (value : Int) : Jl ReinterpretValue :=
  setindex array value (firstIndex array)

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

end JuliaLean.ArrayCov
