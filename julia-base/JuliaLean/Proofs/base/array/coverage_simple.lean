import JuliaLean.base.array
import JuliaLean.Core

namespace JuliaLean.ArrayCov

/-! Source-faithful models of simple `base/array.jl` methods. -/

def ArrayBasicsCorrect : Prop :=
  (∀ u, array14DimensionMismatch u = "") ∧
  (∀ u, array158Vect u = []) ∧
  (∀ size ndims n, array188AsizeFrom size ndims n =
      if n > ndims then [] else array188AsizeLoop size n (ndims - n + 1).toNat) ∧
  (∀ stored type, array190AllocatedInline stored type = (stored type != 0)) ∧
  (∀ isUnion inline type, array206IsbitsUnion isUnion inline type =
      (isUnion type && inline type)) ∧
  (∀ aligned type, array218ElsizeArray aligned type = aligned type) ∧
  (∀ u, array226ElsizeBottom u = 0) ∧
  (∀ n, array227ElsizeBottomExtra n = .error (.methodError s!"elsize/{n + 1}")) ∧
  (∀ length elsize, array229Sizeof length elsize = length * elsize) ∧
  (∀ message, array321ThrowArgError message = .error (.argumentError message))

theorem arrayBasicsCorrect : ArrayBasicsCorrect := by
  simp [ArrayBasicsCorrect, array14DimensionMismatch, array158Vect,
    array188AsizeFrom, array190AllocatedInline, array206IsbitsUnion,
    array218ElsizeArray, array226ElsizeBottom, array227ElsizeBottomExtra,
    array229Sizeof, array321ThrowArgError]

def ArrayCopyRoutesCorrect : Prop :=
  (∀ toIndex unset assigned i, array208UnsetIndexInteger toIndex unset assigned i =
      (toIndex i).bind (unset assigned)) ∧
  (∀ copyto dest src, array323Copyto2Arg copyto dest src =
      copyto dest 1 src 1 src.length) ∧
  (∀ call dest src, array325CopytoArrayArray call dest src = call dest src) ∧
  (∀ call dest src, array326CopytoArrayMemory call dest src = call dest src) ∧
  (∀ call dest src, array327CopytoMemoryArray call dest src = call dest src) ∧
  (∀ call dest src, array330CopytoSameArray call dest src = call dest src) ∧
  (∀ call dest src, array331CopytoSameArrayMemory call dest src = call dest src) ∧
  (∀ call dest src, array332CopytoSameMemoryArray call dest src = call dest src)

theorem arrayCopyRoutesCorrect : ArrayCopyRoutesCorrect := by
  unfold ArrayCopyRoutesCorrect
  refine ⟨?_, ?_⟩
  · intro toIndex unset assigned i
    rfl
  · simp [array323Copyto2Arg, array325CopytoArrayArray, array326CopytoArrayMemory,
      array327CopytoMemoryArray, array330CopytoSameArray, array331CopytoSameArrayMemory,
      array332CopytoSameMemoryArray]

def ArraySimilarCorrect : Prop :=
  (∀ array a, array414SimilarVector array a = array a.elementType [a.dims.getD 0 0]) ∧
  (∀ array a, array415SimilarMatrix array a =
      array a.elementType [a.dims.getD 0 0, a.dims.getD 1 0]) ∧
  (∀ array a type, array416SimilarVectorType array a type =
      array type [a.dims.getD 0 0]) ∧
  (∀ array a type, array417SimilarMatrixType array a type =
      array type [a.dims.getD 0 0, a.dims.getD 1 0]) ∧
  (∀ array a length, array418SimilarLength array a length = array a.elementType [length]) ∧
  (∀ array a type dims, array419SimilarTypeDims array a type dims = array type dims) ∧
  (∀ array a dims, array420SimilarDims array a dims = array a.elementType dims) ∧
  (∀ similar type dims, array421SimilarArrayType similar type dims = similar type dims)

theorem arraySimilarCorrect : ArraySimilarCorrect := by
  simp [ArraySimilarCorrect, array414SimilarVector, array415SimilarMatrix,
    array416SimilarVectorType, array417SimilarMatrixType, array418SimilarLength,
    array419SimilarTypeDims, array420SimilarDims, array421SimilarArrayType]

end JuliaLean.ArrayCov
