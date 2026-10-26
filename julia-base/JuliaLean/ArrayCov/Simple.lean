import JuliaLean.Core

namespace JuliaLean.ArrayCov

/-! Source-faithful models of simple `base/array.jl` methods. -/

structure ArrayShape where
  elementType : Int
  dims : List Int
  deriving Repr, DecidableEq

/-- `DimensionMismatch()`, `base/array.jl:14`. -/
def array14DimensionMismatch (_ : Unit) : String := ""

/-- `vect()`, `base/array.jl:158`. -/
def array158Vect (_ : Unit) : List Int := []

/-- The recursive calls made by `asize_from`. -/
def array188AsizeLoop (size : Int → Int) : Int → Nat → List Int
  | _, 0 => []
  | n, fuel + 1 => size n :: array188AsizeLoop size (n + 1) fuel

/-- `asize_from(a, n)`, `base/array.jl:188`, including nonpositive `n`. -/
def array188AsizeFrom (size : Int → Int) (ndims n : Int) : List Int :=
  if n > ndims then []
  else array188AsizeLoop size n (ndims - n + 1).toNat

/-- `allocatedinline(T)`, `base/array.jl:190`. -/
def array190AllocatedInline (storedInline : Int → Int) (type : Int) : Bool :=
  storedInline type != 0

/-- `isbitsunion(u)`, `base/array.jl:206`. -/
def array206IsbitsUnion (isUnion : Int → Bool) (allocatedInline : Int → Bool)
    (type : Int) : Bool :=
  isUnion type && allocatedInline type

/-- The integer-index wrapper of `unsetindex!`, `base/array.jl:208`. -/
def array208UnsetIndexInteger (toIndex : Int → Jl Int)
    (unsetIndex : List Bool → Int → Jl (List Bool))
    (assigned : List Bool) (i : Int) : Jl (List Bool) := do
  let index ← toIndex i
  unsetIndex assigned index

/-- `elsize(::Type{Array})`, `base/array.jl:218`. -/
def array218ElsizeArray (alignedSizeof : Int → JInt64) (elementType : Int) : JInt64 :=
  alignedSizeof elementType

/-- `elsize(::Type{Union{}})`, `base/array.jl:226`. -/
def array226ElsizeBottom (_ : Unit) : Nat := 0

/-- The slurping bottom-type `elsize` method, `base/array.jl:227`. -/
def array227ElsizeBottomExtra (argumentCount : Nat) : Jl Nat :=
  .error (.methodError s!"elsize/{argumentCount + 1}")

/-- `sizeof(a::Array)`, `base/array.jl:229`; multiplication is wrapping `Int`. -/
def array229Sizeof (length elsize : JInt64) : JInt64 := length * elsize

/-- `_throw_argerror(s)`, `base/array.jl:321`. -/
def array321ThrowArgError (message : String) : Jl Unit :=
  .error (.argumentError message)

/-- `_copyto2arg!(dest, src)`, `base/array.jl:323`. -/
def array323Copyto2Arg
    (copyto : List Int → Int → List Int → Int → Nat → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto dest 1 src 1 src.length

/-- `copyto!(::Array, ::Array)`, `base/array.jl:325`. -/
def array325CopytoArrayArray
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- `copyto!(::Array, ::Memory)`, `base/array.jl:326`. -/
def array326CopytoArrayMemory
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- `copyto!(::Memory, ::Array)`, `base/array.jl:327`. -/
def array327CopytoMemoryArray
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- Same-element `copyto!(::Array, ::Array)`, `base/array.jl:330`. -/
def array330CopytoSameArray
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- Same-element `copyto!(::Array, ::Memory)`, `base/array.jl:331`. -/
def array331CopytoSameArrayMemory
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- Same-element `copyto!(::Memory, ::Array)`, `base/array.jl:332`. -/
def array332CopytoSameMemoryArray
    (copyto2 : List Int → List Int → Jl (List Int))
    (dest src : List Int) : Jl (List Int) :=
  copyto2 dest src

/-- `similar(a::Vector{T})`, `base/array.jl:414`. -/
def array414SimilarVector (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) : Jl ArrayShape :=
  array a.elementType [a.dims.getD 0 0]

/-- `similar(a::Matrix{T})`, `base/array.jl:415`. -/
def array415SimilarMatrix (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) : Jl ArrayShape :=
  array a.elementType [a.dims.getD 0 0, a.dims.getD 1 0]

/-- `similar(a::Vector{T}, S)`, `base/array.jl:416`. -/
def array416SimilarVectorType (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) (newType : Int) : Jl ArrayShape :=
  array newType [a.dims.getD 0 0]

/-- `similar(a::Matrix{T}, S)`, `base/array.jl:417`. -/
def array417SimilarMatrixType (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) (newType : Int) : Jl ArrayShape :=
  array newType [a.dims.getD 0 0, a.dims.getD 1 0]

/-- `similar(a::Array{T}, m)`, `base/array.jl:418`. -/
def array418SimilarLength (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) (length : Int) : Jl ArrayShape :=
  array a.elementType [length]

/-- `similar(a::Array, T, dims)`, `base/array.jl:419`. -/
def array419SimilarTypeDims (array : Int → List Int → Jl ArrayShape)
    (_a : ArrayShape) (newType : Int) (dims : List Int) : Jl ArrayShape :=
  array newType dims

/-- `similar(a::Array{T}, dims)`, `base/array.jl:420`. -/
def array420SimilarDims (array : Int → List Int → Jl ArrayShape)
    (a : ArrayShape) (dims : List Int) : Jl ArrayShape :=
  array a.elementType dims

/-- `similar(::Type{Array{T,N}}, dims)`, `base/array.jl:421`. -/
def array421SimilarArrayType (similarArray : Int → List Int → Jl ArrayShape)
    (elementType : Int) (dims : List Int) : Jl ArrayShape :=
  similarArray elementType dims

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
