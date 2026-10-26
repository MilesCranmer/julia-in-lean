import JuliaLean.Core
import JuliaLean.ArrayCov.Simple

namespace JuliaLean.ArrayCov

inductive DimArg where
  | integer (value : Int)
  | oneTo (last : Int)
  deriving Repr, DecidableEq

/-- `to_dim(d::Integer)`, `base/array.jl:482`. -/
def array482ToDimInteger (d : Int) : Int := d

/-- `to_dim(d::OneTo)`, `base/array.jl:483`. -/
def array483ToDimOneTo (last : Int) : Int := last

def dimArgValue : DimArg → Int
  | .integer value => array482ToDimInteger value
  | .oneTo last => array483ToDimOneTo last

/-- Vararg `fill`, `base/array.jl:583`. -/
def array583FillVarargs (fillTuple : Int → List DimArg → Jl ArrayShape)
    (value : Int) (dims : List DimArg) : Jl ArrayShape :=
  fillTuple value dims

/-- Union-dimension tuple `fill`, `base/array.jl:584`. -/
def array584FillMapped (fillInts : Int → List Int → Jl ArrayShape)
    (value : Int) (dims : List DimArg) : Jl ArrayShape :=
  fillInts value (dims.map dimArgValue)

/-- Integer-dimension `fill`, `base/array.jl:585`: allocate, fill, return. -/
def array585FillInteger (allocate : Int → List Int → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape)
    (value type : Int) (dims : List Int) : Jl ArrayShape := do
  let array ← allocate type dims
  fillBang array value

/-- General-dimension `fill`, `base/array.jl:586`: similar, fill, return. -/
def array586FillDimArgs (similar : Int → List DimArg → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape)
    (value type : Int) (dims : List DimArg) : Jl ArrayShape := do
  let array ← similar type dims
  fillBang array value

/-- Zero-dimensional `fill`, `base/array.jl:587`. -/
def array587FillZero (allocate : Int → List Int → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape)
    (value type : Int) : Jl ArrayShape := do
  let array ← allocate type []
  fillBang array value

/-- Generated `zeros`/`ones` vararg wrapper, `base/array.jl:633`. -/
def array633FilledVarargs (call : List DimArg → Jl ArrayShape)
    (dims : List DimArg) : Jl ArrayShape := call dims

/-- Generated typed vararg wrapper, `base/array.jl:634`. -/
def array634FilledTypedVarargs (call : Int → List DimArg → Jl ArrayShape)
    (type : Int) (dims : List DimArg) : Jl ArrayShape := call type dims

/-- Generated default-Float64 tuple wrapper, `base/array.jl:635`. -/
def array635FilledDefaultTuple (call : Int → List DimArg → Jl ArrayShape)
    (float64 : Int) (dims : List DimArg) : Jl ArrayShape := call float64 dims

/-- Generated typed mapped-dimension wrapper, `base/array.jl:636`. -/
def array636FilledMapped (call : Int → List Int → Jl ArrayShape)
    (type : Int) (dims : List DimArg) : Jl ArrayShape :=
  call type (dims.map dimArgValue)

/-- Generated integer-dimension body, `base/array.jl:637-641`. -/
def array637FilledInteger (allocate : Int → List Int → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape) (felt : Int → Int)
    (type : Int) (dims : List Int) : Jl ArrayShape := do
  let array ← allocate type dims
  fillBang array (felt type)

/-- Generated zero-dimensional body, `base/array.jl:642-646`. -/
def array642FilledZero (allocate : Int → List Int → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape) (felt : Int → Int)
    (type : Int) : Jl ArrayShape := do
  let array ← allocate type []
  fillBang array (felt type)

/-- Generated general-dimension body, `base/array.jl:647-651`. -/
def array647FilledDimArgs (similar : Int → List DimArg → Jl ArrayShape)
    (fillBang : ArrayShape → Int → Jl ArrayShape) (felt : Int → Int)
    (type : Int) (dims : List DimArg) : Jl ArrayShape := do
  let array ← similar type dims
  fillBang array (felt type)

def ArrayFillConstructorsCorrect : Prop :=
  (∀ d, array482ToDimInteger d = d) ∧
  (∀ last, array483ToDimOneTo last = last) ∧
  (∀ call value dims, array583FillVarargs call value dims = call value dims) ∧
  (∀ call value dims, array584FillMapped call value dims =
      call value (dims.map dimArgValue)) ∧
  (∀ allocate fill value type dims, array585FillInteger allocate fill value type dims = do
      let array ← allocate type dims; fill array value) ∧
  (∀ similar fill value type dims, array586FillDimArgs similar fill value type dims = do
      let array ← similar type dims; fill array value) ∧
  (∀ allocate fill value type, array587FillZero allocate fill value type = do
      let array ← allocate type []; fill array value) ∧
  (∀ call dims, array633FilledVarargs call dims = call dims) ∧
  (∀ call type dims, array634FilledTypedVarargs call type dims = call type dims) ∧
  (∀ call float64 dims, array635FilledDefaultTuple call float64 dims = call float64 dims) ∧
  (∀ call type dims, array636FilledMapped call type dims =
      call type (dims.map dimArgValue)) ∧
  (∀ allocate fill felt type dims, array637FilledInteger allocate fill felt type dims = do
      let array ← allocate type dims; fill array (felt type)) ∧
  (∀ allocate fill felt type, array642FilledZero allocate fill felt type = do
      let array ← allocate type []; fill array (felt type)) ∧
  (∀ similar fill felt type dims, array647FilledDimArgs similar fill felt type dims = do
      let array ← similar type dims; fill array (felt type))

theorem arrayFillConstructorsCorrect : ArrayFillConstructorsCorrect := by
  simp [ArrayFillConstructorsCorrect, array482ToDimInteger, array483ToDimOneTo,
    array583FillVarargs, array584FillMapped, array585FillInteger, array586FillDimArgs,
    array587FillZero, array633FilledVarargs, array634FilledTypedVarargs,
    array635FilledDefaultTuple, array636FilledMapped, array637FilledInteger,
    array642FilledZero, array647FilledDimArgs]

/-- `convert(::Type{T}, a::AbstractArray)`, `base/array.jl:657`. -/
def array657Convert (isType : List Int → Bool) (construct : List Int → Jl (List Int))
    (array : List Int) : Jl (List Int) :=
  if isType array then .ok array else construct array

/-- `promote_rule(::Type{Array}, ::Type{Array})`, `base/array.jl:659`. -/
def array659PromoteRule (promoteType : Int → Int → Int)
    (elSame : Int → Int → Int → Int) (left right leftArray rightArray : Int) : Int :=
  elSame (promoteType left right) leftArray rightArray

/-- Concrete Array conversion constructor, `base/array.jl:664`. -/
def array664ArrayConstructor (size : List Int → List Int)
    (allocate : List Int → Jl (List Int))
    (copyAxes : List Int → List Int → Jl (List Int)) (source : List Int) : Jl (List Int) := do
  let dest ← allocate (size source)
  copyAxes dest source

/-- AbstractArray conversion constructor, `base/array.jl:665`. -/
def array665AbstractConstructor (similar : List Int → Jl (List Int))
    (copyAxes : List Int → List Int → Jl (List Int)) (source : List Int) : Jl (List Int) := do
  let dest ← similar source
  copyAxes dest source

def ArrayConversionConstructorsCorrect : Prop :=
  (∀ isType construct array, array657Convert isType construct array =
      if isType array then .ok array else construct array) ∧
  (∀ promote same left right a b, array659PromoteRule promote same left right a b =
      same (promote left right) a b) ∧
  (∀ size allocate copy source, array664ArrayConstructor size allocate copy source = do
      let dest ← allocate (size source); copy dest source) ∧
  (∀ similar copy source, array665AbstractConstructor similar copy source = do
      let dest ← similar source; copy dest source)

theorem arrayConversionConstructorsCorrect : ArrayConversionConstructorsCorrect := by
  simp [ArrayConversionConstructorsCorrect, array657Convert, array659PromoteRule,
    array664ArrayConstructor, array665AbstractConstructor]

inductive IteratorSizeModel where
  | unknown | hasLength | hasShape
  deriving Repr, DecidableEq

/-- `collect(T, itr)`, `base/array.jl:684`. -/
def array684Collect (iteratorSize : List Int → IteratorSizeModel)
    (collectInner : List Int → IteratorSizeModel → Jl (List Int))
    (iterator : List Int) : Jl (List Int) :=
  collectInner iterator (iteratorSize iterator)

/-- Sized `_collect`, `base/array.jl:686-687`. -/
def array686CollectSized (similarShape : List Int → IteratorSizeModel → Int)
    (arrayFor : IteratorSizeModel → Int → Jl (List Int))
    (copyto : List Int → List Int → Jl (List Int))
    (iterator : List Int) (size : IteratorSizeModel) : Jl (List Int) := do
  let dest ← arrayFor size (similarShape iterator size)
  copyto dest iterator

def array688PushAll (push : List Int → Int → Jl (List Int)) :
    List Int → List Int → Jl (List Int)
  | dest, [] => .ok dest
  | dest, value :: rest => do
      let dest ← push dest value
      array688PushAll push dest rest

/-- Unknown-size `_collect`, `base/array.jl:688-694`. -/
def array688CollectUnknown (push : List Int → Int → Jl (List Int))
    (iterator : List Int) : Jl (List Int) :=
  array688PushAll push [] iterator

/-- Generic `_similar_for`, `base/array.jl:697`. -/
def array697SimilarFor (similar : Int → Int → Jl Int)
    (container type : Int) : Jl Int :=
  similar container type

def array699SimilarShapeUnknown (_iterator : List Int) : Option Int := none
def array700SimilarShapeLength (iterator : List Int) : Int := iterator.length
def array701SimilarShapeAxes (axes : List Int → Int) (iterator : List Int) : Int := axes iterator

def array703SimilarForUnknown (similar : Int → Int → Int → Jl Int)
    (container type : Int) : Jl Int := similar container type 0

def array705SimilarForLength (similar : Int → Int → Int → Jl Int)
    (container type length : Int) : Jl Int := similar container type length

def array707SimilarForShape (similar : Int → Int → Int → Jl Int)
    (container type axes : Int) : Jl Int := similar container type axes

def array711ArrayForUnknown (allocate : Int → Int → Jl Int) (type : Int) : Jl Int :=
  allocate type 0

def array712ArrayForLength (allocate : Int → Int → Jl Int)
    (type length : Int) : Jl Int := allocate type length

def array713ArrayForShape (similar : Int → Int → Jl Int)
    (type axes : Int) : Jl Int := similar type axes

def array716ArrayFor (similarShape : List Int → IteratorSizeModel → Int)
    (arrayFor : IteratorSizeModel → Int → Jl Int)
    (iterator : List Int) (size : IteratorSizeModel) : Jl Int :=
  arrayFor size (similarShape iterator size)

def ArrayTypedCollectCorrect : Prop :=
  (∀ size collect iterator, array684Collect size collect iterator =
      collect iterator (size iterator)) ∧
  (∀ shape allocate copy iterator size, array686CollectSized shape allocate copy iterator size = do
      let dest ← allocate size (shape iterator size); copy dest iterator) ∧
  (∀ push iterator, array688CollectUnknown push iterator = array688PushAll push [] iterator) ∧
  (∀ similar container type, array697SimilarFor similar container type =
      similar container type) ∧
  (∀ iterator, array699SimilarShapeUnknown iterator = none) ∧
  (∀ iterator, array700SimilarShapeLength iterator = iterator.length) ∧
  (∀ axes iterator, array701SimilarShapeAxes axes iterator = axes iterator) ∧
  (∀ similar container type, array703SimilarForUnknown similar container type =
      similar container type 0) ∧
  (∀ similar container type length, array705SimilarForLength similar container type length =
      similar container type length) ∧
  (∀ similar container type axes, array707SimilarForShape similar container type axes =
      similar container type axes) ∧
  (∀ allocate type, array711ArrayForUnknown allocate type = allocate type 0) ∧
  (∀ allocate type length, array712ArrayForLength allocate type length = allocate type length) ∧
  (∀ similar type axes, array713ArrayForShape similar type axes = similar type axes) ∧
  (∀ shape allocate iterator size, array716ArrayFor shape allocate iterator size =
      allocate size (shape iterator size))

theorem arrayTypedCollectCorrect : ArrayTypedCollectCorrect := by
  simp [ArrayTypedCollectCorrect, array684Collect, array686CollectSized,
    array688CollectUnknown, array697SimilarFor, array699SimilarShapeUnknown,
    array700SimilarShapeLength, array701SimilarShapeAxes, array703SimilarForUnknown,
    array705SimilarForLength, array707SimilarForShape, array711ArrayForUnknown,
    array712ArrayForLength, array713ArrayForShape, array716ArrayFor]

end JuliaLean.ArrayCov
