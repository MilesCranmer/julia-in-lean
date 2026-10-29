import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayConcatFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

inductive CatFailure where
  | argument (message : LazyString)
  | bounds
  | dimensionMismatch (message : LazyString)
  | errorException (message : String)
  | assertion (message : String)
  | callback (id : Nat)
  deriving Repr, DecidableEq

abbrev CResult (α : Type) := Except CatFailure α

def firstOrBounds : List α → CResult α
  | [] => .error .bounds
  | head :: _ => .ok head

def tailOrBounds : List α → CResult (List α)
  | [] => .error .bounds
  | _ :: tail => .ok tail

/-- `cat_size(A::AbstractArray,d)`, line 1839. -/
def m1839 (size : A → IntegerValue → CResult IntegerValue) (array : A)
    (dimension : IntegerValue) : CResult IntegerValue := size array dimension
def P1839 : Prop := ∀ {A : Type} (size : A → IntegerValue → CResult IntegerValue)
    (array : A) dimension,
  m1839 size array dimension = size array dimension
theorem p1839 : P1839 := by unfold P1839; intros; rfl

/-- `cat_indices(A::AbstractArray,d)`, line 1848. -/
def m1848 (axes : A → IntegerValue → CResult R) (array : A)
    (dimension : IntegerValue) : CResult R := axes array dimension
def P1848 : Prop := ∀ {A R : Type} (axes : A → IntegerValue → CResult R)
    (array : A) dimension,
  m1848 axes array dimension = axes array dimension
theorem p1848 : P1848 := by unfold P1848; intros; rfl

/-- Generic tuple-shape `cat_similar`, line 1850. -/
def m1850 (arrayConstructor : T → List IntegerValue → CResult B)
    (_example : A) (elementType : T) (shape : List IntegerValue) : CResult B :=
  arrayConstructor elementType shape
def P1850 : Prop := ∀ {A T B : Type} (arrayConstructor : T → List IntegerValue → CResult B)
    (exemplar : A) elementType shape,
  m1850 arrayConstructor exemplar elementType shape = arrayConstructor elementType shape
theorem p1850 : P1850 := by unfold P1850; intros; rfl

/-- Generic vector-shape `cat_similar`, line 1851. -/
def m1851 (arrayConstructorSplat : T → List IntegerValue → CResult B)
    (_example : A) (elementType : T) (shape : List IntegerValue) : CResult B :=
  arrayConstructorSplat elementType shape
def P1851 : Prop := ∀ {A T B : Type} (constructor : T → List IntegerValue → CResult B)
    (exemplar : A) elementType shape,
  m1851 constructor exemplar elementType shape = constructor elementType shape
theorem p1851 : P1851 := by unfold P1851; intros; rfl

/-- Array-specialized tuple-shape `cat_similar`, line 1852. -/
def m1852 := @m1850
def P1852 : Prop := ∀ {A T B : Type} (constructor : T → List IntegerValue → CResult B)
    (exemplar : A) elementType shape,
  m1852 constructor exemplar elementType shape = m1850 constructor exemplar elementType shape
theorem p1852 : P1852 := by unfold P1852; intros; rfl

/-- Array-specialized vector-shape `cat_similar`, line 1853. -/
def m1853 := @m1851
def P1853 : Prop := ∀ {A T B : Type} (constructor : T → List IntegerValue → CResult B)
    (exemplar : A) elementType shape,
  m1853 constructor exemplar elementType shape = m1851 constructor exemplar elementType shape
theorem p1853 : P1853 := by unfold P1853; intros; rfl

/-- AbstractArray tuple-shape `cat_similar`, line 1854. -/
def m1854 (similar : A → T → List IntegerValue → CResult B)
    (exemplar : A) (elementType : T) (shape : List IntegerValue) : CResult B :=
  similar exemplar elementType shape
def P1854 : Prop := ∀ {A T B : Type} (similar : A → T → List IntegerValue → CResult B)
    (exemplar : A) elementType shape,
  m1854 similar exemplar elementType shape = similar exemplar elementType shape
theorem p1854 : P1854 := by unfold P1854; intros; rfl

/-- AbstractArray splatted vector-shape `cat_similar`, line 1855. -/
def m1855 (similarSplat : A → T → List IntegerValue → CResult B)
    (exemplar : A) (elementType : T) (shape : List IntegerValue) : CResult B :=
  similarSplat exemplar elementType shape
def P1855 : Prop := ∀ {A T B : Type} (similar : A → T → List IntegerValue → CResult B)
    (exemplar : A) elementType shape,
  m1855 similar exemplar elementType shape = similar exemplar elementType shape
theorem p1855 : P1855 := by unfold P1855; intros; rfl

/-- Backward-compatible tuple `cat_shape`, line 1858. -/
def m1858 (_dimensions : D) (shape : List Int) : List Int := shape
def P1858 : Prop := ∀ {D : Type} (dimensions : D) shape, m1858 dimensions shape = shape
theorem p1858 : P1858 := by unfold P1858; intros; rfl

def catShapeLoop (combine : Int → D → List Int → List Int → CResult (List Int))
    (dimensions : D) : List (List Int) → List Int → CResult (List Int)
  | [], output => .ok output
  | shape :: rest, output => do
      let next ← combine 1 dimensions output shape
      catShapeLoop combine dimensions rest next

/-- General `cat_shape`, lines 1859-1865. -/
def m1859 (combine : Int → D → List Int → List Int → CResult (List Int))
    (dimensions : D) (shapes : List (List Int)) : CResult (List Int) :=
  catShapeLoop combine dimensions shapes []
def P1859 : Prop := ∀ {D : Type}
    (combine : Int → D → List Int → List Int → CResult (List Int))
    (dimensions : D) shapes,
  m1859 combine dimensions shapes = catShapeLoop combine dimensions shapes []
theorem p1859 : P1859 := by unfold P1859; intros; rfl

/-- Empty-input `cat_size_shape`, line 1867. -/
def m1867 (dimensions : List Bool) : List Int := List.replicate dimensions.length 0
def P1867 : Prop := ∀ dimensions, m1867 dimensions = List.replicate dimensions.length 0
theorem p1867 : P1867 := by unfold P1867; intros; rfl

/-- Nonempty `cat_size_shape`, line 1868. -/
def m1868 (catSize : X → CResult (List Int))
    (combine : Int → List Bool → List Int → List Int → CResult (List Int))
    (recursive : List Bool → List Int → List X → CResult (List Int))
    (dimensions : List Bool) (head : X) (tail : List X) : CResult (List Int) := do
  let size ← catSize head
  let shape ← combine 1 dimensions [] size
  recursive dimensions shape tail
def P1868 : Prop := ∀ {X : Type} (catSize : X → CResult (List Int))
    (combine : Int → List Bool → List Int → List Int → CResult (List Int))
    (recursive : List Bool → List Int → List X → CResult (List Int))
    dimensions head tail,
  m1868 catSize combine recursive dimensions head tail = do
    let size ← catSize head
    let shape ← combine 1 dimensions [] size
    recursive dimensions shape tail
theorem p1868 : P1868 := by unfold P1868; intros; rfl

/-- Base `_cat_size_shape`, line 1869. -/
def m1869 (_dimensions : D) (shape : S) : S := shape
def P1869 : Prop := ∀ {D S : Type} (dimensions : D) (shape : S), m1869 dimensions shape = shape
theorem p1869 : P1869 := by unfold P1869; intros; rfl

/-- Recursive `_cat_size_shape`, line 1870. -/
def m1870 (catSize : X → CResult (List Int))
    (combine : Int → List Bool → List Int → List Int → CResult (List Int))
    (recursive : List Bool → List Int → List X → CResult (List Int))
    (dimensions : List Bool) (shape : List Int) (head : X) (tail : List X) : CResult (List Int) := do
  let size ← catSize head
  let next ← combine 1 dimensions shape size
  recursive dimensions next tail
def P1870 : Prop := ∀ {X : Type} (catSize : X → CResult (List Int))
    (combine : Int → List Bool → List Int → List Int → CResult (List Int))
    (recursive : List Bool → List Int → List X → CResult (List Int))
    dimensions shape head tail,
  m1870 catSize combine recursive dimensions shape head tail = do
    let size ← catSize head
    let next ← combine 1 dimensions shape size
    recursive dimensions next tail
theorem p1870 : P1870 := by unfold P1870; intros; rfl

def cshp (checkSame : Int → Int → Int → CResult Int) :
    Int → List Bool → List Int → List Int → CResult (List Int)
  | _, [], [], [] => .ok []
  | _, [], [], newShape => .ok newShape
  | _, dimensions, [], [] => .ok (List.replicate dimensions.length 1)
  | dimension, flag :: flags, value :: shape, [] => do
      let rest ← cshp checkSame (dimension + 1) flags shape []
      .ok ((value + if flag then 1 else 0) :: rest)
  | dimension, _ :: flags, [], value :: newShape => do
      let rest ← cshp checkSame (dimension + 1) flags [] newShape
      .ok (value :: rest)
  | dimension, [], value :: shape, [] => do
      let _ ← checkSame dimension value 1
      let rest ← cshp checkSame (dimension + 1) [] shape []
      .ok (1 :: rest)
  | dimension, [], value :: shape, newValue :: newShape => do
      let next ← checkSame dimension value newValue
      let rest ← cshp checkSame (dimension + 1) [] shape newShape
      .ok (next :: rest)
  | dimension, flag :: flags, value :: shape, newValue :: newShape => do
      let next ← if flag then .ok (value + newValue) else checkSame dimension value newValue
      let rest ← cshp checkSame (dimension + 1) flags shape newShape
      .ok (next :: rest)

def m1873 (newShape : List Int) : CResult (List Int) := .ok newShape
def P1873 : Prop := ∀ newShape, m1873 newShape = .ok newShape
theorem p1873 : P1873 := by unfold P1873; intros; rfl

def m1874 (dimensions : List Bool) : CResult (List Int) :=
  .ok (List.replicate dimensions.length 1)
def P1874 : Prop := ∀ dimensions, m1874 dimensions = .ok (List.replicate dimensions.length 1)
theorem p1874 : P1874 := by unfold P1874; intros; rfl

def m1875 (add : Int → Int → CResult Int)
    (recurse : Int → List Bool → List Int → List Int → CResult (List Int))
    (dimension : Int) (dimensions : List Bool) (shape : List Int) : CResult (List Int) := do
  let flag ← firstOrBounds dimensions
  let value ← firstOrBounds shape
  let next ← add value (if flag then 1 else 0)
  let flags ← tailOrBounds dimensions
  let restShape ← tailOrBounds shape
  let rest ← recurse (dimension + 1) flags restShape []
  .ok (next :: rest)
def P1875 : Prop := ∀ add recurse dimension dimensions shape,
  m1875 add recurse dimension dimensions shape = do
    let flag ← firstOrBounds dimensions
    let value ← firstOrBounds shape
    let next ← add value (if flag then 1 else 0)
    let flags ← tailOrBounds dimensions
    let restShape ← tailOrBounds shape
    let rest ← recurse (dimension + 1) flags restShape []
    .ok (next :: rest)
theorem p1875 : P1875 := by unfold P1875; intros; rfl

def m1877 (recurse : Int → List Bool → List Int → List Int → CResult (List Int))
    (dimension : Int) (dimensions : List Bool) (newShape : List Int) : CResult (List Int) := do
  let value ← firstOrBounds newShape
  let flags ← tailOrBounds dimensions
  let restNew ← tailOrBounds newShape
  let rest ← recurse (dimension + 1) flags [] restNew
  .ok (value :: rest)
def P1877 : Prop := ∀ recurse dimension dimensions newShape,
  m1877 recurse dimension dimensions newShape = do
    let value ← firstOrBounds newShape
    let flags ← tailOrBounds dimensions
    let restNew ← tailOrBounds newShape
    let rest ← recurse (dimension + 1) flags [] restNew
    .ok (value :: rest)
theorem p1877 : P1877 := by unfold P1877; intros; rfl

def m1879 (checkSame : Int → Int → Int → CResult Int)
    (recurse : Int → List Bool → List Int → List Int → CResult (List Int))
    (dimension : Int) (shape : List Int) : CResult (List Int) := do
  let value ← firstOrBounds shape
  let _ ← checkSame dimension value 1
  let restShape ← tailOrBounds shape
  let rest ← recurse (dimension + 1) [] restShape []
  .ok (1 :: rest)
def P1879 : Prop := ∀ checkSame recurse dimension shape,
  m1879 checkSame recurse dimension shape = do
    let value ← firstOrBounds shape
    let _ ← checkSame dimension value 1
    let restShape ← tailOrBounds shape
    let rest ← recurse (dimension + 1) [] restShape []
    .ok (1 :: rest)
theorem p1879 : P1879 := by unfold P1879; intros; rfl

def m1883 (checkSame : Int → Int → Int → CResult Int)
    (recurse : Int → List Bool → List Int → List Int → CResult (List Int))
    (dimension : Int) (shape newShape : List Int) : CResult (List Int) := do
  let value ← firstOrBounds shape
  let newValue ← firstOrBounds newShape
  let next ← checkSame dimension value newValue
  let restShape ← tailOrBounds shape
  let restNew ← tailOrBounds newShape
  let rest ← recurse (dimension + 1) [] restShape restNew
  .ok (next :: rest)
def P1883 : Prop := ∀ checkSame recurse dimension shape newShape,
  m1883 checkSame recurse dimension shape newShape = do
    let value ← firstOrBounds shape
    let newValue ← firstOrBounds newShape
    let next ← checkSame dimension value newValue
    let restShape ← tailOrBounds shape
    let restNew ← tailOrBounds newShape
    let rest ← recurse (dimension + 1) [] restShape restNew
    .ok (next :: rest)
theorem p1883 : P1883 := by unfold P1883; intros; rfl

def m1887 (add : Int → Int → CResult Int) (checkSame : Int → Int → Int → CResult Int)
    (recurse : Int → List Bool → List Int → List Int → CResult (List Int))
    (dimension : Int) (dimensions : List Bool) (shape newShape : List Int) : CResult (List Int) := do
  let flag ← firstOrBounds dimensions
  let value ← firstOrBounds shape
  let newValue ← firstOrBounds newShape
  let next ← if flag then add value newValue else checkSame dimension value newValue
  let flags ← tailOrBounds dimensions
  let restShape ← tailOrBounds shape
  let restNew ← tailOrBounds newShape
  let rest ← recurse (dimension + 1) flags restShape restNew
  .ok (next :: rest)
def P1887 : Prop := ∀ add checkSame recurse dimension dimensions shape newShape,
  m1887 add checkSame recurse dimension dimensions shape newShape = do
    let flag ← firstOrBounds dimensions
    let value ← firstOrBounds shape
    let newValue ← firstOrBounds newShape
    let next ← if flag then add value newValue else checkSame dimension value newValue
    let flags ← tailOrBounds dimensions
    let restShape ← tailOrBounds shape
    let restNew ← tailOrBounds newShape
    let rest ← recurse (dimension + 1) flags restShape restNew
    .ok (next :: rest)
theorem p1887 : P1887 := by unfold P1887; intros; rfl

/-- `_cs`, line 1894. -/
def m1894 (dimension left right : Int) : CResult Int :=
  if left = right then .ok left
  else .error (.dimensionMismatch (lazyAppend [.literal "mismatch in dimension ",
    .integer dimension, .literal " (expected ", .integer left,
    .literal " got ", .integer right, .literal ")"]))
def P1894 : Prop := ∀ dimension left right, m1894 dimension left right =
  if left = right then .ok left else .error (.dimensionMismatch (lazyAppend
    [.literal "mismatch in dimension ", .integer dimension,
      .literal " (expected ", .integer left, .literal " got ",
      .integer right, .literal ")"]))
theorem p1894 : P1894 := by unfold P1894; intros; rfl

def maximumInteger : List IntegerValue → CResult Int
  | [] => .error (.argument (.literal "reducing over an empty collection is not allowed"))
  | head :: tail => .ok (tail.foldl (fun best value => max best value.value) head.value)

/-- `dims2cat(dims)`, lines 1898-1903. -/
def m1898 (asAny : List IntegerValue → AnyValue)
    (dimensions : List IntegerValue) : CResult (List Bool) :=
  if dimensions.any (fun dimension => dimension.value ≤ 0) then
    .error (.argument (lazyAppend [.literal "All cat dimensions must be positive integers, but got ",
      .dynamic (asAny dimensions)]))
  else do
    let largest ← maximumInteger dimensions
    .ok ((List.range largest.toNat).map fun index =>
      dimensions.any fun dimension => dimension.value = Int.ofNat index + 1)
def P1898 : Prop := ∀ asAny dimensions, m1898 asAny dimensions =
  if dimensions.any (fun dimension => dimension.value ≤ 0) then
    .error (.argument (lazyAppend [.literal "All cat dimensions must be positive integers, but got ",
      .dynamic (asAny dimensions)]))
  else do
    let largest ← maximumInteger dimensions
    .ok ((List.range largest.toNat).map fun index =>
      dimensions.any fun dimension => dimension.value = Int.ofNat index + 1)
theorem p1898 : P1898 := by unfold P1898; intros; rfl

/-- `dims2cat(::Val)`, line 1897. -/
def m1897 (convert : D → CResult (List IntegerValue))
    (asAny : List IntegerValue → AnyValue) (dimensions : D) : CResult (List Bool) := do
  let values ← convert dimensions
  m1898 asAny values
def P1897 : Prop := ∀ {D : Type} (convert : D → CResult (List IntegerValue))
    asAny (dimensions : D),
  m1897 convert asAny dimensions = do
    let values ← convert dimensions
    m1898 asAny values
theorem p1897 : P1897 := by unfold P1897; intros; rfl

/-- `_cat`, line 1905. -/
def m1905 (promoteEltypeof : List X → CResult T)
    (typedCat : List IntegerValue → T → List X → CResult A)
    (dimensions : List IntegerValue) (values : List X) : CResult A := do
  let elementType ← promoteEltypeof values
  typedCat dimensions elementType values
def P1905 : Prop := ∀ {X T A : Type} (promote : List X → CResult T)
    (typedCat : List IntegerValue → T → List X → CResult A) dimensions values,
  m1905 promote typedCat dimensions values = do
    let elementType ← promote values
    typedCat dimensions elementType values
theorem p1905 : P1905 := by unfold P1905; intros; rfl

/-- `_cat_t`, lines 1907-1915. -/
def m1907 (dims2cat : List IntegerValue → CResult (List Bool))
    (catSizeShape : List Bool → List X → CResult (List Int))
    (catSimilar : X → T → List Int → CResult A) (zero : T → CResult V)
    (fill : A → V → CResult A) (cat : A → List Int → List Bool → List X → CResult A)
    (dimensions : List IntegerValue) (elementType : T) (values : List X) : CResult A := do
  let catDimensions ← dims2cat dimensions
  let shape ← catSizeShape catDimensions values
  let first ← firstOrBounds values
  let allocated ← catSimilar first elementType shape
  let nonzero := (catDimensions.filter id).length
  let initialized ← if 1 < nonzero then do
    let value ← zero elementType
    fill allocated value
  else .ok allocated
  cat initialized shape catDimensions values
def P1907 : Prop := ∀ {X T A V : Type}
    (dims2cat : List IntegerValue → CResult (List Bool))
    (catSizeShape : List Bool → List X → CResult (List Int))
    (catSimilar : X → T → List Int → CResult A) (zero : T → CResult V)
    (fill : A → V → CResult A) (cat : A → List Int → List Bool → List X → CResult A)
    dimensions elementType values,
  m1907 dims2cat catSizeShape catSimilar zero fill cat dimensions elementType values = do
    let catDimensions ← dims2cat dimensions
    let shape ← catSizeShape catDimensions values
    let first ← firstOrBounds values
    let allocated ← catSimilar first elementType shape
    let nonzero := (catDimensions.filter id).length
    let initialized ← if 1 < nonzero then do
      let value ← zero elementType
      fill allocated value
    else .ok allocated
    cat initialized shape catDimensions values
theorem p1907 : P1907 := by unfold P1907; intros; rfl

/-- Keyword-compatible `cat_t`, line 1918. -/
def m1918 (typedCat : D → T → List X → CResult A) (elementType : T)
    (values : List X) (dimensions : D) : CResult A := typedCat dimensions elementType values
def P1918 : Prop := ∀ {D T X A : Type} (typedCat : D → T → List X → CResult A)
    elementType values dimensions,
  m1918 typedCat elementType values dimensions = typedCat dimensions elementType values
theorem p1918 : P1918 := by unfold P1918; intros; rfl

/-- `_typed_vcat_similar`, line 1740. -/
def m1740 (getindex : C → Int → CResult A) (similar : A → T → Int → CResult B)
    (vectors : C) (elementType : T) (count : Int) : CResult B := do
  let first ← getindex vectors 1
  similar first elementType count
def P1740 : Prop := ∀ {C A T B : Type} (getindex : C → Int → CResult A)
    (similar : A → T → Int → CResult B) (vectors : C) elementType count,
  m1740 getindex similar vectors elementType count = do
    let first ← getindex vectors 1
    similar first elementType count
theorem p1740 : P1740 := by unfold P1740; intros; rfl

def sumLengths (getindex : C → Int → CResult A) (length : A → CResult IntegerValue) :
    C → Int → Nat → Int → CResult Int
  | _, _, 0, total => .ok total
  | collection, index, remaining + 1, total => do
      let array ← getindex collection index
      let count ← length array
      sumLengths getindex length collection (index + 1) remaining (total + count.value)

/-- `_typed_vcat`, line 1741. -/
def m1741 (sumMappedLengths : C → CResult Int)
    (allocate : C → T → Int → CResult B) (fill : B → C → CResult B)
    (elementType : T) (vectors : C) : CResult B := do
  let total ← sumMappedLengths vectors
  let dest ← allocate vectors elementType total
  fill dest vectors
def P1741 : Prop := ∀ {C T B : Type} (sumMappedLengths : C → CResult Int)
    (allocate : C → T → Int → CResult B) (fill : B → C → CResult B)
    elementType vectors,
  m1741 sumMappedLengths allocate fill elementType vectors = do
    let total ← sumMappedLengths vectors
    let dest ← allocate vectors elementType total
    fill dest vectors
theorem p1741 : P1741 := by unfold P1741; intros; rfl

def vcatFillLoop (getindex : C → Int → CResult A) (length : A → CResult IntegerValue)
    (assign : B → Int → Int → A → CResult B) :
    B → C → Int → Nat → Int → CResult B
  | dest, _, _, 0, _ => .ok dest
  | dest, vectors, index, remaining + 1, position => do
      let vector ← getindex vectors index
      let vectorLength ← length vector
      let final := position + vectorLength.value - 1
      let next ← assign dest position final vector
      vcatFillLoop getindex length assign next vectors (index + 1) remaining (final + 1)

/-- `_typed_vcat!`, lines 1744-1753. -/
def m1744 (collectionLength : C → CResult IntegerValue) (toInt : IntegerValue → CResult Int)
    (getindex : C → Int → CResult A) (length : A → CResult IntegerValue)
    (assign : B → Int → Int → A → CResult B) (dest : B) (vectors : C) : CResult B := do
  let rawCount ← collectionLength vectors
  let count ← toInt rawCount
  vcatFillLoop getindex length assign dest vectors 1 count.toNat 1
def P1744 : Prop := ∀ {C A B : Type} (collectionLength : C → CResult IntegerValue)
    (toInt : IntegerValue → CResult Int) (getindex : C → Int → CResult A)
    (length : A → CResult IntegerValue) (assign : B → Int → Int → A → CResult B)
    dest vectors,
  m1744 collectionLength toInt getindex length assign dest vectors = do
    let rawCount ← collectionLength vectors
    let count ← toInt rawCount
    vcatFillLoop getindex length assign dest vectors 1 count.toNat 1
theorem p1744 : P1744 := by unfold P1744; intros; rfl

/-- Ambiguous `typed_hcat`, line 1759. -/
def m1759 : CResult A := .error (.argument (.literal
  "It is unclear whether you intend to perform an indexing operation or typed concatenation. If you intend to perform indexing (v[1 + 2]), adjust spacing or insert missing operator to clarify. If you intend to perform typed concatenation (T[1 2]), ensure that T is a type."))
def P1759 : Prop := ∀ (A : Type), (m1759 : CResult A) = .error (.argument (.literal
  "It is unclear whether you intend to perform an indexing operation or typed concatenation. If you intend to perform indexing (v[1 + 2]), adjust spacing or insert missing operator to clarify. If you intend to perform typed concatenation (T[1 2]), ensure that T is a type."))
theorem p1759 : P1759 := by unfold P1759; intros; rfl

structure HcatState where
  columns : Int
  dense : Bool
  deriving Repr, DecidableEq

def scanHcat (getindex : C → Int → CResult A) (size : A → Int → CResult Int)
    (ndims : A → CResult Int) (isArray : A → Bool)
    (allRows : C → CResult AnyValue) (expectedRows : Int) :
    C → Int → Nat → HcatState → CResult HcatState
  | _, _, 0, state => .ok state
  | arrays, index, remaining + 1, state => do
      let array ← getindex arrays index
      let rows ← size array 1
      if rows != expectedRows then
        let rowsValue ← allRows arrays
        .error (.dimensionMismatch (lazyAppend [.literal "number of rows of each array must match (got ",
          .dynamic rowsValue, .literal ")"]))
      else
        let rank ← ndims array
        let width ← if rank = 2 then size array 2 else .ok 1
        scanHcat getindex size ndims isArray allRows expectedRows arrays (index + 1) remaining
          ⟨state.columns + width, state.dense && isArray array⟩

def fillHcatDense (getindex : C → Int → CResult A) (length : A → CResult Int)
    (copy : B → Int → A → Int → Int → CResult B) :
    B → C → Int → Nat → Int → CResult B
  | dest, _, _, 0, _ => .ok dest
  | dest, arrays, index, remaining + 1, position => do
      let array ← getindex arrays index
      let count ← length array
      let next ← copy dest position array 1 count
      fillHcatDense getindex length copy next arrays (index + 1) remaining (position + count)

def fillHcatSlices (getindex : C → Int → CResult A) (size : A → Int → CResult Int)
    (isMatrix : A → Bool) (assign : B → Int → Int → A → CResult B) :
    B → C → Int → Nat → Int → CResult B
  | dest, _, _, 0, _ => .ok dest
  | dest, arrays, index, remaining + 1, position => do
      let array ← getindex arrays index
      let width ← if isMatrix array then size array 2 else .ok 1
      let final := position + width - 1
      let next ← assign dest position final array
      fillHcatSlices getindex size isMatrix assign next arrays (index + 1) remaining (final + 1)

/-- `_typed_hcat`, lines 1768-1800. -/
def m1768 (collectionLength : C → CResult Nat) (getindex : C → Int → CResult A)
    (size : A → Int → CResult Int) (ndims : A → CResult Int) (isArray isMatrix : A → Bool)
    (allRows : C → CResult AnyValue) (similar : A → T → Int → Int → CResult B)
    (length : A → CResult Int) (copy : B → Int → A → Int → Int → CResult B)
    (assign : B → Int → Int → A → CResult B) (elementType : T) (arrays : C) : CResult B := do
  let count ← collectionLength arrays
  let first ← getindex arrays 1
  let rows ← size first 1
  let state ← scanHcat getindex size ndims isArray allRows rows arrays 1 count ⟨0, true⟩
  let dest ← similar first elementType rows state.columns
  if state.dense then fillHcatDense getindex length copy dest arrays 1 count 1
  else fillHcatSlices getindex size isMatrix assign dest arrays 1 count 1
def P1768 : Prop := ∀ {C A T B : Type} (collectionLength : C → CResult Nat)
    (getindex : C → Int → CResult A) (size : A → Int → CResult Int)
    (ndims : A → CResult Int) (isArray isMatrix : A → Bool)
    (allRows : C → CResult AnyValue) (similar : A → T → Int → Int → CResult B)
    (length : A → CResult Int) (copy : B → Int → A → Int → Int → CResult B)
    (assign : B → Int → Int → A → CResult B) elementType arrays,
  m1768 collectionLength getindex size ndims isArray isMatrix allRows similar length copy assign
    elementType arrays = do
    let count ← collectionLength arrays
    let first ← getindex arrays 1
    let rows ← size first 1
    let state ← scanHcat getindex size ndims isArray allRows rows arrays 1 count ⟨0, true⟩
    let dest ← similar first elementType rows state.columns
    if state.dense then fillHcatDense getindex length copy dest arrays 1 count 1
    else fillHcatSlices getindex size isMatrix assign dest arrays 1 count 1
theorem p1768 : P1768 := by unfold P1768; intros; rfl

def scanVcatColumns (getindex : C → Int → CResult A) (size : A → Int → CResult Int)
    (allColumns : C → CResult AnyValue) (expected : Int) : C → Int → Nat → CResult Unit
  | _, _, 0 => .ok ()
  | arrays, index, remaining + 1 => do
      let array ← getindex arrays index
      let columns ← size array 2
      if columns != expected then
        let values ← allColumns arrays
        .error (.dimensionMismatch (lazyAppend [.literal "number of columns of each array must match (got ",
          .dynamic values, .literal ")"]))
      else scanVcatColumns getindex size allColumns expected arrays (index + 1) remaining

def sumRows (getindex : C → Int → CResult A) (size : A → Int → CResult Int) :
    C → Int → Nat → Int → CResult Int
  | _, _, 0, total => .ok total
  | arrays, index, remaining + 1, total => do
      let array ← getindex arrays index
      let rows ← size array 1
      sumRows getindex size arrays (index + 1) remaining (total + rows)

def fillVcat (getindex : C → Int → CResult A) (size : A → Int → CResult Int)
    (assign : B → Int → Int → A → CResult B) : B → C → Int → Nat → Int → CResult B
  | dest, _, _, 0, _ => .ok dest
  | dest, arrays, index, remaining + 1, position => do
      let array ← getindex arrays index
      let rows ← size array 1
      let final := position + rows - 1
      let next ← assign dest position final array
      fillVcat getindex size assign next arrays (index + 1) remaining (final + 1)

/-- `_typed_vcat` for vectors or matrices, lines 1805-1823. -/
def m1805 (collectionLength : C → CResult Nat) (getindex : C → Int → CResult A)
    (size : A → Int → CResult Int) (allColumns : C → CResult AnyValue)
    (similar : A → T → Int → Int → CResult B) (assign : B → Int → Int → A → CResult B)
    (elementType : T) (arrays : C) : CResult B := do
  let count ← collectionLength arrays
  let totalRows ← sumRows getindex size arrays 1 count 0
  let first ← getindex arrays 1
  let columns ← size first 2
  scanVcatColumns getindex size allColumns columns arrays 2 (count - 1)
  let dest ← similar first elementType totalRows columns
  fillVcat getindex size assign dest arrays 1 count 1
def P1805 : Prop := ∀ {C A T B : Type} (collectionLength : C → CResult Nat)
    (getindex : C → Int → CResult A) (size : A → Int → CResult Int)
    (allColumns : C → CResult AnyValue) (similar : A → T → Int → Int → CResult B)
    (assign : B → Int → Int → A → CResult B) elementType arrays,
  m1805 collectionLength getindex size allColumns similar assign elementType arrays = do
    let count ← collectionLength arrays
    let totalRows ← sumRows getindex size arrays 1 count 0
    let first ← getindex arrays 1
    let columns ← size first 2
    scanVcatColumns getindex size allColumns columns arrays 2 (count - 1)
    let dest ← similar first elementType totalRows columns
    fillVcat getindex size assign dest arrays 1 count 1
theorem p1805 : P1805 := by unfold P1805; intros; rfl

/-- `__cat`, line 1921. -/
def m1921 (offsetCopy : A → List Int → List Bool → List Int → List X → CResult A)
    (dest : A) (shape : List Int) (catDimensions : List Bool) (values : List X) : CResult A :=
  offsetCopy dest shape catDimensions (List.replicate shape.length 0) values
def P1921 : Prop := ∀ {A X : Type}
    (offsetCopy : A → List Int → List Bool → List Int → List X → CResult A)
    (dest : A) shape catDimensions values,
  m1921 offsetCopy dest shape catDimensions values =
    offsetCopy dest shape catDimensions (List.replicate shape.length 0) values
theorem p1921 : P1921 := by unfold P1921; intros; rfl

/-- Recursive `__cat_offset!`, lines 1923-1927. -/
def m1923 (copyOne : A → List Int → List Bool → List Int → X → CResult (A × List Int))
    (recursive : A → List Int → List Bool → List Int → List X → CResult A)
    (dest : A) (shape : List Int) (catDimensions : List Bool) (offsets : List Int)
    (head : X) (tail : List X) : CResult A := do
  let next ← copyOne dest shape catDimensions offsets head
  recursive next.1 shape catDimensions next.2 tail
def P1923 : Prop := ∀ {A X : Type}
    (copyOne : A → List Int → List Bool → List Int → X → CResult (A × List Int))
    (recursive : A → List Int → List Bool → List Int → List X → CResult A)
    (dest : A) shape catDimensions offsets head tail,
  m1923 copyOne recursive dest shape catDimensions offsets head tail = do
    let next ← copyOne dest shape catDimensions offsets head
    recursive next.1 shape catDimensions next.2 tail
theorem p1923 : P1923 := by unfold P1923; intros; rfl

def catIndexLoop (catIndices : X → IntegerValue → CResult R)
    (offsetIndices : Int → R → CResult R) :
    X → List Int → List Bool → List Int → Nat → Nat → CResult (List (Sum (List Int) R))
  | _, _, _, _, _, 0 => .ok []
  | value, shape, dimensions, offsets, index, remaining + 1 => do
      let current ←
        if index < dimensions.length && dimensions.getD index false then do
          let axis ← catIndices value ⟨Int.ofNat index + 1⟩
          let shifted ← offsetIndices (offsets.getD index 0) axis
          .ok (Sum.inr shifted)
        else .ok (Sum.inl [1, shape.getD index 0])
      let rest ← catIndexLoop catIndices offsetIndices value shape dimensions offsets
        (index + 1) remaining
      .ok (current :: rest)

def catOffsetLoop (add : Int → Int → CResult Int)
    (catSize : X → IntegerValue → CResult Int) :
    X → List Bool → List Int → Nat → Nat → CResult (List Int)
  | _, _, _, _, 0 => .ok []
  | value, dimensions, offsets, index, remaining + 1 => do
      let current ←
        if index < dimensions.length && dimensions.getD index false then do
          let size ← catSize value ⟨Int.ofNat index + 1⟩
          add (offsets.getD index 0) size
        else .ok (offsets.getD index 0)
      let rest ← catOffsetLoop add catSize value dimensions offsets (index + 1) remaining
      .ok (current :: rest)

/-- `__cat_offset1!`, lines 1930-1941. -/
def m1930 (catIndices : X → IntegerValue → CResult R)
    (offsetIndices : Int → R → CResult R)
    (copyOrFill : A → List (Sum (List Int) R) → X → CResult A)
    (add : Int → Int → CResult Int) (catSize : X → IntegerValue → CResult Int)
    (dest : A) (shape : List Int) (catDimensions : List Bool)
    (offsets : List Int) (value : X) : CResult (A × List Int) := do
  let indices ← catIndexLoop catIndices offsetIndices value shape catDimensions offsets 0 offsets.length
  let updated ← copyOrFill dest indices value
  let next ← catOffsetLoop add catSize value catDimensions offsets 0 offsets.length
  .ok (updated, next)
def P1930 : Prop := ∀ {X R A : Type} (catIndices : X → IntegerValue → CResult R)
    (offsetIndices : Int → R → CResult R)
    (copyOrFill : A → List (Sum (List Int) R) → X → CResult A)
    (add : Int → Int → CResult Int) (catSize : X → IntegerValue → CResult Int)
    (dest : A) shape catDimensions offsets value,
  m1930 catIndices offsetIndices copyOrFill add catSize dest shape catDimensions offsets value = do
    let indices ← catIndexLoop catIndices offsetIndices value shape catDimensions offsets 0 offsets.length
    let updated ← copyOrFill dest indices value
    let next ← catOffsetLoop add catSize value catDimensions offsets 0 offsets.length
    .ok (updated, next)
theorem p1930 : P1930 := by unfold P1930; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-concat-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.AbstractArrayConcatFaithful
