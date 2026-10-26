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

def m1875 (recurse : Int → List Bool → List Int → List Int → CResult (List Int))
    (dimension : Int) (dimensions : List Bool) (shape : List Int) : CResult (List Int) := do
  let flag ← firstOrBounds dimensions
  let value ← firstOrBounds shape
  let flags ← tailOrBounds dimensions
  let restShape ← tailOrBounds shape
  let rest ← recurse (dimension + 1) flags restShape []
  .ok ((value + if flag then 1 else 0) :: rest)
def P1875 : Prop := ∀ recurse dimension dimensions shape,
  m1875 recurse dimension dimensions shape = do
    let flag ← firstOrBounds dimensions
    let value ← firstOrBounds shape
    let flags ← tailOrBounds dimensions
    let restShape ← tailOrBounds shape
    let rest ← recurse (dimension + 1) flags restShape []
    .ok ((value + if flag then 1 else 0) :: rest)
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

def m1887 (checkSame : Int → Int → Int → CResult Int)
    (recurse : Int → List Bool → List Int → List Int → CResult (List Int))
    (dimension : Int) (dimensions : List Bool) (shape newShape : List Int) : CResult (List Int) := do
  let flag ← firstOrBounds dimensions
  let value ← firstOrBounds shape
  let newValue ← firstOrBounds newShape
  let next ← if flag then .ok (value + newValue) else checkSame dimension value newValue
  let flags ← tailOrBounds dimensions
  let restShape ← tailOrBounds shape
  let restNew ← tailOrBounds newShape
  let rest ← recurse (dimension + 1) flags restShape restNew
  .ok (next :: rest)
def P1887 : Prop := ∀ checkSame recurse dimension dimensions shape newShape,
  m1887 checkSame recurse dimension dimensions shape newShape = do
    let flag ← firstOrBounds dimensions
    let value ← firstOrBounds shape
    let newValue ← firstOrBounds newShape
    let next ← if flag then .ok (value + newValue) else checkSame dimension value newValue
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
    .dynamic ⟨0, dimension.natAbs⟩, .literal " (expected ", .dynamic ⟨0, left.natAbs⟩,
    .literal " got ", .dynamic ⟨0, right.natAbs⟩, .literal ")"]))
def P1894 : Prop := ∀ dimension left right, m1894 dimension left right =
  if left = right then .ok left else .error (.dimensionMismatch (lazyAppend
    [.literal "mismatch in dimension ", .dynamic ⟨0, dimension.natAbs⟩,
      .literal " (expected ", .dynamic ⟨0, left.natAbs⟩, .literal " got ",
      .dynamic ⟨0, right.natAbs⟩, .literal ")"]))
theorem p1894 : P1894 := by unfold P1894; intros; rfl

def maximumInteger : List IntegerValue → CResult Int
  | [] => .error (.argument (.literal "reducing over an empty collection is not allowed"))
  | head :: tail => .ok (tail.foldl (fun best value => max best value.value) head.value)

/-- `dims2cat(dims)`, lines 1898-1903. -/
def m1898 (dimensions : List IntegerValue) : CResult (List Bool) :=
  if dimensions.any (fun dimension => dimension.value ≤ 0) then
    .error (.argument (lazyAppend [.literal "All cat dimensions must be positive integers, but got ",
      .dynamic ⟨0, dimensions.length⟩]))
  else do
    let largest ← maximumInteger dimensions
    .ok ((List.range largest.toNat).map fun index =>
      dimensions.any fun dimension => dimension.value = Int.ofNat index + 1)
def P1898 : Prop := ∀ dimensions, m1898 dimensions =
  if dimensions.any (fun dimension => dimension.value ≤ 0) then
    .error (.argument (lazyAppend [.literal "All cat dimensions must be positive integers, but got ",
      .dynamic ⟨0, dimensions.length⟩]))
  else do
    let largest ← maximumInteger dimensions
    .ok ((List.range largest.toNat).map fun index =>
      dimensions.any fun dimension => dimension.value = Int.ofNat index + 1)
theorem p1898 : P1898 := by unfold P1898; intros; rfl

/-- `dims2cat(::Val)`, line 1897. -/
def m1897 (convert : D → CResult (List IntegerValue)) (dimensions : D) : CResult (List Bool) := do
  let values ← convert dimensions
  m1898 values
def P1897 : Prop := ∀ {D : Type} (convert : D → CResult (List IntegerValue))
    (dimensions : D),
  m1897 convert dimensions = do
    let values ← convert dimensions
    m1898 values
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
  m1907 dims2cat catSizeShape catSimilar zero fill cat dimensions elementType values =
  m1907 dims2cat catSizeShape catSimilar zero fill cat dimensions elementType values
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
def m1741 (collectionLength : C → CResult Nat) (getindex : C → Int → CResult A)
    (length : A → CResult IntegerValue) (allocate : C → T → Int → CResult B)
    (fill : B → C → CResult B) (elementType : T) (vectors : C) : CResult B := do
  let count ← collectionLength vectors
  let total ← sumLengths getindex length vectors 1 count 0
  let dest ← allocate vectors elementType total
  fill dest vectors
def P1741 : Prop := ∀ {C A T B : Type} (collectionLength : C → CResult Nat)
    (getindex : C → Int → CResult A) (length : A → CResult IntegerValue)
    (allocate : C → T → Int → CResult B) (fill : B → C → CResult B)
    elementType vectors,
  m1741 collectionLength getindex length allocate fill elementType vectors =
  m1741 collectionLength getindex length allocate fill elementType vectors
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
    elementType arrays =
  m1768 collectionLength getindex size ndims isArray isMatrix allRows similar length copy assign
    elementType arrays
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
  m1805 collectionLength getindex size allColumns similar assign elementType arrays =
  m1805 collectionLength getindex size allColumns similar assign elementType arrays
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
def m1923 (copyOne : A → List Int → List Bool → List Int → X → CResult (List Int))
    (recursive : A → List Int → List Bool → List Int → List X → CResult A)
    (dest : A) (shape : List Int) (catDimensions : List Bool) (offsets : List Int)
    (head : X) (tail : List X) : CResult A := do
  let next ← copyOne dest shape catDimensions offsets head
  recursive dest shape catDimensions next tail
def P1923 : Prop := ∀ {A X : Type}
    (copyOne : A → List Int → List Bool → List Int → X → CResult (List Int))
    (recursive : A → List Int → List Bool → List Int → List X → CResult A)
    (dest : A) shape catDimensions offsets head tail,
  m1923 copyOne recursive dest shape catDimensions offsets head tail = do
    let next ← copyOne dest shape catDimensions offsets head
    recursive dest shape catDimensions next tail
theorem p1923 : P1923 := by unfold P1923; intros; rfl

def catIndexLoop (catIndices : X → IntegerValue → CResult R) :
    X → List Int → List Bool → List Int → Nat → Nat → CResult (List (Sum (List Int) R))
  | _, _, _, _, _, 0 => .ok []
  | value, shape, dimensions, offsets, index, remaining + 1 => do
      let rest ← catIndexLoop catIndices value shape dimensions offsets (index + 1) remaining
      if index < dimensions.length && dimensions.getD index false then
        let axis ← catIndices value ⟨Int.ofNat index + 1⟩
        .ok (Sum.inr axis :: rest)
      else .ok (Sum.inl [1, shape.getD index 0] :: rest)

def catOffsetLoop (catSize : X → IntegerValue → CResult Int) :
    X → List Bool → List Int → Nat → Nat → CResult (List Int)
  | _, _, _, _, 0 => .ok []
  | value, dimensions, offsets, index, remaining + 1 => do
      let rest ← catOffsetLoop catSize value dimensions offsets (index + 1) remaining
      if index < dimensions.length && dimensions.getD index false then
        let size ← catSize value ⟨Int.ofNat index + 1⟩
        .ok ((offsets.getD index 0 + size) :: rest)
      else .ok (offsets.getD index 0 :: rest)

/-- `__cat_offset1!`, lines 1930-1941. -/
def m1930 (catIndices : X → IntegerValue → CResult R)
    (copyOrFill : A → List (Sum (List Int) R) → X → CResult A)
    (catSize : X → IntegerValue → CResult Int) (dest : A) (shape : List Int)
    (catDimensions : List Bool) (offsets : List Int) (value : X) : CResult (List Int) := do
  let indices ← catIndexLoop catIndices value shape catDimensions offsets 0 offsets.length
  let _ ← copyOrFill dest indices value
  catOffsetLoop catSize value catDimensions offsets 0 offsets.length
def P1930 : Prop := ∀ {X R A : Type} (catIndices : X → IntegerValue → CResult R)
    (copyOrFill : A → List (Sum (List Int) R) → X → CResult A)
    (catSize : X → IntegerValue → CResult Int) (dest : A) shape catDimensions offsets value,
  m1930 catIndices copyOrFill catSize dest shape catDimensions offsets value = do
    let indices ← catIndexLoop catIndices value shape catDimensions offsets 0 offsets.length
    let _ ← copyOrFill dest indices value
    catOffsetLoop catSize value catDimensions offsets 0 offsets.length
theorem p1930 : P1930 := by unfold P1930; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-concat-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 1740 "_typed_vcat_similar" "Allocation indexes V[1] before calling similar, including BoundsError on empty collections." "base/abstractarray.jl:1740" ``P1740 ``p1740,
  entry 1741 "_typed_vcat" "Typed vector concatenation reads every component length, indexes V[1] during allocation, then fills." "base/abstractarray.jl:1741-1742" ``P1741 ``p1741,
  entry 1744 "_typed_vcat!" "The fill loop converts collection length to Int, indexes every vector, converts lengths, assigns each slice, and preserves mutation order." "base/abstractarray.jl:1744-1753" ``P1744 ``p1744,
  entry 1759 "typed_hcat(AbstractArray,...)" "Ambiguous typed concatenation throws ArgumentError with the complete documented diagnostic." "base/abstractarray.jl:1759-1763" ``P1759 ``p1759,
  entry 1768 "_typed_hcat" "Horizontal concatenation scans actual arrays, validates rows, tracks density and widths, allocates from A[1], then performs the selected mutation loop." "base/abstractarray.jl:1768-1800" ``P1768 ``p1768,
  entry 1805 "_typed_vcat" "Vertical concatenation sums actual rows, indexes A[1], validates remaining columns, allocates, and assigns row slices in order." "base/abstractarray.jl:1805-1823" ``P1805 ``p1805,
  entry 1839 "cat_size(AbstractArray,d)" "Array cat_size forwards every Integer representation to size." "base/abstractarray.jl:1839" ``P1839 ``p1839,
  entry 1848 "cat_indices(AbstractArray,d)" "Array cat_indices forwards every Integer representation to axes." "base/abstractarray.jl:1848" ``P1848 ``p1848,
  entry 1850 "cat_similar(tuple)" "Generic tuple-shape allocation calls Array with the element type and complete shape." "base/abstractarray.jl:1850" ``P1850 ``p1850,
  entry 1851 "cat_similar(vector)" "Generic vector-shape allocation splats the complete shape into Array." "base/abstractarray.jl:1851" ``P1851 ``p1851,
  entry 1852 "cat_similar(Array,tuple)" "Array tuple-shape allocation calls the concrete Array constructor." "base/abstractarray.jl:1852" ``P1852 ``p1852,
  entry 1853 "cat_similar(Array,vector)" "Array vector-shape allocation splats into the concrete Array constructor." "base/abstractarray.jl:1853" ``P1853 ``p1853,
  entry 1854 "cat_similar(AbstractArray,tuple)" "AbstractArray tuple-shape allocation calls similar on the actual exemplar." "base/abstractarray.jl:1854" ``P1854 ``p1854,
  entry 1855 "cat_similar(AbstractArray,vector)" "AbstractArray vector-shape allocation splats into similar on the actual exemplar." "base/abstractarray.jl:1855" ``P1855 ``p1855,
  entry 1858 "cat_shape(Int tuple)" "The compatibility overload returns the complete Int shape unchanged for arbitrary dimensions." "base/abstractarray.jl:1858" ``P1858 ``p1858,
  entry 1859 "cat_shape(shape tuple)" "General cat_shape folds every shape through _cshp in source order." "base/abstractarray.jl:1859-1865" ``P1859 ``p1859,
  entry 1867 "cat_size_shape(dims)" "Empty-input size-shape returns one zero for every cat dimension." "base/abstractarray.jl:1867" ``P1867 ``p1867,
  entry 1868 "cat_size_shape(dims,X,tail)" "Nonempty size-shape calls cat_size, _cshp, then recursive accumulation." "base/abstractarray.jl:1868" ``P1868 ``p1868,
  entry 1869 "_cat_size_shape base" "The base helper returns its accumulated shape." "base/abstractarray.jl:1869" ``P1869 ``p1869,
  entry 1870 "_cat_size_shape recursive" "The recursive helper calls cat_size and _cshp before its tail call." "base/abstractarray.jl:1870" ``P1870 ``p1870,
  entry 1873 "_cshp empty dimensions and shape" "The empty-dimensions empty-shape overload returns the new shape." "base/abstractarray.jl:1873" ``P1873 ``p1873,
  entry 1874 "_cshp dimensions only" "Dimensions with two empty shapes produce one for each dimension." "base/abstractarray.jl:1874" ``P1874 ``p1874,
  entry 1875 "_cshp old shape only" "The old-shape overload indexes heads and tails, adds the dimension flag, and recurses." "base/abstractarray.jl:1875" ``P1875 ``p1875,
  entry 1877 "_cshp new shape only" "The new-shape overload indexes heads and tails and recurses." "base/abstractarray.jl:1877" ``P1877 ``p1877,
  entry 1879 "_cshp trailing old shape" "A trailing old dimension validates equality with one before recursion." "base/abstractarray.jl:1879-1881" ``P1879 ``p1879,
  entry 1883 "_cshp trailing paired shapes" "Trailing paired dimensions call _cs before recursion." "base/abstractarray.jl:1883-1885" ``P1883 ``p1883,
  entry 1887 "_cshp paired shapes" "Paired dimensions sum on cat axes or call _cs, then recurse on every tail." "base/abstractarray.jl:1887-1892" ``P1887 ``p1887,
  entry 1894 "_cs" "Shape agreement returns the shared size or throws DimensionMismatch with the exact values." "base/abstractarray.jl:1894-1895" ``P1894 ``p1894,
  entry 1897 "dims2cat(Val)" "Val dimensions preserve every Integer representation when delegating to dims2cat." "base/abstractarray.jl:1897" ``P1897 ``p1897,
  entry 1898 "dims2cat" "Dimension conversion validates positivity, handles empty maximum, and constructs membership flags." "base/abstractarray.jl:1898-1903" ``P1898 ``p1898,
  entry 1905 "_cat" "Untyped concatenation promotes element types before calling _cat_t with every Integer dimension." "base/abstractarray.jl:1905" ``P1905 ``p1905,
  entry 1907 "_cat_t" "Typed concatenation computes dimensions and shape, indexes X[1], allocates, conditionally fills, then copies." "base/abstractarray.jl:1907-1915" ``P1907 ``p1907,
  entry 1918 "cat_t" "The compatibility wrapper forwards arbitrary dims, type, and values to _cat_t." "base/abstractarray.jl:1918" ``P1918 ``p1918
  , entry 1921 "__cat" "Concatenation constructs zero offsets with the output rank before calling __cat_offset!." "base/abstractarray.jl:1921" ``P1921 ``p1921
  , entry 1923 "__cat_offset!" "The recursive copier processes the head, receives new offsets, then recurses on the tail." "base/abstractarray.jl:1923-1927" ``P1923 ``p1923
  , entry 1930 "__cat_offset1!" "Single-item copying constructs every dimension index, mutates the destination, then computes every new offset." "base/abstractarray.jl:1930-1941" ``P1930 ``p1930
]

end JuliaLean.MultidimCov.AbstractArrayConcatFaithful
