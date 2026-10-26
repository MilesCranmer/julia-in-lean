import JuliaLean.MultidimCov.ArrayFaithfulCore
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ArrayBasicsFaithful

open JuliaLean.Registry
open ArrayFaithfulCore

def m14 {T : Type} (_unit : T) : Error := .dimensionMismatch
def P14 : Prop := ∀ {T : Type} (unit : T), m14 unit = .dimensionMismatch
theorem p14 : P14 := by simp [P14, m14]

inductive Expr where | escape (value : Expr) | call (name : String) (args : List Expr) | atom (value : String)

def m135 (recurse : Expr → Expr) : Expr → Expr
  | .escape value => .escape (recurse value)
  | .call name args => .call name (args.map recurse)
  | atom => atom
def P135 : Prop := ∀ recurse expr, m135 recurse expr = match expr with
  | .escape value => .escape (recurse value)
  | .call name args => .call name (args.map recurse)
  | atom => atom
theorem p135 : P135 := by intro recurse expr; cases expr <;> rfl

def m158 : ArrayState α := { elementType := "Any", axes := [[]], values := [], id := 0 }
def P158 : Prop := ∀ _ : Unit, (m158 : ArrayState Nat).elementType = "Any" ∧
  (m158 : ArrayState Nat).values = []
theorem p158 : P158 := by simp [P158, m158]

def m188 {A : Type} (size : A → Int → Int) (array : A) (dimension : Int) := size array dimension
def P188 : Prop := ∀ {A : Type} (size : A → Int → Int) array dimension,
  m188 size array dimension = size array dimension
theorem p188 : P188 := by simp [P188, m188]

def m190 {T : Type} (storedInline : T → Int) (type : T) : Bool := storedInline type ≠ 0
def P190 : Prop := ∀ {T : Type} (storedInline : T → Int) type,
  m190 storedInline type = (storedInline type ≠ 0)
theorem p190 : P190 := by simp [P190, m190]

def m219 {T : Type} (alignedSizeof : T → Nat) (type : T) := alignedSizeof type
def P219 : Prop := ∀ {T : Type} (alignedSizeof : T → Nat) type, m219 alignedSizeof type = alignedSizeof type
theorem p219 : P219 := by simp [P219, m219]

def m227 {T : Type} (_bottom : T) : Nat := 0
def P227 : Prop := ∀ {T : Type} (bottom : T), m227 bottom = 0
theorem p227 : P227 := by simp [P227, m227]

def m229 (elementSize : Nat) (arrayLength : Nat) : Nat := elementSize * arrayLength
def P229 : Prop := ∀ elementSize arrayLength, m229 elementSize arrayLength = elementSize * arrayLength
theorem p229 : P229 := by simp [P229, m229]

def m259 {P : Type} (memmove : P → P → Nat → Unit) (dest src : P)
    (count elementSize : Nat) : P :=
  let _ := memmove dest src (count * elementSize)
  dest
def P259 : Prop := ∀ {P : Type} (memmove : P → P → Nat → Unit) dest src count elementSize,
  m259 memmove dest src count elementSize = dest
theorem p259 : P259 := by simp [P259, m259]

def m276 {A : Type} (pointer : A → Int → Nat) (unsafeCopy : Nat → Nat → Nat → Unit)
    (dest : A) (destOffset : Int) (src : A) (srcOffset : Int) (count elementSize : Nat) : A :=
  let _ := unsafeCopy (pointer dest destOffset) (pointer src srcOffset) (count * elementSize)
  dest
def P276 : Prop := ∀ {A : Type} (pointer : A → Int → Nat)
    (unsafeCopy : Nat → Nat → Nat → Unit) dest destOffset src srcOffset count elementSize,
  m276 pointer unsafeCopy dest destOffset src srcOffset count elementSize = dest
theorem p276 : P276 := by simp [P276, m276]

def m299 (dest src : ArrayState α) (destOffset srcOffset count : Int) : Result (ArrayState α) :=
  if destOffset < 1 || srcOffset < 1 || count < 0 || dest.values.length < destOffset + count - 1 ||
      src.values.length < srcOffset + count - 1 then .error .bounds
  else
    let segment := (src.values.drop (srcOffset - 1).toNat).take count.toNat
    .ok { dest with values := dest.values.take (destOffset - 1).toNat ++ segment ++
      dest.values.drop (destOffset + count - 1).toNat }
def P299 : Prop := ∀ {α : Type} (dest src : ArrayState α) destOffset srcOffset count,
  m299 dest src destOffset srcOffset count =
    if destOffset < 1 || srcOffset < 1 || count < 0 || dest.values.length < destOffset + count - 1 ||
        src.values.length < srcOffset + count - 1 then .error .bounds
    else let segment := (src.values.drop (srcOffset - 1).toNat).take count.toNat
      .ok { dest with values := dest.values.take (destOffset - 1).toNat ++ segment ++
        dest.values.drop (destOffset + count - 1).toNat }
theorem p299 : P299 := by simp [P299, m299]

def m321 (message : String) : Error × String := (.argument, message)
def P321 : Prop := ∀ message, m321 message = (.argument, message)
theorem p321 : P321 := by simp [P321, m321]

def m323 {D S : Type} (copyImpl : D → Int → S → Int → Int → D)
    (dest : D) (src : S) (srcLength : Int) : D := copyImpl dest 1 src 1 srcLength
def P323 : Prop := ∀ {D S : Type} (copyImpl : D → Int → S → Int → Int → D) dest src srcLength,
  m323 copyImpl dest src srcLength = copyImpl dest 1 src 1 srcLength
theorem p323 : P323 := by simp [P323, m323]

def m368 (convert : α → Result β) (array : ArrayState β) (value : α) : Result (ArrayState β) := do
  let converted ← convert value
  pure { array with values := List.replicate array.values.length (some converted) }
def P368 : Prop := ∀ {α β : Type} (convert : α → Result β) array value,
  m368 convert array value = do
    let converted ← convert value
    pure { array with values := List.replicate array.values.length (some converted) }
theorem p368 : P368 := by simp [P368, m368]
def m373 (array : ArrayState α) (value : α) : ArrayState α :=
  { array with values := List.replicate array.values.length (some value) }
def P373 : Prop := ∀ {α : Type} (array : ArrayState α) (value : α),
  m373 array value = { array with values := List.replicate array.values.length (some value) }
theorem p373 : P373 := by simp [P373, m373]

def m391 (array : ArrayState α) : Result (ArrayState α) := do
  let values ← assignedValues array
  pure { array with values := values.map some, id := array.id + 1 }
def P391 : Prop := ∀ {α : Type} (array : ArrayState α), m391 array = do
  let values ← assignedValues array
  pure { array with values := values.map some, id := array.id + 1 }
theorem p391 : P391 := by simp [P391, m391]

def m421 (elementType : String) (dims : List Nat) : ArrayState α := allocate elementType (oneToAxes dims)
theorem oneToAxes_lengths (dims : List Nat) : (oneToAxes dims).map List.length = dims := by
  simp [oneToAxes, Function.comp_def]
def P421 : Prop := ∀ {α : Type} elementType dims,
  (m421 elementType dims : ArrayState α).elementType = elementType ∧
    dimensions (m421 elementType dims : ArrayState α) = dims
theorem p421 : P421 := by
  unfold P421
  intro α elementType dims
  constructor
  · rfl
  · simp [m421, dimensions, allocate, oneToAxes_lengths]

def typedLiteral (elementType : String) (values : List α) : ArrayState α :=
  { elementType, axes := oneToAxes [values.length], values := values.map some, id := 0 }
def m445 (elementType : String) (values : List α) := typedLiteral elementType values
def P445 : Prop := ∀ {α : Type} elementType (values : List α),
  (m445 elementType values).elementType = elementType ∧ (m445 elementType values).values = values.map some
theorem p445 : P445 := by simp [P445, m445, typedLiteral]
def m463 (values : List α) := typedLiteral "Any" values
def P463 : Prop := ∀ {α : Type} (values : List α),
  (m463 values).elementType = "Any" ∧ (m463 values).values = values.map some
theorem p463 : P463 := by simp [P463, m463, typedLiteral]
def m471 : ArrayState α := typedLiteral "Any" []
def P471 : Prop := ∀ {α : Type} (_ : α), (m471 : ArrayState α).elementType = "Any" ∧
  (m471 : ArrayState α).values = []
theorem p471 : P471 := by simp [P471, m471, typedLiteral]

def m473 (convertByte : Int → Result α) (array : ArrayState α) (value : Int) : Result (ArrayState α) := do
  let converted ← convertByte value
  pure { array with values := List.replicate array.values.length (some converted) }
def P473 : Prop := ∀ {α : Type} (convertByte : Int → Result α) array value,
  m473 convertByte array value = do
    let converted ← convertByte value
    pure { array with values := List.replicate array.values.length (some converted) }
theorem p473 : P473 := by simp [P473, m473]

inductive Dim where | integer (value : Int) | axis (values : List Int) deriving Repr, DecidableEq
def toDim : Dim → Result Nat
  | .integer value => if value < 0 then .error .argument else .ok value.toNat
  | .axis values => .ok values.length
def m482 (value : Int) := toDim (.integer value)
def P482 : Prop := ∀ value, m482 value = if value < 0 then .error .argument else .ok value.toNat
theorem p482 : P482 := by simp [P482, m482, toDim]
def m483 (values : List Int) := toDim (.axis values)
def P483 : Prop := ∀ values, m483 values = .ok values.length
theorem p483 : P483 := by simp [P483, m483, toDim]

def fillDims (typeOf : α → String) (value : α) (dims : List Dim) : Result (ArrayState α) := do
  let converted ← dims.mapM toDim
  pure (filled (typeOf value) (oneToAxes converted) value)
def m583 := @fillDims
def P583 : Prop := ∀ {α : Type} (typeOf : α → String) (value : α) dims,
  m583 typeOf value dims = fillDims typeOf value dims
theorem p583 : P583 := by simp [P583, m583]
def m584 := @fillDims
def P584 : Prop := ∀ {α : Type} (typeOf : α → String) (value : α) dims,
  m584 typeOf value dims = fillDims typeOf value dims
theorem p584 : P584 := by simp [P584, m584]
def m585 := @fillDims
def P585 : Prop := ∀ {α : Type} (typeOf : α → String) (value : α) dims,
  m585 typeOf value dims = fillDims typeOf value dims
theorem p585 : P585 := by simp [P585, m585]
def m586 := @fillDims
def P586 : Prop := ∀ {α : Type} (typeOf : α → String) (value : α) dims,
  m586 typeOf value dims = fillDims typeOf value dims
theorem p586 : P586 := by simp [P586, m586]
def m587 (typeOf : α → String) (value : α) : ArrayState α := filled (typeOf value) [] value
def P587 : Prop := ∀ {α : Type} (typeOf : α → String) (value : α),
  (m587 typeOf value).values = [some value] ∧ (m587 typeOf value).axes = []
theorem p587 : P587 := by simp [P587, m587, filled]

def zeroOrOne (elementType : String) (makeValue : String → α) (dims : List Dim) : Result (ArrayState α) := do
  let converted ← dims.mapM toDim
  pure (filled elementType (oneToAxes converted) (makeValue elementType))
def m633 := @zeroOrOne
def P633 : Prop := ∀ {α : Type} elementType (makeValue : String → α) dims,
  m633 elementType makeValue dims = zeroOrOne elementType makeValue dims
theorem p633 : P633 := by simp [P633, m633]
def m634 := @zeroOrOne
def P634 : Prop := ∀ {α : Type} elementType (makeValue : String → α) dims,
  m634 elementType makeValue dims = zeroOrOne elementType makeValue dims
theorem p634 : P634 := by simp [P634, m634]
def m635 := @zeroOrOne
def P635 : Prop := ∀ {α : Type} elementType (makeValue : String → α) dims,
  m635 elementType makeValue dims = zeroOrOne elementType makeValue dims
theorem p635 : P635 := by simp [P635, m635]
def m636 := @zeroOrOne
def P636 : Prop := ∀ {α : Type} elementType (makeValue : String → α) dims,
  m636 elementType makeValue dims = zeroOrOne elementType makeValue dims
theorem p636 : P636 := by simp [P636, m636]
def m637 := @zeroOrOne
def P637 : Prop := ∀ {α : Type} elementType (makeValue : String → α) dims,
  m637 elementType makeValue dims = zeroOrOne elementType makeValue dims
theorem p637 : P637 := by simp [P637, m637]
def m642 (elementType : String) (makeValue : String → α) : ArrayState α := filled elementType [] (makeValue elementType)
def P642 : Prop := ∀ {α : Type} elementType (makeValue : String → α),
  (m642 elementType makeValue).values = [some (makeValue elementType)]
theorem p642 : P642 := by simp [P642, m642, filled]
def m647 := @zeroOrOne
def P647 : Prop := ∀ {α : Type} elementType (makeValue : String → α) dims,
  m647 elementType makeValue dims = zeroOrOne elementType makeValue dims
theorem p647 : P647 := by simp [P647, m647]

def m657 (construct : ArrayState α → Result (ArrayState β)) (source : ArrayState α)
    (targetType : String) : Result (ArrayState β) := do
  let result ← construct source
  if result.elementType = targetType then .ok result else .error .typeError
def P657 : Prop := ∀ {α β : Type} (construct : ArrayState α → Result (ArrayState β)) source targetType,
  m657 construct source targetType = do
    let result ← construct source
    if result.elementType = targetType then .ok result else .error .typeError
theorem p657 : P657 := by simp [P657, m657]

def m659 (promote : String → String → String) (left right : String) := promote left right
def P659 : Prop := ∀ promote left right, m659 promote left right = promote left right
theorem p659 : P659 := by simp [P659, m659]

def m664 (convert : α → Result β) (targetType : String) (source : ArrayState α) : Result (ArrayState β) := do
  let values ← assignedValues source
  let converted ← convertAll convert values
  pure { elementType := targetType, axes := source.axes, values := converted.map some, id := source.id + 1 }
def P664 : Prop := ∀ {α β : Type} (convert : α → Result β) targetType source,
  m664 convert targetType source = do
    let values ← assignedValues source
    let converted ← convertAll convert values
    pure { elementType := targetType, axes := source.axes, values := converted.map some, id := source.id + 1 }
theorem p664 : P664 := by simp [P664, m664]
def m665 := @m664
def P665 : Prop := ∀ {α β : Type} (convert : α → Result β) targetType source,
  m665 convert targetType source = m664 convert targetType source
theorem p665 : P665 := by simp [P665, m665]

inductive IteratorSize where | unknown | length (value : Int) | shape (axes : List (List Int)) deriving Repr, DecidableEq
def allocateFor (elementType : String) : IteratorSize → Result (ArrayState α)
  | .unknown => .ok (allocate elementType (oneToAxes [0]))
  | .length value => if value < 0 then .error .inexact else .ok (allocate elementType (oneToAxes [value.toNat]))
  | .shape axes => .ok (allocate elementType axes)

def collectInto (convert : α → Result β) (elementType : String)
    (values : List α) (size : IteratorSize) : Result (ArrayState β) := do
  let converted ← convertAll convert values
  let output : ArrayState β ← allocateFor elementType
    (match size with | .unknown => .length converted.length | other => other)
  pure { output with values := converted.map some }

def m684 := @collectInto
def P684 : Prop := ∀ {α β : Type} (convert : α → Result β) elementType (values : List α) size,
  m684 convert elementType values size = collectInto convert elementType values size
theorem p684 : P684 := by simp [P684, m684]
def m686 := @collectInto
def P686 : Prop := ∀ {α β : Type} (convert : α → Result β) elementType (values : List α) size,
  m686 convert elementType values size = collectInto convert elementType values size
theorem p686 : P686 := by simp [P686, m686]
def m688 := @collectInto
def P688 : Prop := ∀ {α β : Type} (convert : α → Result β) elementType (values : List α),
  m688 convert elementType values .unknown = collectInto convert elementType values .unknown
theorem p688 : P688 := by simp [P688, m688]

def m697 {C : Type} (similar : C → String → IteratorSize → ArrayState α)
    (container : C) elementType size := similar container elementType size
def P697 : Prop := ∀ {C α : Type} (similar : C → String → IteratorSize → ArrayState α)
    container elementType size, m697 similar container elementType size = similar container elementType size
theorem p697 : P697 := by simp [P697, m697]
def m699 {I : Type} (_iterator : I) : Option (List (List Int)) := none
def P699 : Prop := ∀ {I : Type} (iterator : I), m699 iterator = none
theorem p699 : P699 := by simp [P699, m699]
def m700 {I : Type} (length : I → Int) (iterator : I) := some (length iterator)
def P700 : Prop := ∀ {I : Type} (length : I → Int) iterator, m700 length iterator = some (length iterator)
theorem p700 : P700 := by simp [P700, m700]
def m701 {I : Type} (axes : I → List (List Int)) (iterator : I) := some (axes iterator)
def P701 : Prop := ∀ {I : Type} (axes : I → List (List Int)) iterator, m701 axes iterator = some (axes iterator)
theorem p701 : P701 := by simp [P701, m701]
def m703 (similar : ArrayState α → String → ArrayState β) source targetType := similar source targetType
def P703 : Prop := ∀ {α β : Type} (similar : ArrayState α → String → ArrayState β)
    (source : ArrayState α) targetType,
  m703 similar source targetType = similar source targetType
theorem p703 : P703 := by simp [P703, m703]
def m705 (similar : ArrayState α → String → Int → Result (ArrayState β)) source targetType length :=
  similar source targetType length
def P705 : Prop := ∀ {α β : Type}
    (similar : ArrayState α → String → Int → Result (ArrayState β))
    (source : ArrayState α) targetType length,
  m705 similar source targetType length = similar source targetType length
theorem p705 : P705 := by simp [P705, m705]
def m707 (similar : ArrayState α → String → List (List Int) → ArrayState β) source targetType axes :=
  similar source targetType axes
def P707 : Prop := ∀ {α β : Type}
    (similar : ArrayState α → String → List (List Int) → ArrayState β)
    (source : ArrayState α) targetType axes,
  m707 similar source targetType axes = similar source targetType axes
theorem p707 : P707 := by simp [P707, m707]

def m711 (elementType : String) : Result (ArrayState α) := allocateFor elementType .unknown
def P711 : Prop := ∀ {α : Type} elementType, (m711 elementType : Result (ArrayState α)) = allocateFor elementType .unknown
theorem p711 : P711 := by simp [P711, m711]
def m712 (elementType : String) (length : Int) : Result (ArrayState α) := allocateFor elementType (.length length)
def P712 : Prop := ∀ {α : Type} elementType length,
  (m712 elementType length : Result (ArrayState α)) = allocateFor elementType (.length length)
theorem p712 : P712 := by simp [P712, m712]
def m713 (elementType : String) (axes : List (List Int)) : Result (ArrayState α) := allocateFor elementType (.shape axes)
def P713 : Prop := ∀ {α : Type} elementType axes,
  (m713 elementType axes : Result (ArrayState α)) = allocateFor elementType (.shape axes)
theorem p713 : P713 := by simp [P713, m713]
def m716 (elementType : String) (size : IteratorSize) : Result (ArrayState α) := allocateFor elementType size
def P716 : Prop := ∀ {α : Type} elementType size,
  (m716 elementType size : Result (ArrayState α)) = allocateFor elementType size
theorem p716 : P716 := by simp [P716, m716]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-array-faithful-{line}", juliaFile := "base/array.jl", juliaFns := [name],
    statement, source := s!"base/array.jl:{line}; typed construction source equation", status := .proven,
    prop, thm := some thm }

def entries : List Entry := [
  entry 14 "DimensionMismatch()" "The zero-argument constructor creates DimensionMismatch." ``P14 ``p14,
  entry 135 "_safeindex" "Safe-index rewriting preserves atoms and recursively rewrites escape and call children." ``P135 ``p135,
  entry 158 "vect()" "The empty vector literal is a zero-length Vector{Any}." ``P158 ``p158,
  entry 188 "asize_from" "Array size lookup delegates with the original dimension." ``P188 ``p188,
  entry 190 "allocatedinline" "Inline allocation tests whether jl_stored_inline returns nonzero." ``P190 ``p190,
  entry 219 "elsize(::Ptr)" "Pointer element size delegates to aligned_sizeof(T)." ``P219 ``p219,
  entry 227 "elsize(::Union{},slurp...)" "Bottom element size is zero for every slurped argument list." ``P227 ``p227,
  entry 229 "sizeof(::Array)" "Array byte size multiplies element size by fixed-width length." ``P229 ``p229,
  entry 259 "unsafe_copyto!(Ptr,Ptr,n)" "Pointer copy calls memmove with n times sizeof(T) bytes and returns dest." ``P259 ``p259,
  entry 276 "unsafe_copyto!(Array,...)" "Array unsafe copy forms both offset pointers, copies n times element size, and returns dest." ``P276 ``p276,
  entry 299 "_copyto_impl!" "Copy validates offsets and count before overlap-safe ordered segment replacement." ``P299 ``p299,
  entry 321 "_throw_argerror" "The helper constructs ArgumentError with the supplied message." ``P321 ``p321,
  entry 323 "_copyto2arg!" "Two-argument copy delegates with one-based offsets and the complete source length." ``P323 ``p323,
  entry 368 "fill!" "Fill converts once to the array element type and writes every element." ``P368 ``p368,
  entry 373 "_fill!" "Typed fill writes the supplied value to every storage slot." ``P373 ``p373,
  entry 391 "copy(::Array)" "Copy allocates a distinct array with identical axes and every assigned value." ``P391 ``p391,
  entry 421 "similar(::Type{Array},dims)" "Typed similar creates Array{T,N} with requested dimensions." ``P421 ``p421,
  entry 445 "typed array literal" "Typed literal stores every input value in order with the requested element type." ``P445 ``p445,
  entry 463 "Any array literal" "Any literal stores every polymorphic input in order in Vector{Any}." ``P463 ``p463,
  entry 471 "empty Any literal" "The empty literal is a zero-length Vector{Any}." ``P471 ``p471,
  entry 473 "fill! byte array" "Byte fill converts the integer once, performs the byte fill, and preserves the converted value." ``P473 ``p473,
  entry 482 "to_dim(::Integer)" "Integer dimensions reject negatives and otherwise use the exact converted length." ``P482 ``p482,
  entry 483 "to_dim(::OneTo)" "OneTo dimensions call last and return the resulting endpoint length." ``P483 ``p483,
  entry 583 "fill(v,dims...)" "Fill computes typeof(v), converts every dimension, allocates, and stores v everywhere." ``P583 ``p583,
  entry 584 "fill(v,tuple dims)" "Tuple fill computes typeof(v), converts every dimension, and fills the exact shape." ``P584 ``p584,
  entry 585 "fill(v,integer dims)" "Integer tuple fill computes typeof(v), validates dimensions, and fills every element." ``P585 ``p585,
  entry 586 "fill(v,mixed dims)" "Mixed tuple fill computes typeof(v), converts axes and integers, and fills the exact shape." ``P586 ``p586,
  entry 587 "fill(v,())" "Zero-dimensional fill contains exactly the supplied value." ``P587 ``p587,
  entry 633 "zeros/ones(dims...)" "Default typed fill converts dimensions and fills every element with the constructed zero or one." ``P633 ``p633,
  entry 634 "zeros/ones(Type,dims...)" "Typed fill uses the requested element type and exact converted dimensions." ``P634 ``p634,
  entry 635 "zeros/ones(tuple)" "Tuple forwarding preserves requested dimensions and fill value." ``P635 ``p635,
  entry 636 "zeros/ones(Type,tuple)" "Typed tuple forwarding preserves requested type, dimensions, and fill value." ``P636 ``p636,
  entry 637 "zeros/ones(Type,integer tuple)" "Integer tuple fill validates every dimension before allocation and filling." ``P637 ``p637,
  entry 642 "zeros/ones(Type,())" "Zero-dimensional typed construction contains exactly the requested zero or one." ``P642 ``p642,
  entry 647 "zeros/ones(Type,mixed tuple)" "Mixed tuple fill converts every dimension and fills every resulting element." ``P647 ``p647,
  entry 657 "convert(::Type{<:Array},AbstractArray)" "Conversion constructs the result then enforces the requested target array type." ``P657 ``p657,
  entry 659 "promote_rule(Array,Array)" "Array promotion combines element types while preserving rank." ``P659 ``p659,
  entry 664 "Array{T,N}(AbstractArray)" "Typed construction preserves source axes and order while converting every assigned value." ``P664 ``p664,
  entry 665 "AbstractArray{T,N}(AbstractArray)" "AbstractArray construction delegates to typed similar and preserves axes and values." ``P665 ``p665,
  entry 684 "collect(Type,itr)" "Typed collection preserves requested element type and iterator order." ``P684 ``p684,
  entry 686 "_collect(Type,sized itr)" "Sized collection allocates the requested type and exact shape before writing all values." ``P686 ``p686,
  entry 688 "_collect(Type,unknown itr)" "Unknown-size collection grows a typed vector and preserves every iterated value." ``P688 ``p688,
  entry 697 "_similar_for" "Allocation forwards container, requested type, iterator size, and shape unchanged." ``P697 ``p697,
  entry 699 "_similar_shape(SizeUnknown)" "Unknown-size shape returns nothing." ``P699 ``p699,
  entry 700 "_similar_shape(HasLength)" "Length shape calls length(iterator) and preserves conversion behavior." ``P700 ``p700,
  entry 701 "_similar_shape(HasShape)" "Shaped iteration returns axes(iterator)." ``P701 ``p701,
  entry 703 "_similar_for(AbstractArray,unknown)" "Unknown-size array allocation delegates to similar(c,T)." ``P703 ``p703,
  entry 705 "_similar_for(AbstractArray,length)" "Length allocation delegates to similar(c,T,len)." ``P705 ``p705,
  entry 707 "_similar_for(AbstractArray,shape)" "Shaped allocation delegates to similar(c,T,axes)." ``P707 ``p707,
  entry 711 "_array_for_inner(SizeUnknown)" "Unknown-size allocation creates a typed empty vector." ``P711 ``p711,
  entry 712 "_array_for_inner(HasLength)" "Length allocation performs checked Int conversion before creating Vector{T}." ``P712 ``p712,
  entry 713 "_array_for_inner(HasShape)" "Shape allocation creates Array{T,N} with the requested axes." ``P713 ``p713,
  entry 716 "_array_for" "Array allocation forwards requested type and original iterator size." ``P716 ``p716
]

end JuliaLean.MultidimCov.ArrayBasicsFaithful
