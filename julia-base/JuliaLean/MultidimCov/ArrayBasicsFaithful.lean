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

private def entry (id : String) (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/array.jl", juliaFns := [name],
    statement, source := s!"base/array.jl:{line}; typed construction source equation", status := .proven,
    prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.ArrayBasicsFaithful
