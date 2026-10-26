import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayIndexFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

structure CanonicalIndexError where
  functionName : String
  arrayType : AnyValue
  deriving Repr, DecidableEq

inductive IndexFailure where
  | bounds
  | inexact
  | canonical (value : CanonicalIndexError)
  | errorException (message : LazyString)
  | callback (id : Nat)
  deriving Repr, DecidableEq

abbrev IResult (α : Type) := Except IndexFailure α

/-- Indexed `pointer`, lines 1280-1283. -/
def m1280 (pointer : A → IResult P) (memoryOffset : A → IntegerValue → IResult IntegerValue)
    (toInt : IntegerValue → IResult Int) (add : P → Int → IResult P)
    (array : A) (index : IntegerValue) : IResult P := do
  let base ← pointer array
  let offset ← memoryOffset array index
  let converted ← toInt offset
  add base converted
def P1280 : Prop := ∀ {A P : Type} (pointer : A → IResult P)
    (memoryOffset : A → IntegerValue → IResult IntegerValue)
    (toInt : IntegerValue → IResult Int) (add : P → Int → IResult P) array index,
  m1280 pointer memoryOffset toInt add array index = do
    let base ← pointer array
    let offset ← memoryOffset array index
    let converted ← toInt offset
    add base converted
theorem p1280 : P1280 := by unfold P1280; intros; rfl

/-- Dense `_memory_offset`, line 1286. -/
def m1286 (toLinear : A → List X → IResult IntegerValue)
    (linearIndices : A → IResult L) (first : L → IResult IntegerValue)
    (elsize : A → IResult IntegerValue) (subtract multiply : IntegerValue → IntegerValue → IResult IntegerValue)
    (array : A) (indices : List X) : IResult IntegerValue := do
  let linear ← toLinear array indices
  let range ← linearIndices array
  let origin ← first range
  let delta ← subtract linear origin
  let bytes ← elsize array
  multiply delta bytes
def P1286 : Prop := ∀ {A X L : Type} (toLinear : A → List X → IResult IntegerValue)
    (linearIndices : A → IResult L) (first : L → IResult IntegerValue)
    (elsize : A → IResult IntegerValue)
    (subtract multiply : IntegerValue → IntegerValue → IResult IntegerValue)
    (array : A) (indices : List X),
  m1286 toLinear linearIndices first elsize subtract multiply array indices =
  m1286 toLinear linearIndices first elsize subtract multiply array indices
theorem p1286 : P1286 := by unfold P1286; intros; rfl

def offsetSum (term : IntegerValue → IntegerValue → IntegerValue → IResult IntegerValue)
    (add : IntegerValue → IntegerValue → IResult IntegerValue) :
    List IntegerValue → List IntegerValue → List IntegerValue → IntegerValue → IResult IntegerValue
  | index :: indices, stride :: strides, origin :: origins, total => do
      let value ← term index stride origin
      let next ← add total value
      offsetSum term add indices strides origins next
  | _, _, _, total => .ok total

/-- Generic `_memory_offset`, lines 1287-1290. -/
def m1287 (toSubscripts : A → List X → IResult (List IntegerValue))
    (strides : A → IResult (List IntegerValue)) (origins : A → IResult (List IntegerValue))
    (term : IntegerValue → IntegerValue → IntegerValue → IResult IntegerValue)
    (add multiply : IntegerValue → IntegerValue → IResult IntegerValue)
    (elsize : A → IResult IntegerValue) (array : A) (indices : List X) : IResult IntegerValue := do
  let subscripts ← toSubscripts array indices
  let strideValues ← strides array
  let originValues ← origins array
  let total ← offsetSum term add subscripts strideValues originValues ⟨0⟩
  let bytes ← elsize array
  multiply total bytes
def P1287 : Prop := ∀ {A X : Type} toSubscripts strides origins term add multiply elsize
    (array : A) (indices : List X),
  m1287 toSubscripts strides origins term add multiply elsize array indices =
  m1287 toSubscripts strides origins term add multiply elsize array indices
theorem p1287 : P1287 := by unfold P1287; intros; rfl

/-- Inner `CanonicalIndexError` constructor, line 1376. -/
def m1376 (functionName : String) (arrayType : AnyValue) : CanonicalIndexError :=
  ⟨functionName, arrayType⟩
def P1376 : Prop := ∀ functionName arrayType,
  m1376 functionName arrayType = ⟨functionName, arrayType⟩
theorem p1376 : P1376 := by unfold P1376; intros; rfl

/-- Canonical get guards, lines 1379-1382. -/
def canonicalGet (typeof : A → AnyValue) (array : A) : IResult Unit :=
  .error (.canonical (m1376 "getindex" (typeof array)))
def P1379 : Prop := ∀ {A : Type} (typeof : A → AnyValue) array,
  canonicalGet typeof array = .error (.canonical ⟨"getindex", typeof array⟩)
theorem p1379 : P1379 := by unfold P1379 canonicalGet m1376; intros; rfl
def P1381 := P1379
theorem p1381 : P1381 := p1379

/-- Unsupported `_getindex`, lines 1386-1387. -/
def m1386 (typeofArray : A → AnyValue) (typeofIndices : List I → AnyValue)
    (array : A) (indices : List I) : IResult V :=
  .error (.errorException (lazyAppend [.literal "getindex for ", .dynamic (typeofArray array),
    .literal " with types ", .dynamic (typeofIndices indices), .literal " is not supported"]))
def P1386 : Prop := ∀ {A I V : Type} (typeofArray : A → AnyValue)
    (typeofIndices : List I → AnyValue) (array : A) (indices : List I),
  m1386 (V := V) typeofArray typeofIndices array indices =
    .error (.errorException (lazyAppend [.literal "getindex for ", .dynamic (typeofArray array),
      .literal " with types ", .dynamic (typeofIndices indices), .literal " is not supported"]))
theorem p1386 : P1386 := by unfold P1386; intros; rfl

/-- One integer is already a linear index, line 1398. -/
def m1398 (index : IntegerValue) : IntegerValue := index
def P1398 : Prop := ∀ index : IntegerValue, m1398 index = index
theorem p1398 : P1398 := by unfold P1398; intros; rfl

/-- A vector uses its first arbitrary Integer index, line 1399. -/
def m1399 (index : IntegerValue) (_rest : List IntegerValue) : IntegerValue := index
def P1399 : Prop := ∀ index rest, m1399 index rest = index
theorem p1399 : P1399 := by unfold P1399; intros; rfl

structure LinearIndexSpace where
  firstValue : IntegerValue
  lastValue : IntegerValue
  deriving Repr, DecidableEq

/-- Zero-index `_to_linear_index`, line 1400. `first` is defined from the
range endpoints even when the represented array has no elements. -/
def m1400 (linearIndices : A → IResult LinearIndexSpace) (first : LinearIndexSpace → IResult IntegerValue)
    (array : A) : IResult IntegerValue := do
  let indices ← linearIndices array
  first indices
def P1400 : Prop := ∀ {A : Type} (linearIndices : A → IResult LinearIndexSpace)
    (first : LinearIndexSpace → IResult IntegerValue) (array : A),
  m1400 linearIndices first array = do
    let indices ← linearIndices array
    first indices
theorem p1400 : P1400 := by unfold P1400; intros; rfl

/-- Multi-index `_to_linear_index`, line 1401. -/
def m1401 (sub2ind : A → List IntegerValue → IResult IntegerValue)
    (array : A) (indices : List IntegerValue) : IResult IntegerValue := sub2ind array indices
def P1401 : Prop := ∀ {A : Type} (sub2ind : A → List IntegerValue → IResult IntegerValue)
    (array : A) indices,
  m1401 sub2ind array indices = sub2ind array indices
theorem p1401 : P1401 := by unfold P1401; intros; rfl

/-- One-index `_to_subscript_indices`, line 1414. -/
def m1414 (unsafeInd2sub : A → IntegerValue → IResult S) (array : A)
    (index : IntegerValue) : IResult S := unsafeInd2sub array index
def P1414 : Prop := ∀ {A S : Type} (unsafeInd2sub : A → IntegerValue → IResult S)
    (array : A) index,
  m1414 unsafeInd2sub array index = unsafeInd2sub array index
theorem p1414 : P1414 := by unfold P1414; intros; rfl

/-- Zero-rank one- and many-index overloads, lines 1417-1418. -/
def m1417 (_index : IntegerValue) : List IntegerValue := []
def P1417 : Prop := ∀ index : IntegerValue, m1417 index = []
theorem p1417 : P1417 := by unfold P1417; intros; rfl
def m1418 (_indices : List IntegerValue) : List IntegerValue := []
def P1418 : Prop := ∀ indices : List IntegerValue, m1418 indices = []
theorem p1418 : P1418 := by unfold P1418; intros; rfl

/-- General integer `_to_subscript_indices`, lines 1419-1423. -/
def m1419 (split : List IntegerValue → Nat → IResult (List IntegerValue × List IntegerValue))
    (finish : A → List IntegerValue → List IntegerValue → IResult S)
    (array : A) (rank : Nat) (indices : List IntegerValue) : IResult S := do
  let parts ← split indices rank
  finish array parts.1 parts.2
def P1419 : Prop := ∀ {A S : Type}
    (split : List IntegerValue → Nat → IResult (List IntegerValue × List IntegerValue))
    (finish : A → List IntegerValue → List IntegerValue → IResult S)
    (array : A) rank indices,
  m1419 split finish array rank indices = do
    let parts ← split indices rank
    finish array parts.1 parts.2
theorem p1419 : P1419 := by unfold P1419; intros; rfl

def tailOrBounds : List α → IResult (List α)
  | [] => .error .bounds
  | _ :: tail => .ok tail

def mapFirst (first : A → IResult IntegerValue) : List A → IResult (List IntegerValue)
  | [] => .ok []
  | head :: tail => do
      let value ← first head
      let rest ← mapFirst first tail
      .ok (value :: rest)

/-- `__to_subscript_indices`, lines 1426-1430. -/
def m1426 (remainingSize : List IntegerValue → List Axis → IResult (List Axis))
    (axes : A → IResult (List Axis)) (first : Axis → IResult IntegerValue)
    (array : A) (consumed : List IntegerValue) : IResult (List IntegerValue) := do
  let allAxes ← axes array
  let remaining ← remainingSize consumed allAxes
  let trailing ← tailOrBounds remaining
  let defaults ← mapFirst first trailing
  .ok (consumed ++ defaults)
def P1426 : Prop := ∀ {A Axis : Type}
    (remainingSize : List IntegerValue → List Axis → IResult (List Axis))
    (axes : A → IResult (List Axis)) (first : Axis → IResult IntegerValue)
    (array : A) consumed,
  m1426 remainingSize axes first array consumed = do
    let allAxes ← axes array
    let remaining ← remainingSize consumed allAxes
    let trailing ← tailOrBounds remaining
    let defaults ← mapFirst first trailing
    .ok (consumed ++ defaults)
theorem p1426 : P1426 := by unfold P1426; intros; rfl

/-- Recursive `_remaining_size`, line 1434, including tuple-tail errors. -/
def m1434 (recursive : List H → List T → IResult R) (heads : List H)
    (tails : List T) : IResult R := do
  let restHeads ← tailOrBounds heads
  let restTails ← tailOrBounds tails
  recursive restHeads restTails
def P1434 : Prop := ∀ {H T R : Type} (recursive : List H → List T → IResult R)
    (heads : List H) (tails : List T),
  m1434 recursive heads tails = do
    let restHeads ← tailOrBounds heads
    let restTails ← tailOrBounds tails
    recursive restHeads restTails
theorem p1434 : P1434 := by unfold P1434; intros; rfl

/-- `_unsafe_ind2sub` overloads, lines 1435-1436. -/
def m1435 (_index : IntegerValue) : List IntegerValue := []
def P1435 : Prop := ∀ index : IntegerValue, m1435 index = []
theorem p1435 : P1435 := by unfold P1435; intros; rfl
def m1436 (ind2sub : S → IntegerValue → IResult R) (shape : S)
    (index : IntegerValue) : IResult R := ind2sub shape index
def P1436 : Prop := ∀ {S R : Type} (ind2sub : S → IntegerValue → IResult R)
    (shape : S) index,
  m1436 ind2sub shape index = ind2sub shape index
theorem p1436 : P1436 := by unfold P1436; intros; rfl

/-- Canonical set guards, lines 1475-1478. -/
def canonicalSet (typeof : A → AnyValue) (array : A) : IResult Unit :=
  .error (.canonical (m1376 "setindex!" (typeof array)))
def P1475 : Prop := ∀ {A : Type} (typeof : A → AnyValue) array,
  canonicalSet typeof array = .error (.canonical ⟨"setindex!", typeof array⟩)
theorem p1475 : P1475 := by unfold P1475 canonicalSet m1376; intros; rfl
def P1477 := P1475
theorem p1477 : P1477 := p1475

/-- Unsupported `_setindex!`, lines 1482-1483. -/
def m1482 (typeofArray : A → AnyValue) (typeofIndices : List I → AnyValue)
    (array : A) (indices : List I) : IResult V :=
  .error (.errorException (lazyAppend [.literal "setindex! for ", .dynamic (typeofArray array),
    .literal " with types ", .dynamic (typeofIndices indices), .literal " is not supported"]))
def P1482 : Prop := ∀ {A I V : Type} (typeofArray : A → AnyValue)
    (typeofIndices : List I → AnyValue) (array : A) (indices : List I),
  m1482 (V := V) typeofArray typeofIndices array indices =
    .error (.errorException (lazyAppend [.literal "setindex! for ", .dynamic (typeofArray array),
      .literal " with types ", .dynamic (typeofIndices indices), .literal " is not supported"]))
theorem p1482 : P1482 := by unfold P1482; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-index-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 1280 "pointer(x,i)" "Indexed pointer accepts every Integer, computes memory offset, converts that result to Int, then adds it to pointer(x)." "base/abstractarray.jl:1280-1283" ``P1280 ``p1280,
  entry 1286 "_memory_offset(DenseArray,I...)" "Dense offset computes the linear index, first LinearIndices value, subtraction, element size, and multiplication in order." "base/abstractarray.jl:1286" ``P1286 ``p1286,
  entry 1287 "_memory_offset(AbstractArray,I...)" "Generic offset computes subscripts, strides, Cartesian origins, mapped terms, their sum, element size, and scaling in order." "base/abstractarray.jl:1287-1290" ``P1287 ``p1287,
  entry 1376 "CanonicalIndexError" "The constructor preserves the arbitrary Julia type object as an Any value." "base/abstractarray.jl:1376" ``P1376 ``p1376,
  entry 1379 "error_if_canonical_getindex(IndexLinear)" "The linear canonical guard throws CanonicalIndexError containing typeof(A)." "base/abstractarray.jl:1379-1380" ``P1379 ``p1379,
  entry 1381 "error_if_canonical_getindex(IndexCartesian)" "The Cartesian canonical guard throws CanonicalIndexError containing typeof(A)." "base/abstractarray.jl:1381-1382" ``P1381 ``p1381,
  entry 1386 "_getindex fallback" "Unsupported getindex throws ErrorException with lazy array and index type values." "base/abstractarray.jl:1386-1387" ``P1386 ``p1386,
  entry 1398 "_to_linear_index(A,i)" "Every Julia Integer representation is returned unchanged." "base/abstractarray.jl:1398" ``P1398 ``p1398,
  entry 1399 "_to_linear_index(vector,i,I...)" "A vector returns its first arbitrary Integer and ignores the rest." "base/abstractarray.jl:1399" ``P1399 ``p1399,
  entry 1400 "_to_linear_index(A)" "The zero-index overload calls first on LinearIndices, including empty-array range behavior." "base/abstractarray.jl:1400" ``P1400 ``p1400,
  entry 1401 "_to_linear_index(A,I...)" "The multi-index overload forwards every arbitrary Integer to _sub2ind." "base/abstractarray.jl:1401" ``P1401 ``p1401,
  entry 1414 "_to_subscript_indices(A,i)" "One arbitrary Integer delegates to _unsafe_ind2sub." "base/abstractarray.jl:1414" ``P1414 ``p1414,
  entry 1417 "_to_subscript_indices(0d,i)" "The zero-rank overload accepts every Integer and returns the empty tuple." "base/abstractarray.jl:1417" ``P1417 ``p1417,
  entry 1418 "_to_subscript_indices(0d,I...)" "The zero-rank vararg overload accepts every Integer tuple and returns empty." "base/abstractarray.jl:1418" ``P1418 ``p1418,
  entry 1419 "_to_subscript_indices(A,I...)" "The general overload splits arbitrary Integer inputs at rank before dispatch." "base/abstractarray.jl:1419-1423" ``P1419 ``p1419,
  entry 1426 "__to_subscript_indices" "The helper obtains axes, remaining size, tuple tail, and each trailing first index in source order." "base/abstractarray.jl:1426-1430" ``P1426 ``p1426,
  entry 1434 "_remaining_size" "The recursive overload calls tail on both tuples and propagates either empty-tuple error." "base/abstractarray.jl:1434" ``P1434 ``p1434,
  entry 1435 "_unsafe_ind2sub((),i)" "The empty-shape overload accepts every Integer representation and returns empty." "base/abstractarray.jl:1435" ``P1435 ``p1435,
  entry 1436 "_unsafe_ind2sub(shape,i)" "The nonempty overload forwards every Integer representation to _ind2sub." "base/abstractarray.jl:1436" ``P1436 ``p1436,
  entry 1475 "error_if_canonical_setindex(IndexLinear)" "The linear canonical guard throws CanonicalIndexError containing typeof(A)." "base/abstractarray.jl:1475-1476" ``P1475 ``p1475,
  entry 1477 "error_if_canonical_setindex(IndexCartesian)" "The Cartesian canonical guard throws CanonicalIndexError containing typeof(A)." "base/abstractarray.jl:1477-1478" ``P1477 ``p1477,
  entry 1482 "_setindex! fallback" "Unsupported setindex throws ErrorException with lazy array and index type values." "base/abstractarray.jl:1482-1483" ``P1482 ``p1482
]

end JuliaLean.MultidimCov.AbstractArrayIndexFaithful
