import JuliaLean.Core

/-!
# Model of `base/iterators.jl`

Typed iterator protocol models for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
-/

namespace JuliaLean.base.iterators

set_option linter.unusedVariables false

open JuliaLean

instance {α : Type} : Lean.Order.PartialOrder (Jl (Option α)) :=
  Lean.Order.FlatOrder.instOrder (b := .ok none)

instance {α : Type} : Lean.Order.CCPO (Jl (Option α)) :=
  Lean.Order.FlatOrder.instCCPO (b := .ok none)

universe u v w x

/-- Exceptions thrown by `Iterators.Stateful` methods (`Base.EOFError`) and underlying callees. -/
inductive IteratorError where
  | eofError
  | julia (error : JlError)
  deriving Repr, DecidableEq, Inhabited

/-- A computation in `base/iterators.jl` that may throw `EOFError` or a core `JlError`. -/
abbrev IteratorResult (α : Type) := Except IteratorError α

instance : MonadLift Jl IteratorResult where
  monadLift
    | .ok x => .ok x
    | .error e => .error (.julia e)

inductive IteratorSizeTag where
  | sizeUnknown
  | hasLength
  | hasShape (dimensions : Nat)
  | isInfinite
  deriving Repr, DecidableEq

inductive IteratorEltypeTag where
  | hasEltype
  | eltypeUnknown
  deriving Repr, DecidableEq

/-- A typed model of Julia's iteration protocol and metadata operations. -/
structure IteratorModel (α S : Type) where
  run : Option S → Jl (Option (α × S))
  isdone : Option S → Jl (Option Bool)
  iteratorSize : IteratorSizeTag
  iteratorEltype : IteratorEltypeTag
  length : Jl Nat
  size : Jl (List Nat)

def listGet : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet xs n

def listIterator (xs : List α) : IteratorModel α Nat where
  run := fun state => do
    let i := state.getD 0
    match listGet xs i with
    | none => pure none
    | some x => pure (some (x, i + 1))
  isdone := fun state => pure (some (xs.length ≤ state.getD 0))
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]

def collectPrefix {α S : Type} (itr : IteratorModel α S) : Nat → Option S → Jl (List α)
  | 0, _ => pure []
  | n + 1, state => do
      match ← itr.run state with
      | none => pure []
      | some (x, next) => pure (x :: (← collectPrefix itr n (some next)))

def dropAdvance {α : Type} {S : Type} (run : Option S → Jl (Option (α × S))) : Nat → Option S → Jl (Option (α × S))
  | 0, state => run state
  | n + 1, state => do
      match ← run state with
      | none => pure none
      | some (_, next) => dropAdvance run n (some next)

def nthAdvance {α : Type} {S : Type} (run : Option S → Jl (Option (α × S))) : Nat → Option (α × S) → Jl (Option (α × S))
  | 0, current => pure current
  | _ + 1, none => pure none
  | n + 1, some (_, state) => do nthAdvance run n (← run (some state))

def boolOrMissing (left right : Option Bool) : Option Bool :=
  if left = some true || right = some true then some true
  else if left.isNone || right.isNone then none
  else some false

structure GeneratorModel (F I : Type) where
  f : F
  itr : I
  args : List I


def zipMinimumLength {α S : Type} : List (IteratorModel α S) → Jl (Option Nat)
  | [] => pure none
  | itr :: rest => do
      let n ← zipMinimumLength rest
      if itr.iteratorSize == .isInfinite then pure n else
        match n with
        | none => return some (← itr.length)
        | some m => return some (min m (← itr.length))

def productIteratorSizePair : IteratorSizeTag → IteratorSizeTag → IteratorSizeTag
  | .hasLength, .hasLength => .hasShape 2
  | .hasLength, .hasShape n => .hasShape (n + 1)
  | .hasShape n, .hasLength => .hasShape (n + 1)
  | .hasShape m, .hasShape n => .hasShape (m + n)
  | .isInfinite, _ => .isInfinite
  | _, .isInfinite => .isInfinite
  | _, _ => .sizeUnknown

def productIteratorSizeFold : List IteratorSizeTag → IteratorSizeTag
  | [] => .hasShape 0
  | [tag] => productIteratorSizePair tag (.hasShape 0)
  | tag :: rest => productIteratorSizePair tag (productIteratorSizeFold rest)

def productEltypeFold : List IteratorEltypeTag → IteratorEltypeTag
  | [] => .hasEltype
  | tag :: rest => if tag == .eltypeUnknown then .eltypeUnknown else productEltypeFold rest

def checkedProductFold (checkedMul : JInt64 → JInt64 → Jl JInt64) :
    JInt64 → List JInt64 → Jl JInt64
  | acc, [] => pure acc
  | acc, value :: rest => do checkedProductFold checkedMul (← checkedMul acc value) rest

def zipIteratorSizePair (a b : IteratorSizeTag) : IteratorSizeTag :=
  match a, b with
  | .hasLength, .isInfinite => .hasLength
  | .hasShape _, .isInfinite => .hasLength
  | .isInfinite, .hasLength => .hasLength
  | .isInfinite, .hasShape _ => .hasLength
  | .isInfinite, .isInfinite => .isInfinite
  | .isInfinite, .sizeUnknown => .sizeUnknown
  | .sizeUnknown, .isInfinite => .sizeUnknown
  | .hasLength, .hasLength => .hasLength
  | .hasLength, .hasShape _ => .hasLength
  | .hasShape _, .hasLength => .hasLength
  | .hasShape m, .hasShape n => if m = n then .hasShape m else .hasLength
  | .sizeUnknown, _ => .sizeUnknown
  | _, .sizeUnknown => .sizeUnknown

def zipIteratorSizeFold : List IteratorSizeTag → IteratorSizeTag
  | [] => .isInfinite
  | [tag] => tag
  | tag :: rest => zipIteratorSizePair tag (zipIteratorSizeFold rest)

def zipIteratorEltypeFold : List IteratorEltypeTag → IteratorEltypeTag
  | [] => .hasEltype
  | [tag] => tag
  | tag :: rest => if tag == .hasEltype && zipIteratorEltypeFold rest == .hasEltype then .hasEltype else .eltypeUnknown

structure PairsModel (K V I D : Type) where
  data : D
  itr : Option I

inductive PartitionState (S : Type) where
  | cutShort
  | at (state : Option S)
  deriving Repr, DecidableEq

structure FindEachModel (K V : Type) where
  predicate : V → Bool
  pairs : List (K × V)

def collectFindEach {K V : Type} (it : FindEachModel K V) : List K :=
  (it.pairs.filter fun pair => it.predicate pair.2).map Prod.fst

def collectPartitionChunk {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (itr : I) : Nat → Option S → Jl (List α × Option S)
  | 0, state => pure ([], state)
  | n + 1, state => do
      match ← iterate itr state with
      | none => pure ([], none)
      | some (value, next) =>
          let (rest, finalState) ← collectPartitionChunk iterate itr n (some next)
          pure (value :: rest, finalState)


def productSizeList {I : Type} (size : I → Jl (List Nat)) (length : I → Jl Nat)
    (trait : I → IteratorSizeTag) : List I → Jl (List Nat)
  | [] => pure []
  | item :: rest => do
      let first ← match trait item with
        | .hasShape _ => size item
        | .hasLength => pure [← length item]
        | _ => .error (.argumentError "Cannot compute size for iterator")
      pure (first ++ (← productSizeList size length trait rest))

def productAxesList {I : Type} (axes : I → Jl (List Nat)) (length : I → Jl Nat)
    (trait : I → IteratorSizeTag) : List I → Jl (List Nat)
  | [] => pure []
  | item :: rest => do
      let first ← match trait item with
        | .hasShape _ => axes item
        | .hasLength => pure [← length item]
        | _ => .error (.argumentError "Cannot compute indices for iterator")
      pure (first ++ (← productAxesList axes length trait rest))

inductive FlattenInnerKind where
  | bottom
  | emptyTuple
  | fixedTuple (length : Nat)
  | tuple
  | number
  | other
  deriving Repr, DecidableEq

inductive StatefulVS where
  | bottom
  | pairOrNothing (tag : Nat)
  | other (tag : Nat)
  | any
  deriving Repr, DecidableEq

def flattenSizeTag (outer : IteratorSizeTag) (innerEltypeKnown : Bool)
    (kind : FlattenInnerKind) : IteratorSizeTag :=
  if !innerEltypeKnown then .sizeUnknown else
    match outer, kind with
    | .hasLength, .emptyTuple => .hasLength
    | .hasShape _, .emptyTuple => .hasLength
    | .hasLength, .fixedTuple _ => .hasLength
    | .hasShape _, .fixedTuple _ => .hasLength
    | .hasLength, .number => .hasLength
    | .hasShape _, .number => .hasLength
    | _, _ => .sizeUnknown


def zipDoneDetails {I S : Type} : List I → List (Option S) →
    (I → Option S → Jl (Option Bool)) → Jl (Bool × List (Option Bool))
  | [], [], _ => pure (false, [])
  | itr :: rest, state :: states, isdone => do
      let current ← isdone itr state
      let (later, results) ← zipDoneDetails rest states isdone
      pure (current == some true || later, current :: results)
  | _, _, _ => pure (false, [])

def zipUnknownCandidates {I α S : Type} : List I → List (Option S) → List (Option Bool) →
    (I → Option S → Jl (Option (α × S))) → Jl (Option (List (Option (α × S))))
  | [], [], [], _ => pure (some [])
  | itr :: rest, state :: states, check :: checks, iterate => do
      let current : Option (Option (α × S)) ←
        if check.isNone then do
          match ← iterate itr state with
          | none => pure none
          | some value => pure (some (some value))
        else pure (some none)
      match current with
      | none => pure none
      | some entry =>
          match ← zipUnknownCandidates rest states checks iterate with
          | none => pure none
          | some later => pure (some (entry :: later))
  | _, _, _, _ => pure none

def zipResolveCandidates {I α S : Type} : List I → List (Option S) →
    List (Option (α × S)) → (I → Option S → Jl (Option (α × S))) →
    Jl (Option (List (α × S)))
  | [], [], [], _ => pure (some [])
  | itr :: rest, state :: states, candidate :: candidates, iterate => do
      let current ← match candidate with | none => iterate itr state | some value => pure (some value)
      match current with
      | none => pure none
      | some value =>
          match ← zipResolveCandidates rest states candidates iterate with
          | none => pure none
          | some later => pure (some (value :: later))
  | _, _, _, _ => pure none

/--
Julia source: base/iterators.jl:125-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Reverse{T}
    itr::T
end
```
-/
structure Reverse (I : Type) where
  itr : I

/--
Julia source: base/iterators.jl:166-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Enumerate{I}
    itr::I
end
```
-/
structure Enumerate (I : Type) where
  itr : I

/--
Julia source: base/iterators.jl:336-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Zip{Is<:Tuple}
    is::Is
end
```
-/
structure Zip (Is : Type u) where
  is : Is

/--
Julia source: base/iterators.jl:530-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Filter{F,I}
    flt::F
    itr::I
end
```
-/
structure Filter (F : Type) (I : Type) where
  flt : F
  itr : I

/--
Julia source: base/iterators.jl:603-607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Accumulate{F,I,T}
    f::F
    itr::I
    init::T
end
```
-/
structure Accumulate (F : Type) (I : Type) (T : Type) where
  f : F
  itr : I
  init : T

/--
Julia source: base/iterators.jl:669-672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Rest{I,S}
    itr::I
    st::S
end
```
-/
structure Rest (I : Type) (S : Type) where
  itr : I
  st : S

/--
Julia source: base/iterators.jl:743-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Count{T,S}
    start::T
    step::S
end
```
-/
structure Count (T : Type) (S : Type) where
  start : T
  step : S
  add : T → S → T

/--
Julia source: base/iterators.jl:778-780 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Take{I}
    xs::I
    n::Int
```
-/
structure Take (I : Type) where
  xs : I
  n : Nat

/--
Julia source: base/iterators.jl:837-839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Drop{I}
    xs::I
    n::Int
```
-/
structure Drop (I : Type) where
  xs : I
  n : Nat

/--
Julia source: base/iterators.jl:897-899 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct TakeWhile{I,P<:Function}
    pred::P
    xs::I
```
-/
structure TakeWhile (I : Type) (P : Type) where
  pred : P
  xs : I

/--
Julia source: base/iterators.jl:944-946 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct DropWhile{I,P<:Function}
    pred::P
    xs::I
```
-/
structure DropWhile (I : Type) (P : Type) where
  pred : P
  xs : I

/--
Julia source: base/iterators.jl:1023-1025 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Cycle{I}
    xs::I
end
```
-/
structure Cycle (I : Type) where
  xs : I

/--
Julia source: base/iterators.jl:1080-1082 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Repeated{O}
    x::O
end
```
-/
structure Repeated (O : Type) where
  x : O

/--
Julia source: base/iterators.jl:1124-1126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct ProductIterator{T<:Tuple}
    iterators::T
end
```
-/
structure ProductIterator (T : Type) where
  iterators : T

/--
Julia source: base/iterators.jl:1261-1263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct Flatten{I}
    it::I
end
```
-/
structure Flatten (I : Type) where
  it : I

/--
Julia source: base/iterators.jl:1441-1444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct PartitionIterator{T}
    c::T
    n::Int
end
```
-/
structure PartitionIterator (T : Type) where
  c : T
  n : Nat

/--
Julia source: base/iterators.jl:1562-1565 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct Stateful{T, VS}
    itr::T
    # A bit awkward right now, but adapted to the new iteration protocol
    nextvalstate::Union{VS, Nothing}
```
-/
structure Stateful (I : Type) (V : Type) where
  itr : I
  nextvalstate : Option V

/--
Julia source: base/iterators.jl:1700-1702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct IterableStatePairs{T}
    x::T
end
```
-/
structure IterableStatePairs (T : Type) where
  x : T

/--
Julia source: base/iterators.jl:433-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _zip_any_isdone(is::Tuple, ss::Tuple)
    d1 = isdone(is[1], ss[1]...)
    d1 === true && return true
    return d1 | _zip_any_isdone(tail(is), tail(ss))
end
```
-/
def zipAnyIsdone {I S : Type} (isdone : I → Option S → Jl (Option Bool)) :
    List (I × Option S) → Jl (Option Bool)
  | [] => pure (some false)
  | (itr, state) :: rest => do
      let done ← isdone itr state
      if done = some true then pure done else
        boolOrMissing done <$> zipAnyIsdone isdone rest

/--
Julia source: base/iterators.jl:465-471 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _zip_iterate_in_order(is::Tuple, ss::Tuple)
    x = iterate(is[1], ss[1]...)
    x === nothing && return nothing
    y = _zip_iterate_in_order(tail(is), tail(ss))
    y === nothing && return nothing
    return (x, y...)
end
```
-/
def zipIterateInOrder {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))) :
    List (I × Option S) → Jl (Option (List α × List (Option S)))
  | [] => pure (some ([], []))
  | (itr, state) :: rest => do
      match ← iterate itr state with
      | none => pure none
      | some (value, next) =>
          match ← zipIterateInOrder iterate rest with
          | none => pure none
          | some (values, states) => pure (some (value :: values, some next :: states))

/--
Julia source: base/iterators.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(z::Zip) = _zip_any_isdone(z.is, Base.map(_ -> (), z.is))
```
-/
def zipIsdone {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (z : Zip (List I)) : Jl (Option Bool) :=
  zipAnyIsdone isdone (z.is.map fun itr => (itr, none))

/--
Julia source: base/iterators.jl:431-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(z::Zip, ss) = _zip_any_isdone(z.is, Base.map(tuple, ss))
```
-/
def zipIsdoneState {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (z : Zip (List I)) (states : List (Option S)) : Jl (Option Bool) :=
  zipAnyIsdone isdone (List.zip z.is states)

/--
Julia source: base/iterators.jl:438-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _zip_any_isdone(::Tuple{}, ::Tuple{}) = false
```
-/
def zipAnyIsdoneEmpty : Option Bool := some false

/--
Julia source: base/iterators.jl:440-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds iterate(z::Zip) = _zip_iterate_all(z.is, Base.map(_ -> (), z.is))
```
-/
def iterateZipStart {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (z : Zip (List I)) : Jl (Option (List α × List (Option S))) :=
  zipIterateInOrder iterate (z.is.map fun itr => (itr, none))

/--
Julia source: base/iterators.jl:441-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds iterate(z::Zip, ss) = _zip_iterate_all(z.is, Base.map(tuple, ss))
```
-/
def iterateZipState {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (z : Zip (List I)) (states : List (Option S)) : Jl (Option (List α × List (Option S))) :=
  zipIterateInOrder iterate (List.zip z.is states)

/--
Julia source: base/iterators.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, arg, args...) = Base.Generator(f, arg, args...)
```
-/
def mapModel {F I : Type} (f : F) (arg : I) (args : List I) : GeneratorModel F I :=
  ⟨f, arg, args⟩

/--
Julia source: base/iterators.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_min_length(a, b, ::IsInfinite, ::IsInfinite) = min(length(a),length(b)) # inherit behaviour, error
```
-/
def minLengthInfiniteInfinite {I : Type} (length : I → Nat) (a b : I) : Nat :=
  min (length a) (length b)

/--
Julia source: base/iterators.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_min_length(a, b, A, ::IsInfinite) = length(a)
```
-/
def minLengthOtherInfinite {I : Type} (length : I → Nat) (a : I) (_ : I) : Nat := length a

/--
Julia source: base/iterators.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_min_length(a, b, ::IsInfinite, B) = length(b)
```
-/
def minLengthInfiniteOther {I : Type} (length : I → Nat) (_ : I) (b : I) : Nat := length b

/--
Julia source: base/iterators.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_min_length(a, b, A, B) = min(length(a),length(b))
```
-/
def minLengthOtherOther {I : Type} (length : I → Nat) (a b : I) : Nat :=
  min (length a) (length b)

/--
Julia source: base/iterators.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_diff_length(a, b, A, ::IsInfinite) = 0
```
-/
def diffLengthOtherInfinite {I : Type} (_ : I → Nat) (_ _ : I) : Nat := 0

/--
Julia source: base/iterators.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_diff_length(a, b, ::IsInfinite, ::IsInfinite) = 0
```
-/
def diffLengthInfiniteInfinite {I : Type} (_ : I → Nat) (_ _ : I) : Nat := 0

/--
Julia source: base/iterators.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_diff_length(a, b, ::IsInfinite, B) = length(a) # inherit behaviour, error
```
-/
def diffLengthInfiniteOther {I : Type} (length : I → Nat) (a : I) (_ : I) : Nat := length a

/--
Julia source: base/iterators.jl:66-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _diff_length(a, b, A, B)
    m, n = length(a), length(b)
    return m > n ? m - n : zero(n - m)
end
```
-/
def diffLengthOtherOther {I : Type} (length : I → Nat) (a b : I) : Nat :=
  let m := length a
  let n := length b
  if m > n then m - n else 0

/--
Julia source: base/iterators.jl:71-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_iteratorsize(isz::T, ::T) where {T} = isz
```
-/
def andIteratorSizeSame {T : Type} (isz : T) (_ : T) : T := isz

/--
Julia source: base/iterators.jl:72-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_iteratorsize(::HasLength, ::HasShape) = HasLength()
```
-/
def andIteratorSizeLengthShape (_ : IteratorSizeTag) (_ : IteratorSizeTag) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:73-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_iteratorsize(::HasShape, ::HasLength) = HasLength()
```
-/
def andIteratorSizeShapeLength (_ : IteratorSizeTag) (_ : IteratorSizeTag) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:74-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_iteratorsize(::HasShape{N}, ::HasShape{N}) where {N} = HasShape{N}()
```
-/
def andIteratorSizeSameShape (n : Nat) (_ : Nat) : IteratorSizeTag := .hasShape n

/--
Julia source: base/iterators.jl:75-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_iteratorsize(::HasShape, ::HasShape) = HasLength()
```
-/
def andIteratorSizeShapeShape (_ : IteratorSizeTag) (_ : IteratorSizeTag) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_iteratorsize(a, b) = SizeUnknown()
```
-/
def andIteratorSizeOther (_ _ : IteratorSizeTag) : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:78-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_iteratoreltype(iel::T, ::T) where {T} = iel
```
-/
def andIteratorEltypeSame {T : Type} (iel : T) (_ : T) : T := iel

/--
Julia source: base/iterators.jl:79-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
and_iteratoreltype(a, b) = EltypeUnknown()
```
-/
def andIteratorEltypeOther (_ _ : IteratorEltypeTag) : IteratorEltypeTag := .eltypeUnknown

def andIteratorSizeDispatch (a b : IteratorSizeTag) : IteratorSizeTag :=
  match a, b with
  | .hasShape m, .hasShape n =>
      if m = n then andIteratorSizeSameShape m n else andIteratorSizeShapeShape a b
  | .hasLength, .hasLength => andIteratorSizeSame a b
  | .sizeUnknown, .sizeUnknown => andIteratorSizeSame a b
  | .isInfinite, .isInfinite => andIteratorSizeSame a b
  | .hasLength, .hasShape _ => andIteratorSizeLengthShape a b
  | .hasShape _, .hasLength => andIteratorSizeShapeLength a b
  | _, _ => andIteratorSizeOther a b

def andIteratorEltypeDispatch (a b : IteratorEltypeTag) : IteratorEltypeTag :=
  if a = b then andIteratorEltypeSame a b else andIteratorEltypeOther a b

/--
Julia source: base/iterators.jl:113-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(itr) = Reverse(itr)
```
-/
def reverseDefault {I : Type} (itr : I) : Reverse I := ⟨itr⟩

/--
Julia source: base/iterators.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Reverse{T}}) where {T} = eltype(T)
```
-/
def reverseEltype (eltype : Type) {I : Type} (_ : Reverse I) : Type := eltype

/--
Julia source: base/iterators.jl:129-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(r::Reverse) = length(r.itr)
```
-/
def reverseLength {I : Type} {α : Type} (length : I → Jl α) (r : Reverse I) : Jl α := length r.itr

/--
Julia source: base/iterators.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(r::Reverse) = size(r.itr)
```
-/
def reverseSize {I : Type} {α : Type} (size : I → Jl α) (r : Reverse I) : Jl α := size r.itr

/--
Julia source: base/iterators.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{Reverse{T}}) where {T} = IteratorSize(T)
```
-/
def reverseIteratorSize {I : Type} (iteratorSize : I → IteratorSizeTag) (r : Reverse I) : IteratorSizeTag := iteratorSize r.itr

/--
Julia source: base/iterators.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Reverse{T}}) where {T} = IteratorEltype(T)
```
-/
def reverseIteratorEltype {I : Type} (iteratorEltype : I → IteratorEltypeTag) (r : Reverse I) : IteratorEltypeTag := iteratorEltype r.itr

/--
Julia source: base/iterators.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(r::Reverse) = first(r.itr) # the first shall be last
```
-/
def reverseLast {I : Type} {α : Type} (first : I → Jl α) (r : Reverse I) : Jl α := first r.itr

/--
Julia source: base/iterators.jl:136-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function iterate(A::Reverse{<:AbstractArray}, state=(reverse(eachindex(A.itr)),))
    y = iterate(state...)
    y === nothing && return y
    idx, itrs = y
    (A.itr[idx], (state[1], itrs))
end
```
-/
def sourceMethod136 {Arr I R S K V : Type}
    (eachindex : Arr → I) (reverseIndex : I → R)
    (iterate : R → Option S → Jl (Option (K × S)))
    (getindex : Arr → K → Jl V)
    (A : Reverse Arr) (state : Option (R × S) := none) :
    Jl (Option (V × (R × S))) := do
  let (r, rest) := match state with
    | none => (reverseIndex (eachindex A.itr), none)
    | some (r, s) => (r, some s)
  match ← iterate r rest with
  | none => pure none
  | some (idx, itrs) => pure (some (← getindex A.itr idx, (r, itrs)))

/--
Julia source: base/iterators.jl:145-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(A::Reverse, state=(reverse(eachindex(A.itr)),))
    y = iterate(state...)
    y === nothing && return y
    idx, itrs = y
    (A.itr[idx], (state[1], itrs))
end
```
-/
def sourceMethod145 {Arr I R S K V : Type}
    (eachindex : Arr → I) (reverseIndex : I → R)
    (iterate : R → Option S → Jl (Option (K × S)))
    (getindex : Arr → K → Jl V)
    (A : Reverse Arr) (state : Option (R × S) := none) :
    Jl (Option (V × (R × S))) := do
  let (r, rest) := match state with
    | none => (reverseIndex (eachindex A.itr), none)
    | some (r, s) => (r, some s)
  match ← iterate r rest with
  | none => pure none
  | some (idx, itrs) => pure (some (← getindex A.itr idx, (r, itrs)))

/--
Julia source: base/iterators.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::Reverse{Union{}}) = throw(ArgumentError("cannot iterate a reversed iterator of type Union{}"))
```
-/
def sourceMethod153 {I α S : Type} (_ : Reverse I) : Jl (Option (α × S)) :=
  .error (.argumentError "cannot iterate a reversed iterator of type Union{}")

/--
Julia source: base/iterators.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::Reverse{Union{}}, state) = throw(ArgumentError("cannot iterate a reversed iterator of type Union{}"))
```
-/
def sourceMethod154 {I α S Q : Type} (_ : Reverse I) (_ : Q) : Jl (Option (α × S)) :=
  .error (.argumentError "cannot iterate a reversed iterator of type Union{}")

/--
Julia source: base/iterators.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(R::AbstractRange) = Base.reverse(R) # copying ranges is cheap
```
-/
def sourceMethod156 {R : Type} (reverseRange : R → R) (r : R) : R := reverseRange r

/--
Julia source: base/iterators.jl:157-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(G::Generator) = Generator(G.f, reverse(G.iter))
```
-/
def sourceMethod157 {F I : Type} (reverse : I → I) (g : GeneratorModel F I) : GeneratorModel F I :=
  ⟨g.f, reverse g.itr, []⟩

/--
Julia source: base/iterators.jl:158-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(r::Reverse) = r.itr
```
-/
def reverseUnwrap {I : Type} (r : Reverse I) : I := r.itr

/--
Julia source: base/iterators.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(x::Union{Number,AbstractChar}) = x
```
-/
def sourceMethod159 {α : Type} (x : α) : α := x

/--
Julia source: base/iterators.jl:160-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(p::Pair) = Base.reverse(p) # copying pairs is cheap
```
-/
def sourceMethod160 {α β : Type} (reversePair : α × β → β × α) (p : α × β) : β × α :=
  reversePair p

/--
Julia source: base/iterators.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::Reverse{<:Union{Tuple, NamedTuple}}, i::Int = length(r.itr)) = i < 1 ? nothing : (r.itr[i], i-1)
```
-/
def iterateReverseTuple {I α : Type} (length : I → Nat)
    (getindex : I → Nat → Jl α) (r : Reverse I) (state : Option Int) : Jl (Option (α × Int)) := do
  let i := state.getD (Int.ofNat (length r.itr))
  if i < 1 then pure none else
    pure (some (← getindex r.itr (i.toNat - 1), i - 1))

/--
Julia source: base/iterators.jl:207-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
enumerate(iter) = Enumerate(iter)
```
-/
def enumerateModel {I : Type} (iter : I) : Enumerate I := ⟨iter⟩

/--
Julia source: base/iterators.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(e::Enumerate) = length(e.itr)
```
-/
def enumerateLength {I : Type} {α : Type} (length : I → Jl α) (e : Enumerate I) : Jl α := length e.itr

/--
Julia source: base/iterators.jl:210-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(e::Enumerate) = size(e.itr)
```
-/
def enumerateSize {I : Type} {α : Type} (size : I → Jl α) (e : Enumerate I) : Jl α := size e.itr

/--
Julia source: base/iterators.jl:211-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function iterate(e::Enumerate, state=(1,))
    i, rest = state[1], tail(state)
    n = iterate(e.itr, rest...)
    n === nothing && return n
    (i, n[1]), (i+1, n[2])
end
```
-/
def iterateEnumerate {I : Type} {α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (e : Enumerate I) (state : Option (JInt64 × S)) : Jl (Option ((JInt64 × α) × (JInt64 × S))) := do
  let (i, rest) := match state with
    | none => (JInt.lit .i64 1, none)
    | some (i, s) => (i, some s)
  match ← iterate e.itr rest with
  | none => pure none
  | some (x, next) => pure (some ((i, x), (i + JInt.lit .i64 1, next)))

/--
Julia source: base/iterators.jl:217-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(e::Enumerate) = (length(e.itr), last(e.itr))
```
-/
def enumerateLast {I : Type} {α N : Type} (length : I → Jl N) (last : I → Jl α)
    (e : Enumerate I) : Jl (N × α) := do pure ((← length e.itr), (← last e.itr))

/--
Julia source: base/iterators.jl:219-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Enumerate{I}}) where {I} = TupleOrBottom(Int, eltype(I))
```
-/
def enumerateEltype (α : Type) : Type := JInt64 × α

/--
Julia source: base/iterators.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{Enumerate{I}}) where {I} = IteratorSize(I)
```
-/
def enumerateIteratorSize {I : Type} (iteratorSize : I → IteratorSizeTag)
    (e : Enumerate I) : IteratorSizeTag := iteratorSize e.itr

/--
Julia source: base/iterators.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Enumerate{I}}) where {I} = IteratorEltype(I)
```
-/
def enumerateIteratorEltype {I : Type} (iteratorEltype : I → IteratorEltypeTag)
    (e : Enumerate I) : IteratorEltypeTag := iteratorEltype e.itr

/--
Julia source: base/iterators.jl:224-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(r::Reverse{<:Enumerate})
    ri = reverse(r.itr.itr)
    iterate(r, (length(ri), ri))
end
```
-/
def sourceMethod224 {I R α S : Type} (r : Reverse (Enumerate I)) (reverse : I → R)
    (length : R → Jl Nat)
    (iterate : Reverse (Enumerate I) → (Nat × R × Option S) → Jl (Option ((JInt64 × α) × (Nat × R × S)))) :
    Jl (Option ((JInt64 × α) × (Nat × R × S))) := do
  let ri := reverse r.itr.itr
  iterate r (← length ri, ri, none)

/--
Julia source: base/iterators.jl:228-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(r::Reverse{<:Enumerate}, state)
    i, ri, rest = state[1], state[2], tail(tail(state))
    n = iterate(ri, rest...)
    n === nothing && return n
    (i, n[1]), (i-1, ri, n[2])
end
```
-/
def sourceMethod228 {I α S : Type} (i : Nat) (ri : I) (state : Option S)
    (iterate : I → Option S → Jl (Option (α × S))) :
    Jl (Option ((JInt64 × α) × (Nat × I × S))) := do
  match ← iterate ri state with
  | none => pure none
  | some (value, next) => pure (some ((JInt.lit .i64 (Int.ofNat i), value), (i - 1, ri, next)))

/--
Julia source: base/iterators.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(::IndexLinear,    A::AbstractArray) = Pairs(A, LinearIndices(A))
```
-/
def pairsLinear {A K V I : Type} (linearIndices : A → I) (data : A) : PairsModel K V I A :=
  ⟨data, some (linearIndices data)⟩

/--
Julia source: base/iterators.jl:285-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(tuple::Tuple) = Pairs{Int}(tuple, keys(tuple))
```
-/
def pairsTuple {A K V I : Type} (keys : A → I) (data : A) : PairsModel K V I A :=
  ⟨data, some (keys data)⟩

/--
Julia source: base/iterators.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(nt::NamedTuple) = Pairs{Symbol}(nt, nothing)
```
-/
def pairsNamedTuple {A K V I : Type} (_ : A → I) (data : A) : PairsModel K V I A :=
  ⟨data, none⟩

/--
Julia source: base/iterators.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(v::Core.SimpleVector) = Pairs(v, LinearIndices(v))
```
-/
def pairsSimpleVector {A K V I : Type} (linearIndices : A → I) (data : A) : PairsModel K V I A :=
  ⟨data, some (linearIndices data)⟩

/--
Julia source: base/iterators.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(A::AbstractVector) = pairs(IndexLinear(), A)
```
-/
def pairsVector {A K V I : Type} (linearPairsModel : A → PairsModel K V I A) (a : A) : PairsModel K V I A := linearPairsModel a

/--
Julia source: base/iterators.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(::IndexCartesian, A::AbstractArray) = Pairs(A, Base.CartesianIndices(axes(A)))
```
-/
def pairsCartesian {A K V I : Type} (cartesianIndices : A → I) (data : A) : PairsModel K V I A :=
  ⟨data, some (cartesianIndices data)⟩

/--
Julia source: base/iterators.jl:292-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(A::AbstractArray)  = pairs(IndexCartesian(), A)
```
-/
def pairsArray {A K V I : Type} (cartesianPairsModel : A → PairsModel K V I A) (a : A) : PairsModel K V I A := cartesianPairsModel a

/--
Julia source: base/iterators.jl:294-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(v::Pairs) = length(keys(v))
```
-/
def pairsLength {K V I D N : Type} (keys : PairsModel K V I D → List K)
    (length : List K → Jl N) (v : PairsModel K V I D) : Jl N := length (keys v)

/--
Julia source: base/iterators.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(v::Pairs) = axes(keys(v))
```
-/
def pairsAxes {K V I D A : Type} (keys : PairsModel K V I D → List K)
    (axes : List K → Jl A) (v : PairsModel K V I D) : Jl A := axes (keys v)

/--
Julia source: base/iterators.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(v::Pairs) = size(keys(v))
```
-/
def pairsSize {K V I D A : Type} (keys : PairsModel K V I D → List K)
    (size : List K → Jl A) (v : PairsModel K V I D) : Jl A := size (keys v)

/--
Julia source: base/iterators.jl:298-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@eval @propagate_inbounds function _pairs_elt(p::Pairs{K, V}, idx) where {K, V}
    return $(Expr(:new, :(Pair{K, V}), :idx, :(getfield(p, :data)[idx])))
end
```
-/
def pairsElement {K V I D : Type} (getfield : D → I → Jl V) (p : PairsModel K V I D) (idx : I) : Jl (I × V) := do
  pure (idx, ← getfield p.data idx)

/--
Julia source: base/iterators.jl:302-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function iterate(p::Pairs{K, V}, state...) where {K, V}
    x = iterate(keys(p), state...)
    x === nothing && return x
    idx, next = x
    return (_pairs_elt(p, idx), next)
end
```
-/
def iteratePairsModel {K V I D S : Type} (keys : PairsModel K V I D → I)
    (iterate : I → Option S → Jl (Option (I × S)))
    (element : PairsModel K V I D → I → Jl (I × V))
    (p : PairsModel K V I D) (state : Option S) : Jl (Option ((I × V) × S)) := do
  match ← iterate (keys p) state with
  | none => pure none
  | some (idx, next) => pure (some (← element p idx, next))

/--
Julia source: base/iterators.jl:309-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function iterate(r::Reverse{<:Pairs}, state=(reverse(keys(r.itr)),))
    x = iterate(state...)
    x === nothing && return x
    idx, next = x
    return (_pairs_elt(r.itr, idx), (state[1], next))
end
```
-/
def iterateReversePairs {K V I D Ks R S : Type} (keys : PairsModel K V I D → Ks)
    (reverseKeys : Ks → R) (iterate : R → Option S → Jl (Option (I × S)))
    (element : PairsModel K V I D → I → Jl (I × V))
    (r : Reverse (PairsModel K V I D)) (state : Option (R × S) := none) :
    Jl (Option ((I × V) × (R × S))) := do
  let (rks, rest) := match state with
    | none => (reverseKeys (keys r.itr), none)
    | some (rks, s) => (rks, some s)
  match ← iterate rks rest with
  | none => pure none
  | some (idx, next) => pure (some (← element r.itr idx, (rks, next)))

/--
Julia source: base/iterators.jl:316-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(v::Pairs, state...) = isdone(keys(v), state...)
```
-/
def isdonePairsModel {K V I D S : Type} (isdone : I → Option S → Jl (Option Bool))
    (keys : PairsModel K V I D → I) (v : PairsModel K V I D) (state : Option S) : Jl (Option Bool) :=
  isdone (keys v) state

/--
Julia source: base/iterators.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Pairs{<:Any, <:Any, I}}) where {I} = IteratorSize(I)
```
-/
def sourceMethod318 {K V I D : Type} (iteratorSize : IteratorSizeTag)
    (_ : PairsModel K V I D) : IteratorSizeTag := iteratorSize

/--
Julia source: base/iterators.jl:319-319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Pairs{<:Any, <:Any, <:AbstractUnitRange, <:Tuple}}) = HasLength()
```
-/
def sourceMethod319 {K V I D : Type} (_ : PairsModel K V I D) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:321-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function last(v::Pairs{K, V}) where {K, V}
    idx = last(keys(v))
    return Pair{K, V}(idx, v[idx])
end
```
-/
def lastPairs {K V I D : Type} (keys : PairsModel K V I D → List K)
    (lastKey : List K → Jl K) (element : PairsModel K V I D → K → Jl (K × V))
    (v : PairsModel K V I D) : Jl (K × V) := do
  element v (← lastKey (keys v))

/--
Julia source: base/iterators.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haskey(v::Pairs, key) = key in keys(v)
```
-/
def haskeyPairsModel {K V I D : Type} (keys : PairsModel K V I D → List K) (contains : List K → K → Bool)
    (v : PairsModel K V I D) (key : K) : Bool := contains (keys v) key

/--
Julia source: base/iterators.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(v::Pairs) = getfield(v, :itr) === nothing ? keys(getfield(v, :data)) : getfield(v, :itr)
```
-/
def keysPairs {K V I D : Type} (keysData : D → List K) (indices : I → List K)
    (v : PairsModel K V I D) : List K :=
  match v.itr with | none => keysData v.data | some itr => indices itr

/--
Julia source: base/iterators.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
values(v::Pairs) = getfield(v, :data) # TODO: this should be a view of data subset by itr
```
-/
def valuesPairsModel {K V I D : Type} (v : PairsModel K V I D) : D := v.data

/--
Julia source: base/iterators.jl:329-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(v::Pairs, key) = values(v)[key]
```
-/
def getindexPairsModel {K V I D R : Type} (getindex : D → K → Jl R)
    (v : PairsModel K V I D) (key : K) : Jl R := getindex v.data key

/--
Julia source: base/iterators.jl:330-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(v::Pairs, value, key) = (values(v)[key] = value; v)
```
-/
def setindexPairsModel {K V I D R : Type} (setindex : D → K → R → Jl D)
    (v : PairsModel K V I D) (value : R) (key : K) : Jl (PairsModel K V I D) := do
  pure { v with data := ← setindex v.data key value }

/--
Julia source: base/iterators.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(v::Pairs, key, default) = get(values(v), key, default)
```
-/
def getPairsModel {K V I D R : Type} (get : D → K → R → Jl R)
    (v : PairsModel K V I D) (key : K) (default : R) : Jl R := get v.data key default

/--
Julia source: base/iterators.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Base.Callable, v::Pairs, key) = get(f, values(v), key)
```
-/
def getPairsWithFunction {F K V I D R : Type} (get : F → D → K → Jl R)
    (f : F) (v : PairsModel K V I D) (key : K) : Jl R := get f v.data key

/--
Julia source: base/iterators.jl:379-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip(a...) = Zip(a)
```
-/
def zipModel {Is : Type u} (a : Is) : Zip Is := ⟨a⟩

/--
Julia source: base/iterators.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_min_length(is::Tuple{}) = nothing
```
-/
def sourceMethod394 : Jl (Option Nat) := pure none

/--
Julia source: base/iterators.jl:385-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _zip_min_length(is)
    i = is[1]
    n = _zip_min_length(tail(is))
    if IteratorSize(i) isa IsInfinite
        return n
    else
        return n === nothing ? length(i) : min(n, length(i))
    end
end
```
-/
def sourceMethod385 {α S : Type} (itr : IteratorModel α S) (rest : List (IteratorModel α S)) : Jl (Option Nat) := do
  let n ← match rest with
    | [] => sourceMethod394
    | next :: tail => sourceMethod385 next tail
  if itr.iteratorSize == .isInfinite then pure n else
    match n with
    | none => pure (some (← itr.length))
    | some n => pure (some (min n (← itr.length)))

/--
Julia source: base/iterators.jl:380-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(z::Zip)
    n = _zip_min_length(z.is)
    n === nothing && throw(ArgumentError("iterator is of undefined length"))
    return n
end
```
-/
def zipLength {α S : Type} (z : Zip (List (IteratorModel α S))) : Jl Nat := do
  let n ← match z.is with
    | [] => sourceMethod394
    | itr :: rest => sourceMethod385 itr rest
  match n with
  | none => .error (.argumentError "iterator is of undefined length")
  | some n => pure n

/--
Julia source: base/iterators.jl:401-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _zip_lengths_finite_equal(is)
    i = is[1]
    if IteratorSize(i) isa Union{IsInfinite, SizeUnknown}
        return (false, nothing)
    else
        m = length(i)
        b, n = _zip_lengths_finite_equal(tail(is))
        return (b && (n === nothing || n == m), m)
    end
end
```
-/
def zipLengthsFiniteEqual {α S : Type} : List (IteratorModel α S) → Jl (Bool × Option Nat)
  | [] => pure (true, none)
  | itr :: rest =>
      if itr.iteratorSize == .isInfinite || itr.iteratorSize == .sizeUnknown then pure (false, none)
      else do
        let m ← itr.length
        let (same, n) ← zipLengthsFiniteEqual rest
        pure (same && (n.isNone || n = some m), some m)

/--
Julia source: base/iterators.jl:411-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_lengths_finite_equal(is::Tuple{}) = (true, nothing)
```
-/
def zipLengthsFiniteEqualEmpty : Bool × Option Nat := (true, none)

/--
Julia source: base/iterators.jl:414-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_tuple_shape((a,)::Tuple{OneTo}, (b,)::Tuple{OneTo}) = (intersect(a, b),)
```
-/
def sourceMethod414 (intersect : Nat → Nat → Nat) (a b : Nat) : List Nat :=
  [intersect a b]

/--
Julia source: base/iterators.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_tuple_shape((m,)::Tuple{Integer}, (n,)::Tuple{Integer}) = (min(m, n),)
```
-/
def sourceMethod415 (m n : Nat) : List Nat := [min m n]

/--
Julia source: base/iterators.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_tuple_shape(a, b) = promote_shape(a, b)
```
-/
def sourceMethod416 {A : Type} (promoteShape : A → A → Jl A) (a b : A) : Jl A :=
  promoteShape a b

/--
Julia source: base/iterators.jl:418-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_tuple_shape(a) = a
```
-/
def sourceMethod418 {A : Type} (a : A) : A := a

/--
Julia source: base/iterators.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_tuple_shape(a, b...) = _promote_tuple_shape(a, _promote_tuple_shape(b...))
```
-/
def sourceMethod417 {A : Type} (promoteShape : A → A → Jl A) (a : A) (rest : List A) : Jl A := do
  match rest with
  | [] => pure (sourceMethod418 a)
  | b :: bs => sourceMethod416 promoteShape a (← sourceMethod417 promoteShape b bs)

/--
Julia source: base/iterators.jl:412-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(z::Zip) = _promote_tuple_shape(Base.map(size, z.is)...)
```
-/
def sourceMethod412 {I A : Type} (size : I → Jl (List A))
    (promoteShape : List A → List A → Jl (List A)) (z : Zip (List I)) : Jl (List A) := do
  match ← z.is.mapM size with
  | [] => pure []
  | a :: rest => sourceMethod417 promoteShape a rest

/--
Julia source: base/iterators.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(z::Zip) = _promote_tuple_shape(Base.map(axes, z.is)...)
```
-/
def sourceMethod413 {I A : Type} (axes : I → Jl (List A))
    (promoteShape : List A → List A → Jl (List A)) (z : Zip (List I)) : Jl (List A) := do
  match ← z.is.mapM axes with
  | [] => pure []
  | a :: rest => sourceMethod417 promoteShape a rest

/--
Julia source: base/iterators.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Zip{Is}}) where {N, Is<:Tuple{Vararg{Any, N}}} = TupleOrBottom(ntuple(n -> eltype(fieldtype(Is, n)), N)...)
```
-/
def sourceMethod425 {Is T : Type} (fieldTypes : Is → List T) (eltype : T → Type)
    (tupleOrBottom : List Type → Type) (z : Zip Is) : Type :=
  tupleOrBottom ((fieldTypes z.is).map eltype)

/--
Julia source: base/iterators.jl:463-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_all_missing(::Tuple{}) = true
```
-/
def sourceMethod463 : Bool := true

/--
Julia source: base/iterators.jl:462-462 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_all_missing(ds::Tuple) = ds[1] === missing && _zip_all_missing(tail(ds))
```
-/
def sourceMethod462 : List (Option Bool) → Bool
  | [] => sourceMethod463
  | d :: ds => d.isNone && sourceMethod462 ds

/--
Julia source: base/iterators.jl:472-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_iterate_in_order(::Tuple{}, ::Tuple{}) = ()
```
-/
def zipIterateInOrderEmpty {α S : Type} : Option (List α × List (Option S)) := some ([], [])

/--
Julia source: base/iterators.jl:485-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_iterate_unknown(::Tuple{}, ::Tuple{}, ::Tuple{}) = ()
```
-/
def sourceMethod485 {α S : Type} : List (Option (α × S)) := []

/--
Julia source: base/iterators.jl:478-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _zip_iterate_unknown(is::Tuple, ss::Tuple, ds::Tuple)
    x = ds[1] === missing ? iterate(is[1], ss[1]...) : _ZipSkip()
    x === nothing && return nothing
    y = _zip_iterate_unknown(tail(is), tail(ss), tail(ds))
    y === nothing && return nothing
    return (x, y)
end
```
-/
def sourceMethod478 {I α S : Type} (is : List I) (states : List (Option S))
    (checks : List (Option Bool)) (iterate : I → Option S → Jl (Option (α × S))) :
    Jl (Option (List (Option (α × S)))) := do
  match is, states, checks with
  | [], [], [] => pure (some sourceMethod485)
  | itr :: itrs, state :: restStates, check :: restChecks => do
      let next : Option (Option (α × S)) ←
        if check.isNone then do
          match ← iterate itr state with
          | none => pure none
          | some value => pure (some (some value))
        else pure (some none)
      match next with
      | none => pure none
      | some entry =>
          match ← sourceMethod478 itrs restStates restChecks iterate with
          | none => pure none
          | some rest => pure (some (entry :: rest))
  | _, _, _ => pure none

/--
Julia source: base/iterators.jl:494-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_iterate_rest(::Tuple{}, ::Tuple{}, ::Tuple{}) = ()
```
-/
def sourceMethod494 {I : Type} : List I := []

/--
Julia source: base/iterators.jl:487-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _zip_iterate_rest(is::Tuple, ss::Tuple, xs::Tuple)
    x = xs[1] isa _ZipSkip ? iterate(is[1], ss[1]...) : xs[1]
    x === nothing && return nothing
    y = _zip_iterate_rest(tail(is), tail(ss), xs[2])
    y === nothing && return nothing
    return (x, y...)
end
```
-/
def sourceMethod487 {I α S : Type} (is : List I) (states : List (Option S))
    (values : List (Option (α × S))) (iterate : I → Option S → Jl (Option (α × S))) :
    Jl (Option (List (α × S))) := do
  match is, states, values with
  | [], [], [] => pure (some sourceMethod494)
  | itr :: itrs, state :: restStates, value :: restValues => do
      let next ← match value with | none => iterate itr state | some x => pure (some x)
      match next with
      | none => pure none
      | some x =>
          match ← sourceMethod487 itrs restStates restValues iterate with
          | none => pure none
          | some rest => pure (some (x :: rest))
  | _, _, _ => pure none

/--
Julia source: base/iterators.jl:501-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_isdone(::Tuple{}, ::Tuple{}) = (false, ())
```
-/
def sourceMethod501 : Bool × List (Option Bool) := (false, [])

/--
Julia source: base/iterators.jl:496-500 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _zip_isdone(is::Tuple, ss::Tuple)
    d = isdone(is[1], ss[1]...)
    d´, ds = _zip_isdone(tail(is), tail(ss))
    return (d === true || d´, (d, ds...))
end
```
-/
def sourceMethod496 {I S : Type} (is : List I) (states : List (Option S))
    (isdone : I → Option S → Jl (Option Bool)) : Jl (Bool × List (Option Bool)) := do
  match is, states with
  | [], [] => pure sourceMethod501
  | itr :: itrs, state :: rest => do
      let d ← isdone itr state
      let (done, ds) ← sourceMethod496 itrs rest isdone
      pure (d == some true || done, d :: ds)
  | _, _ => pure sourceMethod501

/--
Julia source: base/iterators.jl:448-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _zip_iterate_all(is, ss)
    d, ds = _zip_isdone(is, ss)
    d && return nothing
    if _zip_all_missing(ds)
        xs = _zip_iterate_in_order(is, ss)
    else
        xs1 = _zip_iterate_unknown(is, ss, ds)
        xs1 === nothing && return nothing
        xs = _zip_iterate_rest(is, ss, xs1)
    end
    xs === nothing && return nothing
    return (Base.map(first, xs), Base.map(last, xs))
end
```
-/
def sourceMethod448 {I α S : Type} (is : List I) (states : List (Option S))
    (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S))) :
    Jl (Option (List α × List (Option S))) := do
  let (done, checks) ← sourceMethod496 is states isdone
  if done then pure none else
    if sourceMethod462 checks then zipIterateInOrder iterate (List.zip is states) else do
      match ← sourceMethod478 is states checks iterate with
      | none => pure none
      | some candidates =>
          match ← sourceMethod487 is states candidates iterate with
          | none => pure none
          | some values => pure (some (values.map Prod.fst, values.map fun pair => some pair.2))

/--
Julia source: base/iterators.jl:506-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize() = IsInfinite()
```
-/
def zipIteratorSizeEmpty : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:507-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(I) = I
```
-/
def zipIteratorSizeOne (i : IteratorSizeTag) : IteratorSizeTag := i

/--
Julia source: base/iterators.jl:508-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(a, b) = and_iteratorsize(a,b) # as `and_iteratorsize` but inherit `Union{HasLength,IsInfinite}` of the shorter iterator
```
-/
def zipIteratorSizeTwo (a b : IteratorSizeTag) : IteratorSizeTag := andIteratorSizeDispatch a b

/--
Julia source: base/iterators.jl:509-509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(::HasLength, ::IsInfinite) = HasLength()
```
-/
def zipIteratorSizeLengthInfinite (_ : IteratorSizeTag) (_ : IteratorSizeTag) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:510-510 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(::HasShape, ::IsInfinite) = HasLength()
```
-/
def zipIteratorSizeShapeInfinite (_ : IteratorSizeTag) (_ : IteratorSizeTag) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(a::IsInfinite, b) = zip_iteratorsize(b,a)
```
-/
def zipIteratorSizeInfiniteOther (a b : IteratorSizeTag) : IteratorSizeTag := zipIteratorSizePair b a

/--
Julia source: base/iterators.jl:512-512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(a::IsInfinite, b::IsInfinite) = IsInfinite()
```
-/
def zipIteratorSizeInfiniteInfinite (_ _ : IteratorSizeTag) : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:513-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(a, b, tail...) = zip_iteratorsize(a, zip_iteratorsize(b, tail...))
```
-/
def zipIteratorSizeMany (a : IteratorSizeTag) (rest : List IteratorSizeTag) : IteratorSizeTag :=
  zipIteratorSizePair a (zipIteratorSizeFold rest)

/--
Julia source: base/iterators.jl:515-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratoreltype() = HasEltype()
```
-/
def zipIteratorEltypeEmpty : IteratorEltypeTag := .hasEltype

/--
Julia source: base/iterators.jl:516-516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratoreltype(a) = a
```
-/
def zipIteratorEltypeOne (a : IteratorEltypeTag) : IteratorEltypeTag := a

/--
Julia source: base/iterators.jl:517-517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratoreltype(a, tail...) = and_iteratoreltype(a, zip_iteratoreltype(tail...))
```
-/
def zipIteratorEltypeMany (a : IteratorEltypeTag) (rest : List IteratorEltypeTag) : IteratorEltypeTag :=
  if a == .hasEltype && zipIteratorEltypeFold rest == .hasEltype then .hasEltype else .eltypeUnknown

/--
Julia source: base/iterators.jl:503-503 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{Zip{Is}}) where {N, Is<:Tuple{Vararg{Any, N}}} = zip_iteratorsize(ntuple(n -> IteratorSize(fieldtype(Is, n)), N)...)
```
-/
def zipIteratorSize {α S : Type} (z : Zip (List (IteratorModel α S))) : IteratorSizeTag :=
  match z.is.map fun itr => itr.iteratorSize with
  | [] => zipIteratorSizeEmpty
  | [tag] => zipIteratorSizeOne tag
  | a :: rest => zipIteratorSizeMany a rest

/--
Julia source: base/iterators.jl:504-504 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Zip{Is}}) where {N, Is<:Tuple{Vararg{Any, N}}} = zip_iteratoreltype(ntuple(n -> IteratorEltype(fieldtype(Is, n)), N)...)
```
-/
def zipIteratorEltype {α S : Type} (z : Zip (List (IteratorModel α S))) : IteratorEltypeTag :=
  match z.is.map fun itr => itr.iteratorEltype with
  | [] => zipIteratorEltypeEmpty
  | [tag] => zipIteratorEltypeOne tag
  | a :: rest => zipIteratorEltypeMany a rest

/--
Julia source: base/iterators.jl:519-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(z::Zip) = nth(z, length(z))
```
-/
def sourceMethod519 {I α : Type} (z : Zip (List I)) (length : List I → Jl JInt64)
    (nth : I → JInt64 → Jl α) : Jl (List α) := do
  let n ← length z.is
  z.is.mapM (fun itr => nth itr n)

/--
Julia source: base/iterators.jl:521-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reverse(z::Zip)
    if !first(_zip_lengths_finite_equal(z.is))
        throw(ArgumentError("Cannot reverse zipped iterators of unknown, infinite, or unequal lengths"))
    end
    Zip(Base.map(reverse, z.is))
end
```
-/
def reverseZipModel {T : Type} (finiteEqual : T → Jl (Bool × Option Nat))
    (reverseEach : T → T) (z : Zip T) : Jl (Zip T) := do
  let (same, _) ← finiteEqual z.is
  if same then pure ⟨reverseEach z.is⟩
  else .error (.argumentError "Cannot reverse zipped iterators of unknown, infinite, or unequal lengths")

/--
Julia source: base/iterators.jl:576-576 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter(flt, itr) = Filter(flt, itr)
```
-/
def sourceMethod576 {F I : Type} (flt : F) (itr : I) : Filter F I := ⟨flt, itr⟩

/--
Julia source: base/iterators.jl:578-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(f::Filter, state...)
    y = iterate(f.itr, state...)
    while y !== nothing
        v, s = y
        if f.flt(v)
            if y isa Tuple{Any,Any}
                return (v, s) # incorporate type information that may be improved by user-provided `f.flt`
            else
                return y
            end
        end
        y = iterate(f.itr, s)
    end
    nothing
end
```
-/
def iterateFilter {F I α S : Type} (apply : F → α → Bool)
    (iterate : I → Option S → Jl (Option (α × S))) (f : Filter F I)
    (state : Option S) : Jl (Option (α × S)) :=
  match iterate f.itr state with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some (value, next)) =>
      if apply f.flt value then .ok (some (value, next))
      else iterateFilter apply iterate f (some next)
partial_fixpoint

/--
Julia source: base/iterators.jl:594-594 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Filter{F,I}}) where {F,I} = eltype(I)
```
-/
def filterEltype {F I : Type} (eltype : Type) (_ : Filter F I) : Type := eltype

/--
Julia source: base/iterators.jl:595-595 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Filter{F,I}}) where {F,I} = IteratorEltype(I)
```
-/
def filterIteratorEltype {F I : Type} (iteratorEltype : I → IteratorEltypeTag)
    (f : Filter F I) : IteratorEltypeTag := iteratorEltype f.itr

/--
Julia source: base/iterators.jl:596-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Filter}) = SizeUnknown()
```
-/
def filterIteratorSize : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:598-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(f::Filter) = Filter(f.flt, reverse(f.itr))
```
-/
def reverseFilter {F I : Type} (reverse : I → I) (f : Filter F I) : Filter F I :=
  ⟨f.flt, reverse f.itr⟩

/--
Julia source: base/iterators.jl:599-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(f::Filter) = first(reverse(f))
```
-/
def lastFilter {F I α : Type} (first : Filter F I → Jl α) (reverse : Filter F I → Filter F I)
    (f : Filter F I) : Jl α := first (reverse f)

/--
Julia source: base/iterators.jl:641-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
accumulate(f, itr; init = Base._InitialValue()) = Accumulate(f, itr, init)
```
-/
def accumulateModel {F I T : Type} (f : F) (itr : I) (init : T) : Accumulate F I T :=
  ⟨f, itr, init⟩

/--
Julia source: base/iterators.jl:643-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::Accumulate)
    state = iterate(itr.itr)
    if state === nothing
        return nothing
    end
    val = Base.BottomRF(itr.f)(itr.init, state[1])
    return (val, (val, state[2]))
end
```
-/
def iterateAccumulateStart {I F T α S : Type} (bottomRF : T → α → α)
    (iterate : I → Option S → Jl (Option (α × S))) (itr : Accumulate F I T) :
    Jl (Option (α × (α × S))) := do
  match ← iterate itr.itr none with
  | none => pure none
  | some (value, state) =>
      let result := bottomRF itr.init value
      pure (some (result, (result, state)))

/--
Julia source: base/iterators.jl:652-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::Accumulate, state)
    nxt = iterate(itr.itr, state[2])
    if nxt === nothing
        return nothing
    end
    val = itr.f(state[1], nxt[1])
    return (val, (val, nxt[2]))
end
```
-/
def iterateAccumulateState {I F T α S : Type} (apply : F → α → α → α)
    (iterate : I → Option S → Jl (Option (α × S))) (itr : Accumulate F I T)
    (state : α × S) : Jl (Option (α × (α × S))) := do
  match ← iterate itr.itr (some state.2) with
  | none => pure none
  | some (value, next) =>
      let result := apply itr.f state.1 value
      pure (some (result, (result, next)))

/--
Julia source: base/iterators.jl:661-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(itr::Accumulate) = length(itr.itr)
```
-/
def accumulateLength {I F T N : Type} (length : I → Jl N) (itr : Accumulate F I T) : Jl N := length itr.itr

/--
Julia source: base/iterators.jl:662-662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(itr::Accumulate) = size(itr.itr)
```
-/
def accumulateSize {I F T N : Type} (size : I → Jl N) (itr : Accumulate F I T) : Jl N := size itr.itr

/--
Julia source: base/iterators.jl:664-664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Accumulate{<:Any,I}}) where {I} = IteratorSize(I)
```
-/
def accumulateIteratorSize {I F T : Type} (iteratorSize : I → IteratorSizeTag)
    (itr : Accumulate F I T) : IteratorSizeTag := iteratorSize itr.itr

/--
Julia source: base/iterators.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{<:Accumulate}) = EltypeUnknown()
```
-/
def accumulateIteratorEltype : IteratorEltypeTag := .eltypeUnknown

/--
Julia source: base/iterators.jl:696-696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest(itr,state) = Rest(itr,state)
```
-/
def restWithState {I S : Type} (itr : I) (state : S) : Rest I S := ⟨itr, state⟩

/--
Julia source: base/iterators.jl:697-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest(itr::Rest,state) = Rest(itr.itr,state)
```
-/
def restOnRest {I S T : Type} (itr : Rest I S) (state : T) : Rest I T := ⟨itr.itr, state⟩

/--
Julia source: base/iterators.jl:698-698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest(itr) = itr
```
-/
def restIdentity {I : Type} (itr : I) : I := itr

/--
Julia source: base/iterators.jl:725-730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peel(itr)
    y = iterate(itr)
    y === nothing && return y
    val, s = y
    val, rest(itr, s)
end
```
-/
def peelModel {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (rest : I → S → Rest I S) (itr : I) : Jl (Option (α × Rest I S)) := do
  match ← iterate itr none with
  | none => pure none
  | some (value, state) => pure (some (value, rest itr state))

/--
Julia source: base/iterators.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds iterate(i::Rest, st=i.st) = iterate(i.itr, st)
```
-/
def iterateRest {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (i : Rest I S) (state : Option S) : Jl (Option (α × S)) :=
  iterate i.itr (match state with | none => some i.st | some s => some s)

/--
Julia source: base/iterators.jl:733-733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(i::Rest, st...) = isdone(i.itr, st...)
```
-/
def isdoneRest {I S T : Type} (isdone : I → Option T → Jl (Option Bool))
    (i : Rest I S) (state : Option T) : Jl (Option Bool) := isdone i.itr state

/--
Julia source: base/iterators.jl:735-735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:Rest{I}}) where {I} = eltype(I)
```
-/
def sourceMethod735 {I S : Type} (eltype : Type) (_ : Rest I S) : Type := eltype

/--
Julia source: base/iterators.jl:736-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{<:Rest{I}}) where {I} = IteratorEltype(I)
```
-/
def sourceMethod736 {I S : Type} (iteratorEltype : IteratorEltypeTag)
    (_ : Rest I S) : IteratorEltypeTag := iteratorEltype

/--
Julia source: base/iterators.jl:737-737 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest_iteratorsize(a) = SizeUnknown()
```
-/
def sourceMethod737 (_ : IteratorSizeTag) : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:738-738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest_iteratorsize(::IsInfinite) = IsInfinite()
```
-/
def sourceMethod738 (_ : IteratorSizeTag) : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:739-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Rest{I}}) where {I} = rest_iteratorsize(IteratorSize(I))
```
-/
def sourceMethod739 {I S : Type} (iteratorSize : IteratorSizeTag)
    (_ : Rest I S) : IteratorSizeTag :=
  match iteratorSize with
  | .isInfinite => sourceMethod738 iteratorSize
  | _ => sourceMethod737 iteratorSize

/--
Julia source: base/iterators.jl:764-764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom(start::T, step::S) where {T,S} = Count{typeof(start+step),S}(start, step)
```
-/
def countfromTyped {A S R : Type} (add : A → S → R) (convertStart : A → R)
    (addNext : R → S → R) (start : A) (step : S) : Count R S :=
  let _ := add start step
  ⟨convertStart start, step, addNext⟩

/--
Julia source: base/iterators.jl:765-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom(start::Number, step::Number)   = Count(promote(start, step)...)
```
-/
def countfromPromoted (promote : JInt64 → JInt64 → Jl (JInt64 × JInt64))
    (start step : JInt64) : Jl (Count JInt64 JInt64) := do
  let (s, d) ← promote start step
  pure ⟨s, d, fun x y => x + y⟩

/--
Julia source: base/iterators.jl:766-766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom(start)                         = Count(start, oneunit(start))
```
-/
def countfromOneunit {T : Type} (oneunit : T → T) (add : T → T → T)
    (start : T) : Count T T := ⟨start, oneunit start, add⟩

/--
Julia source: base/iterators.jl:767-767 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom()                              = Count(1, 1)
```
-/
def countfromDefault : Count JInt64 JInt64 :=
  ⟨JInt.lit .i64 1, JInt.lit .i64 1, fun x y => x + y⟩

/--
Julia source: base/iterators.jl:770-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:Count{T}}) where {T} = T
```
-/
def countEltype {T S : Type} (_ : Count T S) : Type := T

/--
Julia source: base/iterators.jl:772-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(it::Count, state=it.start) = (state, state + it.step)
```
-/
def iterateCount {T S : Type} (it : Count T S) (state : Option T) : T × T :=
  let value := state.getD it.start
  (value, it.add value it.step)

/--
Julia source: base/iterators.jl:774-774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Count}) = IsInfinite()
```
-/
def countIteratorSize : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:781-784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Take(xs::I, n::Integer) where {I}
        n < 0 && throw(ArgumentError("Take length must be non-negative"))
        return new{I}(xs, n)
    end
```
-/
def mkTake {I : Type} (xs : I) (n : Int) : Jl (Take I) :=
  if n < 0 then .error (.argumentError "Take length must be non-negative")
  else .ok ⟨xs, n.toNat⟩

/--
Julia source: base/iterators.jl:815-815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
take(xs, n::Integer) = Take(xs, Int(n))
```
-/
def takeModel {I : Type} (xs : I) (n : Int) : Jl (Take I) := do
  let n64 ← JInt.convert .i64 n
  mkTake xs n64.val

/--
Julia source: base/iterators.jl:816-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
take(xs::Take, n::Integer) = Take(xs.xs, min(Int(n), xs.n))
```
-/
def takeTakeModel {I : Type} (xs : Take I) (n : Int) : Jl (Take I) := do
  let n64 ← JInt.convert .i64 n
  mkTake xs.xs (min n64.val xs.n)

/--
Julia source: base/iterators.jl:818-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Take{I}}) where {I} = eltype(I)
```
-/
def takeEltype (eltype : Type) {I : Type} (_ : Take I) : Type := eltype

/--
Julia source: base/iterators.jl:819-819 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Take{I}}) where {I} = IteratorEltype(I)
```
-/
def takeIteratorEltype {I : Type} (iteratorEltype : I → IteratorEltypeTag)
    (t : Take I) : IteratorEltypeTag := iteratorEltype t.xs

/--
Julia source: base/iterators.jl:820-820 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
take_iteratorsize(a) = HasLength()
```
-/
def takeIteratorSize (_ : IteratorSizeTag) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:821-821 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
take_iteratorsize(::SizeUnknown) = SizeUnknown()
```
-/
def takeIteratorSizeUnknown (_ : IteratorSizeTag) : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:822-822 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{Take{I}}) where {I} = take_iteratorsize(IteratorSize(I))
```
-/
def takeIteratorSizeOf {I : Type} (iteratorSize : I → IteratorSizeTag)
    (t : Take I) : IteratorSizeTag :=
  match iteratorSize t.xs with
  | .sizeUnknown => takeIteratorSizeUnknown .sizeUnknown
  | sz => takeIteratorSize sz

/--
Julia source: base/iterators.jl:823-823 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(t::Take) = _min_length(t.xs, 1:t.n, IteratorSize(t.xs), HasLength())
```
-/
def takeLength {I : Type} (iteratorSize : I → IteratorSizeTag)
    (length : I → Jl Nat) (t : Take I) : Jl Nat := do
  if iteratorSize t.xs == .isInfinite then pure t.n else pure (min (← length t.xs) t.n)

/--
Julia source: base/iterators.jl:824-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(t::Take) = isdone(t.xs)
```
-/
def takeIsdone {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (t : Take I) : Jl (Option Bool) := isdone t.xs none

/--
Julia source: base/iterators.jl:825-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(t::Take, state) = (state[1] <= 0) | isdone(t.xs, tail(state)...)
```
-/
def takeIsdoneState {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (t : Take I) (state : Nat × Option S) : Jl (Option Bool) := do
  let done ← isdone t.xs state.2
  pure (boolOrMissing (some (state.1 ≤ 0)) done)

/--
Julia source: base/iterators.jl:827-833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function iterate(it::Take, state=(it.n,))
    n, rest = state[1], tail(state)
    n <= 0 && return nothing
    y = iterate(it.xs, rest...)
    y === nothing && return nothing
    return y[1], (n - 1, y[2])
end
```
-/
def iterateTake {I : Type} {α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (it : Take I) (state : Option (Nat × S)) : Jl (Option (α × (Nat × S))) := do
  let (n, rest) := match state with
    | none => (it.n, none)
    | some (n, s) => (n, some s)
  if n ≤ 0 then pure none else
    match ← iterate it.xs rest with
    | none => pure none
    | some (value, next) => pure (some (value, (n - 1, next)))

/--
Julia source: base/iterators.jl:840-843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Drop(xs::I, n::Integer) where {I}
        n < 0 && throw(ArgumentError("Drop length must be non-negative"))
        return new{I}(xs, n)
    end
```
-/
def mkDrop {I : Type} (xs : I) (n : Int) : Jl (Drop I) :=
  if n < 0 then .error (.argumentError "Drop length must be non-negative")
  else .ok ⟨xs, n.toNat⟩

/--
Julia source: base/iterators.jl:871-871 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
drop(xs, n::Integer) = Drop(xs, Int(n))
```
-/
def dropModel {I : Type} (xs : I) (n : Int) : Jl (Drop I) := do
  let n64 ← JInt.convert .i64 n
  mkDrop xs n64.val

/--
Julia source: base/iterators.jl:872-872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
drop(xs::Take, n::Integer) = Take(drop(xs.xs, Int(n)), max(0, xs.n - Int(n)))
```
-/
def dropTakeModel {I : Type} (xs : Take I) (n : Int) : Jl (Take (Drop I)) := do
  let n64 ← JInt.convert .i64 n
  let dropped ← mkDrop xs.xs n64.val
  let remaining := JInt.wrap .i64 ((JInt.lit .i64 (xs.n : Int)) - n64).val
  mkTake dropped (if remaining.val > 0 then remaining.val else 0)

/--
Julia source: base/iterators.jl:873-873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
drop(xs::Drop, n::Integer) = Drop(xs.xs, Int(n) + xs.n)
```
-/
def dropDropModel {I : Type} (xs : Drop I) (n : Int) : Jl (Drop I) := do
  let n64 ← JInt.convert .i64 n
  let combined := JInt.wrap .i64 (n64.val + (JInt.lit .i64 (xs.n : Int)).val)
  mkDrop xs.xs combined.val

/--
Julia source: base/iterators.jl:875-875 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Drop{I}}) where {I} = eltype(I)
```
-/
def dropEltype (eltype : Type) {I : Type} (_ : Drop I) : Type := eltype

/--
Julia source: base/iterators.jl:876-876 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Drop{I}}) where {I} = IteratorEltype(I)
```
-/
def dropIteratorEltype {I : Type} (iteratorEltype : I → IteratorEltypeTag)
    (d : Drop I) : IteratorEltypeTag := iteratorEltype d.xs

/--
Julia source: base/iterators.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
drop_iteratorsize(::SizeUnknown) = SizeUnknown()
```
-/
def dropIteratorSizeUnknown (_ : IteratorSizeTag) : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:878-878 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
drop_iteratorsize(::Union{HasShape, HasLength}) = HasLength()
```
-/
def dropIteratorSizeFinite (_ : IteratorSizeTag) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:879-879 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
drop_iteratorsize(::IsInfinite) = IsInfinite()
```
-/
def dropIteratorSizeInfinite (_ : IteratorSizeTag) : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:880-880 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{Drop{I}}) where {I} = drop_iteratorsize(IteratorSize(I))
```
-/
def dropIteratorSizeOf {I : Type} (iteratorSize : I → IteratorSizeTag)
    (d : Drop I) : IteratorSizeTag :=
  match iteratorSize d.xs with
  | .sizeUnknown => dropIteratorSizeUnknown .sizeUnknown
  | .isInfinite => dropIteratorSizeInfinite .isInfinite
  | sz => dropIteratorSizeFinite sz

/--
Julia source: base/iterators.jl:881-881 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(d::Drop) = _diff_length(d.xs, 1:d.n, IteratorSize(d.xs), HasLength())
```
-/
def dropLength {I : Type} (iteratorSize : I → IteratorSizeTag)
    (length : I → Jl Nat) (d : Drop I) : Jl Nat := do
  let m ← length d.xs
  if iteratorSize d.xs == .isInfinite then pure m else pure (m - d.n)

/--
Julia source: base/iterators.jl:883-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(it::Drop)
    y = iterate(it.xs)
    for _ in 1:it.n
        y === nothing && return y
        y = iterate(it.xs, y[2])
    end
    y
end
```
-/
def iterateDrop {I : Type} {α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (it : Drop I) (state : Option S) : Jl (Option (α × S)) :=
  match state with
  | some _ => iterate it.xs state
  | none => dropAdvance (iterate it.xs) it.n none

/--
Julia source: base/iterators.jl:891-891 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(it::Drop, state) = iterate(it.xs, state)
```
-/
def iterateDropState {I : Type} {α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (it : Drop I) (state : S) : Jl (Option (α × S)) := iterate it.xs (some state)

/--
Julia source: base/iterators.jl:892-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(it::Drop, state) = isdone(it.xs, state)
```
-/
def isdoneDrop {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (it : Drop I) (state : S) : Jl (Option Bool) := isdone it.xs (some state)

/--
Julia source: base/iterators.jl:928-928 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
takewhile(pred,xs) = TakeWhile(pred,xs)
```
-/
def takewhileModel {I : Type} {P : Type} (pred : P) (xs : I) : TakeWhile I P := ⟨pred, xs⟩

/--
Julia source: base/iterators.jl:930-935 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(ibl::TakeWhile, itr...)
    y = iterate(ibl.xs,itr...)
    y === nothing && return nothing
    ibl.pred(y[1]) || return nothing
    y
end
```
-/
def iterateTakeWhile {I : Type} {P α S : Type} (apply : P → α → Bool)
    (iterate : I → Option S → Jl (Option (α × S))) (it : TakeWhile I P) (state : Option S) :
    Jl (Option (α × S)) := do
  match ← iterate it.xs state with
  | none => pure none
  | some y => if apply it.pred y.1 then pure (some y) else pure none

/--
Julia source: base/iterators.jl:937-937 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:TakeWhile}) = SizeUnknown()
```
-/
def takewhileIteratorSize : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:938-938 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{TakeWhile{I,P}} where P) where {I} = eltype(I)
```
-/
def takewhileEltype (eltype : Type) {I : Type} {P : Type} (_ : TakeWhile I P) : Type := eltype

/--
Julia source: base/iterators.jl:939-939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{TakeWhile{I, P}} where P) where {I} = IteratorEltype(I)
```
-/
def takewhileIteratorEltype {I : Type} {P : Type} (iteratorEltype : I → IteratorEltypeTag)
    (it : TakeWhile I P) : IteratorEltypeTag := iteratorEltype it.xs

/--
Julia source: base/iterators.jl:976-976 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dropwhile(pred,itr) = DropWhile(pred,itr)
```
-/
def dropwhileModel {I : Type} {P : Type} (pred : P) (itr : I) : DropWhile I P := ⟨pred, itr⟩

/--
Julia source: base/iterators.jl:978-978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(ibl::DropWhile,itr) = iterate(ibl.xs, itr)
```
-/
def iterateDropWhileState {I S α P : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (ibl : DropWhile I P) (state : S) : Jl (Option (α × S)) := iterate ibl.xs (some state)

/--
Julia source: base/iterators.jl:979-986 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(ibl::DropWhile)
    y = iterate(ibl.xs)
    while y !== nothing
        ibl.pred(y[1]) || break
        y = iterate(ibl.xs,y[2])
    end
    y
end
```
-/
def dropWhileLoop {I P α S : Type} (apply : P → α → Bool)
    (iterate : I → Option S → Jl (Option (α × S))) (ibl : DropWhile I P)
    (current : Option (α × S)) : Jl (Option (α × S)) :=
  match current with
  | none => .ok none
  | some (value, state) =>
      if apply ibl.pred value then
        match iterate ibl.xs (some state) with
        | .error e => .error e
        | .ok next => dropWhileLoop apply iterate ibl next
      else .ok (some (value, state))
partial_fixpoint

def iterateDropWhileStart {I P α S : Type} (apply : P → α → Bool)
    (iterate : I → Option S → Jl (Option (α × S))) (ibl : DropWhile I P) :
    Jl (Option (α × S)) := do
  dropWhileLoop apply iterate ibl (← iterate ibl.xs none)

/--
Julia source: base/iterators.jl:988-988 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:DropWhile}) = SizeUnknown()
```
-/
def dropwhileIteratorSize : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:989-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{DropWhile{I,P}}) where {I,P} = eltype(I)
```
-/
def dropwhileEltype (eltype : Type) {I : Type} {P : Type} (_ : DropWhile I P) : Type := eltype

/--
Julia source: base/iterators.jl:990-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{DropWhile{I,P}}) where {I,P} = IteratorEltype(I)
```
-/
def dropwhileIteratorEltype {I : Type} {P : Type} (iteratorEltype : I → IteratorEltypeTag)
    (it : DropWhile I P) : IteratorEltypeTag := iteratorEltype it.xs

/--
Julia source: base/iterators.jl:1016-1016 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findeach(f, it) = (k for (k, v) in pairs(it) if f(v))
```
-/
def sourceMethod1016 {K V : Type} (predicate : V → Bool) (pairs : List (K × V)) :
    FindEachModel K V := ⟨predicate, pairs⟩

/--
Julia source: base/iterators.jl:1018-1018 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findeach(it) = findeach(identity, it)
```
-/
def sourceMethod1018 {K V : Type} (identity : V → Bool) (pairs : List (K × V)) :
    FindEachModel K V := sourceMethod1016 identity pairs

/--
Julia source: base/iterators.jl:1058-1058 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cycle(xs) = Cycle(xs)
```
-/
def cycleModel {I : Type} (xs : I) : Cycle I := ⟨xs⟩

/--
Julia source: base/iterators.jl:1061-1061 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Cycle{I}}) where {I} = eltype(I)
```
-/
def cycleEltype (eltype : Type) {I : Type} (_ : Cycle I) : Type := eltype

/--
Julia source: base/iterators.jl:1062-1062 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Cycle{I}}) where {I} = IteratorEltype(I)
```
-/
def cycleIteratorEltype {I : Type} (iteratorEltype : I → IteratorEltypeTag)
    (it : Cycle I) : IteratorEltypeTag := iteratorEltype it.xs

/--
Julia source: base/iterators.jl:1063-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{Cycle{I}}) where {I} = IsInfinite() # XXX: this is false if iterator ever becomes empty
```
-/
def cycleIteratorSize : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:1065-1065 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(it::Cycle) = iterate(it.xs)
```
-/
def iterateCycle {I : Type} {α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (it : Cycle I) : Jl (Option (α × S)) := iterate it.xs none

/--
Julia source: base/iterators.jl:1066-1066 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(it::Cycle) = isdone(it.xs)
```
-/
def isdoneCycle {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (it : Cycle I) : Jl (Option Bool) := isdone it.xs none

/--
Julia source: base/iterators.jl:1067-1067 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(it::Cycle, state) = false
```
-/
def isdoneCycleState {I S : Type} (_ : I → Option S → Jl (Option Bool))
    (_ : Cycle I) (_ : S) : Jl (Option Bool) := pure (some false)

/--
Julia source: base/iterators.jl:1068-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(it::Cycle, state)
    y = iterate(it.xs, state)
    y === nothing && return iterate(it)
    y
end
```
-/
def iterateCycleState {I : Type} {α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (it : Cycle I) (state : S) : Jl (Option (α × S)) := do
  match ← iterate it.xs (some state) with
  | none => iterate it.xs none
  | some y => pure (some y)

/--
Julia source: base/iterators.jl:1074-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(it::Cycle) = Cycle(reverse(it.xs))
```
-/
def reverseCycle {I : Type} (reverse : I → I) (it : Cycle I) : Cycle I := ⟨reverse it.xs⟩

/--
Julia source: base/iterators.jl:1075-1075 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(it::Cycle) = last(it.xs)
```
-/
def lastCycle {I : Type} {α : Type} (last : I → Jl α) (it : Cycle I) : Jl α := last it.xs

/--
Julia source: base/iterators.jl:1083-1083 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repeated(x) = Repeated(x)
```
-/
def repeatedModel {O : Type} (x : O) : Repeated O := ⟨x⟩

/--
Julia source: base/iterators.jl:1111-1111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repeated(x, n::Integer) = take(repeated(x), Int(n))
```
-/
def repeatedNModel {O : Type} (x : O) (n : Int) : Jl (Take (Repeated O)) :=
  takeModel (repeatedModel x) n

/--
Julia source: base/iterators.jl:1113-1113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Repeated{O}}) where {O} = O
```
-/
def repeatedEltype {O : Type} (_ : Repeated O) : Type := O

/--
Julia source: base/iterators.jl:1115-1115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(it::Repeated, state...) = (it.x, nothing)
```
-/
def iterateRepeated {O : Type} (it : Repeated O) (_state : Option Unit) : Option (O × Unit) :=
  some (it.x, ())

/--
Julia source: base/iterators.jl:1117-1117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Repeated}) = IsInfinite()
```
-/
def repeatedIteratorSize : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:1118-1118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{<:Repeated}) = HasEltype()
```
-/
def repeatedIteratorEltype : IteratorEltypeTag := .hasEltype

/--
Julia source: base/iterators.jl:1120-1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(it::Union{Repeated,Take{<:Repeated}}) = it
```
-/
def reverseRepeated {O : Type} (it : Repeated O) : Repeated O := it

/--
Julia source: base/iterators.jl:1121-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(it::Union{Repeated,Take{<:Repeated}}) = first(it)
```
-/
def lastRepeated {O : Type} (first : Repeated O → Jl O) (it : Repeated O) : Jl O := first it

/--
Julia source: base/iterators.jl:1148-1148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
product(iters...) = ProductIterator(iters)
```
-/
def productModel {T : Type} (iters : T) : ProductIterator T := ⟨iters⟩

/--
Julia source: base/iterators.jl:1150-1150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{ProductIterator{Tuple{}}}) = HasShape{0}()
```
-/
def sourceMethod1150 : IteratorSizeTag := .hasShape 0

/--
Julia source: base/iterators.jl:1151-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{ProductIterator{T}}) where {N, T<:Tuple{Vararg{Any, N}}} =
    prod_iteratorsize(ntuple(n -> IteratorSize(fieldtype(T, n)), N)..., HasShape{0}())
```
-/
def sourceMethod1151 (traits : List IteratorSizeTag) : IteratorSizeTag :=
  productIteratorSizeFold traits

/--
Julia source: base/iterators.jl:1154-1154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize() = HasShape{0}()
```
-/
def sourceMethod1154 : IteratorSizeTag := .hasShape 0

/--
Julia source: base/iterators.jl:1155-1155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(I) = I
```
-/
def sourceMethod1155 (trait : IteratorSizeTag) : IteratorSizeTag := trait

/--
Julia source: base/iterators.jl:1157-1157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(::HasLength, ::HasLength) = HasShape{2}()
```
-/
def sourceMethod1157 : IteratorSizeTag := .hasShape 2

/--
Julia source: base/iterators.jl:1158-1158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(::HasLength, ::HasShape{N}) where {N} = HasShape{N+1}()
```
-/
def sourceMethod1158 (n : Nat) : IteratorSizeTag := .hasShape (n + 1)

/--
Julia source: base/iterators.jl:1159-1159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(::HasShape{N}, ::HasLength) where {N} = HasShape{N+1}()
```
-/
def sourceMethod1159 (n : Nat) : IteratorSizeTag := .hasShape (n + 1)

/--
Julia source: base/iterators.jl:1160-1160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(::HasShape{M}, ::HasShape{N}) where {M,N} = HasShape{M+N}()
```
-/
def sourceMethod1160 (m n : Nat) : IteratorSizeTag := .hasShape (m + n)

/--
Julia source: base/iterators.jl:1163-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(::IsInfinite, ::IsInfinite) = IsInfinite()
```
-/
def sourceMethod1163 : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:1164-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(a, ::IsInfinite) = IsInfinite()
```
-/
def sourceMethod1164 (_ : IteratorSizeTag) : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:1165-1165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(::IsInfinite, b) = IsInfinite()
```
-/
def sourceMethod1165 (_ : IteratorSizeTag) : IteratorSizeTag := .isInfinite

/--
Julia source: base/iterators.jl:1166-1166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(a, b) = SizeUnknown()
```
-/
def sourceMethod1166 (_ _ : IteratorSizeTag) : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:1167-1167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(a, b, tail...) = prod_iteratorsize(a, prod_iteratorsize(b, tail...))
```
-/
def sourceMethod1167 (traits : List IteratorSizeTag) : IteratorSizeTag :=
  match traits with
  | [] => .hasShape 0
  | [one] => productIteratorSizePair one (.hasShape 0)
  | first :: rest => productIteratorSizePair first (sourceMethod1167 rest)

/--
Julia source: base/iterators.jl:1170-1170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size(::Tuple{}) = ()
```
-/
def sourceMethod1170 : List Nat := []

/--
Julia source: base/iterators.jl:1172-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size1(a, ::HasShape)  = size(a)
```
-/
def sourceMethod1172 {I : Type} (size : I → Jl (List Nat)) (item : I)
    (_ : IteratorSizeTag) : Jl (List Nat) := size item

/--
Julia source: base/iterators.jl:1173-1173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size1(a, ::HasLength) = (length(a),)
```
-/
def sourceMethod1173 {I : Type} (length : I → Jl Nat) (item : I)
    (_ : IteratorSizeTag) : Jl (List Nat) := do pure [← length item]

/--
Julia source: base/iterators.jl:1174-1175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size1(a, A) =
    throw(ArgumentError(LazyString("Cannot compute size for object of type ", typeof(a))))
```
-/
def sourceMethod1174 {I : Type} (_ : I) (_ : IteratorSizeTag) : Jl (List Nat) :=
  .error (.argumentError "Cannot compute size for iterator")

/--
Julia source: base/iterators.jl:1171-1171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size(t::Tuple) = (_prod_size1(t[1], IteratorSize(t[1]))..., _prod_size(tail(t))...)
```
-/
def sourceMethod1171 {I : Type} (size : I → Jl (List Nat)) (length : I → Jl Nat)
    (trait : I → IteratorSizeTag) : List I → Jl (List Nat)
  | [] => pure sourceMethod1170
  | item :: rest => do
      let first ← match trait item with
        | .hasShape d => sourceMethod1172 size item (.hasShape d)
        | .hasLength => sourceMethod1173 length item .hasLength
        | sz => sourceMethod1174 item sz
      pure (first ++ (← sourceMethod1171 size length trait rest))

/--
Julia source: base/iterators.jl:1169-1169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(P::ProductIterator) = _prod_size(P.iterators)
```
-/
def sourceMethod1169 {I : Type} (size : I → Jl (List Nat)) (length : I → Jl Nat)
    (trait : I → IteratorSizeTag) (p : ProductIterator (List I)) : Jl (List Nat) :=
  sourceMethod1171 size length trait p.iterators

/--
Julia source: base/iterators.jl:1178-1178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_indices(::Tuple{}) = ()
```
-/
def sourceMethod1178 : List Nat := []

/--
Julia source: base/iterators.jl:1180-1180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_axes1(a, ::HasShape)  = axes(a)
```
-/
def sourceMethod1180 {I : Type} (axes : I → Jl (List Nat)) (item : I)
    (_ : IteratorSizeTag) : Jl (List Nat) := axes item

/--
Julia source: base/iterators.jl:1181-1181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_axes1(a, ::HasLength) = (OneTo(length(a)),)
```
-/
def sourceMethod1181 {I : Type} (length : I → Jl Nat) (item : I)
    (_ : IteratorSizeTag) : Jl (List Nat) := do pure [← length item]

/--
Julia source: base/iterators.jl:1182-1183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_axes1(a, A) =
    throw(ArgumentError(LazyString("Cannot compute indices for object of type ", typeof(a))))
```
-/
def sourceMethod1182 {I : Type} (_ : I) (_ : IteratorSizeTag) : Jl (List Nat) :=
  .error (.argumentError "Cannot compute indices for iterator")

/--
Julia source: base/iterators.jl:1179-1179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_indices(t::Tuple) = (_prod_axes1(t[1], IteratorSize(t[1]))..., _prod_indices(tail(t))...)
```
-/
def sourceMethod1179 {I : Type} (axes : I → Jl (List Nat)) (length : I → Jl Nat)
    (trait : I → IteratorSizeTag) : List I → Jl (List Nat)
  | [] => pure sourceMethod1178
  | item :: rest => do
      let first ← match trait item with
        | .hasShape d => sourceMethod1180 axes item (.hasShape d)
        | .hasLength => sourceMethod1181 length item .hasLength
        | sz => sourceMethod1182 item sz
      pure (first ++ (← sourceMethod1179 axes length trait rest))

/--
Julia source: base/iterators.jl:1177-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(P::ProductIterator) = _prod_indices(P.iterators)
```
-/
def sourceMethod1177 {I : Type} (axes : I → Jl (List Nat)) (length : I → Jl Nat)
    (trait : I → IteratorSizeTag) (p : ProductIterator (List I)) : Jl (List Nat) :=
  sourceMethod1179 axes length trait p.iterators

/--
Julia source: base/iterators.jl:1185-1185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ndims(p::ProductIterator) = length(axes(p))
```
-/
def sourceMethod1185 {I : Type} (axes : List I → Jl (List Nat))
    (p : ProductIterator (List I)) : Jl Nat := do pure (← axes p.iterators).length

/--
Julia source: base/iterators.jl:1186-1186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(P::ProductIterator) = reduce(checked_mul, size(P); init=1)
```
-/
def productLength {T : Type}
    (size : T → Jl (List JInt64))
    (reduce : (JInt64 → JInt64 → Jl JInt64) → List JInt64 → JInt64 → Jl JInt64)
    (checkedMul : JInt64 → JInt64 → Jl JInt64) (p : ProductIterator T) : Jl JInt64 := do
  reduce checkedMul (← size p.iterators) (JInt.lit .i64 1)

/--
Julia source: base/iterators.jl:1188-1188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{ProductIterator{Tuple{}}}) = HasEltype()
```
-/
def sourceMethod1188 : IteratorEltypeTag := .hasEltype

/--
Julia source: base/iterators.jl:1189-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{ProductIterator{Tuple{I}}}) where {I} = IteratorEltype(I)
```
-/
def sourceMethod1189 {I : Type} (trait : I → IteratorEltypeTag) (item : I) : IteratorEltypeTag :=
  trait item

/--
Julia source: base/iterators.jl:1191-1195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function IteratorEltype(::Type{ProductIterator{T}}) where {N, T<:Tuple{Vararg{Any, N}}}
    E = ntuple(n -> IteratorEltype(fieldtype(T, n)), N)
    any(I -> I == EltypeUnknown(), E) && return EltypeUnknown()
    return E[end]
end
```
-/
def productIteratorEltype {T : Type} (traits : T → List IteratorEltypeTag)
    (p : ProductIterator T) : IteratorEltypeTag := productEltypeFold (traits p.iterators)

/--
Julia source: base/iterators.jl:1198-1198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_eltype(::Type{Tuple{}}) = Tuple{}
```
-/
def sourceMethod1198 : List Type := []

/--
Julia source: base/iterators.jl:1199-1199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_eltype(::Type{I}) where {N, I<:Tuple{Vararg{Any, N}}} = TupleOrBottom(ntuple(n -> eltype(fieldtype(I, n)), N)...)
```
-/
def sourceMethod1199 {I : Type} (eltype : I → Type) (items : List I)
    (tupleOrBottom : List Type → Type) : Type := tupleOrBottom (items.map eltype)

/--
Julia source: base/iterators.jl:1197-1197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{ProductIterator{I}}) where {I} = _prod_eltype(I)
```
-/
def sourceMethod1197 {I : Type} (eltype : I → Type) (p : ProductIterator (List I))
    (tupleOrBottom : List Type → Type) : Type :=
  match p.iterators with
  | [] => tupleOrBottom sourceMethod1198
  | items => sourceMethod1199 eltype items tupleOrBottom

/--
Julia source: base/iterators.jl:1201-1201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(::ProductIterator{Tuple{}}) = (), true
```
-/
def iterateEmptyProduct {α : Type} : List α × Bool := ([], true)

/--
Julia source: base/iterators.jl:1202-1202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(::ProductIterator{Tuple{}}, state) = nothing
```
-/
def iterateEmptyProductState {S : Type} (_ : S) : Option (List α × Bool) := none

/--
Julia source: base/iterators.jl:1204-1204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(P::ProductIterator) = any(isdone, P.iterators)
```
-/
def isdoneProduct {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (p : ProductIterator (List I)) : Jl (Option Bool) :=
  zipAnyIsdone isdone (p.iterators.map fun itr => (itr, none))

/--
Julia source: base/iterators.jl:1205-1212 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _pisdone(iters, states)
    iter1 = first(iters)
    done1 = isdone(iter1, first(states)[2]) # check step
    done1 === true || return done1 # false or missing
    done1 = isdone(iter1) # check restart
    done1 === true || return done1 # false or missing
    return _pisdone(tail(iters), tail(states)) # check tail
end
```
-/
def pisdone {I S : Type} (isdone : I → Option S → Jl (Option Bool)) :
    List (I × Option S) → Jl (Option Bool)
  | [] => .error (.methodError "_pisdone")
  | (iter1, state1) :: rest => do
      let done1 ← isdone iter1 state1
      if done1 != some true then pure done1 else
        let done1 ← isdone iter1 none
        if done1 != some true then pure done1 else pisdone isdone rest

/--
Julia source: base/iterators.jl:1213-1213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(::ProductIterator{Tuple{}}, states) = true
```
-/
def isdoneEmptyProductState {S : Type} (_ : S) : Jl (Option Bool) := pure (some true)

/--
Julia source: base/iterators.jl:1214-1214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(P::ProductIterator, states) = _pisdone(P.iterators, states)
```
-/
def isdoneProductState {I S : Type} (isdone : I → Option S → Jl (Option Bool))
    (p : ProductIterator (List I)) (states : List (I × (α × S))) : Jl (Option Bool) :=
  pisdone isdone (List.zip p.iterators (states.map fun x => some x.2.2))

/--
Julia source: base/iterators.jl:1216-1216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _piterate() = ()
```
-/
def piterateEmpty {α S I : Type} : Option (List α × List (I × (α × S))) := some ([], [])

/--
Julia source: base/iterators.jl:1217-1225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _piterate(iter1, rest...)
    next = iterate(iter1)
    next === nothing && return nothing
    restnext = _piterate(rest...)
    restnext === nothing && return nothing
    VS = @default_eltype(iter1)
    next = Pair{VS, typeof(next[2])}(next[1], next[2])
    return (next, restnext...)
end
```
-/
def piterate {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))) :
    List I → Jl (Option (List α × List (I × (α × S))))
  | [] => pure piterateEmpty
  | itr :: rest => do
      match ← iterate itr none with
      | none => pure none
      | some (value, state) =>
          match ← piterate iterate rest with
          | none => pure none
          | some (values, states) =>
              pure (some (value :: values, (itr, (value, state)) :: states))

/--
Julia source: base/iterators.jl:1226-1231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(P::ProductIterator)
    isdone(P) === true && return nothing
    next = _piterate(P.iterators...)
    next === nothing && return nothing
    return (Base.map(x -> x[1], next), next)
end
```
-/
def iterateProductStart {I α S : Type} (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S))) (p : ProductIterator (List I)) :
    Jl (Option (List α × List (I × (α × S)))) := do
  if (← isdoneProduct isdone p) == some true then pure none else piterate iterate p.iterators

/--
Julia source: base/iterators.jl:1233-1233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _piterate1(::Tuple{}, ::Tuple{}) = nothing
```
-/
def piterateNextEmpty {α S I : Type} : Option (List α × List (I × (α × S))) := none

/--
Julia source: base/iterators.jl:1234-1247 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _piterate1(iters, states)
    iter1 = first(iters)
    state1, restnext... = states
    next = iterate(iter1, state1[2])
    if next === nothing
        isdone(iter1) === true && return nothing
        restnext = _piterate1(tail(iters), restnext)
        restnext === nothing && return nothing
        next = iterate(iter1)
        next === nothing && return nothing
    end
    next = Pair{fieldtype(typeof(state1), 1), typeof(next[2])}(next[1], next[2])
    return (next, restnext...)
end
```
-/
def piterateNext {I α S : Type} (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S))) :
    List (I × (α × S)) → Jl (Option (List α × List (I × (α × S))))
  | [] => pure piterateNextEmpty
  | (itr, (_, state)) :: rest => do
      match ← iterate itr (some state) with
      | some (value, nextState) =>
          let restValues := rest.map fun x => x.2.1
          pure (some (value :: restValues, (itr, (value, nextState)) :: rest))
      | none =>
          if (← isdone itr none) == some true then pure none else
            match ← piterateNext isdone iterate rest with
            | none => pure none
            | some (values, states) =>
                match ← iterate itr none with
                | none => pure none
                | some (value, nextState) =>
                    pure (some (value :: values, (itr, (value, nextState)) :: states))

/--
Julia source: base/iterators.jl:1248-1253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(P::ProductIterator, states)
    isdone(P, states) === true && return nothing
    next = _piterate1(P.iterators, states)
    next === nothing && return nothing
    return (Base.map(x -> x[1], next), next)
end
```
-/
def iterateProductState {I α S : Type} (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S))) (p : ProductIterator (List I))
    (states : List (I × (α × S))) : Jl (Option (List α × List (I × (α × S)))) := do
  if (← isdoneProductState isdone p states) == some true then pure none
  else piterateNext isdone iterate states

/--
Julia source: base/iterators.jl:1255-1255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(p::ProductIterator) = ProductIterator(Base.map(reverse, p.iterators))
```
-/
def reverseProduct {T : Type} (reverse : T → T) (p : ProductIterator T) : ProductIterator T :=
  ⟨reverse p.iterators⟩

/--
Julia source: base/iterators.jl:1256-1256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(p::ProductIterator) = Base.map(last, p.iterators)
```
-/
def lastProduct {I α : Type} (last : I → Jl α)
    (p : ProductIterator (List I)) : Jl (List α) := p.iterators.mapM last

/--
Julia source: base/iterators.jl:1257-1257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect(a::ProductIterator, b::ProductIterator) = ProductIterator(intersect.(a.iterators, b.iterators))
```
-/
def broadcastIntersect {I J K : Type} (intersect : I → J → K) (as : List I) (bs : List J) :
    List K :=
  if as.length == bs.length then List.zipWith intersect as bs
  else match as, bs with
    | [a], _ => bs.map (intersect a)
    | _, [b] => as.map (fun a => intersect a b)
    | _, _ => List.zipWith intersect as bs

def intersectProduct {I J K : Type} (intersect : I → J → K)
    (a : ProductIterator (List I)) (b : ProductIterator (List J)) : ProductIterator (List K) :=
  ⟨broadcastIntersect intersect a.iterators b.iterators⟩

/--
Julia source: base/iterators.jl:1291-1291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten(itr) = Flatten(itr)
```
-/
def flattenModel {I : Type} (itr : I) : Flatten I := ⟨itr⟩

/--
Julia source: base/iterators.jl:1293-1293 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{Flatten{I}}) where {I} = eltype(eltype(I))
```
-/
def flattenEltype (eltype : Type) {I : Type} (_ : Flatten I) : Type := eltype

/--
Julia source: base/iterators.jl:1298-1300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eltype(::Type{Flatten{I}}) where {N, I<:Tuple{Vararg{Any, N}}}
    afoldl((T, i) -> promote_typejoin(T, eltype(i)), Union{}, ntuple(n -> fieldtype(I, n), N)...)
end
```
-/
def sourceMethod1298 (join : Type → Type → Type) (bottom : Type) (items : List Type) : Type :=
  items.foldl join bottom

/--
Julia source: base/iterators.jl:1301-1303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eltype(::Type{Flatten{I}}) where {I<:NamedTuple}
    afoldl((T, i) -> promote_typejoin(T, eltype(i)), Union{}, fieldtypes(I)...)
end
```
-/
def sourceMethod1301 (join : Type → Type → Type) (bottom : Type) (fields : List Type) : Type :=
  fields.foldl join bottom

/--
Julia source: base/iterators.jl:1307-1307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_flatteneltype(I, ::HasEltype) = IteratorEltype(eltype(I))
```
-/
def flattenHasEltype {I E : Type} (eltype : I → E)
    (iteratorEltype : E → IteratorEltypeTag) (itr : I) (_ : IteratorEltypeTag) :
    IteratorEltypeTag :=
  iteratorEltype (eltype itr)

/--
Julia source: base/iterators.jl:1308-1308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_flatteneltype(I, et) = EltypeUnknown()
```
-/
def flattenUnknownEltype {I : Type} (_ : I) (_ : IteratorEltypeTag) : IteratorEltypeTag :=
  .eltypeUnknown

/--
Julia source: base/iterators.jl:1305-1305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Flatten{I}}) where {I} = _flatteneltype(I, IteratorEltype(I))
```
-/
def flattenIteratorEltype {I E : Type} (outerEltype : I → IteratorEltypeTag)
    (eltype : I → E) (innerIteratorEltype : E → IteratorEltypeTag)
    (f : Flatten I) : IteratorEltypeTag :=
  match outerEltype f.it with
  | .hasEltype => flattenHasEltype eltype innerIteratorEltype f.it .hasEltype
  | .eltypeUnknown => flattenUnknownEltype f.it .eltypeUnknown

/--
Julia source: base/iterators.jl:1306-1306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{Flatten{Tuple{}}}) = IteratorEltype(Tuple{})
```
-/
def flattenEmptyIteratorEltype (tupleEmptyEltype : IteratorEltypeTag := .hasEltype) :
    IteratorEltypeTag := tupleEmptyEltype

/--
Julia source: base/iterators.jl:1310-1310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_iteratorsize(::Union{HasShape, HasLength}, ::Type{Union{}}) = HasLength() # length==0
```
-/
def sourceMethod1310 (_ : IteratorSizeTag) (_ : FlattenInnerKind) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:1311-1312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_iteratorsize(sz::Union{HasShape, HasLength}, ::Type{Union{}}, slurp...) =
    throw(MethodError(flatten_iteratorsize, (sz, Union{}, slurp...)))
```
-/
def sourceMethod1311 (_ : IteratorSizeTag) (_ : FlattenInnerKind) (_ : List FlattenInnerKind) :
    Jl IteratorSizeTag := .error (.methodError "flatten_iteratorsize")

/--
Julia source: base/iterators.jl:1313-1313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_iteratorsize(::Union{HasShape, HasLength}, ::Type{<:NTuple{N,Any}}) where {N} = HasLength()
```
-/
def sourceMethod1313 (_ : IteratorSizeTag) (_ : Nat) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:1314-1314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_iteratorsize(::Union{HasShape, HasLength}, ::Type{<:Tuple}) = SizeUnknown()
```
-/
def sourceMethod1314 (_ : IteratorSizeTag) (_ : FlattenInnerKind) : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:1315-1315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_iteratorsize(::Union{HasShape, HasLength}, ::Type{<:Number}) = HasLength()
```
-/
def sourceMethod1315 (_ : IteratorSizeTag) (_ : FlattenInnerKind) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:1316-1316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_iteratorsize(a, b) = SizeUnknown()
```
-/
def sourceMethod1316 (_ _ : IteratorSizeTag) : IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:1318-1318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_flatten_iteratorsize(sz, ::EltypeUnknown, I) = SizeUnknown()
```
-/
def sourceMethod1318 (_ : IteratorSizeTag) (_ : IteratorEltypeTag) (_ : FlattenInnerKind) :
    IteratorSizeTag := .sizeUnknown

/--
Julia source: base/iterators.jl:1319-1319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_flatten_iteratorsize(sz, ::HasEltype, I) = flatten_iteratorsize(sz, eltype(I))
```
-/
def sourceMethod1319 (sz : IteratorSizeTag) (_ : IteratorEltypeTag)
    (kind : FlattenInnerKind) : IteratorSizeTag :=
  match sz with
  | .hasLength | .hasShape _ =>
      match kind with
      | .bottom | .emptyTuple => sourceMethod1310 sz kind
      | .fixedTuple n => sourceMethod1313 sz n
      | .tuple => sourceMethod1314 sz kind
      | .number => sourceMethod1315 sz kind
      | .other => sourceMethod1316 sz sz
  | _ => sourceMethod1316 sz sz

/--
Julia source: base/iterators.jl:1320-1320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_flatten_iteratorsize(sz, ::HasEltype, ::Type{Tuple{}}) = HasLength()
```
-/
def sourceMethod1320 (_ : IteratorSizeTag) (_ : IteratorEltypeTag) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:1322-1322 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{Flatten{I}}) where {I} = _flatten_iteratorsize(IteratorSize(I), IteratorEltype(I), I)
```
-/
def sourceMethod1322 (outer : IteratorSizeTag) (eltypeKnown : Bool)
    (kind : FlattenInnerKind) : IteratorSizeTag :=
  if !eltypeKnown then sourceMethod1318 outer .eltypeUnknown kind
  else if kind == .emptyTuple then sourceMethod1320 outer .hasEltype
  else sourceMethod1319 outer .hasEltype kind

/--
Julia source: base/iterators.jl:1324-1324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_length(f, T::Type{Union{}}) = 0
```
-/
def flattenLengthBottom {I : Type} (_ : I) : Nat := 0

/--
Julia source: base/iterators.jl:1325-1325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_length(f, ::Type{Union{}}, slurp...) = throw(MethodError(flatten_length, (f, Union{}, slurp...)))
```
-/
def sourceMethod1325 {I α : Type} (_ : I) (_ : List α) : Jl Nat :=
  .error (.methodError "flatten_length")

/--
Julia source: base/iterators.jl:1326-1328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function flatten_length(f, T::Type{<:NTuple{N,Any}}) where {N}
    return checked_mul(N, length(f.it))
end
```
-/
def flattenLengthTuple {I : Type} (checkedMul : Nat → Nat → Jl Nat)
    (length : I → Jl Nat) (f : Flatten I) (tupleLength : Nat) : Jl Nat := do
  checkedMul tupleLength (← length f.it)

/--
Julia source: base/iterators.jl:1329-1329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_length(f, ::Type{<:Number}) = length(f.it)
```
-/
def flattenLengthNumber {I : Type} (length : I → Jl Nat) (f : I) : Jl Nat := length f

/--
Julia source: base/iterators.jl:1330-1331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_length(f, T) = throw(ArgumentError(
    "Iterates of the argument to Flatten are not known to have constant length"))
```
-/
def sourceMethod1330 : Jl Nat :=
  .error (.argumentError "Iterates of the argument to Flatten are not known to have constant length")

/--
Julia source: base/iterators.jl:1332-1332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(f::Flatten{I}) where {I} = flatten_length(f, eltype(I))
```
-/
def sourceMethod1332 {I : Type} (length : I → Jl Nat) (kind : FlattenInnerKind)
    (checkedMul : Nat → Nat → Jl Nat) (f : Flatten I) : Jl Nat :=
  match kind with
  | .bottom => pure (flattenLengthBottom f.it)
  | .emptyTuple => flattenLengthTuple checkedMul length f 0
  | .fixedTuple n => flattenLengthTuple checkedMul length f n
  | .number => flattenLengthNumber length f.it
  | .tuple | .other => sourceMethod1330

/--
Julia source: base/iterators.jl:1333-1333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(f::Flatten{Tuple{}}) = 0
```
-/
def flattenEmptyLength : Nat := 0

/--
Julia source: base/iterators.jl:1335-1352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function iterate(fl::Flatten)
    it_result = iterate(fl.it)
    it_result === nothing && return nothing

    inner_iterator, next_outer_state = it_result
    inner_it_result = iterate(inner_iterator)

    while inner_it_result === nothing
        it_result = iterate(fl.it, next_outer_state)
        it_result === nothing && return nothing

        inner_iterator, next_outer_state = it_result
        inner_it_result = iterate(inner_iterator)
    end

    item, next_inner_state = inner_it_result
    return item, (next_outer_state, inner_iterator, next_inner_state)
end
```
-/
def flattenAdvanceOuter {α O S : Type} (outer : IteratorModel (IteratorModel α S) O)
    (outerState : O) : Jl (Option (α × (O × IteratorModel α S × S))) :=
  match outer.run (some outerState) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some (inner, nextOuterState)) =>
      match inner.run none with
      | .error e => .error e
      | .ok none => flattenAdvanceOuter outer nextOuterState
      | .ok (some (value, nextInnerState)) =>
          .ok (some (value, (nextOuterState, inner, nextInnerState)))
partial_fixpoint

def iterateFlattenStart {α O S : Type} (outer : IteratorModel (IteratorModel α S) O) :
    Jl (Option (α × (O × IteratorModel α S × S))) := do
  match ← outer.run none with
  | none => pure none
  | some (inner, nextOuterState) =>
      match ← inner.run none with
      | none => flattenAdvanceOuter outer nextOuterState
      | some (value, nextInnerState) => pure (some (value, (nextOuterState, inner, nextInnerState)))

/--
Julia source: base/iterators.jl:1354-1377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function iterate(fl::Flatten, state)
    next_outer_state, inner_iterator, next_inner_state = state

    # try to advance the inner iterator
    inner_it_result = iterate(inner_iterator, next_inner_state)
    if inner_it_result !== nothing
        item, next_inner_state = inner_it_result
        return item, (next_outer_state, inner_iterator, next_inner_state)
    end

    # advance the outer iterator
    while true
        outer_it_result = iterate(fl.it, next_outer_state)
        outer_it_result === nothing && return nothing

        inner_iterator, next_outer_state = outer_it_result
        inner_it_result = iterate(inner_iterator)

        if inner_it_result !== nothing
            item, next_inner_state = inner_it_result
            return item, (next_outer_state, inner_iterator, next_inner_state)
        end
    end
end
```
-/
def iterateFlattenState {α O S : Type} (outer : IteratorModel (IteratorModel α S) O)
    (state : O × IteratorModel α S × S) :
    Jl (Option (α × (O × IteratorModel α S × S))) := do
  let (nextOuterState, inner, nextInnerState) := state
  match ← inner.run (some nextInnerState) with
  | some (value, nextInnerState) => pure (some (value, (nextOuterState, inner, nextInnerState)))
  | none => flattenAdvanceOuter outer nextOuterState

/--
Julia source: base/iterators.jl:1379-1379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(f::Flatten) = Flatten(reverse(itr) for itr in reverse(f.it))
```
-/
def sourceMethod1379 {O R I J : Type} (reverseOuter : O → R) (reverseInner : I → J)
    (f : Flatten O) : Flatten (GeneratorModel (I → J) R) :=
  flattenModel ⟨reverseInner, reverseOuter f.it, []⟩

/--
Julia source: base/iterators.jl:1380-1380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(f::Flatten) = first(reverse(f))
```
-/
def lastFlatten {I R α : Type} (first : Flatten R → Jl α)
    (reverse : Flatten I → Flatten R) (f : Flatten I) : Jl α := first (reverse f)

/--
Julia source: base/iterators.jl:1421-1421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatmap(f, c...) = flatten(map(f, c...))
```
-/
def flatmapModel {F I : Type} (f : F) (c : I) : Flatten (GeneratorModel F I) :=
  flattenModel (mapModel f c [])

/--
Julia source: base/iterators.jl:1436-1439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
""" function partition(c, n::Integer)
    n < 1 && throw(ArgumentError("cannot create partitions of length $n"))
    return PartitionIterator(c, Int(n))
end
```
-/
def partitionModel {t : IntTy} {I : Type} (c : I) (n : JInt t) : Jl (PartitionIterator I) :=
  if n.val < 1 then .error (.argumentError s!"cannot create partitions of length {n.val}")
  else do
    let n64 ← JInt.convert .i64 n.val
    pure ⟨c, n64.val.toNat⟩

/--
Julia source: base/iterators.jl:1446-1446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PartitionIterator(A::AbstractArray, n::Int) = PartitionIterator(Base.vec(A), n)
```
-/
def sourceMethod1446 {A α : Type} (vec : A → List α) (a : A) (n : Nat) :
    PartitionIterator (List α) := ⟨vec a, n⟩

/--
Julia source: base/iterators.jl:1447-1447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PartitionIterator(v::AbstractVector, n::Int) = PartitionIterator{typeof(v)}(v, n)
```
-/
def sourceMethod1447 {α : Type} (v : List α) (n : Nat) : PartitionIterator (List α) := ⟨v, n⟩

/--
Julia source: base/iterators.jl:1449-1449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{PartitionIterator{T}}) where {T} = Vector{eltype(T)}
```
-/
def sourceMethod1449 {T : Type} (elementType : Type) (_ : PartitionIterator T) : Type :=
  List elementType

/--
Julia source: base/iterators.jl:1451-1451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{PartitionIterator{T}}) where {T<:AbstractArray} = AbstractVector{eltype(T)}
```
-/
def sourceMethod1451 {T : Type} (elementType : Type) (_ : PartitionIterator T) : Type :=
  List elementType

/--
Julia source: base/iterators.jl:1453-1453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{PartitionIterator{T}}) where {T<:Vector} = Base.SubArray{eltype(T), 1, T, Tuple{UnitRange{Int}}, true}
```
-/
def sourceMethod1453 {T : Type} (viewType : Type → Type) (elementType : Type)
    (_ : PartitionIterator T) : Type := viewType elementType

/--
Julia source: base/iterators.jl:1455-1455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{PartitionIterator{T}}) where {T} = IteratorEltype(T)
```
-/
def sourceMethod1455 {T : Type} (iteratorEltype : IteratorEltypeTag)
    (_ : PartitionIterator T) : IteratorEltypeTag := iteratorEltype

/--
Julia source: base/iterators.jl:1456-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{PartitionIterator{T}}) where {T<:AbstractArray} = EltypeUnknown()
```
-/
def sourceMethod1456 {T : Type} (_ : PartitionIterator T) : IteratorEltypeTag := .eltypeUnknown

/--
Julia source: base/iterators.jl:1457-1457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{PartitionIterator{T}}) where {T<:Vector} = IteratorEltype(T)
```
-/
def sourceMethod1457 {T : Type} (iteratorEltype : IteratorEltypeTag)
    (_ : PartitionIterator T) : IteratorEltypeTag := iteratorEltype

/--
Julia source: base/iterators.jl:1459-1459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
partition_iteratorsize(::HasShape) = HasLength()
```
-/
def sourceMethod1459 (_ : IteratorSizeTag) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:1460-1460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
partition_iteratorsize(isz) = isz
```
-/
def sourceMethod1460 (iteratorSize : IteratorSizeTag) : IteratorSizeTag := iteratorSize

/--
Julia source: base/iterators.jl:1461-1463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function IteratorSize(::Type{PartitionIterator{T}}) where {T}
    partition_iteratorsize(IteratorSize(T))
end
```
-/
def sourceMethod1461 {T : Type} (iteratorSize : IteratorSizeTag)
    (_ : PartitionIterator T) : IteratorSizeTag :=
  match iteratorSize with
  | .hasShape _ => sourceMethod1459 iteratorSize
  | _ => sourceMethod1460 iteratorSize

/--
Julia source: base/iterators.jl:1465-1468 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function length(itr::PartitionIterator)
    l = length(itr.c)
    return cld(l, itr.n)
end
```
-/
def partitionLength {I : Type} (length : I → Jl Nat) (itr : PartitionIterator I) : Jl Nat := do
  let l ← length itr.c
  pure ((l + itr.n - 1) / itr.n)

/--
Julia source: base/iterators.jl:1470-1474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::PartitionIterator{<:AbstractRange}, state = firstindex(itr.c))
    state > lastindex(itr.c) && return nothing
    r = min(state + itr.n - 1, lastindex(itr.c))
    return @inbounds itr.c[state:r], r + 1
end
```
-/
def sourceMethod1470 (itr : PartitionIterator (JInt64 × JInt64))
    (state : Option JInt64 := none) : Option ((JInt64 × JInt64) × JInt64) :=
  let s := state.getD itr.c.1
  let last := itr.c.2
  if s > last then none else
    let n64 := JInt.lit .i64 (Int.ofNat itr.n)
    let sum := s + n64 - JInt.lit .i64 1
    let r := if last < sum then last else sum
    let stop := if s ≤ r then r else s - JInt.lit .i64 1
    some ((s, stop), r + JInt.lit .i64 1)

/--
Julia source: base/iterators.jl:1476-1480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::PartitionIterator{<:AbstractArray}, state = firstindex(itr.c))
    state > lastindex(itr.c) && return nothing
    r = min(state + itr.n - 1, lastindex(itr.c))
    return @inbounds Base.view(itr.c, state:r), r + 1
end
```
-/
def iteratePartitionVector {α : Type} (itr : PartitionIterator (List α))
    (state : Option Nat) : Option (List α × Nat) :=
  let start := state.getD 0
  if start ≥ itr.c.length then none else
    let stop := min (start + itr.n) itr.c.length
    some ((itr.c.drop start).take (stop - start), stop)

/--
Julia source: base/iterators.jl:1484-1502 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::PartitionIterator, state...)
    # This is necessary to remember whether we cut the
    # last element short. In such cases, we do return that
    # element, but not the next one
    state === (IterationCutShort(),) && return nothing
    v = Vector{eltype(itr.c)}(undef, itr.n)
    i = 0
    y = iterate(itr.c, state...)
    while y !== nothing
        i += 1
        v[i] = y[1]
        if i >= itr.n
            break
        end
        y = iterate(itr.c, y[2])
    end
    i === 0 && return nothing
    return resize!(v, i), y === nothing ? IterationCutShort() : y[2]
end
```
-/
def allocPartitionVector (n : Nat) : Jl Unit :=
  if n ≥ 2 ^ 63 - 2 ∨ n * 8 ≥ 2 ^ 63 - 2 then
    .error (.argumentError "invalid GenericMemory size")
  else pure ()

def sourceMethod1484 {I α S : Type} (itr : PartitionIterator I) (state : PartitionState S)
    (iterate : I → Option S → Jl (Option (α × S)))
    (allocVector : Nat → Jl Unit := allocPartitionVector) :
    Jl (Option (List α × PartitionState S)) := do
  match state with
  | .cutShort => pure none
  | .at start => do
      allocVector itr.n
      let (items, next) ← collectPartitionChunk iterate itr.c itr.n start
      if items.isEmpty then pure none else
        let nextState := match next with | none => .cutShort | some s => .at (some s)
        pure (some (items, nextState))

/--
Julia source: base/iterators.jl:1566-1568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function Stateful{<:Any, Any}(itr::T) where {T}
        return new{T, Any}(itr, iterate(itr))
    end
```
-/
def sourceMethod1566 {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (itr : I) : Jl (Stateful I (α × S)) := do
  pure ⟨itr, ← iterate itr none⟩

/--
Julia source: base/iterators.jl:1597-1603 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _approx_iter_type(itrT::Type, vstate::Type)
    vstate <: Union{Nothing, Tuple{Any, Any}} || return Any
    vstate <: Union{} && return Union{}
    itrT <: Union{} && return Union{}
    nextvstate = Base._return_type(doiterate, Tuple{itrT, vstate})
    return (nextvstate <: vstate ? vstate : Any)
end
```
-/
def sourceMethod1597 (itrIsBottom : Bool) (returnTypeDoiterate : StatefulVS → StatefulVS)
    (vstate : StatefulVS) : StatefulVS :=
  match vstate with
  | .other _ | .any => .any
  | .bottom => .bottom
  | .pairOrNothing tag =>
      if itrIsBottom then .bottom else
        let nextvstate := returnTypeDoiterate vstate
        if nextvstate == .bottom || nextvstate == .pairOrNothing tag then vstate else .any

/--
Julia source: base/iterators.jl:1589-1589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
approx_iter_type(itrT::Type) = _approx_iter_type(itrT, Base._return_type(iterate, Tuple{itrT}))
```
-/
def sourceMethod1589 (itrIsBottom : Bool) (returnTypeIterate : StatefulVS)
    (returnTypeDoiterate : StatefulVS → StatefulVS) : StatefulVS :=
  sourceMethod1597 itrIsBottom returnTypeDoiterate returnTypeIterate

/--
Julia source: base/iterators.jl:1569-1572 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function Stateful(itr::T) where {T}
        VS = approx_iter_type(T)
        return new{T, VS}(itr, iterate(itr)::VS)
    end
```
-/
def sourceMethod1569 {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (itr : I) (vs : StatefulVS := .any)
    (matchesVS : Option (α × S) → StatefulVS → Bool := fun _ v => v != .bottom) :
    Jl (Stateful I (α × S)) := do
  let state ← iterate itr none
  if matchesVS state vs then pure ⟨itr, state⟩
  else .error (.methodError "typeassert")

/--
Julia source: base/iterators.jl:1575-1578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reset!(s::Stateful)
    setfield!(s, :nextvalstate, iterate(s.itr)) # bypass convert call of setproperty!
    return s
end
```
-/
def resetStateful {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (s : Stateful I (α × S)) : Jl (Stateful I (α × S)) := do
  pure { s with nextvalstate := ← iterate s.itr none }

/--
Julia source: base/iterators.jl:1579-1583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reset!(s::Stateful{T}, itr::T) where {T}
    s.itr = itr
    reset!(s)
    return s
end
```
-/
def resetStatefulTo {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (s : Stateful I (α × S)) (itr : I) : Jl (Stateful I (α × S)) := do
  resetStateful iterate { s with itr := itr }

/--
Julia source: base/iterators.jl:1592-1596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function doiterate(itr, valstate::Union{Nothing, Tuple{Any, Any}})
    valstate === nothing && return nothing
    _, st = valstate
    return iterate(itr, st)
end
```
-/
def sourceMethod1592 {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (itr : I) : Option (α × S) → Jl (Option (α × S))
  | none => pure none
  | some (_, state) => iterate itr (some state)

/--
Julia source: base/iterators.jl:1605-1605 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Stateful(x::Stateful) = x
```
-/
def sourceMethod1605 {I S : Type} (s : Stateful I S) : Stateful I S := s

/--
Julia source: base/iterators.jl:1606-1606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Stateful}, itr) = Stateful(itr)
```
-/
def sourceMethod1606 {I S : Type} (construct : I → Jl (Stateful I S)) (itr : I) : Jl (Stateful I S) :=
  construct itr

/--
Julia source: base/iterators.jl:1607-1607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(s::Stateful, st=nothing) = s.nextvalstate === nothing
```
-/
def isdoneStateful {I V : Type} (s : Stateful I V) : Bool := s.nextvalstate.isNone

/--
Julia source: base/iterators.jl:1609-1618 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function popfirst!(s::Stateful)
    vs = s.nextvalstate
    if vs === nothing
        throw(Base.EOFError())
    else
        val, state = vs
        setfield!(s, :nextvalstate, iterate(s.itr, state))
        return val
    end
end
```
-/
def popfirstStateful {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (s : Stateful I (α × S)) : IteratorResult (α × Stateful I (α × S)) := do
  match s.nextvalstate with
  | none => .error .eofError
  | some (value, state) =>
      let next ← iterate s.itr (some state)
      pure (value, { s with nextvalstate := next })

/--
Julia source: base/iterators.jl:1620-1623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function peek(s::Stateful, sentinel=nothing)
    ns = s.nextvalstate
    return ns !== nothing ? ns[1] : sentinel
end
```
-/
def peekStateful {I α S : Type} (s : Stateful I (α × S)) (sentinel : α) : α :=
  match s.nextvalstate with | none => sentinel | some (value, _) => value

/--
Julia source: base/iterators.jl:1624-1624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline iterate(s::Stateful, state=nothing) = s.nextvalstate === nothing ? nothing : (popfirst!(s), nothing)
```
-/
def iterateStateful {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (s : Stateful I (α × S)) : IteratorResult (Option (α × Unit) × Stateful I (α × S)) := do
  if s.nextvalstate.isNone then pure (none, s) else
    let (value, next) ← popfirstStateful iterate s
    pure (some (value, ()), next)

/--
Julia source: base/iterators.jl:1625-1625 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Stateful{T}}) where {T} = IteratorSize(T) isa IsInfinite ? IsInfinite() : SizeUnknown()
```
-/
def sourceMethod1625 (underlying : IteratorSizeTag) : IteratorSizeTag :=
  if underlying == .isInfinite then .isInfinite else .sizeUnknown

/--
Julia source: base/iterators.jl:1626-1626 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:Stateful{T}}) where {T} = eltype(T)
```
-/
def sourceMethod1626 {I S : Type} (eltype : Type) (_ : Stateful I S) : Type := eltype

/--
Julia source: base/iterators.jl:1627-1627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{<:Stateful{T}}) where {T} = IteratorEltype(T)
```
-/
def sourceMethod1627 {I S : Type} (iteratorEltype : IteratorEltypeTag)
    (_ : Stateful I S) : IteratorEltypeTag := iteratorEltype

/--
Julia source: base/iterators.jl:1661-1671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _only(x, ::typeof(iterate))
    i = iterate(x)
    @boundscheck if i === nothing
        throw(ArgumentError("Collection is empty, must contain exactly 1 element"))
    end
    (ret, state) = i::NTuple{2,Any}
    @boundscheck if iterate(x, state) !== nothing
        throw(ArgumentError("Collection has multiple elements, must contain exactly 1 element"))
    end
    return ret
end
```
-/
def sourceMethod1661 {I α S : Type} (itr : I)
    (iterate : I → Option S → Jl (Option (α × S)))
    (boundscheck : Bool := true) : Jl α := do
  let i ← iterate itr none
  if boundscheck && i.isNone then
    .error (.argumentError "Collection is empty, must contain exactly 1 element")
  else
    match i with
    | none => .error (.methodError "NTuple{2,Any}")
    | some (ret, state) =>
        if boundscheck then
          match ← iterate itr (some state) with
          | none => pure ret
          | some _ => .error (.argumentError "Collection has multiple elements, must contain exactly 1 element")
        else pure ret

/--
Julia source: base/iterators.jl:1659-1659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds only(x) = _only(x, iterate)
```
-/
def onlyModel {α S : Type} (itr : IteratorModel α S) (boundscheck : Bool := true) : Jl α :=
  sourceMethod1661 itr (fun it st => it.run st) boundscheck

/--
Julia source: base/iterators.jl:1673-1678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _only(x, ::typeof(first))
    @boundscheck if length(x) != 1
        throw(ArgumentError("Collection must contain exactly 1 element"))
    end
    @inbounds first(x)
end
```
-/
def sourceMethod1673 {I α : Type} (length : I → Jl Nat) (firstInbounds : I → Jl α)
    (itr : I) (boundscheck : Bool := true) : Jl α := do
  if boundscheck && (← length itr) != 1 then
    .error (.argumentError "Collection must contain exactly 1 element")
  else firstInbounds itr

/--
Julia source: base/iterators.jl:1680-1680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds only(x::IdDict) = _only(x, first)
```
-/
def sourceMethod1680 {I α : Type} (length : I → Jl Nat) (first : I → Jl α) (itr : I) : Jl α :=
  sourceMethod1673 length first itr

/--
Julia source: base/iterators.jl:1683-1683 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
only(x::Tuple{Any}) = x[1]
```
-/
def sourceMethod1683 {α : Type} (xs : List α) : Jl α :=
  match xs with | [x] => pure x | _ => .error (.argumentError "Tuple must contain exactly 1 element")

/--
Julia source: base/iterators.jl:1684-1686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
only(x::Tuple) = throw(
    ArgumentError("Tuple contains $(length(x)) elements, must contain exactly 1 element")
)
```
-/
def sourceMethod1684 {α : Type} (xs : List α) : Jl α :=
  .error (.argumentError s!"Tuple contains {xs.length} elements, must contain exactly 1 element")

/--
Julia source: base/iterators.jl:1687-1687 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
only(x::NamedTuple{<:Any, <:Tuple{Any}}) = first(x)
```
-/
def sourceMethod1687 {α : Type} (xs : List α) : Jl α :=
  match xs with | [x] => pure x | _ => .error (.argumentError "NamedTuple must contain exactly 1 element")

/--
Julia source: base/iterators.jl:1688-1690 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
only(x::NamedTuple) = throw(
    ArgumentError("NamedTuple contains $(length(x)) elements, must contain exactly 1 element")
)
```
-/
def sourceMethod1688 {α : Type} (xs : List α) : Jl α :=
  .error (.argumentError s!"NamedTuple contains {xs.length} elements, must contain exactly 1 element")

/--
Julia source: base/iterators.jl:1704-1704 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:IterableStatePairs{T}}) where T = IteratorSize(T)
```
-/
def sourceMethod1704 {T : Type} (iteratorSize : IteratorSizeTag) (_ : IterableStatePairs T) : IteratorSizeTag :=
  iteratorSize

/--
Julia source: base/iterators.jl:1705-1705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(x::IterableStatePairs) = length(x.x)
```
-/
def iterableStatePairsLength {T α : Type} (length : T → Jl α) (x : IterableStatePairs T) : Jl α := length x.x

/--
Julia source: base/iterators.jl:1706-1706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.eltype(::Type{IterableStatePairs{T}}) where T = Pair{<:Any, eltype(T)}
```
-/
def sourceMethod1706 {T : Type} (keyType eltype : Type) (_ : IterableStatePairs T) : Type :=
  keyType × eltype

/--
Julia source: base/iterators.jl:1708-1712 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(x::IterableStatePairs, state=first(keys(x.x)))
    it = iterate(x.x, state)
    it === nothing && return nothing
    (state => first(it), last(it))
end
```
-/
def iterateIterableStatePairs {T K V S : Type} (firstKey : T → Jl S)
    (iterate : T → Option S → Jl (Option (V × S)))
    (x : IterableStatePairs T) (state : Option S) : Jl (Option ((S × V) × S)) := do
  let key ← match state with | none => firstKey x.x | some s => pure s
  match ← iterate x.x (some key) with
  | none => pure none
  | some (value, next) => pure (some ((key, value), next))

/--
Julia source: base/iterators.jl:1714-1714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(x::IterableStatePairs) = IterableStatePairs(Iterators.reverse(x.x))
```
-/
def reverseIterableStatePairs {T : Type} (reverse : T → T) (x : IterableStatePairs T) :
    IterableStatePairs T := ⟨reverse x.x⟩

/--
Julia source: base/iterators.jl:1715-1715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(x::IterableStatePairs{<:Iterators.Reverse}) = IterableStatePairs(x.x.itr)
```
-/
def reverseIterableStatePairsReverse {T : Type} (inner : T) : IterableStatePairs T := ⟨inner⟩

/--
Julia source: base/iterators.jl:1717-1721 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(x::IterableStatePairs{<:Iterators.Reverse}, state=last(keys(x.x.itr)))
    it = iterate(x.x, state)
    it === nothing && return nothing
    (state => first(it), last(it))
end
```
-/
def iterateReverseIterableStatePairs {T K V S : Type} (lastKey : T → Jl S)
    (iterate : T → Option S → Jl (Option (V × S)))
    (x : IterableStatePairs T) (state : Option S) : Jl (Option ((S × V) × S)) := do
  let key ← match state with | none => lastKey x.x | some s => pure s
  match ← iterate x.x (some key) with
  | none => pure none
  | some (value, next) => pure (some ((key, value), next))

/--
Julia source: base/iterators.jl:1725-1725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(s::AbstractString) = IterableStatePairs(s)
```
-/
def pairsStringModel {S : Type} (s : S) : IterableStatePairs S := ⟨s⟩

/--
Julia source: base/iterators.jl:1777-1787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _nth(::IteratorSize, itr, n::Integer)
    # unrolled version of `first(drop)`
    n > 0 || throw(BoundsError(itr, n))
    y = iterate(itr)
    for _ in 1:n-1
        y === nothing && break
        y = iterate(itr, y[2])
    end
    y === nothing && throw(BoundsError(itr, n))
    y[1]
end
```
-/
def nthGeneric {α S : Type} (itr : IteratorModel α S) (n : Int)
    (_ : IteratorSizeTag := itr.iteratorSize) : Jl α := do
  if n ≤ 0 then .error .boundsError else
    match ← nthAdvance itr.run (n - 1).toNat (← itr.run none) with
    | none => .error .boundsError
    | some (value, _) => pure value

/--
Julia source: base/iterators.jl:1753-1753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nth(itr, n::Integer) = _nth(IteratorSize(itr), itr, n)
```
-/
def nthModel {α S : Type} (itr : IteratorModel α S) (n : Int)
    (dispatch : IteratorSizeTag → IteratorModel α S → Int → Jl α :=
      fun sz it k => nthGeneric it k sz) : Jl α :=
  dispatch itr.iteratorSize itr n

/--
Julia source: base/iterators.jl:1754-1754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nth(itr::Cycle{I}, n::Integer) where I = _nth(IteratorSize(I), itr, n)
```
-/
def sourceMethod1754 {I α : Type} (iteratorSize : IteratorSizeTag)
    (itr : Cycle I) (n : Int)
    (nth : IteratorSizeTag → Cycle I → Int → Jl α) : Jl α := nth iteratorSize itr n

/--
Julia source: base/iterators.jl:1755-1755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nth(itr::Flatten{Take{Repeated{O}}}, n::Integer) where O = _nth(IteratorSize(O), itr, n)
```
-/
def sourceMethod1755 {O α : Type} (iteratorSize : IteratorSizeTag)
    (itr : Flatten (Take (Repeated O))) (n : Int)
    (nth : IteratorSizeTag → Flatten (Take (Repeated O)) → Int → Jl α) : Jl α :=
  nth iteratorSize itr n

/--
Julia source: base/iterators.jl:1756-1756 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds nth(itr::AbstractArray, n::Integer) = itr[begin + n - 1]
```
-/
def nthArray {t : IntTy} {α : Type} (beginIndex : JInt64)
    (getindex : JInt (IntTy.promote .i64 t) → Jl α) (n : JInt t) : Jl α :=
  let u := IntTy.promote .i64 t
  getindex (JInt.rem u beginIndex + JInt.rem u n - JInt.lit u 1)

/--
Julia source: base/iterators.jl:1758-1764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _nth(::Union{HasShape, HasLength}, itr::Cycle{I}, n::Integer) where {I}
    N = length(itr.xs)
    N == 0 && throw(BoundsError(itr, n))

    # prevents wrap around behaviour and inherit the error handling
    return nth(itr.xs, n > 0 ? mod1(n, N) : n)
end
```
-/
def sourceMethod1758 {I α : Type} (length : I → Jl Nat) (nth : I → Int → Jl α)
    (itr : Cycle I) (n : Int) : Jl α := do
  let count ← length itr.xs
  if count == 0 then .error .boundsError else
    nth itr.xs (if n > 0 then (n - 1) % Int.ofNat count + 1 else n)

/--
Julia source: base/iterators.jl:1767-1775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _nth(::Union{HasShape, HasLength}, itr::Flatten{Take{Repeated{O}}}, n::Integer) where {O}
    cycles = itr.it.n
    torepeat = itr.it.xs.x
    k = length(torepeat)
    (n > k*cycles || k == 0) && throw(BoundsError(itr, n))

    # prevent wrap around behaviour and inherit the error handling
    return nth(torepeat, n > 0 ? mod1(n, k) : n)
end
```
-/
def sourceMethod1767 {O α : Type} (length : O → Jl JInt64) (nth : O → JInt64 → Jl α)
    (itr : Flatten (Take (Repeated O))) (n : JInt64) : Jl α := do
  let cycles := JInt.lit .i64 (itr.it.n : Int)
  let torepeat := itr.it.xs.x
  let k ← length torepeat
  if n.val > (k * cycles).val || k.val == 0 then .error .boundsError else
    let index := if n.val > 0 then JInt.wrap .i64 ((n.val - 1) % k.val + 1) else n
    nth torepeat index

/--
Julia source: base/iterators.jl:1810-1810 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nth(n::Integer) = Base.Fix2(nth, n)
```
-/
def nthCurry {I N α : Type} (n : N) (nthFn : I → N → Jl α) : I → Jl α :=
  fun itr => nthFn itr n

/--
Julia source: base/iterators.jl:1789-1789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nth(::IteratorSize, z::Zip, n::Integer) = Base.map(nth(n), z.is)
```
-/
def nthZip {α S : Type} (is : List (IteratorModel α S)) (n : Int) : Jl (List α) :=
  is.mapM (nthCurry n (fun itr k => nthModel itr k))

/--
Julia source: base/iterators.jl:1059-1059 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cycle(xs, n::Integer) = flatten(repeated(xs, n))
```
-/
def cycleNModel {I : Type} (xs : I) (n : Int) : Jl (Flatten (Take (Repeated I))) := do
  pure (flattenModel (← repeatedNModel xs n))

def takeAsIterator {α S : Type} (xs : IteratorModel α S) (t : Take (IteratorModel α S)) : IteratorModel α (Nat × S) where
  run := fun state => iterateTake (fun _ s => xs.run s) t state
  isdone := fun state =>
    match state with
    | none => takeIsdone (fun _ s => xs.isdone s) t
    | some (n, s) => takeIsdoneState (fun _ st => xs.isdone st) t (n, some s)
  iteratorSize := takeIteratorSizeOf (fun _ => xs.iteratorSize) t
  iteratorEltype := xs.iteratorEltype
  length := takeLength (fun _ => xs.iteratorSize) (fun _ => xs.length) t
  size := xs.size

def dropAsIterator {α S : Type} (xs : IteratorModel α S) (d : Drop (IteratorModel α S)) : IteratorModel α S where
  run := fun state => iterateDrop (fun _ s => xs.run s) d state
  isdone := fun state => xs.isdone state
  iteratorSize := dropIteratorSizeOf (fun _ => xs.iteratorSize) d
  iteratorEltype := xs.iteratorEltype
  length := dropLength (fun _ => xs.iteratorSize) (fun _ => xs.length) d
  size := xs.size

def enumerateAsIterator {α S : Type} (xs : IteratorModel α S) : IteratorModel (JInt64 × α) (JInt64 × S) where
  run := fun state => iterateEnumerate (fun _ s => xs.run s) ⟨xs⟩ state
  isdone := fun state => xs.isdone (state.map Prod.snd)
  iteratorSize := xs.iteratorSize
  iteratorEltype := xs.iteratorEltype
  length := xs.length
  size := xs.size

def takeWhileAsIterator {α S : Type} (xs : IteratorModel α S) (p : α → Bool) : IteratorModel α S where
  run := fun state => iterateTakeWhile (fun pred x => pred x)
    (fun _ s => xs.run s) ⟨p, xs⟩ state
  isdone := fun state => xs.isdone state
  iteratorSize := .sizeUnknown
  iteratorEltype := xs.iteratorEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")


def dropWhileAsIterator {α S : Type} (xs : IteratorModel α S) (p : α → Bool) : IteratorModel α S where
  run := fun state =>
    match state with
    | none => iterateDropWhileStart (fun pred x => pred x) (fun _ s => xs.run s) ⟨p, xs⟩
    | some s => iterateDropWhileState (fun _ st => xs.run st) ⟨p, xs⟩ s
  isdone := fun state => xs.isdone state
  iteratorSize := .sizeUnknown
  iteratorEltype := xs.iteratorEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def countAsIterator {T S : Type} (it : Count T S) : IteratorModel T T where
  run := fun state => pure (some (iterateCount it state))
  isdone := fun _ => pure (some false)
  iteratorSize := .isInfinite
  iteratorEltype := .hasEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def repeatedAsIterator {α : Type} (it : Repeated α) : IteratorModel α Unit where
  run := fun state => pure (iterateRepeated it state)
  isdone := fun _ => pure (some false)
  iteratorSize := repeatedIteratorSize
  iteratorEltype := repeatedIteratorEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def cycleAsIterator {α S : Type} (it : Cycle (IteratorModel α S)) : IteratorModel α S where
  run := fun state => match state with
    | none => iterateCycle (fun _ s => (it.xs).run s) it
    | some s => iterateCycleState (fun _ st => (it.xs).run st) it s
  isdone := fun state => match state with
    | none => isdoneCycle (fun _ s => (it.xs).isdone s) it
    | some s => isdoneCycleState (fun _ st => (it.xs).isdone st) it s
  iteratorSize := .isInfinite
  iteratorEltype := it.xs.iteratorEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def flattenAsIterator {α O S : Type}
    (it : Flatten (IteratorModel (IteratorModel α S) O)) : IteratorModel α (O × IteratorModel α S × S) where
  run := fun state => match state with
    | none => iterateFlattenStart it.it
    | some s => iterateFlattenState it.it s
  isdone := fun _ => pure none
  iteratorSize := .sizeUnknown
  iteratorEltype := .eltypeUnknown
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def partitionVectorAsIterator {α : Type} (it : PartitionIterator (List α)) : IteratorModel (List α) Nat where
  run := fun state => pure (iteratePartitionVector it state)
  isdone := fun state => pure (some (state.getD 0 ≥ it.c.length))
  iteratorSize := sourceMethod1461 .hasLength it
  iteratorEltype := sourceMethod1456 it
  length := partitionLength (fun xs => pure xs.length) it
  size := do pure [← partitionLength (fun xs => pure xs.length) it]


def productAsIterator {I α S : Type} (p : ProductIterator (List I))
    (isdone : I → Option S → Jl (Option Bool))
    (iterate : I → Option S → Jl (Option (α × S))) : IteratorModel (List α) (List (I × (α × S))) where
  run := fun state => do
    match state with
    | none => iterateProductStart isdone iterate p
    | some states => iterateProductState isdone iterate p states
  isdone := fun state =>
    match state with
    | none => isdoneProduct isdone p
    | some states => isdoneProductState isdone p states
  iteratorSize := .sizeUnknown
  iteratorEltype := .hasEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")


def zipAsIterator {α S : Type} (z : Zip (List (IteratorModel α S))) : IteratorModel (List α) (List (Option S)) where
  run := fun state => match state with
    | none => iterateZipStart (fun itr st => itr.run st) z
    | some states => iterateZipState (fun itr st => itr.run st) z states
  isdone := fun state => match state with
    | none => zipIsdone (fun itr st => itr.isdone st) z
    | some states => zipIsdoneState (fun itr st => itr.isdone st) z states
  iteratorSize := .sizeUnknown
  iteratorEltype := .eltypeUnknown
  length := zipLength z
  size := .error (.argumentError "iterator size is not defined")

def filterAsIterator {α S : Type} (xs : IteratorModel α S) (p : α → Bool) : IteratorModel α S where
  run := fun state =>
    iterateFilter (fun pred value => pred value) (fun _ st => xs.run st) ⟨p, xs⟩ state
  isdone := fun state => xs.isdone state
  iteratorSize := .sizeUnknown
  iteratorEltype := xs.iteratorEltype
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def accumulateAsIterator {F α T S : Type} (xs : IteratorModel α S) (f : F)
    (apply : F → α → α → α) (init : T) (bottomRF : T → α → α) :
    IteratorModel α (α × S) where
  run := fun state => match state with
    | none => iterateAccumulateStart bottomRF (fun _ st => xs.run st) ⟨f, xs, init⟩
    | some st => iterateAccumulateState apply (fun _ state => xs.run state) ⟨f, xs, init⟩ st
  isdone := fun state => xs.isdone (state.map Prod.snd)
  iteratorSize := xs.iteratorSize
  iteratorEltype := .eltypeUnknown
  length := xs.length
  size := xs.size


def statefulCreate {I α S : Type} (iterate : I → Option S → Jl (Option (α × S)))
    (itr : I) : Jl (Stateful I (α × S)) := do
  pure ⟨itr, ← iterate itr none⟩

def nthFiniteCycle {O α : Type} (length : O → Jl JInt64) (nth : O → JInt64 → Jl α)
    (itr : Flatten (Take (Repeated O))) (n : JInt64) : Jl α := do
  let cycles := JInt.lit .i64 (itr.it.n : Int)
  let torepeat := itr.it.xs.x
  let k ← length torepeat
  if n.val > (k * cycles).val || k.val == 0 then .error .boundsError else
    let index := if n.val > 0 then JInt.wrap .i64 ((n.val - 1) % k.val + 1) else n
    nth torepeat index


def reverseListAsIterator {α : Type} (xs : List α) : IteratorModel α Int where
  run := fun state =>
    (iterateReverseTuple (fun ys => ys.length) (fun ys n =>
      match listGet ys n with | none => .error .boundsError | some x => pure x)
      (reverseDefault xs) state).map (fun result => result.map fun (x, next) => (x, next))
  isdone := fun state => pure (some ((state.getD (Int.ofNat xs.length)) < 1))
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]


def zipListModel {α : Type} (xs ys : List α) : IteratorModel (List α) (List (Option Nat)) :=
  zipAsIterator (zipModel [listIterator xs, listIterator ys])

def productListModel {α : Type} (xs ys : List α) : IteratorModel (List α)
    (List (IteratorModel α Nat × (α × Nat))) :=
  productAsIterator (productModel [listIterator xs, listIterator ys])
    (fun itr state => itr.isdone state) (fun itr state => itr.run state)

def flattenListModel {α : Type} (rows : List (List α)) :
    IteratorModel α (Nat × IteratorModel α Nat × Nat) :=
  flattenAsIterator (flattenModel (listIterator (rows.map listIterator)))

def cycleOuter {α : Type} (xs : List α) (n : Nat) : IteratorModel (IteratorModel α Nat) (Nat × Unit) :=
  let repeated := repeatedAsIterator (repeatedModel (listIterator xs))
  takeAsIterator repeated ⟨repeated, n⟩

def finiteCycleListModel {α : Type} (xs : List α) (n : Nat) :
    IteratorModel α ((Nat × Unit) × IteratorModel α Nat × Nat) :=
  flattenAsIterator (flattenModel (cycleOuter xs n))

def repeatedListModel {α : Type} (x : α) (n : Nat) : IteratorModel α (Nat × Unit) :=
  let repeated := repeatedAsIterator (repeatedModel x)
  takeAsIterator repeated ⟨repeated, n⟩

def restAsIterator {α S : Type} (r : Rest (IteratorModel α S) S) : IteratorModel α S where
  run := fun state => iterateRest (fun itr st => itr.run st) r state
  isdone := fun state => isdoneRest (fun itr st => itr.isdone st) r state
  iteratorSize := sourceMethod739 r.itr.iteratorSize r
  iteratorEltype := sourceMethod736 r.itr.iteratorEltype r
  length := .error (.argumentError "iterator is of undefined length")
  size := .error (.argumentError "iterator is of undefined size")

def pairsListAsIterator {α : Type} (xs : List α) : IteratorModel (Nat × α) Nat where
  run := fun state =>
    let p : PairsModel Nat α Nat (List α) := pairsLinear (K := Nat) (V := α) (fun _ => 0) xs
    iteratePairsModel (fun _ => 0)
      (fun _ st => do
        let i := st.getD 0
        match listGet xs i with
        | none => pure none
        | some _ => pure (some (i, i + 1)))
      (pairsElement (fun ys i =>
        match listGet ys i with
        | none => .error .boundsError
        | some v => pure v))
      p state
  isdone := fun state => pure (some (xs.length ≤ state.getD 0))
  iteratorSize := sourceMethod319 (pairsLinear (K := Nat) (V := α) (fun _ => 0) xs)
  iteratorEltype := .hasEltype
  length := pairsLength (V := α) (keysPairs (fun ys => List.range ys.length) (fun _ => List.range xs.length))
    (fun ks => pure ks.length) (pairsLinear (K := Nat) (V := α) (fun _ => 0) xs)
  size := pairsSize (V := α) (keysPairs (fun ys => List.range ys.length) (fun _ => List.range xs.length))
    (fun ks => pure [ks.length]) (pairsLinear (K := Nat) (V := α) (fun _ => 0) xs)

def iterableStatePairsAsIterator {α : Type} (xs : List α) : IteratorModel (Nat × α) Nat where
  run := fun state =>
    iterateIterableStatePairs (K := Nat) (fun _ => pure 0)
      (fun ys st => (listIterator ys).run st) (pairsStringModel xs) state
  isdone := fun state => (listIterator xs).isdone state
  iteratorSize := sourceMethod1704 .hasLength (pairsStringModel xs)
  iteratorEltype := .hasEltype
  length := iterableStatePairsLength (fun ys => pure ys.length) (pairsStringModel xs)
  size := pure [xs.length]

def listLastModel {α : Type} : List α → Jl α
  | [] => .error .boundsError
  | [x] => pure x
  | _ :: rest => listLastModel rest

def unitRangeIndex {u : IntTy} (first last : Int) (i : JInt u) : Jl Int :=
  if first ≤ i.val ∧ i.val ≤ last then .ok i.val else .error .boundsError

def checkedMulI64 (a b : JInt64) : Jl JInt64 :=
  if -(2 ^ 63) ≤ a.val * b.val ∧ a.val * b.val ≤ 2 ^ 63 - 1 then .ok (a * b)
  else .error (.overflowError "checked_mul")

def collectStateful {I α S : Type} (iterate : I → Option S → Jl (Option (α × S))) :
    Nat → Stateful I (α × S) → IteratorResult (List α × Stateful I (α × S))
  | 0, s => pure ([], s)
  | fuel + 1, s => do
      let (step, s') ← iterateStateful iterate s
      match step with
      | none => pure ([], s')
      | some (x, _) =>
          let (rest, sFinal) ← collectStateful iterate fuel s'
          pure (x :: rest, sFinal)

def firstIterModel {α S : Type} (itr : IteratorModel α S) : Jl α := do
  match ← itr.run none with
  | none => .error .boundsError
  | some (x, _) => pure x

def partitionGenericAsIterator {α : Type} (xs : List α) (n : Nat) :
    IteratorModel (List α) (PartitionState Nat) where
  run := fun state =>
    sourceMethod1484 ⟨listIterator xs, n⟩ (state.getD (.at none)) (fun itr st => itr.run st)
  isdone := fun _ => pure none
  iteratorSize := sourceMethod1461 .hasLength ⟨listIterator xs, n⟩
  iteratorEltype := sourceMethod1455 .hasEltype ⟨listIterator xs, n⟩
  length := partitionLength (fun it => it.length) ⟨listIterator xs, n⟩
  size := do pure [← partitionLength (fun it => it.length) ⟨listIterator xs, n⟩]


def generatorAsIterator {α β S : Type} (g : GeneratorModel (α → β) (IteratorModel α S)) :
    IteratorModel β S where
  run := fun state => do
    match ← g.itr.run state with
    | none => pure none
    | some (x, next) => pure (some (g.f x, next))
  isdone := g.itr.isdone
  iteratorSize := g.itr.iteratorSize
  iteratorEltype := .eltypeUnknown
  length := g.itr.length
  size := g.itr.size

def reverseFlattenAsIterator {α : Type} (rows : List (List α)) :
    IteratorModel α (Int × IteratorModel α Int × Int) :=
  let revGen := (sourceMethod1379 reverseListAsIterator reverseListAsIterator (flattenModel rows)).it
  flattenAsIterator ⟨generatorAsIterator revGen⟩

def reverseArrayAsIterator {α : Type} (xs : List α) : IteratorModel α (List Nat × Nat) where
  run := fun state =>
    sourceMethod136 (fun ys => List.range ys.length) List.reverse
      (fun r st => (listIterator r).run st)
      (fun ys idx => match listGet ys idx with | none => .error .boundsError | some v => pure v)
      (reverseDefault xs) state
  isdone := fun state => pure (some (xs.length ≤ (state.map Prod.snd).getD 0))
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]

def reverseGenericAsIterator {α : Type} (xs : List α) : IteratorModel α (List Nat × Nat) where
  run := fun state =>
    sourceMethod145 (fun ys => List.range ys.length) List.reverse
      (fun r st => (listIterator r).run st)
      (fun ys idx => match listGet ys idx with | none => .error .boundsError | some v => pure v)
      (reverseDefault xs) state
  isdone := fun state => pure (some (xs.length ≤ (state.map Prod.snd).getD 0))
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]

def reverseEnumerateAsIterator {α : Type} (xs : List α) :
    IteratorModel (JInt64 × α) (Nat × IteratorModel α Int × Int) where
  run := fun state =>
    match state with
    | none =>
      sourceMethod224 (reverseDefault (enumerateModel (listIterator xs)))
        (fun _ => reverseListAsIterator xs)
        (fun ri => ri.length)
        (fun _ (i, ri, st) => sourceMethod228 i ri st (fun it s => it.run s))
    | some (i, ri, st) =>
      sourceMethod228 i ri (some st) (fun it s => it.run s)
  isdone := fun state => pure (some ((state.map Prod.fst).getD xs.length == 0))
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]

def reversePairsListAsIterator {α : Type} (xs : List α) :
    IteratorModel (Nat × α) (List Nat × Nat) where
  run := fun state =>
    let p : PairsModel Nat α Nat (List α) :=
      pairsLinear (K := Nat) (V := α) (fun _ => 0) xs
    iterateReversePairs (K := Nat) (V := α) (I := Nat) (D := List α) (Ks := List Nat) (R := List Nat) (S := Nat)
      (keysPairs (fun ys => List.range ys.length) (fun _ => List.range xs.length))
      List.reverse
      (fun rks st => (listIterator rks).run st)
      (pairsElement (fun ys i =>
        match listGet ys i with | none => .error .boundsError | some v => pure v))
      (reverseDefault p) state
  isdone := fun state => pure (some (xs.length ≤ (state.map Prod.snd).getD 0))
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]

def reverseIterableStatePairsAsIterator {α : Type} (xs : List α) :
    IteratorModel (Int × α) Int where
  run := fun state =>
    iterateReverseIterableStatePairs (K := Int)
      (fun _ => pure (Int.ofNat xs.length))
      (fun ys st => (reverseListAsIterator ys).run st)
      (pairsStringModel xs) state
  isdone := fun state => (reverseListAsIterator xs).isdone state
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]

def dropTakeAsIterator {α S : Type} (xs : IteratorModel α S) (td : Take (Drop (IteratorModel α S))) :
    IteratorModel α (Nat × S) :=
  let d := dropAsIterator xs td.xs
  takeAsIterator d ⟨d, td.n⟩

def promoteSizeShape1D (a b : List Nat) : Jl (List Nat) :=
  match a, b with
  | [m], [n] => pure (sourceMethod415 m n)
  | _, _ => if a == b then pure a else .error (.argumentError "DimensionMismatch")

def promoteAxesShape1D (intersect : Nat → Nat → Nat := min) (a b : List Nat) : Jl (List Nat) :=
  match a, b with
  | [m], [n] => pure (sourceMethod414 intersect m n)
  | _, _ => if a == b then pure a else .error (.argumentError "DimensionMismatch")

def checkedMulNatI64 (a b : Nat) : Jl Nat :=
  if a * b < 2 ^ 63 then .ok (a * b) else .error (.overflowError "checked_mul")

def vectorGetIndex {α : Type} {u : IntTy} (xs : List α) (idx : JInt u) : Jl α :=
  if 1 ≤ idx.val ∧ idx.val ≤ xs.length then
    match listGet xs (idx.val.toNat - 1) with
    | some x => .ok x
    | none => .error .boundsError
  else .error .boundsError

def onlyTupleDispatch {α : Type} (xs : List α) : Jl α :=
  if xs.length == 1 then sourceMethod1683 xs else sourceMethod1684 xs

def onlyNamedTupleDispatch {α : Type} (xs : List α) : Jl α :=
  if xs.length == 1 then sourceMethod1687 xs else sourceMethod1688 xs

end JuliaLean.base.iterators
