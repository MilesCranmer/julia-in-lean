import JuliaLean.Core
import JuliaLean.base.generator
import JuliaLean.base.reduce
import JuliaLean.base.checked
import JuliaLean.base.indices
import JuliaLean.base.promotion
import JuliaLean.base.number
import JuliaLean.base.range

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


instance {α β γ : Type} : Lean.Order.PartialOrder (Jl (α × β × Option γ)) :=
  Lean.Order.FlatOrder.instOrder (b := .error .boundsError)

instance {α β γ : Type} : Lean.Order.CCPO (Jl (α × β × Option γ)) :=
  Lean.Order.FlatOrder.instCCPO (b := .error .boundsError)
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

def iteratorErrorToJl : IteratorError → JlError
  | .julia error => error
  | .eofError => .eofError

def iteratorResultToJl {α : Type} (result : IteratorResult α) : Jl α :=
  result.mapError iteratorErrorToJl

instance : MonadLift IteratorResult Jl where
  monadLift := iteratorResultToJl

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

/-- Representation of Julia's bottom type `Union{}` for dispatch. -/
inductive UnionBottom where
  | bottom
  deriving Repr, DecidableEq, Inhabited

/-- Witness that `α` models a subtype of `Union{Number, AbstractChar}`. -/
class IsNumberOrAbstractChar (α : Type) : Prop where
  isScalar : True

instance (t : IntTy) : IsNumberOrAbstractChar (JInt t) := ⟨trivial⟩
instance : IsNumberOrAbstractChar Fl := ⟨trivial⟩
instance : IsNumberOrAbstractChar Int := ⟨trivial⟩
instance : IsNumberOrAbstractChar Nat := ⟨trivial⟩
instance : IsNumberOrAbstractChar Char := ⟨trivial⟩
instance : IsNumberOrAbstractChar UInt32 := ⟨trivial⟩

/-- Unit-range index domain `first:last` (`AbstractUnitRange`). -/
structure UnitRangeIndices (K : Type) where
  start : K
  stop : K
  deriving Repr, DecidableEq

/-- Homogeneous tuple container (`Tuple`). -/
structure TupleContainer (V : Type) where
  items : List V
  deriving Repr, DecidableEq

/-- An `IdDict{K, V}` container with its stored key-value associations. -/
structure IdDictModel (K V : Type) where
  entries : List (K × V)
  deriving Repr, DecidableEq

/-- A 1-element tuple (`Tuple{Any}`). -/
structure Tuple1 (α : Type) where
  first : α
  deriving Repr, DecidableEq

/-- A 1-field named tuple (`NamedTuple{<:Any, <:Tuple{Any}}`). -/
structure NamedTuple1 (Name α : Type) where
  name : Name
  value : α
  deriving Repr, DecidableEq

/-- An arbitrary Julia `Integer`: either a fixed-width `BitInteger` (`JInt t`) or a `BigInt` (`Int`). -/
inductive IntegerArg where
  | bool (val : Bool)
  | bit (t : IntTy) (val : JInt t)
  | big (val : Int)
  deriving Repr, DecidableEq

namespace IntegerArg

def toInt : IntegerArg → Int
  | .bool b => if b then 1 else 0
  | .bit _ v => v.val
  | .big v => v

def add : IntegerArg → IntegerArg → IntegerArg
  | .bool a, .bool b =>
      .bit .i64 (JInt.lit .i64 ((if a then 1 else 0) + (if b then 1 else 0)))
  | .bit t a, .bool b =>
      .bit t (a + JInt.lit t (if b then 1 else 0))
  | .bool a, .bit t b =>
      .bit t (JInt.lit t (if a then 1 else 0) + b)
  | .bit ta a, .bit tb b =>
      let u := IntTy.promote ta tb
      .bit u (JInt.rem u a + JInt.rem u b)
  | a, b => .big (a.toInt + b.toInt)

def subOne : IntegerArg → IntegerArg
  | .bool a => .bit .i64 (JInt.lit .i64 (if a then 1 else 0) - JInt.lit .i64 1)
  | .bit t a =>
      let u := IntTy.promote t .i64
      .bit u (JInt.rem u a - JInt.lit u 1)
  | .big a => .big (a - 1)

def OffsetType : IntegerArg → Type
  | .bool _ => JInt64
  | .bit t _ => JInt (IntTy.promote .i64 t)
  | .big _ => Int

def offsetFrom (beginIndex : JInt64) : (n : IntegerArg) → n.OffsetType
  | .bool b => beginIndex + JInt.lit .i64 (if b then 1 else 0) - JInt.lit .i64 1
  | .bit t v =>
      let u := IntTy.promote .i64 t
      JInt.rem u beginIndex + JInt.rem u v - JInt.lit u 1
  | .big v => beginIndex.val + v - 1

end IntegerArg

structure IntegerIndexOps (K : Type) where
  greaterThan : K → K → Bool
  add : K → K → K
  subtract : K → K → K
  fromInt : Int → K
  one : K
  minimum : K → K → K

def tupleOrBottomPair (a b : Option Type) : Option Type :=
  match a, b with
  | some A, some B => some (A × B)
  | _, _ => none

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
Julia source: base/iterators.jl:379-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip(a...) = Zip(a)
```
-/
def zipModel {Is : Type u} (a : Is) : Zip Is := ⟨a⟩

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
structure Accumulate (F : Type u) (I T : Type) where
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
  deriving Repr, DecidableEq

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
  n : JInt64

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
  n : JInt64

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
  n : JInt64
  deriving Repr, DecidableEq

def mkPartitionIterator {T : Type} (c : T) (n : JInt64) : PartitionIterator T :=
  ⟨c, n⟩

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
Julia source: base/iterators.jl:696-696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rest(itr,state) = Rest(itr,state)
```
-/
def restWithState {I S : Type} (itr : I) (state : S) : Rest I S := ⟨itr, state⟩

/--
Julia source: base/iterators.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
values(v::Pairs) = getfield(v, :data) # TODO: this should be a view of data subset by itr
```
-/
def valuesPairsModel {K V I D : Type} (v : PairsModel K V I D) : D := v.data

/--
Julia source: base/iterators.jl:772-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(it::Count, state=it.start) = (state, state + it.step)
```
-/
def iterateCountState {m : Type → Type} [Monad m] (add : State → Step → m Next)
    (it : Count Start Step) (state : State) : m (State × Next) := do
  let next ← add state it.step
  pure (state,next)

/--
Julia source: base/iterators.jl:1148-1148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
product(iters...) = ProductIterator(iters)
```
-/
def productModel {T : Type} (iters : T) : ProductIterator T := ⟨iters⟩

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
Julia source: base/iterators.jl:1213-1213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(::ProductIterator{Tuple{}}, states) = true
```
-/
def isdoneEmptyProductState {S : Type} (_ : S) : Jl (Option Bool) := pure (some true)

/--
Julia source: base/iterators.jl:1447-1447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PartitionIterator(v::AbstractVector, n::Int) = PartitionIterator{typeof(v)}(v, n)
```
-/
def sourceMethod1447 {V : Type} (v : V) (n : JInt64) : PartitionIterator V :=
  mkPartitionIterator v n


-- R5.1: none is divergence; a returned exception retains the current heap.
abbrev Exec (E H α : Type) := H → Option (Except E α × H)

instance {E H α : Type} : Lean.Order.PartialOrder (Option (Except E α × H)) :=
  Lean.Order.FlatOrder.instOrder (b := none)
instance {E H α : Type} : Lean.Order.CCPO (Option (Except E α × H)) :=
  Lean.Order.FlatOrder.instCCPO (b := none)

def ret {E H α : Type} (a : α) : Exec E H α :=
  fun h => some (.ok a, h)
def fail {E H α : Type} (e : E) : Exec E H α :=
  fun h => some (.error e, h)
def bind {E H α β : Type} (x : Exec E H α) (f : α → Exec E H β) : Exec E H β :=
  fun h => match x h with
  | none => none
  | some (.error e, h) => some (.error e, h)
  | some (.ok x, h) => f x h

instance {E H : Type} : Monad (Exec E H) where
  pure := ret
  bind := bind

structure DescriptorOps (Ty : Type u) where
  subtype : Ty → Ty → Bool
  anyType : Ty
  bottom : Ty
  stateTupleType : Ty
  returnTypeIterate : Ty → Ty
  returnTypeDoiterate : Ty → Ty → Ty

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
def approxIterType {Ty : Type u} (ops : DescriptorOps Ty) (itrT vstate : Ty) : Ty :=
  if !ops.subtype vstate ops.stateTupleType then ops.anyType
  else if ops.subtype vstate ops.bottom then ops.bottom
  else if ops.subtype itrT ops.bottom then ops.bottom
  else
    let next := ops.returnTypeDoiterate itrT vstate
    if ops.subtype next vstate then vstate else ops.anyType

/--
Julia source: base/iterators.jl:1589-1589 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
approx_iter_type(itrT::Type) = _approx_iter_type(itrT, Base._return_type(iterate, Tuple{itrT}))
```
-/
def approxIterTypeInitial {Ty : Type u} (ops : DescriptorOps Ty) (itrT : Ty) : Ty :=
  approxIterType ops itrT (ops.returnTypeIterate itrT)

structure StatefulOps (E H Handle I Y Ty : Type) where
  allocate : I → Ty → Option Y → Exec E H Handle
  iterator : Handle → Exec E H I
  pending : Handle → Exec E H (Option Y)
  declaredCacheType : Handle → Exec E H Ty
  setIterator : Handle → I → Exec E H Unit
  writeCacheRaw : Handle → Option Y → Exec E H Unit
  assertCache : Option Y → Ty → Exec E H (Option Y)

def setCache (ops : StatefulOps E H Handle I Y Ty)
    (s : Handle) (value : Option Y) : Exec E H Unit := do
  let ty ← ops.declaredCacheType s
  let value ← ops.assertCache value ty
  ops.writeCacheRaw s value

/--
Julia source: base/iterators.jl:1566-1568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function Stateful{<:Any, Any}(itr::T) where {T}
        return new{T, Any}(itr, iterate(itr))
    end
```
-/
def statefulAny (ops : StatefulOps E H Handle I Y Ty)
    (run : I → Exec E H (Option Y)) (any : Ty) (itr : I) : Exec E H Handle := do
  ops.allocate itr any (← run itr)

/--
Julia source: base/iterators.jl:1569-1572 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @inline function Stateful(itr::T) where {T}
        VS = approx_iter_type(T)
        return new{T, VS}(itr, iterate(itr)::VS)
    end
```
-/
def stateful (ops : StatefulOps E H Handle I Y Ty) (types : DescriptorOps Ty)
    (typeof : I → Ty) (run : I → Exec E H (Option Y)) (itr : I) :
    Exec E H Handle := do
  let vs := approxIterTypeInitial types (typeof itr)
  let initial ← ops.assertCache (← run itr) vs
  ops.allocate itr vs initial

/--
Julia source: base/iterators.jl:1575-1578 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reset!(s::Stateful)
    setfield!(s, :nextvalstate, iterate(s.itr)) # bypass convert call of setproperty!
    return s
end
```
-/
def resetStateful (ops : StatefulOps E H Handle I Y Ty)
    (run : I → Exec E H (Option Y)) (s : Handle) : Exec E H Handle := do
  setCache ops s (← run (← ops.iterator s))
  pure s

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
def resetStatefulTo (ops : StatefulOps E H Handle I Y Ty)
    (run : I → Exec E H (Option Y)) (s : Handle) (itr : I) :
    Exec E H Handle := do
  ops.setIterator s itr
  let _ ← resetStateful ops run s
  pure s

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
def popfirstStateful (ops : StatefulOps E H Handle I (α × S) Ty)
    (run : I → S → Exec E H (Option (α × S))) (eof : E)
    (s : Handle) : Exec E H α := do
  match ← ops.pending s with
  | none => fail eof
  | some (value, state) =>
      setCache ops s (← run (← ops.iterator s) state)
      pure value

/--
Julia source: base/iterators.jl:1620-1623 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function peek(s::Stateful, sentinel=nothing)
    ns = s.nextvalstate
    return ns !== nothing ? ns[1] : sentinel
end
```
-/
def peekStateful (ops : StatefulOps E H Handle I (α × S) Ty)
    (s : Handle) (sentinel : β) : Exec E H (α ⊕ β) := do
  match ← ops.pending s with
  | none => pure (.inr sentinel)
  | some (value, _) => pure (.inl value)

/--
Julia source: base/iterators.jl:1607-1607 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(s::Stateful, st=nothing) = s.nextvalstate === nothing
```
-/
def isdoneStateful (ops : StatefulOps E H Handle I Y Ty) (s : Handle) :
    Exec E H Bool := do
  pure (← ops.pending s).isNone

/--
Julia source: base/iterators.jl:1624-1624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline iterate(s::Stateful, state=nothing) = s.nextvalstate === nothing ? nothing : (popfirst!(s), nothing)
```
-/
def iterateStateful (ops : StatefulOps E H Handle I (α × S) Ty)
    (run : I → S → Exec E H (Option (α × S))) (eof : E)
    (s : Handle) : Exec E H (Option (α × Unit)) := do
  if (← ops.pending s).isNone then pure none
  else pure (some (← popfirstStateful ops run eof s, ()))



/--
Julia source: base/iterators.jl:826-833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
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
def iterateTake (run : I → Option S → Exec E H (Option (α × S)))
    (t : Take I) (state : Option (JInt64 × S)) :
    Exec E H (Option (α × (JInt64 × S))) := do
  let (n, st) := match state with
    | none => (t.n, none)
    | some (n, st) => (n, some st)
  if n.val ≤ 0 then pure none
  else
    match ← run t.xs st with
    | none => pure none
    | some (x, next) =>
        pure (some (x, (JuliaLean.base.int.sub_int n (JInt.lit .i64 1), next)))

/--
Julia source: base/iterators.jl:824-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(t::Take) = isdone(t.xs)
```
-/
def takeIsdone (done : I → Option S → Exec E H (Option Bool)) (t : Take I) :
    Exec E H (Option Bool) := done t.xs none

/--
Julia source: base/iterators.jl:825-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(t::Take, state) = (state[1] <= 0) | isdone(t.xs, tail(state)...)
```
-/
def takeIsdoneState (done : I → Option S → Exec E H (Option Bool))
    (t : Take I) (n : JInt64) (st : Option S) : Exec E H (Option Bool) := do
  let d ← done t.xs st
  pure (boolOrMissing (some (n.val ≤ 0)) d)

/--
Julia source: base/iterators.jl:732-732 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds iterate(i::Rest, st=i.st) = iterate(i.itr, st)
```
-/
def iterateRest (run : I → Option S → Exec E H (Option (α × S)))
    (r : JuliaLean.base.iterators.Rest I S) (state : Option S) :
    Exec E H (Option (α × S)) :=
  run r.itr (some (state.getD r.st))

/--
Julia source: base/iterators.jl:733-733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isdone(i::Rest, st...) = isdone(i.itr, st...)
```
-/
def isdoneRest (done : I → Option Q → Exec E H (Option Bool))
    (r : JuliaLean.base.iterators.Rest I S) (state : Option Q) :
    Exec E H (Option Bool) := done r.itr state

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
def peel (run : I → Option S → Exec E H (Option (α × S))) (itr : I) :
    Exec E H (Option (α × JuliaLean.base.iterators.Rest I S)) := do
  match ← run itr none with
  | none => pure none
  | some (x, st) => pure (some (x, restWithState itr st))

def isempty (done : I → Option S → Exec E H (Option Bool))
    (run : I → Option S → Exec E H (Option (α × S)))
    (itr : I) (st : Option S := none) : Exec E H Bool := do
  match ← done itr st with
  | some b => pure b
  | none => pure (← run itr st).isNone

-- R5.2: raw Expr(:new) and converting Pair construction are different operations.
/--
Julia source: base/iterators.jl:327-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(v::Pairs) = getfield(v, :itr) === nothing ? keys(getfield(v, :data)) : getfield(v, :itr)
```
-/
def keysPairs [Monad m] (keysData : D → m Keys)
    (p : PairsModel K V Keys D) : m Keys :=
  match p.itr with
  | none => keysData p.data
  | some keys => pure keys

/--
Julia source: base/iterators.jl:298-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@eval @propagate_inbounds function _pairs_elt(p::Pairs{K, V}, idx) where {K, V}
    return $(Expr(:new, :(Pair{K, V}), :idx, :(getfield(p, :data)[idx])))
end
```
-/
def pairsElement [Monad m] (getindex : D → Idx → m Val)
    (rawTypedPair : Idx → Val → m (K × V))
    (p : PairsModel K V Keys D) (idx : Idx) : m (K × V) := do
  let val ← getindex p.data idx
  rawTypedPair idx val

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
def iteratePairs [Monad m] (keysData : D → m Keys)
    (run : Keys → Option S → m (Option (Idx × S)))
    (getindex : D → Idx → m Val) (rawTypedPair : Idx → Val → m (K × V))
    (p : PairsModel K V Keys D) (st : Option S) :
    m (Option ((K × V) × S)) := do
  match ← run (← keysPairs keysData p) st with
  | none => pure none
  | some (idx, next) => pure (some (← pairsElement getindex rawTypedPair p idx, next))

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
def iterateReversePairs [Monad m] (keysData : D → m Keys)
    (reverse : Keys → m R) (run : R → Option S → m (Option (Idx × S)))
    (getindex : D → Idx → m Val) (rawTypedPair : Idx → Val → m (K × V))
    (r : Reverse (PairsModel K V Keys D)) (st : Option (R × S) := none) :
    m (Option ((K × V) × (R × S))) := do
  let (keys, st) ← match st with
    | none => do pure (← reverse (← keysPairs keysData r.itr), none)
    | some (keys, st) => pure (keys, some st)
  match ← run keys st with
  | none => pure none
  | some (idx, next) =>
      pure (some (← pairsElement getindex rawTypedPair r.itr idx, (keys, next)))

/--
Julia source: base/iterators.jl:329-329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(v::Pairs, key) = values(v)[key]
```
-/
def getindexPairs [Monad m] (getindex : D → Idx → m Val)
    (p : PairsModel K V Keys D) (idx : Idx) : m Val :=
  getindex (valuesPairsModel p) idx

/--
Julia source: base/iterators.jl:321-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function last(v::Pairs{K, V}) where {K, V}
    idx = last(keys(v))
    return Pair{K, V}(idx, v[idx])
end
```
-/
def lastPairs [Monad m] (keysData : D → m Keys) (last : Keys → m Idx)
    (getindex : D → Idx → m Val)
    (convertingPair : Idx → Val → m (K × V))
    (p : PairsModel K V Keys D) : m (K × V) := do
  let idx ← last (← keysPairs keysData p)
  convertingPair idx (← getindexPairs getindex p idx)

def pairsMetadata [Monad m] (keysData : D → m Keys) (query : Keys → m R)
    (p : PairsModel K V Keys D) : m R := do query (← keysPairs keysData p)

/--
Julia source: base/iterators.jl:330-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setindex!(v::Pairs, value, key) = (values(v)[key] = value; v)
```
-/
def setindexPairs [Monad m] (setindex : D → Key → Value → m Unit)
    (p : PairsModel K V Keys D) (value : Value) (key : Key) :
    m (PairsModel K V Keys D) := do
  setindex p.data key value
  pure p

/--
Julia source: base/iterators.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(v::Pairs, key, default) = get(values(v), key, default)
```
-/
def getPairs [Monad m] (get : D → Key → Default → m Result)
    (p : PairsModel K V Keys D) (key : Key) (default : Default) : m Result :=
  get p.data key default

/--
Julia source: base/iterators.jl:1708-1713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(x::IterableStatePairs, state=first(keys(x.x)))
    it = iterate(x.x, state)
    it === nothing && return nothing
    (state => first(it), last(it))
end

```
-/
def iterateStatePairs [Monad m] (keys : I → m Keys) (first : Keys → m S)
    (run : I → S → m (Option (V × S)))
    (x : IterableStatePairs I) (st : Option S := none) :
    m (Option ((S × V) × S)) := do
  let st ← match st with
    | none => first (← keys x.x)
    | some st => pure st
  pure ((← run x.x st).map fun (v, next) => ((st, v), next))

-- R5.3: source overloads retain independent operand and result types.
/--
Julia source: base/iterators.jl:58-58 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_min_length(a, b, ::IsInfinite, ::IsInfinite) = min(length(a),length(b)) # inherit behaviour, error
```
-/
def minLengthBothInfinite [Monad m]
    (lenA : A → m LA) (lenB : B → m LB) (minimum : LA → LB → m L)
    (a : A) (b : B) : m L := do
  let la ← lenA a
  let lb ← lenB b
  minimum la lb
/--
Julia source: base/iterators.jl:59-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_min_length(a, b, A, ::IsInfinite) = length(a)
```
-/
def minLengthRightInfinite [Monad m] (lenA : A → m LA) (a : A) (_ : B) : m LA :=
  lenA a
/--
Julia source: base/iterators.jl:60-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_min_length(a, b, ::IsInfinite, B) = length(b)
```
-/
def minLengthLeftInfinite [Monad m] (lenB : B → m LB) (_ : A) (b : B) : m LB :=
  lenB b
/--
Julia source: base/iterators.jl:61-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_min_length(a, b, A, B) = min(length(a),length(b))
```
-/
def minLengthFinite [Monad m]
    (lenA : A → m LA) (lenB : B → m LB) (minimum : LA → LB → m L)
    (a : A) (b : B) : m L := do
  let la ← lenA a
  let lb ← lenB b
  minimum la lb

/--
Julia source: base/iterators.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_diff_length(a, b, A, ::IsInfinite) = 0
```
-/
def diffLengthRightInfinite (_ : A) (_ : B) : JInt64 := JInt.lit .i64 0
/--
Julia source: base/iterators.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_diff_length(a, b, ::IsInfinite, ::IsInfinite) = 0
```
-/
def diffLengthBothInfinite (_ : A) (_ : B) : JInt64 := JInt.lit .i64 0
/--
Julia source: base/iterators.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_diff_length(a, b, ::IsInfinite, B) = length(a) # inherit behaviour, error
```
-/
def diffLengthLeftInfinite [Monad m] (lenA : A → m LA) (a : A) (_ : B) : m LA :=
  lenA a
/--
Julia source: base/iterators.jl:66-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _diff_length(a, b, A, B)
    m, n = length(a), length(b)
    return m > n ? m - n : zero(n - m)
end
```
-/
def diffLengthFinite [Monad m]
    (lenA : A → m LA) (lenB : B → m LB) (gt : LA → LB → m Bool)
    (subAB : LA → LB → m DAB) (subBA : LB → LA → m DBA)
    (zero : DBA → m Z) (a : A) (b : B) : m (DAB ⊕ Z) := do
  let la ← lenA a
  let lb ← lenB b
  if ← gt la lb then pure (.inl (← subAB la lb))
  else pure (.inr (← zero (← subBA lb la)))

/--
Julia source: base/iterators.jl:823-823 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(t::Take) = _min_length(t.xs, 1:t.n, IteratorSize(t.xs), HasLength())
```
-/
def takeLength [Monad m] (trait : I → IteratorSizeTag)
    (colon : JInt64 → JInt64 → m R) (len : I → m LA) (lenR : R → m LB)
    (minimum : LA → LB → m L) (t : Take I) : m (LB ⊕ L) := do
  let r ← colon (JInt.lit .i64 1) t.n
  match trait t.xs with
  | .isInfinite => pure (.inl (← minLengthLeftInfinite lenR t.xs r))
  | _ => pure (.inr (← minLengthFinite len lenR minimum t.xs r))

/--
Julia source: base/iterators.jl:881-881 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(d::Drop) = _diff_length(d.xs, 1:d.n, IteratorSize(d.xs), HasLength())
```
-/
def dropLength [Monad m] (trait : I → IteratorSizeTag)
    (colon : JInt64 → JInt64 → m R) (len : I → m LA) (lenR : R → m LB)
    (gt : LA → LB → m Bool)
    (subAB : LA → LB → m DAB) (subBA : LB → LA → m DBA)
    (zero : DBA → m Z) (d : Drop I) : m (LA ⊕ (DAB ⊕ Z)) := do
  let r ← colon (JInt.lit .i64 1) d.n
  match trait d.xs with
  | .isInfinite => pure (.inl (← diffLengthLeftInfinite len d.xs r))
  | _ => pure (.inr (← diffLengthFinite len lenR gt subAB subBA zero d.xs r))

/--
Julia source: base/iterators.jl:1172-1174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size1(a, ::HasShape)  = size(a)
_prod_size1(a, ::HasLength) = (length(a),)
_prod_size1(a, A) =
```
-/
def prodSizeOne [Monad m] [MonadExceptOf JlError m]
    (size : I → m (List Dim)) (length : I → m Dim) (typeof : I → String)
    (i : I) (tag : IteratorSizeTag) : m (List Dim) := do
  match tag with
  | .hasShape _ => size i
  | .hasLength => pure [← length i]
  | _ => throw (.argumentError s!"Cannot compute size for object of type {typeof i}")

/--
Julia source: base/iterators.jl:1180-1182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_axes1(a, ::HasShape)  = axes(a)
_prod_axes1(a, ::HasLength) = (OneTo(length(a)),)
_prod_axes1(a, A) =
```
-/
def prodAxesOne [Monad m] [MonadExceptOf JlError m]
    (axes : I → m (List Axis)) (length : I → m L) (oneTo : L → m Axis)
    (typeof : I → String) (i : I) (tag : IteratorSizeTag) : m (List Axis) := do
  match tag with
  | .hasShape _ => axes i
  | .hasLength => pure [← oneTo (← length i)]
  | _ => throw (.argumentError s!"Cannot compute indices for object of type {typeof i}")

/--
Julia source: base/iterators.jl:1171-1171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size(t::Tuple) = (_prod_size1(t[1], IteratorSize(t[1]))..., _prod_size(tail(t))...)
```
-/
def prodMetadata [Monad m] (part : I → m (List A)) : List I → m (List A)
  | [] => pure []
  | i :: is => do
      let first ← part i
      pure (first ++ (← prodMetadata part is))

/--
Julia source: base/iterators.jl:1326-1326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function flatten_length(f, T::Type{<:NTuple{N,Any}}) where {N}
```
-/
def flattenTupleLength [Monad m]
    (length : I → m L) (checkedMul : N → L → m Product)
    (f : Flatten I) (n : N) : m Product := do
  checkedMul n (← length f.it)

-- R5.4: exact constructor order and a lifted shared-handle partition loop.
/--
Julia source: base/iterators.jl:1436-1439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
""" function partition(c, n::Integer)
    n < 1 && throw(ArgumentError("cannot create partitions of length $n"))
    return PartitionIterator(c, Int(n))
end
```
-/
def partition [Monad m] (ltOne : N → m Bool) (toInt : N → m JInt64)
    (showN : N → m String) (argumentError : String → m (PartitionIterator C))
    (construct : I → JInt64 → m (PartitionIterator C))
    (c : I) (n : N) : m (PartitionIterator C) := do
  if ← ltOne n then do
    let shown ← showN n
    argumentError s!"cannot create partitions of length {shown}"
  else construct c (← toInt n)

/--
Julia source: base/iterators.jl:1446-1446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
PartitionIterator(A::AbstractArray, n::Int) = PartitionIterator(Base.vec(A), n)
```
-/
def partitionArray [Monad m] (vec : A → m V) (a : A) (n : JInt64) :
    m (PartitionIterator V) := do
  pure (sourceMethod1447 (← vec a) n)

/--
Julia source: base/iterators.jl:1470-1474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::PartitionIterator{<:AbstractRange}, state = firstindex(itr.c))
    state > lastindex(itr.c) && return nothing
    r = min(state + itr.n - 1, lastindex(itr.c))
    return @inbounds itr.c[state:r], r + 1
end
```

Julia source: base/iterators.jl:1476-1480 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::PartitionIterator{<:AbstractArray}, state = firstindex(itr.c))
    state > lastindex(itr.c) && return nothing
    r = min(state + itr.n - 1, lastindex(itr.c))
    return @inbounds Base.view(itr.c, state:r), r + 1
end
```
-/
def partitionIndexed [Monad m]
    (first : C → m Index) (last : C → m Last) (gt : Index → Last → m Bool)
    (addCount : Index → JInt64 → m Added) (subOne : Added → JInt64 → m End)
    (minimum : End → Last → m Stop) (colon : Index → Stop → m Range)
    (slice : C → Range → m Chunk) (addOne : Stop → JInt64 → m Next)
    (p : PartitionIterator C) (state : Option Index := none) :
    m (Option (Chunk × Next)) := do
  let st ← match state with | none => first p.c | some st => pure st
  let last1 ← last p.c
  if ← gt st last1 then pure none
  else do
    let sum ← addCount st p.n
    let stop0 ← subOne sum (JInt.lit .i64 1)
    let last2 ← last p.c
    let stop ← minimum stop0 last2
    let range ← colon st stop
    let chunk ← slice p.c range
    pure (some (chunk, ← addOne stop (JInt.lit .i64 1)))

def partitionLoop
    (run : I → Option S → Exec E H (Option (α × S)))
    (store : Vec → α → JInt64 → Exec E H Unit)
    (p : PartitionIterator I) (v : Vec) (i : JInt64)
    (y : Option (α × S)) : Exec E H (JInt64 × Option (α × S)) :=
  fun heap => match y with
  | none => some (.ok (i, none), heap)
  | some (x, st) =>
      let next := JuliaLean.base.int.add_int i (JInt.lit .i64 1)
      match store v x next heap with
      | none => none
      | some (.error e, heap) => some (.error e, heap)
      | some (.ok (), heap) =>
          if next.val ≥ p.n.val then some (.ok (next, y), heap)
          else
            match run p.c (some st) heap with
            | none => none
            | some (.error e, heap) => some (.error e, heap)
            | some (.ok y, heap) => partitionLoop run store p v next y heap
partial_fixpoint

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
def partitionGeneric (eltype : I → Ty)
    (allocate : Ty → JInt64 → Exec E H Vec)
    (store : Vec → α → JInt64 → Exec E H Unit)
    (resize : Vec → JInt64 → Exec E H Vec)
    (run : I → Option S → Exec E H (Option (α × S)))
    (p : PartitionIterator I) (state : PartitionState S := .at none) :
    Exec E H (Option (Vec × PartitionState S)) := do
  match state with
  | .cutShort => pure none
  | .at st =>
      let v ← allocate (eltype p.c) p.n
      let y ← run p.c st
      let (i, y) ← partitionLoop run store p v (JInt.lit .i64 0) y
      if i.val = 0 then pure none
      else do
        let v ← resize v i
        pure (some (v, match y with
          | none => .cutShort
          | some (_, st) => .at (some st)))

-- R5.5: the raw Y result and the Tuple{Any,Any} branch are retained.
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
def filterScan (run : I → Option S → Exec E H (Option Y))
    (unpack : Y → Exec E H (α × S)) (test : F → α → Exec E H Bool)
    (isTuple2 : Y → Bool) (tuple : α → S → Y)
    (f : Filter F I) (st : Option S) : Exec E H (Option Y) :=
  fun heap => match run f.itr st heap with
  | none => none
  | some (.error e, heap) => some (.error e, heap)
  | some (.ok none, heap) => some (.ok none, heap)
  | some (.ok (some y), heap) =>
      match unpack y heap with
      | none => none
      | some (.error e, heap) => some (.error e, heap)
      | some (.ok (v, s), heap) =>
          match test f.flt v heap with
          | none => none
          | some (.error e, heap) => some (.error e, heap)
          | some (.ok true, heap) =>
              if isTuple2 y then some (.ok (some (tuple v s)), heap)
              else some (.ok (some y), heap)
          | some (.ok false, heap) =>
              filterScan run unpack test isTuple2 tuple f (some s) heap
partial_fixpoint

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
def takeWhile (run : I → Option S → Exec E H (Option Y))
    (first : Y → Exec E H α) (test : P → α → Exec E H Bool)
    (it : TakeWhile I P) (st : Option S) : Exec E H (Option Y) := do
  match ← run it.xs st with
  | none => pure none
  | some y => if ← test it.pred (← first y) then pure (some y) else pure none

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
def dropWhileScan (run : I → Option S → Exec E H (Option Y))
    (first : Y → Exec E H α) (second : Y → Exec E H S)
    (test : P → α → Exec E H Bool) (it : DropWhile I P)
    (y : Option Y) : Exec E H (Option Y) :=
  fun heap => match y with
  | none => some (.ok none, heap)
  | some y =>
      match first y heap with
      | none => none
      | some (.error e, heap) => some (.error e, heap)
      | some (.ok x, heap) =>
          match test it.pred x heap with
          | none => none
          | some (.error e, heap) => some (.error e, heap)
          | some (.ok false, heap) => some (.ok (some y), heap)
          | some (.ok true, heap) =>
              match second y heap with
              | none => none
              | some (.error e, heap) => some (.error e, heap)
              | some (.ok st, heap) =>
                  match run it.xs (some st) heap with
                  | none => none
                  | some (.error e, heap) => some (.error e, heap)
                  | some (.ok y, heap) => dropWhileScan run first second test it y heap
partial_fixpoint

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
def dropWhile (run : I → Option S → Exec E H (Option Y))
    (first : Y → Exec E H α) (second : Y → Exec E H S)
    (test : P → α → Exec E H Bool) (it : DropWhile I P) :
    Exec E H (Option Y) := do
  dropWhileScan run first second test it (← run it.xs none)

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
def flattenOuter (outer : OI → Option O → Exec E H (Option (I × O)))
    (inner : I → Option S → Exec E H (Option (α × S)))
    (f : Flatten OI) (st : Option O) :
    Exec E H (Option (α × (O × I × S))) :=
  fun heap => match outer f.it st heap with
  | none => none
  | some (.error e, heap) => some (.error e, heap)
  | some (.ok none, heap) => some (.ok none, heap)
  | some (.ok (some (i, nextOuter)), heap) =>
      match inner i none heap with
      | none => none
      | some (.error e, heap) => some (.error e, heap)
      | some (.ok none, heap) => flattenOuter outer inner f (some nextOuter) heap
      | some (.ok (some (x, nextInner)), heap) =>
          some (.ok (some (x, (nextOuter, i, nextInner))), heap)
partial_fixpoint

/--
Julia source: base/iterators.jl:1373-1377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
            item, next_inner_state = inner_it_result
            return item, (next_outer_state, inner_iterator, next_inner_state)
        end
    end
end
```
-/
def flattenState (outer : OI → Option O → Exec E H (Option (I × O)))
    (inner : I → Option S → Exec E H (Option (α × S)))
    (f : Flatten OI) (st : O × I × S) :
    Exec E H (Option (α × (O × I × S))) := do
  match ← inner st.2.1 (some st.2.2) with
  | some (x, next) => pure (some (x, (st.1, st.2.1, next)))
  | none => flattenOuter outer inner f (some st.1)

-- R5.6: actual descriptor carrier, actual subtype and Option-returning typejoin.
def descriptorOps (stateTuple : JuliaLean.base.promotion.PType)
    (inferIterate : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
    (inferDoiterate : JuliaLean.base.promotion.PType →
      JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType) :
    DescriptorOps JuliaLean.base.promotion.PType where
  subtype := JuliaLean.base.promotion.pSubtype
  anyType := .any
  bottom := .bottom
  stateTupleType := stateTuple
  returnTypeIterate := inferIterate
  returnTypeDoiterate := inferDoiterate

def typejoin (nothing missing : JuliaLean.base.promotion.PType)
    (a b : JuliaLean.base.promotion.PType) : Option JuliaLean.base.promotion.PType :=
  JuliaLean.base.promotion.promoteTypejoin JuliaLean.base.promotion.typejoin
    (JuliaLean.base.promotion.promoteTypesubtract
      JuliaLean.base.promotion.sourcePTypeOps nothing missing) a b

/--
Julia source: base/iterators.jl:1298-1300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eltype(::Type{Flatten{I}}) where {N, I<:Tuple{Vararg{Any, N}}}
    afoldl((T, i) -> promote_typejoin(T, eltype(i)), Union{}, ntuple(n -> fieldtype(I, n), N)...)
end
```
-/
def flattenTupleEltype
    (fieldtype : T → Nat → JuliaLean.base.promotion.PType)
    (eltype : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
    (nothing missing : JuliaLean.base.promotion.PType) (t : T) (N : Nat) :
    Option JuliaLean.base.promotion.PType :=
  ((List.range N).map (fun k => fieldtype t (k + 1))).foldlM
    (fun a field => typejoin nothing missing a (eltype field)) .bottom

/--
Julia source: base/iterators.jl:1301-1303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eltype(::Type{Flatten{I}}) where {I<:NamedTuple}
    afoldl((T, i) -> promote_typejoin(T, eltype(i)), Union{}, fieldtypes(I)...)
end
```
-/
def flattenNamedEltype
    (fieldtypes : T → List JuliaLean.base.promotion.PType)
    (eltype : JuliaLean.base.promotion.PType → JuliaLean.base.promotion.PType)
    (nothing missing : JuliaLean.base.promotion.PType) (t : T) :
    Option JuliaLean.base.promotion.PType :=
  (fieldtypes t).foldlM (fun a field => typejoin nothing missing a (eltype field)) .bottom

structure CountFamily (Step : Type) where
  State : Nat → Type
  start : State 0
  step : Step
  add : (k : Nat) → State k → Step → Jl (State (k + 1))

/--
Julia source: base/iterators.jl:772-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(it::Count, state=it.start) = (state, state + it.step)
```
-/
def countStep (it : CountFamily Step) (k : Nat) (state : it.State k) :
    Jl (it.State k × it.State (k + 1)) :=
  iterateCountState (it.add k) (Count.mk it.start it.step) state

/--
Julia source: base/iterators.jl:764-764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom(start::T, step::S) where {T,S} = Count{typeof(start+step),S}(start, step)
```
-/
def countTyped [Monad m]
    (add : T → S → m R) (convertStart : T → m R) (start : T) (step : S) :
    m (Count R S) := do
  let _ ← add start step
  pure ⟨← convertStart start, step⟩

/--
Julia source: base/iterators.jl:765-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom(start::Number, step::Number)   = Count(promote(start, step)...)
```
-/
def countNumbers [Monad m] (promote : A → B → m (C × C))
    (a : A) (b : B) : m (Count C C) := do
  let (a, b) ← promote a b
  pure ⟨a, b⟩

/--
Julia source: base/iterators.jl:765-765 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom(start::Number, step::Number)   = Count(promote(start, step)...)
```
-/
def countNumbersDifferent [Monad m]
    (promoteTypeof : A → B → m JuliaLean.base.promotion.PType)
    (convertA : JuliaLean.base.promotion.PType → A → m C)
    (convertB : JuliaLean.base.promotion.PType → B → m C)
    (notSameType : A × B → C × C → m Unit) (a : A) (b : B) : m (Count C C) :=
  countNumbers
    (JuliaLean.base.promotion.promoteTwoValues
      (JuliaLean.base.promotion.promotePairValues promoteTypeof convertA convertB)
      notSameType) a b

/--
Julia source: base/iterators.jl:766-766 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom(start)                         = Count(start, oneunit(start))
```
-/
def countOne {m : Type → Type} [Monad m] (oneunit : A → m B) (start : A) : m (Count A B) := do
  pure ⟨start,← oneunit start⟩

-- R5.6: when typeof(start+step) depends on the returned value, retain that tag.
structure TypedCount (Ty : Type) (Value : Ty → Type) (Step : Type) where
  declaredType : Ty
  start : Value declaredType
  step : Step

def constructTypedCount [Monad m] {Ty : Type} {Value : Ty → Type}
    (convertStart : (target : Ty) → T → m (Value target))
    (convertStep : S → m S) (target : Ty) (start : T) (step : S) :
    m (TypedCount Ty Value S) := do
  let start ← convertStart target start
  let step ← convertStep step
  pure ⟨target, start, step⟩

/--
Julia source: base/iterators.jl:764-764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom(start::T, step::S) where {T,S} = Count{typeof(start+step),S}(start, step)
```
-/
def countTypedValue [Monad m] {Ty : Type} {Value : Ty → Type}
    (add : T → S → m Result) (typeof : Result → Ty)
    (convertStart : (target : Ty) → T → m (Value target))
    (convertStep : S → m S) (start : T) (step : S) :
    m (TypedCount Ty Value S) := do
  let sum ← add start step
  constructTypedCount convertStart convertStep (typeof sum) start step

/--
Julia source: base/iterators.jl:772-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(it::Count, state=it.start) = (state, state + it.step)
```
-/
def iterateTypedCount [Monad m] {Ty : Type} {Value : Ty → Type}
    (add : Sigma Value → S → m (Sigma Value)) (it : TypedCount Ty Value S)
    (state : Option (Sigma Value) := none) : m (Sigma Value × Sigma Value) := do
  let state := state.getD ⟨it.declaredType, it.start⟩
  pure (state, ← add state it.step)

/--
Julia source: base/iterators.jl:770-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:Count{T}}) where {T} = T
```
-/
def typedCountEltype {Ty : Type} {Value : Ty → Type} (it : TypedCount Ty Value S) : Ty :=
  it.declaredType

-- R5.9: base/iterators.jl:430-501, with independent component types.
inductive TupleVals {K : Type} (F : K → Type) : List K → Type where
  | nil : TupleVals F []
  | cons {k ks} : F k → TupleVals F ks → TupleVals F (k :: ks)

def tupleMap {K : Type} {F G : K → Type}
    (f : (k : K) → F k → G k) :
    {ks : List K} → TupleVals F ks → TupleVals G ks
  | [], .nil => .nil
  | k :: _, .cons a rest => .cons (f k a) (tupleMap f rest)

def tupleInitial {K : Type} {I S : K → Type} :
    {ks : List K} → TupleVals I ks → TupleVals (fun k => Option (S k)) ks
  | [], .nil => .nil
  | _ :: _, .cons _ rest => .cons none (tupleInitial rest)

/--
Julia source: base/iterators.jl:462-463 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_all_missing(ds::Tuple) = ds[1] === missing && _zip_all_missing(tail(ds))
_zip_all_missing(::Tuple{}) = true
```
-/
def tupleAllMissing {K : Type} :
    {ks : List K} → TupleVals (fun _ : K => Option Bool) ks → Bool
  | [], .nil => true
  | _ :: _, .cons d rest => d.isNone && tupleAllMissing rest

structure ZipCalls (m : Type → Type) {K : Type} (I V S : K → Type) where
  run : (k : K) → I k → Option (S k) → m (Option (V k × S k))
  done : (k : K) → I k → Option (S k) → m (Option Bool)

/--
Julia source: base/iterators.jl:433-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _zip_any_isdone(is::Tuple, ss::Tuple)
    d1 = isdone(is[1], ss[1]...)
    d1 === true && return true
    return d1 | _zip_any_isdone(tail(is), tail(ss))
end
@inline _zip_any_isdone(::Tuple{}, ::Tuple{}) = false
```
-/
def zipAnyDone [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) :
    {ks : List K} → TupleVals I ks → TupleVals (fun k => Option (S k)) ks →
      m (Option Bool)
  | [], .nil, .nil => pure (some false)
  | k :: _, .cons i is, .cons s ss => do
      let d ← ops.done k i s
      if d = some true then pure d
      else pure (boolOrMissing d (← zipAnyDone ops is ss))

/--
Julia source: base/iterators.jl:496-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _zip_isdone(is::Tuple, ss::Tuple)
    d = isdone(is[1], ss[1]...)
    d´, ds = _zip_isdone(tail(is), tail(ss))
    return (d === true || d´, (d, ds...))
end
_zip_isdone(::Tuple{}, ::Tuple{}) = (false, ())
```
-/
def zipDoneScan [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) :
    {ks : List K} → TupleVals I ks → TupleVals (fun k => Option (S k)) ks →
      m (Bool × TupleVals (fun _ : K => Option Bool) ks)
  | [], .nil, .nil => pure (false, .nil)
  | k :: _, .cons i is, .cons s ss => do
      let d ← ops.done k i s
      let (restDone, ds) ← zipDoneScan ops is ss
      pure (d = some true || restDone, .cons d ds)

/--
Julia source: base/iterators.jl:465-472 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _zip_iterate_in_order(is::Tuple, ss::Tuple)
    x = iterate(is[1], ss[1]...)
    x === nothing && return nothing
    y = _zip_iterate_in_order(tail(is), tail(ss))
    y === nothing && return nothing
    return (x, y...)
end
_zip_iterate_in_order(::Tuple{}, ::Tuple{}) = ()
```
-/
def zipInOrder [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) :
    {ks : List K} → TupleVals I ks → TupleVals (fun k => Option (S k)) ks →
      m (Option (TupleVals (fun k => V k × S k) ks))
  | [], .nil, .nil => pure (some .nil)
  | k :: _, .cons i is, .cons s ss => do
      match ← ops.run k i s with
      | none => pure none
      | some x =>
          match ← zipInOrder ops is ss with
          | none => pure none
          | some rest => pure (some (.cons x rest))

/--
Julia source: base/iterators.jl:478-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _zip_iterate_unknown(is::Tuple, ss::Tuple, ds::Tuple)
    x = ds[1] === missing ? iterate(is[1], ss[1]...) : _ZipSkip()
    x === nothing && return nothing
    y = _zip_iterate_unknown(tail(is), tail(ss), tail(ds))
    y === nothing && return nothing
    return (x, y)
end
_zip_iterate_unknown(::Tuple{}, ::Tuple{}, ::Tuple{}) = ()
```
-/
def zipUnknown [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) :
    {ks : List K} → TupleVals I ks → TupleVals (fun k => Option (S k)) ks →
      TupleVals (fun _ : K => Option Bool) ks →
      m (Option (TupleVals (fun k => Option (V k × S k)) ks))
  | [], .nil, .nil, .nil => pure (some .nil)
  | k :: _, .cons i is, .cons s ss, .cons d ds => do
      let x ← if d.isNone then do
        match ← ops.run k i s with
        | none => pure none
        | some x => pure (some (some x))
      else pure (some none)
      match x with
      | none => pure none
      | some x =>
          match ← zipUnknown ops is ss ds with
          | none => pure none
          | some rest => pure (some (.cons x rest))

/--
Julia source: base/iterators.jl:487-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function _zip_iterate_rest(is::Tuple, ss::Tuple, xs::Tuple)
    x = xs[1] isa _ZipSkip ? iterate(is[1], ss[1]...) : xs[1]
    x === nothing && return nothing
    y = _zip_iterate_rest(tail(is), tail(ss), xs[2])
    y === nothing && return nothing
    return (x, y...)
end
_zip_iterate_rest(::Tuple{}, ::Tuple{}, ::Tuple{}) = ()
```
-/
def zipRest [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) :
    {ks : List K} → TupleVals I ks → TupleVals (fun k => Option (S k)) ks →
      TupleVals (fun k => Option (V k × S k)) ks →
      m (Option (TupleVals (fun k => V k × S k) ks))
  | [], .nil, .nil, .nil => pure (some .nil)
  | k :: _, .cons i is, .cons s ss, .cons x xs => do
      let x ← match x with
        | some x => pure (some x)
        | none => ops.run k i s
      match x with
      | none => pure none
      | some x =>
          match ← zipRest ops is ss xs with
          | none => pure none
          | some rest => pure (some (.cons x rest))

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
def zipIterateAll [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) {ks : List K}
    (is : TupleVals I ks) (ss : TupleVals (fun k => Option (S k)) ks) :
    m (Option (TupleVals V ks × TupleVals S ks)) := do
  let (finished, ds) ← zipDoneScan ops is ss
  if finished then pure none
  else do
    let xs ← if tupleAllMissing ds then zipInOrder ops is ss else do
      match ← zipUnknown ops is ss ds with
      | none => pure none
      | some xs => zipRest ops is ss xs
    pure (xs.map fun xs =>
      (tupleMap (fun k (p : V k × S k) => p.1) xs,
       tupleMap (fun k (p : V k × S k) => p.2) xs))

/--
Julia source: base/iterators.jl:440-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds iterate(z::Zip) = _zip_iterate_all(z.is, Base.map(_ -> (), z.is))
```
-/
def zipStart [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) {ks : List K} (z : Zip (TupleVals I ks)) :
    m (Option (TupleVals V ks × TupleVals S ks)) :=
  zipIterateAll ops z.is (tupleInitial z.is)

/--
Julia source: base/iterators.jl:441-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds iterate(z::Zip, ss) = _zip_iterate_all(z.is, Base.map(tuple, ss))
```
-/
def zipState [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) {ks : List K} (z : Zip (TupleVals I ks))
    (ss : TupleVals S ks) : m (Option (TupleVals V ks × TupleVals S ks)) :=
  zipIterateAll ops z.is (tupleMap (fun _ s => some s) ss)

/--
Julia source: base/iterators.jl:430-430 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(z::Zip) = _zip_any_isdone(z.is, Base.map(_ -> (), z.is))
```
-/
def zipIsdoneStart [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) {ks : List K} (z : Zip (TupleVals I ks)) :
    m (Option Bool) := zipAnyDone ops z.is (tupleInitial z.is)

/--
Julia source: base/iterators.jl:431-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(z::Zip, ss) = _zip_any_isdone(z.is, Base.map(tuple, ss))
```
-/
def zipIsdoneState [Monad m] {K : Type} {I V S : K → Type}
    (ops : ZipCalls m I V S) {ks : List K} (z : Zip (TupleVals I ks))
    (ss : TupleVals S ks) : m (Option Bool) :=
  zipAnyDone ops z.is (tupleMap (fun _ s => some s) ss)

def tupleMetadata [Monad m] {K : Type} {I A : K → Type}
    (query : (k : K) → I k → m (A k)) :
    {ks : List K} → TupleVals I ks → m (TupleVals A ks)
  | [], .nil => pure .nil
  | k :: _, .cons i is => do
      let a ← query k i
      pure (.cons a (← tupleMetadata query is))

/--
Julia source: base/iterators.jl:1256-1256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(p::ProductIterator) = Base.map(last, p.iterators)
```
-/
def tupleLast [Monad m] {K : Type} {I V : K → Type}
    (last : (k : K) → I k → m (V k)) {ks : List K}
    (p : ProductIterator (TupleVals I ks)) : m (TupleVals V ks) :=
  tupleMetadata last p.iterators

/--
Julia source: base/iterators.jl:1255-1255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(p::ProductIterator) = ProductIterator(Base.map(reverse, p.iterators))
```
-/
def tupleReverse [Monad m] {K : Type} {I R : K → Type}
    (reverse : (k : K) → I k → m (R k)) {ks : List K}
    (p : ProductIterator (TupleVals I ks)) :
    m (ProductIterator (TupleVals R ks)) := do
  pure (productModel (← tupleMetadata reverse p.iterators))

-- R5.1: explicit compositions for the reported Take/Rest/Stateful isempty contracts.
def statefulDone (ops : StatefulOps E H Handle I Y Ty)
    (s : Handle) (_ : Option Unit) : Exec E H (Option Bool) := do
  pure (some (← isdoneStateful ops s))

def takeStatefulEmpty (ops : StatefulOps E H Handle I (α × S) Ty)
    (run : I → S → Exec E H (Option (α × S))) (eof : E)
    (t : Take Handle) : Exec E H Bool :=
  isempty
    (fun (t : Take Handle) (state : Option (JInt64 × Unit)) => match state with
      | none => takeIsdone (statefulDone ops) t
      | some (n, st) => takeIsdoneState (statefulDone ops) t n (some st))
    (iterateTake (fun s _ => iterateStateful ops run eof s)) t

def restStatefulEmpty (ops : StatefulOps E H Handle I (α × S) Ty)
    (run : I → S → Exec E H (Option (α × S))) (eof : E)
    (r : JuliaLean.base.iterators.Rest Handle Unit) : Exec E H Bool :=
  isempty (isdoneRest (statefulDone ops))
    (iterateRest (fun s _ => iterateStateful ops run eof s)) r

def peelOrdinaryStateful (ops : StatefulOps E H Handle I (α × S) Ty)
    (types : DescriptorOps Ty) (typeof : I → Ty)
    (run : I → Option S → Exec E H (Option (α × S))) (eof : E)
    (itr : I) : Exec E H (Option (α × JuliaLean.base.iterators.Rest Handle Unit)) := do
  let s ← stateful ops types typeof (fun it => run it none) itr
  peel (fun s _ => iterateStateful ops (fun it st => run it (some st)) eof s) s

def dropLoop (run : I → Option S → Exec E H (Option (α × S)))
    (rangeRun : Range → Option RS → Exec E H (Option (Index × RS)))
    (itr : I) (r : Range) (rangeState : Option RS) (y : Option (α × S)) :
    Exec E H (Option (α × S)) :=
  fun heap => match rangeRun r rangeState heap with
  | none => none
  | some (.error e, heap) => some (.error e, heap)
  | some (.ok none, heap) => some (.ok y, heap)
  | some (.ok (some (_, nextRange)), heap) =>
      match y with
      | none => some (.ok none, heap)
      | some (_, st) =>
          match run itr (some st) heap with
          | none => none
          | some (.error e, heap) => some (.error e, heap)
          | some (.ok y, heap) => dropLoop run rangeRun itr r (some nextRange) y heap
partial_fixpoint

/--
Julia source: base/iterators.jl:883-891 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(it::Drop)
    y = iterate(it.xs)
    for _ in 1:it.n
        y === nothing && return y
        y = iterate(it.xs, y[2])
    end
    y
end
iterate(it::Drop, state) = iterate(it.xs, state)
```
-/
def iterateDrop (run : I → Option S → Exec E H (Option (α × S)))
    (colon : JInt64 → JInt64 → Exec E H Range)
    (rangeRun : Range → Option RS → Exec E H (Option (Index × RS)))
    (d : Drop I) (state : Option S := none) : Exec E H (Option (α × S)) := do
  match state with
  | some st => run d.xs (some st)
  | none =>
      let y ← run d.xs none
      let r ← colon (JInt.lit .i64 1) d.n
      dropLoop run rangeRun d.xs r none y

/--
Julia source: base/iterators.jl:1065-1065 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(it::Cycle) = iterate(it.xs)
```

Julia source: base/iterators.jl:1068-1072 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(it::Cycle, state)
    y = iterate(it.xs, state)
    y === nothing && return iterate(it)
    y
end
```
-/
def iterateCycle (run : I → Option S → Exec E H (Option (α × S)))
    (c : Cycle I) (state : Option S := none) : Exec E H (Option (α × S)) := do
  match state with
  | none => run c.xs none
  | some st =>
      match ← run c.xs (some st) with
      | none => run c.xs none
      | some y => pure (some y)



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
def accumulateStartBound {I α β S : Type}
    (run : I → Option S → Jl (Option (α × S)))
    (a : Accumulate (JuliaLean.base.reduce.Reducer β α) I
      (JuliaLean.base.reduce.FoldInit β)) :
    Jl (Option (JuliaLean.base.reduce.FoldInit β ×
      (JuliaLean.base.reduce.FoldInit β × S))) := do
  match ← run a.itr none with
  | none => pure none
  | some (x, st) =>
      let value := match a.init with
        | .initial => JuliaLean.base.reduce.bottomRF_initial ⟨a.f⟩ x
        | .value acc => JuliaLean.base.reduce.bottomRF_apply ⟨a.f⟩ acc x
      pure (some (value, (value, st)))

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
def accumulateStateM [Monad m]
    (apply : F → β → α → m β)
    (run : I → Option S → m (Option (α × S)))
    (a : Accumulate F I Init) (st : β × S) :
    m (Option (β × (β × S))) := do
  match ← run a.itr (some st.2) with
  | none => pure none
  | some (x, next) =>
      let value ← apply a.f st.1 x
      pure (some (value, (value, next)))

-- R5.10: force the actual BottomRF's effectful result before storing/yielding it.

def forceFoldInit :
    JuliaLean.base.reduce.FoldInit (Exec E H α) →
      Exec E H (JuliaLean.base.reduce.FoldInit α)
  | .initial => pure .initial
  | .value action => do pure (.value (← action))

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
def accumulateStart
    (run : I → Option S → Exec E H (Option (α × S)))
    (a : Accumulate (JuliaLean.base.reduce.Reducer (Exec E H β) α) I
      (JuliaLean.base.reduce.FoldInit (Exec E H β))) :
    Exec E H (Option (JuliaLean.base.reduce.FoldInit β ×
      (JuliaLean.base.reduce.FoldInit β × S))) := do
  match ← run a.itr none with
  | none => pure none
  | some (x, st) =>
      let value ← forceFoldInit (match a.init with
        | .initial => JuliaLean.base.reduce.bottomRF_initial ⟨a.f⟩ x
        | .value acc => JuliaLean.base.reduce.bottomRF_apply ⟨a.f⟩ acc x)
      pure (some (value, (value, st)))

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
def accumulateState (apply : F → β → α → Exec E H β)
    (run : I → Option S → Exec E H (Option (α × S)))
    (a : Accumulate F I Init) (state : β × S) :
    Exec E H (Option (β × (β × S))) := do
  match ← run a.itr (some state.2) with
  | none => pure none
  | some (x, st) =>
      let value ← apply a.f state.1 x
      pure (some (value, (value, st)))


inductive ProductTuple (I A V S : K → Type) : List K → Type where
  | nil : ProductTuple I A V S []
  | cons {k ks} (iterator : I k) (rest : ProductTuple I A V S ks) :
      ProductTuple I A V S (k :: ks)

inductive ProductValues (V : K → Type) : List K → Type where
  | nil : ProductValues V []
  | cons {k ks} : V k → ProductValues V ks → ProductValues V (k :: ks)

inductive ProductStates (V S : K → Type) : List K → Type where
  | nil : ProductStates V S []
  | cons {k ks} : V k × S k → ProductStates V S ks →
      ProductStates V S (k :: ks)

structure ProductCalls (m : Type → Type) (I A V S : K → Type) where
  run : (k : K) → I k → Option (S k) → m (Option (A k × S k))
  done : (k : K) → I k → Option (S k) → m (Option Bool)
  convertStart : (k : K) → I k → A k → m (V k)
  convertState : (k : K) → V k × S k → A k → m (V k)

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
def piterateTyped [Monad m] {K : Type} {I A V S : K → Type}
    (ops : ProductCalls m I A V S) :
    {ks : List K} → ProductTuple I A V S ks →
      m (Option (ProductStates V S ks))
  | [], .nil => pure (some .nil)
  | k :: ks, .cons i is => do
      match ← ops.run k i none with
      | none => pure none
      | some (x, st) =>
          match ← piterateTyped ops is with
          | none => pure none
          | some rest => pure (some (.cons (← ops.convertStart k i x, st) rest))

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
def piterate1Typed [Monad m] {K : Type} {I A V S : K → Type}
    (ops : ProductCalls m I A V S) :
    {ks : List K} → ProductTuple I A V S ks → ProductStates V S ks →
      m (Option (ProductStates V S ks))
  | [], .nil, .nil => pure none
  | k :: ks, .cons i is, .cons state rest => do
      match ← ops.run k i (some state.2) with
      | some (x, st) =>
          pure (some (.cons (← ops.convertState k state x, st) rest))
      | none =>
          if (← ops.done k i none) = some true then pure none
          else
            match ← piterate1Typed ops is rest with
            | none => pure none
            | some rest =>
                match ← ops.run k i none with
                | none => pure none
                | some (x, st) =>
                    pure (some (.cons (← ops.convertState k state x, st) rest))

def productValues {K : Type} {V S : K → Type} :
    {ks : List K} → ProductStates V S ks → ProductValues V ks
  | [], .nil => .nil
  | _ :: _, .cons (v, _) rest => .cons v (productValues rest)

/--
Julia source: base/iterators.jl:1204-1204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline isdone(P::ProductIterator) = any(isdone, P.iterators)
```
-/
def productIsdoneTyped [Monad m] {K : Type} {I A V S : K → Type}
    (ops : ProductCalls m I A V S) :
    {ks : List K} → ProductTuple I A V S ks → m (Option Bool)
  | [], .nil => pure (some false)
  | k :: ks, .cons i is => do
      let d ← ops.done k i none
      if d = some true then pure d
      else pure (boolOrMissing d (← productIsdoneTyped ops is))

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
def pisdoneTyped [Monad m] [MonadExceptOf JlError m]
    {K : Type} {I A V S : K → Type}
    (ops : ProductCalls m I A V S) :
    {ks : List K} → ProductTuple I A V S ks → ProductStates V S ks →
      m (Option Bool)
  | [], .nil, .nil => throw (.argumentError "tuple must be non-empty")
  | k :: ks, .cons i is, .cons state rest => do
      let d ← ops.done k i (some state.2)
      if d != some true then pure d
      else do
        let d ← ops.done k i none
        if d != some true then pure d
        else pisdoneTyped ops is rest

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
def iterateProductTyped [Monad m] [MonadExceptOf JlError m]
    {K : Type} {I A V S : K → Type}
    (ops : ProductCalls m I A V S) {ks : List K}
    (p : ProductTuple I A V S ks) (state : Option (ProductStates V S ks)) :
    m (Option (ProductValues V ks × ProductStates V S ks)) := do
  let next ← (match ks, p, state with
    | [], .nil, none => pure (some .nil)
    | [], .nil, some _ => pure none
    | _ :: _, p, none => do
        if (← productIsdoneTyped ops p) = some true then pure none
        else piterateTyped ops p
    | _ :: _, p, some state => do
        if (← pisdoneTyped ops p state) = some true then pure none
        else piterate1Typed ops p state : m (Option (ProductStates V S ks)))
  pure (next.map fun st => (productValues st, st))

/--
Julia source: base/iterators.jl:1257-1257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect(a::ProductIterator, b::ProductIterator) = ProductIterator(intersect.(a.iterators, b.iterators))
```
-/
def intersectProductM [Monad m]
    (intersect : I → J → m R)
    (broadcast : (I → J → m R) → Is → Js → m Rs)
    (a : ProductIterator Is) (b : ProductIterator Js) :
    m (ProductIterator Rs) := do
  pure (productModel (← broadcast intersect a.iterators b.iterators))

@[simp] def tupleTail {α : Type} : List α → Jl (List α)
  | _ :: xs => .ok xs
  | [] => .error (.argumentError "Cannot call tail on an empty tuple.")

/--
Julia source: base/iterators.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(f, arg, args...) = Base.Generator(f, arg, args...)
```
-/
def mapSingleModel {F I : Type} (f : F) (arg : I) :
    JuliaLean.base.generator.Generator I F :=
  ⟨f, arg⟩

def mapManyModel {F G I1 I2 Rest : Type}
    (splat : F → G)
    (f : F) (arg1 : I1) (arg2 : I2) (args : Rest) :
    JuliaLean.base.generator.Generator (Zip (I1 × I2 × Rest)) G :=
  JuliaLean.base.generator.generatorMany splat
    (fun i1 i2 rest => zipModel (i1, i2, rest)) f arg1 arg2 args

def mapModel {F G I : Type}
    (splat : F → G)
    (f : F) (arg : I) (args : List I := []) :
    JuliaLean.base.generator.Generator I F ⊕
      JuliaLean.base.generator.Generator (Zip (List I)) G :=
  match args with
  | [] => .inl ⟨f, arg⟩
  | arg2 :: rest =>
      .inr (JuliaLean.base.generator.generatorMany splat
        (fun i1 i2 rs => zipModel (i1 :: i2 :: rs)) f arg arg2 rest)

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
def sourceMethod136 {m : Type → Type} [Monad m]
    (eachindex : Arr → m Indices) (reverseIndex : Indices → m R)
    (run : R → Option S → m (Option (K × S))) (getInbounds : Arr → K → m V)
    (a : Reverse Arr) (state : Option (R × S) := none) : m (Option (V × (R × S))) := do
  let (indices,st) ← match state with
    | none => do pure (← reverseIndex (← eachindex a.itr),none)
    | some (indices,st) => pure (indices,some st)
  match ← run indices st with
  | none => pure none
  | some (index,next) => pure (some (← getInbounds a.itr index,(indices,next)))

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
def sourceMethod145 {m : Type → Type} [Monad m]
    (eachindex : Arr → m Indices) (reverseIndex : Indices → m R)
    (run : R → Option S → m (Option (K × S))) (getindex : Arr → K → m V)
    (a : Reverse Arr) (state : Option (R × S) := none) : m (Option (V × (R × S))) := do
  let (indices,st) ← match state with
    | none => do pure (← reverseIndex (← eachindex a.itr),none)
    | some (indices,st) => pure (indices,some st)
  match ← run indices st with
  | none => pure none
  | some (index,next) => pure (some (← getindex a.itr index,(indices,next)))

/--
Julia source: base/iterators.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::Reverse{Union{}}) = throw(ArgumentError("cannot iterate a reversed iterator of type Union{}"))
```
-/
def sourceMethod153 {m : Type → Type} [Monad m] (argumentError : String → m (Option Y))
    (_r : Reverse UnionBottom) : m (Option Y) :=
  argumentError "cannot iterate a reversed iterator of type Union{}"

/--
Julia source: base/iterators.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
iterate(r::Reverse{Union{}}, state) = throw(ArgumentError("cannot iterate a reversed iterator of type Union{}"))
```
-/
def sourceMethod154 {m : Type → Type} [Monad m] (argumentError : String → m (Option Y))
    (_r : Reverse UnionBottom) (_state : State) : m (Option Y) :=
  argumentError "cannot iterate a reversed iterator of type Union{}"

/--
Julia source: base/iterators.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(R::AbstractRange) = Base.reverse(R) # copying ranges is cheap
```
-/
def sourceMethod156 {m : Type → Type} [Monad m] (reverse : R → m Reversed) (r : R) : m Reversed :=
  reverse r

/--
Julia source: base/iterators.jl:157-157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(G::Generator) = Generator(G.f, reverse(G.iter))
```
-/
def sourceMethod157 {m : Type → Type} [Monad m] (reverse : I → m R)
    (g : JuliaLean.base.generator.Generator I F) :
    m (JuliaLean.base.generator.Generator R F) := do
  pure ⟨g.f, ← reverse g.iter⟩

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
def sourceMethod159 {α : Type} [IsNumberOrAbstractChar α] (x : α) : α := x

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
def iterateReverseTuple {m : Type → Type} [Monad m] (length : A → m JInt64) (getindex : A → JInt64 → m V)
    (r : Reverse A) (state : Option JInt64 := none) : m (Option (V × JInt64)) := do
  let index ← match state with | none => length r.itr | some i => pure i
  if index.val < 1 then pure none
  else pure (some (← getindex r.itr index,JuliaLean.base.int.sub_int index (JInt.lit .i64 1)))

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
def enumerateEltype {I : Type} (eltype : I → Option Type)
    (tupleOrBottom : Option Type → Option Type → Option Type := tupleOrBottomPair)
    (e : Enumerate I) : Option Type :=
  tupleOrBottom (some JInt64) (eltype e.itr)

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
def sourceMethod228 {m : Type → Type} [Monad m] (run : R → Option S → m (Option (V × S)))
    (subtract : Index → JInt64 → m NextIndex) (_r : Reverse (Enumerate I))
    (state : Index × R × Option S) : m (Option ((Index × V) × (NextIndex × R × S))) := do
  let (index,ri,st) := state
  match ← run ri st with
  | none => pure none
  | some (value,next) => pure (some ((index,value),(← subtract index (JInt.lit .i64 1),ri,next)))

/--
Julia source: base/iterators.jl:224-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function iterate(r::Reverse{<:Enumerate})
    ri = reverse(r.itr.itr)
    iterate(r, (length(ri), ri))
end
```
-/
def sourceMethod224 {m : Type → Type} [Monad m] (reverse : I → m R) (length : R → m Index)
    (run : R → Option S → m (Option (V × S))) (subtract : Index → JInt64 → m NextIndex)
    (r : Reverse (Enumerate I)) : m (Option ((Index × V) × (NextIndex × R × S))) := do
  let ri ← reverse r.itr.itr
  sourceMethod228 run subtract r (← length ri,ri,none)

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
def pairsCartesian {A Ax K V I : Type}
    (axes : A → Jl Ax) (cartesianIndices : Ax → Jl I)
    (data : A) : Jl (PairsModel K V I A) := do
  let ax ← axes data
  let ci ← cartesianIndices ax
  pure ⟨data, some ci⟩

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
def sourceMethod319 {K V : Type}
    (_ : PairsModel K V (UnitRangeIndices K) (TupleContainer V)) : IteratorSizeTag := .hasLength

/--
Julia source: base/iterators.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haskey(v::Pairs, key) = key in keys(v)
```
-/
def haskeyPairsModel {K V I D : Type} (keys : PairsModel K V I D → List K) (contains : List K → K → Bool)
    (v : PairsModel K V I D) (key : K) : Bool := contains (keys v) key

/--
Julia source: base/iterators.jl:332-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(f::Base.Callable, v::Pairs, key) = get(f, values(v), key)
```
-/
def getPairsWithFunction {F K V I D R : Type} (get : F → D → K → Jl R)
    (f : F) (v : PairsModel K V I D) (key : K) : Jl R := get f v.data key

/--
Julia source: base/iterators.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_zip_min_length(is::Tuple{}) = nothing
```
-/
def sourceMethod394 {m : Type → Type} [Pure m] {L : Type} : m (Option L) := pure none

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
def sourceMethod385 {m : Type → Type} [Monad m] {Kind : Type} {Iter : Kind → Type}
    (trait : (kind : Kind) → Iter kind → m IteratorSizeTag)
    (length : (kind : Kind) → Iter kind → m L) (minimum : L → L → m L) :
    {ks : List Kind} → TupleVals Iter ks → m (Option L)
  | [], .nil => sourceMethod394
  | k :: _, .cons itr rest => do
      let n ← sourceMethod385 trait length minimum rest
      if (← trait k itr) = .isInfinite then pure n
      else
        match n with
        | none => pure (some (← length k itr))
        | some n => pure (some (← minimum n (← length k itr)))

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
def zipLength {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {Kind : Type} {Iter : Kind → Type}
    (trait : (kind : Kind) → Iter kind → m IteratorSizeTag)
    (length : (kind : Kind) → Iter kind → m L) (minimum : L → L → m L)
    {ks : List Kind} (z : Zip (TupleVals Iter ks)) : m L := do
  match ← sourceMethod385 trait length minimum z.is with
  | none => throwThe JlError (.argumentError "iterator is of undefined length")
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
def sourceMethod414 {m : Type → Type} [Monad m] (intersect : A → B → m R) (a : A) (b : B) : m (List R) := do
  pure [← intersect a b]

/--
Julia source: base/iterators.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_tuple_shape((m,)::Tuple{Integer}, (n,)::Tuple{Integer}) = (min(m, n),)
```
-/
def sourceMethod415 {m : Type → Type} [Monad m] (minimum : A → B → m R) (a : A) (b : B) : m (List R) := do
  pure [← minimum a b]

/--
Julia source: base/iterators.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_tuple_shape(a, b) = promote_shape(a, b)
```
-/
def sourceMethod416 {m : Type → Type} [Monad m] (promote : A → B → m R) (a : A) (b : B) : m R :=
  promote a b

/--
Julia source: base/iterators.jl:418-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_tuple_shape(a) = a
```
-/
def sourceMethod418 {A : Type} (a : A) : A := a

def promoteTupleShape2 {m : Type → Type} [Monad m] (asOneTo : A → Option O) (fromOneTo : O → A)
    (intersect : O → O → m O) (asInteger : A → Option N) (fromInteger : N → A)
    (minimum : N → N → m N) (promote : List A → List A → m (List A))
    (a b : List A) : m (List A) :=
  match a,b with
  | [a],[b] =>
      match asOneTo a,asOneTo b with
      | some a,some b =>
          sourceMethod414 (fun a b => do pure (fromOneTo (← intersect a b))) a b
      | _,_ =>
          match asInteger a,asInteger b with
          | some a,some b =>
              sourceMethod415 (fun a b => do pure (fromInteger (← minimum a b))) a b
          | _,_ => sourceMethod416 promote [a] [b]
  | _,_ => sourceMethod416 promote a b

/--
Julia source: base/iterators.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_promote_tuple_shape(a, b...) = _promote_tuple_shape(a, _promote_tuple_shape(b...))
```
-/
def sourceMethod417 {m : Type → Type} [Monad m] {Kind : Type} (two : A → A → m A) :
    {ks : List Kind} → A → TupleVals (fun _ : Kind => A) ks → m A
  | [], first, .nil => pure (sourceMethod418 first)
  | _ :: _, first, .cons next rest => do two first (← sourceMethod417 two next rest)

def zipShape {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {Kind : Type} {Iter : Kind → Type}
    (query : (kind : Kind) → Iter kind → m A) (two : A → A → m A)
    {ks : List Kind} (z : Zip (TupleVals Iter ks)) : m A := do
  let shapes ← tupleMetadata query z.is
  match ks,shapes with
  | [], .nil => throwThe JlError (.methodError "_promote_tuple_shape")
  | _ :: _, .cons first rest =>
      sourceMethod417 two first rest
/--
Julia source: base/iterators.jl:412-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(z::Zip) = _promote_tuple_shape(Base.map(size, z.is)...)
```
-/
def sourceMethod412 {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {Kind : Type} {Iter : Kind → Type}
    (size : (kind : Kind) → Iter kind → m A) (two : A → A → m A)
    {ks : List Kind} (z : Zip (TupleVals Iter ks)) : m A :=
  zipShape size two z

/--
Julia source: base/iterators.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(z::Zip) = _promote_tuple_shape(Base.map(axes, z.is)...)
```
-/
def sourceMethod413 {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {Kind : Type} {Iter : Kind → Type}
    (axes : (kind : Kind) → Iter kind → m A) (two : A → A → m A)
    {ks : List Kind} (z : Zip (TupleVals Iter ks)) : m A :=
  zipShape axes two z

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
Julia source: base/iterators.jl:512-512 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(a::IsInfinite, b::IsInfinite) = IsInfinite()
```
-/
def zipIteratorSizeInfiniteInfinite (_ _ : IteratorSizeTag) : IteratorSizeTag := .isInfinite

def zipIteratorSizeNonInfiniteLeft (a b : IteratorSizeTag) : IteratorSizeTag :=
  match a, b with
  | .hasLength, .isInfinite => zipIteratorSizeLengthInfinite a b
  | .hasShape _, .isInfinite => zipIteratorSizeShapeInfinite a b
  | _, _ => zipIteratorSizeTwo a b

/--
Julia source: base/iterators.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(a::IsInfinite, b) = zip_iteratorsize(b,a)
```
-/
def zipIteratorSizeInfiniteOther (a b : IteratorSizeTag) : IteratorSizeTag :=
  match b with
  | .isInfinite => zipIteratorSizeInfiniteInfinite b a
  | _ => zipIteratorSizeNonInfiniteLeft b a

def zipIteratorSizeDispatch2 (a b : IteratorSizeTag) : IteratorSizeTag :=
  match a, b with
  | .isInfinite, .isInfinite => zipIteratorSizeInfiniteInfinite a b
  | .isInfinite, _ => zipIteratorSizeInfiniteOther a b
  | _, _ => zipIteratorSizeNonInfiniteLeft a b

/--
Julia source: base/iterators.jl:513-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
zip_iteratorsize(a, b, tail...) = zip_iteratorsize(a, zip_iteratorsize(b, tail...))
```
-/
def zipIteratorSizeMany (a b : IteratorSizeTag) : List IteratorSizeTag → IteratorSizeTag
  | [] => zipIteratorSizeDispatch2 a (zipIteratorSizeOne b)
  | c :: cs => zipIteratorSizeDispatch2 a (zipIteratorSizeMany b c cs)

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
def zipIteratorEltypeMany (a : IteratorEltypeTag) : List IteratorEltypeTag → IteratorEltypeTag
  | [] => andIteratorEltypeDispatch a zipIteratorEltypeEmpty
  | [b] => andIteratorEltypeDispatch a (zipIteratorEltypeOne b)
  | b :: c :: cs => andIteratorEltypeDispatch a (zipIteratorEltypeMany b (c :: cs))

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
  | [a, b] => zipIteratorSizeDispatch2 a b
  | a :: b :: rest => zipIteratorSizeMany a b rest

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
def sourceMethod519 {Is N R : Type} (z : Zip Is) (length : Zip Is → Jl N)
    (nth : Zip Is → N → Jl R) : Jl R := do
  nth z (← length z)

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
def zipLengthsFiniteEqualOn {I Len : Type} [DecidableEq Len]
    (iteratorSize : I → IteratorSizeTag) (length : I → Jl Len) :
    List I → Jl (Bool × Option Len)
  | [] => pure (true, none)
  | itr :: rest =>
      if iteratorSize itr == .isInfinite || iteratorSize itr == .sizeUnknown then
        pure (false, none)
      else do
        let m ← length itr
        let (b, n) ← zipLengthsFiniteEqualOn iteratorSize length rest
        pure (b && (n.isNone || n == some m), some m)

def reverseZipModel {I R Len : Type} [DecidableEq Len]
    (iteratorSize : I → IteratorSizeTag) (length : I → Jl Len)
    (reverse : I → Jl R) (z : Zip (List I)) : Jl (Zip (List R)) := do
  let (same, _) ← zipLengthsFiniteEqualOn iteratorSize length z.is
  if !same then
    .error (.argumentError "Cannot reverse zipped iterators of unknown, infinite, or unequal lengths")
  else do
    let revIs ← z.is.mapM reverse
    pure (zipModel revIs)

/--
Julia source: base/iterators.jl:576-576 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter(flt, itr) = Filter(flt, itr)
```
-/
def sourceMethod576 {F I : Type} (flt : F) (itr : I) : Filter F I := ⟨flt, itr⟩

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
def reverseFilter {m : Type → Type} [Monad m] (reverse : I → m R) (f : Filter F I) :
    m (Filter F R) := do pure ⟨f.flt, ← reverse f.itr⟩

/--
Julia source: base/iterators.jl:599-599 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(f::Filter) = first(reverse(f))
```
-/
def lastFilter {m : Type → Type} [Monad m] (reverse : Filter F I → m R) (first : R → m V)
    (f : Filter F I) : m V := do first (← reverse f)

/--
Julia source: base/iterators.jl:641-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
accumulate(f, itr; init = Base._InitialValue()) = Accumulate(f, itr, init)
```
-/
def accumulateModel {F : Type u} {I T : Type} (f : F) (itr : I) (init : T) : Accumulate F I T :=
  ⟨f, itr, init⟩

/--
Julia source: base/iterators.jl:770-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:Count{T}}) where {T} = T
```
-/
def countEltype {T S : Type} (_ : Count T S) : Type := T

/--
Julia source: base/iterators.jl:661-661 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(itr::Accumulate) = length(itr.itr)
```
-/
def accumulateLength {F : Type u} {I  T N : Type} (length : I → Jl N) (itr : Accumulate F I T) : Jl N := length itr.itr

/--
Julia source: base/iterators.jl:662-662 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(itr::Accumulate) = size(itr.itr)
```
-/
def accumulateSize {F : Type u} {I  T N : Type} (size : I → Jl N) (itr : Accumulate F I T) : Jl N := size itr.itr

/--
Julia source: base/iterators.jl:664-664 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:Accumulate{<:Any,I}}) where {I} = IteratorSize(I)
```
-/
def accumulateIteratorSize {F : Type u} {I  T : Type} (iteratorSize : I → IteratorSizeTag)
    (itr : Accumulate F I T) : IteratorSizeTag := iteratorSize itr.itr

/--
Julia source: base/iterators.jl:665-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{<:Accumulate}) = EltypeUnknown()
```
-/
def accumulateIteratorEltype : IteratorEltypeTag := .eltypeUnknown

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
Julia source: base/iterators.jl:767-767 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
countfrom()                              = Count(1, 1)
```
-/
def countfromDefault : Count JInt64 JInt64 :=
  ⟨JInt.lit .i64 1, JInt.lit .i64 1⟩

def iterateCountStart {m : Type → Type} [Monad m] (add : Start → Step → m Next)
    (it : Count Start Step) : m (Start × Next) := iterateCountState add it it.start

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
def mkTake {m : Type → Type} [Monad m] (ltZero : N → m Bool) (convertField : N → m JInt64)
    (argumentError : String → m (Take I)) (xs : I) (n : N) : m (Take I) := do
  if ← ltZero n then argumentError "Take length must be non-negative"
  else pure ⟨xs, ← convertField n⟩

/--
Julia source: base/iterators.jl:815-815 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
take(xs, n::Integer) = Take(xs, Int(n))
```
-/
def takeModel {m : Type → Type} [Monad m] (toInt : N → m JInt64)
    (construct : I → JInt64 → m (Take I)) (xs : I) (n : N) : m (Take I) := do
  construct xs (← toInt n)

/--
Julia source: base/iterators.jl:816-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
take(xs::Take, n::Integer) = Take(xs.xs, min(Int(n), xs.n))
```
-/
def takeTakeModel {m : Type → Type} [Monad m] (toInt : N → m JInt64)
    (minimum : JInt64 → JInt64 → m JInt64)
    (construct : I → JInt64 → m (Take I)) (xs : Take I) (n : N) : m (Take I) := do
  construct xs.xs (← minimum (← toInt n) xs.n)

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
Julia source: base/iterators.jl:840-843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function Drop(xs::I, n::Integer) where {I}
        n < 0 && throw(ArgumentError("Drop length must be non-negative"))
        return new{I}(xs, n)
    end
```
-/
def mkDrop {m : Type → Type} [Monad m] (ltZero : N → m Bool) (convertField : N → m JInt64)
    (argumentError : String → m (Drop I)) (xs : I) (n : N) : m (Drop I) := do
  if ← ltZero n then argumentError "Drop length must be non-negative"
  else pure ⟨xs, ← convertField n⟩

/--
Julia source: base/iterators.jl:871-871 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
drop(xs, n::Integer) = Drop(xs, Int(n))
```
-/
def dropModel {m : Type → Type} [Monad m] (toInt : N → m JInt64)
    (construct : I → JInt64 → m (Drop I)) (xs : I) (n : N) : m (Drop I) := do
  construct xs (← toInt n)

/--
Julia source: base/iterators.jl:872-872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
drop(xs::Take, n::Integer) = Take(drop(xs.xs, Int(n)), max(0, xs.n - Int(n)))
```
-/
def dropTakeModel {m : Type → Type} [Monad m] (toInt : N → m JInt64)
    (dropModel : I → JInt64 → m D)
    (maximum : JInt64 → JInt64 → m JInt64)
    (construct : D → JInt64 → m (Take D)) (xs : Take I) (n : N) : m (Take D) := do
  let d ← dropModel xs.xs (← toInt n)
  let remaining := JuliaLean.base.int.sub_int xs.n (← toInt n)
  construct d (← maximum (JInt.lit .i64 0) remaining)

/--
Julia source: base/iterators.jl:873-873 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
drop(xs::Drop, n::Integer) = Drop(xs.xs, Int(n) + xs.n)
```
-/
def dropDropModel {m : Type → Type} [Monad m] (toInt : N → m JInt64)
    (construct : I → JInt64 → m (Drop I)) (xs : Drop I) (n : N) : m (Drop I) := do
  let n ← toInt n
  construct xs.xs (JuliaLean.base.int.add_int n xs.n)

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
def sourceMethod1016 {m : Type → Type} [Monad m] {Y : Type} (pairs : I → m P)
    (unpack : Y → m (K × V)) (apply : F → V → m Result) (f : F) (itr : I) :
    m (JuliaLean.base.generator.Generator (Filter (Y → m Result) P) (Y → m K)) := do
  let collection ← pairs itr
  pure ⟨(fun pair => do pure (← unpack pair).1),
    sourceMethod576 (fun pair => do apply f (← unpack pair).2) collection⟩

/--
Julia source: base/iterators.jl:1018-1018 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findeach(it) = findeach(identity, it)
```
-/
def sourceMethod1018 {m : Type → Type} [Monad m] {Y : Type} (pairs : I → m P) (unpack : Y → m (K × V)) (itr : I) :
    m (JuliaLean.base.generator.Generator (Filter (Y → m V) P) (Y → m K)) :=
  sourceMethod1016 pairs unpack (fun (_ : Unit) value => pure value) () itr

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
Julia source: base/iterators.jl:1074-1074 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(it::Cycle) = Cycle(reverse(it.xs))
```
-/
def reverseCycle {m : Type → Type} [Monad m] (reverse : I → m R) (c : Cycle I) :
    m (Cycle R) := do pure ⟨← reverse c.xs⟩

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
def repeatedNModel {m : Type → Type} [Monad m] (toInt : N → m JInt64)
    (takeModel : Repeated O → JInt64 → m (Take (Repeated O))) (x : O) (n : N) :
    m (Take (Repeated O)) := do
  takeModel (repeatedModel x) (← toInt n)

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
Julia source: base/iterators.jl:1120-1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(it::Union{Repeated,Take{<:Repeated}}) = it
```
-/
def reverseTakeRepeated {O : Type} (it : Take (Repeated O)) : Take (Repeated O) := it

/--
Julia source: base/iterators.jl:1121-1121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(it::Union{Repeated,Take{<:Repeated}}) = first(it)
```
-/
def lastTakeRepeated {O : Type} (first : Take (Repeated O) → Jl O)
    (it : Take (Repeated O)) : Jl O := first it

/--
Julia source: base/iterators.jl:1150-1150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{ProductIterator{Tuple{}}}) = HasShape{0}()
```
-/
def sourceMethod1150 : IteratorSizeTag := .hasShape 0

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

def prodIteratorSizeDispatch2 (a b : IteratorSizeTag) : IteratorSizeTag :=
  match a, b with
  | .hasLength, .hasLength => sourceMethod1157
  | .hasLength, .hasShape n => sourceMethod1158 n
  | .hasShape n, .hasLength => sourceMethod1159 n
  | .hasShape m, .hasShape n => sourceMethod1160 m n
  | .isInfinite, .isInfinite => sourceMethod1163
  | _, .isInfinite => sourceMethod1164 a
  | .isInfinite, _ => sourceMethod1165 b
  | _, _ => sourceMethod1166 a b

/--
Julia source: base/iterators.jl:1167-1167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prod_iteratorsize(a, b, tail...) = prod_iteratorsize(a, prod_iteratorsize(b, tail...))
```
-/
def sourceMethod1167 (a b : IteratorSizeTag) : List IteratorSizeTag → IteratorSizeTag
  | [] => prodIteratorSizeDispatch2 a (sourceMethod1155 b)
  | c :: cs => prodIteratorSizeDispatch2 a (sourceMethod1167 b c cs)

def prodIteratorSizeDispatch : List IteratorSizeTag → IteratorSizeTag
  | [] => sourceMethod1154
  | [a] => sourceMethod1155 a
  | [a, b] => prodIteratorSizeDispatch2 a b
  | a :: b :: c :: cs => sourceMethod1167 a b (c :: cs)

/--
Julia source: base/iterators.jl:1151-1152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{ProductIterator{T}}) where {N, T<:Tuple{Vararg{Any, N}}} =
    prod_iteratorsize(ntuple(n -> IteratorSize(fieldtype(T, n)), N)..., HasShape{0}())
```
-/
def sourceMethod1151 {T F : Type}
    (fieldtype : T → Nat → F) (iteratorSize : F → IteratorSizeTag)
    (N : Nat) (p : ProductIterator T)
    (ntuple : (Nat → IteratorSizeTag) → Nat → List IteratorSizeTag :=
      fun f n => (List.range n).map (fun i => f (i + 1))) : IteratorSizeTag :=
  let traits := ntuple (fun n => iteratorSize (fieldtype p.iterators n)) N
  prodIteratorSizeDispatch (traits ++ [.hasShape 0])

/--
Julia source: base/iterators.jl:1170-1170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size(::Tuple{}) = ()
```
-/
def sourceMethod1170 {Dim : Type} : List Dim := []

/--
Julia source: base/iterators.jl:1172-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size1(a, ::HasShape)  = size(a)
```
-/
def sourceMethod1172 {I Dim : Type} (size : I → Jl (List Dim)) (item : I)
    (_ : IteratorSizeTag) : Jl (List Dim) := size item

/--
Julia source: base/iterators.jl:1173-1173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size1(a, ::HasLength) = (length(a),)
```
-/
def sourceMethod1173 {I Dim : Type} (length : I → Jl Dim) (item : I)
    (_ : IteratorSizeTag) : Jl (List Dim) := do pure [← length item]

/--
Julia source: base/iterators.jl:1174-1175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size1(a, A) =
    throw(ArgumentError(LazyString("Cannot compute size for object of type ", typeof(a))))
```
-/
def sourceMethod1174 {I Dim : Type} (a : I) (_ : IteratorSizeTag)
    (typeof : I → String := fun _ => "Any") : Jl (List Dim) :=
  .error (.argumentError s!"Cannot compute size for object of type {typeof a}")

/--
Julia source: base/iterators.jl:1171-1171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_size(t::Tuple) = (_prod_size1(t[1], IteratorSize(t[1]))..., _prod_size(tail(t))...)
```
-/
def sourceMethod1171 {I Dim : Type} (size : I → Jl (List Dim)) (length : I → Jl Dim)
    (trait : I → IteratorSizeTag) (items : List I)
    (typeof : I → String := fun _ => "Any") : Jl (List Dim) :=
  match items with
  | [] => pure sourceMethod1170
  | item :: rest => do
      let first ← match trait item with
        | .hasShape d => sourceMethod1172 size item (.hasShape d)
        | .hasLength => sourceMethod1173 length item .hasLength
        | sz => sourceMethod1174 item sz typeof
      pure (first ++ (← sourceMethod1171 size length trait rest typeof))

/--
Julia source: base/iterators.jl:1169-1169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(P::ProductIterator) = _prod_size(P.iterators)
```
-/
def sourceMethod1169 {I Dim : Type} (size : I → Jl (List Dim)) (length : I → Jl Dim)
    (trait : I → IteratorSizeTag) (p : ProductIterator (List I))
    (typeof : I → String := fun _ => "Any") : Jl (List Dim) :=
  sourceMethod1171 size length trait p.iterators typeof

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
def sourceMethod1182 {I : Type} (a : I) (_ : IteratorSizeTag)
    (typeof : I → String := fun _ => "Any") : Jl (List Nat) :=
  .error (.argumentError s!"Cannot compute indices for object of type {typeof a}")

/--
Julia source: base/iterators.jl:1179-1179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_prod_indices(t::Tuple) = (_prod_axes1(t[1], IteratorSize(t[1]))..., _prod_indices(tail(t))...)
```
-/
def sourceMethod1179 {I : Type} (axes : I → Jl (List Nat)) (length : I → Jl Nat)
    (trait : I → IteratorSizeTag) (items : List I)
    (typeof : I → String := fun _ => "Any") : Jl (List Nat) :=
  match items with
  | [] => pure sourceMethod1178
  | item :: rest => do
      let first ← match trait item with
        | .hasShape d => sourceMethod1180 axes item (.hasShape d)
        | .hasLength => sourceMethod1181 length item .hasLength
        | sz => sourceMethod1182 item sz typeof
      pure (first ++ (← sourceMethod1179 axes length trait rest typeof))

/--
Julia source: base/iterators.jl:1177-1177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
axes(P::ProductIterator) = _prod_indices(P.iterators)
```
-/
def sourceMethod1177 {I : Type} (axes : I → Jl (List Nat)) (length : I → Jl Nat)
    (trait : I → IteratorSizeTag) (p : ProductIterator (List I))
    (typeof : I → String := fun _ => "Any") : Jl (List Nat) :=
  sourceMethod1179 axes length trait p.iterators typeof

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
def checkedMulReducer (checkedMul : JInt64 → JInt64 → Jl JInt64) :
    JuliaLean.base.reduce.Reducer (Jl JInt64) JInt64 where
  first := fun x => .value (.ok x)
  step := fun state x =>
    match state with
    | .initial => .value (.ok x)
    | .value acc => .value (do checkedMul (← acc) x)
  empty := .ok (.ok (JInt.lit .i64 1))

def productLength {I : Type}
    (size : I → Jl (List JInt64)) (length : I → Jl JInt64)
    (trait : I → IteratorSizeTag)
    (p : ProductIterator (List I))
    (checkedMul : JInt64 → JInt64 → Jl JInt64 := JuliaLean.base.checked.checkedMulBits)
    (typeof : I → String := fun _ => "Any") : Jl JInt64 := do
  let dims ← sourceMethod1169 size length trait p typeof
  let reduced ← JuliaLean.base.reduce.reduce
    (fun _ => .hasEltype) id (checkedMulReducer checkedMul)
    (.values dims) (.value (.ok (JInt.lit .i64 1)))
  reduced

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
def productIteratorEltype {T F : Type}
    (fieldtype : T → Nat → F) (iteratorEltype : F → IteratorEltypeTag)
    (N : Nat) (p : ProductIterator T)
    (ntuple : (Nat → IteratorEltypeTag) → Nat → List IteratorEltypeTag :=
      fun f n => (List.range n).map (fun i => f (i + 1))) :
    Jl IteratorEltypeTag :=
  let E := ntuple (fun n => iteratorEltype (fieldtype p.iterators n)) N
  if E.any (fun I => I == .eltypeUnknown) then
    .ok .eltypeUnknown
  else
    match E.getLast? with
    | some last => .ok last
    | none => .error .boundsError

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

def iteratorAny {I : Type} (p : I → Jl (Option Bool)) : List I → Jl (Option Bool)
  | [] => pure (some false)
  | x :: xs => do
      let result ← p x
      if result = some true then pure result
      else boolOrMissing result <$> iteratorAny p xs

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
@[simp] def tupleFirstElem {α : Type} : List α → Jl α
  | x :: _ => .ok x
  | [] => .error (.argumentError "tuple must be non-empty")

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
Julia source: base/iterators.jl:1329-1329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatten_length(f, ::Type{<:Number}) = length(f.it)
```
-/
def flattenLengthNumber {I L : Type} (length : I → Jl L) (f : Flatten I) : Jl L :=
  length f.it

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
  | .emptyTuple => flattenTupleLength length checkedMul f 0
  | .fixedTuple n => flattenTupleLength length checkedMul f n
  | .number => flattenLengthNumber length f
  | .tuple | .other => sourceMethod1330

/--
Julia source: base/iterators.jl:1333-1333 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(f::Flatten{Tuple{}}) = 0
```
-/
def flattenEmptyLength : Nat := 0

/--
Julia source: base/iterators.jl:1379-1379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(f::Flatten) = Flatten(reverse(itr) for itr in reverse(f.it))
```
-/
def sourceMethod1379 {m : Type → Type} [Monad m] {I : Type} (reverseOuter : O → m R) (reverseInner : I → m J)
    (f : Flatten O) : m (Flatten (JuliaLean.base.generator.Generator R (I → m J))) := do
  pure (flattenModel ⟨reverseInner,← reverseOuter f.it⟩)

/--
Julia source: base/iterators.jl:1380-1380 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
last(f::Flatten) = first(reverse(f))
```
-/
def lastFlatten {m : Type → Type} [Monad m] (reverse : Flatten I → m R) (first : R → m V)
    (f : Flatten I) : m V := do first (← reverse f)

/--
Julia source: base/iterators.jl:1421-1421 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
flatmap(f, c...) = flatten(map(f, c...))
```
-/
def flatmapModel {m : Type → Type} [Monad m] (map : F → Args → m Mapped)
    (f : F) (args : Args) : m (Flatten Mapped) := do
  pure (flattenModel (← map f args))

/--
Julia source: base/iterators.jl:1449-1449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{PartitionIterator{T}}) where {T} = Vector{eltype(T)}
```
-/
inductive PartitionIndexTupleType where
  | unitRangeInt
  deriving Repr, DecidableEq

inductive PartitionEltype (T : Type) (Elem : Type 1) where
  | vector (elementType : Elem)
  | abstractVector (elementType : Elem)
  | subArray (elementType : Elem) (ndims : Nat) (parentType : T)
      (indexTuple : PartitionIndexTupleType) (fastLinear : Bool)
  deriving Repr, DecidableEq

def sourceMethod1449 {T : Type} {Elem : Type 1} (eltype : T → Elem) (p : PartitionIterator T) :
    PartitionEltype T Elem :=
  .vector (eltype p.c)

/--
Julia source: base/iterators.jl:1451-1451 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{PartitionIterator{T}}) where {T<:AbstractArray} = AbstractVector{eltype(T)}
```
-/
def sourceMethod1451 {T : Type} {Elem : Type 1} (eltype : T → Elem) (p : PartitionIterator T) :
    PartitionEltype T Elem :=
  .abstractVector (eltype p.c)

/--
Julia source: base/iterators.jl:1453-1453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{PartitionIterator{T}}) where {T<:Vector} = Base.SubArray{eltype(T), 1, T, Tuple{UnitRange{Int}}, true}
```
-/
def sourceMethod1453 {T : Type} {Elem : Type 1} (eltype : T → Elem) (p : PartitionIterator T) :
    PartitionEltype T Elem :=
  .subArray (eltype p.c) 1 p.c .unitRangeInt true

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
def partitionLength {I L Q : Type}
    (length : I → Jl L)
    (cld : L → JInt64 → Jl Q)
    (itr : PartitionIterator I) : Jl Q := do
  let l ← length itr.c
  cld l itr.n

def partitionLengthInt {I : Type}
    (length : I → Jl JInt64) (itr : PartitionIterator I) : Jl JInt64 :=
  partitionLength length JInt.cld itr

def iteratePartitionVectorI64 {A SubRange View : Type}
    (firstindex lastindex : A → Jl JInt64)
    (colon : JInt64 → JInt64 → Jl SubRange)
    (viewInbounds : A → SubRange → Jl View)
    (itr : PartitionIterator A) (state : Option JInt64 := none) :
    Jl (Option (View × JInt64)) :=
  partitionIndexed firstindex lastindex
    (fun s last => pure (last.val < s.val))
    (fun s n => pure (s + n))
    (fun x one => pure (x - one))
    (fun a b => pure (if a.val ≤ b.val then a else b))
    colon viewInbounds
    (fun r one => pure (r + one))
    itr state

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

def allocPartitionList {α : Type} (_ : Type) (n : JInt64) : Jl (List α) :=
  if n.val < 0 ∨ n.val ≥ 2 ^ 63 - 2 ∨ n.val * 8 ≥ 2 ^ 63 - 2 then
    .error (.argumentError "invalid GenericMemory size")
  else pure []

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
def sourceMethod1605 {Handle : Type} (s : Handle) : Handle := s

/--
Julia source: base/iterators.jl:1606-1606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Stateful}, itr) = Stateful(itr)
```
-/
def sourceMethod1606 [Monad m] (construct : I → m Handle) (itr : I) : m Handle :=
  construct itr

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
def sourceMethod1626 {Handle : Type} {Ty : Type u} (eltype : Ty) (_ : Handle) : Ty := eltype

/--
Julia source: base/iterators.jl:1627-1627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorEltype(::Type{<:Stateful{T}}) where {T} = IteratorEltype(T)
```
-/
def sourceMethod1627 {Handle : Type} (iteratorEltype : IteratorEltypeTag)
    (_ : Handle) : IteratorEltypeTag := iteratorEltype

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
def sourceMethod1661
    (run : I → Option S → Exec E H (Option Y))
    (assertPair : Option Y → Exec E H (α × S))
    (argumentError : String → Exec E H α)
    (itr : I) (boundscheck : Bool := true) : Exec E H α := do
  let i ← run itr none
  if boundscheck && i.isNone then
    argumentError "Collection is empty, must contain exactly 1 element"
  else
    let (ret, state) ← assertPair i
    if boundscheck then
      if (← run itr (some state)).isSome then
        argumentError "Collection has multiple elements, must contain exactly 1 element"
      else pure ret
    else pure ret

/--
Julia source: base/iterators.jl:1659-1659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds only(x) = _only(x, iterate)
```
-/
def onlyModel (run : I → Option S → Exec E H (Option Y))
    (assertPair : Option Y → Exec E H (α × S))
    (argumentError : String → Exec E H α)
    (itr : I) (boundscheck : Bool := true) : Exec E H α :=
  sourceMethod1661 run assertPair argumentError itr boundscheck

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
def sourceMethod1673 {m : Type → Type} [Monad m] (length : I → m L) (notEqualOne : L → m P)
    (assertBool : P → m Bool)
    (firstInbounds : I → m α) (argumentError : String → m α)
    (itr : I) (boundscheck : Bool := true) : m α := do
  if boundscheck then
    if ← assertBool (← notEqualOne (← length itr)) then
      argumentError "Collection must contain exactly 1 element"
    else firstInbounds itr
  else firstInbounds itr

/--
Julia source: base/iterators.jl:1680-1680 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds only(x::IdDict) = _only(x, first)
```
-/
def sourceMethod1680 {m : Type → Type} [Monad m] {K V L P : Type}
    (length : IdDictModel K V → m L) (notEqualOne : L → m P)
    (assertBool : P → m Bool) (first : IdDictModel K V → m (K × V))
    (argumentError : String → m (K × V)) (x : IdDictModel K V)
    (boundscheck : Bool := true) : m (K × V) :=
  sourceMethod1673 length notEqualOne assertBool first argumentError x boundscheck

/--
Julia source: base/iterators.jl:1683-1683 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
only(x::Tuple{Any}) = x[1]
```
-/
def sourceMethod1683 {α : Type} (x : Tuple1 α) : α := x.first

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
def sourceMethod1687 {Name α β : Type} (first : NamedTuple1 Name α → β)
    (x : NamedTuple1 Name α) : β :=
  first x

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
structure PairAnyFirst (V : Type) where
  Key : Type
  first : Key
  second : V

def sourceMethod1706 {T : Type} (eltype : T → Type) (x : IterableStatePairs T) : Type 1 :=
  PairAnyFirst (eltype x.x)

/--
Julia source: base/iterators.jl:1714-1714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(x::IterableStatePairs) = IterableStatePairs(Iterators.reverse(x.x))
```
-/
def reverseIterableStatePairs {m : Type → Type} [Monad m] (reverse : I → m R) (x : IterableStatePairs I) :
    m (IterableStatePairs R) := do pure ⟨← reverse x.x⟩

/--
Julia source: base/iterators.jl:1715-1715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(x::IterableStatePairs{<:Iterators.Reverse}) = IterableStatePairs(x.x.itr)
```
-/
def reverseIterableStatePairsReverse {T : Type}
    (x : IterableStatePairs (Reverse T)) : IterableStatePairs T :=
  ⟨x.x.itr⟩

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
def iterateReverseIterableStatePairs {T Keys V S : Type}
    (keys : T → Jl Keys)
    (last : Keys → Jl S)
    (iterate : Reverse T → Option S → Jl (Option (V × S)))
    (x : IterableStatePairs (Reverse T)) (state : Option S := none) :
    Jl (Option ((S × V) × S)) := do
  let st ← match state with
    | none => do
        let ks ← keys x.x.itr
        last ks
    | some s => pure s
  match ← iterate x.x (some st) with
  | none => pure none
  | some (value, next) => pure (some ((st, value), next))

/--
Julia source: base/iterators.jl:1725-1725 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pairs(s::AbstractString) = IterableStatePairs(s)
```
-/
def pairsStringModel {S : Type} (s : S) : IterableStatePairs S := ⟨s⟩

def nthLoop (run : I → Option S → Exec E H (Option (V × S)))
    (rangeRun : Range → Option RS → Exec E H (Option (Index × RS)))
    (itr : I) (r : Range) (rangeState : Option RS) (y : Option (V × S)) :
    Exec E H (Option (V × S)) :=
  fun heap => match rangeRun r rangeState heap with
  | none => none
  | some (.error e, heap) => some (.error e, heap)
  | some (.ok none, heap) => some (.ok y, heap)
  | some (.ok (some (_, nextRange)), heap) =>
      match y with
      | none => some (.ok none, heap)
      | some (_, st) =>
          match run itr (some st) heap with
          | none => none
          | some (.error e, heap) => some (.error e, heap)
          | some (.ok y, heap) => nthLoop run rangeRun itr r (some nextRange) y heap
partial_fixpoint
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
def nthGeneric (positive : N → Exec E H Bool)
    (subtractOne : N → JInt64 → Exec E H End)
    (colon : JInt64 → End → Exec E H Range)
    (rangeRun : Range → Option RS → Exec E H (Option (Index × RS)))
    (run : I → Option S → Exec E H (Option (V × S)))
    (bounds : I → N → Exec E H V) (itr : I) (n : N) : Exec E H V := do
  if !(← positive n) then bounds itr n
  else do
    let y ← run itr none
    let r ← colon (JInt.lit .i64 1) (← subtractOne n (JInt.lit .i64 1))
    match ← nthLoop run rangeRun itr r none y with
    | none => bounds itr n
    | some (v, _) => pure v

/--
Julia source: base/iterators.jl:1753-1753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nth(itr, n::Integer) = _nth(IteratorSize(itr), itr, n)
```
-/
def nthModel {m : Type → Type} [Monad m] (trait : I → m IteratorSizeTag)
    (dispatch : IteratorSizeTag → I → N → m V) (itr : I) (n : N) : m V := do
  dispatch (← trait itr) itr n

/--
Julia source: base/iterators.jl:1754-1754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nth(itr::Cycle{I}, n::Integer) where I = _nth(IteratorSize(I), itr, n)
```
-/
def sourceMethod1754 {m : Type → Type} [Monad m] (trait : Ty → m IteratorSizeTag) (innerType : Ty)
    (dispatch : IteratorSizeTag → Cycle I → N → m V) (itr : Cycle I) (n : N) : m V := do
  dispatch (← trait innerType) itr n

/--
Julia source: base/iterators.jl:1755-1755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nth(itr::Flatten{Take{Repeated{O}}}, n::Integer) where O = _nth(IteratorSize(O), itr, n)
```
-/
def sourceMethod1755 {m : Type → Type} [Monad m] (trait : Ty → m IteratorSizeTag) (innerType : Ty)
    (dispatch : IteratorSizeTag → Flatten (Take (Repeated O)) → N → m V)
    (itr : Flatten (Take (Repeated O))) (n : N) : m V := do
  dispatch (← trait innerType) itr n

/--
Julia source: base/iterators.jl:1756-1756 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds nth(itr::AbstractArray, n::Integer) = itr[begin + n - 1]
```
-/
def nthArray {m : Type → Type} [Monad m] (firstindex : A → m B) (add : B → N → m Added)
    (sub : Added → JInt64 → m Idx) (getindex : A → Idx → m V)
    (a : A) (n : N) : m V := do
  let start ← firstindex a
  let added ← add start n
  getindex a (← sub added (JInt.lit .i64 1))

def nthArrayIntegerArg {A α : Type}
    (firstindex : A → Jl IntegerArg)
    (getindex : A → IntegerArg → Jl α)
    (itr : A) (n : IntegerArg) : Jl α :=
  nthArray firstindex
    (fun b k => pure (IntegerArg.add b k))
    (fun s _ => pure (IntegerArg.subOne s))
    getindex itr n

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
def sourceMethod1758 {m : Type → Type} [Monad m] (length : I → m L)
    (isZero : L → m Bool) (positive : N → m Bool) (mod1 : N → L → m Reduced)
    (nthReduced : I → Reduced → m ReducedValue) (nthOriginal : I → N → m OriginalValue)
    (bounds : Cycle I → N → m (ReducedValue ⊕ OriginalValue))
    (c : Cycle I) (n : N) : m (ReducedValue ⊕ OriginalValue) := do
  let k ← length c.xs
  if ← isZero k then bounds c n
  else if ← positive n then pure (.inl (← nthReduced c.xs (← mod1 n k)))
  else pure (.inr (← nthOriginal c.xs n))

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
def sourceMethod1767 {m : Type → Type} [Monad m] (length : O → m L)
    (mul : L → JInt64 → m Product) (gt : N → Product → m Bool)
    (isZero : L → m Bool) (positive : N → m Bool) (mod1 : N → L → m Reduced)
    (nthReduced : O → Reduced → m ReducedValue) (nthOriginal : O → N → m OriginalValue)
    (bounds : Flatten (Take (Repeated O)) → N → m (ReducedValue ⊕ OriginalValue))
    (c : Flatten (Take (Repeated O))) (n : N) : m (ReducedValue ⊕ OriginalValue) := do
  let cycles := c.it.n
  let torepeat := c.it.xs.x
  let k ← length torepeat
  let tooLarge ← gt n (← mul k cycles)
  if tooLarge then bounds c n
  else if ← isZero k then bounds c n
  else if ← positive n then pure (.inl (← nthReduced torepeat (← mod1 n k)))
  else pure (.inr (← nthOriginal torepeat n))

/--
Julia source: base/iterators.jl:1810-1810 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
nth(n::Integer) = Base.Fix2(nth, n)
```
-/
def nthCurry {m : Type → Type} [Monad m] (n : N) (nthModel : I → N → m V) : I → m V := fun itr => nthModel itr n

/--
Julia source: base/iterators.jl:1789-1789 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_nth(::IteratorSize, z::Zip, n::Integer) = Base.map(nth(n), z.is)
```
-/
def nthZip {m : Type → Type} [Monad m] (nthModel : I → N → m V)
    (map : (I → m V) → Is → m Values) (z : Zip Is) (n : N) : m Values :=
  map (nthCurry n nthModel) z.is

/--
Julia source: base/iterators.jl:1059-1059 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cycle(xs, n::Integer) = flatten(repeated(xs, n))
```
-/
def cycleNModel {m : Type → Type} [Monad m] (repeated : O → N → m R) (xs : O) (n : N) : m (Flatten R) := do
  pure (flattenModel (← repeated xs n))

def enumerateAsIterator {α S : Type} (xs : IteratorModel α S) : IteratorModel (JInt64 × α) (JInt64 × S) where
  run := fun state => iterateEnumerate (fun _ s => xs.run s) ⟨xs⟩ state
  isdone := fun state => xs.isdone (state.map Prod.snd)
  iteratorSize := xs.iteratorSize
  iteratorEltype := xs.iteratorEltype
  length := xs.length
  size := xs.size

def countAsIterator {T S : Type} (add : T → S → T) (it : Count T S) : IteratorModel T T where
  run := fun state => do
    let s := state.getD it.start
    let (v, next) ← iterateCountState (fun a b => pure (add a b)) it s
    pure (some (v, next))
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

def nthFiniteCycle {O α : Type} (length : O → Jl JInt64) (nth : O → JInt64 → Jl α)
    (itr : Flatten (Take (Repeated O))) (n : JInt64) : Jl α := do
  let cycles := JInt.lit .i64 itr.it.n.val
  let torepeat := itr.it.xs.x
  let k ← length torepeat
  if n.val > (k * cycles).val || k.val == 0 then .error .boundsError else
    let index := if n.val > 0 then JInt.wrap .i64 ((n.val - 1) % k.val + 1) else n
    nth torepeat index


def iterateReverseList {I α : Type} (length : I → Nat)
    (getindex : I → Nat → Jl α) (r : Reverse I) (state : Option Int) : Jl (Option (α × Int)) := do
  let i := state.getD (Int.ofNat (length r.itr))
  if i < 1 then pure none else
    pure (some (← getindex r.itr (i.toNat - 1), i - 1))

def reverseListAsIterator {α : Type} (xs : List α) : IteratorModel α Int where
  run := fun state =>
    (iterateReverseList (fun ys => ys.length) (fun ys n =>
      match listGet ys n with | none => .error .boundsError | some x => pure x)
      (reverseDefault xs) state).map (fun result => result.map fun (x, next) => (x, next))
  isdone := fun state => pure (some ((state.getD (Int.ofNat xs.length)) < 1))
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
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

def firstIterModel {α S : Type} (itr : IteratorModel α S) : Jl α := do
  match ← itr.run none with
  | none => .error .boundsError
  | some (x, _) => pure x

def generatorAsIterator {F α β S : Type} (apply : F → α → Jl β)
    (g : JuliaLean.base.generator.Generator (IteratorModel α S) F) : IteratorModel β S where
  run := fun state => JuliaLean.base.generator.iterateGenerator apply
    (fun itr st => itr.run st) Except.ok g state
  isdone := g.iter.isdone
  iteratorSize := g.iter.iteratorSize
  iteratorEltype := .eltypeUnknown
  length := g.iter.length
  size := g.iter.size


@[simp] def mapGeneratorAsIterator {α β S : Type} :
    JuliaLean.base.generator.Generator (IteratorModel α S) (α → β) ⊕
      JuliaLean.base.generator.Generator (Zip (List (IteratorModel α S))) (α → β) →
    IteratorModel β S
  | .inl g => generatorAsIterator (fun f x => pure (f x)) g
  | .inr _ =>
      { run := fun _ => pure none
        isdone := fun _ => pure (some true)
        iteratorSize := .sizeUnknown
        iteratorEltype := .eltypeUnknown
        length := .error (.argumentError "iterator is of undefined length")
        size := .error (.argumentError "iterator is of undefined size") }
def reverseArrayAsIterator {α : Type} (xs : List α) : IteratorModel α (List Nat × Nat) where
  run := fun state =>
    sourceMethod136 (fun ys => pure (List.range ys.length)) (fun indices => pure indices.reverse)
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
    sourceMethod145 (fun ys => pure (List.range ys.length)) (fun indices => pure indices.reverse)
      (fun r st => (listIterator r).run st)
      (fun ys idx => match listGet ys idx with | none => .error .boundsError | some v => pure v)
      (reverseDefault xs) state
  isdone := fun state => pure (some (xs.length ≤ (state.map Prod.snd).getD 0))
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]

def reverseEnumerateStep {I α S : Type} (i : Nat) (ri : I) (state : Option S)
    (iterate : I → Option S → Jl (Option (α × S))) :
    Jl (Option ((JInt64 × α) × (Nat × I × S))) := do
  match ← iterate ri state with
  | none => pure none
  | some (value, next) => pure (some ((JInt.lit .i64 (Int.ofNat i), value), (i - 1, ri, next)))

def reverseEnumerateAsIterator {α : Type} (xs : List α) :
    IteratorModel (JInt64 × α) (Nat × IteratorModel α Int × Int) where
  run := fun state =>
    match state with
    | none => do
      let ri := reverseListAsIterator xs
      reverseEnumerateStep (← ri.length) ri none (fun it s => it.run s)
    | some (i, ri, st) =>
      reverseEnumerateStep i ri (some st) (fun it s => it.run s)
  isdone := fun state => pure (some ((state.map Prod.fst).getD xs.length == 0))
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]

def reverseIterableStatePairsAsIterator {α : Type} (xs : List α) :
    IteratorModel (Int × α) Int where
  run := fun state =>
    iterateReverseIterableStatePairs
      (fun ys => pure ys)
      (fun ys => pure (Int.ofNat ys.length))
      (fun r st => (reverseListAsIterator r.itr).run st)
      (pairsStringModel (reverseDefault xs)) state
  isdone := fun state => (reverseListAsIterator xs).isdone state
  iteratorSize := .hasLength
  iteratorEltype := .hasEltype
  length := pure xs.length
  size := pure [xs.length]

def promoteSizeShape1D (a b : List Nat) : Jl (List Nat) :=
  match a, b with
  | [m], [n] => return (← sourceMethod415 (fun a b : Int => pure (min a b)) (Int.ofNat m) (Int.ofNat n)).map Int.toNat
  | _, _ => if a == b then pure a else .error (.argumentError "DimensionMismatch")

def promoteAxesShape1D (intersect : Nat → Nat → Nat := min) (a b : List Nat) : Jl (List Nat) :=
  match a, b with
  | [m], [n] => sourceMethod414 (fun a b => pure (intersect a b)) m n
  | _, _ => if a == b then pure a else .error (.argumentError "DimensionMismatch")

def checkedMulNatI64 (a b : Nat) : Jl Nat :=
  if a * b < 2 ^ 63 then .ok (a * b) else .error (.overflowError "checked_mul")

def vectorGetIndex {α : Type} {u : IntTy} (xs : List α) (idx : JInt u) : Jl α :=
  if 1 ≤ idx.val ∧ idx.val ≤ xs.length then
    match listGet xs (idx.val.toNat - 1) with
    | some x => .ok x
    | none => .error .boundsError
  else .error .boundsError

def vectorGetIndexInt {α : Type} (xs : List α) (idx : Int) : Jl α :=
  if 1 ≤ idx ∧ idx ≤ xs.length then
    match listGet xs (idx.toNat - 1) with
    | some x => .ok x
    | none => .error .boundsError
  else .error .boundsError

def vectorGetIndexArg {α : Type} (xs : List α) : (n : IntegerArg) → n.OffsetType → Jl α
  | .bool _, idx => vectorGetIndex xs idx
  | .bit _ _, idx => vectorGetIndex xs idx
  | .big _, idx => vectorGetIndexInt xs idx

def vectorGetIndexIntegerArg {α : Type} (xs : List α) : IntegerArg → Jl α
  | .bool b => vectorGetIndexInt xs (if b then 1 else 0)
  | .bit _ idx => vectorGetIndex xs idx
  | .big idx => vectorGetIndexInt xs idx

def unitRangeIndexInt (first last idx : Int) : Jl Int :=
  if first ≤ idx ∧ idx ≤ last then .ok idx else .error .boundsError

def unitRangeIndexArg (first last : Int) : (n : IntegerArg) → n.OffsetType → Jl Int
  | .bool _, idx => unitRangeIndex first last idx
  | .bit _ _, idx => unitRangeIndex first last idx
  | .big _, idx => unitRangeIndexInt first last idx

def unitRangeIndexIntegerArg (first last : Int) : IntegerArg → Jl Int
  | .bool b => unitRangeIndexInt first last (if b then 1 else 0)
  | .bit _ idx => unitRangeIndex first last idx
  | .big idx => unitRangeIndexInt first last idx
def onlyTupleDispatch {α : Type} : List α → Jl α
  | [x] => pure (sourceMethod1683 ⟨x⟩)
  | xs => sourceMethod1684 xs

def onlyNamedTupleDispatch {α : Type} : List α → Jl α
  | [x] => pure (sourceMethod1687 NamedTuple1.value (⟨(), x⟩ : NamedTuple1 Unit α))
  | xs => sourceMethod1688 xs

end JuliaLean.base.iterators

/-!
# Model of `base/iterators.jl` (master `bbfa0ce4150`)

Julia values and iterators are modelled by a deep embedding, so that Julia's
method dispatch on the type of an iterator (`drop(xs::Take, n)`,
`nth(itr::Cycle, n)`, ...) can be mirrored by pattern matching.

* `Ty` is the part of a Julia type the traits look at (`eltype`, `NTuple{N}`).
* `Val` is a Julia value: an `Int64`, a tuple, a `Vector`, a `UnitRange{Int64}`,
  a lazily reversed value, or an unassigned array slot (`undef`).
* `St` is an iteration state.
* `Itr` is an iterator object. Leaves are vectors, tuples, unit ranges
  (`UnitRange` or `Base.IdentityUnitRange`) and `Iterators.Stateful` wrappers of
  vectors; the other constructors are the wrappers of `base/iterators.jl`.

`iter fuel it st` is `iterate(it)` (`st = none`) or `iterate(it, s)`
(`st = some s`). `fuel` bounds the `while` loops of `dropwhile`, `flatten` and
`partition`; running out is the model-only error `Err.fuel`, never a Julia
result. `Err.oob` is an out-of-bounds store under `@inbounds` (memory
corruption in Julia).

Modelling notes:
* `Stateful` is mutable in Julia. Its model iterates over the position in the
  wrapped vector; `isdone(s)` uses the position at construction and
  `isdone(s, st)` the position in `st`, which is the object's position whenever
  every consumption goes through the iterator under study. Where Julia
  restarts or queries an iterator it is already iterating (`Cycle`,
  `ProductIterator`), a `Stateful` continues from its current position
  (`statefulCur`).
* Array iteration states are linear indices; Julia's `Vector` state is the same
  index (base/abstractarray.jl:1250).
* Elements of vectors are `Int64`s unless a property says otherwise; every
  element type has an 8-byte array slot (inline `Int64` or a boxed pointer).
-/

namespace JuliaLean.Iterators

open JuliaLean

/-- The part of a Julia type the iterator traits inspect. `tuple ts` is
`Tuple{ts...}` (an `NTuple{length ts}`), `vector t` is `Vector{t}`, `range` is
`UnitRange{Int64}`, `bottom` is `Union{}`. -/
inductive Ty where
  | int
  | tuple (ts : List Ty)
  | vector (t : Ty)
  | range
  | any
  | bottom
  deriving Repr, Inhabited

mutual
/-- Structural equality of types. -/
def Ty.beq : Ty → Ty → Bool
  | .int, .int => true
  | .tuple as, .tuple bs => Ty.beqList as bs
  | .vector a, .vector b => Ty.beq a b
  | .range, .range => true
  | .any, .any => true
  | .bottom, .bottom => true
  | _, _ => false
def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | _, _ => false
end

instance : BEq Ty := ⟨Ty.beq⟩

/-- Julia values. `rev v` is `Iterators.reverse(v)` of a value; `undef` is an
unassigned slot of a freshly allocated array (`#undef`, or garbage bits for
`Int64`). -/
inductive Val where
  | int (x : Int)
  | tup (vs : List Val)
  | vec (et : Ty) (vs : List Val)
  | rng (lo hi : Int)
  | rev (v : Val)
  | undef
  deriving Repr, Inhabited

/-- Errors: Julia exceptions, plus the model-only `fuel` (loop bound reached)
and `oob` (an `@inbounds` store past the end of an array). -/
inductive Err where
  | jl (e : JlError)
  | eof
  | dimMismatch
  | fuel
  | oob
  deriving Repr, DecidableEq, Inhabited

abbrev M (α : Type) := Except Err α

def jthrow {α : Type} (e : JlError) : M α := .error (.jl e)

def liftJ {α : Type} : Jl α → M α
  | .ok a => .ok a
  | .error e => .error (.jl e)

/-- Iteration states. `cut` is `IterationCutShort()` (base/iterators.jl:1482). -/
inductive St where
  | nothing
  | int (x : Int)
  | nat (n : Nat)
  | val (v : Val)
  | tup (ss : List St)
  | cut
  deriving Repr, Inhabited

/-- Is the state `IterationCutShort()`? -/
def isCutSt : Option St → Bool
  | some .cut => true
  | _ => false

/-- `UnitRange{Int64}` (`firstindex == 1`) or `Base.IdentityUnitRange`. -/
inductive URKind where
  | unit
  | identity
  deriving Repr, DecidableEq, Inhabited

/-- Iterator objects. `urange k fi li d` has indices `fi:li` and value `i + d`
at index `i` (`UnitRange a:b` is `urange .unit 1 (b-a+1) (a-1)`;
`IdentityUnitRange(a:b)` is `urange .identity a b 0`). `stateful et xs pos` is
an `Iterators.Stateful(::Vector{et})` that has already produced `pos` elements.
`revEnum ri` is `Iterators.Reverse{<:Enumerate}` with the reversed inner
iterator `ri = reverse(r.itr.itr)` (base/iterators.jl:225) computed once;
`revEach it` is the generator `(reverse(x) for x in it)` of
`reverse(::Flatten)` (base/iterators.jl:1379). -/
inductive Itr where
  | vec (et : Ty) (xs : List Val)
  | tuple (xs : List Val)
  | urange (k : URKind) (fi li : JInt64) (d : Int)
  | stateful (et : Ty) (xs : List Val) (pos : Nat)
  | take (it : Itr) (n : JInt64)
  | drop (it : Itr) (n : JInt64)
  | takeWhile (p : Val → Bool) (it : Itr)
  | dropWhile (p : Val → Bool) (it : Itr)
  | enumerate (it : Itr)
  | zip (its : List Itr)
  | repeated (x : Val)
  | cycle (it : Itr)
  | flatten (it : Itr)
  | product (its : List Itr)
  | partition (it : Itr) (n : JInt64)
  | rest (it : Itr) (st : St)
  | accumulate (f : Val → Val → Val) (it : Itr) (init : Option Val)
  | count (start step : JInt64)
  | reverse (it : Itr)
  | revEnum (ri : Itr)
  | revEach (it : Itr)

instance : Inhabited Itr := ⟨.tuple []⟩

/-- `Base.IteratorSize` values, base/generator.jl:84-88. -/
inductive Isz where
  | sizeUnknown
  | hasLength
  | hasShape (n : Nat)
  | isInfinite
  deriving Repr, DecidableEq, Inhabited

/-- `Int64` literal. -/
abbrev i64 (x : Int) : JInt64 := JInt.lit .i64 x

/-! ## Types -/

/-- `promote_typejoin` over the field types of a tuple type, as `eltype(Tuple{...})`
computes it; distinct field types join to `Any` (a supertype the traits treat
like any other non-tuple, non-number type). -/
def tyJoin : List Ty → Ty
  | [] => .bottom
  | t :: ts => if ts.all (· == t) then t else .any

/-- `eltype(T)` of a type. -/
def Ty.eltype : Ty → Ty
  | .int => .int
  | .tuple ts => tyJoin ts
  | .vector t => t
  | .range => .int
  | .any => .any
  | .bottom => .bottom

mutual
/-- `typeof(v)`. -/
def Val.ty : Val → Ty
  | .int _ => .int
  | .tup vs => .tuple (Val.tys vs)
  | .vec et _ => .vector et
  | .rng _ _ => .range
  | .rev v => Val.ty v
  | .undef => .any
def Val.tys : List Val → List Ty
  | [] => []
  | v :: vs => Val.ty v :: Val.tys vs
end

/-! ## Leaf iteration of values -/

/-- `iterate(t::Tuple, i=1)` (base/tuple.jl:69-73) and `iterate(A::Vector, i)`
(base/abstractarray.jl:1250): the state is the next index. -/
def idxIter (vs : List Val) : Option St → M (Option (Val × St))
  | none => if 1 ≤ vs.length then pure (some (vs.getD 0 .undef, .int 2)) else pure none
  | some (.int i) =>
    if 1 ≤ i ∧ i ≤ vs.length then pure (some (vs.getD (i - 1).toNat .undef, .int (i + 1)))
    else pure none
  | some _ => jthrow (.methodError "iterate")

/-- `iterate(r::OrdinalRange)` and `iterate(r, i)` for `UnitRange{Int64}`
`lo:hi`, base/range.jl:935-942: the state is the last value produced. -/
def rangeIter (lo hi : Int) : Option St → M (Option (Val × St))
  | none => if lo > hi then pure none else pure (some (.int lo, .int lo))
  | some (.int v) =>
    if v = hi then pure none
    else let nx := (i64 v + i64 1).val; pure (some (.int nx, .int nx))
  | some _ => jthrow (.methodError "iterate")

/-- Reverse iteration of a vector or tuple (base/iterators.jl:136-150,162):
indices from `length` down to 1. -/
def revIdxIter (vs : List Val) : Option St → M (Option (Val × St))
  | none =>
    if vs.length < 1 then pure none
    else pure (some (vs.getD (vs.length - 1) .undef, .int (vs.length - 1)))
  | some (.int i) =>
    if i < 1 then pure none else pure (some (vs.getD (i - 1).toNat .undef, .int (i - 1)))
  | some _ => jthrow (.methodError "iterate")

/-- `iterate` on a value used as an iterator (inner iterators of `flatten`):
numbers iterate once (base/number.jl:329-330), tuples and vectors by index,
ranges by value. `Iterators.reverse` of a range is the reversed range
`hi:-1:lo` (base/iterators.jl:156). -/
def valIter : Val → Option St → M (Option (Val × St))
  | .int x, none => pure (some (.int x, .nothing))
  | .int _, some _ => pure none
  | .tup vs, s => idxIter vs s
  | .vec _ vs, s => idxIter vs s
  | .rng lo hi, s => rangeIter lo hi s
  | .rev (.tup vs), s => revIdxIter vs s
  | .rev (.vec _ vs), s => revIdxIter vs s
  | .rev (.rng lo hi), none => if lo > hi then pure none else pure (some (.int hi, .int hi))
  | .rev (.rng lo _), some (.int v) =>
    if v = lo then pure none
    else let nx := (i64 v - i64 1).val; pure (some (.int nx, .int nx))
  | .rev (.int x), s => valIter (.int x) s
  | _, _ => jthrow (.methodError "iterate")

/-- `Iterators.reverse(x)` of a value: numbers are their own reverse and
`reverse(r::Reverse) = r.itr` (base/iterators.jl:158-159). -/
def Val.reverse : Val → Val
  | .int x => .int x
  | .rev v => v
  | v => .rev v

/-- `length(x)` of a value used as an iterator. -/
def Val.length : Val → M JInt64
  | .int _ => pure (i64 1)
  | .tup vs => pure (i64 vs.length)
  | .vec _ vs => pure (i64 vs.length)
  | .rng lo hi => pure (i64 (hi - lo + 1))
  | .rev v => match v with
    | .tup vs => pure (i64 vs.length)
    | .vec _ vs => pure (i64 vs.length)
    | .rng lo hi => pure (i64 (hi - lo + 1))
    | _ => jthrow (.methodError "length")
  | .undef => jthrow (.methodError "length")

/-- `IteratorSize(typeof(x))` of a value. Numbers are `HasShape{0}`
(base/number.jl). -/
def Val.isz : Val → Isz
  | .int _ => .hasShape 0
  | .tup _ => .hasLength
  | .vec _ _ => .hasShape 1
  | .rng _ _ => .hasShape 1
  | .rev v => match v with
    | .tup _ => .hasLength
    | .vec _ _ => .hasShape 1
    | .rng _ _ => .hasShape 1
    | _ => .hasLength
  | .undef => .hasLength

/-! ## Traits -/

/-- `and_iteratorsize`, base/iterators.jl:71-76. -/
def andIsz : Isz → Isz → Isz
  | a, b => if a = b then a else
    match a, b with
    | .hasLength, .hasShape _ => .hasLength
    | .hasShape _, .hasLength => .hasLength
    | .hasShape _, .hasShape _ => .hasLength
    | _, _ => .sizeUnknown

/-- `zip_iteratorsize(a, b)`, base/iterators.jl:508-512. -/
def zipIsz2 : Isz → Isz → Isz
  | .isInfinite, .isInfinite => .isInfinite
  | .hasLength, .isInfinite => .hasLength
  | .hasShape _, .isInfinite => .hasLength
  | .isInfinite, .hasLength => .hasLength
  | .isInfinite, .hasShape _ => .hasLength
  | .isInfinite, b => andIsz b .isInfinite
  | a, b => andIsz a b

/-- `zip_iteratorsize(...)`, base/iterators.jl:506-513. -/
def zipIsz : List Isz → Isz
  | [] => .isInfinite
  | [a] => a
  | a :: b :: rest => zipIsz2 a (zipIsz (b :: rest))

/-- `prod_iteratorsize(a, b)`, base/iterators.jl:1157-1166. -/
def prodIsz2 : Isz → Isz → Isz
  | .hasLength, .hasLength => .hasShape 2
  | .hasLength, .hasShape n => .hasShape (n + 1)
  | .hasShape n, .hasLength => .hasShape (n + 1)
  | .hasShape m, .hasShape n => .hasShape (m + n)
  | .isInfinite, _ => .isInfinite
  | _, .isInfinite => .isInfinite
  | _, _ => .sizeUnknown

/-- `prod_iteratorsize(...)`, base/iterators.jl:1154-1167. -/
def prodIszList : List Isz → Isz
  | [] => .hasShape 0
  | [a] => a
  | a :: b :: rest => prodIsz2 a (prodIszList (b :: rest))

/-- `flatten_iteratorsize(sz, T)`, base/iterators.jl:1310-1316. -/
def flattenIsz (sz : Isz) (t : Ty) : Isz :=
  match sz with
  | .hasLength | .hasShape _ =>
    match t with
    | .bottom | .tuple _ | .int => .hasLength
    | _ => .sizeUnknown
  | _ => .sizeUnknown

/-- Is `it` the empty tuple (`Flatten{Tuple{}}`, base/iterators.jl:1306,1320,1333)? -/
def isEmptyTuple : Itr → Bool
  | .tuple [] => true
  | _ => false

mutual
/-- `Base.IteratorSize(typeof(it))`. -/
def isz : Itr → Isz
  | .vec _ _ => .hasShape 1
  | .tuple _ => .hasLength
  | .urange _ _ _ _ => .hasShape 1
  -- base/iterators.jl:1625
  | .stateful _ _ _ => .sizeUnknown
  -- base/iterators.jl:820-822
  | .take it _ => if isz it = .sizeUnknown then .sizeUnknown else .hasLength
  -- base/iterators.jl:877-880
  | .drop it _ => match isz it with
    | .sizeUnknown => .sizeUnknown
    | .isInfinite => .isInfinite
    | _ => .hasLength
  -- base/iterators.jl:937,988
  | .takeWhile _ _ => .sizeUnknown
  | .dropWhile _ _ => .sizeUnknown
  -- base/iterators.jl:221
  | .enumerate it => isz it
  -- base/iterators.jl:503
  | .zip its => zipIsz (iszList its)
  -- base/iterators.jl:1117,1063
  | .repeated _ => .isInfinite
  | .cycle _ => .isInfinite
  -- base/iterators.jl:1318-1322
  | .flatten it =>
    if !(ieltype it) then .sizeUnknown
    else if isEmptyTuple it then .hasLength
    else flattenIsz (isz it) (eltype it)
  -- base/iterators.jl:1150-1152
  | .product its => prodIszList (iszList its ++ [.hasShape 0])
  -- base/iterators.jl:1459-1463
  | .partition c _ => match isz c with
    | .hasShape _ => .hasLength
    | s => s
  -- base/iterators.jl:737-739
  | .rest it _ => if isz it = .isInfinite then .isInfinite else .sizeUnknown
  -- base/iterators.jl:664
  | .accumulate _ it _ => isz it
  -- base/iterators.jl:774
  | .count _ _ => .isInfinite
  -- base/iterators.jl:131
  | .reverse it => isz it
  | .revEnum ri => isz ri
  -- base/generator.jl:139 (Generator{I}: IteratorSize(I))
  | .revEach it => isz it
def iszList : List Itr → List Isz
  | [] => []
  | it :: its => isz it :: iszList its

/-- `Base.IteratorEltype(typeof(it)) isa HasEltype`. -/
def ieltype : Itr → Bool
  | .vec _ _ | .tuple _ | .urange _ _ _ _ | .stateful _ _ _ => true
  | .take it _ | .drop it _ | .takeWhile _ it | .dropWhile _ it => ieltype it
  | .enumerate it => ieltype it
  -- base/iterators.jl:504,515-517
  | .zip its => ieltypeAll its
  | .repeated _ => true
  | .cycle it => ieltype it
  -- base/iterators.jl:1305-1308: IteratorEltype(eltype(I)); IteratorEltype(Any) is unknown
  | .flatten it => isEmptyTuple it || (ieltype it && eltype it != .any)
  -- base/iterators.jl:1188-1195
  | .product [] => true
  | .product [i] => ieltype i
  | .product its => ieltypeAll its
  -- base/iterators.jl:1455-1457, base/multidimensional.jl:657
  | .partition (.vec _ _) _ => true
  | .partition (.urange .unit _ _ _) _ => true
  | .partition (.urange .identity _ _ _) _ => false
  | .partition c _ => ieltype c
  | .rest it _ => ieltype it
  -- base/iterators.jl:665
  | .accumulate _ _ _ => false
  | .count _ _ => true
  | .reverse it => ieltype it
  | .revEnum ri => ieltype ri
  -- base/generator.jl:173
  | .revEach _ => false
def ieltypeAll : List Itr → Bool
  | [] => true
  | it :: its => ieltype it && ieltypeAll its

/-- `eltype(typeof(it))`. -/
def eltype : Itr → Ty
  | .vec et _ => et
  | .tuple xs => tyJoin (Val.tys xs)
  | .urange _ _ _ _ => .int
  | .stateful et _ _ => et
  | .take it _ | .drop it _ | .takeWhile _ it | .dropWhile _ it => eltype it
  | .enumerate it => .tuple [.int, eltype it]
  | .zip its => .tuple (eltypeList its)
  | .repeated x => x.ty
  | .cycle it => eltype it
  | .flatten it => (eltype it).eltype
  | .product its => .tuple (eltypeList its)
  | .partition c _ => .vector (eltype c)
  | .rest it _ => eltype it
  | .accumulate _ _ _ => .any
  | .count _ _ => .int
  | .reverse it => eltype it
  | .revEnum ri => .tuple [.int, eltype ri]
  | .revEach _ => .any
def eltypeList : List Itr → List Ty
  | [] => []
  | it :: its => eltype it :: eltypeList its
end

/-! ## `isdone` -/

/-- Julia's three-valued `|` on `Union{Bool, Missing}`. -/
def or3 : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-- `isdone(x)` on an object whose last state is `s`: a `Stateful` answers from
its current (mutated) position, which is the position in `s`; any other
iterator answers from its start. Used where Julia calls `isdone(x)` on an
iterator it is already iterating (base/iterators.jl:1209,1239). -/
def statefulCur : Itr → St → Option St
  | .stateful _ _ _, s => some s
  | _, _ => none

/-- The state component of a `ProductIterator` state entry `Pair(value, state)`. -/
def pairState : St → St
  | .tup [_, s] => s
  | s => s

mutual
/-- `isdone(it)` (no state). The default `isdone(_, _...) = missing` is `none`
(base/essentials.jl:1591). -/
def isdone0 : Itr → M (Option Bool)
  -- base/iterators.jl:1607
  | .stateful _ xs pos => pure (some (decide (xs.length ≤ pos)))
  -- base/iterators.jl:824
  | .take xs _ => isdone0 xs
  -- base/iterators.jl:430
  | .zip its => zipAnyIsdone0 its
  -- base/iterators.jl:1066
  | .cycle xs => isdone0 xs
  -- base/iterators.jl:1204
  | .product its => anyIsdone0 its
  -- base/iterators.jl:733: isdone(i::Rest) = isdone(i.itr)
  | .rest it _ => isdone0 it
  -- base/generator.jl:59
  | .revEach it => isdone0 it
  | _ => pure none
/-- `_zip_any_isdone(is, ())`, base/iterators.jl:433-438. -/
def zipAnyIsdone0 : List Itr → M (Option Bool)
  | [] => pure (some false)
  | it :: its => do
    let d1 ← isdone0 it
    if d1 = some true then pure (some true) else pure (or3 d1 (← zipAnyIsdone0 its))
/-- `any(isdone, P.iterators)`, base/anyall.jl:115-133. -/
def anyIsdone0 : List Itr → M (Option Bool)
  | [] => pure (some false)
  | it :: its => do
    match ← isdone0 it with
    | some true => pure (some true)
    | none => do
      let r ← anyIsdone0 its
      pure (if r = some true then some true else none)
    | some false => anyIsdone0 its
end

mutual
/-- `isdone(it, s)`. -/
def isdoneS : Itr → St → M (Option Bool)
  | .stateful _ xs _, .nat p => pure (some (decide (xs.length ≤ p)))
  | .stateful _ xs pos, _ => pure (some (decide (xs.length ≤ pos)))
  -- base/iterators.jl:825
  | .take xs _, .tup (.int n :: rest) => do
    let inner ← match rest with
      | [] => isdone0 xs
      | s :: _ => isdoneS xs s
    pure (or3 (some (decide (n ≤ 0))) inner)
  -- base/iterators.jl:892
  | .drop xs _, s => isdoneS xs s
  -- base/iterators.jl:431
  | .zip its, .tup ss => zipAnyIsdoneS its ss
  -- base/iterators.jl:1067
  | .cycle _, _ => pure (some false)
  -- base/iterators.jl:1213
  | .product [], _ => pure (some true)
  -- base/iterators.jl:1214
  | .product its, .tup sts => pisdone its sts
  -- base/iterators.jl:733
  | .rest it _, s => isdoneS it s
  | .revEach it, s => isdoneS it s
  | _, _ => pure none
/-- `_zip_any_isdone(is, map(tuple, ss))`, base/iterators.jl:433-438. -/
def zipAnyIsdoneS : List Itr → List St → M (Option Bool)
  | it :: its, s :: ss => do
    let d1 ← isdoneS it s
    if d1 = some true then pure (some true) else pure (or3 d1 (← zipAnyIsdoneS its ss))
  | _, _ => pure (some false)
/-- `_pisdone(iters, states)`, base/iterators.jl:1205-1212. There is no method
for empty tuples: when every factor is done, `first(())` throws
`ArgumentError("tuple must be non-empty")`. -/
def pisdone : List Itr → List St → M (Option Bool)
  | it :: its, s :: ss => do
    let d1 ← isdoneS it (pairState s)
    if d1 ≠ some true then pure d1 else
    let d2 ← match statefulCur it (pairState s) with
      | some c => isdoneS it c
      | none => isdone0 it
    if d2 ≠ some true then pure d2 else pisdone its ss
  | _, _ => jthrow (.argumentError "tuple must be non-empty")
end

/-! ## `length` and `size` -/

/-- `min(x, y)` (base/promotion.jl: `ifelse(y < x, y, x)`). -/
def jmin (x y : JInt64) : JInt64 := if y < x then y else x

/-- `checked_mul` on `Int64`, base/checked.jl:290-295. -/
def checkedMul64 (x y : JInt64) : M JInt64 := liftJ (JuliaLean.IntArith.Checked.checkedMul x y)

/-- `reduce(checked_mul, dims; init=1)`: a left fold. -/
def foldCheckedMul : JInt64 → List JInt64 → M JInt64
  | acc, [] => pure acc
  | acc, d :: ds => do foldCheckedMul (← checkedMul64 acc d) ds

/-- `_promote_tuple_shape(a, b)` for sizes, base/iterators.jl:415-416: two
one-dimensional sizes give the minimum; other sizes must agree
(`promote_shape`, base/indices.jl). -/
def promoteShape (a b : List JInt64) : M (List JInt64) :=
  match a, b with
  | [m], [n] => pure [jmin m n]
  | _, _ => if a = b then pure a else .error .dimMismatch

/-- `_promote_tuple_shape(a, b...) = _promote_tuple_shape(a, _promote_tuple_shape(b...))`,
base/iterators.jl:417-418. -/
def promoteAll : List (List JInt64) → M (List JInt64)
  | [] => pure []
  | [a] => pure a
  | a :: b :: rest => do promoteShape a (← promoteAll (b :: rest))

mutual
/-- `length(it)`. Iterators without a `length` method throw `MethodError`. -/
def len : Itr → M JInt64
  | .vec _ xs => pure (i64 xs.length)
  | .tuple xs => pure (i64 xs.length)
  -- base/range.jl:794-804
  | .urange _ fi li _ => pure (li - fi + i64 1)
  -- base/iterators.jl:823 and 58-61; length(1:n) == n for n >= 0
  | .take xs n => if isz xs = .isInfinite then pure n else do pure (jmin (← len xs) n)
  -- base/iterators.jl:881 and 63-69
  | .drop xs n => do
    if isz xs = .isInfinite then len xs else
    let m ← len xs
    pure (if n < m then m - n else i64 0)
  -- base/iterators.jl:209
  | .enumerate it => len it
  -- base/iterators.jl:380-394
  | .zip its => do
    match ← zipMinLength its with
    | none => jthrow (.argumentError "iterator is of undefined length")
    | some n => pure n
  -- base/iterators.jl:1324-1333
  | .flatten (.tuple []) => pure (i64 0)
  | .flatten it => match eltype it with
    | .bottom => pure (i64 0)
    | .tuple ts => do checkedMul64 (i64 ts.length) (← len it)
    | .int => len it
    | _ => jthrow (.argumentError "Iterates of the argument to Flatten are not known to have constant length")
  -- base/iterators.jl:1186
  | .product its => do foldCheckedMul (i64 1) (← prodSize its)
  -- base/iterators.jl:1465-1468
  | .partition c n => do liftJ (JInt.cld (← len c) n)
  -- base/iterators.jl:661
  | .accumulate _ it _ => len it
  -- base/iterators.jl:129
  | .reverse it => len it
  | .revEnum ri => len ri
  | .revEach it => len it
  | _ => jthrow (.methodError "length")
/-- `_zip_min_length(is)`, base/iterators.jl:385-394. -/
def zipMinLength : List Itr → M (Option JInt64)
  | [] => pure none
  | it :: its => do
    let n ← zipMinLength its
    if isz it = .isInfinite then pure n else
    let l ← len it
    match n with
    | none => pure (some l)
    | some m => pure (some (jmin m l))
/-- `size(it)`. -/
def size : Itr → M (List JInt64)
  | .vec _ xs => pure [i64 xs.length]
  | .urange _ fi li _ => pure [li - fi + i64 1]
  | .enumerate it => size it
  -- base/iterators.jl:412
  | .zip its => do promoteAll (← sizeList its)
  -- base/iterators.jl:1169-1175
  | .product its => prodSize its
  | .accumulate _ it _ => size it
  | .reverse it => size it
  | .revEnum ri => size ri
  | .revEach it => size it
  | _ => jthrow (.methodError "size")
def sizeList : List Itr → M (List (List JInt64))
  | [] => pure []
  | it :: its => do pure ((← size it) :: (← sizeList its))
/-- `_prod_size(t)`, base/iterators.jl:1170-1175. -/
def prodSize : List Itr → M (List JInt64)
  | [] => pure []
  | it :: its => do
    let here ← match isz it with
      | .hasShape _ => size it
      | .hasLength => do pure [← len it]
      | _ => jthrow (.argumentError "Cannot compute size for object of type")
    pure (here ++ (← prodSize its))
end

/-! ## Allocation -/

/-- `MAXINTVAL` of src/julia_internal.h (`typemax(Int)`). -/
def maxIntVal : Int := 2 ^ 63 - 1

/-- `Vector{T}(undef, n)` with 8-byte slots: src/genericmemory.c:55-66 throws
`ArgumentError("invalid GenericMemory size ...")` when `n` (as `size_t`) or the
byte count `8n` reaches `MAXINTVAL - 1`, or the multiplication overflows. -/
def allocCheck (n : Int) : M Unit :=
  if n = 0 then pure ()
  else
    let nel : Int := n % 2 ^ 64
    if nel ≥ maxIntVal - 1 ∨ nel * 8 ≥ maxIntVal - 1 then
      jthrow (.argumentError "invalid GenericMemory size")
    else pure ()

/-! ## Iteration -/

/-- The `for _ in 1:n` loop of `iterate(::Drop)`, base/iterators.jl:883-890. -/
def dropLoop (step : St → M (Option (Val × St))) : Nat → Option (Val × St) → M (Option (Val × St))
  | 0, y => pure y
  | _ + 1, none => pure none
  | k + 1, some (_, s) => do dropLoop step k (← step s)

/-- The `while` loop of `iterate(::DropWhile)`, base/iterators.jl:979-986. -/
def whileLoop (step : St → M (Option (Val × St))) (p : Val → Bool) :
    Nat → Option (Val × St) → M (Option (Val × St))
  | _, none => pure none
  | 0, some _ => .error .fuel
  | k + 1, some (x, s) => if p x then do whileLoop step p k (← step s) else pure (some (x, s))

/-- The outer-advancing `while` loops of `iterate(::Flatten)`,
base/iterators.jl:1342-1351 and 1365-1376: `r` is the result of iterating the
current inner value `inner`; `so` is the next outer state. -/
def flatLoop (step : St → M (Option (Val × St))) :
    Nat → Val → St → Option (Val × St) → M (Option (Val × St))
  | _, inner, so, some (item, si) => pure (some (item, .tup [so, .val inner, si]))
  | 0, _, _, none => .error .fuel
  | k + 1, _, so, none => do
    match ← step so with
    | none => pure none
    | some (inner', so') => flatLoop step k inner' so' (← valIter inner' none)

/-- The fill loop of the generic `iterate(::PartitionIterator)`,
base/iterators.jl:1490-1499: `acc` holds the `i` elements stored so far. -/
def partLoop (step : St → M (Option (Val × St))) (n : Int) :
    Nat → List Val → Option (Val × St) → M (List Val × Option (Val × St))
  | _, acc, none => pure (acc, none)
  | 0, _, some _ => .error .fuel
  | k + 1, acc, some (x, s) =>
    let acc' := acc ++ [x]
    if n ≤ acc'.length then pure (acc', some (x, s))
    else do partLoop step n k acc' (← step s)

/-- `UnitRange(start, stop)` normalisation, base/range.jl:428,439-441. -/
def unitRangeLast (start stop : JInt64) : JInt64 :=
  if start ≤ stop then stop else start - i64 1

/-- `c[s:r]` for `c = urange k fi li d` without bounds checks: an
`IdentityUnitRange` returns the index range itself (base/indices.jl:380-384);
a `UnitRange` shifts it, base/range.jl:1002-1015. -/
def urangeSlice (k : URKind) (fi : JInt64) (d : Int) (s r : JInt64) : Val :=
  let stop := unitRangeLast s r
  match k with
  | .identity => .rng s.val stop.val
  | .unit =>
    let f := fi + i64 d
    let start := f + s - fi
    let len := stop - s + i64 1
    let stop' := start + (len - i64 1)
    .rng start.val (unitRangeLast start stop').val

/-- Decode a `Take`/`Enumerate` state `(n, rest...)`. -/
def splitCountState : Option St → JInt64 → M (JInt64 × Option St)
  | none, n => pure (n, none)
  | some (.tup [.int m]), _ => pure (i64 m, none)
  | some (.tup [.int m, s]), _ => pure (i64 m, some s)
  | some _, _ => jthrow (.methodError "iterate")

mutual
/-- `iterate(it)` (`st = none`) and `iterate(it, s)` (`st = some s`). -/
def iter (fuel : Nat) : Itr → Option St → M (Option (Val × St))
  | .vec _ xs, st => idxIter xs st
  | .tuple xs, st => idxIter xs st
  -- base/range.jl:935-942 on the values i + d
  | .urange _ fi li d, st => rangeIter (fi.val + d) (li.val + d) st
  -- base/iterators.jl:1624, 1609-1618
  | .stateful _ xs pos, st =>
    let p := match st with
      | some (.nat q) => q
      | _ => pos
    if xs.length ≤ p then pure none else pure (some (xs.getD p .undef, .nat (p + 1)))
  -- base/iterators.jl:827-833
  | .take xs n, st => do
    let (m, rest) ← splitCountState st n
    if m ≤ i64 0 then pure none else
    match ← iter fuel xs rest with
    | none => pure none
    | some (y, s) => pure (some (y, .tup [.int (m - i64 1).val, s]))
  -- base/iterators.jl:883-891
  | .drop xs n, none => do
    let y ← iter fuel xs none
    dropLoop (fun s => iter fuel xs (some s)) n.val.toNat y
  | .drop xs _, some s => iter fuel xs (some s)
  -- base/iterators.jl:930-935
  | .takeWhile p xs, st => do
    match ← iter fuel xs st with
    | none => pure none
    | some (y, s) => if p y then pure (some (y, s)) else pure none
  -- base/iterators.jl:978-986
  | .dropWhile p xs, none => do
    whileLoop (fun s => iter fuel xs (some s)) p fuel (← iter fuel xs none)
  | .dropWhile _ xs, some s => iter fuel xs (some s)
  -- base/iterators.jl:211-216
  | .enumerate it, st => do
    let (i, rest) ← splitCountState st (i64 1)
    match ← iter fuel it rest with
    | none => pure none
    | some (x, s) => pure (some (.tup [.int i.val, x], .tup [.int (i + i64 1).val, s]))
  -- base/iterators.jl:440-460
  | .zip its, st => do
    let ss : List (Option St) := match st with
      | some (.tup ss) => ss.map some
      | _ => its.map (fun _ => none)
    let ds ← zipIsdones its ss
    if ds.any (· = some true) then pure none else
    let xs ← if ds.all (· = none) then zipInOrder fuel its ss
      else do
        match ← zipUnknown fuel its ss ds with
        | none => pure none
        | some xs1 => zipRest fuel its ss xs1
    match xs with
    | none => pure none
    | some xs => pure (some (.tup (xs.map (·.1)), .tup (xs.map (·.2))))
  -- base/iterators.jl:1115
  | .repeated x, _ => pure (some (x, .nothing))
  -- base/iterators.jl:1065-1072
  | .cycle xs, none => iter fuel xs none
  | .cycle xs, some s => do
    match ← iter fuel xs (some s) with
    | none => iter fuel xs (statefulCur xs s)
    | some y => pure (some y)
  -- base/iterators.jl:1335-1352
  | .flatten it, none => do
    match ← iter fuel it none with
    | none => pure none
    | some (inner, so) => flatLoop (fun s => iter fuel it (some s)) fuel inner so (← valIter inner none)
  -- base/iterators.jl:1354-1377
  | .flatten it, some (.tup [so, .val inner, si]) => do
    match ← valIter inner (some si) with
    | some (item, si') => pure (some (item, .tup [so, .val inner, si']))
    | none => flatLoop (fun s => iter fuel it (some s)) fuel inner so none
  | .flatten _, some _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:1201-1202
  | .product [], none => pure (some (.tup [], .nat 1))
  | .product [], some _ => pure none
  -- base/iterators.jl:1226-1231
  | .product its, none => do
    if (← anyIsdone0 its) = some true then pure none else
    match ← pIterate fuel its with
    | none => pure none
    | some nx => pure (some (.tup (nx.map (·.1)), .tup (nx.map (fun p => .tup [.val p.1, p.2]))))
  -- base/iterators.jl:1248-1253
  | .product its, some (.tup sts) => do
    if (← pisdone its sts) = some true then pure none else
    match ← pIterate1 fuel its sts with
    | none => pure none
    | some nx => pure (some (.tup (nx.map (·.1)), .tup (nx.map (fun p => .tup [.val p.1, p.2]))))
  | .product _, some _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:1470-1474
  | .partition (.urange k fi li d) n, st => do
    let s : JInt64 := match st with
      | some (.int x) => i64 x
      | _ => fi
    if li < s then pure none else
    let r := jmin (s + n - i64 1) li
    pure (some (urangeSlice k fi d s r, .int (r + i64 1).val))
  -- base/iterators.jl:1476-1480
  | .partition (.vec et xs) n, st => do
    let s : JInt64 := match st with
      | some (.int x) => i64 x
      | _ => i64 1
    if i64 xs.length < s then pure none else
    let r := jmin (s + n - i64 1) (i64 xs.length)
    if s.val < 1 then .error .oob else
    pure (some (.vec et ((xs.drop (s.val - 1).toNat).take (r.val - s.val + 1).toNat), .int (r + i64 1).val))
  -- base/iterators.jl:1484-1502
  | .partition c n, st => do
    if isCutSt st then pure none else
    allocCheck n.val
    let (acc, y) ← partLoop (fun s => iter fuel c (some s)) n.val fuel [] (← iter fuel c st)
    if acc.isEmpty then pure none else
    pure (some (.vec (eltype c) acc, match y with
      | none => .cut
      | some (_, s) => s))
  -- base/iterators.jl:732
  | .rest it s0, none => iter fuel it (some s0)
  | .rest it _, some s => iter fuel it (some s)
  -- base/iterators.jl:643-659
  | .accumulate f it init, none => do
    match ← iter fuel it none with
    | none => pure none
    | some (x, s) =>
      let v := match init with
        | none => x
        | some i => f i x
      pure (some (v, .tup [.val v, s]))
  | .accumulate f it _, some (.tup [.val v, s]) => do
    match ← iter fuel it (some s) with
    | none => pure none
    | some (x, s') => let v' := f v x; pure (some (v', .tup [.val v', s']))
  | .accumulate _ _ _, some _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:772
  | .count start _, none => pure (some (.int start.val, .int start.val))
  | .count _ step, some (.int v) =>
    pure (some (.int (i64 v + step).val, .int (i64 v + step).val))
  | .count _ _, some _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:136-150 (vectors), 162 (tuples), 156 (ranges, reversed by Base.reverse)
  | .reverse (.vec _ xs), st => revIdxIter xs st
  | .reverse (.tuple xs), st => revIdxIter xs st
  | .reverse (.urange _ fi li d), st => valIter (.rev (.rng (fi.val + d) (li.val + d))) st
  | .reverse _, _ => jthrow (.methodError "iterate")
  -- base/iterators.jl:224-232
  | .revEnum ri, st => do
    let (i, rest) ← match st with
      | none => do pure (← len ri, none)
      | some s => splitCountState (some s) (i64 0)
    match ← iter fuel ri rest with
    | none => pure none
    | some (x, s) => pure (some (.tup [.int i.val, x], .tup [.int (i - i64 1).val, s]))
  -- base/generator.jl:52-58
  | .revEach it, st => do
    match ← iter fuel it st with
    | none => pure none
    | some (x, s) => pure (some (x.reverse, s))
/-- `_zip_isdone(is, ss)`, base/iterators.jl:496-501 (only the `ds` list). -/
def zipIsdones : List Itr → List (Option St) → M (List (Option Bool))
  | it :: its, s :: ss => do
    let d ← match s with
      | none => isdone0 it
      | some s => isdoneS it s
    pure (d :: (← zipIsdones its ss))
  | _, _ => pure []
/-- `_zip_iterate_in_order`, base/iterators.jl:465-472. -/
def zipInOrder (fuel : Nat) : List Itr → List (Option St) → M (Option (List (Val × St)))
  | it :: its, s :: ss => do
    match ← iter fuel it s with
    | none => pure none
    | some x => do
      match ← zipInOrder fuel its ss with
      | none => pure none
      | some y => pure (some (x :: y))
  | _, _ => pure (some [])
/-- `_zip_iterate_unknown`, base/iterators.jl:478-485: `none` entries are `_ZipSkip()`. -/
def zipUnknown (fuel : Nat) : List Itr → List (Option St) → List (Option Bool) →
    M (Option (List (Option (Val × St))))
  | it :: its, s :: ss, d :: ds => do
    let x ← if d = none then do
        match ← iter fuel it s with
        | none => pure none
        | some x => pure (some (some x))
      else pure (some none)
    match x with
    | none => pure none
    | some x => do
      match ← zipUnknown fuel its ss ds with
      | none => pure none
      | some y => pure (some (x :: y))
  | _, _, _ => pure (some [])
/-- `_zip_iterate_rest`, base/iterators.jl:487-494. -/
def zipRest (fuel : Nat) : List Itr → List (Option St) → List (Option (Val × St)) →
    M (Option (List (Val × St)))
  | it :: its, s :: ss, x :: xs => do
    let x ← match x with
      | some x => pure (some x)
      | none => iter fuel it s
    match x with
    | none => pure none
    | some x => do
      match ← zipRest fuel its ss xs with
      | none => pure none
      | some y => pure (some (x :: y))
  | _, _, _ => pure (some [])
/-- `_piterate(iters...)`, base/iterators.jl:1216-1225. -/
def pIterate (fuel : Nat) : List Itr → M (Option (List (Val × St)))
  | [] => pure (some [])
  | it :: its => do
    match ← iter fuel it none with
    | none => pure none
    | some nx => do
      match ← pIterate fuel its with
      | none => pure none
      | some rest => pure (some (nx :: rest))
/-- `_piterate1(iters, states)`, base/iterators.jl:1233-1247. States are
`Pair(value, state)` entries. -/
def pIterate1 (fuel : Nat) : List Itr → List St → M (Option (List (Val × St)))
  | it :: its, st1 :: sts => do
    let old : List (Val × St) := sts.map fun
      | .tup [.val v, s] => (v, s)
      | s => (.undef, s)
    match ← iter fuel it (some (pairState st1)) with
    | some nx => pure (some (nx :: old))
    | none => do
      let d ← match statefulCur it (pairState st1) with
        | some c => isdoneS it c
        | none => isdone0 it
      if d = some true then pure none else
      match ← pIterate1 fuel its sts with
      | none => pure none
      | some restnext => do
        match ← iter fuel it (statefulCur it (pairState st1)) with
        | none => pure none
        | some nx => pure (some (nx :: restnext))
  | _, _ => pure none
end

/-! ## Running an iterator -/

/-- Iterate until `nothing`, at most `fuel` steps: the elements in order. -/
def runFrom (step : St → M (Option (Val × St))) : Nat → Option (Val × St) → M (List Val)
  | _, none => pure []
  | 0, some _ => .error .fuel
  | k + 1, some (x, s) => do pure (x :: (← runFrom step k (← step s)))

/-- All elements `itr` yields (`for x in itr`), with `fuel` bounding both the
number of elements and the inner loops. -/
def elems (fuel : Nat) (it : Itr) : M (List Val) := do
  runFrom (fun s => iter fuel it (some s)) fuel (← iter fuel it none)

/-- `copyto!(dest, src)` into `n` fresh slots, base/abstractarray.jl:941-951:
`ArgumentError` when `src` has more than `n` elements; unwritten slots stay
`undef`. -/
def copyFrom (step : St → M (Option (Val × St))) : Nat → Nat → Option (Val × St) → M (List Val)
  | _, n, none => pure (List.replicate n .undef)
  | 0, _, some _ => .error .fuel
  | _ + 1, 0, some _ => jthrow (.argumentError "destination has fewer elements than required")
  | k + 1, n + 1, some (x, s) => do pure (x :: (← copyFrom step k n (← step s)))

/-- `collect_to!(dest, itr, i, st)` with `@inbounds` stores, base/array.jl:896-911:
a store past the `n` remaining slots is `Err.oob`. -/
def collectTo (step : St → M (Option (Val × St))) : Nat → Nat → Option (Val × St) → M (List Val)
  | _, n, none => pure (List.replicate n .undef)
  | 0, _, some _ => .error .fuel
  | _ + 1, 0, some _ => .error .oob
  | k + 1, n + 1, some (x, s) => do pure (x :: (← collectTo step k n (← step s)))

/-- `collect(itr)`, base/array.jl:759-860 (`_collect` methods). -/
def collect (fuel : Nat) (it : Itr) : M (List Val) := do
  let step := fun s => iter fuel it (some s)
  let n ← match isz it with
    | .isInfinite => jthrow (.methodError "_collect")
    | .sizeUnknown => pure none
    | .hasLength => do pure (some (← len it).val)
    | .hasShape _ => do pure (some ((← size it).foldl (fun a d => a * d.val) 1))
  match n with
  | none => elems fuel it
  | some n =>
    if ieltype it then do
      allocCheck n
      copyFrom step fuel n.toNat (← iter fuel it none)
    else do
      match ← iter fuel it none with
      | none => do allocCheck n; pure (List.replicate n.toNat .undef)
      | some (v1, s) => do
        allocCheck n
        if n ≤ 0 then jthrow .boundsError else
        pure (v1 :: (← collectTo step fuel (n.toNat - 1) (← step s)))

end JuliaLean.Iterators

/-!
# Julia-level functions of `base/iterators.jl`

Constructors with their dispatch on the argument's type (`take(xs::Take, n)`,
`drop(xs::Drop, n)`, `Iterators.reverse(::Zip)`, ...), `nth`, `first(itr, n)`,
`last(itr, n)`, `only`, `isempty`, `peel`/`rest` and the `Stateful` operations.
Counts of any integer type are `JInt t`.
-/

namespace JuliaLean.Iterators

open JuliaLean

/-- `Int(n)` for an integer of type `t`: `InexactError` when out of range. -/
def toInt {t : IntTy} (n : JInt t) : M JInt64 := liftJ (JInt.convert (IntTy.i64.name) .i64 n.val)

/-- The `Take` inner constructor, base/iterators.jl:781-784. -/
def mkTake (xs : Itr) (n : JInt64) : M Itr :=
  if n < i64 0 then jthrow (.argumentError "Take length must be non-negative") else pure (.take xs n)

/-- The `Drop` inner constructor, base/iterators.jl:840-843. -/
def mkDrop (xs : Itr) (n : JInt64) : M Itr :=
  if n < i64 0 then jthrow (.argumentError "Drop length must be non-negative") else pure (.drop xs n)

/-- `take(xs, n)`, base/iterators.jl:815-816. -/
def take {t : IntTy} (xs : Itr) (n : JInt t) : M Itr := do
  match xs with
  | .take ys m => mkTake ys (jmin (← toInt n) m)
  | _ => mkTake xs (← toInt n)

/-- `drop(xs, n)`, base/iterators.jl:871-873. -/
def drop {t : IntTy} (xs : Itr) (n : JInt t) : M Itr := do
  match xs with
  | .take ys m => do
    let n' ← toInt n
    let d ← match ys with
      | .drop zs k => mkDrop zs (n' + k)
      | _ => mkDrop ys n'
    let r := m - n'
    mkTake d (if i64 0 < r then r else i64 0)
  | .drop ys m => mkDrop ys ((← toInt n) + m)
  | _ => mkDrop xs (← toInt n)

/-- `repeated(x, n) = take(repeated(x), Int(n))`, base/iterators.jl:1111. -/
def repeatedN {t : IntTy} (x : Val) (n : JInt t) : M Itr := do take (.repeated x) (← toInt n)

/-- `cycle(xs, n) = flatten(repeated(xs, n))`, base/iterators.jl:1059. -/
def cycleN {t : IntTy} (xs : Val) (n : JInt t) : M Itr := do pure (.flatten (← repeatedN xs n))

/-- `partition(c, n)`, base/iterators.jl:1436-1439. -/
def partition {t : IntTy} (c : Itr) (n : JInt t) : M Itr := do
  if n.val < 1 then jthrow (.argumentError "cannot create partitions of length n") else
  pure (.partition c (← toInt n))

/-- `_zip_lengths_finite_equal(is)`, base/iterators.jl:401-411 (the flag). -/
def zipLengthsFiniteEqual : List Itr → M (Bool × Option JInt64)
  | [] => pure (true, none)
  | i :: is => do
    match isz i with
    | .isInfinite | .sizeUnknown => pure (false, none)
    | _ => do
      let m ← len i
      let (b, n) ← zipLengthsFiniteEqual is
      pure (b && (n.isNone || n = some m), some m)

mutual
/-- `Iterators.reverse(itr)`, base/iterators.jl:113-160, 521-526, 1074,
1120, 1255, 1379. -/
def reverse : Itr → M Itr
  | .urange k fi li d => pure (.reverse (.urange k fi li d))
  | .reverse it => pure it
  | .zip its => do
    if !(← zipLengthsFiniteEqual its).1 then
      jthrow (.argumentError "Cannot reverse zipped iterators of unknown, infinite, or unequal lengths")
    else pure (.zip (← reverseList its))
  | .cycle it => do pure (.cycle (← reverse it))
  | .repeated x => pure (.repeated x)
  | .take (.repeated x) n => pure (.take (.repeated x) n)
  | .product its => do pure (.product (← reverseList its))
  | .flatten it => do pure (.flatten (.revEach (← reverse it)))
  | .enumerate it => do pure (.revEnum (← reverse it))
  | .revEach it => do pure (.revEach (← reverse it))
  | it => pure (.reverse it)
def reverseList : List Itr → M (List Itr)
  | [] => pure []
  | it :: its => do pure ((← reverse it) :: (← reverseList its))
end

/-- `isempty(itr)`: base/abstractarray.jl:1262 for arrays, base/range.jl:711 for
unit ranges, base/tuple.jl:665-666 for tuples, base/generator.jl:58 for
generators, otherwise base/essentials.jl:1225-1229. -/
def isempty (fuel : Nat) : Itr → M Bool
  | .vec _ xs => pure (xs.length = 0)
  | .tuple xs => pure (xs = [])
  | .urange _ fi li _ => pure (li < fi)
  | .revEach it => isempty fuel it
  | it => do
    match ← isdone0 it with
    | some d => pure d
    | none => do pure (← iter fuel it none).isNone

/-- `first(itr)`, base/abstractarray.jl:474-478. -/
def first (fuel : Nat) (it : Itr) : M Val := do
  match ← iter fuel it none with
  | none => jthrow (.argumentError "collection must be non-empty")
  | some (x, _) => pure x

/-- `first(itr, n)`: base/abstractarray.jl:505 and the vector method 507-510. -/
def firstN {t : IntTy} (fuel : Nat) (it : Itr) (n : JInt t) : M (List Val) :=
  match it with
  | .vec _ xs =>
    if n.val < 0 then jthrow (.argumentError "Number of elements must be non-negative")
    else pure (xs.take (min n.val xs.length).toNat)
  | _ => do collect fuel (← take it n)

/-- `last(itr, n)`: base/abstractarray.jl:555 and the vector method 557-560. -/
def lastN {t : IntTy} (fuel : Nat) (it : Itr) (n : JInt t) : M (List Val) :=
  match it with
  | .vec _ xs =>
    if n.val < 0 then jthrow (.argumentError "Number of elements must be non-negative")
    else pure (xs.drop (xs.length - (min n.val xs.length).toNat))
  | _ => do pure (← collect fuel (← take (← reverse it) n)).reverse

/-- `only(x)`, base/iterators.jl:1659-1690. -/
def only (fuel : Nat) : Itr → M Val
  | .tuple [x] => pure x
  | .tuple _ => jthrow (.argumentError "Tuple contains n elements, must contain exactly 1 element")
  | it => do
    match ← iter fuel it none with
    | none => jthrow (.argumentError "Collection is empty, must contain exactly 1 element")
    | some (ret, s) => do
      if (← iter fuel it (some s)).isSome then
        jthrow (.argumentError "Collection has multiple elements, must contain exactly 1 element")
      else pure ret

mutual
/-- `last(x)`: `a[end]` for vectors (base/abstractarray.jl:530), the end point
of a unit range even when empty (base/range.jl), `map(last, p.iterators)` for
products (base/iterators.jl:1256). -/
def lastOf : Itr → M Val
  | .vec _ xs => match xs.getLast? with
    | some x => pure x
    | none => jthrow .boundsError
  | .urange _ _ li d => pure (.int (li.val + d))
  | .product its => do pure (.tup (← lastList its))
  | _ => jthrow (.methodError "last")
def lastList : List Itr → M (List Val)
  | [] => pure []
  | it :: its => do pure ((← lastOf it) :: (← lastList its))
end

/-- Integer value of a promoted Julia integer operation. -/
def promotedWrap (t s : IntTy) (x : Int) : Int := wrapInt (IntTy.promote t s) x

/-- `A[begin + n - 1]` for a vector or a unit range, base/iterators.jl:1756:
`begin + n - 1` is computed in `promote_type(Int, typeof(n))`, then bounds
checked. The index `n` has type `t` and value `n`. -/
def arrayNth (it : Itr) (t : IntTy) (n : Int) : M Val :=
  match it with
  | .vec _ xs =>
    let i := promotedWrap .i64 t (1 + n - 1)
    if 1 ≤ i ∧ i ≤ xs.length then pure (xs.getD (i - 1).toNat .undef) else jthrow .boundsError
  | .urange _ fi li d =>
    let i := promotedWrap .i64 t (fi.val + n - 1)
    if fi.val ≤ i ∧ i ≤ li.val then pure (.int (i + d)) else jthrow .boundsError
  | _ => jthrow (.methodError "getindex")

/-- The `for _ in 1:n-1` loop of the generic `_nth`. -/
def nthLoop (fuel : Nat) (it : Itr) : Nat → Option (Val × St) → M (Option (Val × St))
  | 0, y => pure y
  | _ + 1, none => pure none
  | k + 1, some (_, s) => do nthLoop fuel it k (← iter fuel it (some s))

/-- The generic `_nth(::IteratorSize, itr, n)`, base/iterators.jl:1777-1787. -/
def genericNth (fuel : Nat) (it : Itr) (n : Int) : M Val := do
  if n ≤ 0 then jthrow .boundsError else
  match ← nthLoop fuel it (n - 1).toNat (← iter fuel it none) with
  | none => jthrow .boundsError
  | some (x, _) => pure x

/-- `Val` as the iterator it denotes (vectors, tuples, ranges). -/
def Val.toItr : Val → Itr
  | .vec et xs => .vec et xs
  | .tup xs => .tuple xs
  | .rng lo hi => .urange .unit (i64 1) (i64 (hi - lo + 1)) (lo - 1)
  | v => .flatten (.tuple [v])

/-- `nth` of a value: arrays index, tuples and numbers iterate. -/
def nthVal (fuel : Nat) (v : Val) (t : IntTy) (n : Int) : M Val :=
  match v with
  | .vec _ _ | .rng _ _ => arrayNth v.toItr t n
  | .tup _ => genericNth fuel v.toItr n
  | .int x =>
    if n ≤ 0 then jthrow .boundsError
    else if n = 1 then pure (.int x) else jthrow .boundsError
  | _ => jthrow (.methodError "nth")

/-- `mod1(n, k)` for `n > 0`, `k > 0` (exact in the promoted type). -/
def mod1Pos (n k : Int) : Int := (n - 1) % k + 1

mutual
/-- `nth(itr, n)` for `n` of type `t`, base/iterators.jl:1753-1789. -/
def nth (fuel : Nat) : Itr → IntTy → Int → M Val
  | .vec et xs, t, n => arrayNth (.vec et xs) t n
  | .urange k fi li d, t, n => arrayNth (.urange k fi li d) t n
  -- base/iterators.jl:1754, 1758-1764
  | .cycle xs, t, n =>
    match isz xs with
    | .hasShape _ | .hasLength => do
      let bigN ← len xs
      if bigN = i64 0 then jthrow .boundsError else
      if 0 < n then nth fuel xs (IntTy.promote t .i64) (mod1Pos n bigN.val)
      else nth fuel xs t n
    | _ => genericNth fuel (.cycle xs) n
  -- base/iterators.jl:1755, 1767-1775
  | .flatten (.take (.repeated x) cycles), t, n =>
    match x.isz with
    | .hasShape _ | .hasLength => do
      let k ← x.length
      if n > (k * cycles).val ∨ k = i64 0 then jthrow .boundsError else
      if 0 < n then nthVal fuel x (IntTy.promote t .i64) (mod1Pos n k.val)
      else nthVal fuel x t n
    | _ => genericNth fuel (.flatten (.take (.repeated x) cycles)) n
  -- base/iterators.jl:1789
  | .zip its, t, n => do pure (.tup (← nthList fuel its t n))
  | it, _, n => genericNth fuel it n
def nthList (fuel : Nat) : List Itr → IntTy → Int → M (List Val)
  | [], _, _ => pure []
  | it :: its, t, n => do pure ((← nth fuel it t n) :: (← nthList fuel its t n))
end

/-- `Iterators.nth(itr, n)` with `n::t`. -/
def nthJ {t : IntTy} (fuel : Nat) (it : Itr) (n : JInt t) : M Val := nth fuel it t n.val

/-- `Iterators.peel(itr)`, base/iterators.jl:725-730: the first element and
`rest(itr, state)`. -/
def peel (fuel : Nat) (it : Itr) : M (Option (Val × Itr)) := do
  match ← iter fuel it none with
  | none => pure none
  | some (x, s) => pure (some (x, .rest it s))

/-! ## `Iterators.Stateful` -/

/-- `popfirst!(s)`, base/iterators.jl:1609-1618: the value and the advanced
object. -/
def popfirst : Itr → M (Val × Itr)
  | .stateful et xs pos =>
    if xs.length ≤ pos then .error .eof else pure (xs.getD pos .undef, .stateful et xs (pos + 1))
  | _ => jthrow (.methodError "popfirst!")

/-- `peek(s, sentinel)`, base/iterators.jl:1620-1623. -/
def peek (sentinel : Val) : Itr → M Val
  | .stateful _ xs pos => pure (if pos < xs.length then xs.getD pos .undef else sentinel)
  | _ => jthrow (.methodError "peek")

end JuliaLean.Iterators


/-!
# Iterator-size and eltype trait algebra of `base/iterators.jl`

The helpers combine the `IteratorSize` of the component iterators of `zip`
and `product`, and compute `length(take(..))`/`length(drop(..))`. Their
properties are stated against the true element count of an iterator, `Len`
(`fin n` elements, or `inf`inite): an `IteratorSize` value *agrees* with a
count when `HasLength`/`HasShape` go with finite counts and `IsInfinite` with
infinite ones (base/generator.jl:69-82).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-! ## `and_iteratorsize`, `and_iteratoreltype` -/

/-- `and_iteratorsize`, base/iterators.jl:71-76: equal traits are returned
(`(isz::T, ::T)`, line 71, and `HasShape{N}`, line 74), mixed `HasLength` /
`HasShape` and `HasShape`s of different `N` give `HasLength` (72, 73, 75),
everything else `SizeUnknown()` (76). -/
def andIsz : Isz → Isz → Isz
  | .hasShape m, .hasShape n => if m = n then .hasShape n else .hasLength
  | .hasLength, .hasLength => .hasLength
  | .sizeUnknown, .sizeUnknown => .sizeUnknown
  | .isInfinite, .isInfinite => .isInfinite
  | .hasLength, .hasShape _ => .hasLength
  | .hasShape _, .hasLength => .hasLength
  | _, _ => .sizeUnknown

/-- `and_iteratoreltype`, base/iterators.jl:78-79 (`true` is `HasEltype()`). -/
def andIel (a b : Bool) : Bool := if a = b then a else false

/-! ## `zip_iteratorsize`, `zip_iteratoreltype` -/

/-- `zip_iteratorsize(a, b)`, base/iterators.jl:508-512. -/
def zipIsz2 : Isz → Isz → Isz
  | .isInfinite, .isInfinite => .isInfinite          -- 512
  | .hasLength, .isInfinite => .hasLength            -- 509
  | .hasShape _, .isInfinite => .hasLength           -- 510
  | .isInfinite, b =>                                -- 511: zip_iteratorsize(b, a)
    match b with
    | .hasLength => .hasLength
    | .hasShape _ => .hasLength
    | _ => andIsz b .isInfinite
  | a, b => andIsz a b                               -- 508

/-- `zip_iteratorsize(...)`, base/iterators.jl:506-507, 513. -/
def zipIsz : List Isz → Isz
  | [] => .isInfinite                                -- 506
  | [a] => a                                         -- 507
  | a :: b :: rest => zipIsz2 a (zipIsz (b :: rest)) -- 513

/-- `zip_iteratoreltype(...)`, base/iterators.jl:515-517. -/
def zipIel : List Bool → Bool
  | [] => true                                       -- 515
  | [a] => a                                         -- 516
  | a :: b :: rest => andIel a (zipIel (b :: rest))  -- 517

/-- `IteratorSize(Zip{Is})`, base/iterators.jl:503: `zip_iteratorsize` of the
component traits. -/
def zipTypeIsz (cs : List Isz) : Isz := zipIsz cs

/-- `IteratorEltype(Zip{Is})`, base/iterators.jl:504. -/
def zipTypeIel (cs : List Bool) : Bool := zipIel cs

/-! ## `prod_iteratorsize` -/

/-- `prod_iteratorsize(a, b)`, base/iterators.jl:1157-1166. -/
def prodIsz2 : Isz → Isz → Isz
  | .hasLength, .hasLength => .hasShape 2            -- 1157
  | .hasLength, .hasShape n => .hasShape (n + 1)     -- 1158
  | .hasShape n, .hasLength => .hasShape (n + 1)     -- 1159
  | .hasShape m, .hasShape n => .hasShape (m + n)    -- 1160
  | .isInfinite, .isInfinite => .isInfinite          -- 1163
  | _, .isInfinite => .isInfinite                    -- 1164
  | .isInfinite, _ => .isInfinite                    -- 1165
  | _, _ => .sizeUnknown                             -- 1166

/-- `prod_iteratorsize(...)`, base/iterators.jl:1154-1155, 1167. -/
def prodIsz : List Isz → Isz
  | [] => .hasShape 0                                -- 1154
  | [a] => a                                         -- 1155
  | a :: b :: rest => prodIsz2 a (prodIsz (b :: rest)) -- 1167

/-- `IteratorSize(ProductIterator{T})`, base/iterators.jl:1150-1152:
`HasShape{0}()` for no factors, otherwise `prod_iteratorsize` of the factor
traits followed by `HasShape{0}()`. -/
def productIsz (cs : List Isz) : Isz :=
  match cs with
  | [] => .hasShape 0
  | _ => prodIsz (cs ++ [.hasShape 0])

/-- Number of dimensions an iterator contributes to a product: `N` for
`HasShape{N}`, one for `HasLength`. -/
def Isz.dims : Isz → Nat
  | .hasShape n => n
  | _ => 1

/-! ## `IteratorEltype(ProductIterator)` -/

/-- `IteratorEltype(ProductIterator{T})`, base/iterators.jl:1188-1195:
`HasEltype` for no factors (1188), the factor's trait for one factor (1189),
otherwise `EltypeUnknown` if any factor's is, else the last factor's trait
(1191-1195). -/
def productIel (cs : List Bool) : Bool :=
  match cs with
  | [] => true
  | [c] => c
  | _ => if cs.contains false then false else cs.getLastD true

/-! ## `_min_length`, `_diff_length` -/

/-- `_min_length(a, b, A, B)`, base/iterators.jl:58-61, given the two
`length` calls and the two `IteratorSize` traits. -/
def minLength (la lb : R JInt64) : Isz → Isz → R JInt64
  | .isInfinite, .isInfinite => do let x ← la; let y ← lb; pure (jmin x y) -- 58
  | _, .isInfinite => la                                               -- 59
  | .isInfinite, _ => lb                                               -- 60
  | _, _ => do let x ← la; let y ← lb; pure (jmin x y)                  -- 61

/-- `_diff_length(a, b, A, B)`, base/iterators.jl:63-69. -/
def diffLength (la lb : R JInt64) : Isz → Isz → R JInt64
  | _, .isInfinite => pure (i64 0)                                     -- 63, 64
  | .isInfinite, _ => la                                               -- 65
  | _, _ => do                                                         -- 66-69
    let m ← la
    let n ← lb
    pure (if m > n then m - n else i64 0)
end JuliaLean.IteratorsCov


/-!
# Leaf iterators: vectors and tuples

`iterate(A::AbstractArray, i = firstindex(A))` for `IndexLinear` arrays
(base/abstractarray.jl:1250-1260) and `iterate(t::Tuple, i = 1)`
(base/tuple.jl:69-73) both use the next index as state:
`checkbounds(Bool, A, i) ? (A[i], i + 1) : nothing`.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- `A[i]` for `1 ≤ i ≤ length(A)` (Julia indices are 1-based here). -/
def getIdx (xs : List V) (i : Int) : V := xs.getD (i - 1).toNat .nothing

/-- One indexed iteration step from index `i`. -/
def idxStep (xs : List V) (i : Int) : Step :=
  if 1 ≤ i ∧ i ≤ xs.length then .ok (some (getIdx xs i, .int (i + 1))) else .ok none

/-- `iterate(A, s)` for an indexed collection; a non-integer state is a
`MethodError`. -/
def idxNext (xs : List V) : V → Step
  | .int i => idxStep xs i
  | _ => jthrow (.methodError "iterate")

/-- A `Vector{et}` with elements `xs`: `IteratorSize` `HasShape{1}`
(base/generator.jl:101), `length`, `size`, `eltype`. -/
def vecIt (et : Ty) (xs : List V) : It where
  first := idxStep xs 1
  next := idxNext xs
  isz := .hasShape 1
  elt := et
  len := .ok (i64 xs.length)
  size := .ok [i64 xs.length]

/-- A tuple with elements `xs` and type `Tuple{ts...}`: `IteratorSize`
`HasLength` (base/generator.jl:100). -/
def tupIt (ts : List Ty) (xs : List V) : It where
  first := idxStep xs 1
  next := idxNext xs
  isz := .hasLength
  elt := ts.foldr .union .bottom
  len := .ok (i64 xs.length)
end JuliaLean.IteratorsCov


/-!
# `Iterators.Take` and `Iterators.Drop` (base/iterators.jl:776-892)
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- `iterate(it, rest...)` for a state tail `rest` that is empty or one state. -/
def innerIter (it : It) : List V → Step
  | [] => it.first
  | [s] => it.next s
  | _ => jthrow (.methodError "iterate")

/-- `isdone(it, rest...)` for a state tail `rest`. -/
def innerDone (it : It) : List V → R (Option Bool)
  | [] => it.done0
  | [s] => it.doneS s
  | _ => jthrow (.methodError "isdone")

/-- Julia's `|` on `Union{Bool, Missing}` (`none` is `missing`). -/
def or3 : Option Bool → Option Bool → Option Bool
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

/-! ## `Take` -/

/-- The tail of `iterate(it::Take, state)` after `n <= 0` was ruled out:
`y === nothing && return nothing; return y[1], (n - 1, y[2])`. -/
def takeCont (n : Int) : Step → Step
  | .ok none => .ok none
  | .ok (some (y, s)) => .ok (some (y, .tup [.int (i64 n - i64 1).val, s]))
  | .error e => .error e

/-- `iterate(it::Take, state=(it.n,))`, base/iterators.jl:827-833. -/
def takeNext (xs : It) : V → Step
  | .tup (.int n :: rest) => if n ≤ 0 then .ok none else takeCont n (innerIter xs rest)
  | _ => jthrow (.methodError "iterate")

/-- `take_iteratorsize`, base/iterators.jl:820-821. -/
def takeIsz : Isz → Isz
  | .sizeUnknown => .sizeUnknown
  | _ => .hasLength

/-- `isdone(t::Take, state) = (state[1] <= 0) | isdone(t.xs, tail(state)...)`,
base/iterators.jl:825. -/
def takeDoneS (xs : It) : V → R (Option Bool)
  | .tup (.int n :: rest) => do
    let d ← innerDone xs rest
    pure (or3 (some (decide (n ≤ 0))) d)
  | _ => jthrow (.methodError "isdone")

/-- The object `Take(xs, n)` with its methods: `eltype` and `IteratorEltype`
of the wrapped type (818-819), `IteratorSize` (822), `length` (823,
`_min_length(t.xs, 1:t.n, IteratorSize(t.xs), HasLength())` with
`length(1:n) == n`), the two `isdone` methods (824-825) and `iterate`
(827-833). -/
def takeIt (xs : It) (n : JInt64) : It where
  first := takeNext xs (.tup [.int n.val])
  next := takeNext xs
  isz := takeIsz xs.isz
  iel := xs.iel
  elt := xs.elt
  len := minLength xs.len (.ok n) xs.isz .hasLength
  done0 := xs.done0
  doneS := takeDoneS xs

/-- The inner constructor `Take(xs, n)`, base/iterators.jl:781-784. -/
def mkTake (xs : It) (n : JInt64) : R It :=
  if n < i64 0 then jthrow (.argumentError "Take length must be non-negative") else .ok (takeIt xs n)

/-- `take(xs, n::Integer) = Take(xs, Int(n))`, base/iterators.jl:815, for an
`Int` count. -/
def take (xs : It) (n : JInt64) : R It := mkTake xs n

/-- `take(xs::Take, n) = Take(xs.xs, min(Int(n), xs.n))`, base/iterators.jl:816:
`inner` is `xs.xs` and `m` is `xs.n`. -/
def takeTake (inner : It) (m : JInt64) (n : JInt64) : R It := mkTake inner (jmin n m)

/-! ## `Drop` -/

/-- The loop `for _ in 1:it.n; y === nothing && return y; y = iterate(it.xs, y[2]); end`
of `iterate(it::Drop)`, base/iterators.jl:885-888. -/
def dropLoop (xs : It) : Nat → Step → Step
  | 0, y => y
  | k + 1, .ok none => .ok none
  | k + 1, .ok (some (_, s)) => dropLoop xs k (xs.next s)
  | _ + 1, .error e => .error e

/-- `drop_iteratorsize`, base/iterators.jl:877-879. -/
def dropIsz : Isz → Isz
  | .sizeUnknown => .sizeUnknown
  | .hasShape _ => .hasLength
  | .hasLength => .hasLength
  | .isInfinite => .isInfinite

/-- The object `Drop(xs, n)` with its methods: `eltype`, `IteratorEltype`
(875-876), `IteratorSize` (880), `length` (881,
`_diff_length(d.xs, 1:d.n, IteratorSize(d.xs), HasLength())`), `iterate(it::Drop)`
(883-890), `iterate(it::Drop, state)` (891) and `isdone(it::Drop, state)` (892).
There is no `isdone(::Drop)` method: the fallback answers `missing`. -/
def dropIt (xs : It) (n : JInt64) : It where
  first := dropLoop xs n.val.toNat xs.first
  next := xs.next
  isz := dropIsz xs.isz
  iel := xs.iel
  elt := xs.elt
  len := diffLength xs.len (.ok n) xs.isz .hasLength
  done0 := .ok none
  doneS := xs.doneS

/-- The inner constructor `Drop(xs, n)`, base/iterators.jl:840-843. -/
def mkDrop (xs : It) (n : JInt64) : R It :=
  if n < i64 0 then jthrow (.argumentError "Drop length must be non-negative") else .ok (dropIt xs n)
end JuliaLean.IteratorsCov


/-!
# `Iterators.Enumerate` (base/iterators.jl:164-233)
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- `T === Union{}`. -/
def Ty.isBottom : Ty → Bool
  | .bottom => true
  | _ => false

/-- `TupleOrBottom(ts...)`: `Union{}` if a field type is `Union{}`, else `Tuple{ts...}`. -/
def tupleOrBottom (ts : List Ty) : Ty := if ts.any Ty.isBottom then .bottom else .tuple ts

/-- The tail of `iterate(e::Enumerate, state)`: `n === nothing && return n;
(i, n[1]), (i+1, n[2])`. -/
def enumCont (i : Int) : Step → Step
  | .ok none => .ok none
  | .ok (some (x, s)) => .ok (some (.tup [.int i, x], .tup [.int (i64 i + i64 1).val, s]))
  | .error e => .error e

/-- `iterate(e::Enumerate, state=(1,))`, base/iterators.jl:211-216:
`i, rest = state[1], tail(state); n = iterate(e.itr, rest...)`. -/
def enumNext (it : It) : V → Step
  | .tup (.int i :: rest) => enumCont i (innerIter it rest)
  | _ => jthrow (.methodError "iterate")

/-- The object `enumerate(itr) = Enumerate(itr)` (207) with `length` (209),
`size` (210), `iterate` (211-216), `last(e) = (length(e.itr), last(e.itr))`
(217), `eltype` `TupleOrBottom(Int, eltype(I))` (219), `IteratorSize` and
`IteratorEltype` of `I` (221-222). -/
def enumIt (it : It) : It where
  first := enumNext it (.tup [.int 1])
  next := enumNext it
  isz := it.isz
  iel := it.iel
  elt := tupleOrBottom [.int, it.elt]
  len := it.len
  size := it.size
  lastv := do
    let n ← it.len
    let l ← it.lastv
    pure (.tup [.int n.val, l])

/-- The tail of `iterate(r::Reverse{<:Enumerate}, state)`, base/iterators.jl:228-233:
`n = iterate(ri, rest...); (i, n[1]), (i-1, ri, n[2])`. -/
def revEnumCont (ri : V) (i : Int) : Step → Step
  | .ok none => .ok none
  | .ok (some (x, s)) => .ok (some (.tup [.int i, x], .tup [.int (i64 i - i64 1).val, ri, s]))
  | .error e => .error e

def revEnumNext (rit : It) : V → Step
  | .tup (.int i :: ri :: rest) => revEnumCont ri i (innerIter rit rest)
  | _ => jthrow (.methodError "iterate")

/-- `Iterators.Reverse(enumerate(itr))` given `ri = reverse(itr)` (the object
`riObj` with iterator `rit`): `iterate(r) = iterate(r, (length(ri), ri))`
(224-227) and `iterate(r, state)` (228-233). -/
def revEnumIt (rit : It) (riObj : V) : It where
  first := rit.len.bind fun n => revEnumNext rit (.tup [.int n.val, riObj])
  next := revEnumNext rit
end JuliaLean.IteratorsCov


/-!
# `Iterators.Zip` (base/iterators.jl:376-526)

A `Zip` holds a tuple of component iterators `is`. Its state is the tuple of
component states; a component that has not been started yet is iterated with
`iterate(is[k])`, modelled by the position `none` (`ss[k] = ()` in Julia).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- `iterate(it, o...)`: `iterate(it)` at the start, `iterate(it, s)` later. -/
def stepOf (it : It) : Option V → Step
  | none => it.first
  | some s => it.next s

/-- `isdone(it, o...)`. -/
def doneOf (it : It) : Option V → R (Option Bool)
  | none => it.done0
  | some s => it.doneS s

/-! ## Iteration -/

/-- `_zip_isdone(is, ss)`, base/iterators.jl:496-501. -/
def zipIsdone : List (It × Option V) → R (Bool × List (Option Bool))
  | [] => .ok (false, [])
  | (it, o) :: cs => do
    let d ← doneOf it o
    let (d', ds) ← zipIsdone cs
    pure (decide (d = some true) || d', d :: ds)

/-- `_zip_all_missing(ds)`, base/iterators.jl:462-463. -/
def zipAllMissing : List (Option Bool) → Bool
  | [] => true
  | d :: ds => d.isNone && zipAllMissing ds

/-- `_zip_iterate_in_order(is, ss)`, base/iterators.jl:465-472. -/
def zipInOrder : List (It × Option V) → R (Option (List (V × V)))
  | [] => .ok (some [])
  | (it, o) :: cs => do
    match ← stepOf it o with
    | none => pure none
    | some x =>
      match ← zipInOrder cs with
      | none => pure none
      | some y => pure (some (x :: y))

/-- An entry of `_zip_iterate_unknown`: `_ZipSkip()` or an `iterate` result. -/
inductive ZX where
  | skip
  | got (p : V × V)

/-- `_zip_iterate_unknown(is, ss, ds)`, base/iterators.jl:478-485: iterate the
components whose `isdone` was `missing`. -/
def zipUnknown : List (It × Option V) → List (Option Bool) → R (Option (List ZX))
  | [], [] => .ok (some [])
  | (it, o) :: cs, d :: ds => do
    let x ← if d.isNone then
        (do match ← stepOf it o with
            | none => pure none
            | some p => pure (some (ZX.got p)))
      else pure (some ZX.skip)
    match x with
    | none => pure none
    | some x =>
      match ← zipUnknown cs ds with
      | none => pure none
      | some y => pure (some (x :: y))
  | _, _ => jthrow .boundsError

/-- `_zip_iterate_rest(is, ss, xs)`, base/iterators.jl:487-494: iterate the
skipped components. -/
def zipRest : List (It × Option V) → List ZX → R (Option (List (V × V)))
  | [], [] => .ok (some [])
  | (it, o) :: cs, x :: xs => do
    let r ← match x with
      | .skip => stepOf it o
      | .got p => pure (some p)
    match r with
    | none => pure none
    | some p =>
      match ← zipRest cs xs with
      | none => pure none
      | some y => pure (some (p :: y))
  | _, _ => jthrow .boundsError

/-- `_zip_iterate_all(is, ss)`, base/iterators.jl:448-460. -/
def zipAll (cs : List (It × Option V)) : Step :=
  match zipIsdone cs with
  | .error e => .error e
  | .ok (d, ds) =>
    if d then .ok none else
    let xs := if zipAllMissing ds then zipInOrder cs else
      match zipUnknown cs ds with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some xs1) => zipRest cs xs1
    match xs with
    | .error e => .error e
    | .ok none => .ok none
    | .ok (some xs) => .ok (some (.tup (xs.map Prod.fst), .tup (xs.map Prod.snd)))

/-- `iterate(z::Zip, ss) = _zip_iterate_all(z.is, map(tuple, ss))`, 441. -/
def zipNext (its : List It) : V → Step
  | .tup ss => if ss.length = its.length then zipAll (its.zip (ss.map some)) else jthrow .boundsError
  | _ => jthrow (.methodError "iterate")

/-- `_zip_any_isdone(is, ss)`, base/iterators.jl:433-438. -/
def zipAnyIsdone : List (It × Option V) → R (Option Bool)
  | [] => .ok (some false)
  | (it, o) :: cs => do
    let d1 ← doneOf it o
    if d1 = some true then pure (some true) else pure (or3 d1 (← zipAnyIsdone cs))

/-- `isdone(z::Zip, ss) = _zip_any_isdone(z.is, map(tuple, ss))`, 431. -/
def zipDoneS (its : List It) : V → R (Option Bool)
  | .tup ss => if ss.length = its.length then zipAnyIsdone (its.zip (ss.map some)) else jthrow .boundsError
  | _ => jthrow (.methodError "isdone")

/-! ## `length`, `size`, `axes` -/

/-- `_zip_min_length(is)`, base/iterators.jl:385-394 (`nothing` is `none`). -/
def zipMinLength : List It → R (Option JInt64)
  | [] => .ok none
  | i :: is => do
    let n ← zipMinLength is
    if i.isz = .isInfinite then pure n else
    match n with
    | none => do pure (some (← i.len))
    | some n => do pure (some (jmin n (← i.len)))

/-- `length(z::Zip)`, base/iterators.jl:380-384. -/
def zipLength (its : List It) : R JInt64 := do
  match ← zipMinLength its with
  | none => jthrow (.argumentError "iterator is of undefined length")
  | some n => pure n

/-- `_zip_lengths_finite_equal(is)`, base/iterators.jl:401-411. -/
def zipLFE : List It → R (Bool × Option JInt64)
  | [] => .ok (true, none)
  | i :: is =>
    if i.isz = .isInfinite ∨ i.isz = .sizeUnknown then .ok (false, none) else do
    let m ← i.len
    let (b, n) ← zipLFE is
    pure (b && (match n with | none => true | some n => decide (n = m)), some m)

/-- `promote_shape(a::Dims, b::Dims)` (base/indices.jl:112-130): the longer
shape, provided the shorter one is a prefix of it and the extra dimensions are 1. -/
def promoteShape (a b : List JInt64) : R (List JInt64) :=
  let (a, b) := if a.length < b.length then (b, a) else (a, b)
  if a.take b.length = b ∧ ∀ d ∈ a.drop b.length, d.val = 1 then .ok a
  else .error .dimensionMismatch

/-- `_promote_tuple_shape(a, b)`, base/iterators.jl:414-416; the `OneTo` axes
method (414) is the `Integer` one on the axis lengths. -/
def pts2 : List JInt64 → List JInt64 → R (List JInt64)
  | [m], [n] => .ok [jmin m n]
  | a, b => promoteShape a b

/-- `_promote_tuple_shape(a, b...)` and `_promote_tuple_shape(a)`,
base/iterators.jl:417-418; there is no method without arguments. -/
def pts : List (List JInt64) → R (List JInt64)
  | [] => jthrow (.methodError "_promote_tuple_shape")
  | [a] => .ok a
  | a :: b :: rest => do pts2 a (← pts (b :: rest))

/-- `size(z::Zip)` (412) and, on axis lengths, `axes(z::Zip)` (413). -/
def zipSize (its : List It) : R (List JInt64) := do pts (← its.mapM (·.size))

/-! ## `nth`, `last` -/

/-- The loop of the generic `_nth(::IteratorSize, itr, n)`,
base/iterators.jl:1780-1784: `for _ in 1:n-1; y === nothing && break;
y = iterate(itr, y[2]); end`. -/
def nthLoop (nx : V → Step) : Nat → Step → Step
  | 0, y => y
  | _ + 1, .ok none => .ok none
  | k + 1, .ok (some (_, s)) => nthLoop nx k (nx s)
  | _ + 1, .error e => .error e

/-- The generic `_nth(::IteratorSize, itr, n)`, base/iterators.jl:1777-1787. -/
def nthGen (it : It) (n : Int) : R V :=
  if ¬ 0 < n then jthrow .boundsError else
  match nthLoop it.next (n - 1).toNat it.first with
  | .ok none => jthrow .boundsError
  | .ok (some (x, _)) => .ok x
  | .error e => .error e

/-- `last(z::Zip) = nth(z, length(z))` (519) with
`_nth(::IteratorSize, z::Zip, n) = map(nth(n), z.is)` (1789) and the generic
`nth` of each component. -/
def zipLast (its : List It) : R V := do
  let n ← zipLength its
  let xs ← its.mapM fun it => nthGen it n.val
  pure (.tup xs)

/-- `zip(a...) = Zip(a)` (379) with the `Zip` methods: `iterate` (440-441),
`isdone` (430-431), `length` (380), `size` (412), `eltype` (425),
`IteratorSize` and `IteratorEltype` (503-504) and `last` (519). -/
def zipIt (its : List It) : It where
  first := zipAll (its.map (·, none))
  next := zipNext its
  isz := zipTypeIsz (its.map (·.isz))
  iel := zipTypeIel (its.map (·.iel))
  elt := tupleOrBottom (its.map (·.elt))
  len := zipLength its
  size := zipSize its
  done0 := zipAnyIsdone (its.map (·, none))
  doneS := zipDoneS its
  lastv := zipLast its
end JuliaLean.IteratorsCov


/-!
# `Iterators.reverse` and `Iterators.Reverse` (base/iterators.jl:81-162)

`Iterators.reverse` dispatches on the type of its argument, so its argument
is a small deep embedding `Obj` of the Julia objects it has methods for:
numbers and characters, pairs, unit ranges `lo:hi`, descending ranges
`hi:-1:lo`, vectors, tuples, `Iterators.Reverse` objects and generators.
`Obj.it` is the object's iterator: `iterate` of numbers (base/number.jl:329-330),
pairs (base/pair.jl:41), ranges (base/range.jl:935-942), vectors and tuples
(`Leaves`), the `iterate` methods of `Reverse` (base/iterators.jl:136-162) and
of `Generator` (base/generator.jl:44-50).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Julia objects `Iterators.reverse` dispatches on. `urange lo hi` is the
`UnitRange` `lo:hi` (normalised: `hi ≥ lo - 1`); `drange hi lo` is the
`StepRange` `hi:-1:lo` (empty when `hi < lo`); `rev o` is
`Iterators.Reverse(o)`; `gen f o` is `Base.Generator(f, o)`. -/
inductive Obj where
  | num (v : V)
  | pair (a b : V)
  | urange (lo hi : JInt64)
  | drange (hi lo : JInt64)
  | vec (xs : List V)
  | tup (xs : List V)
  | rev (o : Obj)
  | gen (f : V → V) (o : Obj)

/-! ## Leaf iterators -/

/-- `iterate(r::OrdinalRange, i)` for `lo:hi`: `i == last(r) && return nothing`,
then `i + 1`. -/
def urNext (hi : JInt64) : V → Step
  | .int i => if i = hi.val then .ok none else
    let nx := (i64 i + i64 1).val
    .ok (some (.int nx, .int nx))
  | _ => jthrow (.methodError "iterate")

/-- `iterate(r::OrdinalRange)` for `lo:hi`: `isempty(r) ? nothing : (first(r), first(r))`. -/
def urFirst (lo hi : JInt64) : Step :=
  if hi < lo then .ok none else .ok (some (.int lo.val, .int lo.val))

/-- `iterate(r, i)` for `hi:-1:lo`: `i == last(r)` ends, else `i - 1`. -/
def drNext (lo : JInt64) : V → Step
  | .int i => if i = lo.val then .ok none else
    let nx := (i64 i - i64 1).val
    .ok (some (.int nx, .int nx))
  | _ => jthrow (.methodError "iterate")

def drFirst (hi lo : JInt64) : Step :=
  if hi < lo then .ok none else .ok (some (.int hi.val, .int hi.val))

/- Unfolding these during unification decides `hi < lo` on `Int64` literals,
which evaluates wraparound by well-founded recursion; the proofs unfold them
explicitly. -/
attribute [local irreducible] urFirst drFirst

/-- `iterate(p::Pair, i=1) = i > 2 ? nothing : (getfield(p, i), i + 1)`. -/
def pairNext (a b : V) : V → Step
  | .int i => if i > 2 then .ok none else
    if i = 1 then .ok (some (a, .int 2)) else if i = 2 then .ok (some (b, .int 3))
    else jthrow .boundsError
  | _ => jthrow (.methodError "iterate")

/-- `Generator` iteration, base/generator.jl:44-50: `y = iterate(g.iter, s...)`,
`nothing` stays `nothing`, otherwise `(g.f(y[1]), y[2])`. -/
def genCont (f : V → V) : Step → Step
  | .ok (some (x, s)) => .ok (some (f x, s))
  | y => y

/-- The step of `iterate(A::Reverse{<:AbstractArray}, state)` and of the generic
`iterate(A::Reverse, state)` (base/iterators.jl:136-150), whose bodies are
identical: `y = iterate(state...)` on the reversed index range `r`, then
`(A.itr[idx], (state[1], itrs))`. -/
def revArrCont (get : V → R V) (r : V) : Step → Step
  | .ok none => .ok none
  | .ok (some (idx, itrs)) => do
    let v ← get idx
    pure (some (v, .tup [r, itrs]))
  | .error e => .error e

/-- `iterate(r::Reverse{<:Union{Tuple, NamedTuple}}, i::Int = length(r.itr)) =
i < 1 ? nothing : (r.itr[i], i-1)`, base/iterators.jl:162. -/
def revTupStep (xs : List V) (i : Int) : Step :=
  if i < 1 then .ok none else
  if i ≤ xs.length then .ok (some (getIdx xs i, .int (i - 1))) else jthrow .boundsError

def revTupNext (xs : List V) : V → Step
  | .int i => revTupStep xs i
  | _ => jthrow (.methodError "iterate")

/-- `iterate(r::Reverse{Union{}})` and `iterate(r::Reverse{Union{}}, state)`,
base/iterators.jl:153-154. -/
def revBottomIt : It where
  first := jthrow (.argumentError "cannot iterate a reversed iterator of type Union{}")
  next := fun _ => jthrow (.argumentError "cannot iterate a reversed iterator of type Union{}")

/-- The reversed index range `reverse(eachindex(A))` of an array with `n`
elements, `n:-1:1`, as the value carried in the state. -/
def revIdxObj (n : Nat) : V := .tup [.int n, .int (-1), .int 1]

/-- `A[i]` of a unit range, descending range or vector (`BoundsError` outside). -/
def arrGet (len : Nat) (g : Int → V) (i : V) : R V :=
  match i with
  | .int i => if 1 ≤ i ∧ i ≤ len then .ok (g i) else jthrow .boundsError
  | _ => jthrow (.methodError "getindex")

/-- Number of elements of `lo:hi`. -/
def urLen (lo hi : JInt64) : Nat := (hi.val - lo.val + 1).toNat

/-- `first(itr)` (base/abstractarray.jl:474-478) from `iterate(itr)`. -/
def firstOf (y : Step) : R V :=
  y.bind fun
    | some (x, _) => .ok x
    | none => jthrow (.argumentError "collection must be non-empty")

/-- `iterate(A::Reverse, state)` on a state `(r, itrs)`: the index iterator's
`iterate(r, itrs)` is `ix itrs`. -/
def revArrNext (get : V → R V) (ix : V → Step) : V → Step
  | .tup [r, itrs] => revArrCont get r (ix itrs)
  | _ => jthrow (.methodError "iterate")

/-- `Iterators.Reverse(A)` of an array with `n` elements and `A[i] = g i`:
`eltype`, `length`, `size`, `IteratorSize`, `IteratorEltype` of the wrapped
type (base/iterators.jl:128-132), `last(r) = first(r.itr)` (133) and the
`iterate` methods (136-150). -/
def revArrIt (inner : It) (n : Nat) (N : JInt64) (g : Int → V) : It where
  first := revArrCont (arrGet n g) (revIdxObj n) (drFirst N (i64 1))
  next := revArrNext (arrGet n g) (drNext (i64 1))
  isz := inner.isz
  iel := inner.iel
  elt := inner.elt
  len := inner.len
  size := inner.size
  lastv := firstOf inner.first

/-- A number (or character) as an iterator, base/number.jl:329-330. -/
def numIt (v : V) : It :=
  { first := .ok (some (v, .nothing)), next := fun _ => .ok none,
    isz := .hasShape 0, len := .ok (i64 1), size := .ok [], lastv := .ok v }

/-- A pair as an iterator, base/pair.jl:41. -/
def pairIt (a b : V) : It :=
  { first := pairNext a b (.int 1), next := pairNext a b, len := .ok (i64 2), lastv := .ok b }

/-- `lo:hi` as an iterator. -/
def urIt (lo hi : JInt64) : It :=
  { first := urFirst lo hi, next := urNext hi, isz := .hasShape 1, elt := .int,
    len := .ok (hi - lo + i64 1), size := .ok [hi - lo + i64 1], lastv := .ok (.int hi.val) }

/-- `hi:-1:lo` as an iterator. -/
def drIt (hi lo : JInt64) : It :=
  { first := drFirst hi lo, next := drNext lo, isz := .hasShape 1, elt := .int,
    len := .ok (hi - lo + i64 1), size := .ok [hi - lo + i64 1], lastv := .ok (.int lo.val) }

/-- A vector with `last(A) = A[end]`. -/
def vecObjIt (xs : List V) : It :=
  { vecIt .any xs with lastv := match xs.getLast? with
    | some x => .ok x
    | none => jthrow .boundsError }

/-- A tuple with `last(t) = t[end]`. -/
def tupObjIt (xs : List V) : It :=
  { tupIt [] xs with elt := .any, lastv := match xs.getLast? with
    | some x => .ok x
    | none => jthrow .boundsError }

/-- `Iterators.Reverse(t)` of a tuple: the wrapped type's traits, `last(r) =
first(r.itr)` and the tuple `iterate` method (base/iterators.jl:128-133, 162). -/
def revTupIt (xs : List V) : It :=
  let i := tupObjIt xs
  { first := revTupStep xs xs.length, next := revTupNext xs, isz := i.isz, iel := i.iel,
    elt := i.elt, len := i.len, size := i.size, lastv := firstOf i.first }

/-- The iterator of `Iterators.Reverse(o)`: the array methods for arrays, the
tuple method for tuples; any other wrapped object has no `eachindex`. -/
def revItOf : Obj → It
  | .vec xs => revArrIt (vecObjIt xs) xs.length (i64 xs.length) (fun i => getIdx xs i)
  | .urange lo hi => revArrIt (urIt lo hi) (urLen lo hi) (i64 (urLen lo hi)) (fun i => .int (lo.val + i - 1))
  | .drange hi lo => revArrIt (drIt hi lo) (urLen lo hi) (i64 (urLen lo hi)) (fun i => .int (hi.val - i + 1))
  | .tup xs => revTupIt xs
  | _ => { first := jthrow (.methodError "eachindex"), next := fun _ => jthrow (.methodError "iterate") }

/-- The iterator of an object. -/
def Obj.it : Obj → It
  | .num v => numIt v
  | .pair a b => pairIt a b
  | .urange lo hi => urIt lo hi
  | .drange hi lo => drIt hi lo
  | .vec xs => vecObjIt xs
  | .tup xs => tupObjIt xs
  | .rev o => revItOf o
  | .gen f o =>
    let i := o.it
    { first := genCont f i.first, next := fun s => genCont f (i.next s),
      isz := i.isz, iel := false, len := i.len, size := i.size, done0 := i.done0,
      doneS := i.doneS, lastv := i.lastv.map f }

/-- `Iterators.reverse(itr)`, base/iterators.jl:113, 156-160. -/
def itReverse : Obj → Obj
  | .urange lo hi => .drange hi lo        -- 156: Base.reverse(R) is hi:-1:lo
  | .drange hi lo => .urange lo hi        -- 156: Base.reverse(hi:-1:lo) is lo:1:hi
  | .gen f o => .gen f (itReverse o)      -- 157
  | .rev o => o                           -- 158
  | .num v => .num v                      -- 159
  | .pair a b => .pair b a                -- 160: Base.reverse(p::Pair) = p.second => p.first
  | o => .rev o                           -- 113
end JuliaLean.IteratorsCov


/-!
# `Filter`, `Accumulate`, `Rest`, `TakeWhile`, `DropWhile`
(base/iterators.jl:528-739, 895-990)

Predicates are Julia functions returning `Bool` (`V → Bool`); the model's
`fuel` bounds the `while` loops of `Filter` and `DropWhile` (running out is
`E.fuel`, never a Julia result).
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-! ## `Filter` -/

/-- The loop of `iterate(f::Filter, state...)`, base/iterators.jl:578-592:
`while y !== nothing; v, s = y; f.flt(v) && return (v, s); y = iterate(f.itr, s); end`. -/
def filterLoop (p : V → Bool) (nx : V → Step) : Nat → Step → Step
  | _, .ok none => .ok none
  | _, .error e => .error e
  | 0, .ok (some _) => .error .fuel
  | k + 1, .ok (some (v, s)) => if p v then .ok (some (v, s)) else filterLoop p nx k (nx s)

/-- The object `filter(flt, itr) = Filter(flt, itr)` (576) with `iterate`
(578-592), `eltype` and `IteratorEltype` of `I` (594-595) and `IteratorSize`
`SizeUnknown()` (596). -/
def filterIt (fuel : Nat) (p : V → Bool) (it : It) : It where
  first := filterLoop p it.next fuel it.first
  next := fun s => filterLoop p it.next fuel (it.next s)
  isz := .sizeUnknown
  iel := it.iel
  elt := it.elt

/-- `reverse(f::Filter) = Filter(f.flt, reverse(f.itr))` (598) given the
reversed wrapped iterator `rit`, and `last(f::Filter) = first(reverse(f))` (599). -/
def filterLast (fuel : Nat) (p : V → Bool) (rit : It) : R V :=
  (filterIt fuel p rit).first.bind fun
    | some (x, _) => .ok x
    | none => jthrow (.argumentError "collection must be non-empty")

/-! ## `Accumulate` -/

/-- `Base.BottomRF(op)(acc, x)`: `reduce_first(op, x)` (here `rf x`) when there
is no `init` (`acc` is `Base._InitialValue()`), otherwise `op(acc, x)`
(base/reduce.jl:85-90). -/
def bottomRF (op : V → V → V) (rf : V → V) : Option V → V → V
  | none, x => rf x
  | some a, x => op a x

/-- `iterate(itr::Accumulate)`, base/iterators.jl:643-650. -/
def accFirst (op : V → V → V) (rf : V → V) (init : Option V) : Step → Step
  | .ok none => .ok none
  | .ok (some (x, s)) => let v := bottomRF op rf init x; .ok (some (v, .tup [v, s]))
  | .error e => .error e

/-- The tail of `iterate(itr::Accumulate, state)`, base/iterators.jl:652-659,
on `nxt = iterate(itr.itr, state[2])`: `val = itr.f(state[1], nxt[1])`. -/
def accCont (op : V → V → V) (a : V) : Step → Step
  | .ok none => .ok none
  | .ok (some (x, s')) => let v := op a x; .ok (some (v, .tup [v, s']))
  | .error e => .error e

/-- `iterate(itr::Accumulate, state)`, base/iterators.jl:652-659. -/
def accNext (op : V → V → V) (it : It) : V → Step
  | .tup [a, s] => accCont op a (it.next s)
  | _ => jthrow (.methodError "iterate")

/-- `Iterators.accumulate(f, itr; init)` (641) with `iterate` (643-659),
`length` (661), `size` (662), `IteratorSize` of `I` (664) and
`IteratorEltype` `EltypeUnknown()` (665). -/
def accIt (op : V → V → V) (rf : V → V) (init : Option V) (it : It) : It where
  first := accFirst op rf init it.first
  next := accNext op it
  isz := it.isz
  iel := false
  len := it.len
  size := it.size

/-! ## `Rest` -/

/-- An `Iterators.Rest` object: the wrapped iterator and the start state. -/
structure RestObj where
  itr : It
  st : V

/-- `rest(itr, state) = Rest(itr, state)` (696) and `rest(itr::Rest, state) =
Rest(itr.itr, state)` (697): a `Rest` argument is rebased. -/
def mkRest : Sum It RestObj → V → RestObj
  | .inl itr, s => ⟨itr, s⟩
  | .inr r, s => ⟨r.itr, s⟩

/-- `rest(itr) = itr`, base/iterators.jl:698. -/
def rest1 (itr : It) : It := itr

/-- `rest_iteratorsize`, base/iterators.jl:737-738. -/
def restIsz : Isz → Isz
  | .isInfinite => .isInfinite
  | _ => .sizeUnknown

/-- The iterator of a `Rest`: `iterate(i::Rest, st=i.st) = iterate(i.itr, st)`
(732), `eltype`/`IteratorEltype` of `I` (735-736), `IteratorSize` (739). -/
def RestObj.it (r : RestObj) : It where
  first := r.itr.next r.st
  next := r.itr.next
  isz := restIsz r.itr.isz
  iel := r.itr.iel
  elt := r.itr.elt

/-! ## `TakeWhile`, `DropWhile` -/

/-- `iterate(ibl::TakeWhile, itr...)`, base/iterators.jl:930-935. -/
def twCont (p : V → Bool) : Step → Step
  | .ok none => .ok none
  | .ok (some (v, s)) => if p v then .ok (some (v, s)) else .ok none
  | .error e => .error e

/-- `takewhile(pred, xs) = TakeWhile(pred, xs)` (928) with `iterate`
(930-935), `IteratorSize` `SizeUnknown()` (937), `eltype` and
`IteratorEltype` of `I` (938-939). -/
def takeWhileIt (p : V → Bool) (it : It) : It where
  first := twCont p it.first
  next := fun s => twCont p (it.next s)
  isz := .sizeUnknown
  iel := it.iel
  elt := it.elt

/-- The loop of `iterate(ibl::DropWhile)`, base/iterators.jl:979-986. -/
def dwLoop (p : V → Bool) (nx : V → Step) : Nat → Step → Step
  | _, .ok none => .ok none
  | _, .error e => .error e
  | 0, .ok (some _) => .error .fuel
  | k + 1, .ok (some (v, s)) => if p v then dwLoop p nx k (nx s) else .ok (some (v, s))

/-- `dropwhile(pred, itr) = DropWhile(pred, itr)` (976) with
`iterate(ibl, itr) = iterate(ibl.xs, itr)` (978), `iterate(ibl)` (979-986),
`IteratorSize` `SizeUnknown()` (988), `eltype` and `IteratorEltype` (989-990). -/
def dropWhileIt (fuel : Nat) (p : V → Bool) (it : It) : It where
  first := dwLoop p it.next fuel it.first
  next := it.next
  isz := .sizeUnknown
  iel := it.iel
  elt := it.elt
end JuliaLean.IteratorsCov


/-!
# Pair views, searching adapters, cycle/repeated and state-pair adapters

Models for the remaining collection-shaped methods in `base/iterators.jl`.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-! ## `Pairs` -/

structure PairView where
  keys : List V
  values : List V
  deriving Repr

/-- Constructors at lines 281-292 select an index list and retain the data. -/
def pairsLinear (values : List V) : PairView :=
  ⟨(List.range values.length).map (fun i : Nat => .int ((i : Int) + 1)), values⟩

def pairsCartesian (keys values : List V) : PairView := ⟨keys, values⟩
def pairsTuple (values : List V) : PairView := pairsLinear values
def pairsNamedTuple (keys values : List V) : PairView := ⟨keys, values⟩
def pairsSimpleVector (values : List V) : PairView := pairsLinear values
def pairsVector (values : List V) : PairView := pairsLinear values
def pairsArray (keys values : List V) : PairView := pairsCartesian keys values

/-- `_pairs_elt`, lines 298-300. -/
def pairElt (p : PairView) (i : Nat) : R V :=
  match p.keys[i]?, p.values[i]? with
  | some key, some value => .ok (.pair key value)
  | _, _ => jthrow .boundsError

/-- `iterate(::Pairs)`, lines 302-307; the state is the zero-based position
inside the model's key iterator. -/
def pairsIterate (p : PairView) (state : Nat := 0) : R (Option (V × Nat)) :=
  if state < p.keys.length then do
    pure (some (← pairElt p state, state + 1))
  else .ok none

/-- Reverse iteration, lines 309-314. -/
def reversePairsIterate (p : PairView) (state : Nat := p.keys.length) : R (Option (V × Nat)) :=
  if state = 0 then .ok none else do
    pure (some (← pairElt p (state - 1), state - 1))

def pairsLength (p : PairView) : Nat := p.keys.length
def pairsAxes (p : PairView) : List Nat := [p.keys.length]
def pairsSize (p : PairView) : List Nat := [p.keys.length]
def pairsIsdone (p : PairView) (state : Nat) : Bool := p.keys.length ≤ state
def pairsIteratorSize (inner : Isz) : Isz := inner
def pairsTupleIteratorSize : Isz := .hasLength
def pairsHasKey (p : PairView) (key : V) : Bool :=
  p.keys.any (fun k => toString (repr k) == toString (repr key))
def pairsKeys (p : PairView) : List V := p.keys
def pairsValues (p : PairView) : List V := p.values

def pairsGetindex (p : PairView) (i : Nat) : R V :=
  match p.values[i]? with | some value => .ok value | none => jthrow .boundsError

def pairsSetindex (p : PairView) (i : Nat) (value : V) : R PairView :=
  if h : i < p.values.length then
    .ok { p with values := p.values.set i value }
  else jthrow .boundsError

def pairsGet (p : PairView) (i : Nat) (default : V) : V := p.values[i]?.getD default
def pairsGetCall (fallback : Unit → V) (p : PairView) (i : Nat) : V :=
  match p.values[i]? with | some value => value | none => fallback ()

def pairsLast (p : PairView) : R V :=
  if p.keys.isEmpty then jthrow (.argumentError "collection must be non-empty")
  else pairElt p (p.keys.length - 1)

/-! ## `findeach`, `cycle`, `repeated`, `flatmap` -/

/-- `Iterators.map(f, arg, args...) = Generator(f, arg, args...)`, line 56. -/
def iteratorMap (f : List V → V) (its : List It) : It := generatorMany zipIt f its

/-- `findeach(f, it)`, lines 1016-1018, after `pairs(it)` has produced the
key/value list. -/
def findEach (f : V → Bool) (pairs : List (V × V)) : List V :=
  (pairs.filter fun pair => f pair.2).map Prod.fst

def findEachIdentity (pairs : List (V × Bool)) : List V :=
  findEach (fun | .bool b => b | _ => false) (pairs.map fun p => (p.1, .bool p.2))

/-- `Cycle` methods, lines 1058-1075. -/
def cycleIt (it : It) : It where
  first := it.first
  next := fun state => match it.next state with
    | .ok none => it.first
    | result => result
  isz := .isInfinite
  iel := it.iel
  elt := it.elt
  len := it.len
  size := it.size
  done0 := it.done0
  doneS := fun _ => .ok (some false)
  lastv := it.lastv

def cycleN (xs : List V) (n : Nat) : List V := (List.replicate n xs).flatten
def reverseCycle (reverseInner : It) : It := cycleIt reverseInner
def lastCycle (it : It) : R V := it.lastv

/-- `Repeated` methods, lines 1083-1121. -/
def repeatedIt (x : V) : It where
  first := .ok (some (x, .nothing))
  next := fun _ => .ok (some (x, .nothing))
  isz := .isInfinite
  iel := true
  elt := .any
  lastv := .ok x

def repeatedN (x : V) (n : Nat) : List V := List.replicate n x
def reverseRepeated (it : It) : It := it
def lastRepeated (it : It) : R V := firstOf it.first

/-- `flatmap(f, c...) = flatten(map(f, c...))`, line 1421, on finite lists. -/
def flatMapLists (f : List V → List V) (rows : List (List V)) : List V :=
  (rows.map f).flatten

/-! ## `IterableStatePairs` and string `pairs` -/

def iterableStatePairs (keys values : List V) : List V :=
  List.zipWith V.pair keys values

def reverseIterableStatePairs (keys values : List V) : List V :=
  iterableStatePairs keys.reverse values.reverse

/-- String states are string keys, so `pairs(::AbstractString)` has the same
state/value pairing. Characters and their states are supplied in iteration order. -/
def stringPairs (states : List V) (chars : List V) : List V :=
  iterableStatePairs states chars

def iterableStatePairsSize (inner : Isz) : Isz := inner
def iterableStatePairsLength (values : List V) : Nat := values.length
def iterableStatePairsEltype (valueType : Ty) : Ty := .pair .any valueType
end JuliaLean.IteratorsCov


/-!
# `intersect(::ProductIterator, ::ProductIterator)`

The model uses lists for product factors and product elements. Julia's method
at `base/iterators.jl:1257` broadcasts `intersect` over the two factor tuples,
then wraps those factors in `ProductIterator`. Tuple broadcasting repeats a
one-element tuple against a longer tuple.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Set-like intersection of two integer factors, preserving the first
factor's order. -/
def factorIntersect (a b : List Int) : List Int := a.filter b.contains

/-- Julia tuple broadcasting for the binary call `intersect.(as, bs)` used by
`intersect(::ProductIterator, ::ProductIterator)` (`base/iterators.jl:1257`). -/
def broadcastFactorIntersect (as bs : List (List Int)) : R (List (List Int)) :=
  if as.length = bs.length then .ok (List.zipWith factorIntersect as bs)
  else match as, bs with
  | [a], _ => .ok (bs.map (factorIntersect a))
  | _, [b] => .ok (as.map (fun a => factorIntersect a b))
  | _, _ => .error .dimensionMismatch

/-- Elements of a product of factors. The first factor changes fastest in
Julia; reversing the construction order gives that observable ordering. -/
def productElements : List (List Int) → List (List Int)
  | [] => [[]]
  | a :: as => (productElements as).flatMap fun tail => a.map fun x => x :: tail

/-- The body of Julia's method: broadcast the factor intersections and build
the resulting product. -/
def productIntersect (as bs : List (List Int)) : R (List (List Int)) := do
  pure (productElements (← broadcastFactorIntersect as bs))
end JuliaLean.IteratorsCov


/-!
# `Iterators.countfrom` (base/iterators.jl:743-774)

Numbers are `Bool`, `Int64` and `Char` (a non-`Number` with `+(::Char, ::Integer)`).
`Bool + Bool` is an `Int` (base/bool.jl: `+(x::Bool, y::Bool) = Int(x) + Int(y)`),
`Bool + Int` promotes to `Int`, `Int + Int` wraps, and `Char + Int` is the
`Char` with the shifted code point (base/char.jl), which throws for a negative
or too large code point.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Numbers and characters of the model. -/
inductive Num where
  | bool (b : Bool)
  | int (x : JInt64)
  | chr (c : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Their types (`Bool`, `Int64`, `Char`). -/
inductive NTy where
  | bool
  | int
  | chr
  deriving Repr, DecidableEq, Inhabited

def Num.ty : Num → NTy
  | .bool _ => .bool
  | .int _ => .int
  | .chr _ => .chr

/-- `x isa Number`. -/
def Num.isNumber : Num → Bool
  | .chr _ => false
  | _ => true

/-- `Int(x)` of a `Bool`. -/
def boolInt (b : Bool) : JInt64 := if b then i64 1 else i64 0

/-- `x + y`. -/
def numAdd : Num → Num → R Num
  | .bool a, .bool b => .ok (.int (boolInt a + boolInt b))
  | .bool a, .int y => .ok (.int (boolInt a + y))
  | .int x, .bool b => .ok (.int (x + boolInt b))
  | .int x, .int y => .ok (.int (x + y))
  | .chr c, .int y =>
    if 0 ≤ (c : Int) + y.val ∧ (c : Int) + y.val < 0x110000 then .ok (.chr ((c : Int) + y.val).toNat)
    else jthrow (.argumentError "invalid code point")
  | _, _ => jthrow (.methodError "+")

/-- `oneunit(x)`. -/
def oneunit : Num → R Num
  | .bool _ => .ok (.bool true)
  | .int _ => .ok (.int (i64 1))
  | .chr _ => jthrow (.methodError "oneunit")

/-- `convert(T, x)` into the field type `T` of a `Count{T,S}`. -/
def numConvert : NTy → Num → R Num
  | .bool, .bool b => .ok (.bool b)
  | .bool, .int x =>
    if x.val = 0 then .ok (.bool false) else if x.val = 1 then .ok (.bool true)
    else jthrow (.inexactError "Bool")
  | .int, .bool b => .ok (.int (boolInt b))
  | .int, .int x => .ok (.int x)
  | .chr, .chr c => .ok (.chr c)
  | _, _ => jthrow (.methodError "convert")

/-- `promote(x, y)` of two numbers (`Bool` promotes to `Int`). -/
def numPromote : Num → Num → R (Num × Num)
  | .bool a, .int y => .ok (.int (boolInt a), .int y)
  | .int x, .bool b => .ok (.int x, .int (boolInt b))
  | x, y => .ok (x, y)

/-- An `Iterators.Count{T,S}` object: its type parameter `T` and its fields. -/
structure Count where
  T : NTy
  start : Num
  step : Num
  deriving Repr

/-- The default constructor `Count(start, step)`: `T = typeof(start)`. -/
def mkCount (start step : Num) : Count := ⟨start.ty, start, step⟩

/-- The `countfrom` methods, base/iterators.jl:764-767:
`countfrom(start::T, step::S) = Count{typeof(start+step),S}(start, step)` for
non-numbers (764), `countfrom(start::Number, step::Number) =
Count(promote(start, step)...)` (765). -/
def countfrom2 (start step : Num) : R Count :=
  if start.isNumber && step.isNumber then do
    let (a, b) ← numPromote start step
    pure (mkCount a b)
  else do
    let t ← numAdd start step
    let s ← numConvert t.ty start
    pure ⟨t.ty, s, step⟩

/-- `countfrom(start) = Count(start, oneunit(start))`, base/iterators.jl:766. -/
def countfrom1 (start : Num) : R Count := do pure (mkCount start (← oneunit start))

/-- `countfrom() = Count(1, 1)`, base/iterators.jl:767. -/
def countfrom0 : Count := mkCount (.int (i64 1)) (.int (i64 1))

/-- `eltype(::Type{<:Count{T}}) = T`, base/iterators.jl:770. -/
def Count.eltype (c : Count) : NTy := c.T

/-- `iterate(it::Count, state=it.start) = (state, state + it.step)`,
base/iterators.jl:772: the first `k` elements and the state after them. -/
def countRun (c : Count) : Nat → Num → R (List Num)
  | 0, _ => .ok []
  | k + 1, st => do
    let nx ← numAdd st c.step
    pure (st :: (← countRun c k nx))

/-- The first `k` elements of `countfrom(...)`. -/
def countPrefix (c : Count) (k : Nat) : R (List Num) := countRun c k c.start
end JuliaLean.IteratorsCov


/-!
# Method-family equations for product, flatten, partition, Stateful, only and nth

The executable iterator semantics reuse the earlier deep model in
`JuliaLean/base/iterators.lean`; these propositions expose every helper method used
by the owned coverage rows.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean


/-! ## Product -/

def productIelExpected (its : List JuliaLean.Iterators.Itr) : Bool :=
  match its with
  | [] => true
  | [it] => JuliaLean.Iterators.ieltype it
  | _ => JuliaLean.Iterators.ieltypeAll its

def productAxes (sizes : List (List JInt64)) : List (List JInt64) := sizes
def productNdims (axes : List (List JInt64)) : Nat := axes.flatten.length

/-! ## Flatten -/

def flattenLengthModel (it : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.M JInt64 :=
  match JuliaLean.Iterators.eltype it with
  | .bottom => .ok (JuliaLean.Iterators.i64 0)
  | .tuple ts => do JuliaLean.Iterators.checkedMul64 (JuliaLean.Iterators.i64 ts.length) (← JuliaLean.Iterators.len it)
  | .int => JuliaLean.Iterators.len it
  | _ => JuliaLean.Iterators.jthrow (.argumentError "Iterates of the argument to Flatten are not known to have constant length")

def flattenLastModel (fuel : Nat) (it : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.M JuliaLean.Iterators.Val := do
  JuliaLean.Iterators.first fuel (← JuliaLean.Iterators.reverse (.flatten it))

/-! ## Partition -/

def partitionEltype (c : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.Ty := .vector (JuliaLean.Iterators.eltype c)

/-! ## Stateful and type approximation -/

inductive ApproxType where
  | bottom | valueState | maybeValueState | other
  deriving Repr, DecidableEq

/-- `_approx_iter_type`, lines 1597-1603. -/
def approxIterType (iteratorBottom : Bool) (current next : ApproxType) : ApproxType :=
  if current = .other then .other
  else if current = .bottom || iteratorBottom then .bottom
  else if next = current then current else .other

def resetStateful (et : JuliaLean.Iterators.Ty) (xs : List JuliaLean.Iterators.Val) : JuliaLean.Iterators.Itr := .stateful et xs 0
def resetStatefulTo (et : JuliaLean.Iterators.Ty) (xs : List JuliaLean.Iterators.Val) : JuliaLean.Iterators.Itr := .stateful et xs 0
def statefulIdentity (x : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.Itr := x
def statefulConvert (x : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.Itr := x

/-! ## only and nth adapters -/

def onlyFirst (length : Nat) (first : JuliaLean.Iterators.M JuliaLean.Iterators.Val) : JuliaLean.Iterators.M JuliaLean.Iterators.Val :=
  if length = 1 then first
  else JuliaLean.Iterators.jthrow (.argumentError "Collection must contain exactly 1 element")

def nthFix (fuel : Nat) (type : IntTy) (n : Int) (it : JuliaLean.Iterators.Itr) : JuliaLean.Iterators.M JuliaLean.Iterators.Val :=
  JuliaLean.Iterators.nth fuel it type n
end JuliaLean.IteratorsCov
