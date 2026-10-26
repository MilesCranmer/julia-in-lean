import JuliaLean.IteratorsCov.Generator
import JuliaLean.IteratorsCov.Reverse

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

/-- `Pairs` exposes the chosen keys and corresponding values in order; its
length/axes/size and lookup methods delegate to those fields, mutation returns
the same view with one value replaced, and reverse iteration reverses the pairs. -/
def PairsSemantics : Prop :=
  (∀ values, (pairsLinear values).values = values ∧
    (pairsLinear values).keys.length = values.length) ∧
  (∀ keys values, (pairsCartesian keys values).keys = keys ∧
    (pairsCartesian keys values).values = values) ∧
  (∀ p, pairsLength p = p.keys.length ∧ pairsAxes p = [p.keys.length] ∧
    pairsSize p = [p.keys.length] ∧ pairsKeys p = p.keys ∧ pairsValues p = p.values) ∧
  (∀ p i key value, p.keys[i]? = some key → p.values[i]? = some value →
    pairElt p i = .ok (.pair key value)) ∧
  (∀ p i value, p.values[i]? = some value → pairsGetindex p i = .ok value) ∧
  (∀ p i value, i < p.values.length →
    pairsSetindex p i value = .ok { p with values := p.values.set i value }) ∧
  (∀ p i d, pairsGet p i d = p.values[i]?.getD d) ∧
  (∀ p i f, pairsGetCall f p i = match p.values[i]? with
    | some value => value | none => f ()) ∧
  (∀ p state, pairsIsdone p state = decide (p.keys.length ≤ state)) ∧
  (∀ size, pairsIteratorSize size = size) ∧
  (pairsTupleIteratorSize = .hasLength) ∧
  (∀ p state, pairsIterate p state =
    if state < p.keys.length then do pure (some (← pairElt p state, state + 1)) else .ok none) ∧
  (∀ p state, reversePairsIterate p state =
    if state = 0 then .ok none else do pure (some (← pairElt p (state - 1), state - 1))) ∧
  (∀ p key, pairsHasKey p key =
    p.keys.any (fun k => toString (repr k) == toString (repr key))) ∧
  (∀ p, pairsLast p = if p.keys.isEmpty then
    jthrow (.argumentError "collection must be non-empty") else pairElt p (p.keys.length - 1))

theorem pairsSemantics : PairsSemantics := by
  refine ⟨fun values => ⟨rfl, by simp [pairsLinear]⟩, fun _ _ => ⟨rfl, rfl⟩,
    fun p => ⟨rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ => rfl, fun _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ => rfl⟩
  · intro p i key value hk hv
    simp [pairElt, hk, hv]
  · intro p i value h
    simp [pairsGetindex, h]
  · intro p i value h
    simp [pairsSetindex, h]

/-! ## `findeach`, `cycle`, `repeated`, `flatmap` -/

/-- `Iterators.map(f, arg, args...) = Generator(f, arg, args...)`, line 56. -/
def iteratorMap (f : List V → V) (its : List It) : It := generatorMany f its

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

def CycleRepeatedSemantics : Prop :=
  (∀ f its, iteratorMap f its = generatorMany f its) ∧
  (∀ f ps, findEach f ps = (ps.filter fun p => f p.2).map Prod.fst) ∧
  (∀ ps, findEachIdentity ps =
    findEach (fun | .bool b => b | _ => false) (ps.map fun p => (p.1, .bool p.2))) ∧
  (∀ xs n, cycleN xs n = (List.replicate n xs).flatten) ∧
  (∀ it, (cycleIt it).first = it.first ∧ (cycleIt it).isz = .isInfinite ∧
    (cycleIt it).iel = it.iel ∧ (cycleIt it).elt = it.elt ∧
    ((cycleIt it).doneS = fun _ => .ok (some false)) ∧ lastCycle it = it.lastv ∧
    (∀ state, (cycleIt it).next state = match it.next state with
      | .ok none => it.first | result => result)) ∧
  (∀ it, reverseCycle it = cycleIt it) ∧
  (∀ x n, repeatedN x n = List.replicate n x) ∧
  (∀ x, (repeatedIt x).first = .ok (some (x, .nothing)) ∧
    (repeatedIt x).next .nothing = .ok (some (x, .nothing)) ∧
    (repeatedIt x).isz = .isInfinite ∧ (repeatedIt x).iel = true) ∧
  (∀ it, reverseRepeated it = it ∧ lastRepeated it = firstOf it.first) ∧
  (∀ f rows, flatMapLists f rows = (rows.map f).flatten)

theorem cycleRepeatedSemantics : CycleRepeatedSemantics := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, ?_,
    fun _ => rfl, fun _ _ => rfl, ?_, fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩
  · intro it; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · intro x; exact ⟨rfl, rfl, rfl, rfl⟩

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

def IterableStatePairsSemantics : Prop :=
  (∀ keys values, iterableStatePairs keys values = List.zipWith V.pair keys values) ∧
  (∀ keys values, reverseIterableStatePairs keys values =
    List.zipWith V.pair keys.reverse values.reverse) ∧
  (∀ states chars, stringPairs states chars = List.zipWith V.pair states chars) ∧
  (∀ keys values, (iterableStatePairs keys values).length = min keys.length values.length) ∧
  (∀ inner, iterableStatePairsSize inner = inner) ∧
  (∀ values, iterableStatePairsLength values = values.length) ∧
  (∀ t, iterableStatePairsEltype t = .pair .any t)

theorem iterableStatePairsSemantics : IterableStatePairsSemantics := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_,
    fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  intro keys values
  simp [iterableStatePairs]

end JuliaLean.IteratorsCov
