import JuliaLean.base.iterators
import JuliaLean.Proofs.base.generator.coverage
import JuliaLean.Proofs.base.iterators.coverage_reverse

/-!
# Pair views, searching adapters, cycle/repeated and state-pair adapters

Models for the remaining collection-shaped methods in `base/iterators.jl`.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

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

def CycleRepeatedSemantics : Prop :=
  (∀ f its, iteratorMap f its = generatorMany zipIt f its) ∧
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
