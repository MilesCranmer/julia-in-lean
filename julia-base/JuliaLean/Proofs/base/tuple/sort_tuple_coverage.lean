import JuliaLean.base.tuple
import JuliaLean.Proofs.base.tuple.sort_tuple_correct
/-! Faithful models for the remaining type and construction methods in
`base/tuple.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

def TupleTypeMethodsCorrect : Prop :=
  (∀ n, countTupleSpecific (.tuple [.vararg .any (some n)]) = some n) ∧
  (∀ t, countTupleFallback t = none) ∧
  (∀ join free, tupleEltype join free (fun _ => false) (.tuple []) = .bottom) ∧
  (∀ join free a b, computeTupleEltype join free (.union a b) =
    if free (.union a b) then .any
    else join a b) ∧
  (∀ ts, tupleKeytypeValue ts = .atom "Int64") ∧
  (∀ t, tupleKeytypeType t = .atom "Int64") ∧
  (∀ join ts, tupleValtypeValue join ts =
    computeTupleEltype join (fun _ => false) (.tuple (ts.map .type))) ∧
  (∀ join t, tupleValtypeType join t = computeTupleEltype join (fun _ => false) t) ∧
  (∀ t n, tupleTypeTail (.tuple [.vararg t (some n)]) =
    .ok (.tuple [.vararg t (some (n - 1))])) ∧
  (∀ t ps, tupleTypeTail (.tuple (.type t :: ps)) = .ok (.tuple ps)) ∧
  (∀ a b, tupleTypeTail (.union a b) = do
    pure (.union (← tupleTypeTail a) (← tupleTypeTail b)))

theorem tupleTypeMethodsCorrect : TupleTypeMethodsCorrect := by
  refine ⟨by simp [countTupleSpecific], by simp [countTupleFallback], by simp [tupleEltype], ?_,
    by simp [tupleKeytypeValue], by simp [tupleKeytypeType], by simp [tupleValtypeValue],
    by simp [tupleValtypeType], by simp [tupleTypeTail], by simp [tupleTypeTail], ?_⟩
  intro join free a b
  simp [computeTupleEltype]
  intro a b
  rfl

def TupleConstructionCorrect : Prop :=
  (∀ (V : Type) (isT : List V → Bool) convert x,
    isT x = true → tupleTypeCall isT convert x = .ok x) ∧
  (∀ (V : Type) (x : V), tupleRef x = [x] ∧ tupleArray0 x = [x]) ∧
  (∀ (V : Type), (toTupleError : Jl (List V)) =
    .error (.argumentError "too few elements for tuple type")) ∧
  (∀ (V : Type) hasType convert xs,
    toTupleFixed (V := V) hasType convert [] xs = .ok []) ∧
  (∀ (V : Type) convert xs, toTupleVararg (V := V) convert xs = xs.mapM convert) ∧
  (∀ (V : Type) (xs : List V), toTupleAny xs = xs) ∧
  (∀ (V : Type) (a b : V), toTupleFast (.pair a b) = [a, b]) ∧
  (∀ (V : Type) (x : V), toTupleFast (.number x) = [x])

theorem tupleConstructionCorrect : TupleConstructionCorrect := by
  refine ⟨?_, by simp [tupleRef, tupleArray0], by simp [toTupleError], by simp [toTupleFixed],
    by simp [toTupleVararg], by simp [toTupleAny], by simp [toTupleFast], by simp [toTupleFast]⟩
  intro V isT convert x h
  simp [tupleTypeCall, h]

end JuliaLean.SortTuplesCov
