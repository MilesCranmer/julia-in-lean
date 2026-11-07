import JuliaLean.base.idset

namespace JuliaLean.BitSetsCov.Coll

open Bugs

def IdSetBasicSpec : Prop :=
  idEmpty = [] ∧ (∀ s, idCopy s = s) ∧ (∀ xs, idOfList xs = xs.foldl idPush []) ∧
  (∀ s x, idHasKey s x = decide (idFind x.identity s).isSome) ∧
  (∀ s, idIsEmpty s = s.isEmpty)

def IdSetPopSpec : Prop :=
  (∀ s x, idPopInternal s x = if idHasKey s x then (0, idErase x.identity s) else (-1, s)) ∧
  (∀ s x, idPopKey s x = if idHasKey s x then some (x, idErase x.identity s) else none) ∧
  (∀ s x d, idPopDefault s x d = if idHasKey s x then (x, idErase x.identity s) else (d, s))

def IdSetMemorySpec : Prop :=
  (∀ a, idZero a = List.replicate a.length 0) ∧
  (∀ f s, idFilter f s = s.filter f)

theorem idSetBasicSpec : IdSetBasicSpec := by simp [IdSetBasicSpec, idEmpty, idCopy, idOfList, idHasKey, idIsEmpty]
theorem idSetPopSpec : IdSetPopSpec := by simp [IdSetPopSpec, idPopInternal, idPopKey, idPopDefault]
theorem idSetMemorySpec : IdSetMemorySpec := by simp [IdSetMemorySpec, idZero, idFilter]
end JuliaLean.BitSetsCov.Coll
