import JuliaLean.base.set

namespace JuliaLean.BitSetsCov

namespace Bugs

def replaceExpected (f : Nat → Nat) (source : List Nat) : List Nat :=
  setOf (source.map f)

/-- `replace(f, s)` must replace every original member simultaneously. -/
def ReplaceGenericSetSpec : Prop :=
  ∀ (f : Nat → Nat) (source : List Nat), source.Nodup →
    setOf (replaceSeparate f source source) = setOf (replaceExpected f source)

theorem replaceGenericSetSpec_refuted : ¬ ReplaceGenericSetSpec := by
  intro h
  have := h (fun x => x + 1) [1, 2] (by decide)
  simp [replaceSeparate, replaceExpected, setOf, insertUnique] at this

def AlluniqueSetSpec : Prop :=
  ∀ xs : List IdValue, (xs.map IdValue.identity).Nodup →
    (alluniqueIdSet xs = true ↔ (xs.map IdValue.value).Nodup)

theorem alluniqueSetSpec_refuted : ¬ AlluniqueSetSpec := by
  intro h
  have := h [⟨1, 7⟩, ⟨2, 7⟩] (by decide)
  simp [alluniqueIdSet] at this

def ReplaceSetSingletonSpec : Prop := ∀ hasUnreplacedValue, replaceSetSingleton hasUnreplacedValue = .ok

theorem replaceSetSingletonSpec_refuted : ¬ ReplaceSetSingletonSpec := by
  intro h
  have := h true
  simp [replaceSetSingleton] at this
end Bugs

abbrev ReplaceGenericSetSpec := Bugs.ReplaceGenericSetSpec
abbrev AlluniqueSetSpec := Bugs.AlluniqueSetSpec
abbrev ReplaceSetSingletonSpec := Bugs.ReplaceSetSingletonSpec

theorem replaceGenericSetSpec_refuted : ¬ ReplaceGenericSetSpec := Bugs.replaceGenericSetSpec_refuted
theorem alluniqueSetSpec_refuted : ¬ AlluniqueSetSpec := Bugs.alluniqueSetSpec_refuted
theorem replaceSetSingletonSpec_refuted : ¬ ReplaceSetSingletonSpec := Bugs.replaceSetSingletonSpec_refuted
end JuliaLean.BitSetsCov
