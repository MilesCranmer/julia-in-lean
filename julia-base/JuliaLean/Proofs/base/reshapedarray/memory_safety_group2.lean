import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/reshapedarray.jl:270-339` -/

def reshapedLinearAccess (parent : Axis) (reshapeLength : Nat) (i : Int) : List Access :=
  if 1 ≤ i && i ≤ reshapeLength && reshapeLength = parent.len then
    let parentIndex := i - 1 + parent.first.val
    [⟨parent.len, parentIndex - parent.first.val + 1⟩]
  else []

def reshapedIndexAccess (parentLength : Nat) (parentIndex : Int) : List Access :=
  if 1 ≤ parentIndex && parentIndex ≤ parentLength then [⟨parentLength, parentIndex⟩] else []

def ReshapedIndexingInBounds : Prop :=
  (∀ parent reshapeLength i, AllInBounds (reshapedLinearAccess parent reshapeLength i)) ∧
  (∀ parentLength parentIndex, AllInBounds (reshapedIndexAccess parentLength parentIndex))





private theorem reshapedLinearInBounds : ∀ parent reshapeLength i,
    AllInBounds (reshapedLinearAccess parent reshapeLength i) := by
  intro parent reshapeLength i access ha
  simp only [reshapedLinearAccess] at ha
  split at ha
  · simp only [List.mem_singleton] at ha
    subst access
    simp only [Access.inBounds]
    simp_all
    omega
  · simp at ha

theorem reshapedIndexingInBounds : ReshapedIndexingInBounds := by
  refine ⟨reshapedLinearInBounds, ?_⟩
  intro parentLength parentIndex access ha
  simp only [reshapedIndexAccess] at ha
  split at ha
  · simp only [List.mem_singleton] at ha
    subst access
    simp_all [Access.inBounds]
  · simp at ha

end JuliaLean.MemSafety.G2
