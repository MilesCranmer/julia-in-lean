import JuliaLean.Core
import JuliaLean.base.indices

/-!
Source-level bounds models for the unchecked accesses in
`memsafety/sites-2.tsv`, against Julia master `bbfa0ce4150`.

Every trace below starts from the enclosing Julia function's arguments and
executes the checks, branches, loop bounds, and index arithmetic that lead to
the attributed access. An `Access` records the one-based index and the length
of the storage selected by that source path.
-/
namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
structure Access where
  len : Nat
  index : Int
  deriving DecidableEq, Repr

def Access.inBounds (a : Access) : Prop := 1 ≤ a.index ∧ a.index ≤ a.len

def AllInBounds (xs : List Access) : Prop := ∀ a ∈ xs, a.inBounds

def oneBased (n : Nat) : List Int :=
  (List.range n).map fun (k : Nat) => (k : Int) + 1

def axisValues (a : Axis) : List Int :=
  (List.range a.len).map fun (k : Nat) => a.first.val + k

def product (ns : List Nat) : Nat := ns.foldr (· * ·) 1





theorem oneBased_mem {n : Nat} {i : Int} (h : i ∈ oneBased n) :
    1 ≤ i ∧ i ≤ n := by
  simp [oneBased] at h
  omega

theorem mappedOneBased (n : Nat) :
    AllInBounds ((oneBased n).map fun i => Access.mk n i) := by
  intro a ha
  simp only [List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact oneBased_mem hi

end JuliaLean.MemSafety.G2
