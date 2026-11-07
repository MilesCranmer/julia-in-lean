import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- A HAMT bitmap split at the hash-selected bit. The fields are the three
results of that split; `entry_index` counts the set bits before it,
`base/hamt.jl:119-140,158-215`. -/
structure HamtSplit where
  before : Nat
  present : Bool
  after : Nat

def HamtSplit.dataLen (s : HamtSplit) : Nat :=
  s.before + (if s.present then 1 else 0) + s.after

def HamtSplit.entryIndex (s : HamtSplit) : Int := s.before + 1

def hamtDataAccess (s : HamtSplit) : Option (Nat × Int) :=
  if s.present then some (s.dataLen, s.entryIndex) else none

def HamtSlotInBounds : Prop :=
  ∀ (s : HamtSplit) (len : Nat) (i : Int), hamtDataAccess s = some (len, i) → InBounds len i


theorem hamtSlotInBounds : HamtSlotInBounds := by
  intro s len i h
  unfold hamtDataAccess at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    unfold HamtSplit.dataLen HamtSplit.entryIndex InBounds at *
    simp_all
    omega
  · contradiction

end JuliaLean.MemSafety.G4
