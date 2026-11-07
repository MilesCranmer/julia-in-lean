import JuliaLean.Proofs.base.array.common


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-! ## GenericMemory checked callers -/

inductive MemorySide where
  | source
  | destination
  deriving DecidableEq, Repr

structure MemoryAccess where
  side : MemorySide
  index : Int
  deriving DecidableEq, Repr

/-- `isassigned(a, i)` at `base/genericmemory.jl:189-192`: the access occurs only after
`checkbounds(Bool, a, i)` succeeds. -/
def isassignedAccess (len : Nat) (i : Int) : List MemoryAccess :=
  match checkedIndex len i with
  | some j => [⟨.source, j⟩]
  | none => []

/-- `copy(a::Memory)` at `base/genericmemory.jl:257-262`: both memories have `length(a)` and
the unsafe copy starts at one for exactly that many elements. -/
def copyMemoryAccesses (len : Nat) : List MemoryAccess :=
  (span 1 len).map (⟨.source, ·⟩) ++ (span 1 len).map (⟨.destination, ·⟩)

/-- Range assignment at `base/genericmemory.jl:346-353`. `checkbounds(A, I)` checks the
destination span and `setindex_shape_check(X, length(I))` checks the source length before the
nonempty branch calls `unsafe_copyto!`. -/
def setRangeAccesses (destLen srcLen first count : Nat) : List MemoryAccess :=
  if count = 0 then []
  else if first ≥ 1 ∧ first + count ≤ destLen + 1 ∧ srcLen = count then
    (span first count).map (⟨.destination, ·⟩) ++
      (span 1 count).map (⟨.source, ·⟩)
  else []

/-- Colon assignment at `base/genericmemory.jl:356-362`: the shape check requires
`length(X) == length(A)` and the nonempty branch copies that exact length. -/
def setColonAccesses (destLen srcLen : Nat) : List MemoryAccess :=
  if destLen = 0 then []
  else if srcLen = destLen then
    (span 1 destLen).map (⟨.destination, ·⟩) ++
      (span 1 destLen).map (⟨.source, ·⟩)
  else []

def accessInMemory (srcLen destLen : Nat) (a : MemoryAccess) : Prop :=
  match a.side with
  | .source => inBounds srcLen a.index
  | .destination => inBounds destLen a.index

def GenericMemoryCheckedAccessesInBounds : Prop :=
  (∀ len i a, a ∈ isassignedAccess len i → accessInMemory len 0 a) ∧
  (∀ len a, a ∈ copyMemoryAccesses len → accessInMemory len len a) ∧
  (∀ dl sl first count a, a ∈ setRangeAccesses dl sl first count →
    accessInMemory sl dl a) ∧
  (∀ dl sl a, a ∈ setColonAccesses dl sl → accessInMemory sl dl a)

theorem genericMemoryCheckedAccessesInBounds_proven :
    GenericMemoryCheckedAccessesInBounds := by
  constructor
  · intro len i a h
    unfold isassignedAccess at h
    unfold checkedIndex at h
    split at h <;> simp_all [accessInMemory, inBounds] <;> omega
  constructor
  · intro len a h
    unfold copyMemoryAccesses at h
    rw [List.mem_append] at h
    rcases h with h | h <;> rw [List.mem_map] at h <;>
      obtain ⟨i, hi, rfl⟩ := h <;> obtain ⟨k, hk, rfl⟩ := mem_span hi <;>
      simp [accessInMemory, inBounds] <;> omega
  constructor
  · intro dl sl first count a h
    unfold setRangeAccesses at h
    split at h
    · simp_all
    split at h
    · rename_i hv
      rw [List.mem_append] at h
      rcases h with h | h <;> rw [List.mem_map] at h <;>
        obtain ⟨i, hi, rfl⟩ := h <;> obtain ⟨k, hk, rfl⟩ := mem_span hi <;>
        simp [accessInMemory, inBounds] <;> omega
    · simp_all
  · intro dl sl a h
    unfold setColonAccesses at h
    split at h
    · simp_all
    split at h
    · rename_i heq
      rw [List.mem_append] at h
      rcases h with h | h <;> rw [List.mem_map] at h <;>
        obtain ⟨i, hi, rfl⟩ := h <;> obtain ⟨k, hk, rfl⟩ := mem_span hi <;>
        simp [accessInMemory, inBounds] <;> omega
    · simp_all
end JuliaLean.MemSafety.G6
end
