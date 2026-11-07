import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- `fieldname` checks both sides before reading `_fieldnames(t)[i]`, and
`DataTypeFieldDesc.getindex` performs the same check,
`base/runtime_internals.jl:391-405,797-812`. -/
def runtimeFieldIndex (n : Nat) (i : Int) : Option Int :=
  if i > n then none else if i < 1 then none else some i

def RuntimeFieldInBounds : Prop :=
  ∀ (n : Nat) (i j : Int), runtimeFieldIndex n i = some j → InBounds n j

/-- `isconst` and `isfieldatomic` reject fields outside `1:n`, subtract one,
then load word `1+s÷32`, `base/runtime_internals.jl:544-578`. -/
def runtimeBitfieldIndex (n : Nat) (s : Int) : Option Int :=
  if 1 ≤ s ∧ s ≤ n then some (1 + (s - 1) / 32) else none

def RuntimeBitfieldInBounds : Prop :=
  ∀ (n : Nat) (s i : Int), runtimeBitfieldIndex n s = some i →
    InBounds ((n + 31) / 32) i

/-- Runtime-owned pointers at these sites point to one complete object: a
`DataTypeLayout`, a checked field descriptor, or the `UInt` global itself. -/
def runtimeMetadataIndex (objects : Nat) (i : Int) : Option Int :=
  if 1 ≤ i ∧ i ≤ objects then some i else none

def RuntimeMetadataInBounds : Prop :=
  ∀ (objects : Nat) (i j : Int), runtimeMetadataIndex objects i = some j → InBounds objects j

inductive RuntimeMetadataSite where
  | dataTypeLayout
  | fieldLayout
  | requireWorld

/-- Each runtime pointer is at offset zero of one complete runtime-owned
object of the loaded type. Null layout pointers are rejected before these
loads; `cglobal` returns the address of the complete UInt global. -/
def runtimeMetadataAccess : RuntimeMetadataSite → ByteSpan
  | .dataTypeLayout => ⟨1, 0, 1⟩
  | .fieldLayout => ⟨1, 0, 1⟩
  | .requireWorld => ⟨1, 0, 1⟩

def RuntimeMetadataAccessesInBounds : Prop :=
  ∀ site : RuntimeMetadataSite, (runtimeMetadataAccess site).safe


theorem runtimeFieldInBounds : RuntimeFieldInBounds := by
  intro n i j h
  unfold runtimeFieldIndex at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Option.some.injEq] at h
  subst j
  unfold InBounds
  omega

theorem runtimeBitfieldInBounds : RuntimeBitfieldInBounds := by
  intro n s i h
  unfold runtimeBitfieldIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem runtimeMetadataInBounds : RuntimeMetadataInBounds := by
  intro objects i j h
  unfold runtimeMetadataIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst j
    exact ‹1 ≤ i ∧ i ≤ ↑objects›
  · contradiction

theorem runtimeMetadataAccessesInBounds : RuntimeMetadataAccessesInBounds := by
  intro site
  cases site <;> simp [runtimeMetadataAccess, ByteSpan.safe]

end JuliaLean.MemSafety.G4
