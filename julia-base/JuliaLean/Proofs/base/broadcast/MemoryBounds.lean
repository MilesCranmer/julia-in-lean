import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

/-- `copyto!` first checks equal axes, then `eachindex(bc)` returns an element
of those axes, `base/broadcast.jl:1015-1029`. -/
def broadcastEachindex (axes : List α) (k : Nat) : Option α := axes[k]?

def BroadcastEachindexInBounds : Prop :=
  ∀ (α : Type) (axes : List α) (k : Nat) (i : α), broadcastEachindex axes k = some i → i ∈ axes

/-- BitArray broadcast increments `indc` once per complete 64-bit output and
writes the optional remainder at the next chunk. -/
def broadcastChunkIndex (logicalLen k : Nat) : Option Int :=
  let chunks := (logicalLen + 63) / 64
  if k < chunks then some (k + 1) else none

def BroadcastChunkInBounds : Prop :=
  ∀ (logicalLen k : Nat) (i : Int), broadcastChunkIndex logicalLen k = some i →
    InBounds ((logicalLen + 63) / 64) i


theorem broadcastEachindexInBounds : BroadcastEachindexInBounds := by
  intro α axes k i h
  have hk : k < axes.length := List.getElem?_eq_some_iff.mp h |>.1
  have hi : axes[k] = i := by simpa [broadcastEachindex, List.getElem?_eq_getElem hk] using h
  rw [← hi]
  exact List.getElem_mem hk

theorem broadcastChunkInBounds : BroadcastChunkInBounds := by
  intro logicalLen k i h
  dsimp [broadcastChunkIndex] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

end JuliaLean.MemSafety.G4
