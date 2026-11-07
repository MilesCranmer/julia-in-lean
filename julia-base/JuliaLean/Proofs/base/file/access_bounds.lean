import JuliaLean.Proofs.base.array.common


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-! ## Runtime-owned pointer objects -/

/-- The success result of `uv_fs_statfs` is one complete `uv_statfs_t`, which `DiskStat`
mirrors field for field (`base/file.jl:1662-1713`). The branch on the return code is included:
an error performs no load and success loads object zero. -/
def diskstatLoad (uvSucceeded : Bool) : Option (Nat × Nat) :=
  if uvSucceeded then some (0, 1) else none

def DiskstatPointerLoadInBounds : Prop :=
  ∀ ok offset objects, diskstatLoad ok = some (offset, objects) → offset < objects

theorem diskstatPointerLoadInBounds_proven : DiskstatPointerLoadInBounds := by
  intro ok offset objects h
  unfold diskstatLoad at h
  split at h <;> simp_all <;> omega
end JuliaLean.MemSafety.G6
end
