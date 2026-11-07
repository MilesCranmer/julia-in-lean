import JuliaLean.base.runtime_internals
import JuliaLean.Core


section
namespace JuliaLean.RuntimeCov

theorem uvError_ok_iff (err : Int) : uvError err = .ok () ↔ 0 ≤ err := by
  unfold uvError; split <;> simp_all <;> omega
end JuliaLean.RuntimeCov
end

/-!
Bounds-obligation models for group 4. Each property calls a small program
that performs the Julia entry checks and computes the index used at the site.
No property accepts an in-bounds index as a hypothesis.
-/

namespace JuliaLean.MemSafety.G4

/-- One-based array bounds. -/
def InBounds (len : Nat) (i : Int) : Prop := 1 ≤ i ∧ i ≤ len

structure ByteSpan where
  objectBytes : Nat
  offset : Nat
  readBytes : Nat

def ByteSpan.safe (a : ByteSpan) : Prop := a.offset + a.readBytes ≤ a.objectBytes

end JuliaLean.MemSafety.G4
