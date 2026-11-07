import JuliaLean.base.iddict

namespace JuliaLean.IdDicts
theorem egal_iff (a b : JVal) : egal a b = true ↔ a = b := by
  simp [egal]

theorem convert_isa {T : JTy} {x w : JVal} (h : convert T x = .ok w) : isa w T = true := by
  unfold convert at h
  split at h
  · cases h; assumption
  · split at h <;> first | (cases h; rfl) | cases h

end JuliaLean.IdDicts
