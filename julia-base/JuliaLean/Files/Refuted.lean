import JuliaLean.Files.Props

namespace JuliaLean.Files

theorem cpForceReplaces_refuted : ¬CpForceReplaces := by
  intro h
  have counterexample := h Destination.danglingLink
  simp [cp, Destination.isPath] at counterexample

theorem rmSymlinkSafe_refuted : ¬RmSymlinkSafe := by
  intro h
  have counterexample := h 1
  simp [rm, targetChildrenAfter] at counterexample

theorem tempnameUnused_refuted : ¬TempnameUnused := by
  intro h
  let parent : TempParent := { text := [], shape := .relative, isDir := true }
  let candidate : TempCandidate := { random := [], isPath := false, isLink := true }
  have counterexample := h parent candidate [] false (by rfl) (by rfl)
  simp [tempname, chooseTemp, parent, candidate] at counterexample

end JuliaLean.Files
