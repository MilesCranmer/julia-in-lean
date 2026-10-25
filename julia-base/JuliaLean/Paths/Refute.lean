import JuliaLean.Paths.Props

/-!
# Refuted path properties
-/

namespace JuliaLean.Paths

/-- `splitext(".bashrc") == (".bashrc", "")`. -/
theorem splitext_dotfile : splitext ['.', 'b', 'a', 's', 'h', 'r', 'c'] = (['.', 'b', 'a', 's', 'h', 'r', 'c'], []) := by
  decide

theorem splitextDoc_refuted : ¬ SplitextDoc := by
  intro h
  have := h [] ['b', 'a', 's', 'h', 'r', 'c'] (by decide)
  rw [List.nil_append, splitext_dotfile] at this
  cases this

end JuliaLean.Paths
