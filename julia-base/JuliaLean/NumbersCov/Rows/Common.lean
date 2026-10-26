import JuliaLean.NumbersCov.Model

namespace JuliaLean.NumbersCov.Rows

/-- A total Julia method returns its source-selected value or exception for
every allowed input. This is useful only when the function argument itself is
the row-specific, source-shaped model. -/
def HasResult {α : Type} (x : α) : Prop := ∃ y, x = y

theorem hasResult {α : Type} (x : α) : HasResult x := ⟨x, rfl⟩

end JuliaLean.NumbersCov.Rows
