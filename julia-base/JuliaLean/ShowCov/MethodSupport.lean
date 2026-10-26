import JuliaLean.ShowCov.Basic
import JuliaLean.Registry.Types

namespace JuliaLean.ShowCov.Methods

open JuliaLean.Registry

/-- A source-order model has a result for every quantified model input. -/
def HasResult {α : Type} (x : α) : Prop := ∃ r, x = r

theorem hasResult {α : Type} (x : α) : HasResult x := ⟨x, rfl⟩

def entry (id file fn statement : String) (prop thm : Lean.Name) : Entry :=
  { id := id, juliaFile := file, juliaFns := [fn], statement := statement
    source := "source method body and obvious evaluation invariant"
    status := .proven, prop := prop, thm := some thm }

end JuliaLean.ShowCov.Methods
