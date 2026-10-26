import JuliaLean.RuntimeCov.Modules

namespace JuliaLean.RuntimeCov.RuntimeInternalsCoverage

open JuliaLean.RuntimeCov
open JuliaLean.RuntimeCov.Modules

/-- `isconst(m::Module, s::Symbol)`, base/runtime_internals.jl:522-523. -/
def isconstModule (runtime : Mod → Sym → Int) (m : Mod) (s : Sym) : Bool :=
  runtime m s != 0

/-- `isconst(g::GlobalRef)`, base/runtime_internals.jl:525-527. -/
def isconstGlobalRef (runtime : GlobalRef → Int) (g : GlobalRef) : Bool :=
  runtime g != 0

def IsconstGlobalBodies : Prop :=
  (∀ runtime m s, isconstModule runtime m s = true ↔ runtime m s != 0) ∧
  (∀ runtime g, isconstGlobalRef runtime g = true ↔ runtime g != 0)

theorem isconstGlobalBodies_proven : IsconstGlobalBodies := by
  refine ⟨?_, ?_⟩ <;> intros <;> simp [isconstModule, isconstGlobalRef]

end JuliaLean.RuntimeCov.RuntimeInternalsCoverage
