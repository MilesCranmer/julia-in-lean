import JuliaLean.Proofs.base.array.common


section
namespace JuliaLean.MemSafety.G6

open JuliaLean

/-- `cglobal(:jl_default_debug_info_kind, Cint)` denotes one `Cint`; `unsafe_load` reads its
zero offset (`base/reflection.jl:90`, `src/jl_exported_data.inc`). -/
inductive DebugInfoGlobal where
  | runtimeOwned

def reflectionGlobalLoad (_ : DebugInfoGlobal) : Nat × Nat := (0, 1)

def ReflectionGlobalLoadInBounds : Prop :=
  ∀ global : DebugInfoGlobal, (reflectionGlobalLoad global).1 < (reflectionGlobalLoad global).2

theorem reflectionGlobalLoadInBounds_proven : ReflectionGlobalLoadInBounds := by
  intro global
  cases global
  unfold reflectionGlobalLoad
  omega
end JuliaLean.MemSafety.G6
end
