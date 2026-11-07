import JuliaLean.base.reflection
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.reflection.memory_safety
open JuliaLean
open JuliaLean.base.io (M)

-- The exported Cint global occupies one cell; pointer offsets are measured in Cints.
def checkedGlobalLoad (value : JInt .i32) (offset : Nat) : M Unit (JInt .i32) :=
  if offset < 1 then pure value else throw (.jl .boundsError)

def ReflectionGlobalLoadInBounds : Prop :=
  ∀ value : JInt .i32,
    JuliaLean.base.reflection.defaultDebugInfoKind
      (pure 0 : M Unit Nat) (checkedGlobalLoad value) () = some (.ok (value, ()))

theorem reflectionGlobalLoadInBounds_proven : ReflectionGlobalLoadInBounds := by
  intro value
  rfl

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-reflection-debug-global", juliaFile := "base/reflection.jl"
    juliaFns := ["default_debug_info_kind"]
    statement := "Reading the runtime-owned default-debug-info Cint succeeds without accessing beyond its single allocated cell."
    source := "base/reflection.jl:90; src/jl_exported_data.inc"
    status := .proven, prop := ``ReflectionGlobalLoadInBounds
    thm := some ``reflectionGlobalLoadInBounds_proven }
]
end JuliaLean.Proofs.base.reflection.memory_safety
