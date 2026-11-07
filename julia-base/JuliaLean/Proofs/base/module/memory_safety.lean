import JuliaLean.base.module
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.module.memory_safety

def ModuleSymbolSafe : Prop :=
  ∀ name : String, ∃ first : UInt8,
    (name.toUTF8.toList ++ [0]).head? = some first ∧
    JuliaLean.base.module_.startsWithAt name = (first == 0x40)

theorem moduleSymbolSafe_proven : ModuleSymbolSafe := by
  intro name
  unfold JuliaLean.base.module_.startsWithAt
  cases h : name.toUTF8.toList with
  | nil => exact ⟨0, by simp, by decide⟩
  | cons first rest => exact ⟨first, by simp, by simp⟩

open JuliaLean.Registry

def entries : List Entry := [
  { id := "memsafety-module-symbol-prefix", juliaFile := "base/module.jl"
    juliaFns := ["check_macro_rename"]
    statement := "The macro-name prefix test reads an existing byte of the runtime's NUL-terminated Symbol storage, including for the empty name."
    source := "base/module.jl:67-75; Symbol C-string representation invariant"
    status := .proven, prop := ``ModuleSymbolSafe
    thm := some ``moduleSymbolSafe_proven }
]
end JuliaLean.Proofs.base.module.memory_safety
