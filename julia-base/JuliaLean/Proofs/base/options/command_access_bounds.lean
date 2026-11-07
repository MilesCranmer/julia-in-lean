import JuliaLean.Proofs.base.array.common.index_bounds

namespace JuliaLean.MemSafety.G5

/-! ## runtime-owned pointer tables -/

/-- One command string in the runtime-owned `JLOptions.commands` table. Its
head is the byte read at options.jl:128; `tail` includes the remaining C string. -/
structure RuntimeCommand where
  head : Nat
  tail : List Nat

/-- The runtime table is the listed command pointers followed by a null
sentinel, exactly the layout scanned at options.jl:121-131. -/
structure RuntimeOptions where
  commands : List RuntimeCommand

/-- Pointer-table indices loaded by the sentinel loop, including the final
null pointer. -/
def optionsPointerLoads (options : RuntimeOptions) : List Nat :=
  oneBasedLoop (options.commands.length + 1)

/-- The first-byte load for each non-null command pointer. -/
def optionsCommandByteLoads (options : RuntimeOptions) : List Nat :=
  options.commands.map (fun _ => 1)

/-- `JLOptions()` loads one runtime object; all show and `exec_options` callers
scan the null-terminated command table and one byte of each command string. -/
def OptionsCommandsAccessesInBounds : Prop :=
  OneBasedInBounds 1 1 ∧
  (∀ options i, i ∈ optionsPointerLoads options →
    OneBasedInBounds (options.commands.length + 1) i) ∧
  (∀ options i, i ∈ optionsCommandByteLoads options → OneBasedInBounds 1 i)

theorem optionsCommandsAccessesInBounds : OptionsCommandsAccessesInBounds := by
  refine ⟨by simp [OneBasedInBounds], ?_, ?_⟩
  · intro options i hi
    simp only [optionsPointerLoads, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    simp only [OneBasedInBounds]
    omega
  · intro options i hi
    simp only [optionsCommandByteLoads, List.mem_map] at hi
    obtain ⟨command, _, rfl⟩ := hi
    simp [OneBasedInBounds]

end JuliaLean.MemSafety.G5
