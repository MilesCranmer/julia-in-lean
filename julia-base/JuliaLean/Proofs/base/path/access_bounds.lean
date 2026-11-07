import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- A string returned by `ConvertSidToStringSidW`; `wcslen` computes the
wrapped extent from these code units and excludes the trailing NUL. -/
structure SidString where
  codeunits : List UInt16

def sidWrapLength (sid : SidString) : Nat := sid.codeunits.length

def sidStorageLength (sid : SidString) : Nat := sid.codeunits.length + 1

/-- Byte offsets read for `pw_uid` after the two pointer fields in
`struct passwd`, `base/path.jl:781-807`. -/
def passwdUidOffsets (width : SupportedPointerWidth) : List Nat :=
  (List.range 4).map (fun byte => 2 * pointerBytes width + byte)

/-- The SID wrapper uses exactly the `wcslen` result, and the four-byte uid
load lies inside the 256-byte `pwd_storage` on every supported pointer width. -/
def PathBufferSafe : Prop :=
  (∀ sid : SidString, sidWrapLength sid ≤ sidStorageLength sid) ∧
  (∀ width offset, offset ∈ passwdUidOffsets width → offset < 256)

theorem pathBufferSafe_proven : PathBufferSafe := by
  constructor
  · intro sid
    simp [sidWrapLength, sidStorageLength]
  · intro width offset hi
    cases width <;>
      simp [passwdUidOffsets, pointerBytes] at hi <;>
      omega

end JuliaLean.MemSafety.G3
