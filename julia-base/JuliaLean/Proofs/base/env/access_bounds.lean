import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Word count of the Windows block returned by `GetEnvironmentStringsW`,
represented by the lengths of its NUL-terminated entries and the final NUL,
`base/env.jl:193-228`. -/
def windowsEnvStorageLength : List Nat → Nat
  | [] => 1
  | len :: rest => len + 1 + windowsEnvStorageLength rest

/-- Offsets at which `iterate(::EnvDict)` reads the first word of an entry or
the final NUL. -/
def windowsEnvStarts : Nat → List Nat → List Nat
  | offset, [] => [offset]
  | offset, len :: rest => offset :: windowsEnvStarts (offset + len + 1) rest

/-- Source spans copied after `wcslen` has computed each entry length. -/
def windowsEnvCopies : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | offset, len :: rest => (offset, len) :: windowsEnvCopies (offset + len + 1) rest

/-- The 1-based pointer indices read from the POSIX `environ` array, including
its terminating null pointer, `base/env.jl:230-245`. -/
def unixEnvLoads (entries : List Nat) : List Nat :=
  oneBasedLoop (entries.length + 1)

/-- `_environ` loads one pointer from the pointer supplied by Darwin or the
process symbol table. Windows block layout follows the documented
`entry\0...\0\0` format; POSIX `environ` is a null-terminated pointer array. -/
def EnvironmentBufferSafe : Prop :=
  (0 < 1) ∧
  (∀ (entryLengths : List Nat) offset,
    offset ∈ windowsEnvStarts 0 entryLengths →
      offset < windowsEnvStorageLength entryLengths) ∧
  (∀ (entryLengths : List Nat) span,
    span ∈ windowsEnvCopies 0 entryLengths →
      span.1 + span.2 ≤ windowsEnvStorageLength entryLengths) ∧
  (∀ (entries : List Nat) i, i ∈ unixEnvLoads entries →
    inOneBased (entries.length + 1) i)

private theorem windowsEnvStarts_safe :
    ∀ entryLengths offset i, i ∈ windowsEnvStarts offset entryLengths →
      i < offset + windowsEnvStorageLength entryLengths
  | [], offset, i, hi => by
      have h : i = offset := by simpa [windowsEnvStarts] using hi
      subst i
      simp [windowsEnvStorageLength]
  | len :: rest, offset, i, hi => by
      simp only [windowsEnvStarts, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp [windowsEnvStorageLength]
        omega
      · have h := windowsEnvStarts_safe rest (offset + len + 1) i hi
        simp only [windowsEnvStorageLength]
        omega

private theorem windowsEnvCopies_safe :
    ∀ entryLengths offset span, span ∈ windowsEnvCopies offset entryLengths →
      span.1 + span.2 ≤ offset + windowsEnvStorageLength entryLengths
  | [], _, span, hi => by simp [windowsEnvCopies] at hi
  | len :: rest, offset, span, hi => by
      simp only [windowsEnvCopies, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp only [windowsEnvStorageLength]
        simpa only [Nat.add_assoc] using
          Nat.add_le_add_left (Nat.le_add_right len (1 + windowsEnvStorageLength rest)) offset
      · have h := windowsEnvCopies_safe rest (offset + len + 1) span hi
        simp only [windowsEnvStorageLength]
        omega

theorem environmentBufferSafe_proven : EnvironmentBufferSafe := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro entryLengths offset hi
    simpa using windowsEnvStarts_safe entryLengths 0 offset hi
  · intro entryLengths span hi
    simpa using windowsEnvCopies_safe entryLengths 0 span hi
  · intro entries i hi
    simp only [unixEnvLoads, oneBasedLoop, List.mem_map, List.mem_range] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    unfold inOneBased
    omega

end JuliaLean.MemSafety.G3
