import JuliaLean.Proofs.base.abstractarray.common.input_invariants

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Runtime thread ids are zero-based and below `maxthreadid()`. -/
structure ThreadRuntime where
  maxThreadId : Nat
  threadId : Fin maxThreadId

/-- The global context vector starts nonempty and only grows. -/
structure MatchContexts where
  length : Nat
  nonempty : 1 ≤ length

def juliaThreadId (runtime : ThreadRuntime) : Nat := runtime.threadId.val + 1

/-- The vector length after the slow-path growth at
`base/pcre.jl:40-56`. -/
def matchContextLength (runtime : ThreadRuntime) (contexts : MatchContexts) : Nat :=
  let tid := juliaThreadId runtime
  if contexts.length < tid then contexts.length + runtime.maxThreadId else contexts.length

/-- A PCRE2 8-bit name table has `count` fixed-size entries; every entry begins
with two capture-number bytes. -/
structure PcreNameTable where
  count : Nat
  entrySize : Nat
  headerFits : 2 ≤ entrySize

/-- The two 1-based pointer indices computed for every table entry by
`capture_names`, `base/pcre.jl:265-280`. -/
def pcreNameByteIndices (table : PcreNameTable) : List Nat :=
  (oneBasedLoop table.count).flatMap fun i =>
    let offset := (i - 1) * table.entrySize + 1
    [offset, offset + 1]

def pcreNameStorageLength (table : PcreNameTable) : Nat :=
  table.count * table.entrySize

def PcreNameTableSafe : Prop :=
  (∀ (runtime : ThreadRuntime) (contexts : MatchContexts),
    inOneBased (matchContextLength runtime contexts) (juliaThreadId runtime)) ∧
  (∀ (table : PcreNameTable) i, i ∈ pcreNameByteIndices table →
    inOneBased (pcreNameStorageLength table) i)

theorem pcreNameTableSafe_proven : PcreNameTableSafe := by
  constructor
  · intro runtime contexts
    have ht := runtime.threadId.isLt
    by_cases h : contexts.length < runtime.threadId.val + 1 <;>
      simp [matchContextLength, juliaThreadId, inOneBased, h] <;>
      omega
  · intro table i hi
    simp only [pcreNameByteIndices, List.mem_flatMap, oneBasedLoop,
      List.mem_map, List.mem_range] at hi
    obtain ⟨entry, ⟨k, hk, rfl⟩, hi⟩ := hi
    simp only [List.mem_cons] at hi
    rcases hi with rfl | hi
    · unfold pcreNameStorageLength inOneBased
      simp only [Nat.succ_sub_one]
      have hs := table.headerFits
      have hnext : k + 1 ≤ table.count := by omega
      have hmul := Nat.mul_le_mul_right table.entrySize hnext
      rw [Nat.add_mul] at hmul
      omega
    · rcases hi with rfl | hi
      · unfold pcreNameStorageLength inOneBased
        simp only [Nat.succ_sub_one]
        have hs := table.headerFits
        have hnext : k + 1 ≤ table.count := by omega
        have hmul := Nat.mul_le_mul_right table.entrySize hnext
        rw [Nat.add_mul] at hmul
        omega
      · contradiction

end JuliaLean.MemSafety.G3
