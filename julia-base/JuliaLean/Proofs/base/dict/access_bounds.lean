import JuliaLean.Proofs.base.abstractarray.common.input_invariants
import JuliaLean.Proofs.base.dict.ProofLookup
import JuliaLean.Proofs.base.dict.ProofInsert

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Every slot reached by a complete probe cycle from the hash-selected home
slot. Actual lookup and insertion loops use prefixes of this list. -/
def dictProbeAccesses (t : Dicts.Table K V) (hash : JInt .u64) : List Nat :=
  if t.size = 0 then [] else
    (List.range t.size).map fun distance =>
      Dicts.pr t.size (Dicts.hashindex hash t.size).1 distance

/-- Every slot reached by `eachindex(slots)`, `1:length(slots)`, rehash copy,
and filter/map scans. -/
def dictScanAccesses (t : Dicts.Table K V) : List Nat :=
  oneBasedLoop t.size

/-- The suffix scanned by Dict iteration and pop, starting at `idxfloor`. -/
def dictFloorAccesses (t : Dicts.Table K V) : List Nat :=
  (List.range (t.size + 1 - t.idxfloor)).map fun k => t.idxfloor + k

/-- Union of computed slots used by rehashing, lookup, insertion, deletion,
iteration, filtering, mapping, and merge paths in `base/dict.jl:140-770`. -/
def dictAccesses (t : Dicts.Table K V) (hash : JInt .u64) : List Nat :=
  dictProbeAccesses t hash ++ dictScanAccesses t ++ dictFloorAccesses t

def DictProbeSafe : Prop :=
  ∀ (K V : Type) (o : Dicts.KeyOps K) (t : Dicts.Table K V) hash index,
    Dicts.Inv o t → index ∈ dictAccesses t hash → inOneBased t.size index

theorem dictProbeSafe_proven : DictProbeSafe := by
  intro K V o t hash index hinv hi
  unfold dictAccesses at hi
  simp only [List.mem_append] at hi
  rcases hi with (hprobe | hscan) | hfloor
  · unfold dictProbeAccesses at hprobe
    by_cases hzero : t.size = 0
    · simp [hzero] at hprobe
    · simp only [hzero, ↓reduceIte, List.mem_map, List.mem_range] at hprobe
      obtain ⟨distance, hd, rfl⟩ := hprobe
      have hp : Dicts.IsPow t.size := by
        rcases hinv.size with h | h
        · exact absurd h hzero
        · exact h
      have hh := Dicts.hashindex_range hp hash
      exact Dicts.pr_range hp hh.1 hh.2 hd
  · simp only [dictScanAccesses, oneBasedLoop, List.mem_map, List.mem_range] at hscan
    obtain ⟨k, hk, rfl⟩ := hscan
    unfold inOneBased
    omega
  · simp only [dictFloorAccesses, List.mem_map, List.mem_range] at hfloor
    obtain ⟨k, hk, rfl⟩ := hfloor
    unfold inOneBased
    have hf := hinv.idxfloor
    omega

end JuliaLean.MemSafety.G3
