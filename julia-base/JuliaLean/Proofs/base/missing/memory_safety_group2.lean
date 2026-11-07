import JuliaLean.Proofs.base.experimental.memory_safety_group2

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/missing.jl`: `SkipMissing` enumerators and mapreduce -/

def skipMissingEachindexAccesses (first : I64) (missing : List Bool) : List Access :=
  (axisValues ⟨first, missing.length⟩).map fun i =>
    ⟨missing.length, i - first.val + 1⟩

def SkipMissingEachindexInBounds : Prop := ∀ first missing,
  AllInBounds (skipMissingEachindexAccesses first missing)


def cartesianAxisCoords : List Axis → List (List Int)
  | [] => [[]]
  | a :: axes =>
      (axisValues a).flatMap fun i => (cartesianAxisCoords axes).map fun is => i :: is


def skipMissingKeysAccesses (axes : List Axis) : List Access :=
  (cartesianAxisCoords axes).flatMap (constCartesianAccessAxes axes)

def SkipMissingKeysInBounds : Prop := ∀ axes,
  AllInBounds (skipMissingKeysAccesses axes)

structure Scan where
  visited : List Nat
  found : Option Nat
  deriving DecidableEq, Repr

def scanMissing (missing : List Bool) (start count : Nat) : Scan :=
  let offsets := List.range (min count (missing.length - start))
  match offsets.findIdx? (fun off => !missing.getD (start + off) true) with
  | some off => ⟨(List.range (off + 1)).map (start + ·), some (start + off)⟩
  | none => ⟨offsets.map (start + ·), none⟩

def indexValue (first : I64) (ordinal : Nat) : I64 := first + i64 ordinal

def sequentialMapreduceTrace (first : I64) (missing : List Bool)
    (start count : Nat) : List Nat :=
  match (scanMissing missing start count).found with
  | none => (scanMissing missing start count).visited
  | some p =>
      if (indexValue first p).val = IntTy.max .i64 then
        (scanMissing missing start count).visited
      else match (scanMissing missing (p + 1) (start + count - (p + 1))).found with
      | none => (scanMissing missing start count).visited ++
          (scanMissing missing (p + 1) (start + count - (p + 1))).visited
      | some q =>
          if (indexValue first q).val = IntTy.max .i64 then
            (scanMissing missing start count).visited ++
              (scanMissing missing (p + 1) (start + count - (p + 1))).visited
          else
            (scanMissing missing start count).visited ++
              (scanMissing missing (p + 1) (start + count - (p + 1))).visited ++
              (List.range (start + count - (q + 1))).map (q + 1 + ·)

def mapreduceImplTrace : Nat → I64 → List Bool → Nat → Nat → Nat → List Nat
  | 0, _, _, _, _, _ => []
  | fuel + 1, first, missing, start, count, blockSize =>
      if count = 0 then []
      else if count = 1 then [start]
      else if count - 1 < blockSize then
        sequentialMapreduceTrace first missing start count
      else
        let leftCount := (count - 1) / 2 + 1
        mapreduceImplTrace fuel first missing start leftCount blockSize ++
          mapreduceImplTrace fuel first missing (start + leftCount) (count - leftCount) blockSize

def mapreduceOrdinals (first : I64) (missing : List Bool) (blockSize : Nat) : List Nat :=
  match (scanMissing missing 0 missing.length).found with
  | none => (scanMissing missing 0 missing.length).visited
  | some p =>
      if (indexValue first p).val = IntTy.max .i64 then
        (scanMissing missing 0 missing.length).visited
      else match (scanMissing missing (p + 1) (missing.length - (p + 1))).found with
      | none => (scanMissing missing 0 missing.length).visited ++
          (scanMissing missing (p + 1) (missing.length - (p + 1))).visited
      | some _ => (scanMissing missing 0 missing.length).visited ++
          (scanMissing missing (p + 1) (missing.length - (p + 1))).visited ++
          mapreduceImplTrace missing.length first missing 0 missing.length blockSize

def mapreduceBlockAccesses (first : I64) (missing : List Bool) (blockSize : Nat) : List Access :=
  (mapreduceOrdinals first missing blockSize).map fun (k : Nat) =>
    ⟨missing.length, (k : Int) + 1⟩

def MissingMapreduceInBounds : Prop := ∀ first missing blockSize,
  AllInBounds (mapreduceBlockAccesses first missing blockSize)



theorem skipMissingEachindexInBounds : SkipMissingEachindexInBounds := by
  intro first missing access ha
  simp only [skipMissingEachindexAccesses, List.mem_map] at ha
  obtain ⟨i, hi, heq⟩ := ha
  subst access
  simp [axisValues] at hi
  simp only [Access.inBounds]
  omega

theorem skipMissingKeysInBounds : SkipMissingKeysInBounds := by
  intro axes access ha
  simp only [skipMissingKeysAccesses, List.mem_flatMap] at ha
  obtain ⟨coords, hcoords, ha⟩ := ha
  exact constCartesianAccessAxes_safe axes coords access ha

private theorem scanMissing_safe (missing : List Bool) (start count : Nat) :
    (∀ k ∈ (scanMissing missing start count).visited,
      start ≤ k ∧ k < start + count ∧ k < missing.length) ∧
    (∀ k, (scanMissing missing start count).found = some k →
      start ≤ k ∧ k < start + count ∧ k < missing.length) := by
  simp only [scanMissing]
  split
  · rename_i off hfind
    have hoff : off < (List.range (min count (missing.length - start))).length :=
      (List.findIdx?_eq_some_iff_getElem.mp hfind).1
    simp only [List.length_range] at hoff
    constructor
    · intro k hk
      simp only [List.mem_map, List.mem_range] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      omega
    · intro k hk
      simp only [Option.some.injEq] at hk
      subst k
      omega
  · constructor
    · intro k hk
      simp only [List.mem_map, List.mem_range] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      omega
    · intro k hk
      simp at hk

private theorem sequentialMapreduceTrace_safe (first : JuliaLean.AbstractArrays.I64)
    (missing : List Bool) :
    ∀ start count k, start + count ≤ missing.length →
      k ∈ sequentialMapreduceTrace first missing start count → k < missing.length := by
  intro start count k hspan hk
  simp only [sequentialMapreduceTrace] at hk
  cases hfound : (scanMissing missing start count).found with
  | none =>
      rw [hfound] at hk
      exact ((scanMissing_safe missing start count).1 k hk).2.2
  | some p =>
    rw [hfound] at hk
    simp_all only [Option.some.injEq]
    split at hk
    · exact ((scanMissing_safe missing start count).1 k hk).2.2
    · cases hfound2 : (scanMissing missing (p + 1) (start + count - (p + 1))).found with
      | none =>
        rw [hfound2] at hk
        rcases List.mem_append.mp hk with hk | hk
        · exact ((scanMissing_safe missing start count).1 k hk).2.2
        · exact ((scanMissing_safe missing (p + 1) (start + count - (p + 1))).1 k hk).2.2
      | some q =>
        rw [hfound2] at hk
        simp_all only [Option.some.injEq]
        split at hk
        · rcases List.mem_append.mp hk with hk | hk
          · exact ((scanMissing_safe missing start count).1 k hk).2.2
          · exact ((scanMissing_safe missing (p + 1) (start + count - (p + 1))).1 k hk).2.2
        · rcases List.mem_append.mp hk with hk | hk
          · rcases List.mem_append.mp hk with hk | hk
            · exact ((scanMissing_safe missing start count).1 k hk).2.2
            · exact ((scanMissing_safe missing (p + 1) (start + count - (p + 1))).1 k hk).2.2
          · simp only [List.mem_map, List.mem_range] at hk
            obtain ⟨j, hj, rfl⟩ := hk
            have hq := (scanMissing_safe missing (p + 1)
              (start + count - (p + 1))).2 q hfound2
            omega

private theorem mapreduceImplTrace_safe (first : JuliaLean.AbstractArrays.I64)
    (missing : List Bool) :
    ∀ fuel start count blockSize k, start + count ≤ missing.length →
      k ∈ mapreduceImplTrace fuel first missing start count blockSize → k < missing.length
  | 0, start, count, blockSize, k, hspan, hk => by simp [mapreduceImplTrace] at hk
  | fuel + 1, start, count, blockSize, k, hspan, hk => by
      simp only [mapreduceImplTrace] at hk
      split at hk
      · simp at hk
      · split at hk
        · simp only [List.mem_singleton] at hk
          subst k
          omega
        · split at hk
          · exact sequentialMapreduceTrace_safe first missing start count k hspan hk
          · rw [List.mem_append] at hk
            rcases hk with hk | hk
            · exact mapreduceImplTrace_safe first missing fuel start ((count - 1) / 2 + 1)
                blockSize k (by omega) hk
            · exact mapreduceImplTrace_safe first missing fuel (start + ((count - 1) / 2 + 1))
                (count - ((count - 1) / 2 + 1)) blockSize k (by omega) hk

theorem missingMapreduceInBounds : MissingMapreduceInBounds := by
  intro first missing blockSize access ha
  simp only [mapreduceBlockAccesses, List.mem_map] at ha
  obtain ⟨k, hk, heq⟩ := ha
  subst access
  simp only [Access.inBounds]
  have hbound : k < missing.length := by
    simp only [mapreduceOrdinals] at hk
    cases hfound : (scanMissing missing 0 missing.length).found with
    | none =>
      rw [hfound] at hk
      exact ((scanMissing_safe missing 0 missing.length).1 k hk).2.2
    | some p =>
      rw [hfound] at hk
      simp_all only [Option.some.injEq]
      split at hk
      · exact ((scanMissing_safe missing 0 missing.length).1 k hk).2.2
      · cases hfound2 : (scanMissing missing (p + 1) (missing.length - (p + 1))).found with
        | none =>
          rw [hfound2] at hk
          rcases List.mem_append.mp hk with hk | hk
          · exact ((scanMissing_safe missing 0 missing.length).1 k hk).2.2
          · exact ((scanMissing_safe missing (p + 1) (missing.length - (p + 1))).1 k hk).2.2
        | some q =>
          rw [hfound2] at hk
          simp_all only [Option.some.injEq]
          rcases List.mem_append.mp hk with hk | hk
          · rcases List.mem_append.mp hk with hk | hk
            · exact ((scanMissing_safe missing 0 missing.length).1 k hk).2.2
            · exact ((scanMissing_safe missing (p + 1) (missing.length - (p + 1))).1 k hk).2.2
          · exact mapreduceImplTrace_safe first missing missing.length 0 missing.length
              blockSize k (by omega) hk
  exact ⟨by omega, by omega⟩

end JuliaLean.MemSafety.G2
