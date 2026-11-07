import JuliaLean.base.gmp
import JuliaLean.Proofs.base.hashing.memory_safety_group2

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/gmp.jl`: BigInt limb and string accesses -/

inductive BigStorage where
  | owned (value : Int)
  | globalZero
  deriving DecidableEq, Repr

def BigStorage.used : BigStorage → Nat
  | .owned x => JuliaLean.BigNums.nlimbs x
  | .globalZero => 0

def BigStorage.capacity : BigStorage → Nat
  | .owned x => max 1 (JuliaLean.BigNums.nlimbs x)
  | .globalZero => 0

/-- Eager `&` evaluates the limb load even for zero. -/
def gmpBoolRemAccess (x : BigStorage) : List Access := [⟨x.capacity, 1⟩]

def GmpBoolRemInBounds : Prop := ∀ x, AllInBounds (gmpBoolRemAccess x)

structure IntegerInput where
  value : Int
  isBits : Bool
  deriving DecidableEq, Repr

def gmpConstructorAccesses (x : IntegerInput) : List Access :=
  if x.isBits && -(2^63 : Int) ≤ x.value && x.value ≤ (2^63 : Int) - 1 then []
  else (oneBased (JuliaLean.BigNums.nlimbs x.value)).map fun i =>
    ⟨JuliaLean.BigNums.nlimbs x.value, i⟩

def gmpRemainderAccesses (x : Int) (words : Nat) : List Access :=
  let used := JuliaLean.BigNums.nlimbs x
  let small := if x = 0 then [] else [⟨used, 1⟩]
  let wide := (oneBased (min used words)).map fun i => ⟨used, i⟩
  small ++ wide

def scanNonzeroLimbs (x : Int) : Nat → List Int
  | 0 => []
  | i + 1 =>
      (i + 1 : Int) ::
        if JuliaLean.BigNums.limb x i = 0 then scanNonzeroLimbs x i else []

def gmpFloatAccesses (x : Int) : List Access :=
  let used := JuliaLean.BigNums.nlimbs x
  if used = 0 then [] else
    let top := JuliaLean.BigNums.limb x (used - 1)
    let filled := top.log2 + 1
    let rest := if 1 < used && filled < 64 then scanNonzeroLimbs x (used - 1) else []
    ((used : Int) :: rest).map fun i => ⟨used, i⟩

def GmpLimbAccessesInBounds : Prop :=
  (∀ x, AllInBounds (gmpConstructorAccesses x)) ∧
  (∀ x words, AllInBounds (gmpRemainderAccesses x words)) ∧
  (∀ x, AllInBounds (gmpFloatAccesses x))

def gmpBitMagnitudeAccess (x : Int) : List Access :=
  if x = 0 then [] else
    let used := JuliaLean.BigNums.nlimbs x
    [⟨used, used⟩]

def GmpBitMagnitudeInBounds : Prop := ∀ x, AllInBounds (gmpBitMagnitudeAccess x)

def gmpStringSignAccess (n base pad : Int) : List Access :=
  if base < 0 || base < 2 || 62 < base || (n = 0 && pad < 1) then [] else
    let nd1 := (JuliaLean.BigNums.digitChars n base.toNat).length
    let nd := max nd1 pad.toNat
    if n < 0 then [⟨nd + 1, 1⟩] else []

def GmpStringSignInBounds : Prop := ∀ n base pad,
  AllInBounds (gmpStringSignAccess n base pad)


/-! `base/gmp.jl:873-955`: the two BigInt hash paths and their
`UnsafeLimbView`. `limbs` is the GMP little-endian limb storage; each value is
reduced to the 64-bit `Limb` width before bit and byte selection. -/

def limbBit (limbs : List Nat) (bit : Nat) : Bool :=
  let limb := (limbs.getD (bit / 64) 0) % 2^64
  decide (limb / 2^(bit % 64) % 2 = 1)

def firstNonzeroBit (limbs : List Nat) : Nat :=
  (List.range (64 * limbs.length)).findIdx? (limbBit limbs) |>.getD (64 * limbs.length)

def leadingZeroBytes (limbs : List Nat) : Nat :=
  if limbs.isEmpty then 0 else
    let top := (limbs.getLastD 0) % 2^64
    if top = 0 then 8 else (63 - top.log2) / 8

def viewLimbAccesses (limbs : List Nat) (startByte count : Nat) : List Access :=
  (hashByteOffsets count).map fun (byte : Nat) =>
    ⟨limbs.length, (((startByte + byte - 1) / 8 + 1 : Nat) : Int)⟩

def gmpHashIntegerAccesses (limbs : List Nat) : List Access :=
  if limbs.isEmpty then [] else
    let used := limbs.length
    let count := 8 * used - leadingZeroBytes limbs
    ⟨used, used⟩ :: viewLimbAccesses limbs 1 count

def gmpHashAccesses (limbs : List Nat) : List Access :=
  if limbs.isEmpty then [] else
    let used := limbs.length
    if used = 1 then [⟨used, 1⟩] else
      let pow := firstNonzeroBit limbs
      if pow = 64 * used then [] else
        let idx := pow / 64 + 1
        let shift := pow % 64
        let direct := if shift = 0 then [⟨used, idx⟩]
          else [⟨used, idx⟩] ++ if idx < used then [⟨used, idx + 1⟩] else []
        let trailingBytes := pow / 8
        let count := 8 * used - (leadingZeroBytes limbs + trailingBytes)
        direct ++ [⟨used, used⟩] ++ viewLimbAccesses limbs (trailingBytes + 1) count

def GmpHashInBounds : Prop :=
  (∀ limbs, AllInBounds (gmpHashIntegerAccesses limbs)) ∧
  (∀ limbs, AllInBounds (gmpHashAccesses limbs))


theorem gmpBoolRemInBounds_refuted : ¬ GmpBoolRemInBounds := by
  intro h
  have bad := h BigStorage.globalZero
  simp [gmpBoolRemAccess, BigStorage.capacity, AllInBounds, Access.inBounds] at bad

private theorem scanNonzeroLimbs_safe (x : Int) : ∀ n i,
    i ∈ scanNonzeroLimbs x n → 1 ≤ i ∧ i ≤ n
  | 0, i, h => by simp [scanNonzeroLimbs] at h
  | n + 1, i, h => by
      simp only [scanNonzeroLimbs, List.mem_cons] at h
      rcases h with rfl | h
      · omega
      · split at h
        · have ih := scanNonzeroLimbs_safe x n i h
          omega
        · simp at h

theorem gmpLimbAccessesInBounds : GmpLimbAccessesInBounds := by
  refine ⟨?_, ?_, ?_⟩
  · intro x access ha
    simp only [gmpConstructorAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      exact oneBased_mem hi
  · intro x words access ha
    simp only [gmpRemainderAccesses, List.mem_append] at ha
    rcases ha with ha | ha
    · split at ha
      · simp at ha
      · simp only [List.mem_singleton] at ha
        subst access
        simp only [Access.inBounds]
        have hp : 0 < JuliaLean.BigNums.nlimbs x := by
          unfold JuliaLean.BigNums.nlimbs
          simp [*]
        omega
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      have hb := oneBased_mem hi
      simp only [Access.inBounds]
      omega
  · intro x access ha
    simp only [gmpFloatAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp only [Access.inBounds]
        omega
      · split at hi
        · have hs := scanNonzeroLimbs_safe x _ i hi
          simp only [Access.inBounds]
          omega
        · simp at hi

theorem gmpBitMagnitudeInBounds : GmpBitMagnitudeInBounds := by
  intro x access ha
  simp only [gmpBitMagnitudeAccess] at ha
  split at ha
  · simp at ha
  · simp only [List.mem_singleton] at ha
    subst access
    simp only [Access.inBounds]
    have hp : 0 < JuliaLean.BigNums.nlimbs x := by
      unfold JuliaLean.BigNums.nlimbs
      simp [*]
    omega

theorem gmpStringSignInBounds : GmpStringSignInBounds := by
  intro n base pad access ha
  simp only [gmpStringSignAccess] at ha
  split at ha
  · simp at ha
  · split at ha
    · simp only [List.mem_singleton] at ha
      subst access
      simp only [Access.inBounds]
      omega
    · simp at ha



private theorem firstNonzeroBit_le (limbs : List Nat) :
    firstNonzeroBit limbs ≤ 64 * limbs.length := by
  unfold firstNonzeroBit
  cases h : (List.range (64 * limbs.length)).findIdx? (limbBit limbs) with
  | none => simp [h]
  | some k =>
      have hk : k < (List.range (64 * limbs.length)).length :=
        (List.findIdx?_eq_some_iff_getElem.mp h).1
      simp only [List.length_range] at hk
      simp [h]
      omega

private theorem viewLimbAccesses_safe (limbs : List Nat) (start count : Nat)
    (hstart : 1 ≤ start) (hspan : start - 1 + count ≤ 8 * limbs.length) :
    AllInBounds (viewLimbAccesses limbs start count) := by
  intro access ha
  simp only [viewLimbAccesses, List.mem_map] at ha
  obtain ⟨byte, hbyte, rfl⟩ := ha
  have hb := hashByteOffsets_mem hbyte
  simp only [Access.inBounds]
  constructor
  · exact_mod_cast Nat.succ_pos ((start + byte - 1) / 8)
  · have hlt : (start + byte - 1) / 8 < limbs.length := by
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 8)]
      omega
    exact_mod_cast Nat.succ_le_of_lt hlt

set_option maxHeartbeats 200000 in
theorem gmpHashInBounds : GmpHashInBounds := by
  constructor
  · intro limbs access ha
    simp only [gmpHashIntegerAccesses] at ha
    split at ha
    · simp at ha
    · simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp only [Access.inBounds]
        have hne : limbs ≠ [] := by
          intro hnil
          subst limbs
          simp_all
        have : 0 < limbs.length := List.length_pos_iff.mpr hne
        omega
      · exact viewLimbAccesses_safe limbs 1 (8 * limbs.length - leadingZeroBytes limbs)
          (by omega) (by omega) access ha
  · intro limbs access ha
    simp only [gmpHashAccesses] at ha
    split at ha
    · simp at ha
    · split at ha
      · simp at ha
        subst access
        simp only [Access.inBounds]
        simp_all
      · split at ha
        · simp at ha
        · rw [List.mem_append] at ha
          rcases ha with hdirectTop | hview
          · rw [List.mem_append] at hdirectTop
            rcases hdirectTop with hdirect | htop
            · have hp := firstNonzeroBit_le limbs
              have hd : firstNonzeroBit limbs / 64 < limbs.length := by
                rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 64)]
                omega
              split at hdirect
              · simp only [List.mem_singleton] at hdirect
                subst access
                simp only [Access.inBounds]
                exact ⟨by omega, by exact_mod_cast Nat.succ_le_of_lt hd⟩
              · rw [List.mem_append] at hdirect
                rcases hdirect with hdirect | hnext
                · simp only [List.mem_singleton] at hdirect
                  subst access
                  simp only [Access.inBounds]
                  exact ⟨by omega, by exact_mod_cast Nat.succ_le_of_lt hd⟩
                · split at hnext
                  · simp only [List.mem_singleton] at hnext
                    subst access
                    simp only [Access.inBounds]
                    omega
                  · simp at hnext
            · simp only [List.mem_singleton] at htop
              subst access
              simp only [Access.inBounds]
              have hne : limbs ≠ [] := by
                intro hnil
                subst limbs
                simp_all
              have : 0 < limbs.length := List.length_pos_iff.mpr hne
              omega
          · exact viewLimbAccesses_safe limbs (firstNonzeroBit limbs / 8 + 1)
              (8 * limbs.length - (leadingZeroBytes limbs + firstNonzeroBit limbs / 8))
              (by omega) (by have hp := firstNonzeroBit_le limbs; omega) access hview

end JuliaLean.MemSafety.G2
