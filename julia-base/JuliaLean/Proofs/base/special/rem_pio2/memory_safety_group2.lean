import JuliaLean.Runtime.Float
import JuliaLean.Proofs.base.indices.memory_safety_group2_common

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.AbstractArrays
/-! ## `base/special/rem_pio2.jl:130-293` -/

def payneHanekIndices (rawExponent : Nat) : List Int :=
  let k : Int := rawExponent - 1023 - 52
  let idx := k / 64
  let shift := k - idx * 64
  if shift = 0 then [idx + 1, idx + 2, idx + 3]
  else (if idx < 0 then [] else [idx + 1]) ++ [idx + 2, idx + 3, idx + 4]

def f64PayneAccesses (x : JuliaLean.Float.F64) : List Access :=
  let bits := JuliaLean.Float.F64.toBits x
  let highword := (bits % 2^63) / 2^32
  let rawExponent := highword / 2^20
  if highword < 0x7ff00000 && 0x413921fb ≤ highword then
    (payneHanekIndices rawExponent).map fun i => ⟨19, i⟩
  else []

def f32PayneAccesses (bits : BitVec 32) : List Access :=
  let raw := bits.toNat / 2^23 % 256
  let magnitude := bits.toNat % 2^31
  if raw < 255 && 0x4dc90fdb ≤ magnitude then
    (payneHanekIndices (raw - 127 + 1023)).map fun i => ⟨19, i⟩
  else []

def PayneHanekCallerInBounds : Prop :=
  (∀ x, AllInBounds (f64PayneAccesses x)) ∧
  (∀ x, AllInBounds (f32PayneAccesses x))





private theorem payne_indices_safe (raw : Nat) (hlo : 1043 ≤ raw) (hhi : raw ≤ 2046) :
    ∀ i ∈ payneHanekIndices raw, 1 ≤ i ∧ i ≤ 19 := by
  intro i hi
  simp only [payneHanekIndices] at hi
  split at hi
  · simp at hi
    rcases hi with rfl | rfl | rfl <;> omega
  · rw [List.mem_append] at hi
    rcases hi with hi | hi
    · split at hi
      · simp at hi
      · simp at hi
        omega
    · simp at hi
      rcases hi with rfl | rfl | rfl <;> omega

theorem payneHanekCallerInBounds : PayneHanekCallerInBounds := by
  constructor
  · intro x access ha
    simp only [f64PayneAccesses] at ha
    split at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      apply payne_indices_safe _ _ _ i hi
      · simp_all
        omega
      · simp_all
        omega
    · simp at ha
  · intro x access ha
    simp only [f32PayneAccesses] at ha
    split at ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      apply payne_indices_safe _ _ _ i hi
      · simp_all
        omega
      · simp_all
        omega
    · simp at ha

end JuliaLean.MemSafety.G2
