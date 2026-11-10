import JuliaLean.Proofs.Compiler.src.optimize.EncodingChunks

/-!
Facts about the 8-bit inlining-cost encoding of `src/ircode.c` (`jl_encode_inlining_cost`,
`jl_decode_inlining_cost`), checked by kernel evaluation over every `UInt16` and every `UInt8`.
The exhaustive `UInt16` check is in `EncodingChunks.lean`.
-/

namespace JuliaLean.Proofs.Compiler.src.optimize

open JuliaLean JuliaLean.Compiler JuliaLean.Compiler.Optimize

theorem encFacts_chunks : ∀ k, k < 16 → allTree encFacts 12 (k * 4096) = true := by
  intro k hk
  match k, hk with
  | 0, _ => exact encFacts_c0
  | 1, _ => exact encFacts_c1
  | 2, _ => exact encFacts_c2
  | 3, _ => exact encFacts_c3
  | 4, _ => exact encFacts_c4
  | 5, _ => exact encFacts_c5
  | 6, _ => exact encFacts_c6
  | 7, _ => exact encFacts_c7
  | 8, _ => exact encFacts_c8
  | 9, _ => exact encFacts_c9
  | 10, _ => exact encFacts_c10
  | 11, _ => exact encFacts_c11
  | 12, _ => exact encFacts_c12
  | 13, _ => exact encFacts_c13
  | 14, _ => exact encFacts_c14
  | 15, _ => exact encFacts_c15
  | k + 16, h => exact absurd h (by omega)

theorem encFacts_of (c : UInt16) : encFacts c.toNat = true := by
  have hc := c.toNat_lt
  have hk : c.toNat / 4096 < 16 := by simp at hc; omega
  exact allTree_spec encFacts 12 _ (encFacts_chunks _ hk) c.toNat (by omega) (by simp; omega)

theorem ofNat_toNat16 (c : UInt16) : UInt16.ofNat c.toNat = c := UInt16.ofNat_toNat

/-- Below 3969 the decoded cost rounds the input up, by at most 1/32. -/
theorem dec_enc_ge (c : UInt16) (h : c.toNat ≤ 3968) :
    c.toNat ≤ (jlDecodeInliningCost (jlEncodeInliningCost c)).toNat ∧
    (jlDecodeInliningCost (jlEncodeInliningCost c)).toNat * 32 ≤ c.toNat * 33 := by
  have := encFacts_of c
  simp only [encFacts, ofNat_toNat16, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1.1 h, this.1.1.1.2 h⟩

/-- Above 3968 the decoded cost is `MAX_INLINE_COST`. -/
theorem dec_enc_big (c : UInt16) (h : 3968 < c.toNat) :
    (jlDecodeInliningCost (jlEncodeInliningCost c)).toNat = 65535 := by
  have := encFacts_of c
  simp only [encFacts, ofNat_toNat16, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1.2 h

/-- Below 64 the encoding is exact. -/
theorem dec_enc_small (c : UInt16) (h : c.toNat < 64) :
    (jlDecodeInliningCost (jlEncodeInliningCost c)).toNat = c.toNat := by
  have := encFacts_of c
  simp only [encFacts, ofNat_toNat16, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.2 h

theorem enc_succ (n : Nat) (h : n < 65535) : encN n ≤ encN (n + 1) := by
  have := encFacts_of (UInt16.ofNat n)
  have hn : (UInt16.ofNat n).toNat = n := by simp [UInt16.toNat_ofNat]; omega
  rw [hn] at this
  simp only [encFacts, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this.2 with h' | h'
  · omega
  · exact h'

theorem encN_mono (a b : Nat) (hab : a ≤ b) (hb : b ≤ 65535) : encN a ≤ encN b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    by_cases h : a = b + 1
    · subst h; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) (by omega)) (enc_succ b (by omega))

/-- `jl_encode_inlining_cost` is monotone. -/
theorem enc_mono (c d : UInt16) (h : c ≤ d) :
    (jlEncodeInliningCost c).toNat ≤ (jlEncodeInliningCost d).toNat := by
  have h' : c.toNat ≤ d.toNat := h
  have := encN_mono c.toNat d.toNat h' (by have := d.toNat_lt; omega)
  simpa [encN, ofNat_toNat16] using this

/-- The facts checked at each byte `n`: `enc (dec n) = n`, and `dec n < dec (n + 1)`. -/
def decFacts (n : Nat) : Bool :=
  encN (decN n) == n && (n == 255 || decN n < decN (n + 1))

theorem decFacts_all : allTree decFacts 8 0 = true := by decide +kernel

theorem decFacts_of (n : Nat) (h : n < 256) : decFacts n = true :=
  allTree_spec decFacts 8 0 decFacts_all n (Nat.zero_le _) (by simpa using h)

/-- `jl_encode_inlining_cost(jl_decode_inlining_cost(b)) == b` for every byte. -/
theorem enc_dec (b : UInt8) : jlEncodeInliningCost (jlDecodeInliningCost b) = b := by
  have := decFacts_of b.toNat b.toNat_lt
  simp only [decFacts, encN, decN, UInt8.ofNat_toNat, Bool.and_eq_true, beq_iff_eq] at this
  have h1 := this.1
  have e : UInt16.ofNat (jlDecodeInliningCost b).toNat = jlDecodeInliningCost b := UInt16.ofNat_toNat
  rw [e] at h1
  exact UInt8.toNat_inj.mp h1

theorem decN_succ (n : Nat) (h : n < 255) : decN n < decN (n + 1) := by
  have := decFacts_of n (by omega)
  simp only [decFacts, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this.2 with h' | h'
  · omega
  · exact h'

theorem dec_mono_nat (a b : Nat) (hab : a ≤ b) (hb : b ≤ 255) : decN a ≤ decN b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ b ih =>
    by_cases h : a = b + 1
    · subst h; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_of_lt (decN_succ b (by omega)))

/-- `jl_decode_inlining_cost` is monotone. -/
theorem dec_mono (a b : UInt8) (h : a.toNat ≤ b.toNat) :
    (jlDecodeInliningCost a).toNat ≤ (jlDecodeInliningCost b).toNat := by
  have := dec_mono_nat a.toNat b.toNat h (by have := b.toNat_lt; omega)
  simpa [decN, UInt8.ofNat_toNat] using this

/-- `dec(254) = 3968` is the largest finite decoded cost and `dec(255) = 0xffff`. -/
theorem dec_top : (jlDecodeInliningCost 254).toNat = 3968 ∧ (jlDecodeInliningCost 255).toNat = 65535 := by
  decide

end JuliaLean.Proofs.Compiler.src.optimize
