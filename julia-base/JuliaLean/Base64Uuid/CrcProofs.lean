import JuliaLean.Base64Uuid.Props
import JuliaLean.Base64Uuid.BitLemmas

/-!
CRC-32c: chunked checksums equal the checksum of the concatenation, the generic vector
method's 24576-byte blocks do not change the result, and the `IO` methods checksum
exactly the bytes they consume.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

theorem bxor_ff_ff (x : U32) :
    bxor (bxor x (JInt.lit .u32 0xffffffff)) (JInt.lit .u32 0xffffffff) = x := by
  apply vn_inj uns_u32
  rw [vn_bxor uns_u32, vn_bxor uns_u32, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem jl_crc32c_append (crc : U32) (a b : List Byte) :
    jl_crc32c (jl_crc32c crc a) b = jl_crc32c crc (a ++ b) := by
  simp only [jl_crc32c, bxor_ff_ff, List.foldl_append]

theorem jl_crc32c_nil (crc : U32) : jl_crc32c crc [] = crc := by
  simp only [jl_crc32c, List.foldl_nil, bxor_ff_ff]

theorem crcBlocks_eq : ∀ (fuel : Nat) (crc : U32) (rem : List Byte), rem.length < fuel →
    crcBlocks fuel crc rem = jl_crc32c crc rem
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, crc, rem, h => by
    simp only [crcBlocks]
    split
    · rw [crcBlocks_eq fuel _ _ (by simp only [List.length_drop]; omega), jl_crc32c_append,
        List.take_append_drop]
    · have : rem = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rw [jl_crc32c_nil]

theorem crc32cVec_eq (a : List Byte) (crc : U32) : crc32cVec a crc = crc32cDense a crc :=
  crcBlocks_eq _ _ _ (Nat.lt_succ_self _)

theorem crc32cChunks_proven : Crc32cChunks := by
  intro a b crc
  refine ⟨jl_crc32c_append crc a b, ?_, crc32cVec_eq a crc⟩
  rw [crc32cVec_eq, crc32cVec_eq, crc32cVec_eq]
  exact jl_crc32c_append crc a b

/-- The read loop of `_crc32c(io, nb, crc)` consumes a prefix of the stream and
checksums it; it stops at the end of the stream or once at most one block is left. -/
theorem crcIoLoop_spec : ∀ (fuel blen : Nat) (io : List Byte) (nb : Int) (crc : U32),
    io.length < fuel → 0 ≤ nb → (nb ≤ 24576 ∨ blen = 24576) →
    ∃ pre, io = pre ++ (crcIoLoop fuel blen io nb crc).1 ∧
      (crcIoLoop fuel blen io nb crc).2.1 = nb - pre.length ∧
      (crcIoLoop fuel blen io nb crc).2.2 = jl_crc32c crc pre ∧
      ((crcIoLoop fuel blen io nb crc).1 = [] ∨ (crcIoLoop fuel blen io nb crc).2.1 ≤ 24576) ∧
      0 ≤ (crcIoLoop fuel blen io nb crc).2.1 ∧
      (nb ≤ 24576 → pre = [])
  | 0, _, _, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, blen, io, nb, crc, h, h0, hb => by
    simp only [crcIoLoop]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        decide_eq_true_eq] at hc
      obtain ⟨hne, hnb⟩ := hc
      have hblen : blen = 24576 := by omega
      subst hblen
      have hlen : 0 < io.length := List.length_pos_iff.mpr hne
      obtain ⟨pre, hio, hnb', hcrc, hend, hpos, _⟩ := crcIoLoop_spec fuel 24576
        (io.drop (min 24576 io.length)) (nb - (min 24576 io.length : Nat))
        (jl_crc32c crc (io.take (min 24576 io.length)))
        (by simp only [List.length_drop]; omega) (by omega) (Or.inr rfl)
      refine ⟨io.take (min 24576 io.length) ++ pre, ?_, ?_, ?_, hend, hpos, fun h => by omega⟩
      · rw [List.append_assoc, ← hio, List.take_append_drop]
      · rw [hnb', List.length_append, List.length_take]; omega
      · rw [hcrc, jl_crc32c_append]
    · rename_i hc
      refine ⟨[], by simp, by simp, by rw [jl_crc32c_nil], ?_, h0, fun _ => rfl⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        decide_eq_true_eq, not_and] at hc
      by_cases hio : io = []
      · exact Or.inl hio
      · exact Or.inr (by have := hc hio; show nb ≤ 24576; omega)

theorem take_min_length (l : List Byte) (k : Nat) : l.take (min k l.length) = l.take k := by
  by_cases h : k ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

theorem drop_min_length (l : List Byte) (k : Nat) : l.drop (min k l.length) = l.drop k := by
  by_cases h : k ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.drop_length, List.drop_of_length_le (by omega)]

theorem take_pre_append (pre rest : List Byte) (k : Nat) :
    (pre ++ rest).take (pre.length + k) = pre ++ rest.take k := by
  induction pre with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, List.length_cons, Nat.add_right_comm, List.take_succ_cons, ih]

theorem drop_pre_append (pre rest : List Byte) (k : Nat) :
    (pre ++ rest).drop (pre.length + k) = rest.drop k := by
  induction pre with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, List.length_cons, Nat.add_right_comm, List.drop_succ_cons, ih]

theorem crc32cIoNb_eq (io : List Byte) (nb : Int) (crc : U32) (h0 : 0 ≤ nb) :
    crc32cIoNb io nb crc = .ok (crc32cDense (io.take nb.toNat) crc, io.drop nb.toNat) := by
  simp only [crc32cIoNb]
  have hn0 : ¬ nb < 0 := by omega
  simp only [hn0, ↓reduceIte]
  have hbl : nb ≤ 24576 ∨ (min nb 24576).toNat = 24576 := by omega
  obtain ⟨pre, hio, hnb', hcrc, hend, hpos, hnone⟩ :=
    crcIoLoop_spec (io.length + 1) ((min nb 24576).toNat) io nb crc (by omega) h0 hbl
  generalize crcIoLoop (io.length + 1) ((min nb 24576).toNat) io nb crc = r at hio hnb' hcrc hend hpos
  obtain ⟨io', nb', crc'⟩ := r
  simp only at hio hnb' hcrc hend hpos ⊢
  -- the final read is `min(nb', length(buf))` bytes, which is `nb'` bytes or the rest
  have hn : min (min nb' ((min nb 24576).toNat : Int)).toNat io'.length = min nb'.toNat io'.length := by
    rcases hend with he | he
    · subst he; simp
    · by_cases hs : nb ≤ 24576
      · have := hnone hs; subst this; simp at hnb'; omega
      · omega
  have hk : nb.toNat = pre.length + nb'.toNat := by omega
  rw [hn, take_min_length, drop_min_length, hcrc]
  simp only [crc32cDense]
  rw [jl_crc32c_append, hk, hio, take_pre_append, drop_pre_append]

theorem crc32cIo_proven : Crc32cIo := by
  intro io nb crc h0
  refine ⟨crc32cIoNb_eq io nb crc h0, fun hl => ?_⟩
  simp only [crc32cIo]
  rw [crc32cIoNb_eq io typemaxI64 crc (by decide)]
  have : io.length ≤ typemaxI64.toNat := by simp only [typemaxI64]; omega
  rw [List.take_of_length_le this, List.drop_of_length_le this]

end JuliaLean.Base64Uuid
