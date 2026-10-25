import JuliaLean.IOBuffers.WriteProofsPos

/-! `read(io, UInt8)`, `read(io, n)`, `read(io)` on a well-formed readable buffer. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

attribute [local irreducible] wrapInt

theorem addu_val (a b : U) : (a + b).val = wrapInt .u64 (a.val + b.val) := rfl

theorem take_min_length (l : List UInt8) (a : Nat) : l.take (min a l.length) = l.take a := by
  by_cases h : a ≤ l.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

theorem avail_length {x : IOBuf} (hw : Wf x) : ((avail x).length : Int) = x.size.val - x.ptr.val + 1 := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len
  unfold avail; exact slice_length _ _ _ (by omega) (by omega) (by omega)

theorem avail_adv {x : IOBuf} (hw : Wf x) (Q : I) (n : Nat) (hQ : Q.val = x.ptr.val + n)
    (hn : (n : Int) ≤ x.size.val - x.ptr.val + 1) : avail { x with ptr := Q } = (avail x).drop n := by
  have := hw.ptr_le; have := hw.ptr_ge
  unfold avail
  simp only []
  rw [hQ, slice_drop x.data x.ptr.val (x.ptr.val + n) x.size.val (by omega) (by omega) (by omega)]
  congr 1; omega

theorem readAt_avail {x : IOBuf} (hw : Wf x) (n : Nat) (hn : (n : Int) ≤ x.size.val - x.ptr.val + 1) :
    readAt x.data x.ptr n = .ok ((avail x).take n) := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len
  unfold readAt
  by_cases h0 : n = 0
  · rw [if_pos h0, h0]; simp
  · rw [if_neg h0, if_pos ⟨by omega, by omega⟩]
    unfold avail slice
    rw [List.take_take, show (x.ptr.val + n - 1 - x.ptr.val + 1).toNat = min n (x.size.val - x.ptr.val + 1).toNat by
      omega]

theorem toU_ok (n : Nat) (h : n ≤ 2 ^ 62) : ∃ v : U, toU n = .ok v ∧ v.val = n := by
  have hb : IntTy.u64.min ≤ (n : Int) ∧ (n : Int) ≤ IntTy.u64.max := by
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  exact ⟨⟨n, hb⟩, by simp [toU, JInt.convert, hb], rfl⟩

theorem unsafeRead_spec {x : IOBuf} (hw : Wf x) (hrd : x.readable = true) (nb : U) (n : Nat)
    (hnb : nb.val = n) (hn : (n : Int) ≤ x.size.val - x.ptr.val + 1) :
    ∃ Q : I, (unsafeRead nb).run x = .ok ((avail x).take n) { x with ptr := Q } ∧ Q.val = x.ptr.val + n := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len
  have hb := bytesavailable_val hw
  unfold unsafeRead
  rw [get_bind]
  simp only [hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  generalize hA : JInt.rem .u64 (bytesavailable x) = A
  have hAv : A.val = x.size.val - x.ptr.val + 1 := by rw [← hA, rem_u64_val, hb]; exact wru _ (by omega) (by omega)
  generalize hD : uminU A nb = D
  have hDv : D.val = n := by rw [← hD, uminU_val, hAv, hnb]; omega
  rw [hDv, Int.toNat_natCast, readAt_avail hw n hn, lift_ok_bind]
  generalize hE : (JInt.rem .u64 x.ptr + D).val = E
  have hEv : E = x.ptr.val + n := by
    rw [← hE, addu_val, rem_u64_val, hDv, wru x.ptr.val (by omega) (by omega)]; exact wru _ (by omega) (by omega)
  obtain ⟨v, hv, hvv⟩ := toI_ok E (by omega) (by omega)
  rw [hv, lift_ok_bind, set_bind, if_neg (by rw [hnb, hAv]; omega), run_pure]
  exact ⟨v, rfl, by rw [hvv, hEv]⟩

theorem readBang_spec {x : IOBuf} (hw : Wf x) (hrd : x.readable = true) (n : Nat)
    (hn : (n : Int) ≤ x.size.val - x.ptr.val + 1) :
    ∃ Q : I, (readBang n).run x = .ok ((avail x).take n) { x with ptr := Q } ∧ Q.val = x.ptr.val + n := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len
  obtain ⟨v, hv, hvv⟩ := toU_ok n (by omega)
  unfold readBang
  rw [hv, lift_ok_bind]
  exact unsafeRead_spec hw hrd v n hvv hn

theorem readN_spec {x : IOBuf} (hw : Wf x) (hrd : x.readable = true) (n : Int) (h0 : 0 ≤ n)
    (h1 : n < 2 ^ 63) :
    ∃ Q : I, (readN (i n)).run x = .ok ((avail x).take n.toNat) { x with ptr := Q } ∧
      Q.val = x.ptr.val + min n (x.size.val - x.ptr.val + 1) := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len
  have hb := bytesavailable_val hw
  have hal := avail_length hw
  unfold readN
  rw [get_bind]
  simp only []
  generalize hN : imin (i n) (bytesavailable x) = N
  have hNv : N.val = min n (x.size.val - x.ptr.val + 1) := by
    rw [← hN, imin_val, hb, i_val, wr _ (by omega) (by omega)]
  rw [stringMemory_ok N (by omega), lift_ok_bind, List.length_replicate]
  obtain ⟨Q, hQ, hQv⟩ := readBang_spec hw hrd N.val.toNat (by omega)
  rw [hQ]
  refine ⟨Q, ?_, by rw [hQv]; omega⟩
  rw [show N.val.toNat = min n.toNat (avail x).length by omega, take_min_length]

theorem readAll_spec {x : IOBuf} (hw : Wf x) (hrd : x.readable = true) :
    ∃ Q : I, readAll.run x = .ok (avail x) { x with ptr := Q } ∧ Q.val = x.size.val + 1 := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len
  have hb := bytesavailable_val hw
  have hal := avail_length hw
  unfold readAll
  rw [get_bind, stringMemory_ok _ (by rw [hb]; omega), lift_ok_bind, List.length_replicate]
  obtain ⟨Q, hQ, hQv⟩ := readBang_spec hw hrd (bytesavailable x).val.toNat (by rw [hb]; omega)
  rw [hQ]
  refine ⟨Q, ?_, by rw [hQv, hb]; omega⟩
  rw [List.take_of_length_le (by rw [hb]; omega)]

theorem readByte_eof {x : IOBuf} (hw : Wf x) (hrd : x.readable = true) (h : avail x = []) :
    readByte.run x = .error .eofError x := by
  have hal := avail_length hw
  rw [h] at hal
  unfold readByte
  rw [get_bind]
  simp only [hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [if_pos (by simp at hal; omega)]
  rfl

theorem readByte_some {x : IOBuf} (hw : Wf x) (hrd : x.readable = true) (b : UInt8) (rest : List UInt8)
    (h : avail x = b :: rest) :
    ∃ Q : I, readByte.run x = .ok b { x with ptr := Q } ∧ Q.val = x.ptr.val + 1 := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len
  have hal := avail_length hw
  rw [h] at hal; simp at hal
  unfold readByte
  rw [get_bind]
  simp only [hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [if_neg (by omega), readAt_avail hw 1 (by omega), lift_ok_bind, set_bind, run_pure, h]
  refine ⟨_, rfl, ?_⟩
  rw [add_val, i1]; exact wr _ (by omega) (by omega)

end WriteP
end JuliaLean.IOBuffers
