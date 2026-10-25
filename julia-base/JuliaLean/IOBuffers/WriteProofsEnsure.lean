import JuliaLean.IOBuffers.WriteProofsBasic

/-! `getUsedSpan`, `compact`, `resize` and `ensureroom` on well-formed buffers. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

/-- Bounds that keep the buffer-management arithmetic free of wrapping; weaker than `Inv`
so that it survives compaction. -/
structure Wf (io : IOBuf) : Prop where
  ms : 0 ≤ io.maxsize.val
  len : io.data.length ≤ 2 ^ 62
  ocl : io.size.val - io.oc.val ≤ 2 ^ 62 + 2 ^ 61
  seek : io.seekable = true → 0 ≤ io.oc.val
  off_size : max 0 io.oc.val ≤ io.size.val
  size_len : io.size.val ≤ io.data.length
  ptr_ge : max 0 io.oc.val + 1 ≤ io.ptr.val
  ptr_le : io.ptr.val ≤ io.size.val + 1
  stored : io.size.val - max 0 io.oc.val ≤ io.maxsize.val
  mark_ge : -1 ≤ io.mark.val
  mark_le : io.mark.val ≤ 2 ^ 62
  mark_pipe : io.seekable = false → 0 ≤ io.mark.val →
    io.mark.val ≤ io.ptr.val - io.oc.val - 1 ∧ max 0 io.oc.val ≤ io.mark.val + io.oc.val

theorem position_val {io : IOBuf} (h : -2 ^ 63 + 1 ≤ io.ptr.val - io.oc.val ∧ io.ptr.val - io.oc.val ≤ 2 ^ 63 - 1) :
    (position io).val = io.ptr.val - io.oc.val - 1 := by
  simp only [position]; wrg

theorem wf_of_inv {io : IOBuf} (h : Inv io) : Wf io := by
  have h1 := off_val io
  have p1 := h.mark_pipe
  have hp := h.ptr_ge; have hl := h.len_le; have hz := h.size_le_len; have hq := h.ptr_le
  have ho := h.oc_ge; have hs0 := h.off_le_size
  rw [h1] at hp hs0
  rw [position_val (io := io) (by omega), h1] at p1
  refine ⟨h.maxsize_nonneg, h.len_le, by omega, h.oc_seekable, by omega, h.size_le_len,
    by omega, h.ptr_le, ?_, h.mark_ge, h.mark_le, p1⟩
  have := h.stored_le; rw [h1] at this; omega

/-- Start of the used span, `get_used_span(io)[1]`. -/
def ustart (io : IOBuf) : Int :=
  if io.seekable then max 0 io.oc.val + 1
  else if 0 ≤ io.mark.val then io.mark.val + io.oc.val + 1 else io.ptr.val

theorem ustart_ge {io : IOBuf} (hw : Wf io) : max 0 io.oc.val + 1 ≤ ustart io := by
  unfold ustart
  have := hw.mark_pipe; have := hw.ptr_ge
  split
  · omega
  · split
    · rename_i h1 h2; have := hw.mark_pipe (by simpa using h1) h2; omega
    · omega

theorem ustart_le {io : IOBuf} (hw : Wf io) : ustart io ≤ io.ptr.val := by
  unfold ustart
  have := hw.ptr_ge
  split
  · omega
  · split
    · rename_i h1 h2; have := hw.mark_pipe (by simpa using h1) h2; omega
    · omega
theorem tsp_eq {io : IOBuf} (h1 : -2 ^ 63 ≤ io.mark.val + io.oc.val + 1)
    (h2 : io.mark.val + io.oc.val + 1 ≤ 2 ^ 63 - 1) :
    translateSeekPosition io io.mark = i (io.mark.val + io.oc.val + 1) := by
  simp only [translateSeekPosition, clampToI]
  rw [if_neg (by omega), if_neg (by omega)]

theorem usedSpan_eq {io : IOBuf} (hw : Wf io) (hm : io.isMem = true) :
    getUsedSpan io = .ok (i (ustart io), io.size) := by
  have hl := hw.len; have hz := hw.size_len; have hp := hw.ptr_le; have hg := hw.ptr_ge
  have hz0 := hw.off_size; have ho := hw.ocl; have hk := hw.mark_le; have hk2 := hw.mark_ge
  unfold getUsedSpan ustart
  simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
  cases hs : io.seekable
  · simp only [Bool.false_eq_true, if_false]
    by_cases hmk : 0 ≤ io.mark.val
    · have hmp := hw.mark_pipe hs hmk
      rw [if_pos (by omega), if_pos hmk, tsp_eq (by omega) (by omega)]
      congr 2
      apply Subtype.ext
      rw [imin_val]; wrg; omega
    · rw [if_neg (by omega), if_neg hmk]
      congr 2
      apply Subtype.ext
      have := I.ge io.ptr; wrg
  · simp only [if_true]
    congr 2
    apply Subtype.ext
    wrg

theorem slice_length (d : List UInt8) (a b : Int) (h1 : 1 ≤ a) (h2 : a ≤ b + 1) (h3 : b ≤ d.length) :
    ((slice d a b).length : Int) = b - a + 1 := by
  simp only [slice, List.length_take, List.length_drop]
  omega

theorem getCompacted_val {io : IOBuf} (h : -(2 ^ 62 + 2 ^ 61) ≤ io.oc.val) :
    (getCompacted io).val = max 0 (-io.oc.val) := by
  have := I.le io.oc
  simp only [getCompacted]; wrg

theorem rangeLength_val (a b : I) (h : a.val ≤ b.val + 1) (h1 : 0 ≤ a.val) (h2 : b.val ≤ 2 ^ 62) :
    (rangeLength a b).val = b.val - a.val + 1 := by
  unfold rangeLength
  split
  · rename_i h3; rw [i0]; omega
  · wrg

theorem copyto_front (d src : List UInt8) (s L : I) (hL : 0 ≤ L.val) (h1 : L.val ≤ d.length)
    (h2 : 1 ≤ s.val) (h3 : s.val + L.val - 1 ≤ src.length) :
    copyto d (i 1) src s L = .ok (slice src s.val (s.val + L.val - 1) ++ d.drop L.val.toNat) := by
  unfold copyto
  by_cases h0 : L.val = 0
  · rw [if_pos h0, h0]; simp [slice] <;> omega
  · rw [if_neg h0, if_neg (by omega), if_pos (by rw [i1]; omega)]
    simp [i1]

/-- `io'` holds the used span of `io` shifted `δ` bytes towards the front. -/
structure Shift (io io' : IOBuf) (δ : Int) : Prop where
  isMem : io'.isMem = io.isMem
  reinit : io'.reinit = io.reinit
  readable : io'.readable = io.readable
  writable : io'.writable = io.writable
  seekable : io'.seekable = io.seekable
  append : io'.append = io.append
  maxsize : io'.maxsize = io.maxsize
  mark : io'.mark = io.mark
  ptr : io'.ptr.val = io.ptr.val - δ
  size : io'.size.val = io.size.val - δ
  oc : io'.oc.val = io.oc.val - δ
  dlo : 0 ≤ δ
  dhi : δ ≤ ustart io - 1
  bytes : slice io'.data (ustart io - δ) (io.size.val - δ) = slice io.data (ustart io) io.size.val
  size_len : io.size.val - δ ≤ io'.data.length

theorem Shift.refl {io : IOBuf} (hw : Wf io) : Shift io io 0 := by
  have := ustart_ge hw
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by omega, by omega, by omega, Int.le_refl _, by omega,
    by simp, by have := hw.size_len; omega⟩

theorem compact_spec {io : IOBuf} (hw : Wf io) (hm : io.isMem = true) :
    ∃ d io', compact.run io = .ok d io' ∧ Shift io io' (ustart io - 1) ∧
      io'.data.length = io.data.length := by
  have hl := hw.len; have hz := hw.size_len; have hp := hw.ptr_le; have hg := hw.ptr_ge
  have ho := hw.ocl; have hu1 := ustart_ge hw; have hu2 := ustart_le hw
  have ho' : -(2 ^ 62 + 2 ^ 61) ≤ io.oc.val := by have := hw.off_size; omega
  have hz0 := hw.off_size
  unfold compact
  rw [get_bind, usedSpan_eq hw hm, lift_ok_bind]
  simp only []
  have hd : (i (ustart io) - i 1).val = ustart io - 1 := by wrg
  by_cases hu : ustart io = 1
  · rw [if_pos (by rw [hd]; omega), run_pure]
    refine ⟨_, _, rfl, ?_, rfl⟩
    rw [hu]; simpa using Shift.refl hw
  · rw [if_neg (by rw [hd]; omega)]
    have hr := rangeLength_val (i (ustart io)) io.size (by wrg <;> omega) (by wrg <;> omega) (by omega)
    have hs : (i (ustart io) - i 1 + i 1).val = ustart io := by wrg <;> omega
    rw [copyto_front _ _ _ _ (by rw [hr]; wrg <;> omega) (by rw [hr]; wrg <;> omega) (by rw [hs]; omega)
      (by rw [hs, hr]; wrg <;> omega), lift_ok_bind, set_bind, run_pure]
    have hgc := getCompacted_val ho'
    have hsl := slice_length io.data (ustart io) io.size.val (by omega) (by omega) hz
    refine ⟨_, _, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, by omega, Int.le_refl _, ?_, ?_⟩, ?_⟩
    · show (io.ptr - (i (ustart io) - i 1)).val = _; wrg
    · show (io.size - (i (ustart io) - i 1)).val = _; wrg
    · show (-getCompacted io - (i (ustart io) - i 1 - getOffset io)).val = _
      rw [sub_val, neg_val, hgc, sub_val, off_val, hd]; wrg; omega
    · rw [hs, hr]
      simp only [i_val]
      rw [wr (ustart io) (by omega) (by omega)]
      have e1 : ustart io - (ustart io - 1) = 1 := by omega
      have e2 : ustart io + (io.size.val - ustart io + 1) - 1 = io.size.val := by omega
      rw [e1, e2]
      simp only [slice]
      simp only [Int.sub_self, Int.toNat_zero, List.drop_zero]
      rw [List.take_append_of_le_length (by simp only [slice] at hsl; omega)]
      apply List.take_of_length_le
      simp only [slice] at hsl; omega
    · rw [hs, hr]; simp only [List.length_append, List.length_drop]
      simp only [i_val]; rw [wr (ustart io) (by omega) (by omega)]
      have e2 : ustart io + (io.size.val - ustart io + 1) - 1 = io.size.val := by omega
      rw [e2]; omega
    · rw [hs, hr]; simp only [List.length_append, List.length_drop]
      simp only [i_val]; rw [wr (ustart io) (by omega) (by omega)]
      have e2 : ustart io + (io.size.val - ustart io + 1) - 1 = io.size.val := by omega
      rw [e2]; omega

theorem ustart_seek {io : IOBuf} (h : io.seekable = true) : ustart io = max 0 io.oc.val + 1 := by
  simp [ustart, h]

theorem ustart_mark {io : IOBuf} (h : io.seekable = false) (hm : 0 ≤ io.mark.val) :
    ustart io = io.mark.val + io.oc.val + 1 := by
  simp [ustart, h, hm]

theorem ustart_unmarked {io : IOBuf} (h : io.seekable = false) (hm : ¬ 0 ≤ io.mark.val) :
    ustart io = io.ptr.val := by
  simp [ustart, h, hm]

theorem ustart_shift {io io' : IOBuf} {δ : Int} (hw : Wf io) (hs : Shift io io' δ) :
    ustart io' = ustart io - δ := by
  have := hs.dlo; have := hs.dhi; have := ustart_ge hw
  cases h : io.seekable
  · have h' : io'.seekable = false := by rw [hs.seekable, h]
    by_cases hm : 0 ≤ io.mark.val
    · rw [ustart_mark h hm, ustart_mark h' (by rw [hs.mark]; exact hm), hs.mark, hs.oc]; omega
    · rw [ustart_unmarked h hm, ustart_unmarked h' (by rw [hs.mark]; exact hm), hs.ptr]
  · have h' : io'.seekable = true := by rw [hs.seekable, h]
    have := hw.seek h
    rw [ustart_seek h] at *; rw [ustart_seek h', hs.oc]; omega

theorem Shift.wf {io io' : IOBuf} {δ : Int} (hw : Wf io) (hs : Shift io io' δ)
    (hl : io'.data.length ≤ 2 ^ 62) : Wf io' := by
  have := hs.dlo; have := hs.dhi; have hu := ustart_ge hw; have hu2 := ustart_le hw
  have := hs.size_len; have := hw.ocl; have := hw.off_size; have := hw.ptr_ge; have := hw.ptr_le
  have := hw.stored; have := hw.mark_ge; have := hw.mark_le
  have e1 := hs.ptr; have e2 := hs.size; have e3 := hs.oc
  refine ⟨by rw [hs.maxsize]; exact hw.ms, hl, by omega, ?_, by omega, by omega, by omega, by omega,
    by rw [hs.maxsize]; omega, by rw [hs.mark]; omega, by rw [hs.mark]; omega, ?_⟩
  · intro h; rw [hs.seekable] at h
    have := hw.seek h; rw [ustart_seek h] at *; omega
  · intro h hm; rw [hs.seekable] at h; rw [hs.mark] at hm ⊢
    have := hw.mark_pipe h hm; rw [ustart_mark h hm] at *; omega

theorem bitLength_le (f n : Nat) : bitLength f n ≤ f := by
  induction f generalizing n with
  | zero => simp [bitLength]
  | succ f ih => simp only [bitLength]; split <;> (have := ih (n / 2); omega)

theorem mul_val (a b : I) : (a * b).val = wrapInt .i64 (a.val * b.val) := rfl

theorem overalloc_val (n : I) (h0 : 0 ≤ n.val) (h1 : n.val ≤ 2 ^ 62 + 2 ^ 61) :
    n.val ≤ (overallocation n).val ∧ (overallocation n).val ≤ n.val + n.val / 8 + 3 * 2 ^ 56 := by
  unfold overallocation
  have hn : ¬ n.val < 0 := by omega
  simp only [hn, ↓reduceIte]
  generalize hb : bitLength 64 n.val.toNat = b
  have hb64 : b ≤ 64 := hb ▸ bitLength_le 64 _
  have he : b * 7 / 8 ≤ 56 := by omega
  have hp1 := Nat.pow_le_pow_right (by decide : 2 > 0) he
  have hp0 := Nat.pow_le_pow_right (by decide : 2 > 0) (Nat.zero_le (b * 7 / 8))
  have hc : ((2 ^ (b * 7 / 8) : Nat) : Int) = (2 : Int) ^ (b * 7 / 8) := Int.natCast_pow 2 _
  generalize (2 : Int) ^ (b * 7 / 8) = x at *
  have hx1 : x ≤ 2 ^ 56 := by omega
  have hx0 : 1 ≤ x := by simp at hp0; omega
  have ht : n.val.tdiv 8 = n.val / 8 := Int.tdiv_eq_ediv_of_nonneg h0
  have hex : (i x * i 3 + i (n.val.tdiv 8)).val = x * 3 + n.val / 8 := by
    rw [ht, add_val, mul_val]; wrg <;> omega
  have him : imaxval.val = 2 ^ 63 - 1 := rfl
  rw [if_neg (by rw [sub_val, hex, him]; wrg <;> omega), add_val, hex]
  wrg <;> omega

theorem stringMemory_ok (n : I) (h : 0 ≤ n.val) : stringMemory n = .ok (List.replicate n.val.toNat 0) := by
  simp [stringMemory]; omega

theorem resize_spec {io : IOBuf} (hw : Wf io) (hm : io.isMem = true) (ns : I) (ex : Bool) (N : I)
    (hN : (if ex = true then ns else imin io.maxsize (overallocation ns)) = N) (hpos : 0 < N.val)
    (hL : io.size.val - ustart io + 1 ≤ N.val) :
    ∃ io', (resize ns ex).run io = .ok () io' ∧ Shift io io' (ustart io - 1) ∧
      (io'.data.length : Int) = N.val := by
  have hl := hw.len; have hz := hw.size_len; have hp := hw.ptr_le; have hg := hw.ptr_ge
  have ho := hw.ocl; have hu1 := ustart_ge hw; have hu2 := ustart_le hw
  have hz0 := hw.off_size
  have ho' : -(2 ^ 62 + 2 ^ 61) ≤ io.oc.val := by omega
  have hNle := I.le N
  unfold resize
  rw [get_bind]
  simp only [hN]
  rw [usedSpan_eq hw hm, lift_ok_bind]
  simp only [similarData, hm, if_true, stringMemory_ok N (by omega)]
  rw [lift_ok_bind, set_bind]
  rw [if_neg (by omega)]
  have hiu : (i (ustart io)).val = ustart io := by wrg <;> omega
  have hr := rangeLength_val (i (ustart io)) io.size (by omega) (by omega) (by omega)
  rw [hiu] at hr
  have hrep : List.replicate N.val.toNat (0 : UInt8) = slice io.data (ustart io) io.size.val ++
      (List.replicate N.val.toNat 0).drop (io.size.val - ustart io + 1).toNat →
      List.replicate N.val.toNat (0 : UInt8) = slice io.data (ustart io) io.size.val ++
      (List.replicate N.val.toNat 0).drop (io.size.val - ustart io + 1).toNat := id
  have hgc := getCompacted_val ho'
  have hsl := slice_length io.data (ustart io) io.size.val (by omega) (by omega) hz
  split
  rename_i h0
  rw [pure_bind']
  have : (io.size.val - ustart io + 1).toNat = 0 := by omega
  rw [hrep (by simp only [slice, this, List.take_zero, List.drop_zero, List.nil_append])]
  rotate_left
  rw [copyto_front _ _ _ _ (by omega) (by simp; omega) (by omega) (by omega), hiu, hr, lift_ok_bind]
  have e2 : ustart io + (io.size.val - ustart io + 1) - 1 = io.size.val := by omega
  rw [e2]
  all_goals
    refine ⟨_, run_set _ _, ⟨hm.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, by omega,
      Int.le_refl _, ?_, ?_⟩, ?_⟩
    · show (io.ptr - (i (ustart io) - i 1)).val = _; wrg <;> omega
    · show (rangeLength (i (ustart io)) io.size).val = _; rw [hr]; omega
    · show (-getCompacted io - (i (ustart io) - i 1 - getOffset io)).val = _
      rw [sub_val, neg_val, hgc, sub_val, off_val, sub_val, hiu]; wrg <;> omega
    · show slice (slice io.data (ustart io) io.size.val ++ _) _ _ = _
      have e1 : ustart io - (ustart io - 1) = 1 := by omega
      rw [e1]
      simp only [slice] at hsl ⊢
      simp only [Int.sub_self, Int.toNat_zero, List.drop_zero]
      rw [List.take_append_of_le_length (by omega)]
      apply List.take_of_length_le
      omega
    · show _ ≤ ((slice io.data (ustart io) io.size.val ++ _).length : Int)
      simp only [List.length_append, List.length_drop, List.length_replicate]; omega
    · show ((slice io.data (ustart io) io.size.val ++ _).length : Int) = _
      simp only [List.length_append, List.length_drop, List.length_replicate]; omega

end WriteP
end JuliaLean.IOBuffers
