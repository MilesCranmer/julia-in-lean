import JuliaLean.IOBuffers.WriteProofsAt

/-! `WriteAtPosition` and `AppendWritesAtEnd`. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

attribute [local irreducible] wrapInt

theorem bytesavailable_val {io : IOBuf} (hw : Wf io) : (bytesavailable io).val = io.size.val - io.ptr.val + 1 := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len
  unfold bytesavailable; wrg <;> omega

theorem position_wf {io : IOBuf} (hw : Wf io) : (position io).val = io.ptr.val - io.oc.val - 1 := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len; have := hw.ocl
  exact position_val (by omega)

theorem held_eq {io : IOBuf} (hw : Wf io) : heldBytes io = io.size.val - (ustart io - 1) := by
  have hb := bytesavailable_val hw; have hp := position_wf hw
  unfold heldBytes
  cases hsk : io.seekable
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hmk : 0 ≤ io.mark.val
    · rw [if_pos (by simp [ismarked, hmk]), hp, hb, ustart_mark hsk hmk]; omega
    · rw [if_neg (by simp [ismarked]; omega), hb, ustart_unmarked hsk hmk]; omega
  · have := hw.off_size; have := hw.size_len; have := hw.len
    simp only [↓reduceIte, filesize, hsk]
    rw [ustart_seek hsk]; wrg <;> omega

theorem i_natCast_val (k : Nat) (h : (k : Int) ≤ 2 ^ 63 - 1) : (i (k : Int)).val = k := by
  rw [i_val]; exact wr _ (by omega) h

theorem writeAtPosition' (hinv : ∀ io, Reachable io → Inv io) : WriteAtPosition := by
  intro io hr hm hwr hsk hap w hwl0
  have hwl : w.length ≤ 2 ^ 60 := hwl0
  have hI := hinv io hr
  have hw := wf_of_inv hI
  have hpos := position_wf hw
  have hoc := hw.seek hsk; have hst := hw.stored; have hpl := hw.ptr_le; have hpg := hw.ptr_ge
  have hzl := hw.size_len; have hl := hw.len; have hms := hw.ms
  simp only []
  cases hre : io.reinit
  · obtain ⟨s, δ, hens, hroom⟩ := ensure_spec hw hm hwr hre w.length hwl
    obtain ⟨r, D, Z, P, hrun, hrv, hD, hZ, hP⟩ := uw_room hw w hwl hens hroom
    have hs := hroom.1
    have hsz := hs.size; have hsl := hs.size_len; have := hs.dlo
    have hK2 : st s + kw s w.length ≤ s.data.length := by unfold kw; omega
    have hsts : st s = io.ptr.val - 1 - δ := by
      rw [st_shift hs]; unfold st; rw [hap]; simp
    have hoffs : max 0 s.oc.val = io.oc.val - δ := by
      rw [hs.oc]; have := hs.dhi; rw [ustart_seek hsk] at this; omega
    have hsap : s.append = false := by rw [hs.append, hap]
    have hR := hroom.2.2.2
    rw [hs.maxsize, hsts, hoffs] at hR
    have hk : kw s w.length = min (w.length : Int) (io.maxsize.val - (position io).val) := by
      unfold kw; rw [hsts, hoffs, hs.maxsize, hpos]; rcases hR with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have hkn : ((min w.length (io.maxsize.val - (position io).val).toNat : Nat) : Int) = kw s w.length := by
      rw [hk]; omega
    have hPv := hP
    rw [hsap] at hPv; simp only [Bool.false_eq_true, ↓reduceIte] at hPv
    rw [hsts] at hPv hK2
    have hq : (position { s with data := D, size := Z, ptr := P }).val = P.val - s.oc.val - 1 := by
      apply position_val
      simp only []
      rw [hPv, hs.oc]; rw [hk] at hK2 ⊢; omega
    simp only [resultOf, stateOf, hrun]
    refine ⟨?_, ?_, ?_⟩
    · have hr' : r = i ↑(min w.length (io.maxsize.val - (position io).val).toNat) := by
        apply Subtype.ext
        rw [i_natCast_val (min w.length (io.maxsize.val - (position io).val).toNat) (by omega), hrv, hkn]
      rw [hr']
    · have hcs := content_shift hw hs hsk
      unfold content at hcs ⊢
      simp only [off_val] at hcs ⊢
      rw [← hcs, hD, hZ, hsts, hoffs]
      have e1 : io.ptr.val - 1 - δ = io.oc.val - δ + (position io).val := by omega
      rw [hk] at hK2
      rw [e1, slice_after_mid _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)
        (by rw [hk]; omega) (by rw [hk]; omega) (by simp; rw [hk]; omega)]
      rw [← hkn, Int.toNat_natCast,
        show ((position io).val + ↑(min w.length (io.maxsize.val - (position io).val).toNat)).toNat =
          (position io).val.toNat + min w.length (io.maxsize.val - (position io).val).toNat by omega]
    · rw [hq, hPv, hs.oc, hkn, hk, hpos]
      omega
  · obtain ⟨hp1, hz0, ho0⟩ := hI.reinit_state hre
    have hens := ensure_reinit hm hwr hre hms w.length hwl
    have hmv : (imin io.maxsize (JInt.rem .i64 (u w.length))).val = min io.maxsize.val w.length := by
      rw [imin_val, rem_i64_val, u_val, wru _ (by omega) (by omega), wr _ (by omega) (by omega)]
    have hgc : (-getCompacted io).val = 0 := by
      rw [neg_val, getCompacted_val (by omega), ho0, wr _ (by omega) (by omega)] <;> omega
    generalize hS : reallocState io w.length = s at hens
    have hsst : st s = 0 := by rw [← hS]; simp [reallocState, st, hap, hp1]
    have hsoc : s.oc.val = 0 := by rw [← hS]; exact hgc
    have hslen : (s.data.length : Int) = min io.maxsize.val w.length := by
      rw [← hS]; simp only [reallocState, List.length_replicate]; rw [hmv]; omega
    have hssz : s.size = io.size := by rw [← hS]; rfl
    have hsms : s.maxsize = io.maxsize := by rw [← hS]; rfl
    have hsap : s.append = false := by rw [← hS]; exact hap
    obtain ⟨r, D, Z, P, hrun, hrv, hD, hZ, hP⟩ := uw_of w hwl hens (by omega) (by rw [hssz]; omega)
      (by rw [hssz, hslen]; omega) (by rw [hslen]; omega) (by rw [hsoc]; omega)
      (by rw [hsoc, hsms]; omega) (by rw [hssz]; omega)
    have hk : kw s w.length = min (w.length : Int) io.maxsize.val := by
      unfold kw; rw [hsst, hslen, hsoc, hsms]; omega
    have hpz : (position io).val = 0 := by rw [hpos]; omega
    have hkn : ((min w.length (io.maxsize.val - (position io).val).toNat : Nat) : Int) = kw s w.length := by
      rw [hk, hpz]; omega
    have hc0 : content io = [] := by
      unfold content; rw [off_val, ho0, hz0]; simp [slice]
    have hPv := hP
    rw [hsap] at hPv; simp only [Bool.false_eq_true, ↓reduceIte] at hPv
    rw [hsst] at hPv
    have hq : (position { s with data := D, size := Z, ptr := P }).val = P.val - s.oc.val - 1 := by
      apply position_val
      simp only []
      rw [hPv, hsoc, hk]; omega
    simp only [resultOf, stateOf, hrun]
    refine ⟨?_, ?_, ?_⟩
    · have hr' : r = i ↑(min w.length (io.maxsize.val - (position io).val).toNat) := by
        apply Subtype.ext
        rw [i_natCast_val (min w.length (io.maxsize.val - (position io).val).toNat) (by omega), hrv, hkn]
      rw [hr']
    · rw [hc0]
      simp only [List.take_nil, List.drop_nil, List.nil_append, List.append_nil]
      have hkw : min w.length (io.maxsize.val - (position io).val).toNat ≤ w.length := Nat.min_le_left _ _
      generalize min w.length (io.maxsize.val - (position io).val).toNat = k at hkn hkw ⊢
      unfold content
      simp only [off_val]
      rw [hsoc, hD, hZ, hsst, ← hkn, hssz, hz0, show max (0 : Int) 0 + 1 = 1 by omega,
        show max (0 : Int) (0 + ↑k) = 0 + ↑k by omega,
        slice_after_append _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by simp; omega)]
      simp [slice]
    · rw [hq, hPv, hsoc, hkn, hk, hpz]
      omega

end WriteP
end JuliaLean.IOBuffers
