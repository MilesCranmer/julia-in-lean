import JuliaLean.IOBuffers.WriteProofsRead

/-! Writes and reads on a `PipeBuffer`, step by step. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

attribute [local irreducible] wrapInt

/-- A writable `PipeBuffer` that received `T` bytes in total. -/
structure PInv (x : IOBuf) (T : Int) : Prop where
  wf : Wf x
  mem : x.isMem = true
  rd : x.readable = true
  wr : x.writable = true
  sk : x.seekable = false
  ap : x.append = true
  ri : x.reinit = false
  ms : x.maxsize.val = 2 ^ 63 - 1
  ocn : x.oc.val ≤ 0
  tot : x.size.val - x.oc.val = T
  tb : T ≤ 2 ^ 61 + 2 ^ 60

theorem wf_set {s : IOBuf} (hws : Wf s) (D : List UInt8) (Z : I) (hD : D.length = s.data.length)
    (hZ1 : s.size.val ≤ Z.val) (hZ2 : Z.val ≤ D.length) (hZ3 : Z.val - s.oc.val ≤ 2 ^ 62 + 2 ^ 61)
    (hZ4 : Z.val - max 0 s.oc.val ≤ s.maxsize.val) : Wf { s with data := D, size := Z } := by
  have := hws.len; have := hws.off_size; have := hws.ptr_ge; have := hws.ptr_le; have := hws.size_len
  exact ⟨hws.ms, by simp only []; omega, hZ3, hws.seek, by simp only []; omega, hZ2,
    hws.ptr_ge, by simp only []; omega, hZ4, hws.mark_ge, hws.mark_le, hws.mark_pipe⟩

theorem wf_adv {x : IOBuf} (hw : Wf x) (Q : I) (h1 : x.ptr.val ≤ Q.val) (h2 : Q.val ≤ x.size.val + 1) :
    Wf { x with ptr := Q } := by
  have := hw.ptr_ge
  refine ⟨hw.ms, hw.len, hw.ocl, hw.seek, hw.off_size, hw.size_len, by simp only []; omega, h2,
    hw.stored, hw.mark_ge, hw.mark_le, ?_⟩
  intro hs hm; have := hw.mark_pipe hs hm; simp only []; omega

theorem pinv_adv {x : IOBuf} {T : Int} (h : PInv x T) (Q : I) (h1 : x.ptr.val ≤ Q.val)
    (h2 : Q.val ≤ x.size.val + 1) : PInv { x with ptr := Q } T :=
  ⟨wf_adv h.wf Q h1 h2, h.mem, h.rd, h.wr, h.sk, h.ap, h.ri, h.ms, h.ocn, h.tot, h.tb⟩

theorem used_adv {x : IOBuf} (h : PInv x T) (hm : 0 ≤ x.mark.val) (Q : I) :
    used { x with ptr := Q } = used x := by
  unfold used
  rw [ustart_mark (io := { x with ptr := Q }) h.sk hm, ustart_mark h.sk hm]

/-- What the ensureroom step leaves for a pipe write of `n` bytes. -/
theorem pipe_room {x : IOBuf} {T : Int} (h : PInv x T) (n : Nat) (hn : n ≤ 2 ^ 60)
    (hT : T + n ≤ 2 ^ 61 + 2 ^ 60) :
    ∃ s δ, (ensureroom (u n)).run x = .ok () s ∧ Shift x s δ ∧ Wf s ∧
      s.size.val + n ≤ s.data.length ∧ st s = s.size.val := by
  have hw := h.wf
  have hz := hw.size_len; have hl := hw.len; have hoc := h.ocn; have htot := h.tot; have hms := h.ms
  have hzo := hw.off_size
  obtain ⟨s, δ, hens, hs, hl1, hl2, hR⟩ := ensure_spec hw h.mem h.wr h.ri n hn
  have hex : exr x = x.data.length - x.size.val := by
    unfold exr st; rw [h.ap]; simp only [↓reduceIte]; omega
  have hls : (s.data.length : Int) ≤ 2 ^ 62 := by
    rw [hex] at hl2; rcases hl2 with h1 | ⟨h1, h2⟩ | h1 <;> omega
  have hws := hs.wf hw (by omega)
  have hsts : st s = s.size.val := by unfold st; rw [hs.append, h.ap]; simp
  have hso := hs.oc; have hsz := hs.size; have := hs.dlo; have := hs.dhi; have hsm := hs.maxsize
  have hu1 := ustart_ge hw; have hu2 := ustart_le hw; have hpl := hw.ptr_le
  rw [hsts, hsm, hms] at hR
  refine ⟨s, δ, hens, hs, hws, ?_, hsts⟩
  rcases hR with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega

theorem pipe_wbytes {x : IOBuf} {T : Int} (h : PInv x T) (w : List UInt8) (hwl : w.length ≤ 2 ^ 60)
    (hT : T + w.length ≤ 2 ^ 61 + 2 ^ 60) :
    ∃ r x', (unsafeWrite w).run x = .ok r x' ∧ PInv x' (T + w.length) ∧ avail x' = avail x ++ w ∧
      x'.mark = x.mark ∧ used x' = used x ++ w := by
  have hw := h.wf
  obtain ⟨s, δ, hens, hs, hws, hroom, hsts⟩ := pipe_room h w.length hwl hT
  have hz := hws.size_len; have hl := hws.len; have hoc := h.ocn; have htot := h.tot
  have hso := hs.oc; have hsz := hs.size; have := hs.dlo; have := hs.dhi; have hsm := hs.maxsize
  have hzo := hws.off_size; have hpl := hws.ptr_le; have hpg := hws.ptr_ge; have hms := h.ms
  obtain ⟨r, D, Z, P, hrun, hrv, hD, hZ, hP⟩ :=
    uw_of w hwl hens (by omega) (by omega) hz (by omega) (by omega) (by rw [hsm]; omega) (by omega)
  have hk : kw s w.length = w.length := by unfold kw; rw [hsts, hsm, hms]; omega
  rw [hsts, hk] at hD hZ
  have hsap : s.append = true := by rw [hs.append, h.ap]
  rw [hsap] at hP; simp only [↓reduceIte] at hP
  have hPe : P = s.ptr := Subtype.ext hP
  subst hPe
  have hZv : Z.val = s.size.val + w.length := by rw [hZ]; omega
  have hDl : D.length = s.data.length := by
    rw [hD]; simp only [List.length_append, List.length_take, List.length_drop]; omega
  refine ⟨r, _, hrun, ⟨?_, hs.isMem.trans h.mem, hs.readable.trans h.rd, hs.writable.trans h.wr,
    hs.seekable.trans h.sk, hsap, hs.reinit.trans h.ri, (congrArg Subtype.val hsm).trans hms,
    by simp only []; omega, by simp only []; omega, hT⟩, ?_, hs.mark, ?_⟩
  · exact wf_set hws D Z hDl (by omega) (by omega) (by omega) (by rw [hsm]; omega)
  · rw [← avail_shift hw hs]
    unfold avail; simp only []
    rw [hD, hZv, slice_after_append _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by simp <;> omega)]
    simp
  · rw [← used_shift hw hs]
    have hu : ustart { s with data := D, size := Z, ptr := s.ptr } = ustart s := by
      unfold ustart; simp only []
    have hu1 := ustart_ge hws; have hu2 := ustart_le hws
    unfold used; rw [hu]; simp only []
    rw [hD, hZv, slice_after_append _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by simp <;> omega)]
    simp

theorem pipe_wbyte {x : IOBuf} {T : Int} (h : PInv x T) (b : UInt8) (hT : T + 1 ≤ 2 ^ 61 + 2 ^ 60) :
    ∃ x', (writeByte b).run x = .ok (i 1) x' ∧ PInv x' (T + 1) ∧ avail x' = avail x ++ [b] ∧
      x'.mark = x.mark ∧ used x' = used x ++ [b] := by
  have hw := h.wf
  obtain ⟨s, δ, hens, hs, hws, hroom, hsts⟩ := pipe_room h 1 (by decide) hT
  have hz := hws.size_len; have hl := hws.len; have hoc := h.ocn; have htot := h.tot
  have hso := hs.oc; have hsz := hs.size; have := hs.dlo; have := hs.dhi; have hsm := hs.maxsize
  have hzo := hws.off_size; have hpl := hws.ptr_le; have hpg := hws.ptr_ge; have hms := h.ms
  have hsap : s.append = true := by rw [hs.append, h.ap]
  have hens' : (ensureroom (u 1)).run x = .ok () s := hens
  obtain ⟨Z, hrun, hZv⟩ := wb_of b hens' hsap hzo (by omega) (by omega) (by rw [hsm]; omega)
  have hDl : (wbData s b).length = s.data.length := by
    unfold wbData; simp only [List.length_append, List.length_take, List.length_drop, List.length_singleton]
    omega
  refine ⟨_, hrun, ⟨?_, hs.isMem.trans h.mem, hs.readable.trans h.rd, hs.writable.trans h.wr,
    hs.seekable.trans h.sk, hsap, hs.reinit.trans h.ri, (congrArg Subtype.val hsm).trans hms,
    by simp only []; omega, by simp only []; omega, hT⟩, ?_, hs.mark, ?_⟩
  · exact wf_set hws (wbData s b) Z hDl (by omega) (by omega) (by omega) (by rw [hsm]; omega)
  · rw [← avail_shift hw hs]
    unfold avail; simp only []
    rw [hZv]; unfold wbData
    rw [slice_after_append _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by simp)]
  · rw [← used_shift hw hs]
    have hu : ustart { s with data := wbData s b, size := Z } = ustart s := by
      unfold ustart; simp only []
    have hu1 := ustart_ge hws; have hu2 := ustart_le hws
    unfold used; rw [hu]; simp only []
    rw [hZv]; unfold wbData
    rw [slice_after_append _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by simp)]

end WriteP
end JuliaLean.IOBuffers
