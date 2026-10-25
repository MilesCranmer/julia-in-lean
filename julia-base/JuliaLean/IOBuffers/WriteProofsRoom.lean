import JuliaLean.IOBuffers.WriteProofsEnsure

/-! `ensureroom` on a well-formed writable `IOBuffer`. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

/-- Index before the first byte a write stores. -/
def st (io : IOBuf) : Int := if io.append then io.size.val else io.ptr.val - 1

/-- Room `ensureroom` measures, `existing` in `base/iobuffer.jl:611`. -/
def exr (io : IOBuf) : Int := min (io.data.length - st io) (io.maxsize.val - (st io - max 0 io.oc.val))

/-- `start` in `ensureroom`. -/
def startI (io : IOBuf) : I := if io.append then io.size else io.ptr - i 1

/-- `existing` in `ensureroom`. -/
def existingI (io : IOBuf) : I :=
  imin (i io.data.length - startI io) (io.maxsize - (startI io - getOffset io))

theorem ensureroom_eq (nb : U) : ensureroom nb = (do
    let io ← get
    if !io.writable || io.reinit then ensureroomReallocate nb
    else if (existingI io).val < (JInt.rem .i64 nb).val then ensureroomSlowpath nb (existingI io)
    else pure ()) := rfl

theorem startI_val {io : IOBuf} (hw : Wf io) : (startI io).val = st io := by
  have := hw.ptr_ge; have := hw.ptr_le; have := hw.size_len; have := hw.len
  unfold startI st
  cases io.append <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> wrg

theorem st_bounds {io : IOBuf} (hw : Wf io) : max 0 io.oc.val ≤ st io ∧ st io ≤ io.size.val := by
  have := hw.ptr_ge; have := hw.ptr_le; have := hw.off_size
  unfold st; cases io.append <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem existingI_val {io : IOBuf} (hw : Wf io) : (existingI io).val = exr io := by
  have := hw.ptr_ge; have := hw.ptr_le; have := hw.size_len; have := hw.len; have := hw.off_size
  have := hw.stored; have := hw.ms; have := I.le io.maxsize
  have h1 := startI_val hw; have h2 := st_bounds hw
  unfold existingI exr
  rw [imin_val, sub_val, sub_val, sub_val, h1, off_val]
  wrg <;> omega

theorem exr_bounds {io : IOBuf} (hw : Wf io) : 0 ≤ exr io ∧ exr io ≤ io.data.length - st io := by
  have := hw.size_len; have := hw.stored; have h2 := st_bounds hw
  unfold exr; omega

theorem st_shift {io io' : IOBuf} {δ : Int} (hs : Shift io io' δ) : st io' = st io - δ := by
  unfold st; rw [hs.append, hs.size, hs.ptr]; cases io.append <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem Shift.trans {io io1 io2 : IOBuf} {d1 d2 : Int} (hw : Wf io) (h1 : Shift io io1 d1)
    (h2 : Shift io1 io2 d2) : Shift io io2 (d1 + d2) := by
  have hu := ustart_shift hw h1
  have := h2.dhi; have := h1.dhi; have := h1.dlo; have := h2.dlo
  have hb := h2.bytes; rw [hu, h1.size] at hb
  have e1 : ustart io - d1 - d2 = ustart io - (d1 + d2) := by omega
  have e2 : io.size.val - d1 - d2 = io.size.val - (d1 + d2) := by omega
  rw [e1, e2, h1.bytes] at hb
  have hsl := h2.size_len; rw [h1.size, e2] at hsl
  refine ⟨by rw [h2.isMem, h1.isMem], by rw [h2.reinit, h1.reinit], by rw [h2.readable, h1.readable],
    by rw [h2.writable, h1.writable], by rw [h2.seekable, h1.seekable], by rw [h2.append, h1.append],
    by rw [h2.maxsize, h1.maxsize], by rw [h2.mark, h1.mark], by rw [h2.ptr, h1.ptr]; omega,
    by rw [h2.size, h1.size]; omega, by rw [h2.oc, h1.oc]; omega, by omega, by omega, hb, hsl⟩

theorem discard_ok {α} {x : M α} {s s' : IOBuf} {a : α} (h : x.run s = .ok a s') :
    (discard x : M PUnit).run s = .ok () s' := by
  show EStateM.map (fun _ => PUnit.unit) x s = _
  unfold EStateM.map
  rw [show x s = _ from h]

theorem toI_ok (x : Int) (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) : ∃ v : I, toI x = .ok v ∧ v.val = x := by
  have hb : IntTy.i64.min ≤ x ∧ x ≤ IntTy.i64.max := by
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  exact ⟨⟨x, hb⟩, by simp [toI, JInt.convert, hb], rfl⟩

/-- What `ensureroom(io, n)` leaves behind: the used span, shifted `δ` bytes to the front,
and room for the write (`n` bytes, or as much as `maxsize` allows after a full compaction). -/
def Room (io io' : IOBuf) (δ : Int) (n : Nat) : Prop :=
  Shift io io' δ ∧ (io'.data.length : Int) ≤ 2 ^ 63 - 1 ∧
  (io'.data.length = io.data.length ∨
    ((io'.data.length : Int) = io.maxsize.val ∧ io.data.length + n - exr io > io.maxsize.val) ∨
    (io'.data.length : Int) ≤ (io.data.length + n - exr io) + (io.data.length + n - exr io) / 8 + 3 * 2 ^ 56) ∧
  ((n ≤ io'.data.length - st io' ∧ n ≤ io'.maxsize.val - (st io' - max 0 io'.oc.val)) ∨
   (δ = ustart io - 1 ∧ min (n : Int) (io'.maxsize.val - (st io' - max 0 io'.oc.val)) ≤ io'.data.length - st io'))

/-- The end of `ensureroom_slowpath` when `maxsize` limits the buffer. -/
def resizeTail : M Unit := do
  let io ← get
  if (io.data.length : Int) < io.maxsize.val then resize io.maxsize true else pure ()

theorem slowpath_eq (nb : U) (available : I) : ensureroomSlowpath nb available = (do
    let io ← get
    let (a, _) ← lift (getUsedSpan io)
    let reclaimable := a - i 1
    if reclaimable.val ≥ 32 ∧ reclaimable.val ≥ (io.data.length / 8 : Nat) ∧
        (JInt.rem .u64 (reclaimable + available)).val ≥ nb.val then
      let _ ← compact
      return
    let n ← lift (toI nb.val)
    let desired := i io.data.length + n - available
    if desired.val > io.maxsize.val then
      if reclaimable.val ≠ 0 then do discard compact; resizeTail
      else resizeTail
    else resize desired false) := rfl

theorem tail_spec {io x : IOBuf} (hw : Wf io) (hm : io.isMem = true) (n : Nat)
    (hx : Shift io x (ustart io - 1)) (hxl : x.data.length = io.data.length)
    (hbig : io.data.length + n - exr io > io.maxsize.val) :
    ∃ io' δ', resizeTail.run x = .ok () io' ∧ Room io io' δ' n := by
  have hwx := hx.wf hw (by rw [hxl]; exact hw.len)
  have hus := ustart_shift hw hx
  have hstx := st_shift hx
  have hu1 := ustart_ge hw; have hu2 := ustart_le hw; have hst := hw.stored
  have hxo : max 0 x.oc.val = 0 := by rw [hx.oc]; omega
  have hxm := hx.maxsize
  unfold resizeTail
  rw [get_bind]
  by_cases hlt : (x.data.length : Int) < x.maxsize.val
  · rw [if_pos hlt]
    obtain ⟨y, hy, hsy, hyl⟩ := resize_spec hwx (by rw [hx.isMem]; exact hm) x.maxsize true x.maxsize
      (by simp) (by omega) (by rw [hus, hx.size, hxm]; omega)
    have hsxy := Shift.trans hw hx hsy
    have e : ustart io - 1 + (ustart x - 1) = ustart io - 1 := by rw [hus]; omega
    rw [e] at hsxy
    have h3 := st_shift hsxy
    have h4 : max 0 y.oc.val = 0 := by rw [hsxy.oc]; omega
    refine ⟨y, _, hy, hsxy, by rw [hyl]; exact I.le _, Or.inr (Or.inl ⟨by rw [hyl, hxm], hbig⟩),
      Or.inr ⟨rfl, ?_⟩⟩
    rw [hyl, hsxy.maxsize, hxm, h4]; omega
  · rw [if_neg hlt, run_pure]
    refine ⟨x, _, rfl, hx, by rw [hxl]; have := hw.len; omega, Or.inl hxl, Or.inr ⟨rfl, ?_⟩⟩
    rw [hxm] at hlt ⊢; rw [hxo]; omega

theorem ensure_spec {io : IOBuf} (hw : Wf io) (hm : io.isMem = true) (hwr : io.writable = true)
    (hr : io.reinit = false) (n : Nat) (hn : n ≤ 2 ^ 60) :
    ∃ io' δ, (ensureroom (u n)).run io = .ok () io' ∧ Room io io' δ n := by
  have hl := hw.len
  have hsb := st_bounds hw; have heb := exr_bounds hw; have hev := existingI_val hw
  have hun : (u n).val = n := by rw [u_val]; exact wru _ (by omega) (by omega)
  have hrn : (JInt.rem .i64 (u n)).val = n := by rw [rem_i64_val, hun]; exact wr _ (by omega) (by omega)
  rw [ensureroom_eq, get_bind]
  simp only [hwr, hr, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  by_cases hfast : (n : Int) ≤ exr io
  · rw [if_neg (by rw [hev, hrn]; omega), run_pure]
    refine ⟨io, 0, rfl, Shift.refl hw, by omega, Or.inl rfl, Or.inl ⟨?_, ?_⟩⟩ <;> unfold exr at hfast <;> omega
  rw [if_pos (by rw [hev, hrn]; omega)]
  rw [slowpath_eq, get_bind, usedSpan_eq hw hm, lift_ok_bind]
  simp only []
  have hu1 := ustart_ge hw; have hu2 := ustart_le hw
  have hp := hw.ptr_le; have hz := hw.size_len
  have hd : (i (ustart io) - i 1).val = ustart io - 1 := by wrg <;> omega
  have hoff : ∀ x : IOBuf, Shift io x (ustart io - 1) → max 0 x.oc.val = 0 := by
    intro x hx; rw [hx.oc]; omega
  by_cases hc : ustart io - 1 ≥ 32 ∧ ustart io - 1 ≥ ((io.data.length / 8 : Nat) : Int) ∧
      ustart io - 1 + exr io ≥ n
  · rw [if_pos (by rw [hd, rem_u64_val, add_val, hd, hev, hun]; wrg <;> omega)]
    obtain ⟨d, ioc, hcr, hsh, hlen⟩ := compact_spec hw hm
    rw [bind_ok hcr, run_pure]
    have h1 := st_shift hsh; have h2 := hoff _ hsh
    refine ⟨ioc, _, rfl, hsh, by omega, Or.inl hlen, Or.inr ⟨rfl, ?_⟩⟩
    rw [h1, hlen]; unfold exr at hc; omega
  rw [if_neg (by rw [hd, rem_u64_val, add_val, hd, hev, hun]; wrg <;> omega)]
  obtain ⟨v, hv, hvv⟩ := toI_ok (n : Int) (by omega) (by omega)
  rw [hun, hv, lift_ok_bind]
  have hdes : (i ↑io.data.length + v - existingI io).val = io.data.length + n - exr io := by
    rw [sub_val, add_val, hev, hvv]; wrg <;> omega
  by_cases hbig : io.data.length + n - exr io > io.maxsize.val
  · rw [if_pos (by rw [hdes]; omega)]
    by_cases hu : ustart io = 1
    · rw [if_neg (by rw [hd]; omega)]
      exact tail_spec hw hm n (by rw [show ustart io - 1 = 0 by omega]; exact Shift.refl hw) rfl hbig
    · rw [if_pos (by rw [hd]; omega)]
      obtain ⟨d, ioc, hcr, hsh, hlen⟩ := compact_spec hw hm
      rw [bind_ok (discard_ok hcr)]
      exact tail_spec hw hm n hsh hlen hbig
  · rw [if_neg (by rw [hdes]; omega)]
    clear hc
    generalize hD : i ↑io.data.length + v - existingI io = D at hdes ⊢
    have hov := overalloc_val D (by omega) (by omega)
    rw [hdes] at hov
    have hN := imin_val io.maxsize (overallocation D)
    have hms := hw.ms
    obtain ⟨y, hy, hsy, hyl⟩ := resize_spec hw hm D false (imin io.maxsize (overallocation D))
      (by simp) (by rw [hN]; omega) (by rw [hN]; omega)
    have h3 := st_shift hsy; have h4 := hoff _ hsy
    refine ⟨y, _, hy, hsy, by rw [hyl]; exact I.le _, Or.inr (Or.inr (by rw [hyl, hN]; omega)),
      Or.inr ⟨rfl, ?_⟩⟩
    rw [hyl, hN, h3, h4, hsy.maxsize]; omega

end WriteP
end JuliaLean.IOBuffers
