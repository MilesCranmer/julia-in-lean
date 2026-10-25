import JuliaLean.IOBuffers.WriteProofsWrite
import JuliaLean.IOBuffers.WriteProofsList

/-! `unsafe_write` and `write(::UInt8)` from a well-formed buffer, in terms of `content`,
`avail` and the used span. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

theorem slice_after_append (d wk : List UInt8) (q z K : Int) (h1 : 1 ≤ q) (h2 : q ≤ z + 1)
    (h3 : z ≤ d.length) (hK : 0 ≤ K) (hk : (wk.length : Int) = K) :
    slice (d.take z.toNat ++ wk ++ d.drop (z + K).toNat) q (z + K) = slice d q z ++ wk := by
  unfold slice
  rw [show (z + K - q + 1).toNat = z.toNat - (q - 1).toNat + K.toNat by omega,
    show (z + K).toNat = z.toNat + K.toNat by omega, show (z - q + 1).toNat = z.toNat - (q - 1).toNat by omega]
  exact take_end d wk (q - 1).toNat z.toNat K.toNat (by omega) (by omega) (by omega)

theorem slice_after_mid (d wk : List UInt8) (o p z K : Int) (h0 : 0 ≤ o) (hp : 0 ≤ p) (h1 : o + p ≤ z)
    (h2 : z ≤ d.length) (h3 : o + p + K ≤ d.length) (hK : 0 ≤ K) (hk : (wk.length : Int) = K) :
    slice (d.take (o + p).toNat ++ wk ++ d.drop (o + p + K).toNat) (o + 1) (max z (o + p + K)) =
      (slice d (o + 1) z).take p.toNat ++ wk ++ (slice d (o + 1) z).drop (p + K).toNat := by
  unfold slice
  rw [show (o + 1 - 1).toNat = o.toNat by omega,
    show (max z (o + p + K) - (o + 1) + 1).toNat = max z.toNat (o.toNat + p.toNat + K.toNat) - o.toNat by omega,
    show (o + p).toNat = o.toNat + p.toNat by omega,
    show (o + p + K).toNat = o.toNat + p.toNat + K.toNat by omega,
    show (z - (o + 1) + 1).toNat = z.toNat - o.toNat by omega,
    show (p + K).toNat = p.toNat + K.toNat by omega]
  exact take_mid d wk o.toNat p.toNat z.toNat K.toNat (by omega) (by omega) (by omega) (by omega)

theorem avail_shift {io s : IOBuf} {δ : Int} (hw : Wf io) (hs : Shift io s δ) : avail s = avail io := by
  have := ustart_le hw; have := ustart_ge hw; have := hs.dhi; have := hs.dlo; have := hw.ptr_le
  unfold avail
  rw [hs.ptr, hs.size, slice_drop s.data (ustart io - δ) _ _ (by omega) (by omega) (by omega), hs.bytes,
    slice_drop io.data (ustart io) io.ptr.val io.size.val (by omega) (by omega) (by omega)]
  congr 1; omega

theorem content_shift {io s : IOBuf} {δ : Int} (hw : Wf io) (hs : Shift io s δ)
    (hsk : io.seekable = true) : content s = content io := by
  have := hw.seek hsk; have hu := ustart_seek hsk; have := hs.dhi; have := hs.dlo
  unfold content
  rw [off_val, off_val, hs.size, hs.oc, show max 0 (io.oc.val - δ) + 1 = ustart io - δ by omega,
    show max 0 io.oc.val + 1 = ustart io by omega, hs.bytes]

/-- The used span `data[get_used_span(io)]`. -/
def used (io : IOBuf) : List UInt8 := slice io.data (ustart io) io.size.val

theorem used_shift {io s : IOBuf} {δ : Int} (hw : Wf io) (hs : Shift io s δ) : used s = used io := by
  unfold used; rw [ustart_shift hw hs, hs.size, hs.bytes]

theorem st_ge_ustart {io : IOBuf} (hw : Wf io) : ustart io - 1 ≤ st io := by
  have := ustart_le hw; have := hw.ptr_le
  unfold st; cases io.append <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem uw_room {io s : IOBuf} {δ : Int} (hw : Wf io) (w : List UInt8) (hwl : w.length ≤ 2 ^ 60)
    (hens : (ensureroom (u w.length)).run io = .ok () s) (hroom : Room io s δ w.length) :
    ∃ r D Z P, (unsafeWrite w).run io = .ok r { s with data := D, size := Z, ptr := P } ∧
      r.val = kw s w.length ∧
      D = s.data.take (st s).toNat ++ w.take (kw s w.length).toNat ++
        s.data.drop (st s + kw s w.length).toNat ∧
      Z.val = max s.size.val (st s + kw s w.length) ∧
      P.val = (if s.append then s.ptr.val else st s + 1 + kw s w.length) := by
  obtain ⟨hs, hl, -, -⟩ := hroom
  have h1 := st_shift hs; have h2 := st_bounds hw; have h3 := st_ge_ustart hw
  have := hs.dhi; have := hs.dlo; have := hs.size_len; have := hw.stored; have := hw.len
  have := hw.size_len; have e1 := hs.oc; have e2 := hs.size; have e3 := hs.maxsize
  exact uw_of w hwl hens (by omega) (by omega) (by omega) hl (by omega) (by rw [e3]; omega) (by omega)

/-- The buffer `ensureroom_reallocate` leaves behind. -/
def reallocState (io : IOBuf) (n : Nat) : IOBuf :=
  { io with data := List.replicate (imin io.maxsize (JInt.rem .i64 (u n))).val.toNat 0, reinit := false,
            oc := -getCompacted io }

theorem ensure_reinit {io : IOBuf} (hm : io.isMem = true) (hwr : io.writable = true)
    (hr : io.reinit = true) (hms : 0 ≤ io.maxsize.val) (n : Nat) (hn : n ≤ 2 ^ 60) :
    (ensureroom (u n)).run io = .ok () (reallocState io n) := by
  have hv : (imin io.maxsize (JInt.rem .i64 (u n))).val = min io.maxsize.val n := by
    rw [imin_val, rem_i64_val, u_val, wru _ (by omega) (by omega), wr _ (by omega) (by omega)]
  rw [ensureroom_eq, get_bind]
  simp only [hwr, hr, Bool.not_true, Bool.false_or, ↓reduceIte]
  unfold ensureroomReallocate
  rw [get_bind]
  simp only [hwr, hm, Bool.not_true, Bool.false_eq_true, ↓reduceIte, similarData]
  rw [stringMemory_ok _ (by rw [hv]; omega), lift_ok_bind, run_set]
  simp only [reallocState, hm, hwr]

end WriteP
end JuliaLean.IOBuffers
