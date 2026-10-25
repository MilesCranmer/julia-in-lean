import JuliaLean.IOBuffers.WriteProofsRoom

/-! The store step of `unsafe_write` and `write(::UInt8)` after `ensureroom`. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

theorem writeAt_ok (isMem : Bool) (d : List UInt8) (p : I) (bs : List UInt8) (h1 : 1 ≤ p.val)
    (h2 : p.val - 1 + bs.length ≤ d.length) :
    writeAt isMem d p bs = .ok (d.take (p.val - 1).toNat ++ bs ++ d.drop (p.val - 1 + bs.length).toNat) := by
  unfold writeAt
  by_cases hb : bs.length = 0
  · rw [if_pos hb]
    have : bs = [] := List.eq_nil_of_length_eq_zero hb
    subst this
    simp
  · rw [if_neg hb, if_pos ⟨h1, by omega⟩]

/-- Bytes `unsafe_write` stores after `ensureroom` left the buffer `s`. -/
def kw (s : IOBuf) (n : Nat) : Int :=
  min (n : Int) (min (s.data.length - st s) (s.maxsize.val - (st s - max 0 s.oc.val)))

theorem uw_of {io s : IOBuf} (w : List UInt8) (hwl : w.length ≤ 2 ^ 60)
    (hens : (ensureroom (u w.length)).run io = .ok () s)
    (h1 : 0 ≤ st s) (h2 : st s ≤ s.size.val) (h3 : s.size.val ≤ s.data.length)
    (h4 : (s.data.length : Int) ≤ 2 ^ 63 - 1) (h5 : max 0 s.oc.val ≤ st s)
    (h6 : st s - max 0 s.oc.val ≤ s.maxsize.val)
    (h9 : s.size.val ≤ 2 ^ 62) :
    ∃ r D Z P, (unsafeWrite w).run io = .ok r { s with data := D, size := Z, ptr := P } ∧
      r.val = kw s w.length ∧
      D = s.data.take (st s).toNat ++ w.take (kw s w.length).toNat ++
        s.data.drop (st s + kw s w.length).toNat ∧
      Z.val = max s.size.val (st s + kw s w.length) ∧
      P.val = (if s.append then s.ptr.val else st s + 1 + kw s w.length) := by
  have hmx := I.le s.maxsize
  unfold unsafeWrite
  simp only []
  rw [bind_ok hens, get_bind]
  generalize hPt : (if s.append = true then s.size + i 1 else s.ptr) = Pt
  have hP : Pt.val = st s + 1 := by
    rw [← hPt]; unfold st
    by_cases ha : s.append = true
    · rw [if_pos ha, if_pos ha]; wrg <;> omega
    · rw [if_neg ha, if_neg ha]; omega
  generalize hT : imax (i 0) (JInt.rem .i64 (uminU (u w.length) (JInt.rem .u64
    (imin (i s.data.length - (Pt - i 1)) (s.maxsize - (Pt - i 1 - getOffset s)))))) = T
  have hk0 : 0 ≤ kw s w.length := by unfold kw; omega
  have hk1 : kw s w.length ≤ w.length := by unfold kw; omega
  have hk2 : st s + kw s w.length ≤ s.data.length := by unfold kw; omega
  have hk3 : st s + kw s w.length - max 0 s.oc.val ≤ s.maxsize.val := by unfold kw; omega
  have hTv : T.val = kw s w.length := by
    rw [← hT]
    simp only [imax_val, rem_i64_val, uminU_val, rem_u64_val, imin_val, sub_val, i_val, off_val, u_val, hP]
    wrg <;> unfold kw <;> omega
  have hlen : ((w.take T.val.toNat).length : Int) = kw s w.length := by
    simp only [List.length_take]; rw [hTv]; omega
  rw [writeAt_ok _ _ _ _ (by rw [hP]; omega) (by rw [hP, hlen]; omega), lift_ok_bind, set_bind, run_pure]
  refine ⟨T, _, _, _, rfl, hTv, ?_, ?_, ?_⟩
  · rw [hP, hlen, hTv, show st s + 1 - 1 = st s by omega]
  · show (imax s.size (Pt - i 1 + T)).val = _
    rw [imax_val, add_val, sub_val, hP, hTv]; wrg <;> omega
  · by_cases ha : s.append = true
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha, add_val, hP, hTv]; wrg <;> omega

theorem setChecked_ok (d : List UInt8) (k : I) (b : UInt8) (h : 1 ≤ k.val ∧ k.val ≤ d.length) :
    setChecked d k b = .ok (d.set (k.val - 1).toNat b) := by
  simp [setChecked, h]

/-- Data after `write(io, a::UInt8)` stores `a` at the end of `s`. -/
def wbData (s : IOBuf) (a : UInt8) : List UInt8 :=
  s.data.take s.size.val.toNat ++ [a] ++ s.data.drop (s.size.val + 1).toNat

theorem wb_of {io s : IOBuf} (a : UInt8) (hens : (ensureroom (u 1)).run io = .ok () s)
    (hap : s.append = true) (h1 : max 0 s.oc.val ≤ s.size.val) (h2 : s.size.val + 1 ≤ s.data.length)
    (h3 : (s.data.length : Int) ≤ 2 ^ 63 - 1) (h4 : s.size.val + 1 - max 0 s.oc.val ≤ s.maxsize.val) :
    ∃ Z, (writeByte a).run io = .ok (i 1) { s with data := wbData s a, size := Z } ∧
      Z.val = s.size.val + 1 := by
  unfold writeByte
  rw [bind_ok hens, get_bind]
  simp only [hap, ↓reduceIte]
  have hp : (s.size + i 1).val = s.size.val + 1 := by wrg <;> omega
  rw [if_neg (by rw [sub_val, hp, off_val]; wrg <;> omega)]
  rw [setChecked_ok _ _ _ (by rw [hp]; omega), lift_ok_bind, set_bind, run_pure]
  refine ⟨imax s.size (s.size + i 1), ?_, by rw [imax_val, hp]; omega⟩
  unfold wbData
  have e : (s.size.val + 1 - 1).toNat = s.size.val.toNat := by omega
  have e2 : (s.size.val + 1).toNat = s.size.val.toNat + 1 := by omega
  rw [hp, List.set_eq_take_append_cons_drop, if_pos (by omega), e, e2]
  simp

end WriteP
end JuliaLean.IOBuffers
