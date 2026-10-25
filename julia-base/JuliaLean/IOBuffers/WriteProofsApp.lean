import JuliaLean.IOBuffers.WriteProofsPos

/-! `AppendWritesAtEnd`. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

attribute [local irreducible] wrapInt

theorem appendWritesAtEnd' (hinv : ∀ io, Reachable io → Inv io) : AppendWritesAtEnd := by
  intro io hr hm hwr hap w hwl0
  have hwl : w.length ≤ 2 ^ 60 := hwl0
  have hI := hinv io hr
  have hw := wf_of_inv hI
  have hpos := position_wf hw
  have hheld := held_eq hw
  have hst := hw.stored; have hpl := hw.ptr_le; have hpg := hw.ptr_ge
  have hzl := hw.size_len; have hl := hw.len; have hms := hw.ms
  have hu1 := ustart_ge hw; have hu2 := ustart_le hw
  simp only []
  cases hre : io.reinit
  · obtain ⟨s, δ, hens, hroom⟩ := ensure_spec hw hm hwr hre w.length hwl
    obtain ⟨r, D, Z, P, hrun, hrv, hD, hZ, hP⟩ := uw_room hw w hwl hens hroom
    have hs := hroom.1
    have hsz := hs.size; have hsl := hs.size_len; have := hs.dlo; have := hs.dhi; have hso := hs.oc
    have hspt := hs.ptr; have hocl := hw.ocl; have hofs := hw.off_size
    have hK2 : st s + kw s w.length ≤ s.data.length := by unfold kw; omega
    have hsts : st s = io.size.val - δ := by
      rw [st_shift hs]; unfold st; rw [hap]; simp
    have hsap : s.append = true := by rw [hs.append, hap]
    have hR := hroom.2.2.2
    rw [hs.maxsize, hsts, hso] at hR
    have hk : kw s w.length = min (w.length : Int) (io.maxsize.val - heldBytes io) := by
      unfold kw; rw [hsts, hs.maxsize, hheld, hso]; rcases hR with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
    have hkn : ((min w.length (io.maxsize.val - heldBytes io).toNat : Nat) : Int) = kw s w.length := by
      rw [hk]; omega
    have hK0 : 0 ≤ kw s w.length := by rw [hk]; omega
    have hK1 : kw s w.length ≤ w.length := by rw [hk]; omega
    have hPv := hP
    rw [hsap] at hPv; simp only [↓reduceIte] at hPv
    simp only [resultOf, stateOf, hrun]
    refine ⟨?_, ?_, ?_⟩
    · have hr' : r = i ↑(min w.length (io.maxsize.val - heldBytes io).toNat) := by
        apply Subtype.ext
        rw [i_natCast_val (min w.length (io.maxsize.val - heldBytes io).toNat) (by omega), hrv, hkn]
      rw [hr']
    · rw [← avail_shift hw hs]
      unfold avail
      simp only []
      rw [hD, hZ, hPv, hsts, hsz, show max (io.size.val - δ) (io.size.val - δ + kw s w.length) =
        io.size.val - δ + kw s w.length by omega]
      rw [hsts] at hK2
      rw [slice_after_append _ _ _ _ _ (by omega) (by omega) (by omega) hK0 (by simp; omega), ← hkn,
        Int.toNat_natCast]
    · apply Subtype.ext
      have hq : (position { s with data := D, size := Z, ptr := P }).val = P.val - s.oc.val - 1 := by
        apply position_val
        simp only []
        rw [hPv, hso, hspt]; omega
      rw [hq, hPv, hso, hspt, hpos]
      omega
  · obtain ⟨hp1, hz0, ho0⟩ := hI.reinit_state hre
    have hens := ensure_reinit hm hwr hre hms w.length hwl
    have hmv : (imin io.maxsize (JInt.rem .i64 (u w.length))).val = min io.maxsize.val w.length := by
      rw [imin_val, rem_i64_val, u_val, wru _ (by omega) (by omega), wr _ (by omega) (by omega)]
    have hgc : (-getCompacted io).val = 0 := by
      rw [neg_val, getCompacted_val (by omega), ho0, wr _ (by omega) (by omega)] <;> omega
    generalize hS : reallocState io w.length = s at hens
    have hsst : st s = 0 := by rw [← hS]; simp [reallocState, st, hap, hz0]
    have hsoc : s.oc.val = 0 := by rw [← hS]; exact hgc
    have hslen : (s.data.length : Int) = min io.maxsize.val w.length := by
      rw [← hS]; simp only [reallocState, List.length_replicate]; rw [hmv]; omega
    have hssz : s.size = io.size := by rw [← hS]; rfl
    have hsms : s.maxsize = io.maxsize := by rw [← hS]; rfl
    have hsptr : s.ptr = io.ptr := by rw [← hS]; rfl
    have hsap : s.append = true := by rw [← hS]; exact hap
    obtain ⟨r, D, Z, P, hrun, hrv, hD, hZ, hP⟩ := uw_of w hwl hens (by omega) (by rw [hssz]; omega)
      (by rw [hssz, hslen]; omega) (by rw [hslen]; omega) (by rw [hsoc]; omega)
      (by rw [hsoc, hsms]; omega) (by rw [hssz]; omega)
    have hk : kw s w.length = min (w.length : Int) io.maxsize.val := by
      unfold kw; rw [hsst, hslen, hsoc, hsms]; omega
    have hh0 : heldBytes io = 0 := by rw [hheld]; omega
    have hkn : ((min w.length (io.maxsize.val - heldBytes io).toNat : Nat) : Int) = kw s w.length := by
      rw [hk, hh0]; omega
    have hPv := hP
    rw [hsap] at hPv; simp only [↓reduceIte] at hPv
    simp only [resultOf, stateOf, hrun]
    refine ⟨?_, ?_, ?_⟩
    · have hr' : r = i ↑(min w.length (io.maxsize.val - heldBytes io).toNat) := by
        apply Subtype.ext
        rw [i_natCast_val (min w.length (io.maxsize.val - heldBytes io).toNat) (by omega), hrv, hkn]
      rw [hr']
    · have ha0 : avail io = [] := by
        unfold avail; rw [hp1, hz0]; simp [slice]
      rw [ha0]
      unfold avail
      simp only []
      rw [hD, hZ, hPv, hsst, hsptr, hp1, hssz, hz0, show max (0 : Int) (0 + kw s w.length) =
        0 + kw s w.length by omega]
      rw [slice_after_append _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by simp; omega), ← hkn,
        Int.toNat_natCast]
      simp [slice]
    · apply Subtype.ext
      have hq : (position { s with data := D, size := Z, ptr := P }).val = P.val - s.oc.val - 1 := by
        apply position_val
        simp only []
        rw [hPv, hsoc, hsptr, hp1]; omega
      rw [hq, hPv, hsoc, hsptr, hp1, hpos, hp1, ho0]

end WriteP
end JuliaLean.IOBuffers
