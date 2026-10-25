import JuliaLean.IOBuffers.WriteProofsPipeSeq

/-! `PipeFIFO`, `PipeMarkReset` and `WriteReadRoundtrip`. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

theorem except_ok_bind {ε α β} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

theorem except_ok_map {ε α β} (a : α) (f : α → β) : (f <$> (Except.ok a : Except ε α)) = Except.ok (f a) := rfl

/-- `PipeBuffer()`. -/
def p0 : IOBuf := newBuf [] true true true false true ⟨2 ^ 63 - 1, by decide⟩

theorem pipeBuffer_eq : pipeBuffer = .ok p0 := rfl

theorem pinv_p0 : PInv p0 0 :=
  ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩

theorem avail_p0 : avail p0 = [] := by decide

theorem pipeFIFO' : PipeFIFO := by
  intro ops ho hw
  refine ⟨p0, pipeBuffer_eq, ?_⟩
  have hsum := weight_sum ops ho
  have hb : (bound : Int) = 2 ^ 60 := by decide
  have hs' : ((ops.map Op.weight).sum : Int) = ((ops.map Op.written).flatten.length : Int) := by rw [hsum]
  have := (pipe_seq ops p0 0 pinv_p0 ho (by omega)).1
  rw [avail_p0, List.nil_append] at this
  exact this

theorem pipeMarkReset' : PipeMarkReset := by
  intro w0 ops hw0 ho hw
  refine ⟨p0, pipeBuffer_eq, ?_⟩
  simp only []
  have hsum := weight_sum ops ho
  have hb : (bound : Int) = 2 ^ 60 := by decide
  have hs' : ((ops.map Op.weight).sum : Int) = ((ops.map Op.written).flatten.length : Int) := by rw [hsum]
  have hw0' : w0.length ≤ 2 ^ 60 := hw0
  obtain ⟨r, x, hrun, hinv, hav, hmk, hus⟩ := pipe_wbytes pinv_p0 w0 hw0' (by omega)
  have hrx : (runOp (.writeBytes w0)).run p0 = .ok (.int r.val) x := by
    show ((unsafeWrite w0) >>= fun a => pure (Val.int a.val)).run p0 = _
    rw [bind_ok hrun]; rfl
  have hmx : (runOp .mark).run x = .ok (.int (position x).val) { x with mark := position x } := by
    show (mark >>= fun a => pure (Val.int a.val)).run x = _
    rw [bind_ok (mark_run x)]; rfl
  have hfin : finalState [Op.writeBytes w0, Op.mark] p0 = { x with mark := position x } := by
    rw [finalState_cons, finalState_cons, (res_state_ok hrx).2, (res_state_ok hmx).2]; rfl
  rw [hfin]
  obtain ⟨hinv1, hpos, hused1⟩ := pinv_mark hinv
  rw [avail_p0, List.nil_append] at hav
  obtain ⟨_, r2, r3, r4⟩ := pipe_seq ops _ _ hinv1 ho (by omega)
  generalize hy : finalState ops { x with mark := position x } = y at r2 r3 r4 ⊢
  have hym : 0 ≤ y.mark.val := by rw [r3]; exact hpos
  obtain ⟨Q, hrs, hQ⟩ := reset_spec r2 hym
  obtain ⟨h1, h2⟩ := res_state_ok hrs
  refine ⟨by rw [h1, r3]; rfl, ?_⟩
  rw [h2, ← hav, ← hused1, ← r4 hpos]
  unfold avail used
  simp only []
  rw [hQ, ustart_mark r2.sk hym]

theorem uw_flags {y : IOBuf} (hw : Wf y) (hm : y.isMem = true) (hwr : y.writable = true)
    (hr : y.reinit = false) (w : List UInt8) (hwl : w.length ≤ 2 ^ 60) :
    let z := stateOf (unsafeWrite w) y
    z.isMem = y.isMem ∧ z.readable = y.readable ∧ z.writable = y.writable ∧ z.seekable = y.seekable ∧
      z.append = y.append ∧ z.maxsize = y.maxsize ∧ z.reinit = y.reinit := by
  obtain ⟨s, δ, hens, hroom⟩ := ensure_spec hw hm hwr hr w.length hwl
  obtain ⟨r, D, Z, P, hrun, -⟩ := uw_room hw w hwl hens hroom
  have hs := hroom.1
  simp only [stateOf, hrun]
  exact ⟨hs.isMem, hs.readable, hs.writable, hs.seekable, hs.append, hs.maxsize, hs.reinit⟩

theorem finalState_append (ops1 ops2 : List Op) (x : IOBuf) :
    finalState (ops1 ++ ops2) x = finalState ops2 (finalState ops1 x) := by
  induction ops1 generalizing x with
  | nil => rfl
  | cons o os ih => rw [List.cons_append, finalState_cons, finalState_cons, ih]

theorem stateOf_bind_pure {α β} (m : M α) (g : α → β) (x : IOBuf) :
    stateOf (m >>= fun a => pure (g a)) x = stateOf m x := by
  unfold stateOf
  cases h : m.run x with
  | ok a s => rw [bind_ok h]; rfl
  | error e s => rw [bind_err h]

theorem stateOf_writeBytes (w : List UInt8) (x : IOBuf) :
    stateOf (runOp (.writeBytes w)) x = stateOf (unsafeWrite w) x :=
  stateOf_bind_pure (unsafeWrite w) (fun a => Val.int a.val) x

/-- The roundtrip buffer after some writes. -/
structure RT (y : IOBuf) (m : Int) (F : List UInt8) : Prop where
  mem : y.isMem = true
  rd : y.readable = true
  wr : y.writable = true
  sk : y.seekable = true
  ap : y.append = false
  ri : y.reinit = false
  ms : y.maxsize.val = m
  con : content y = F.take m.toNat
  pos : (position y).val = (content y).length

theorem take_app (F w : List UInt8) (M : Nat) :
    F.take M ++ w.take (min w.length (M - (F.take M).length)) = (F ++ w).take M := by
  rw [List.take_append]
  congr 1
  rw [List.length_take]
  by_cases h : M ≤ F.length
  · rw [Nat.min_eq_left h, Nat.sub_self, Nat.min_zero, show M - F.length = 0 by omega]
  · rw [show min M F.length = F.length by omega, Nat.min_comm, take_min_length]

theorem rt_write (hinv : ∀ io, Reachable io → Inv io) {y : IOBuf} {m : Int} {F : List UInt8}
    (hr : Reachable y) (h : RT y m F) (hm0 : 0 ≤ m) (w : List UInt8) (hwl : w.length ≤ bound) :
    RT (stateOf (unsafeWrite w) y) m (F ++ w) := by
  have hI := hinv y hr
  have hw := wf_of_inv hI
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := uw_flags hw h.mem h.wr h.ri w hwl
  obtain ⟨_, hc, hp⟩ := writeAtPosition' hinv y hr h.mem h.wr h.sk h.ap w hwl
  have hpc := h.pos
  have hcon := h.con
  have hlen : (content y).length ≤ m.toNat := by rw [hcon, List.length_take]; omega
  refine ⟨f1.trans h.mem, f2.trans h.rd, f3.trans h.wr, f4.trans h.sk, f5.trans h.ap, f7.trans h.ri,
    by rw [f6]; exact h.ms, ?_, ?_⟩
  · rw [hc, hpc, Int.toNat_natCast, List.take_length, List.drop_eq_nil_of_le (by omega), List.append_nil,
      h.ms, hcon, show (m - ((F.take m.toNat).length : Int)).toNat = m.toNat - (F.take m.toNat).length by omega,
      take_app]
  · rw [hp, hc, hpc, Int.toNat_natCast, List.take_length, List.drop_eq_nil_of_le (by omega), List.append_nil,
      List.length_append, List.length_take]
    omega

theorem rt_seq (hinv : ∀ io, Reachable io → Inv io) (c : Ctor) (io0 : IOBuf) (hc : c.ok)
    (hb : c.build = .ok io0) (m : Int) (hm0 : 0 ≤ m) :
    ∀ (ws : List (List UInt8)) (P : List Op) (F : List UInt8), (∀ o ∈ P, Op.ok o) →
      (P.map Op.weight).sum + (ws.map List.length).sum ≤ bound → RT (finalState P io0) m F →
      RT (finalState (P ++ ws.map Op.writeBytes) io0) m (F ++ ws.flatten) ∧
      Reachable (finalState (P ++ ws.map Op.writeBytes) io0) := by
  intro ws
  induction ws with
  | nil =>
    intro P F hP hw h
    simp only [List.map_nil, List.append_nil, List.flatten_nil]
    exact ⟨h, c, P, io0, hc, hb, hP, by simp at hw; omega, rfl⟩
  | cons w ws ih =>
    intro P F hP hw h
    simp only [List.map_cons, List.sum_cons] at hw
    have hr : Reachable (finalState P io0) := ⟨c, P, io0, hc, hb, hP, by omega, rfl⟩
    have hwl : w.length ≤ bound := by omega
    have h1 := rt_write hinv hr h hm0 w hwl
    have hfin : finalState (P ++ [Op.writeBytes w]) io0 = stateOf (unsafeWrite w) (finalState P io0) := by
      rw [finalState_append, finalState_cons, stateOf_writeBytes]; rfl
    rw [← hfin] at h1
    have := ih (P ++ [Op.writeBytes w]) (F ++ w)
      (fun o ho' => by
        rcases List.mem_append.mp ho' with h' | h'
        · exact hP o h'
        · simp at h'; subst h'; exact hwl)
      (by simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Op.weight]; omega) h1
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    exact this

theorem seekstart_spec {z : IOBuf} (hw : Wf z) (hsk : z.seekable = true) :
    ∃ Q : I, (runOp .seekstart).run z = .ok .unit { z with ptr := Q } ∧ Q.val = z.oc.val + 1 := by
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len; have hoc := hw.seek hsk
  have := hw.off_size
  have htsp : translateSeekPosition z (i 0) = i (z.oc.val + 1) := by
    unfold translateSeekPosition clampToI
    rw [i0, Int.zero_add, if_neg (by omega), if_neg (by omega)]
  have hs0 : ∃ Q : I, (seek (i 0)).run z = .ok () { z with ptr := Q } ∧ Q.val = z.oc.val + 1 := by
    unfold seek
    rw [get_bind]
    simp only [hsk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    generalize hQ : clampI (translateSeekPosition z (i 0)) (getOffset z + i 1) (z.size + i 1) = Q
    have hQv : Q.val = z.oc.val + 1 := by
      rw [← hQ, htsp]
      unfold clampI
      have e1 : (i (z.oc.val + 1)).val = z.oc.val + 1 := by rw [i_val]; exact wr _ (by omega) (by omega)
      have e2 : (z.size + i 1).val = z.size.val + 1 := by rw [add_val, i1]; exact wr _ (by omega) (by omega)
      have e3 : (getOffset z + i 1).val = max 0 z.oc.val + 1 := by
        rw [add_val, i1, off_val]; exact wr _ (by omega) (by omega)
      rw [if_neg (by rw [e1, e2]; omega), if_neg (by rw [e1, e3]; omega), e1]
    exact ⟨Q, run_set _ _, hQv⟩
  obtain ⟨Q, hs, hQ⟩ := hs0
  refine ⟨Q, ?_, hQ⟩
  show (seek (i 0) >>= fun _ => pure Val.unit).run z = _
  rw [bind_ok hs]; rfl

theorem writeReadRoundtrip' (hinv : ∀ io, Reachable io → Inv io) : WriteReadRoundtrip := by
  intro m ws hm0 hm1 hsum
  obtain ⟨v, hv, hvv⟩ := toI_ok m (by omega) (by omega)
  have hc : (Ctor.empty (some true) (some true) none (some true) m none).ok :=
    ⟨hm0, hm1, fun _ hs => nomatch hs⟩
  have hmem : ∀ n : I, 0 ≤ n.val → stringMemory n = .ok (List.replicate n.val.toNat 0) := stringMemory_ok
  have h32 : 0 ≤ (imin v (i 32)).val := by rw [imin_val, hvv]; simp only [i_val]; rw [wr 32 (by decide) (by decide)]; omega
  have hbuild : iobufferEmpty (some true) (some true) none (some true) m none =
      .ok { newBuf (List.replicate (imin v (i 32)).val.toNat 0) true true true true false v with size := i 0 } := by
    simp [iobufferEmpty, hv, hvv, hmem _ h32, openFlags, except_ok_bind, except_ok_map, show ¬ m < 0 by omega]
  refine ⟨_, hbuild, ?_⟩
  generalize hio : { newBuf (List.replicate (imin v (i 32)).val.toNat 0) true true true true false v with
    size := i 0 } = io0 at hbuild
  have hRT0 : RT (finalState [] io0) m [] := by
    rw [← hio]
    have hc0 : content { newBuf (List.replicate (imin v (i 32)).val.toNat 0) true true true true false v with
        size := i 0 } = [] := by
      simp [content, slice, newBuf, off_val, i0]
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, hvv, by simp only [finalState]; rw [hc0]; simp, ?_⟩
    simp only [finalState]; rw [hc0]; show (i 1 - i 0 - i 1).val = ((0 : Nat) : Int); decide
  obtain ⟨hRT, hR⟩ := rt_seq hinv _ io0 hc hbuild m hm0 ws [] [] (by simp) (by simpa using hsum) hRT0
  simp only [List.nil_append] at hRT hR
  rw [finalState_append, finalState_cons]
  generalize hz : finalState (ws.map Op.writeBytes) io0 = z at hRT hR ⊢
  have hI := hinv z hR
  have hw := wf_of_inv hI
  obtain ⟨Q, hs, hQ⟩ := seekstart_spec hw hRT.sk
  rw [(res_state_ok hs).2]
  simp only [finalState]
  have hw' : Wf { z with ptr := Q } := by
    have := hw.ptr_ge; have := hw.ptr_le; have := hw.off_size; have hoc := hw.seek hRT.sk
    exact ⟨hw.ms, hw.len, hw.ocl, hw.seek, hw.off_size, hw.size_len, by simp only []; omega,
      by simp only []; omega, hw.stored, hw.mark_ge, hw.mark_le, fun hs => by simp [hRT.sk] at hs⟩
  obtain ⟨Q', hra, -⟩ := readAll_spec hw' hRT.rd
  rw [(res_state_ok hra).1, ← hRT.con]
  congr 1
  unfold avail content
  simp only []
  rw [hQ, off_val, show max 0 z.oc.val = z.oc.val by have := hw.seek hRT.sk; omega]

end WriteP
end JuliaLean.IOBuffers
