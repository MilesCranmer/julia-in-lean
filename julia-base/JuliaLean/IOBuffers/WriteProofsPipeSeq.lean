import JuliaLean.IOBuffers.WriteProofsPipe

/-! Interleaved writes and reads on a `PipeBuffer`, and `mark`/`reset`. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

attribute [local irreducible] wrapInt

theorem res_state_ok {α} {m : M α} {x x' : IOBuf} {a : α} (h : m.run x = .ok a x') :
    resultOf m x = .ok a ∧ stateOf m x = x' := by
  simp [resultOf, stateOf, h]

theorem res_state_err {α} {m : M α} {x x' : IOBuf} {e : IOErr} (h : m.run x = .error e x') :
    resultOf m x = .error e ∧ stateOf m x = x' := by
  simp [resultOf, stateOf, h]

theorem runOps_cons (o : Op) (os : List Op) (x : IOBuf) :
    runOps (o :: os) x = (resultOf (runOp o) x, stateOf (runOp o) x) :: runOps os (stateOf (runOp o) x) := by
  cases h : (runOp o).run x <;> simp [runOps, resultOf, stateOf, h]

theorem finalState_cons (o : Op) (os : List Op) (x : IOBuf) :
    finalState (o :: os) x = finalState os (stateOf (runOp o) x) := by
  cases h : (runOp o).run x <;> simp [finalState, stateOf, h]

/-- One pipe-client operation. -/
structure Step (x : IOBuf) (T : Int) (o : Op) : Prop where
  fifo : readOut (resultOf (runOp o) x) ++ avail (stateOf (runOp o) x) = avail x ++ o.written
  inv : PInv (stateOf (runOp o) x) (T + o.written.length)
  mark : (stateOf (runOp o) x).mark = x.mark
  used : 0 ≤ x.mark.val → used (stateOf (runOp o) x) = used x ++ o.written

theorem pipe_step {x : IOBuf} {T : Int} (h : PInv x T) (o : Op) (ho : o.isPipeIO)
    (hT : T + o.written.length ≤ 2 ^ 61 + 2 ^ 60) : Step x T o := by
  have hw := h.wf
  have hal := avail_length hw
  have := hw.ptr_le; have := hw.ptr_ge
  cases o with
  | writeByte b =>
    obtain ⟨x', hrun, hinv, hav, hmk, hus⟩ := pipe_wbyte h b (by simpa [Op.written] using hT)
    have hr : (runOp (.writeByte b)).run x = .ok (.int (i 1).val) x' := by
      show ((writeByte b) >>= fun a => pure (Val.int a.val)).run x = _
      rw [bind_ok hrun]; rfl
    obtain ⟨h1, h2⟩ := res_state_ok hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, h2]; simpa [readOut, Op.written] using hav
    · rw [h2]; simpa [Op.written] using hinv
    · rw [h2]; exact hmk
    · intro _; rw [h2]; simpa [Op.written] using hus
  | writeBytes bs =>
    obtain ⟨r, x', hrun, hinv, hav, hmk, hus⟩ := pipe_wbytes h bs ho (by simpa [Op.written] using hT)
    have hr : (runOp (.writeBytes bs)).run x = .ok (.int r.val) x' := by
      show ((unsafeWrite bs) >>= fun a => pure (Val.int a.val)).run x = _
      rw [bind_ok hrun]; rfl
    obtain ⟨h1, h2⟩ := res_state_ok hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, h2]; simpa [readOut, Op.written] using hav
    · rw [h2]; simpa [Op.written] using hinv
    · rw [h2]; exact hmk
    · intro _; rw [h2]; simpa [Op.written] using hus
  | readByte =>
    cases ha : avail x with
    | nil =>
      have hrb := readByte_eof hw h.rd ha
      have hr : (runOp .readByte).run x = .error .eofError x := by
        show (readByte >>= fun a => pure (Val.bytes [a])).run x = _
        rw [bind_err hrb]
      obtain ⟨h1, h2⟩ := res_state_err hr
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h1, h2, ha]; simp [readOut, Op.written]
      · rw [h2]; simpa [Op.written] using h
      · rw [h2]
      · intro _; rw [h2]; simp [Op.written]
    | cons b rest =>
      obtain ⟨Q, hrb, hQ⟩ := readByte_some hw h.rd b rest ha
      have hr : (runOp .readByte).run x = .ok (.bytes [b]) { x with ptr := Q } := by
        show (readByte >>= fun a => pure (Val.bytes [a])).run x = _
        rw [bind_ok hrb]; rfl
      obtain ⟨h1, h2⟩ := res_state_ok hr
      rw [ha] at hal; simp at hal
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h1, h2, avail_adv hw Q 1 (by omega) (by omega), ha]; simp [readOut, Op.written]
      · rw [h2]; simpa [Op.written] using pinv_adv h Q (by omega) (by omega)
      · rw [h2]
      · intro hm; rw [h2]; simpa [Op.written] using used_adv h hm Q
  | readN n =>
    obtain ⟨n0, n1⟩ := ho
    obtain ⟨Q, hrb, hQ⟩ := readN_spec hw h.rd n n0 n1
    have hr : (runOp (.readN n)).run x = .ok (.bytes ((avail x).take n.toNat)) { x with ptr := Q } := by
      show (readN (i n) >>= fun a => pure (Val.bytes a)).run x = _
      rw [bind_ok hrb]; rfl
    obtain ⟨h1, h2⟩ := res_state_ok hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, h2, avail_adv hw Q (min n (x.size.val - x.ptr.val + 1)).toNat (by omega) (by omega)]
      simp only [readOut, Op.written, List.append_nil]
      rw [← take_min_length (avail x) n.toNat, show min n.toNat (avail x).length =
          (min n (x.size.val - x.ptr.val + 1)).toNat by omega, List.take_append_drop]
    · rw [h2]; simpa [Op.written] using pinv_adv h Q (by omega) (by omega)
    · rw [h2]
    · intro hm; rw [h2]; simpa [Op.written] using used_adv h hm Q
  | readAll =>
    obtain ⟨Q, hrb, hQ⟩ := readAll_spec hw h.rd
    have hr : (runOp .readAll).run x = .ok (.bytes (avail x)) { x with ptr := Q } := by
      show (readAll >>= fun a => pure (Val.bytes a)).run x = _
      rw [bind_ok hrb]; rfl
    obtain ⟨h1, h2⟩ := res_state_ok hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, h2, avail_adv hw Q (avail x).length (by omega) (by omega), List.drop_length]
      simp [readOut, Op.written]
    · rw [h2]; simpa [Op.written] using pinv_adv h Q (by omega) (by omega)
    · rw [h2]
    · intro hm; rw [h2]; simpa [Op.written] using used_adv h hm Q
  | _ => exact absurd ho id

theorem weight_eq (o : Op) (ho : o.isPipeIO) : o.weight = o.written.length := by
  cases o <;> simp_all [Op.isPipeIO, Op.weight, Op.written]

theorem weight_sum (ops : List Op) (ho : ∀ o ∈ ops, o.isPipeIO) :
    (ops.map Op.weight).sum = (ops.map Op.written).flatten.length := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append]
    rw [weight_eq o (ho o (by simp)), ih (fun o' h' => ho o' (by simp [h']))]

theorem pipe_seq (ops : List Op) : ∀ (x : IOBuf) (T : Int), PInv x T → (∀ o ∈ ops, o.isPipeIO) →
    T + ((ops.map Op.written).flatten.length : Int) ≤ 2 ^ 61 + 2 ^ 60 →
    ((runOps ops x).map (fun s => readOut s.1)).flatten ++ avail (finalState ops x) =
      avail x ++ (ops.map Op.written).flatten ∧
    PInv (finalState ops x) (T + (ops.map Op.written).flatten.length) ∧ (finalState ops x).mark = x.mark ∧
    (0 ≤ x.mark.val → used (finalState ops x) = used x ++ (ops.map Op.written).flatten) := by
  induction ops with
  | nil =>
    intro x T h _ _
    refine ⟨by simp [runOps, finalState], by simpa [finalState] using h, rfl, fun _ => by simp [finalState]⟩
  | cons o os ih =>
    intro x T h ho hT
    simp only [List.map_cons, List.flatten_cons, List.length_append, Int.natCast_add] at hT ⊢
    have st := pipe_step h o (ho o (by simp)) (by omega)
    obtain ⟨r1, r2, r3, r4⟩ := ih _ _ st.inv (fun o' h' => ho o' (by simp [h'])) (by omega)
    rw [runOps_cons, finalState_cons]
    simp only [List.map_cons, List.flatten_cons, List.append_assoc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [r1, ← List.append_assoc, st.fifo, List.append_assoc]
    · rw [← Int.add_assoc]; exact r2
    · rw [r3, st.mark]
    · intro hm
      rw [r4 (by rw [st.mark]; exact hm), st.used hm, List.append_assoc]

theorem mark_run (x : IOBuf) : mark.run x = .ok (position x) { x with mark := position x } := rfl

theorem pinv_mark {x : IOBuf} {T : Int} (h : PInv x T) :
    PInv { x with mark := position x } T ∧ 0 ≤ (position x).val ∧
      used { x with mark := position x } = avail x := by
  have hw := h.wf
  have hp := position_wf hw
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len; have := h.ocn; have := h.tot
  have := h.tb
  refine ⟨⟨⟨hw.ms, hw.len, hw.ocl, hw.seek, hw.off_size, hw.size_len, hw.ptr_ge, hw.ptr_le, hw.stored,
    by simp only []; omega, by simp only []; omega, by intro _ _; simp only []; omega⟩,
    h.mem, h.rd, h.wr, h.sk, h.ap, h.ri, h.ms, h.ocn, h.tot, h.tb⟩, by omega, ?_⟩
  unfold used avail
  rw [ustart_mark (io := { x with mark := position x }) h.sk (by simp only []; omega)]
  simp only []
  rw [hp]; congr 1; omega

theorem seek_mark_spec {x : IOBuf} {T : Int} (h : PInv x T) (hm : 0 ≤ x.mark.val) :
    ∃ Q : I, (seek x.mark).run x = .ok () { x with ptr := Q } ∧ Q.val = x.mark.val + x.oc.val + 1 := by
  have hw := h.wf
  have := hw.ptr_le; have := hw.ptr_ge; have := hw.size_len; have := hw.len; have := h.ocn
  have hmp := hw.mark_pipe h.sk hm; have := hw.mark_le
  have hmk : ismarked x = true := by simp [ismarked]; omega
  unfold seek
  rw [get_bind]
  simp only [hmk, h.sk, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, ne_eq,
    not_true_eq_false]
  generalize hQ : clampI (translateSeekPosition x x.mark) (getOffset x + i 1) (x.size + i 1) = Q
  have hQv : Q.val = x.mark.val + x.oc.val + 1 := by
    rw [← hQ, tsp_eq (by omega) (by omega)]
    unfold clampI
    have e1 : (i (x.mark.val + x.oc.val + 1)).val = x.mark.val + x.oc.val + 1 := by
      rw [i_val]; exact wr _ (by omega) (by omega)
    have e2 : (x.size + i 1).val = x.size.val + 1 := by rw [add_val, i1]; exact wr _ (by omega) (by omega)
    have e3 : (getOffset x + i 1).val = max 0 x.oc.val + 1 := by
      rw [add_val, i1, off_val]; exact wr _ (by omega) (by omega)
    rw [if_neg (by rw [e1, e2]; omega), if_neg (by rw [e1, e3]; omega), e1]
  exact ⟨Q, run_set _ _, hQv⟩

theorem reset_spec {x : IOBuf} {T : Int} (h : PInv x T) (hm : 0 ≤ x.mark.val) :
    ∃ Q : I, reset.run x = .ok x.mark { { x with ptr := Q } with mark := i (-1) } ∧
      Q.val = x.mark.val + x.oc.val + 1 := by
  have hmk : ismarked x = true := by simp [ismarked]; omega
  obtain ⟨Q, hs, hQv⟩ := seek_mark_spec h hm
  unfold reset
  rw [get_bind]
  simp only [hmk, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [bind_ok hs, bind_ok (run_modify _ _), run_pure]
  exact ⟨Q, rfl, hQv⟩

end WriteP
end JuliaLean.IOBuffers
