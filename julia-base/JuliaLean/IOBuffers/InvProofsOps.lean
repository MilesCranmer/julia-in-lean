import JuliaLean.IOBuffers.InvProofsBuf

/-!
Every operation of `Op` with in-range arguments preserves `SInv` (with the budget grown by
the operation's weight), also when it throws, and never throws `IOErr.outOfBounds`.
-/

namespace JuliaLean.IOBuffers.InvP

open JuliaLean JuliaLean.IOBuffers

attribute [local irreducible] wrapInt

theorem Spec.weaken {α} {m : M α} {s : IOBuf} {K1 K2 : Int}
    (hsp : Spec m s (fun _ s' => SInv s' K1) (Err K1)) (hk : K1 ≤ K2) :
    Spec m s (fun _ s' => SInv s' K2) (Err K2) :=
  hsp.mono (fun _ _ x => x.mono hk) (Err.mono hk)

/-! ## Reading -/

theorem readByte_spec {s : IOBuf} {K : Int} (h : SInv s K) :
    Spec readByte s (fun _ s' => SInv s' K ∧ ∃ p, s' = { s with ptr := p })
      (fun e s' => NotOOB e ∧ s' = s) := by
  unfold readByte
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure, throwNotReadable, throwArg,
    spec_throw]
  facts h
  split
  · exact ⟨noob_jl _, by trivial⟩
  · split
    · exact ⟨nofun, by trivial⟩
    · next hle =>
      refine spec_readAt (Or.inr ⟨by omega, by omega⟩) (fun r => ⟨?_, _, rfl⟩)
      exact sinv_ptr_fwd h _ (by vo) (by vo)

theorem peekByte_spec {s : IOBuf} :
    Spec peekByte s (fun _ s' => s' = s) (fun e s' => NotOOB e ∧ s' = s) := by
  unfold peekByte
  simp only [spec_bind, spec_get, spec_ite, spec_pure, throwNotReadable, throwArg, spec_throw]
  split
  · exact ⟨noob_jl _, by trivial⟩
  · split
    · exact ⟨nofun, by trivial⟩
    · exact spec_lift_of (fun _ _ => by trivial) (fun e he => ⟨noob_getChecked he, by trivial⟩)

theorem unsafeRead_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60)
    (nb : U) :
    Spec (unsafeRead nb) s (fun _ s' => SInv s' K ∧ ∃ p, s' = { s with ptr := p }) (Err K) := by
  unfold unsafeRead
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure, throwNotReadable, throwArg,
    spec_throw]
  facts h
  have := U.bounds nb
  split
  · exact ⟨noob_jl _, h⟩
  · refine spec_readAt (by vo) (fun r => ?_)
    refine spec_toI (by vo) (by vo) (fun v hv => ?_)
    have hv' : v.val = s.ptr.val + min (s.size.val - s.ptr.val + 1) nb.val := by rw [hv]; vo
    have hS := sinv_ptr_fwd h v (by omega) (by omega)
    split
    · exact ⟨nofun, hS⟩
    · exact ⟨hS, _, rfl⟩

theorem readBang_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60)
    (n : Nat) :
    Spec (readBang n) s (fun _ s' => SInv s' K ∧ ∃ p, s' = { s with ptr := p }) (Err K) := by
  unfold readBang
  simp only [spec_bind]
  exact spec_lift_of (fun v _ => unsafeRead_spec h hK v) (fun e he => ⟨noob_toU he, h⟩)

theorem readN_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) (nb : I) :
    Spec (readN nb) s (fun _ s' => SInv s' K) (Err K) := by
  unfold readN
  simp only [spec_bind, spec_get]
  exact spec_lift_of (fun _ _ => (readBang_spec h hK _).mono (fun _ _ x => x.1) (fun _ _ x => x))
    (fun e he => ⟨noob_stringMemory he, h⟩)

theorem readAll_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) :
    Spec readAll s (fun _ s' => SInv s' K) (Err K) := by
  unfold readAll
  simp only [spec_bind, spec_get]
  exact spec_lift_of (fun _ _ => (readBang_spec h hK _).mono (fun _ _ x => x.1) (fun _ _ x => x))
    (fun e he => ⟨noob_stringMemory he, h⟩)

theorem readbytes_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60)
    (nb : I) : Spec (readbytes nb) s (fun _ s' => SInv s' K) (Err K) := by
  unfold readbytes
  simp only [spec_bind, spec_get, spec_ite, spec_pure, throwNotReadable, throwArg, spec_throw]
  split
  · exact ⟨noob_jl _, h⟩
  · exact spec_lift_of (fun v _ => (unsafeRead_spec h hK v).mono (fun _ _ x => x.1)
      (fun _ _ x => x)) (fun e he => ⟨noob_toU he, h⟩)

theorem peekT_spec {s : IOBuf} {K : Int} (h : SInv s K) (nb : Nat) :
    Spec (peekT nb) s (fun _ s' => s' = s ∧ (nb : Int) ≤ s.size.val - s.ptr.val + 1)
      (fun e s' => NotOOB e ∧ s' = s) := by
  unfold peekT
  simp only [spec_bind, spec_get, spec_ite, spec_pure, throwNotReadable, throwArg, spec_throw]
  facts h
  split
  · exact ⟨noob_jl _, by trivial⟩
  · split
    · exact ⟨nofun, by trivial⟩
    · next hle =>
      vsimp at hle
      exact spec_readAt (by omega) (fun _ => ⟨rfl, by omega⟩)

theorem readT_spec {s : IOBuf} {K : Int} (h : SInv s K) (nb : Nat) :
    Spec (readT nb) s (fun _ s' => SInv s' K) (Err K) := by
  unfold readT
  simp only [spec_bind, spec_modify, spec_pure]
  facts h
  refine (peekT_spec h nb).mono (fun _ s' ⟨he, hle⟩ => ?_) (fun e s' ⟨h1, h2⟩ => ?_)
  · subst he
    exact sinv_ptr_fwd h _ (by vo) (by vo)
  · subst h2
    exact ⟨h1, h⟩

/-! ## Seeking and marks -/

theorem seek_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) (n : I) :
    Spec (seek n) s (fun _ s' => SInv s' K) (Err K) := by
  unfold seek
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure, throwArg, spec_throw]
  facts h
  have hlohi : (getOffset s + i 1).val ≤ (s.size + i 1).val := by vo
  have hcl := v_clampI (translateSeekPosition s n) (getOffset s + i 1) (s.size + i 1) hlohi
  have hlo : (getOffset s + i 1).val = max 0 s.oc.val + 1 := by vo
  have hhi : (s.size + i 1).val = s.size.val + 1 := by vo
  rw [hlo, hhi] at hcl
  split
  · next hns =>
    have hs : s.seekable = false := by simpa using hns
    split
    · exact ⟨noob_jl _, h⟩
    · next hmk =>
      split
      · exact ⟨noob_jl _, h⟩
      · next hn =>
        have hn' : n = s.mark := Decidable.of_not_not hn
        have hm : 0 ≤ s.mark.val := by unfold ismarked at hmk; simpa using hmk
        have hp := h.pipe hs hm
        have ht : (translateSeekPosition s n).val = s.mark.val + s.oc.val + 1 := by
          rw [hn']; vo
        exact sinv_ptr h _ (by omega) (by omega) (fun _ _ => by omega)
  · next hns =>
    have hs : s.seekable = true := by simpa using hns
    exact sinv_ptr h _ (by omega) (by omega) (fun hs' => by rw [hs] at hs'; cases hs')

theorem skip_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) (n : Int) :
    Spec (skip n) s (fun _ s' => SInv s' K) (Err K) := by
  unfold skip
  simp only [spec_bind, spec_get, spec_ite, spec_set]
  facts h
  split
  · exact seek_spec h hK _
  · next hn =>
    vsimp at hn
    exact sinv_ptr_fwd h _ (by vo) (by vo)

theorem seekend_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) :
    Spec seekend s (fun _ s' => SInv s' K) (Err K) := by
  unfold seekend
  simp only [spec_modify]
  facts h
  exact sinv_ptr_fwd h _ (by vo) (by vo)

theorem mark_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) :
    Spec mark s (fun _ s' => SInv s' K) (Err K) := by
  unfold mark
  simp only [spec_bind, spec_get, spec_set, spec_pure]
  facts h
  have hp : (position s).val = s.ptr.val - s.oc.val - 1 := by vo
  exact sinv_mark h _ (by omega) (by omega) (fun _ _ => by rw [hp]; omega)

theorem unmark_spec {s : IOBuf} {K : Int} (h : SInv s K) :
    Spec unmark s (fun _ s' => SInv s' K) (Err K) := by
  unfold unmark
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure]
  split
  · exact h
  · exact sinv_mark h _ (by vo) (by vo) (fun _ hm => by vsimp at hm <;> omega)

theorem reset_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) :
    Spec reset s (fun _ s' => SInv s' K) (Err K) := by
  unfold reset
  simp only [spec_bind, spec_get, spec_ite, spec_modify, spec_pure, throwArg, spec_throw]
  split
  · exact ⟨noob_jl _, h⟩
  · exact (seek_spec h hK s.mark).mono
      (fun _ _ h1 => sinv_mark h1 _ (by vo) (by vo) (fun _ hm => by vsimp at hm <;> omega))
      (fun _ _ x => x)

theorem peekGeneric_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) :
    Spec peekGeneric s (fun _ s' => SInv s' K) (Err K) := by
  unfold peekGeneric
  simp only [spec_bind, spec_pure, spec_tryCatch, spec_throw]
  refine (mark_spec h hK).mono (fun _ s1 h1 => ?_) (fun _ _ x => x)
  refine (readByte_spec h1).mono (fun _ s2 ⟨h2, _⟩ => ?_) (fun e s2 ⟨he, hs2⟩ => ?_)
  · exact (reset_spec h2 hK).mono (fun _ _ x => x) (fun _ _ x => x)
  · subst hs2
    exact (reset_spec h1 hK).mono (fun _ _ h3 => ⟨he, h3⟩) (fun _ _ x => x)

/-! ## Truncation and taking -/

theorem truncate_grow {s1 : IOBuf} {K : Int} (h1 : SInv s1 K) (n : I)
    (hK : K + n.val ≤ 2 ^ 61 + 2 ^ 60) (hs1 : s1.seekable = true) (hr1 : s1.reinit = false)
    (hn : s1.size.val - max 0 s1.oc.val < n.val) (hnm : n.val ≤ s1.maxsize.val) :
    Spec (resize (n + getOffset s1) false) s1 (fun _ s2 =>
      Spec (lift (fillZero s2.data (s2.size + i 1) (imin (i ↑s2.data.length) (n + getOffset s2))))
        s2
        (fun d _ =>
          SInv { s2 with data := d, size := imin (i ↑s2.data.length) (n + getOffset s2) }
            (K + n.val.toNat))
        (Err (K + n.val.toNat)))
      (Err (K + n.val.toNat)) := by
  facts h1
  have hoc := h1.seek hs1
  have hx : (n + getOffset s1).val = n.val + s1.oc.val := by vo
  generalize n + getOffset s1 = X at hx ⊢
  obtain ⟨ho1, ho2⟩ := overalloc_spec X (by omega) (by omega)
  refine (resize_spec h1 (by omega) _ false _ (if_neg Bool.false_ne_true) ?_ ?_ ?_).mono
    (fun _ s2 ⟨h2, ⟨d, o, p, z, he⟩, hrel⟩ => ?_) (Err.mono (by omega))
  · rw [v_imin]; omega
  · rw [v_imin]; omega
  · rw [v_imin]; omega
  · have hs2 : s2.seekable = true := by rw [he]; exact hs1
    have hr2 : s2.reinit = false := by rw [he]; exact hr1
    have hms : s2.maxsize.val = s1.maxsize.val := by rw [he]
    have hoc2 := h2.seek hs2
    facts h2
    refine spec_fillZero (by vo) (by vo) (fun r hrl => ?_)
    sinv_close h2

theorem truncate_spec {s : IOBuf} {K : Int} (h : SInv s K) (n : I)
    (hK : K + n.val.toNat ≤ 2 ^ 61 + 2 ^ 60) :
    Spec (truncate n) s (fun _ s' => SInv s' (K + n.val.toNat)) (Err (K + n.val.toNat)) := by
  have hKK : K ≤ K + n.val.toNat := by omega
  have hK' : K ≤ 2 ^ 61 + 2 ^ 60 := by omega
  unfold truncate
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure, spec_discard, throwArg,
    spec_throw]
  facts h
  split
  · exact ⟨noob_jl _, h.mono hKK⟩
  · split
    · exact ⟨noob_jl _, h.mono hKK⟩
    · next hsk =>
      have hsk' : s.seekable = true := by simpa using hsk
      have hoc := h.seek hsk'
      split
      · exact ⟨noob_jl _, h.mono hKK⟩
      · next hn0 =>
        split
        · exact ⟨noob_jl _, h.mono hKK⟩
        · next hnm =>
          split
          · next hre =>
            have hre' := h.re hre
            refine spec_similarData (by omega) (fun _ => ?_) (fun _ => ⟨noob_jl _, h.mono hKK⟩)
            sinv_close h
          · next hre =>
            have hre' : s.reinit = false := by simpa using hre
            split
            · next hlt =>
              vsimp at hlt
              by_cases hc : (translateSeekPosition s s.mark).val > (n + getOffset s).val
              · simp only [hc, ↓reduceIte]
                sinv_close h
              · simp only [hc, ↓reduceIte]
                sinv_close h
            · next hge =>
              split
              · next hgt =>
                vsimp at hge hgt
                split
                · exact (compact_spec h hK').mono (fun _ s1 ⟨hs1, ⟨_, _, _, _, he⟩, _, hrel⟩ => by
                    have hsk1 : s1.seekable = true := by rw [he]; exact hsk'
                    have hr1 : s1.reinit = false := by rw [he]; exact hre'
                    have hms1 : s1.maxsize.val = s.maxsize.val := by rw [he]
                    have := hs1.seek hsk1
                    exact truncate_grow hs1 n (by omega) hsk1 hr1 (by omega) (by omega))
                    (Err.mono hKK)
                · exact truncate_grow h n (by omega) hsk' hre' (by omega) (by omega)
              · exact h.mono hKK

theorem take_tail {s : IOBuf} {K : Int} (h : SInv s K) (hmk : s.mark.val = -1) :
    (if s.writable = true then SInv (resetTaken s) K else SInv s K) := by
  split
  · unfold resetTaken
    sinv_close h
  · exact h

theorem take_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) :
    Spec take s (fun _ s' => SInv s' K) (Err K) := by
  unfold take
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure, spec_modify, spec_throw]
  have h1 : SInv { s with mark := i (-1) } K :=
    sinv_mark h _ (by vo) (by vo) (fun _ hm => by vsimp at hm <;> omega)
  have hm1 : ({ s with mark := i (-1) } : IOBuf).mark.val = -1 := by vo
  split
  · split
    · split
      · exact take_tail h1 hm1
      · exact spec_lift_of (fun _ _ => take_tail h1 hm1) (fun e he => ⟨noob_wrapBytes he, h1⟩)
    · split
      · exact take_tail h1 hm1
      · split
        · exact spec_lift_of (fun _ _ => take_tail h1 hm1)
            (fun e he => ⟨noob_wrapBytes he, h1⟩)
        · exact ⟨nofun, h1⟩
  · split
    · exact spec_lift_of (fun _ _ => spec_lift_of (fun _ _ => take_tail h1 hm1)
        (fun e he => ⟨noob_copyto he, h1⟩)) (fun e he => ⟨noob_stringMemory he, h1⟩)
    · exact spec_lift_of (fun _ _ => (readBang_spec h1 hK _).mono
        (fun _ s' ⟨hs', _, he⟩ => by subst he; exact take_tail hs' hm1) (fun _ _ x => x))
        (fun e he => ⟨noob_stringMemory he, h1⟩)

theorem takestring_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) :
    Spec takestring s (fun _ s' => SInv s' K) (Err K) := by
  unfold takestring
  simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure]
  split
  · exact take_spec h hK
  · split
    · exact h
    · split
      · refine spec_lift_of (fun _ _ => ?_) (fun e he => ⟨noob_getUsedSpan he, h⟩)
        unfold resetTaken
        sinv_close h
      · exact spec_lift_of (fun _ _ => h) (fun e he => ⟨noob_getUsedSpan he, h⟩)

/-! ## Delimited reading -/

theorem findOrLen_le (d : List UInt8) (x : UInt8) : findOrLen d x ≤ d.length := by
  unfold findOrLen
  split
  · next k hk =>
    obtain ⟨hlt, _⟩ := List.idxOf?_eq_some_iff.mp hk
    omega
  · exact Nat.le_refl _

theorem pending_ok {s : IOBuf} {K : Int} (h : SInv s K) :
    ∃ d, pending s = .ok d ∧ (d.length : Int) = s.size.val - s.ptr.val + 1 := by
  facts h
  unfold pending
  split
  · exact ⟨[], rfl, by simp only [List.length_nil]; omega⟩
  · rw [if_pos (And.intro (by omega : 1 ≤ s.ptr.val) (by omega : s.size.val ≤ ↑s.data.length))]
    exact ⟨_, rfl, by rw [slice_length _ _ _ (by omega) (by omega) (by omega)]; omega⟩

theorem readuntil_spec {s : IOBuf} {K : Int} (h : SInv s K)
    (delim : UInt8) (keep : Bool) :
    Spec (readuntil delim keep) s (fun _ s' => SInv s' K) (Err K) := by
  unfold readuntil
  simp only [spec_bind, spec_get, spec_set, spec_pure]
  obtain ⟨d, hd, hdl⟩ := pending_ok h
  rw [hd, spec_lift_ok]
  have := findOrLen_le d delim
  facts h
  exact sinv_ptr_fwd h _ (by vo) (by vo)

theorem readline_spec {s : IOBuf} {K : Int} (h : SInv s K)
    (keep : Bool) : Spec (readline keep) s (fun _ s' => SInv s' K) (Err K) := by
  unfold readline
  simp only [spec_bind, spec_get, spec_set, spec_pure]
  obtain ⟨d, hd, hdl⟩ := pending_ok h
  rw [hd, spec_lift_ok]
  have := findOrLen_le d 0x0a
  facts h
  exact sinv_ptr_fwd h _ (by vo) (by vo)

/-! ## Closing -/

theorem sinv_closed {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60)
    (d : List UInt8) (hd : (d.length : Int) ≤ 2 ^ 62) :
    SInv (closedState { s with data := d }) K := by
  unfold closedState
  sinv_close h

theorem close_spec {s : IOBuf} {K : Int} (h : SInv s K) (hK : K ≤ 2 ^ 61 + 2 ^ 60) :
    Spec close s (fun _ s' => SInv s' K) (Err K) := by
  unfold close
  simp only [spec_bind, spec_get, spec_ite, spec_modify, spec_pure]
  facts h
  split
  · unfold resize
    simp only [spec_bind, spec_get, spec_ite, spec_set, spec_pure]
    rw [if_pos trivial]
    by_cases hm : s.isMem = true
    · obtain ⟨a, ha, -⟩ := usedSpan_ok h hm
      rw [ha, spec_lift_ok]
      dsimp only
      refine spec_similarData (by vo) (fun _ => ?_) (fun hm' => by rw [hm] at hm'; cases hm')
      rw [if_pos (show (i 0).val = 0 by vo)]
      exact sinv_closed h hK _ (by vo)
    · rw [usedSpan_err (by simpa using hm), spec_lift_error]; exact ⟨noob_jl _, h⟩
  · exact sinv_closed h hK s.data h.len

/-! ## Operations -/

theorem runOp_spec {s : IOBuf} {K : Int} (o : Op) (ho : o.ok) (h : SInv s K)
    (hK : K + o.weight ≤ 2 ^ 61 + 2 ^ 60) :
    Spec (runOp o) s (fun _ s' => SInv s' (K + o.weight)) (Err (K + o.weight)) := by
  have hK' : K ≤ 2 ^ 61 + 2 ^ 60 := by omega
  have hw : K ≤ K + o.weight := by omega
  cases o with
  | writeByte b =>
    simp only [runOp, spec_bind, spec_pure, Op.weight] at hK hw ⊢
    exact (writeByte_spec h (by omega)).weaken (by omega)
  | writeBytes bs =>
    simp only [Op.ok, bound] at ho
    simp only [runOp, spec_bind, spec_pure, Op.weight] at hK hw ⊢
    exact unsafeWrite_spec h (by omega) (by omega)
  | readByte =>
    simp only [runOp, spec_bind, spec_pure]
    refine (readByte_spec h).mono (fun _ _ x => x.1.mono hw) (fun e s' ⟨he, hs⟩ => ?_)
    subst hs
    exact ⟨he, h.mono hw⟩
  | peekByte =>
    simp only [runOp, spec_bind, spec_pure]
    refine peekByte_spec.mono (fun _ s' hs => ?_) (fun e s' ⟨he, hs⟩ => ?_)
    · subst hs; exact h.mono hw
    · subst hs; exact ⟨he, h.mono hw⟩
  | readN n =>
    simp only [runOp, spec_bind, spec_pure]
    exact (readN_spec h hK' _).weaken hw
  | readAll =>
    simp only [runOp, spec_bind, spec_pure]
    exact (readAll_spec h hK').weaken hw
  | readBang n =>
    simp only [runOp, spec_bind, spec_pure]
    exact (readBang_spec h hK' n).mono (fun _ _ x => x.1.mono hw) (Err.mono hw)
  | readbytes nb =>
    simp only [runOp, spec_bind, spec_pure]
    exact (readbytes_spec h hK' _).weaken hw
  | peekT nb =>
    simp only [runOp, spec_bind, spec_pure]
    refine (peekT_spec h nb).mono (fun _ s' ⟨hs, _⟩ => ?_) (fun e s' ⟨he, hs⟩ => ?_)
    · subst hs; exact h.mono hw
    · subst hs; exact ⟨he, h.mono hw⟩
  | readT nb =>
    simp only [runOp, spec_bind, spec_pure]
    exact (readT_spec h nb).weaken hw
  | peekGeneric =>
    simp only [runOp, spec_bind, spec_pure]
    exact (peekGeneric_spec h hK').weaken hw
  | skip n =>
    simp only [runOp, spec_bind, spec_pure]
    exact (skip_spec h hK' n).weaken hw
  | seek n =>
    simp only [runOp, spec_bind, spec_pure, seekAny]
    exact (seek_spec h hK' _).weaken hw
  | seekstart =>
    simp only [runOp, spec_bind, spec_pure, seekstart]
    exact (seek_spec h hK' _).weaken hw
  | seekend =>
    simp only [runOp, spec_bind, spec_pure]
    exact (seekend_spec h hK').weaken hw
  | mark =>
    simp only [runOp, spec_bind, spec_pure]
    exact (mark_spec h hK').weaken hw
  | unmark =>
    simp only [runOp, spec_bind, spec_pure]
    exact (unmark_spec h).weaken hw
  | reset =>
    simp only [runOp, spec_bind, spec_pure]
    exact (reset_spec h hK').weaken hw
  | truncate n =>
    simp only [Op.ok, isInt] at ho
    have hin : (i n).val = n := by vo
    simp only [runOp, spec_bind, spec_pure, Op.weight] at hK hw ⊢
    exact (truncate_spec h (i n) (by rw [hin]; omega)).weaken (by rw [hin]; exact Int.le_refl _)
  | take =>
    simp only [runOp, spec_bind, spec_pure]
    exact (take_spec h hK').weaken hw
  | takestring =>
    simp only [runOp, spec_bind, spec_pure]
    exact (takestring_spec h hK').weaken hw
  | readuntil d k =>
    simp only [runOp, spec_bind, spec_pure]
    exact (readuntil_spec h d k).weaken hw
  | readline k =>
    simp only [runOp, spec_bind, spec_pure]
    exact (readline_spec h k).weaken hw
  | occursin d =>
    simp only [runOp, spec_bind, spec_get, spec_pure]
    refine spec_lift_of (fun _ _ => h.mono hw) (fun e he => ⟨?_, h.mono hw⟩)
    obtain ⟨d', hd', _⟩ := pending_ok h
    unfold occursin at he
    rw [hd'] at he
    cases he
  | copyline l k => exact ho.elim
  | closewrite =>
    simp only [runOp, spec_bind, spec_pure, closewrite, spec_modify]
    have h' := h.mono hw
    sinv_same h'
  | close =>
    simp only [runOp, spec_bind, spec_pure]
    exact (close_spec h hK').weaken hw

end JuliaLean.IOBuffers.InvP
