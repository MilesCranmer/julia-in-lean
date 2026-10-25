import JuliaLean.IOBuffers.OpProofsBase

/-!
`seek`, `skip` and `occursin` on a buffer satisfying `Inv`.
-/

namespace JuliaLean.IOBuffers

open JuliaLean

namespace OpP

theorem seek_run_ok (io : IOBuf) (n : I)
    (hc : io.seekable = true ∨ (ismarked io = true ∧ n = io.mark)) :
    (seek n).run io = .ok ()
      { io with ptr := clampI (translateSeekPosition io n) (getOffset io + i 1) (io.size + i 1) } := by
  rcases hc with hs | ⟨hm, hn⟩
  · simp [seek, hs]
  · cases hs : io.seekable
    · simp [seek, hs, hm, hn]
    · simp [seek, hs]

theorem seek_run_err (io : IOBuf) (n : I) (hs : io.seekable = false)
    (hc : ¬ (ismarked io = true ∧ n = io.mark)) : ∃ e, (seek n).run io = .error e io := by
  by_cases hm : ismarked io = true
  · have hn : n ≠ io.mark := fun h => hc ⟨hm, h⟩
    simp [seek, hs, hm, hn, throwArg]
  · have hm' : ismarked io = false := by simpa using hm
    simp [seek, hs, hm', throwArg]

theorem seek_pos {io : IOBuf} (h : Inv io) (n : I) :
    (position { io with ptr := clampI (translateSeekPosition io n) (getOffset io + i 1) (io.size + i 1) }).val =
      max ((getOffset io).val + 1) (min (max (-2 ^ 63) (min (n.val + io.oc.val + 1) (2 ^ 63 - 1)))
        (io.size.val + 1)) - io.oc.val - 1 := by
  have f := invFacts h
  have hlo : (getOffset io + i 1).val = (getOffset io).val + 1 := add_one_val (by omega)
  have hhi : (io.size + i 1).val = io.size.val + 1 := add_one_val (by omega)
  have hc := clampI_val (translateSeekPosition io n) (getOffset io + i 1) (io.size + i 1) (by omega)
  rw [hlo, hhi, translate_val] at hc
  rw [position_ptr io (clampI (translateSeekPosition io n) (getOffset io + i 1) (io.size + i 1))
    (by omega) (by omega), hc]

theorem seek_seekable {io : IOBuf} (h : Inv io) (hs : io.seekable = true) (n : I) :
    ∃ s, (seek n).run io = .ok () s ∧ (position s).val = max 0 (min n.val (filesize io).val) := by
  have f := invFacts h
  have hoc := h.oc_seekable hs
  have hfs := filesize_val h hs
  have hn := I_bounds n
  refine ⟨_, seek_run_ok io n (Or.inl hs), ?_⟩
  rw [seek_pos h, hfs]
  omega

end OpP

open OpP

theorem occursinSpec_of_inv (hinv : ∀ io, Reachable io → Inv io) : OccursinSpec := by
  intro io hr d
  have h := hinv io hr
  unfold occursin
  rw [pending_eq h]
  show Except.ok ((avail io).contains d) = _
  congr 1
  simp

theorem seekSpec_of_inv (hinv : ∀ io, Reachable io → Inv io) : SeekSpec := by
  intro io hr n
  have h := hinv io hr
  have f := invFacts h
  have hc := clampToI_val n
  constructor
  · intro hs
    obtain ⟨s, hrun, hpos⟩ := seek_seekable h hs (clampToI n)
    have hfs := filesize_val h hs
    refine ⟨resultOf_ok hrun, ?_⟩
    have hst : stateOf (seekAny n) io = s := stateOf_ok hrun
    rw [hst, hpos, hc]
    omega
  · intro hs
    have hmi := ismarked_iff io
    have heq : clampToI n = io.mark ↔ n = io.mark.val := by
      constructor
      · intro he
        have := congrArg Subtype.val he
        omega
      · intro he
        apply Subtype.ext
        omega
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ⟨e, he⟩ ⟨hm, hn⟩
      have hceq : clampToI n = io.mark := heq.mpr hn
      have hok : resultOf (seekAny n) io = .ok () := resultOf_ok (seek_run_ok io _ (Or.inr ⟨hm, hceq⟩))
      rw [hok] at he
      cases he
    · intro hnot
      have hc' : ¬ (ismarked io = true ∧ clampToI n = io.mark) := fun ⟨hm, hceq⟩ =>
        hnot ⟨hm, heq.mp hceq⟩
      obtain ⟨e, he⟩ := seek_run_err io (clampToI n) hs hc'
      exact ⟨e, resultOf_err he⟩
    · intro hm hn
      have hceq : clampToI n = io.mark := heq.mpr hn
      have hrun := seek_run_ok io _ (Or.inr ⟨hm, hceq⟩)
      have hst : stateOf (seekAny n) io = _ := stateOf_ok hrun
      have hp := h.mark_pipe hs (hmi.mp hm)
      have hpos := position_val h
      rw [hst, seek_pos h]
      omega

theorem skipSpec_of_inv (hinv : ∀ io, Reachable io → Inv io) : SkipSpec := by
  intro io hr n
  have h := hinv io hr
  have f := invFacts h
  have hc := clampToI_val n
  have hpos := position_val h
  have hba := ba_val h
  constructor
  · intro hn
    have hnn : ¬ (clampToI n).val < 0 := by omega
    have hnmax : (io.size + i 1 - io.ptr).val = io.size.val + 1 - io.ptr.val := by
      have h1 : (io.size + i 1).val = io.size.val + 1 := add_one_val (by omega)
      rw [sub_val (by rw [h1]; omega) (by rw [h1]; omega), h1]
    have hmin := imin_val (clampToI n) (io.size + i 1 - io.ptr)
    rw [hnmax] at hmin
    have hadd : (io.ptr + imin (clampToI n) (io.size + i 1 - io.ptr)).val =
        io.ptr.val + min (clampToI n).val (io.size.val + 1 - io.ptr.val) := by
      rw [add_val (by rw [hmin]; omega) (by rw [hmin]; omega), hmin]
    have hrun : (skip n).run io =
        .ok () { io with ptr := io.ptr + imin (clampToI n) (io.size + i 1 - io.ptr) } := by
      simp [skip, hnn]
    refine ⟨resultOf_ok hrun, ?_⟩
    rw [stateOf_ok hrun, position_ptr io (io.ptr + imin (clampToI n) (io.size + i 1 - io.ptr))
      (by rw [hadd]; omega) (by rw [hadd]; omega), hadd, hpos, hba]
    omega
  · intro hn hs
    have hneg : (clampToI n).val < 0 := by omega
    have hrun : (skip n).run io = (seek (clampToI ((position io).val + (clampToI n).val))).run io := by
      simp [skip, hneg]
    obtain ⟨s, hs1, hs2⟩ := seek_seekable h hs (clampToI ((position io).val + (clampToI n).val))
    have hfs := filesize_val h hs
    have hoc := h.oc_seekable hs
    rw [hs1] at hrun
    refine ⟨resultOf_ok hrun, ?_⟩
    rw [stateOf_ok hrun, hs2, clampToI_val, hfs, hpos]
    omega

end JuliaLean.IOBuffers
