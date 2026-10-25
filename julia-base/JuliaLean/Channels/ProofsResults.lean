import JuliaLean.Channels.ProofsDefs
import JuliaLean.Channels.ProofsLemmas

namespace JuliaLean.Channels

variable {sz : Nat} {ops : List Op} {s s' : St} {i : Nat}
  {t : Task} {pc : Pc}

private theorem setPc_pc (ht : s.tasks[i]? = some t) :
    (setPc s.tasks i pc)[i]?.map Task.pc = some pc := by
  simp [setPc_getElem?, ht]

private theorem fetchBody_keeps (ht : s.tasks[i]? = some t) :
    (fetchBody s i).ch.data = s.ch.data ∧
    ∀ v, ((fetchBody s i).tasks[i]?.map Task.pc) = some (.done (.ok (some v))) →
      s.ch.data.head? = some v := by
  unfold fetchBody
  split
  · split
    · constructor
      · rfl
      · intro v hv
        simp [St.finish, setPc_getElem?, ht] at hv
    · constructor
      · rfl
      · intro v hv
        simp [St.parkTake, setPc_getElem?, ht] at hv
  · constructor
    · rfl
    · intro v hv
      simp [St.finish, setPc_getElem?, ht] at hv
      simp_all

theorem fetchKeeps_of_fit (hf : FitInv sz ops s)
    (hop : s.tasks[i]?.map Task.op = some .fetch) (hs : stepTask s i = some s') :
    s'.ch.data = s.ch.data ∧
    ∀ v, s'.tasks[i]?.map Task.pc = some (.done (.ok (some v))) →
      s.ch.data.head? = some v := by
  cases ht : s.tasks[i]? with
  | none => simp [ht] at hop
  | some t =>
    have hp := hf.fits t (List.mem_of_getElem? ht)
    have ho : t.op = .fetch := by simpa [ht] using hop
    have herr : ∀ e, (s.finish i (.err e)).ch.data = s.ch.data ∧
        ∀ v, (s.finish i (.err e)).tasks[i]?.map Task.pc = some (.done (.ok (some v))) →
          s.ch.data.head? = some v := by
      intro e
      refine ⟨rfl, ?_⟩
      intro v hv
      simp [St.finish, setPc_getElem?, ht] at hv
    cases hc : t.pc with
    | start =>
      simp only [stepTask, ht, ho, hc] at hs
      split at hs
      · cases hs; exact herr _
      · cases hs; exact fetchBody_keeps ht
    | putLocked v => simp [PcFits, hc, ho] at hp
    | takeLocked it => simp [PcFits, hc, ho] at hp
    | waitLocked => simp [PcFits, hc, ho] at hp
    | handoff v j => simp [PcFits, hc, ho] at hp
    | done r => simp [stepTask, ht, ho, hc] at hs
    | parked k => simp [stepTask, ht, ho, hc] at hs
    | woken k w =>
      cases k with
      | putBuf v => simp [PcFits, ParkFits, hc, ho] at hp
      | putUnb v => simp [PcFits, ParkFits, hc, ho] at hp
      | take it => cases it <;> simp [PcFits, ParkFits, hc, ho] at hp
      | takeUnb it => cases it <;> simp [PcFits, ParkFits, hc, ho] at hp
      | wait => simp [PcFits, ParkFits, hc, ho] at hp
      | fetch =>
        cases w <;> simp only [stepTask, ht, ho, hc, Option.some.injEq] at hs
        all_goals subst s'
        all_goals first | exact fetchBody_keeps ht | exact herr _

 theorem takeClosedEmptyThrows_of_state (hc : s.ch.isOpen = false) (hd : s.ch.data = [])
    (ht : s.tasks[i]? = some { op := .take, pc := .start }) :
    ∃ s', stepTask s i = some s' ∧
      s'.tasks[i]?.map Task.pc = some (.done (.err s.ch.excp)) := by
  refine ⟨s.finish i (.err s.ch.excp), ?_, ?_⟩
  · simp [stepTask, ht, takeBody, takeUnbStart, takeBufBody, hc, hd, finishTake]
  · exact setPc_pc ht

 theorem closeWakesWaiters_of_queue (hq : QueueInv sz s) (hc : s.ch.isOpen = false) :
    s.ch.qTake = [] ∧ s.ch.qPut = [] ∧ s.ch.qWait = [] ∧
    ∀ i k, pcOf s i = some (.parked k) →
      ∃ j v, pcOf s j = some (.handoff v i) := by
  obtain ⟨ht, hp, hw⟩ := hq.closedQueues hc
  refine ⟨ht, hp, hw, ?_⟩
  intro i k hk
  have hh := hq.parkedCovered i k hk
  simpa [ht, hp, hw] using hh

 theorem noLostWakeup_of_queue (hq : QueueInv sz s) :
    (0 < sz →
      (s.ch.qTake ≠ [] → s.ch.data = []) ∧
      (s.ch.qPut ≠ [] → sz ≤ s.ch.data.length + wokenPutBuf s)) ∧
    (sz = 0 →
      (s.ch.qPut ≠ [] → s.ch.qTake ≠ [] → 0 < wokenPutUnb s) ∧
      (s.ch.qWait ≠ [] → s.ch.nAvail = 0)) := by
  constructor
  · intro hsz
    exact ⟨hq.bufferedTake hsz, hq.bufferedPut hsz⟩
  · intro hsz
    refine ⟨?_, hq.unbufferedWait hsz⟩
    intro hp ht
    have hh := hq.unbufferedPut hsz hp
    have : 0 < s.ch.qTake.length := List.length_pos_iff.mpr ht
    omega

private theorem setPc_pc_eq {ts : List Task} {pc pc' : Pc}
    (h : (setPc ts i pc)[i]?.map Task.pc = some pc') : pc = pc' := by
  rw [setPc_getElem?] at h
  simp only [ite_true, Option.map_map] at h
  cases hi : ts[i]? <;> simp_all

private theorem takeBufBody_none
    (h : (takeBufBody s i true).tasks[i]?.map Task.pc = some (.done (.ok none))) :
    s.ch.isOpen = false ∧ s.ch.data = [] := by
  unfold takeBufBody at h
  split at h
  · rename_i hd
    split at h
    · exact ⟨by simpa using ‹(!s.ch.isOpen) = true›, hd⟩
    · have he := setPc_pc_eq h
      contradiction
  · have he := setPc_pc_eq h
    simp [finishTake] at he

private theorem takeBody_none (hq : QueueInv sz s) (hf : FitInv sz ops s)
    (h : (takeBody s i true).tasks[i]?.map Task.pc = some (.done (.ok none))) :
    s.ch.isOpen = false ∧ s.ch.data = [] := by
  unfold takeBody at h
  split at h
  · have hsz : sz = 0 := by have := hf.capacity; omega
    have hd : s.ch.data = [] := by
      have hh := hq.buffer
      rw [hsz] at hh
      exact List.eq_nil_of_length_eq_zero (by omega)
    unfold takeUnbStart at h
    split at h
    · exact ⟨by simpa using ‹(!s.ch.isOpen) = true›, hd⟩
    · have he := setPc_pc_eq h
      contradiction
  · exact takeBufBody_none h

theorem iterateEndsDrained_of_inv (hf : FitInv sz ops s) (hq : QueueInv sz s)
    (hop : s.tasks[i]?.map Task.op = some .iter) (hs : stepTask s i = some s')
    (hr : s'.tasks[i]?.map Task.pc = some (.done (.ok none))) :
    s.ch.isOpen = false ∧ s.ch.data = [] := by
  have emptyOfNonpositive (hn : s.ch.nAvail ≤ 0) : s.ch.data = [] := by
    have ha := hq.availability
    have hl : s.ch.data.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero hl
  cases ht : s.tasks[i]? with
  | none => simp [ht] at hop
  | some t =>
    have hp := hf.fits t (List.mem_of_getElem? ht)
    have ho : t.op = .iter := by simpa [ht] using hop
    cases hc : t.pc with
    | start =>
      by_cases hg : s.ch.isOpen = true ∨ 0 < s.ch.nAvail
      · have he : s' = s.goto i (.takeLocked true) := by
          simpa [stepTask, ht, ho, hc, hg] using hs.symm
        subst s'
        have hh := setPc_pc_eq hr
        contradiction
      · have hopen : s.ch.isOpen = false := by
          cases hb : s.ch.isOpen <;> simp_all
        exact ⟨hopen, emptyOfNonpositive (by omega)⟩
    | putLocked v => simp [PcFits, hc, ho] at hp
    | waitLocked => simp [PcFits, hc, ho] at hp
    | handoff v j => simp [PcFits, hc, ho] at hp
    | done r => simp [stepTask, ht, ho, hc] at hs
    | parked k => simp [stepTask, ht, ho, hc] at hs
    | takeLocked it =>
      have hit : it = true := (by simpa [PcFits, hc, ho] using hp)
      subst it
      have he : s' = takeBody s i true := by
        simpa [stepTask, ht, ho, hc] using hs.symm
      subst s'
      exact takeBody_none hq hf hr
    | woken k w =>
      cases k with
      | putBuf v => simp [PcFits, ParkFits, hc, ho] at hp
      | putUnb v => simp [PcFits, ParkFits, hc, ho] at hp
      | fetch => simp [PcFits, ParkFits, hc, ho] at hp
      | wait => simp [PcFits, ParkFits, hc, ho] at hp
      | take it =>
        cases it with
        | false => simp [PcFits, ParkFits, hc, ho] at hp
        | true =>
          cases w with
          | err e =>
            have hpc : pcOf s i = some (.woken (.take true) (.err e)) := by
              simp [pcOf, ht, hc]
            exact ⟨hq.wakeError i _ e hpc, hq.takeErrorEmpty i true e hpc⟩
          | none | val v =>
            have he : s' = takeBufBody s i true := by
              simpa [stepTask, ht, ho, hc] using hs.symm
            subst s'
            exact takeBufBody_none hr
      | takeUnb it =>
        cases it with
        | false => simp [PcFits, ParkFits, hc, ho] at hp
        | true =>
          cases w with
          | none =>
            have hh := hq.wakeValues i (.takeUnb true) .none (by simp [pcOf, ht, hc])
            exact False.elim hh
          | val v =>
            have he : s' = s.finish i (.ok (some v)) := by
              simpa [stepTask, ht, ho, hc] using hs.symm
            subst s'
            have hh := setPc_pc_eq hr
            simp at hh
          | err e =>
            have hpc : pcOf s i = some (.woken (.takeUnb true) (.err e)) := by
              simp [pcOf, ht, hc]
            have hsz : sz = 0 := (by simpa [PcFits, ParkFits, hc, ho] using hp)
            have hd : s.ch.data = [] := by
              have hb := hq.buffer
              rw [hsz] at hb
              exact List.eq_nil_of_length_eq_zero (by omega)
            exact ⟨hq.wakeError i _ e hpc, hd⟩

end JuliaLean.Channels
