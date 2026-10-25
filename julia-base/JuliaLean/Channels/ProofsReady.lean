import JuliaLean.Channels.ProofsDefs
import JuliaLean.Channels.ProofsLemmas

namespace JuliaLean.Channels

private theorem countP_pos_lookup (p : Task → Bool) (ts : List Task) :
    0 < ts.countP p ↔ ∃ (i : Nat) (t : Task), ts[i]? = some t ∧ t ∈ ts ∧ p t = true := by
  induction ts with
  | nil => simp
  | cons a ts ih =>
    constructor
    · intro h
      by_cases ha : p a = true
      · exact ⟨0, a, rfl, by simp, ha⟩
      · have ht : 0 < ts.countP p := by simpa [List.countP_cons, ha] using h
        obtain ⟨i, t, hi, hm, hp⟩ := ih.mp ht
        exact ⟨i + 1, t, by simpa using hi, by simp [hm], hp⟩
    · rintro ⟨i, t, hi, _, hp⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst t
        simp [hp]
      | succ i =>
        have ht : ts[i]? = some t := by simpa using hi
        have hm : t ∈ ts := List.mem_of_getElem? ht
        have hc := ih.mpr ⟨i, t, ht, hm, hp⟩
        simp only [List.countP_cons]
        split <;> omega

private theorem pendingPut_unbuffered_iff (t : Task) (h : PcFits 0 t.op t.pc) :
    pendingPut t = true ↔
      (∃ v, t.pc = .parked (.putUnb v)) ∨
        ∃ v w, t.pc = .woken (.putUnb v) w := by
  cases t with
  | mk op pc =>
    cases pc with
    | parked k => cases k <;> simp_all [pendingPut, PcFits, ParkFits]
    | woken k w => cases k <;> simp_all [pendingPut, PcFits, ParkFits]
    | _ => simp [pendingPut]

theorem isreadyUnbuffered_of_inv {ops : List Op} {s : St}
    (hf : FitInv 0 ops s) (hq : QueueInv 0 s) :
    (0 < s.ch.nAvail ↔ ∃ i v,
      pcOf s i = some (.parked (.putUnb v)) ∨
        ∃ w, pcOf s i = some (.woken (.putUnb v) w)) := by
  have hav : s.ch.nAvail = (s.tasks.countP pendingPut : Int) := by
    have hb := hq.buffer
    have ha := hq.availability
    omega
  constructor
  · intro hn
    have hc : 0 < s.tasks.countP pendingPut := by omega
    obtain ⟨i, t, hi, hm, hp⟩ := (countP_pos_lookup pendingPut s.tasks).mp hc
    have ht := (pendingPut_unbuffered_iff t (hf.fits t hm)).mp hp
    rcases ht with ⟨v, hv⟩ | ⟨v, w, hv⟩
    · exact ⟨i, v, Or.inl (by simp [pcOf, hi, hv])⟩
    · exact ⟨i, v, Or.inr ⟨w, by simp [pcOf, hi, hv]⟩⟩
  · rintro ⟨i, v, hi⟩
    have hc : 0 < s.tasks.countP pendingPut := by
      rcases hi with hi | ⟨w, hi⟩
      · cases ht : s.tasks[i]? with
        | none => simp [pcOf, ht] at hi
        | some t =>
          have hpc : t.pc = .parked (.putUnb v) := by simpa [pcOf, ht] using hi
          exact (countP_pos_lookup pendingPut s.tasks).mpr
            ⟨i, t, ht, List.mem_of_getElem? ht, by simp [pendingPut, hpc]⟩
      · cases ht : s.tasks[i]? with
        | none => simp [pcOf, ht] at hi
        | some t =>
          have hpc : t.pc = .woken (.putUnb v) w := by simpa [pcOf, ht] using hi
          exact (countP_pos_lookup pendingPut s.tasks).mpr
            ⟨i, t, ht, List.mem_of_getElem? ht, by simp [pendingPut, hpc]⟩
    omega

end JuliaLean.Channels
