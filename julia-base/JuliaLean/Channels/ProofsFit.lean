import JuliaLean.Channels.ProofsDefs
import JuliaLean.Channels.ProofsLemmas

namespace JuliaLean.Channels

variable {sz : Nat} {ops : List Op} {s s' : St} {ts : List Task}
  {i j : Nat} {t : Task} {pc : Pc} {op : Op} {k : Park} {w : Wake}
  {q : List Nat} {v : Val} {it : Bool} {e : Exc} {r : Res}

private def Fits (sz : Nat) (ts : List Task) : Prop :=
  ∀ t ∈ ts, PcFits sz t.op t.pc

private theorem fits_get (h : Fits sz ts) (ht : ts[i]? = some t) : PcFits sz t.op t.pc :=
  h t (List.mem_of_getElem? ht)

private theorem fits_setPc (h : Fits sz ts)
    (hp : ∀ t, ts[i]? = some t → PcFits sz t.op pc) : Fits sz (setPc ts i pc) := by
  induction ts generalizing i with
  | nil => simp [Fits, setPc]
  | cons t ts ih =>
    have hh : PcFits sz t.op t.pc ∧ Fits sz ts := by simpa [Fits] using h
    cases i with
    | zero => simpa [Fits, setPc] using And.intro (hp t rfl) hh.2
    | succ i =>
      have hp' : ∀ t, ts[i]? = some t → PcFits sz t.op pc := by
        intro u hu
        exact hp u (by simpa using hu)
      simpa [Fits, setPc] using And.intro hh.1 (ih hh.2 hp')

private theorem fits_setPc_op (h : Fits sz ts) (hop : ts[i]?.map Task.op = some op)
    (hp : PcFits sz op pc) : Fits sz (setPc ts i pc) := by
  apply fits_setPc h
  intro t ht
  have he : t.op = op := by simpa [ht] using hop
  simpa [he] using hp

private theorem fits_wake (h : Fits sz ts) : Fits sz (wake ts i w) := by
  induction ts generalizing i with
  | nil => simp [Fits, wake]
  | cons t ts ih =>
    have hh : PcFits sz t.op t.pc ∧ Fits sz ts := by simpa [Fits] using h
    cases i with
    | zero => cases hp : t.pc <;> simp_all [Fits, wake, PcFits]
    | succ i => simpa [Fits, wake] using And.intro hh.1 (ih hh.2)

private theorem fits_wakeAll (h : Fits sz ts) : Fits sz (wakeAll ts q w) := by
  induction q generalizing ts with
  | nil => exact h
  | cons j q ih => exact ih (fits_wake h)

@[simp] private theorem opAt_wakeAll :
    (wakeAll ts q w)[i]?.map Task.op = ts[i]?.map Task.op := by
  rw [wakeAll_getElem?]
  split <;> simp_all [Option.map_map, Function.comp_def]

@[simp] private theorem opAt_wake :
    (wake ts j w)[i]?.map Task.op = ts[i]?.map Task.op := by
  rw [wake_getElem?]
  split <;> simp_all [Option.map_map, Function.comp_def]

private theorem fits_finish (h : Fits sz s.tasks) : Fits sz (s.finish i r).tasks :=
  fits_setPc h (by intros; trivial)

private theorem fits_notifyPutOne (h : Fits sz s.tasks) : Fits sz s.notifyPutOne.tasks := by
  unfold St.notifyPutOne
  split <;> first | exact h | exact fits_wake h

@[simp] private theorem opAt_notifyPutOne :
    s.notifyPutOne.tasks[i]?.map Task.op = s.tasks[i]?.map Task.op := by
  unfold St.notifyPutOne
  split <;> simp

private theorem fits_putBufBody (h : Fits sz s.tasks) (hsz : 0 < sz)
    (hop : s.tasks[i]?.map Task.op = some (.put v)) : Fits sz (putBufBody s i v).tasks := by
  unfold putBufBody
  split
  · exact fits_finish h
  · split
    · exact fits_setPc_op h hop ⟨rfl, hsz⟩
    · exact fits_finish (fits_wakeAll h)

private theorem fits_putUnbBody (h : Fits sz s.tasks) (hsz : sz = 0)
    (hop : s.tasks[i]?.map Task.op = some (.put v)) : Fits sz (putUnbBody s i v).tasks := by
  unfold putUnbBody
  split
  · exact fits_finish h
  · split
    · apply fits_setPc_op (fits_wakeAll h) (op := .put v)
      · simpa only [St.notifyWaitAll, opAt_wakeAll] using hop
      · exact ⟨rfl, hsz⟩
    · exact fits_setPc_op h hop ⟨rfl, hsz⟩

private theorem fits_takeBufBody (h : Fits sz s.tasks) (hsz : 0 < sz)
    (hop : s.tasks[i]?.map Task.op = some (if it then .iter else .take)) :
    Fits sz (takeBufBody s i it).tasks := by
  unfold takeBufBody
  split
  · split
    · exact fits_finish h
    · apply fits_setPc_op h hop
      cases it <;> exact ⟨rfl, hsz⟩
  · exact fits_finish (fits_notifyPutOne h)

private theorem fits_takeBody (h : Fits sz s.tasks) (hcap : s.ch.sz = sz)
    (hop : s.tasks[i]?.map Task.op = some (if it then .iter else .take)) :
    Fits sz (takeBody s i it).tasks := by
  unfold takeBody
  split
  · unfold takeUnbStart
    split
    · exact fits_finish h
    · apply fits_setPc_op (fits_notifyPutOne h) (op := if it then .iter else .take)
      · simpa using hop
      · cases it <;> exact ⟨rfl, by omega⟩
  · exact fits_takeBufBody h (by omega) hop

private theorem fits_fetchBody (h : Fits sz s.tasks) (hsz : 0 < sz)
    (hop : s.tasks[i]?.map Task.op = some .fetch) : Fits sz (fetchBody s i).tasks := by
  unfold fetchBody
  split
  · split
    · exact fits_finish h
    · exact fits_setPc_op h hop ⟨rfl, hsz⟩
  · exact fits_finish h

private theorem fits_waitBody (h : Fits sz s.tasks)
    (hop : s.tasks[i]?.map Task.op = some .wait) : Fits sz (waitBody s i).tasks := by
  unfold waitBody
  split
  · exact fits_finish h
  · split
    · exact fits_finish h
    · split <;> exact fits_setPc_op h hop rfl

private theorem putBuf_shape (s : St) (i : Nat) (v : Val) :
    (putBufBody s i v).ch.sz = s.ch.sz ∧
    (putBufBody s i v).tasks.map Task.op = s.tasks.map Task.op := by
  unfold putBufBody
  repeat' split
  all_goals simp [St.finish, St.addAvail, St.parkPut, St.notifyTakeAll]

private theorem putUnb_shape (s : St) (i : Nat) (v : Val) :
    (putUnbBody s i v).ch.sz = s.ch.sz ∧
    (putUnbBody s i v).tasks.map Task.op = s.tasks.map Task.op := by
  unfold putUnbBody
  repeat' split
  all_goals simp [St.finish, St.addAvail, St.parkPut, St.notifyWaitAll, St.goto]

private theorem takeBuf_shape (s : St) (i : Nat) (it : Bool) :
    (takeBufBody s i it).ch.sz = s.ch.sz ∧
    (takeBufBody s i it).tasks.map Task.op = s.tasks.map Task.op := by
  unfold takeBufBody
  repeat' split
  all_goals simp only [St.finish, St.addAvail, St.parkTake, St.notifyPutOne]
  all_goals repeat' split
  all_goals simp

private theorem take_shape (s : St) (i : Nat) (it : Bool) :
    (takeBody s i it).ch.sz = s.ch.sz ∧
    (takeBody s i it).tasks.map Task.op = s.tasks.map Task.op := by
  unfold takeBody
  split
  · unfold takeUnbStart
    split
    · simp [St.finish]
    · simp only [St.parkTake, St.notifyPutOne]
      split <;> simp
  · exact takeBuf_shape s i it

private theorem fetch_shape (s : St) (i : Nat) :
    (fetchBody s i).ch.sz = s.ch.sz ∧
    (fetchBody s i).tasks.map Task.op = s.tasks.map Task.op := by
  unfold fetchBody
  repeat' split
  all_goals simp [St.finish, St.parkTake]

private theorem wait_shape (s : St) (i : Nat) :
    (waitBody s i).ch.sz = s.ch.sz ∧
    (waitBody s i).tasks.map Task.op = s.tasks.map Task.op := by
  unfold waitBody
  repeat' split
  all_goals simp [St.finish, St.parkTake, St.parkWait]

private theorem close_shape (s : St) (i : Nat) (e : Exc) :
    (closeBody s i e).ch.sz = s.ch.sz ∧
    (closeBody s i e).tasks.map Task.op = s.tasks.map Task.op := by
  simp [closeBody, St.finish, St.notifyTakeAll, St.notifyPutAll, St.notifyWaitAll]

private theorem empty_shape (s : St) (i : Nat) :
    (emptyBody s i).ch.sz = s.ch.sz ∧
    (emptyBody s i).tasks.map Task.op = s.tasks.map Task.op := by
  simp [emptyBody, St.finish, St.notifyPutAll, St.addAvail]

 theorem fitInv_init : FitInv sz ops (init sz ops) := by
  constructor
  · rfl
  · simp [init, Function.comp_def]
  · intro t ht
    simp only [init, List.mem_map] at ht
    obtain ⟨op, _, rfl⟩ := ht
    trivial

private theorem step_shape (hs : stepTask s i = some s') :
    s'.ch.sz = s.ch.sz ∧ s'.tasks.map Task.op = s.tasks.map Task.op := by
  unfold stepTask at hs
  repeat' split at hs
  all_goals try { contradiction }
  all_goals
    simp only [Option.some.injEq] at hs
    subst s'
    first
    | apply putBuf_shape
    | apply putUnb_shape
    | apply take_shape
    | apply takeBuf_shape
    | apply fetch_shape
    | apply wait_shape
    | apply close_shape
    | apply empty_shape
    | simp [St.finish, St.goto, St.addAvail]

theorem fitInv_step (hf : FitInv sz ops s) (hs : stepTask s i = some s') :
    FitInv sz ops s' := by
  have shape := step_shape hs
  refine ⟨shape.1.trans hf.capacity, shape.2.trans hf.operations, ?_⟩
  have hh : Fits sz s.tasks := hf.fits
  have hcap := hf.capacity
  cases ht : s.tasks[i]? with
  | none => simp [stepTask, ht] at hs
  | some t =>
    have hp := fits_get hh ht
    rcases t with ⟨op, pc⟩
    have hop : s.tasks[i]?.map Task.op = some op := by simp [ht]
    cases pc with
    | start =>
      cases op with
      | put v =>
        simp only [stepTask, ht] at hs
        split at hs <;> cases hs
        · exact fits_finish hh
        · exact fits_setPc_op hh hop rfl
      | take =>
        simp only [stepTask, ht, Option.some.injEq] at hs
        subst s'
        exact fits_takeBody hh hcap hop
      | iter =>
        simp only [stepTask, ht] at hs
        split at hs <;> cases hs
        · exact fits_setPc_op hh hop ⟨rfl, rfl⟩
        · exact fits_finish hh
      | fetch =>
        simp only [stepTask, ht] at hs
        split at hs <;> cases hs
        · exact fits_finish hh
        · exact fits_fetchBody hh (by omega) hop
      | wait =>
        simp only [stepTask, ht] at hs
        split at hs <;> cases hs
        · exact fits_finish hh
        · exact fits_setPc_op hh hop rfl
      | close e =>
        simp only [stepTask, ht, Option.some.injEq] at hs
        subst s'
        exact fits_finish (fits_wakeAll (fits_wakeAll (fits_wakeAll hh)))
      | empty =>
        simp only [stepTask, ht, Option.some.injEq] at hs
        subst s'
        exact fits_finish (fits_wakeAll hh)
    | putLocked v =>
      change op = .put v at hp
      subst op
      simp only [stepTask, ht] at hs
      split at hs <;> cases hs
      · exact fits_putUnbBody hh (by omega) hop
      · exact fits_putBufBody hh (by omega) hop
    | takeLocked it =>
      change op = .iter ∧ it = true at hp
      rcases hp with ⟨rfl, rfl⟩
      simp only [stepTask, ht, Option.some.injEq] at hs
      subst s'
      exact fits_takeBody hh hcap hop
    | waitLocked =>
      change op = .wait at hp
      subst op
      simp only [stepTask, ht, Option.some.injEq] at hs
      subst s'
      exact fits_waitBody hh hop
    | parked k => cases op <;> simp [stepTask, ht] at hs
    | done r => cases op <;> simp [stepTask, ht] at hs
    | handoff v j =>
      change op = .put v ∧ sz = 0 at hp
      rcases hp with ⟨rfl, _⟩
      simp only [stepTask, ht, Option.some.injEq] at hs
      subst s'
      exact fits_finish (fits_wake hh)
    | woken k w =>
      cases k with
      | putBuf v =>
        change op = .put v ∧ 0 < sz at hp
        rcases hp with ⟨rfl, hsz⟩
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at hs <;> subst s'
        all_goals first
          | exact fits_finish hh
          | exact fits_putBufBody hh hsz hop
      | putUnb v =>
        change op = .put v ∧ sz = 0 at hp
        rcases hp with ⟨rfl, hsz⟩
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at hs <;> subst s'
        all_goals first
          | exact fits_finish hh
          | exact fits_putUnbBody hh hsz hop
      | take it =>
        cases it <;> simp only [PcFits, ParkFits] at hp <;>
          rcases hp with ⟨rfl, hsz⟩ <;> cases w <;>
          simp only [stepTask, ht, Option.some.injEq] at hs <;> subst s'
        all_goals first
          | exact fits_finish hh
          | exact fits_takeBufBody hh hsz hop
      | takeUnb it =>
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at hs <;> subst s'
        all_goals exact fits_finish hh
      | fetch =>
        change op = .fetch ∧ 0 < sz at hp
        rcases hp with ⟨rfl, hsz⟩
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at hs <;> subst s'
        all_goals first
          | exact fits_finish hh
          | exact fits_fetchBody hh hsz hop
      | wait =>
        change op = .wait at hp
        subst op
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at hs <;> subst s'
        all_goals first
          | exact fits_finish hh
          | exact fits_waitBody hh hop

end JuliaLean.Channels
