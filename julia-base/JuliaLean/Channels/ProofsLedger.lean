import JuliaLean.Channels.ProofsDefs
import JuliaLean.Channels.ProofsLemmas

namespace JuliaLean.Channels

private theorem credit_wake_none (x : Val) (t : Task) :
    ledgerCredit x (wakeT .none t) = ledgerCredit x t := by
  rcases t with ⟨op, pc⟩
  cases pc <;> simp [wakeT, ledgerCredit]

private theorem credit_wake_err (x : Val) (e : Exc) (t : Task) :
    ledgerCredit x (wakeT (.err e) t) = ledgerCredit x t := by
  rcases t with ⟨op, pc⟩
  cases pc <;> simp [wakeT, ledgerCredit]

@[simp] private theorem sum_wake_none (x : Val) (ts : List Task) (i : Nat) :
    tsum (ledgerCredit x) (wake ts i .none) = tsum (ledgerCredit x) ts :=
  tsum_wake_of_inv _ _ _ _ (credit_wake_none x)

@[simp] private theorem sum_wake_err (x : Val) (ts : List Task) (i : Nat) (e : Exc) :
    tsum (ledgerCredit x) (wake ts i (.err e)) = tsum (ledgerCredit x) ts :=
  tsum_wake_of_inv _ _ _ _ (credit_wake_err x e)

@[simp] private theorem sum_wakeAll_none (x : Val) (ts : List Task) (q : List Nat) :
    tsum (ledgerCredit x) (wakeAll ts q .none) = tsum (ledgerCredit x) ts :=
  tsum_wakeAll_of_inv _ _ _ _ (credit_wake_none x)

@[simp] private theorem sum_wakeAll_err (x : Val) (ts : List Task) (q : List Nat) (e : Exc) :
    tsum (ledgerCredit x) (wakeAll ts q (.err e)) = tsum (ledgerCredit x) ts :=
  tsum_wakeAll_of_inv _ _ _ _ (credit_wake_err x e)

private theorem sum_setPc_lookup (x : Val) (ts : List Task) (i : Nat) (pc : Pc)
    (t : Task) (h : ts[i]? = some t) :
    tsum (ledgerCredit x) (setPc ts i pc) =
      tsum (ledgerCredit x) ts - ledgerCredit x t + ledgerCredit x {t with pc := pc} := by
  have hi : i < ts.length := List.getElem?_eq_some_iff.mp h |>.1
  have ht : ts[i] = t := by simpa [List.getElem?_eq_getElem hi] using h
  simpa [ht] using tsum_setPc (ledgerCredit x) ts i pc hi

private theorem sum_setPc_zero (x : Val) (ts : List Task) (i : Nat) (pc : Pc)
    (t : Task) (h : ts[i]? = some t)
    (hc : ledgerCredit x {t with pc := pc} = ledgerCredit x t) :
    tsum (ledgerCredit x) (setPc ts i pc) = tsum (ledgerCredit x) ts := by
  rw [sum_setPc_lookup x ts i pc t h, hc]
  omega

private theorem lookup_wake_active (ts : List Task) (i j : Nat) (w : Wake)
    (t : Task) (h : ts[i]? = some t) (ha : ∀ k, t.pc ≠ .parked k) :
    (wake ts j w)[i]? = some t := by
  rw [wake_getElem?]
  split <;> simp_all [wakeT]

private theorem lookup_wakeAll_active (ts : List Task) (q : List Nat) (i : Nat) (w : Wake)
    (t : Task) (h : ts[i]? = some t) (ha : ∀ k, t.pc ≠ .parked k) :
    (wakeAll ts q w)[i]? = some t := by
  rw [wakeAll_getElem?]
  split <;> simp_all [wakeT]

private theorem credit_finishTake_err (x : Val) (op : Op) (it : Bool) (e : Exc)
    (hop : op = .take ∨ op = .iter) :
    ledgerCredit x ⟨op, .done (finishTake it (.err e))⟩ = 0 := by
  rcases hop with rfl | rfl <;> cases it <;> cases e <;> simp [finishTake, ledgerCredit]

private theorem ledger_goto {s : St} (hl : LedgerInv s) (i : Nat) (t : Task) (pc : Pc)
    (ht : s.tasks[i]? = some t)
    (hc : ∀ x, ledgerCredit x {t with pc := pc} = ledgerCredit x t) :
    LedgerInv (s.goto i pc) := by
  intro x
  change tsum (ledgerCredit x) (setPc s.tasks i pc) = _
  rw [sum_setPc_zero x _ _ _ t ht (hc x)]
  exact hl x

private theorem ledger_addAvail {s : St} (hl : LedgerInv s) (n : Int) :
    LedgerInv (s.addAvail n) := hl

private theorem ledger_putBuf {s : St} (hl : LedgerInv s) (i v : Nat) (pc : Pc)
    (ht : s.tasks[i]? = some ⟨.put v, pc⟩)
    (ha : ∀ k, pc ≠ .parked k) (hc : ∀ x, ledgerCredit x ⟨.put v, pc⟩ = 0) :
    LedgerInv (putBufBody s i v) := by
  intro x
  have hs := hl x
  change tsum (ledgerCredit x) s.tasks = _ at hs
  change tsum (ledgerCredit x) (putBufBody s i v).tasks = _
  unfold putBufBody
  split
  · simp only [St.finish, St.addAvail]
    rw [sum_setPc_lookup x _ _ _ _ ht, hc x]
    simpa [ledgerCredit] using hs
  · split
    · simp only [St.parkPut]
      rw [sum_setPc_lookup x _ _ _ _ ht, hc x]
      simpa [ledgerCredit] using hs
    · have hw := lookup_wakeAll_active s.tasks s.ch.qTake i .none ⟨.put v, pc⟩ ht ha
      change tsum (ledgerCredit x) (setPc (wakeAll s.tasks s.ch.qTake .none) i
        (.done (.ok (some v)))) = _
      rw [sum_setPc_lookup x _ _ _ _ hw]
      simp only [sum_wakeAll_none, hc x]
      simp only [St.finish, St.notifyTakeAll]
      simp [ledgerCredit, List.count_append, List.count_singleton, Int.natCast_add]
      split <;> simp_all <;> omega

private theorem ledger_putUnb {s : St} (hl : LedgerInv s) (i v : Nat) (pc : Pc)
    (ht : s.tasks[i]? = some ⟨.put v, pc⟩)
    (ha : ∀ k, pc ≠ .parked k) (hc : ∀ x, ledgerCredit x ⟨.put v, pc⟩ = 0) :
    LedgerInv (putUnbBody s i v) := by
  intro x
  have hs := hl x
  change tsum (ledgerCredit x) s.tasks = _ at hs
  change tsum (ledgerCredit x) (putUnbBody s i v).tasks = _
  unfold putUnbBody
  split
  · simp only [St.finish, St.addAvail]
    rw [sum_setPc_lookup x _ _ _ _ ht, hc x]
    simpa [ledgerCredit] using hs
  · split
    · have hw := lookup_wakeAll_active s.tasks s.ch.qWait i .none ⟨.put v, pc⟩ ht ha
      change tsum (ledgerCredit x) (setPc (wakeAll s.tasks s.ch.qWait .none) i
        (.parked (.putUnb v))) = _
      rw [sum_setPc_lookup x _ _ _ _ hw]
      rw [hc x]
      simpa [St.parkPut, St.notifyWaitAll, ledgerCredit] using hs
    · simp only [St.goto, St.addAvail]
      rw [sum_setPc_lookup x _ _ _ _ ht, hc x]
      simpa [ledgerCredit] using hs

private theorem ledger_takeBuf {s : St} (hl : LedgerInv s) (i : Nat) (it : Bool)
    (op : Op) (pc : Pc) (ht : s.tasks[i]? = some ⟨op, pc⟩)
    (ha : ∀ k, pc ≠ .parked k) (hc : ∀ x, ledgerCredit x ⟨op, pc⟩ = 0)
    (hop : op = .take ∨ op = .iter) :
    LedgerInv (takeBufBody s i it) := by
  intro x
  have hs := hl x
  change tsum (ledgerCredit x) s.tasks = _ at hs
  change tsum (ledgerCredit x) (takeBufBody s i it).tasks = _
  unfold takeBufBody
  split
  · split
    · simp only [St.finish]
      rw [sum_setPc_lookup x _ _ _ _ ht, hc x]
      simpa [credit_finishTake_err x op it s.ch.excp hop] using hs
    · simp only [St.parkTake]
      rw [sum_setPc_lookup x _ _ _ _ ht, hc x]
      simpa [ledgerCredit] using hs
  · rename_i v d hd
    cases hq : s.ch.qPut with
    | nil =>
      simp only [St.addAvail, St.notifyPutOne, hq, St.finish]
      rw [sum_setPc_lookup x _ _ _ _ ht, hc x]
      rcases hop with rfl | rfl <;>
        simp [ledgerCredit, finishTake, hd, List.count_cons] at * <;>
        split <;> simp_all <;> omega
    | cons j q =>
      have hj := lookup_wake_active s.tasks i j .none ⟨op, pc⟩ ht ha
      simp only [St.addAvail, St.notifyPutOne, hq, St.finish]
      rw [sum_setPc_lookup x _ _ _ _ hj, sum_wake_none, hc x]
      rcases hop with rfl | rfl <;>
        simp [ledgerCredit, finishTake, hd, List.count_cons] at * <;>
        split <;> simp_all <;> omega

private theorem ledger_takeUnb {s : St} (hl : LedgerInv s) (i : Nat) (it : Bool)
    (op : Op) (pc : Pc) (ht : s.tasks[i]? = some ⟨op, pc⟩)
    (ha : ∀ k, pc ≠ .parked k) (hc : ∀ x, ledgerCredit x ⟨op, pc⟩ = 0)
    (hop : op = .take ∨ op = .iter) :
    LedgerInv (takeUnbStart s i it) := by
  intro x
  have hs := hl x
  change tsum (ledgerCredit x) s.tasks = _ at hs
  change tsum (ledgerCredit x) (takeUnbStart s i it).tasks = _
  unfold takeUnbStart
  split
  · simp only [St.finish]
    rw [sum_setPc_lookup x _ _ _ _ ht, hc x]
    simpa [credit_finishTake_err x op it s.ch.excp hop] using hs
  · cases hq : s.ch.qPut with
    | nil =>
      simp only [St.notifyPutOne, hq, St.parkTake]
      rw [sum_setPc_lookup x _ _ _ _ ht, hc x]
      simpa [ledgerCredit] using hs
    | cons j q =>
      have hj := lookup_wake_active s.tasks i j .none ⟨op, pc⟩ ht ha
      simp only [St.notifyPutOne, hq, St.parkTake]
      rw [sum_setPc_lookup x _ _ _ _ hj, sum_wake_none, hc x]
      simpa [ledgerCredit] using hs

private theorem ledger_take {s : St} (hl : LedgerInv s) (i : Nat) (it : Bool)
    (op : Op) (pc : Pc) (ht : s.tasks[i]? = some ⟨op, pc⟩)
    (ha : ∀ k, pc ≠ .parked k) (hc : ∀ x, ledgerCredit x ⟨op, pc⟩ = 0)
    (hop : op = .take ∨ op = .iter) :
    LedgerInv (takeBody s i it) := by
  unfold takeBody
  split
  · exact ledger_takeUnb hl i it op pc ht ha hc hop
  · exact ledger_takeBuf hl i it op pc ht ha hc hop

private theorem ledger_fetch {s : St} (hl : LedgerInv s) (i : Nat) (pc : Pc)
    (ht : s.tasks[i]? = some ⟨.fetch, pc⟩)
    (hc : ∀ x, ledgerCredit x ⟨.fetch, pc⟩ = 0) :
    LedgerInv (fetchBody s i) := by
  unfold fetchBody
  split
  · split
    · exact ledger_goto hl i _ _ ht (by intro x; rw [hc x]; simp [ledgerCredit])
    · exact ledger_goto hl i _ _ ht (by intro x; rw [hc x]; simp [ledgerCredit])
  · exact ledger_goto hl i _ _ ht (by intro x; rw [hc x]; simp [ledgerCredit])

private theorem ledger_wait {s : St} (hl : LedgerInv s) (i : Nat) (pc : Pc)
    (ht : s.tasks[i]? = some ⟨.wait, pc⟩)
    (hc : ∀ x, ledgerCredit x ⟨.wait, pc⟩ = 0) :
    LedgerInv (waitBody s i) := by
  unfold waitBody
  split
  · exact ledger_goto hl i _ _ ht (by intro x; rw [hc x]; simp [ledgerCredit])
  · split
    · exact ledger_goto hl i _ _ ht (by intro x; rw [hc x]; simp [ledgerCredit])
    · split
      · exact ledger_goto hl i _ _ ht (by intro x; rw [hc x]; simp [ledgerCredit])
      · exact ledger_goto hl i _ _ ht (by intro x; rw [hc x]; simp [ledgerCredit])

private theorem ledger_close {s : St} (hl : LedgerInv s) (i : Nat) (e : Exc)
    (ht : s.tasks[i]? = some ⟨.close e, .start⟩) :
    LedgerInv (closeBody s i e) := by
  intro x
  have hs := hl x
  change tsum (ledgerCredit x) s.tasks = _ at hs
  have h₁ := lookup_wakeAll_active s.tasks s.ch.qTake i (.err e)
    ⟨.close e, .start⟩ ht (by simp)
  have h₂ := lookup_wakeAll_active (wakeAll s.tasks s.ch.qTake (.err e))
    s.ch.qWait i (.err e) ⟨.close e, .start⟩ h₁ (by simp)
  have h₃ := lookup_wakeAll_active
    (wakeAll (wakeAll s.tasks s.ch.qTake (.err e)) s.ch.qWait (.err e))
    s.ch.qPut i (.err e) ⟨.close e, .start⟩ h₂ (by simp)
  change tsum (ledgerCredit x) (closeBody s i e).tasks = _
  simp only [closeBody, St.finish, St.notifyPutAll, St.notifyWaitAll, St.notifyTakeAll]
  rw [sum_setPc_lookup x _ _ _ _ h₃]
  simpa [ledgerCredit] using hs

private theorem ledger_empty {s : St} (hl : LedgerInv s) (i : Nat)
    (ht : s.tasks[i]? = some ⟨.empty, .start⟩) :
    LedgerInv (emptyBody s i) := by
  intro x
  have hs := hl x
  change tsum (ledgerCredit x) s.tasks = _ at hs
  have hw := lookup_wakeAll_active s.tasks s.ch.qPut i .none
    ⟨.empty, .start⟩ ht (by simp)
  change tsum (ledgerCredit x) (emptyBody s i).tasks = _
  simp only [emptyBody, St.finish, St.notifyPutAll, St.addAvail]
  rw [sum_setPc_lookup x _ _ _ _ hw]
  simp [ledgerCredit, List.count_append, Int.natCast_add]
  omega

private theorem sum_wake_lookup (x : Val) (ts : List Task) (j : Nat) (w : Wake)
    (t : Task) (h : ts[j]? = some t) :
    tsum (ledgerCredit x) (wake ts j w) =
      tsum (ledgerCredit x) ts - ledgerCredit x t + ledgerCredit x (wakeT w t) := by
  have hj : j < ts.length := List.getElem?_eq_some_iff.mp h |>.1
  have ht : ts[j] = t := by simpa [List.getElem?_eq_getElem hj] using h
  simpa [ht] using tsum_wake (ledgerCredit x) ts j w hj

private theorem ledger_handoff {sz : Nat} {s : St} (hl : LedgerInv s)
    (hq : QueueInv sz s) (i v j : Nat)
    (ht : s.tasks[i]? = some ⟨.put v, .handoff v j⟩) :
    LedgerInv ({ s with tasks := wake s.tasks j (.val v) }.finish i (.ok (some v))) := by
  have hp : pcOf s i = some (.handoff v j) := by simp [pcOf, ht]
  obtain ⟨it, hj⟩ := (hq.handoff i v j hp).1
  obtain ⟨t, hjt, hpc⟩ : ∃ t, s.tasks[j]? = some t ∧ t.pc = .parked (.takeUnb it) := by
    unfold pcOf at hj
    cases he : s.tasks[j]? with
    | none => simp [he] at hj
    | some t => exact ⟨t, rfl, by simpa [he] using hj⟩
  have hw := lookup_wake_active s.tasks i j (.val v) ⟨.put v, .handoff v j⟩ ht (by simp)
  intro x
  have hs := hl x
  change tsum (ledgerCredit x) s.tasks = _ at hs
  change tsum (ledgerCredit x) (setPc (wake s.tasks j (.val v)) i (.done (.ok (some v)))) = _
  rw [sum_setPc_lookup x _ _ _ _ hw, sum_wake_lookup x _ _ _ _ hjt]
  rcases t with ⟨op, pc⟩
  simp only at hpc
  subst pc
  simp [ledgerCredit, wakeT, St.finish]
  split <;> simp_all <;> omega

theorem ledgerInv_init (sz : Nat) (ops : List Op) : LedgerInv (init sz ops) := by
  intro x
  simp only [init, List.map_map]
  induction ops with
  | nil => simp
  | cons op ops ih => simpa [ledgerCredit, List.map_cons, List.sum_cons] using ih

theorem ledgerInv_step {sz : Nat} {ops : List Op} {s s' : St} {i : Nat}
    (hl : LedgerInv s) (hf : FitInv sz ops s) (hq : QueueInv sz s)
    (h : stepTask s i = some s') : LedgerInv s' := by
  cases ht : s.tasks[i]? with
  | none => simp [stepTask, ht] at h
  | some t =>
    have hfit := hf.fits t (List.mem_of_getElem? ht)
    rcases t with ⟨op, pc⟩
    cases pc with
    | start =>
      cases op with
      | put v =>
        simp only [stepTask, ht] at h
        split at h <;> cases h <;>
          exact ledger_goto hl i _ _ ht (by intro x; simp [ledgerCredit])
      | take =>
        simp only [stepTask, ht, Option.some.injEq] at h
        subst s'
        exact ledger_take hl i false .take .start ht (by simp)
          (by intro x; simp [ledgerCredit]) (Or.inl rfl)
      | iter =>
        simp only [stepTask, ht] at h
        split at h
        · cases h
          exact ledger_goto hl i _ _ ht (by intro x; simp [ledgerCredit])
        · cases h
          apply ledger_goto hl i _ _ ht
          intro x
          split <;> simp [ledgerCredit]
      | fetch =>
        simp only [stepTask, ht] at h
        split at h
        · cases h
          exact ledger_goto hl i _ _ ht (by intro x; simp [ledgerCredit])
        · cases h
          exact ledger_fetch hl i .start ht (by intro x; simp [ledgerCredit])
      | wait =>
        simp only [stepTask, ht] at h
        split at h <;> cases h <;>
          exact ledger_goto hl i _ _ ht (by intro x; simp [ledgerCredit])
      | close e =>
        simp only [stepTask, ht, Option.some.injEq] at h
        subst s'
        exact ledger_close hl i e ht
      | empty =>
        simp only [stepTask, ht, Option.some.injEq] at h
        subst s'
        exact ledger_empty hl i ht
    | putLocked v =>
      change op = .put v at hfit
      subst op
      simp only [stepTask, ht] at h
      split at h <;> cases h
      · exact ledger_putUnb (ledger_addAvail hl 1) i v (.putLocked v) ht
          (by simp) (by intro x; simp [ledgerCredit])
      · exact ledger_putBuf (ledger_addAvail hl 1) i v (.putLocked v) ht
          (by simp) (by intro x; simp [ledgerCredit])
    | takeLocked it =>
      change op = .iter ∧ it = true at hfit
      rcases hfit with ⟨rfl, rfl⟩
      simp only [stepTask, ht, Option.some.injEq] at h
      subst s'
      exact ledger_take hl i true .iter (.takeLocked true) ht (by simp)
        (by intro x; simp [ledgerCredit]) (Or.inr rfl)
    | waitLocked =>
      change op = .wait at hfit
      subst op
      simp only [stepTask, ht, Option.some.injEq] at h
      subst s'
      exact ledger_wait hl i .waitLocked ht (by intro x; simp [ledgerCredit])
    | parked k => cases op <;> simp [stepTask, ht] at h
    | done r => cases op <;> simp [stepTask, ht] at h
    | handoff v j =>
      change op = .put v ∧ sz = 0 at hfit
      rcases hfit with ⟨rfl, _⟩
      simp only [stepTask, ht, Option.some.injEq] at h
      subst s'
      exact ledger_handoff hl hq i v j ht
    | woken k w =>
      cases k with
      | putBuf v =>
        change op = .put v ∧ 0 < sz at hfit
        rcases hfit with ⟨rfl, _⟩
        cases w with
        | none =>
          simp only [stepTask, ht, Option.some.injEq] at h
          subst s'
          exact ledger_putBuf hl i v _ ht (by simp) (by intro x; simp [ledgerCredit])
        | val a =>
          simp only [stepTask, ht, Option.some.injEq] at h
          subst s'
          exact ledger_putBuf hl i v _ ht (by simp) (by intro x; simp [ledgerCredit])
        | err e =>
          simp only [stepTask, ht, Option.some.injEq] at h
          subst s'
          exact ledger_goto (ledger_addAvail hl (-1)) i _ _ ht
            (by intro x; simp [ledgerCredit])
      | putUnb v =>
        change op = .put v ∧ sz = 0 at hfit
        rcases hfit with ⟨rfl, _⟩
        cases w with
        | none =>
          simp only [stepTask, ht, Option.some.injEq] at h
          subst s'
          exact ledger_putUnb hl i v _ ht (by simp) (by intro x; simp [ledgerCredit])
        | val a =>
          simp only [stepTask, ht, Option.some.injEq] at h
          subst s'
          exact ledger_putUnb hl i v _ ht (by simp) (by intro x; simp [ledgerCredit])
        | err e =>
          simp only [stepTask, ht, Option.some.injEq] at h
          subst s'
          exact ledger_goto (ledger_addAvail hl (-1)) i _ _ ht
            (by intro x; simp [ledgerCredit])
      | take it =>
        cases it <;> simp only [PcFits, ParkFits] at hfit <;>
          rcases hfit with ⟨rfl, _⟩ <;> cases w <;>
          simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals first
          | exact ledger_takeBuf hl i _ _ _ ht (by simp)
              (by intro x; simp [ledgerCredit]) (by simp)
          | exact ledger_goto hl i _ _ ht
              (by intro x
                  rw [credit_finishTake_err x _ _ _ (by simp)]
                  simp [ledgerCredit])
      | takeUnb it =>
        cases it <;> simp only [PcFits, ParkFits] at hfit <;>
          rcases hfit with ⟨rfl, _⟩ <;> cases w <;>
          simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals
          apply ledger_goto hl i _ _ ht
          intro x
          first
          | exact (credit_finishTake_err x _ _ _ (by simp)).trans (by simp [ledgerCredit])
          | simp [ledgerCredit]
      | fetch =>
        change op = .fetch ∧ 0 < sz at hfit
        rcases hfit with ⟨rfl, _⟩
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals first
          | exact ledger_fetch hl i _ ht (by intro x; simp [ledgerCredit])
          | exact ledger_goto hl i _ _ ht (by intro x; simp [ledgerCredit])
      | wait =>
        change op = .wait at hfit
        subst op
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals first
          | exact ledger_wait hl i _ ht (by intro x; simp [ledgerCredit])
          | exact ledger_goto hl i _ _ ht (by intro x; simp [ledgerCredit])

private theorem credit_counts (x : Val) (t : Task) :
    ledgerCredit x t =
      ((match t.op, t.pc with
        | .put v, .done (.ok _) => [v]
        | _, _ => []).count x : Int) -
      ((match t.op, t.pc with
        | .take, .done (.ok (some v)) | .iter, .done (.ok (some v)) => [v]
        | _, .woken (.takeUnb _) (.val v) => [v]
        | _, _ => []).count x : Int) := by
  unfold ledgerCredit
  split <;> split <;> simp_all [List.count_singleton] <;>
    split <;> simp_all

private theorem tsum_sub (f g : Task → Int) (ts : List Task) :
    tsum (fun t => f t - g t) ts = tsum f ts - tsum g ts := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [tsum_cons, ih]; omega

theorem ledgerInv_conservation {s : St} (hl : LedgerInv s) :
    List.Perm (putsDone s) (received s ++ s.ch.data ++ s.dropped) := by
  apply List.perm_iff_count.mpr
  intro x
  have hs := hl x
  have hc : tsum (ledgerCredit x) s.tasks =
      ((putsDone s).count x : Int) - ((received s).count x : Int) := by
    simp only [putsDone, received, count_flatMap_tsum]
    rw [← tsum_sub]
    congr 1
    funext t
    exact credit_counts x t
  change tsum (ledgerCredit x) s.tasks = _ at hs
  rw [hc] at hs
  simp only [List.count_append]
  omega

end JuliaLean.Channels
