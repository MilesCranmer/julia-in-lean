import JuliaLean.Channels.ProofsDefs
import JuliaLean.Channels.ProofsLemmas

namespace JuliaLean.Channels

private theorem pcOf_init (sz : Nat) (ops : List Op) (i : Nat) :
    pcOf (init sz ops) i = (ops[i]?).map (fun _ => Pc.start) := by
  simp [pcOf, init, List.getElem?_map, Option.map_map, Function.comp_def]

theorem queueInv_init (sz : Nat) (ops : List Op) : QueueInv sz (init sz ops) := by
  have hp : ∀ i pc, pcOf (init sz ops) i = some pc → pc = .start := by
    intro i pc h
    rw [pcOf_init] at h
    cases hi : ops[i]? <;> simp_all
  constructor
  · simp [init]
  · simp [init, pendingPut, Function.comp_def]
  · simp [init]
  · simp [init]
  · simp [init]
  · simp [init]
  · simp [init]
  · simp [init]
  · simp [init]
  · intro i v t h; have := hp i _ h; contradiction
  · intro i k h; have := hp i _ h; contradiction
  · simp [init]
  · simp [init]
  · simp [init]
  · simp [init]
  · intro i k w h; have := hp i _ h; contradiction
  · intro i k e h; have := hp i _ h; contradiction
  · intro i it e h; have := hp i _ h; contradiction

private theorem pcOf_set (s : St) (i : Nat) (pc : Pc) (j : Nat) :
    pcOf {s with tasks := setPc s.tasks i pc} j =
      if j = i then (pcOf s j).map (fun _ => pc) else pcOf s j := by
  simp only [pcOf, setPc_getElem?]
  split <;> simp_all [Option.map_map, Function.comp_def]

private def wakePc (w : Wake) : Pc → Pc
  | .parked k => .woken k w
  | pc => pc

private theorem pcOf_wake (s : St) (i : Nat) (w : Wake) (j : Nat) :
    pcOf {s with tasks := wake s.tasks i w} j =
      if j = i then (pcOf s j).map (wakePc w) else pcOf s j := by
  simp only [pcOf, wake_getElem?]
  split <;> simp_all [Option.map_map, Function.comp_def]
  congr 1
  funext t
  cases t with
  | mk op pc => cases pc <;> rfl

private theorem pcOf_wakeAll (s : St) (q : List Nat) (w : Wake) (j : Nat) :
    pcOf {s with tasks := wakeAll s.tasks q w} j =
      if j ∈ q then (pcOf s j).map (wakePc w) else pcOf s j := by
  simp only [pcOf, wakeAll_getElem?]
  split <;> simp_all [Option.map_map, Function.comp_def]
  congr 1
  funext t
  cases t with
  | mk op pc => cases pc <;> rfl

private theorem takeKind_parked {sz : Nat} {pc : Pc} (h : TakeQueueKind sz pc) :
    ∃ k, pc = .parked k := by
  unfold TakeQueueKind at h
  split at h
  · obtain ⟨it, rfl⟩ := h; exact ⟨_, rfl⟩
  · rcases h with ⟨it, rfl⟩ | rfl | rfl <;> exact ⟨_, rfl⟩

private theorem putKind_parked {sz : Nat} {pc : Pc} (h : PutQueueKind sz pc) :
    ∃ k, pc = .parked k := by
  unfold PutQueueKind at h
  split at h <;> obtain ⟨v, rfl⟩ := h <;> exact ⟨_, rfl⟩

private theorem runnable_not_queued {sz : Nat} {s : St} {i : Nat} {pc : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some pc)
    (hr : ∀ k, pc ≠ .parked k) :
    i ∉ s.ch.qTake ∧ i ∉ s.ch.qPut ∧ i ∉ s.ch.qWait := by
  constructor
  · intro h
    obtain ⟨pc', hp, hk⟩ := hq.takeKinds i h
    obtain ⟨k, rfl⟩ := takeKind_parked hk
    exact hr k (Option.some.inj (hi.symm.trans hp))
  constructor
  · intro h
    obtain ⟨pc', hp, hk⟩ := hq.putKinds i h
    obtain ⟨k, rfl⟩ := putKind_parked hk
    exact hr k (Option.some.inj (hi.symm.trans hp))
  · intro h
    exact hr .wait (Option.some.inj (hi.symm.trans (hq.waitKinds i h).2))


private theorem queueInv_retask {sz : Nat} {s : St} {i : Nat} {old pc : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old)
    (hr : ∀ k, old ≠ .parked k)
    (hh : ∀ v t, old ≠ .handoff v t)
    (hp : ∀ k, pc ≠ .parked k)
    (hw : ∀ k w, pc ≠ .woken k w)
    (hh' : ∀ v t, pc ≠ .handoff v t)
    (data : List Val) (d : Int)
    (ha : s.ch.nAvail + d = (data.length : Int) +
      ((setPc s.tasks i pc).countP pendingPut : Int))
    (hbound : data.length ≤ sz)
    (ht : 0 < sz → s.ch.qTake ≠ [] → data = [])
    (hb : 0 < sz → s.ch.qPut ≠ [] →
      sz ≤ data.length + wokenPutBuf ((s.addAvail d).goto i pc))
    (hu : sz = 0 → s.ch.qPut ≠ [] →
      s.ch.qTake.length ≤ wokenPutUnb ((s.addAvail d).goto i pc))
    (hwait : sz = 0 → s.ch.qWait ≠ [] → s.ch.nAvail + d = 0)
    (herr : ∀ j it e, pcOf s j = some (.woken (.take it) (.err e)) → data = []) :
    QueueInv sz (({s with ch := {s.ch with data := data}}.addAvail d).goto i pc) := by
  have hn := runnable_not_queued hq hi hr
  have he : ∀ j, pcOf (({s with ch := {s.ch with data := data}}.addAvail d).goto i pc) j =
      if j = i then some pc else pcOf s j := by
    intro j
    change pcOf {s with tasks := setPc s.tasks i pc} j = _
    rw [pcOf_set]
    by_cases hj : j = i <;> simp [hj, hi]
  have heq : ∀ j p, pcOf (({s with ch := {s.ch with data := data}}.addAvail d).goto i pc) j = some p →
      p = pc ∧ j = i ∨ pcOf s j = some p ∧ j ≠ i := by
    intro j p h
    rw [he] at h
    split at h <;> simp_all
  constructor
  · exact hq.closedQueues
  · exact ha
  · exact hbound
  · intro j hj
    obtain ⟨p, he', hk⟩ := hq.takeKinds j hj
    refine ⟨p, ?_, hk⟩
    rw [he, ite_eq_right]
    · exact he'
    · intro hj'; subst j; exact hn.1 hj
  · intro j hj
    obtain ⟨p, he', hk⟩ := hq.putKinds j hj
    refine ⟨p, ?_, hk⟩
    rw [he, ite_eq_right]
    · exact he'
    · intro hj'; subst j; exact hn.2.1 hj
  · intro j hj
    obtain ⟨hz, he'⟩ := hq.waitKinds j hj
    refine ⟨hz, ?_⟩
    rw [he, ite_eq_right]
    · exact he'
    · intro hj'; subst j; exact hn.2.2 hj
  · exact hq.takeNodup
  · exact hq.putNodup
  · exact hq.waitNodup
  · intro j v t h
    obtain (⟨hc, _⟩ | ⟨hold, hji⟩) := heq j _ h
    · exact False.elim (hh' v t hc.symm)
    obtain ⟨⟨it, ht⟩, hqt, hqp, hqw, huniq⟩ := hq.handoff j v t hold
    have hti : t ≠ i := by
      intro hti; subst t
      exact hr (.takeUnb it) (Option.some.inj (hi.symm.trans ht))
    refine ⟨⟨it, ?_⟩, hqt, hqp, hqw, ?_⟩
    · simpa [he, hti] using ht
    · intro l v' hl
      obtain (⟨hc, _⟩ | ⟨hold', _⟩) := heq l _ hl
      · exact False.elim (hh' v' t hc.symm)
      · exact huniq l v' hold'
  · intro j k hj
    obtain (⟨hc, _⟩ | ⟨hold, _⟩) := heq j _ hj
    · exact False.elim (hp k hc.symm)
    rcases hq.parkedCovered j k hold with h | h | h | ⟨l, v, hl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ⟨l, v, ?_⟩))
      have hli : l ≠ i := by
        intro hli; subst l
        exact hh v j (Option.some.inj (hi.symm.trans hl))
      simpa [he, hli] using hl
  · exact ht
  · exact hb
  · exact hu
  · exact hwait
  · intro j k w hj
    obtain (⟨hc, _⟩ | ⟨hold, _⟩) := heq j _ hj
    · exact False.elim (hw k w hc.symm)
    · exact hq.wakeValues j k w hold
  · intro j k e hj
    obtain (⟨hc, _⟩ | ⟨hold, _⟩) := heq j _ hj
    · exact False.elim (hw k (.err e) hc.symm)
    · exact hq.wakeError j k e hold
  · intro j it e hj
    obtain (⟨hc, _⟩ | ⟨hold, _⟩) := heq j _ hj
    · exact False.elim (hw (.take it) (.err e) hc.symm)
    · exact herr j it e hold

private theorem countPc_set {s : St} {i : Nat} {old : Pc}
    (p : Pc → Bool) (hi : pcOf s i = some old) (pc : Pc) :
    (setPc s.tasks i pc).countP (fun t => p t.pc) + (if p old then 1 else 0) =
      s.tasks.countP (fun t => p t.pc) + (if p pc then 1 else 0) := by
  cases ht : s.tasks[i]? with
  | none => simp [pcOf, ht] at hi
  | some t =>
    have hp : t.pc = old := by simpa [pcOf, ht] using hi
    simpa [hp] using countP_setPc (fun t => p t.pc) s.tasks i pc t ht

private def ordinaryPc : Pc → Prop
  | .start | .putLocked _ | .takeLocked _ | .waitLocked | .done _ => True
  | _ => False

private def passivePc : Pc → Prop
  | .woken (.take _) _ | .woken (.takeUnb _) _ | .woken .fetch _ | .woken .wait _ => True
  | pc => ordinaryPc pc

private def pendingPc (pc : Pc) : Bool := pendingPut {op := .wait, pc := pc}
private def bufPc : Pc → Bool
  | .woken (.putBuf _) _ => true
  | _ => false
private def unbPc : Pc → Bool
  | .woken (.putUnb _) _ => true
  | _ => false

@[simp] private theorem pending_count (ts : List Task) :
    ts.countP pendingPut = ts.countP (fun t => pendingPc t.pc) := rfl

@[simp] private theorem wokenBuf_count (s : St) :
    wokenPutBuf s = s.tasks.countP (fun t => bufPc t.pc) := by
  unfold wokenPutBuf
  apply congrArg (fun p : Task → Bool => s.tasks.countP p)
  funext t
  cases t with
  | mk op pc =>
    cases pc with
    | woken k w => cases k <;> rfl
    | _ => rfl

@[simp] private theorem wokenUnb_count (s : St) :
    wokenPutUnb s = s.tasks.countP (fun t => unbPc t.pc) := by
  unfold wokenPutUnb
  apply congrArg (fun p : Task → Bool => s.tasks.countP p)
  funext t
  cases t with
  | mk op pc =>
    cases pc with
    | woken k w => cases k <;> rfl
    | _ => rfl

private theorem passive_metrics {pc : Pc} (h : passivePc pc) :
    pendingPc pc = false ∧ bufPc pc = false ∧ unbPc pc = false := by
  cases pc with
  | woken k w => cases k <;> simp_all [passivePc, ordinaryPc, pendingPc, pendingPut, bufPc, unbPc]
  | _ => simp_all [passivePc, ordinaryPc, pendingPc, pendingPut, bufPc, unbPc]

private theorem ordinary_passive {pc : Pc} (h : ordinaryPc pc) : passivePc pc := by
  cases pc <;> simp_all [ordinaryPc, passivePc]

private theorem queueInv_neutral {sz : Nat} {s : St} {i : Nat} {old pc : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old)
    (ho : passivePc old) (hn : ordinaryPc pc) :
    QueueInv sz (s.goto i pc) := by
  have hr : ∀ k, old ≠ .parked k := by cases old <;> simp_all [passivePc, ordinaryPc]
  have hh : ∀ v t, old ≠ .handoff v t := by cases old <;> simp_all [passivePc, ordinaryPc]
  have hp : ∀ k, pc ≠ .parked k := by cases pc <;> simp_all [ordinaryPc]
  have hw : ∀ k w, pc ≠ .woken k w := by cases pc <;> simp_all [ordinaryPc]
  have hh' : ∀ v t, pc ≠ .handoff v t := by cases pc <;> simp_all [ordinaryPc]
  have hmo := passive_metrics ho
  have hmn := passive_metrics (ordinary_passive hn)
  have hc : (setPc s.tasks i pc).countP pendingPut = s.tasks.countP pendingPut := by
    have h := countPc_set pendingPc hi pc
    simp only [hmo.1, hmn.1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
    exact h
  have hb : wokenPutBuf (s.goto i pc) = wokenPutBuf s := by
    have h := countPc_set bufPc hi pc
    simp only [hmo.2.1, hmn.2.1, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
    exact h
  have hu : wokenPutUnb (s.goto i pc) = wokenPutUnb s := by
    have h := countPc_set unbPc hi pc
    simp only [hmo.2.2, hmn.2.2, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
    exact h
  simpa [St.addAvail] using queueInv_retask hq hi hr hh hp hw hh' s.ch.data 0
    (by simpa [hc] using hq.availability)
    hq.buffer hq.bufferedTake
    (by
      intro hz hqp
      change sz ≤ s.ch.data.length + wokenPutBuf (s.goto i pc)
      rw [hb]
      exact hq.bufferedPut hz hqp)
    (by
      intro hz hqp
      change s.ch.qTake.length ≤ wokenPutUnb (s.goto i pc)
      rw [hu]
      exact hq.unbufferedPut hz hqp)
    (by simpa using hq.unbufferedWait) hq.takeErrorEmpty


private inductive QueueSide where
  | take | put | wait
  deriving DecidableEq

private def parkOn (s : St) (i : Nat) (k : Park) : QueueSide → St
  | .take => s.parkTake i k
  | .put => s.parkPut i k
  | .wait => s.parkWait i k

private theorem queueInv_park {sz : Nat} {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old)
    (hr : ∀ k, old ≠ .parked k) (hh : ∀ v t, old ≠ .handoff v t)
    (q : QueueSide) (k : Park) (d : Int) (hopen : s.ch.isOpen = true)
    (hkT : q = .take → TakeQueueKind sz (.parked k))
    (hkP : q = .put → PutQueueKind sz (.parked k))
    (hkW : q = .wait → sz = 0 ∧ k = .wait)
    (ha : s.ch.nAvail + d = (s.ch.data.length : Int) +
      ((setPc s.tasks i (.parked k)).countP pendingPut : Int))
    (ht : 0 < sz → (parkOn (s.addAvail d) i k q).ch.qTake ≠ [] → s.ch.data = [])
    (hb : 0 < sz → (parkOn (s.addAvail d) i k q).ch.qPut ≠ [] →
      sz ≤ s.ch.data.length + wokenPutBuf (parkOn (s.addAvail d) i k q))
    (hu : sz = 0 → (parkOn (s.addAvail d) i k q).ch.qPut ≠ [] →
      (parkOn (s.addAvail d) i k q).ch.qTake.length ≤ wokenPutUnb (parkOn (s.addAvail d) i k q))
    (hw : sz = 0 → (parkOn (s.addAvail d) i k q).ch.qWait ≠ [] → s.ch.nAvail + d = 0) :
    QueueInv sz (parkOn (s.addAvail d) i k q) := by
  let s' := parkOn (s.addAvail d) i k q
  have hn := runnable_not_queued hq hi hr
  have hT : ∀ j, j ∈ s'.ch.qTake ↔ j ∈ s.ch.qTake ∨ j = i ∧ q = .take := by
    intro j; cases q <;> simp [s', parkOn, St.addAvail, St.parkTake, St.parkPut, St.parkWait]
  have hP : ∀ j, j ∈ s'.ch.qPut ↔ j ∈ s.ch.qPut ∨ j = i ∧ q = .put := by
    intro j; cases q <;> simp [s', parkOn, St.addAvail, St.parkTake, St.parkPut, St.parkWait]
  have hW : ∀ j, j ∈ s'.ch.qWait ↔ j ∈ s.ch.qWait ∨ j = i ∧ q = .wait := by
    intro j; cases q <;> simp [s', parkOn, St.addAvail, St.parkTake, St.parkPut, St.parkWait]
  have he : ∀ j, pcOf s' j = if j = i then some (.parked k) else pcOf s j := by
    intro j
    have he' : pcOf s' j = pcOf {s with tasks := setPc s.tasks i (.parked k)} j := by
      cases q <;> rfl
    rw [he', pcOf_set]
    by_cases hj : j = i <;> simp [hj, hi]
  have heq : ∀ j p, pcOf s' j = some p →
      p = .parked k ∧ j = i ∨ pcOf s j = some p ∧ j ≠ i := by
    intro j p h; rw [he] at h; split at h <;> simp_all
  have hdata : s'.ch.data = s.ch.data := by cases q <;> rfl
  have havail : s'.ch.nAvail = s.ch.nAvail + d := by cases q <;> rfl
  change QueueInv sz s'
  constructor
  · intro hc; cases q <;> simp [s', parkOn, St.addAvail, St.parkTake, St.parkPut, St.parkWait, hopen] at hc
  · cases q <;> exact ha
  · cases q <;> exact hq.buffer
  · intro j hj
    rcases (hT j).mp hj with hj | ⟨rfl, hq'⟩
    · obtain ⟨p, hp, hk⟩ := hq.takeKinds j hj
      have hji : j ≠ i := by intro hji; subst j; exact hn.1 hj
      exact ⟨p, by simpa [he, hji] using hp, hk⟩
    · exact ⟨_, by simp [he], hkT hq'⟩
  · intro j hj
    rcases (hP j).mp hj with hj | ⟨rfl, hq'⟩
    · obtain ⟨p, hp, hk⟩ := hq.putKinds j hj
      have hji : j ≠ i := by intro hji; subst j; exact hn.2.1 hj
      exact ⟨p, by simpa [he, hji] using hp, hk⟩
    · exact ⟨_, by simp [he], hkP hq'⟩
  · intro j hj
    rcases (hW j).mp hj with hj | ⟨rfl, hq'⟩
    · obtain ⟨hz, hp⟩ := hq.waitKinds j hj
      have hji : j ≠ i := by intro hji; subst j; exact hn.2.2 hj
      exact ⟨hz, by simpa [he, hji] using hp⟩
    · obtain ⟨hz, rfl⟩ := hkW hq'; exact ⟨hz, by simp [he]⟩
  · cases q <;> simp [s', parkOn, St.addAvail, St.parkTake, St.parkPut, St.parkWait,
      List.nodup_append, hq.takeNodup]
    intro a ha he; subst a; exact hn.1 ha
  · cases q <;> simp [s', parkOn, St.addAvail, St.parkTake, St.parkPut, St.parkWait,
      List.nodup_append, hq.putNodup]
    intro a ha he; subst a; exact hn.2.1 ha
  · cases q <;> simp [s', parkOn, St.addAvail, St.parkTake, St.parkPut, St.parkWait,
      List.nodup_append, hq.waitNodup]
    intro a ha he; subst a; exact hn.2.2 ha
  · intro j v t hj
    obtain (⟨hc, _⟩ | ⟨hold, hji⟩) := heq j _ hj
    · contradiction
    obtain ⟨⟨it, ht'⟩, hqt, hqp, hqw, huniq⟩ := hq.handoff j v t hold
    have hti : t ≠ i := by
      intro hti; subst t; exact hr (.takeUnb it) (Option.some.inj (hi.symm.trans ht'))
    refine ⟨⟨it, by simpa [he, hti] using ht'⟩, ?_, ?_, ?_, ?_⟩
    · simpa [hT, hti] using hqt
    · simpa [hP, hti] using hqp
    · simpa [hW, hti] using hqw
    · intro l v' hl
      obtain (⟨hc, _⟩ | ⟨hold', _⟩) := heq l _ hl
      · contradiction
      · exact huniq l v' hold'
  · intro j k' hj
    obtain (⟨hc, hji⟩ | ⟨hold, _⟩) := heq j _ hj
    · subst j
      cases q with
      | take => exact Or.inl ((hT i).mpr (Or.inr ⟨rfl, rfl⟩))
      | put => exact Or.inr (Or.inl ((hP i).mpr (Or.inr ⟨rfl, rfl⟩)))
      | wait => exact Or.inr (Or.inr (Or.inl ((hW i).mpr (Or.inr ⟨rfl, rfl⟩))))
    rcases hq.parkedCovered j k' hold with h | h | h | ⟨l, v, hl⟩
    · exact Or.inl ((hT j).mpr (Or.inl h))
    · exact Or.inr (Or.inl ((hP j).mpr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl ((hW j).mpr (Or.inl h))))
    · have hli : l ≠ i := by intro hli; subst l; exact hh v j (Option.some.inj (hi.symm.trans hl))
      exact Or.inr (Or.inr (Or.inr ⟨l, v, by simpa [he, hli] using hl⟩))
  · simpa only [hdata] using ht
  · simpa only [hdata] using hb
  · exact hu
  · simpa only [havail] using hw
  · intro j k' w hj
    obtain (⟨hc, _⟩ | ⟨hold, _⟩) := heq j _ hj
    · contradiction
    · exact hq.wakeValues j k' w hold
  · intro j k' e hj
    obtain (⟨hc, _⟩ | ⟨hold, _⟩) := heq j _ hj
    · contradiction
    · cases q <;> exact hq.wakeError j k' e hold
  · intro j it e hj
    obtain (⟨hc, _⟩ | ⟨hold, _⟩) := heq j _ hj
    · contradiction
    · cases q <;> exact hq.takeErrorEmpty j it e hold

private theorem queueKinds_exclusive {sz : Nat} {pc : Pc}
    (ht : TakeQueueKind sz pc) (hp : PutQueueKind sz pc) : False := by
  by_cases hz : sz = 0
  · simp only [TakeQueueKind, PutQueueKind, hz, ↓reduceIte] at ht hp
    obtain ⟨it, ht⟩ := ht
    obtain ⟨v, hp⟩ := hp
    cases ht.symm.trans hp
  · simp only [TakeQueueKind, PutQueueKind, hz, ↓reduceIte] at ht hp
    obtain ⟨v, rfl⟩ := hp
    simp at ht

private theorem queues_exclusive {sz : Nat} {s : St} (hq : QueueInv sz s) :
    (∀ j, j ∈ s.ch.qTake → j ∉ s.ch.qPut) ∧
    (∀ j, j ∈ s.ch.qTake → j ∉ s.ch.qWait) ∧
    (∀ j, j ∈ s.ch.qPut → j ∉ s.ch.qWait) := by
  constructor
  · intro j ht hp
    obtain ⟨pc, he, hk⟩ := hq.takeKinds j ht
    obtain ⟨pc', he', hk'⟩ := hq.putKinds j hp
    have hpc : pc' = pc := Option.some.inj (he'.symm.trans he)
    subst pc'
    exact queueKinds_exclusive hk hk'
  constructor
  · intro j ht hw
    obtain ⟨pc, he, hk⟩ := hq.takeKinds j ht
    obtain ⟨hz, he'⟩ := hq.waitKinds j hw
    have hpc : pc = .parked .wait := Option.some.inj (he.symm.trans he')
    simp [hpc, TakeQueueKind, hz] at hk
  · intro j hp hw
    obtain ⟨pc, he, hk⟩ := hq.putKinds j hp
    obtain ⟨hz, he'⟩ := hq.waitKinds j hw
    have hpc : pc = .parked .wait := Option.some.inj (he.symm.trans he')
    simp [hpc, PutQueueKind, hz] at hk

private def selectedQueue (s : St) : QueueSide → List Nat
  | .take => s.ch.qTake
  | .put => s.ch.qPut
  | .wait => s.ch.qWait

private def notifyOn (s : St) : QueueSide → St
  | .take => s.notifyTakeAll .none
  | .put => s.notifyPutAll .none
  | .wait => s.notifyWaitAll .none

private theorem pending_wake (w : Wake) (t : Task) : pendingPut (wakeT w t) = pendingPut t := by
  cases t with
  | mk op pc =>
    cases pc <;> try rfl
    case parked k => cases k <;> rfl

private theorem queue_none_fits {sz : Nat} {s : St} (hq : QueueInv sz s)
    (q : QueueSide) (hvalid : q = .take → 0 < sz) :
    ∀ j k, j ∈ selectedQueue s q → pcOf s j = some (.parked k) → WakeFits k .none := by
  intro j k hj he
  cases q with
  | take =>
    obtain ⟨pc, hp', hk⟩ := hq.takeKinds j hj
    have heq : pc = .parked k := Option.some.inj (hp'.symm.trans he)
    have hz : sz ≠ 0 := Nat.ne_of_gt (hvalid rfl)
    rw [heq] at hk
    cases k <;> simp_all [TakeQueueKind, WakeFits]
  | put =>
    obtain ⟨pc, hp', hk⟩ := hq.putKinds j hj
    have heq : pc = .parked k := Option.some.inj (hp'.symm.trans he)
    rw [heq] at hk
    by_cases hz : sz = 0 <;> cases k <;> simp_all [PutQueueKind, WakeFits]
  | wait =>
    have heq : k = .wait := Pc.parked.inj (Option.some.inj (he.symm.trans (hq.waitKinds j hj).2))
    subst k; trivial

private theorem nil_of_subset {l old : List Nat}
    (h : ∀ j, j ∈ l → j ∈ old) (he : old = []) : l = [] := by
  cases l with
  | nil => rfl
  | cons j l => have := h j (by simp); simp [he] at this

private theorem queueInv_wakeQueues {sz : Nat} {s : St} (hq : QueueInv sz s)
    (selected qt qp qw : List Nat)
    (hT : ∀ j, j ∈ qt ↔ j ∈ s.ch.qTake ∧ j ∉ selected)
    (hP : ∀ j, j ∈ qp ↔ j ∈ s.ch.qPut ∧ j ∉ selected)
    (hW : ∀ j, j ∈ qw ↔ j ∈ s.ch.qWait ∧ j ∉ selected)
    (hnT : qt.Nodup) (hnP : qp.Nodup) (hnW : qw.Nodup)
    (hlen : qt.length ≤ s.ch.qTake.length)
    (hfits : ∀ j k, j ∈ selected → pcOf s j = some (.parked k) → WakeFits k .none) :
    QueueInv sz {s with
      ch := {s.ch with qTake := qt, qPut := qp, qWait := qw}
      tasks := wakeAll s.tasks selected .none} := by
  let s' : St := {s with
    ch := {s.ch with qTake := qt, qPut := qp, qWait := qw}
    tasks := wakeAll s.tasks selected .none}
  change QueueInv sz s'
  have hp : ∀ j k, pcOf s' j = some (.parked k) ↔
      j ∉ selected ∧ pcOf s j = some (.parked k) := by
    intro j k; exact wakeAll_pc_parked _ _ _ _ _
  have hh : ∀ j v t, pcOf s' j = some (.handoff v t) ↔ pcOf s j = some (.handoff v t) := by
    intro j v t; exact wakeAll_pc_handoff _ _ _ _ _ _
  have hw : ∀ j k w, pcOf s' j = some (.woken k w) ↔
      pcOf s j = some (.woken k w) ∨
        (j ∈ selected ∧ pcOf s j = some (.parked k) ∧ w = .none) := by
    intro j k w; exact wakeAll_pc_woken _ _ _ _ _ _
  have hc : s'.tasks.countP pendingPut = s.tasks.countP pendingPut :=
    countP_wakeAll_of_inv _ _ _ _ (pending_wake _)
  have hb : wokenPutBuf s ≤ wokenPutBuf s' := by
    apply countP_wakeAll_mono (fun t => bufPc t.pc)
    intro t ht; cases t with | mk op pc => cases pc <;> simp_all [wakeT, bufPc]
  have hu : wokenPutUnb s ≤ wokenPutUnb s' := by
    apply countP_wakeAll_mono (fun t => unbPc t.pc)
    intro t ht; cases t with | mk op pc => cases pc <;> simp_all [wakeT, unbPc]
  constructor
  · intro hc'
    obtain ⟨ht, hp', hw'⟩ := hq.closedQueues hc'
    exact ⟨nil_of_subset (fun j hj => ((hT j).mp hj).1) ht,
      nil_of_subset (fun j hj => ((hP j).mp hj).1) hp',
      nil_of_subset (fun j hj => ((hW j).mp hj).1) hw'⟩
  · change s.ch.nAvail = _ + _
    rw [hc]; exact hq.availability
  · exact hq.buffer
  · intro j hj
    obtain ⟨pc, he, hk⟩ := hq.takeKinds j ((hT j).mp hj).1
    obtain ⟨k, rfl⟩ := takeKind_parked hk
    exact ⟨_, (hp j k).mpr ⟨((hT j).mp hj).2, he⟩, hk⟩
  · intro j hj
    obtain ⟨pc, he, hk⟩ := hq.putKinds j ((hP j).mp hj).1
    obtain ⟨k, rfl⟩ := putKind_parked hk
    exact ⟨_, (hp j k).mpr ⟨((hP j).mp hj).2, he⟩, hk⟩
  · intro j hj
    obtain ⟨hz, he⟩ := hq.waitKinds j ((hW j).mp hj).1
    exact ⟨hz, (hp j .wait).mpr ⟨((hW j).mp hj).2, he⟩⟩
  · exact hnT
  · exact hnP
  · exact hnW
  · intro j v t hj
    obtain ⟨⟨it, ht⟩, hqt, hqp, hqw, huniq⟩ := hq.handoff j v t ((hh j v t).mp hj)
    have hsel : t ∉ selected := by intro h; have := hfits t (.takeUnb it) h ht; cases this
    refine ⟨⟨it, (hp t _).mpr ⟨hsel, ht⟩⟩, ?_, ?_, ?_, ?_⟩
    · intro h; exact hqt ((hT t).mp h).1
    · intro h; exact hqp ((hP t).mp h).1
    · intro h; exact hqw ((hW t).mp h).1
    · intro l v' hl; exact huniq l v' ((hh l v' t).mp hl)
  · intro j k hj
    obtain ⟨hn, hold⟩ := (hp j k).mp hj
    rcases hq.parkedCovered j k hold with h | h | h | ⟨l, v, hl⟩
    · exact Or.inl ((hT j).mpr ⟨h, hn⟩)
    · exact Or.inr (Or.inl ((hP j).mpr ⟨h, hn⟩))
    · exact Or.inr (Or.inr (Or.inl ((hW j).mpr ⟨h, hn⟩)))
    · exact Or.inr (Or.inr (Or.inr ⟨l, v, (hh l v j).mpr hl⟩))
  · intro hz hqt
    exact hq.bufferedTake hz (fun he => hqt (nil_of_subset (fun j hj => ((hT j).mp hj).1) he))
  · intro hz hqp
    have hold := hq.bufferedPut hz (fun he => hqp (nil_of_subset (fun j hj => ((hP j).mp hj).1) he))
    change sz ≤ s.ch.data.length + wokenPutBuf s'
    omega
  · intro hz hqp
    have hold := hq.unbufferedPut hz (fun he => hqp (nil_of_subset (fun j hj => ((hP j).mp hj).1) he))
    change qt.length ≤ wokenPutUnb s'
    omega
  · intro hz hqw
    exact hq.unbufferedWait hz (fun he => hqw (nil_of_subset (fun j hj => ((hW j).mp hj).1) he))
  · intro j k w hj
    rcases (hw j k w).mp hj with hold | ⟨hm, hold, rfl⟩
    · exact hq.wakeValues j k w hold
    · exact hfits j k hm hold
  · intro j k e hj
    have hold : pcOf s j = some (.woken k (.err e)) := by simpa using (hw j k (.err e)).mp hj
    exact hq.wakeError j k e hold
  · intro j it e hj
    have hold : pcOf s j = some (.woken (.take it) (.err e)) := by simpa using (hw j (.take it) (.err e)).mp hj
    exact hq.takeErrorEmpty j it e hold

private theorem queueInv_notify {sz : Nat} {s : St} (hq : QueueInv sz s)
    (q : QueueSide) (hvalid : q = .take → 0 < sz) :
    QueueInv sz (notifyOn s q) := by
  have hx := queues_exclusive hq
  cases q with
  | take =>
    exact queueInv_wakeQueues hq s.ch.qTake [] s.ch.qPut s.ch.qWait
      (by simp)
      (by
        intro j; constructor
        · intro hj; exact ⟨hj, fun ht => hx.1 j ht hj⟩
        · exact And.left)
      (by
        intro j; constructor
        · intro hj; exact ⟨hj, fun ht => hx.2.1 j ht hj⟩
        · exact And.left)
      (by simp) hq.putNodup hq.waitNodup (by simp)
      (queue_none_fits hq .take hvalid)
  | put =>
    exact queueInv_wakeQueues hq s.ch.qPut s.ch.qTake [] s.ch.qWait
      (by
        intro j; constructor
        · intro hj; exact ⟨hj, hx.1 j hj⟩
        · exact And.left)
      (by simp)
      (by
        intro j; constructor
        · intro hj; exact ⟨hj, fun hp => hx.2.2 j hp hj⟩
        · exact And.left)
      hq.takeNodup (by simp) hq.waitNodup (by simp)
      (queue_none_fits hq .put (by simp))
  | wait =>
    exact queueInv_wakeQueues hq s.ch.qWait s.ch.qTake s.ch.qPut []
      (by
        intro j; constructor
        · intro hj; exact ⟨hj, hx.2.1 j hj⟩
        · exact And.left)
      (by
        intro j; constructor
        · intro hj; exact ⟨hj, hx.2.2 j hj⟩
        · exact And.left)
      (by simp)
      hq.takeNodup hq.putNodup (by simp) (by simp)
      (queue_none_fits hq .wait (by simp))

private theorem queueInv_notifyOne {sz : Nat} {s : St} (hq : QueueInv sz s) :
    QueueInv sz s.notifyPutOne := by
  cases hqp : s.ch.qPut with
  | nil => simpa [St.notifyPutOne, hqp] using hq
  | cons j js =>
    have hx := queues_exclusive hq
    have hn : j ∉ js ∧ js.Nodup := by simpa [hqp] using hq.putNodup
    have hj : j ∈ s.ch.qPut := by simp [hqp]
    have hh := queueInv_wakeQueues hq [j] s.ch.qTake js s.ch.qWait
      (by
        intro k; constructor
        · intro hk
          refine ⟨hk, ?_⟩
          simp only [List.mem_singleton]
          intro he; subst k; exact hx.1 j hk hj
        · exact And.left)
      (by
        intro k
        simp only [hqp, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · intro hk; exact ⟨Or.inr hk, fun he => hn.1 (he ▸ hk)⟩
        · rintro ⟨(rfl | hk), hne⟩
          · exact False.elim (hne rfl)
          · exact hk)
      (by
        intro k; constructor
        · intro hk
          refine ⟨hk, ?_⟩
          simp only [List.mem_singleton]
          intro he; subst k; exact hx.2.2 j hj hk
        · exact And.left)
      hq.takeNodup hn.2 hq.waitNodup (by simp)
      (by
        intro k p hk hp
        have he : k = j := by simpa using hk
        subst k
        exact queue_none_fits hq .put (by simp) j p hj hp)
    simpa [St.notifyPutOne, hqp, wakeAll] using hh

private theorem countPc_wake {s : St} {i : Nat} {old : Pc}
    (p : Pc → Bool) (hi : pcOf s i = some old) (w : Wake) :
    (wake s.tasks i w).countP (fun t => p t.pc) + (if p old then 1 else 0) =
      s.tasks.countP (fun t => p t.pc) + (if p (wakePc w old) then 1 else 0) := by
  cases ht : s.tasks[i]? with
  | none => simp [pcOf, ht] at hi
  | some t =>
    have hp : t.pc = old := by simpa [pcOf, ht] using hi
    have he : (wakeT w t).pc = wakePc w t.pc := by
      cases t with | mk op pc => cases pc <;> rfl
    simpa only [he, hp] using countP_wake (fun t => p t.pc) s.tasks i w t ht

private theorem wakeAll_runnable {s : St} {i : Nat} {pc : Pc}
    (hi : pcOf s i = some pc) (hr : ∀ k, pc ≠ .parked k)
    (q : List Nat) (w : Wake) :
    pcOf {s with tasks := wakeAll s.tasks q w} i = some pc := by
  rw [pcOf_wakeAll]
  have he : wakePc w pc = pc := by cases pc <;> simp_all [wakePc]
  by_cases h : i ∈ q <;> simp [h, hi, he]

private theorem wake_runnable {s : St} {i : Nat} {pc : Pc}
    (hi : pcOf s i = some pc) (hr : ∀ k, pc ≠ .parked k)
    (j : Nat) (w : Wake) :
    pcOf {s with tasks := wake s.tasks j w} i = some pc := by
  rw [pcOf_wake]
  have he : wakePc w pc = pc := by cases pc <;> simp_all [wakePc]
  by_cases h : i = j
  · subst j; simp [hi, he]
  · simp [h, hi]

private theorem notify_runnable {s : St} {i : Nat} {pc : Pc}
    (hi : pcOf s i = some pc) (hr : ∀ k, pc ≠ .parked k) (q : QueueSide) :
    pcOf (notifyOn s q) i = some pc := by
  cases q <;> exact wakeAll_runnable hi hr _ _

private theorem notifyOne_runnable {s : St} {i : Nat} {pc : Pc}
    (hi : pcOf s i = some pc) (hr : ∀ k, pc ≠ .parked k) :
    pcOf s.notifyPutOne i = some pc := by
  cases h : s.ch.qPut with
  | nil => simpa [St.notifyPutOne, h] using hi
  | cons j js => simpa only [St.notifyPutOne, h, pcOf] using wake_runnable hi hr j .none

private theorem passive_set_counts {s : St} {i : Nat} {old pc : Pc}
    (hi : pcOf s i = some old) (ho : passivePc old)
    (hp : pendingPc pc = false) (hb : bufPc pc = false) (hu : unbPc pc = false) :
    (setPc s.tasks i pc).countP pendingPut = s.tasks.countP pendingPut ∧
    (setPc s.tasks i pc).countP (fun t => bufPc t.pc) = wokenPutBuf s ∧
    (setPc s.tasks i pc).countP (fun t => unbPc t.pc) = wokenPutUnb s := by
  have hm := passive_metrics ho
  refine ⟨?_, ?_, ?_⟩
  · have h := countPc_set pendingPc hi pc
    simp only [hm.1, hp, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
    exact h
  · have h := countPc_set bufPc hi pc
    simp only [hm.2.1, hb, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
    exact h
  · have h := countPc_set unbPc hi pc
    simp only [hm.2.2, hu, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h
    exact h

private theorem queueInv_parkTake {sz : Nat} {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old) (ho : passivePc old)
    (k : Park) (hk : TakeQueueKind sz (.parked k)) (hopen : s.ch.isOpen = true)
    (hdata : 0 < sz → s.ch.data = [])
    (hu : sz = 0 → s.ch.qPut ≠ [] → s.ch.qTake.length + 1 ≤ wokenPutUnb s) :
    QueueInv sz (s.parkTake i k) := by
  have hr : ∀ k, old ≠ .parked k := by cases old <;> simp_all [passivePc, ordinaryPc]
  have hh : ∀ v t, old ≠ .handoff v t := by cases old <;> simp_all [passivePc, ordinaryPc]
  have hp : pendingPc (.parked k) = false := by
    by_cases hz : sz = 0 <;> cases k <;> simp_all [TakeQueueKind, pendingPc, pendingPut]
  have hc := passive_set_counts hi ho hp (by rfl) (by rfl)
  have he := queueInv_park hq hi hr hh .take k 0 hopen
    (by intro _; exact hk) (by simp) (by simp)
    (by simpa only [Int.add_zero, hc.1] using hq.availability)
    (by intro hz _; exact hdata hz)
    (by
      intro hz hqp
      change sz ≤ s.ch.data.length + (setPc s.tasks i (.parked k)).countP (fun t => bufPc t.pc)
      rw [hc.2.1]
      exact hq.bufferedPut hz hqp)
    (by
      intro hz hqp
      change (s.ch.qTake ++ [i]).length ≤ (setPc s.tasks i (.parked k)).countP (fun t => unbPc t.pc)
      rw [hc.2.2]
      simpa using hu hz hqp)
    (by simpa only [parkOn, St.parkTake, St.addAvail, Int.add_zero] using hq.unbufferedWait)
  simpa [parkOn, St.addAvail] using he

private theorem queueInv_parkWait {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv 0 s) (hi : pcOf s i = some old) (ho : passivePc old)
    (hopen : s.ch.isOpen = true) (havail : s.ch.nAvail = 0) :
    QueueInv 0 (s.parkWait i .wait) := by
  have hr : ∀ k, old ≠ .parked k := by cases old <;> simp_all [passivePc, ordinaryPc]
  have hh : ∀ v t, old ≠ .handoff v t := by cases old <;> simp_all [passivePc, ordinaryPc]
  have hc := passive_set_counts hi ho (pc := .parked .wait) (by rfl) (by rfl) (by rfl)
  have he := queueInv_park hq hi hr hh .wait .wait 0 hopen
    (by simp) (by simp) (by simp)
    (by simpa only [Int.add_zero, hc.1] using hq.availability)
    (by simp) (by simp)
    (by
      intro _ hqp
      change s.ch.qTake.length ≤ (setPc s.tasks i (.parked .wait)).countP (fun t => unbPc t.pc)
      rw [hc.2.2]
      exact hq.unbufferedPut rfl hqp)
    (by simp [havail])
  simpa [parkOn, St.addAvail] using he

private theorem notifyOne_buf_count {sz : Nat} {s : St} (hq : QueueInv sz s)
    (hz : 0 < sz) (hn : s.ch.qPut ≠ []) :
    wokenPutBuf s.notifyPutOne = wokenPutBuf s + 1 := by
  cases hqp : s.ch.qPut with
  | nil => exact False.elim (hn hqp)
  | cons j js =>
    obtain ⟨pc, hi, hk⟩ := hq.putKinds j (by simp [hqp])
    have hz' : sz ≠ 0 := Nat.ne_of_gt hz
    simp only [PutQueueKind, ite_eq_right hz'] at hk
    obtain ⟨v, rfl⟩ := hk
    have h := countPc_wake bufPc hi .none
    simpa [St.notifyPutOne, hqp, bufPc, wakePc, wokenBuf_count] using h

private theorem notifyOne_unb_count {s : St} (hq : QueueInv 0 s) (hn : s.ch.qPut ≠ []) :
    wokenPutUnb s.notifyPutOne = wokenPutUnb s + 1 := by
  cases hqp : s.ch.qPut with
  | nil => exact False.elim (hn hqp)
  | cons j js =>
    obtain ⟨pc, hi, hk⟩ := hq.putKinds j (by simp [hqp])
    simp only [PutQueueKind, ↓reduceIte] at hk
    obtain ⟨v, rfl⟩ := hk
    have h := countPc_wake unbPc hi .none
    simpa [St.notifyPutOne, hqp, unbPc, wakePc, wokenUnb_count] using h

end JuliaLean.Channels
namespace JuliaLean.Channels.HandoffSupport

private def result (s : St) (i : Nat) (v : Val) (t : Nat) : St :=
  {s with tasks := wake s.tasks t (.val v)}.finish i (.ok (some v))

 theorem queueInv_handoff {sz : Nat} {s : St} {i t : Nat} {v : Val}
    (hq : QueueInv sz s) (hi : pcOf s i = some (.handoff v t)) :
    QueueInv sz (result s i v t) := by
  obtain ⟨⟨it, ht⟩, htTake, htPut, htWait, huniq⟩ := hq.handoff i v t hi
  have hit : i ≠ t := by
    intro he
    subst t
    rw [hi] at ht
    simp at ht
  have sourceNotQueue : i ∉ s.ch.qTake ∧ i ∉ s.ch.qPut ∧ i ∉ s.ch.qWait := by
    constructor
    · intro hm
      obtain ⟨pc, hpc, hk⟩ := hq.takeKinds i hm
      rw [hi] at hpc
      cases hpc
      unfold TakeQueueKind at hk
      split at hk
      · obtain ⟨b, hb⟩ := hk; simp at hb
      · rcases hk with ⟨b, hb⟩ | hb | hb <;> simp_all
    · constructor
      · intro hm
        obtain ⟨pc, hpc, hk⟩ := hq.putKinds i hm
        rw [hi] at hpc
        cases hpc
        unfold PutQueueKind at hk
        split at hk <;> obtain ⟨x, hx⟩ := hk <;> simp_all
      · intro hm
        have hh := (hq.waitKinds i hm).2
        rw [hi] at hh
        simp at hh
  have look (j : Nat) : pcOf (result s i v t) j =
      if j = i then some (.done (.ok (some v)))
      else if j = t then some (.woken (.takeUnb it) (.val v)) else pcOf s j := by
    change pcOf ({s with tasks := wake s.tasks t (.val v)}.finish i (.ok (some v))) j = _
    unfold St.finish
    rw [pcOf_set, pcOf_wake]
    by_cases hji : j = i
    · subst j
      simp [hit, hi]
    · by_cases hjt : j = t
      · subst j
        simp [Ne.symm hit, ht, wakePc]
      · simp [hji, hjt]
  obtain ⟨ti, hgeti, htipc⟩ : ∃ ti, s.tasks[i]? = some ti ∧ ti.pc = .handoff v t := by
    cases hg : s.tasks[i]? with
    | none => simp [pcOf, hg] at hi
    | some ti => exact ⟨ti, rfl, by simpa [pcOf, hg] using hi⟩
  obtain ⟨tt, hgett, httpc⟩ : ∃ tt, s.tasks[t]? = some tt ∧ tt.pc = .parked (.takeUnb it) := by
    cases hg : s.tasks[t]? with
    | none => simp [pcOf, hg] at ht
    | some tt => exact ⟨tt, rfl, by simpa [pcOf, hg] using ht⟩
  have hgetiw : (wake s.tasks t (.val v))[i]? = some ti := by
    simp [wake_getElem?, hit, hgeti]
  have counts (p : Task → Bool)
      (hpi : p ti = p {ti with pc := .done (.ok (some v))})
      (hpt : p tt = p (wakeT (.val v) tt)) :
      (result s i v t).tasks.countP p = s.tasks.countP p := by
    have hw := countP_wake p s.tasks t (.val v) tt hgett
    have hs := countP_setPc p (wake s.tasks t (.val v)) i (.done (.ok (some v))) ti hgetiw
    simp only [← hpi, ← hpt] at hw hs
    change (setPc (wake s.tasks t (.val v)) i (.done (.ok (some v)))).countP p = _
    omega
  have cpending : (result s i v t).tasks.countP pendingPut = s.tasks.countP pendingPut :=
    counts pendingPut (by simp [pendingPut, htipc]) (by simp [pendingPut, wakeT, httpc])
  have cbuf : wokenPutBuf (result s i v t) = wokenPutBuf s := by
    apply counts
    · simp [htipc]
    · simp [wakeT, httpc]
  have cunb : wokenPutUnb (result s i v t) = wokenPutUnb s := by
    apply counts
    · simp [htipc]
    · simp [wakeT, httpc]
  have oldPark (j : Nat) (k : Park) (hh : pcOf (result s i v t) j = some (.parked k)) :
      pcOf s j = some (.parked k) ∧ j ≠ i ∧ j ≠ t := by
    rw [look] at hh
    split at hh
    · simp at hh
    · split at hh
      · simp at hh
      · exact ⟨hh, ‹j ≠ i›, ‹j ≠ t›⟩
  have oldHandoff (j : Nat) (x : Val) (u : Nat)
      (hh : pcOf (result s i v t) j = some (.handoff x u)) :
      pcOf s j = some (.handoff x u) ∧ j ≠ i ∧ j ≠ t := by
    rw [look] at hh
    split at hh
    · simp at hh
    · split at hh
      · simp at hh
      · exact ⟨hh, ‹j ≠ i›, ‹j ≠ t›⟩
  constructor
  · exact hq.closedQueues
  · change s.ch.nAvail = (s.ch.data.length : Int) + ((result s i v t).tasks.countP pendingPut : Int)
    rw [cpending]
    exact hq.availability
  · exact hq.buffer
  · intro j hj
    obtain ⟨pc, hpc, hk⟩ := hq.takeKinds j hj
    refine ⟨pc, ?_, hk⟩
    rw [look, ite_eq_right (by intro he; subst j; exact sourceNotQueue.1 hj),
      ite_eq_right (by intro he; subst j; exact htTake hj)]
    exact hpc
  · intro j hj
    obtain ⟨pc, hpc, hk⟩ := hq.putKinds j hj
    refine ⟨pc, ?_, hk⟩
    rw [look, ite_eq_right (by intro he; subst j; exact sourceNotQueue.2.1 hj),
      ite_eq_right (by intro he; subst j; exact htPut hj)]
    exact hpc
  · intro j hj
    refine ⟨(hq.waitKinds j hj).1, ?_⟩
    rw [look, ite_eq_right (by intro he; subst j; exact sourceNotQueue.2.2 hj),
      ite_eq_right (by intro he; subst j; exact htWait hj)]
    exact (hq.waitKinds j hj).2
  · exact hq.takeNodup
  · exact hq.putNodup
  · exact hq.waitNodup
  · intro j x u hj
    obtain ⟨hjOld, hji, hjt⟩ := oldHandoff j x u hj
    obtain ⟨⟨b, hu⟩, huT, huP, huW, huU⟩ := hq.handoff j x u hjOld
    have hui : u ≠ i := by intro he; subst u; rw [hi] at hu; simp at hu
    have hut : u ≠ t := by
      intro he
      subst u
      exact hji (huniq j x hjOld)
    refine ⟨⟨b, ?_⟩, huT, huP, huW, ?_⟩
    · simpa [look, hui, hut] using hu
    · intro j' x' hj'
      exact huU j' x' (oldHandoff j' x' u hj').1
  · intro j k hj
    obtain ⟨hjOld, hji, hjt⟩ := oldPark j k hj
    rcases hq.parkedCovered j k hjOld with h | h | h | ⟨u, x, hu⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · have hui : u ≠ i := by
        intro he
        subst u
        rw [hi] at hu
        have hh : v = x ∧ t = j := by simpa using hu
        exact hjt hh.2.symm
      have hut : u ≠ t := by intro he; subst u; rw [ht] at hu; simp at hu
      exact Or.inr (Or.inr (Or.inr ⟨u, x, by simpa [look, hui, hut] using hu⟩))
  · exact hq.bufferedTake
  · change 0 < sz → s.ch.qPut ≠ [] → sz ≤ s.ch.data.length + wokenPutBuf (result s i v t)
    rw [cbuf]
    exact hq.bufferedPut
  · change sz = 0 → s.ch.qPut ≠ [] → s.ch.qTake.length ≤ wokenPutUnb (result s i v t)
    rw [cunb]
    exact hq.unbufferedPut
  · exact hq.unbufferedWait
  · intro j k w hj
    rw [look] at hj
    split at hj
    · simp at hj
    · split at hj
      · have he : k = .takeUnb it ∧ w = .val v := by simpa using hj.symm
        rcases he with ⟨rfl, rfl⟩
        trivial
      · exact hq.wakeValues j k w hj
  · intro j k e hj
    rw [look] at hj
    split at hj
    · simp at hj
    · split at hj
      · simp at hj
      · exact hq.wakeError j k e hj
  · intro j b e hj
    rw [look] at hj
    split at hj
    · simp at hj
    · split at hj
      · simp at hj
      · exact hq.takeErrorEmpty j b e hj

end JuliaLean.Channels.HandoffSupport

namespace JuliaLean.Channels

private theorem queueInv_finish_passive {sz : Nat} {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old) (ho : passivePc old)
    (r : Res) (data : List Val) (d : Int)
    (ha : s.ch.nAvail + d = (data.length : Int) + (s.tasks.countP pendingPut : Int))
    (hbound : data.length ≤ sz)
    (ht : 0 < sz → s.ch.qTake ≠ [] → data = [])
    (hb : 0 < sz → s.ch.qPut ≠ [] → sz ≤ data.length + wokenPutBuf s)
    (hw : sz = 0 → s.ch.qWait ≠ [] → s.ch.nAvail + d = 0)
    (he : ∀ j it e, pcOf s j = some (.woken (.take it) (.err e)) → data = []) :
    QueueInv sz (({s with ch := {s.ch with data := data}}.addAvail d).finish i r) := by
  have hr : ∀ k, old ≠ .parked k := by cases old <;> simp_all [passivePc, ordinaryPc]
  have hh : ∀ v t, old ≠ .handoff v t := by cases old <;> simp_all [passivePc, ordinaryPc]
  have hc := passive_set_counts hi ho (pc := .done r) (by rfl) (by rfl) (by rfl)
  apply queueInv_retask hq hi hr hh (by simp) (by simp) (by simp) data d
  · simpa only [hc.1] using ha
  · exact hbound
  · exact ht
  · intro hz hqp
    change sz ≤ data.length + (setPc s.tasks i (.done r)).countP (fun t => bufPc t.pc)
    rw [hc.2.1]
    exact hb hz hqp
  · intro hz hqp
    change s.ch.qTake.length ≤ (setPc s.tasks i (.done r)).countP (fun t => unbPc t.pc)
    rw [hc.2.2]
    exact hq.unbufferedPut hz hqp
  · exact hw
  · exact he

private theorem queueInv_fetchBody {sz : Nat} {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old) (ho : passivePc old)
    (hz : 0 < sz) : QueueInv sz (fetchBody s i) := by
  cases hd : s.ch.data with
  | nil =>
    simp only [fetchBody, hd]
    cases hopen : s.ch.isOpen with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact queueInv_neutral hq hi ho (by trivial)
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact queueInv_parkTake hq hi ho .fetch
        (by simp [TakeQueueKind, Nat.ne_of_gt hz]) hopen
        (by intro _; exact hd) (by intro he; omega)
  | cons v vs =>
    simp only [fetchBody, hd]
    exact queueInv_neutral hq hi ho (by trivial)

private theorem queueInv_waitBody {sz : Nat} {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old) (ho : passivePc old)
    (hcap : s.ch.sz = sz) : QueueInv sz (waitBody s i) := by
  unfold waitBody
  by_cases ha : s.ch.nAvail > 0
  · simp only [ha, ↓reduceIte]
    exact queueInv_neutral hq hi ho (by trivial)
  · simp only [ha, ↓reduceIte]
    cases hopen : s.ch.isOpen with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact queueInv_neutral hq hi ho (by trivial)
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcap]
      have havail := hq.availability
      have hn : s.ch.nAvail = 0 := by omega
      by_cases hz : sz = 0
      · have hq0 : QueueInv 0 s := by simpa only [hz] using hq
        simpa only [hz, ↓reduceIte] using queueInv_parkWait hq0 hi ho hopen hn
      · simp only [hz, ↓reduceIte]
        have hd : s.ch.data = [] := by
          have hl : s.ch.data.length = 0 := by omega
          cases he : s.ch.data <;> simp_all
        exact queueInv_parkTake hq hi ho .wait
          (by simp [TakeQueueKind, hz]) hopen
          (by intro _; exact hd) (by intro he; exact False.elim (hz he))

private theorem queueInv_takeUnbStart {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv 0 s) (hi : pcOf s i = some old) (ho : passivePc old)
    (it : Bool) : QueueInv 0 (takeUnbStart s i it) := by
  unfold takeUnbStart
  cases hopen : s.ch.isOpen with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    exact queueInv_neutral hq hi ho (by trivial)
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hr : ∀ k, old ≠ .parked k := by cases old <;> simp_all [passivePc, ordinaryPc]
    apply queueInv_parkTake (queueInv_notifyOne hq) (notifyOne_runnable hi hr) ho (.takeUnb it)
      (by simp [TakeQueueKind]) (by cases h : s.ch.qPut <;> simpa [St.notifyPutOne, h] using hopen)
      (by omega)
    intro _ hqp
    have hn : s.ch.qPut ≠ [] := by
      intro he; simp [St.notifyPutOne, he] at hqp
    have hc := notifyOne_unb_count hq hn
    have hu := hq.unbufferedPut rfl hn
    have ht : s.notifyPutOne.ch.qTake = s.ch.qTake := by
      cases h : s.ch.qPut <;> simp [St.notifyPutOne, h]
    rw [ht, hc]
    omega

theorem queueInv_closeBody {sz : Nat} {s : St} {i : Nat}
    (hq : QueueInv sz s) (hi : pcOf s i = some .start) (e : Exc) :
    QueueInv sz (closeBody s i e) := by
  let q := s.ch.qTake ++ s.ch.qWait ++ s.ch.qPut
  let ts := wakeAll s.tasks q (.err e)
  let s' := closeBody s i e
  have hs : s' = { s with
      ch := { s.ch with excp := e, isOpen := false, qTake := [], qWait := [], qPut := [] },
      tasks := setPc ts i (.done (.ok none)) } := by
    simp [s', closeBody, St.notifyTakeAll, St.notifyWaitAll, St.notifyPutAll,
      St.finish, ts, q, wakeAll, List.foldl_append]
  have hi' : ts[i]?.map Task.pc = some .start := by
    dsimp [ts]
    rw [wakeAll_getElem?]
    cases ht : s.tasks[i]? with
    | none => simp [pcOf, ht] at hi
    | some t =>
      have hp : t.pc = .start := by simpa [pcOf, ht] using hi
      by_cases hq : i ∈ q <;> simp [hq, wakeT, hp]
  have he (j : Nat) : pcOf s' j =
      if j = i then some (.done (.ok none)) else ts[j]?.map Task.pc := by
    rw [pcOf, hs, setPc_getElem?]
    by_cases hj : j = i
    · subst j
      cases ht : ts[i]? with
      | none => simp [ht] at hi'
      | some t => simp
    · simp [hj]
  have hp (j : Nat) (k : Park) : pcOf s' j = some (.parked k) ↔
      j ≠ i ∧ j ∉ q ∧ pcOf s j = some (.parked k) := by
    rw [he]
    by_cases hj : j = i
    · simp [hj]
    · simp only [ite_eq_right hj]
      simpa [hj, ts, pcOf] using wakeAll_pc_parked s.tasks q (.err e) j k
  have hh (j : Nat) (v : Val) (t : Nat) : pcOf s' j = some (.handoff v t) ↔
      j ≠ i ∧ pcOf s j = some (.handoff v t) := by
    rw [he]
    by_cases hj : j = i
    · simp [hj]
    · simp only [ite_eq_right hj]
      simpa [hj, ts, pcOf] using wakeAll_pc_handoff s.tasks q (.err e) j v t
  have hw (j : Nat) (k : Park) (w : Wake) : pcOf s' j = some (.woken k w) ↔
      j ≠ i ∧ (pcOf s j = some (.woken k w) ∨
        (j ∈ q ∧ pcOf s j = some (.parked k) ∧ w = .err e)) := by
    rw [he]
    by_cases hj : j = i
    · simp [hj]
    · simp only [ite_eq_right hj]
      simpa [hj, ts, pcOf] using wakeAll_pc_woken s.tasks q (.err e) j k w
  have hc : (setPc ts i (.done (.ok none))).countP pendingPut =
      s.tasks.countP pendingPut := by
    have hall := countP_wakeAll_of_inv pendingPut s.tasks q (.err e)
      (pending_wake (.err e))
    cases ht : ts[i]? with
    | none => simp [ht] at hi'
    | some t =>
      have hpc : t.pc = .start := by simpa [ht] using hi'
      have hu := countP_setPc pendingPut ts i (.done (.ok none)) t ht
      simpa [pendingPut, hpc, ts, hall] using hu
  have htake (j : Nat) (it : Bool)
      (hj : pcOf s j = some (.parked (.take it))) (hjq : j ∈ q) :
      s.ch.data = [] := by
    simp only [q, List.mem_append] at hjq
    rcases hjq with (hT | hW) | hP
    · obtain ⟨pc, ht, hk⟩ := hq.takeKinds j hT
      have heq : pc = .parked (.take it) := Option.some.inj (ht.symm.trans hj)
      subst pc
      have hz : 0 < sz := by
        by_cases hz : sz = 0
        · simp [TakeQueueKind, hz] at hk
        · omega
      exact hq.bufferedTake hz (by intro he; simp [he] at hT)
    · obtain ⟨_, ht⟩ := hq.waitKinds j hW
      rw [hj] at ht
      cases ht
    · obtain ⟨pc, ht, hk⟩ := hq.putKinds j hP
      have heq : pc = .parked (.take it) := Option.some.inj (ht.symm.trans hj)
      subst pc
      simp only [PutQueueKind] at hk
      split at hk <;> obtain ⟨v, hv⟩ := hk <;> cases hv
  change QueueInv sz s'
  refine {
    closedQueues := by simp [hs]
    availability := by simpa [hs, hc] using hq.availability
    buffer := by simpa [hs] using hq.buffer
    takeKinds := by simp [hs]
    putKinds := by simp [hs]
    waitKinds := by simp [hs]
    takeNodup := by simp [hs]
    putNodup := by simp [hs]
    waitNodup := by simp [hs]
    handoff := ?_
    parkedCovered := ?_
    bufferedTake := by simp [hs]
    bufferedPut := by simp [hs]
    unbufferedPut := by simp [hs]
    unbufferedWait := by simp [hs]
    wakeValues := ?_
    wakeError := by simp [hs]
    takeErrorEmpty := ?_
  }
  · intro j v t hj
    obtain ⟨hji, hold⟩ := (hh j v t).mp hj
    obtain ⟨⟨it, ht⟩, hT, hP, hW, hu⟩ := hq.handoff j v t hold
    have hti : t ≠ i := by
      intro h; subst t
      rw [hi] at ht
      cases ht
    have htq : t ∉ q := by simpa [q] using And.intro hT (And.intro hW hP)
    refine ⟨⟨it, (hp t (.takeUnb it)).mpr ⟨hti, htq, ht⟩⟩,
      by simp [hs], by simp [hs], by simp [hs], ?_⟩
    intro j' v' hj'
    exact hu j' v' ((hh j' v' t).mp hj').2
  · intro j k hj
    obtain ⟨hji, hjq, hold⟩ := (hp j k).mp hj
    rcases hq.parkedCovered j k hold with hT | hP | hW | ⟨j', v, hh'⟩
    · exact False.elim (hjq (by simp [q, hT]))
    · exact False.elim (hjq (by simp [q, hP]))
    · exact False.elim (hjq (by simp [q, hW]))
    · have hji' : j' ≠ i := by
        intro h; subst j'
        rw [hi] at hh'
        cases hh'
      exact Or.inr (Or.inr (Or.inr ⟨j', v, (hh j' v j).mpr ⟨hji', hh'⟩⟩))
  · intro j k w hj
    obtain ⟨_, hold | ⟨_, _, heq⟩⟩ := (hw j k w).mp hj
    · exact hq.wakeValues j k w hold
    · subst w
      cases k <;> simp [WakeFits]
  · intro j it e' hj
    obtain ⟨_, hold | ⟨hjq, hold, _⟩⟩ := (hw j (.take it) (.err e')).mp hj
    · simpa [hs] using hq.takeErrorEmpty j it e' hold
    · simpa [hs] using htake j it hold hjq
end JuliaLean.Channels

namespace JuliaLean.Channels

private theorem queueInv_takeBufBody {sz : Nat} {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old) (ho : passivePc old)
    (hz : 0 < sz) (it : Bool) : QueueInv sz (takeBufBody s i it) := by
  cases hd : s.ch.data with
  | nil =>
    simp only [takeBufBody, hd]
    cases hopen : s.ch.isOpen with
    | false =>
      simp only [Bool.not_false, ↓reduceIte]
      exact queueInv_neutral hq hi ho (by trivial)
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact queueInv_parkTake hq hi ho (.take it)
        (by simp [TakeQueueKind, Nat.ne_of_gt hz]) hopen
        (by intro _; exact hd) (by intro he; omega)
  | cons v data =>
    have hr : ∀ k, old ≠ .parked k := by cases old <;> simp_all [passivePc, ordinaryPc]
    have hqn := queueInv_notifyOne hq
    have hin := notifyOne_runnable hi hr
    have hdat : s.notifyPutOne.ch.data = s.ch.data := by
      cases h : s.ch.qPut <;> simp [St.notifyPutOne, h]
    have hav : s.notifyPutOne.ch.nAvail = s.ch.nAvail := by
      cases h : s.ch.qPut <;> simp [St.notifyPutOne, h]
    have hqt : s.notifyPutOne.ch.qTake = s.ch.qTake := by
      cases h : s.ch.qPut <;> simp [St.notifyPutOne, h]
    have hfinish := queueInv_finish_passive hqn hin ho (finishTake it (.ok (some v))) data (-1)
      (by have h := hqn.availability; rw [hdat, hd] at h; simp only [List.length_cons] at h; omega)
      (by have h := hq.buffer; rw [hd] at h; simp only [List.length_cons] at h; omega)
      (by
        intro _ hnon
        have hempty := hq.bufferedTake hz (by simpa only [hqt] using hnon)
        rw [hd] at hempty; contradiction)
      (by
        intro _ hnon
        have hold : s.ch.qPut ≠ [] := by intro he; simp [St.notifyPutOne, he] at hnon
        have hc := notifyOne_buf_count hq hz hold
        have hb := hq.bufferedPut hz hold
        rw [hd] at hb
        simp only [List.length_cons] at hb
        rw [hc]
        omega)
      (by intro he; omega)
      (by
        intro j it' e hj
        have he := hqn.takeErrorEmpty j it' e hj
        rw [hdat, hd] at he; contradiction)
    cases hqp : s.ch.qPut <;>
      simpa [takeBufBody, hd, St.notifyPutOne, hqp, St.addAvail, St.finish] using hfinish

private theorem queueInv_takeBody {sz : Nat} {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old) (ho : passivePc old)
    (hcap : s.ch.sz = sz) (it : Bool) : QueueInv sz (takeBody s i it) := by
  unfold takeBody
  rw [hcap]
  by_cases hz : sz = 0
  · simp only [hz, ↓reduceIte]
    exact queueInv_takeUnbStart (by simpa only [hz] using hq) hi ho it
  · simp only [hz, ↓reduceIte]
    exact queueInv_takeBufBody hq hi ho (by omega) it

private theorem queueInv_emptyBody {sz : Nat} {s : St} {i : Nat} {old : Pc}
    (hq : QueueInv sz s) (hi : pcOf s i = some old) (ho : passivePc old) :
    QueueInv sz (emptyBody s i) := by
  let s0 : St := {s with dropped := s.dropped ++ s.ch.data}
  have hq0 : QueueInv sz s0 := {hq with closedQueues := hq.closedQueues}
  have hi0 : pcOf s0 i = some old := hi
  have hr : ∀ k, old ≠ .parked k := by cases old <;> simp_all [passivePc, ordinaryPc]
  have hqn := queueInv_notify hq0 .put (by simp)
  have hin := notify_runnable hi0 hr .put
  have hf := queueInv_finish_passive hqn hin ho (.ok none) [] (-(s.ch.data.length : Int))
    (by
      have h := hqn.availability
      change s.ch.nAvail = (s.ch.data.length : Int) + _ at h
      change s.ch.nAvail + -(s.ch.data.length : Int) = (0 : Int) + _
      omega)
    (by simp) (by simp)
    (by simp [notifyOn, St.notifyPutAll])
    (by
      intro hz hnon
      have hb := hq.buffer
      have he : s.ch.data.length = 0 := by omega
      have hw := hqn.unbufferedWait hz hnon
      simpa only [he, Int.natCast_zero, Int.neg_zero, Int.add_zero] using hw)
    (by simp)
  simpa [emptyBody, s0, notifyOn, St.notifyPutAll, St.addAvail, St.finish] using hf

end JuliaLean.Channels

namespace JuliaLean.Channels

private theorem putBuf_done_counts {s : St} {i : Nat} (v : Val) (fresh : Bool) (w : Wake)
    (hi : pcOf s i = some (if fresh then .putLocked v else .woken (.putBuf v) w))
    (r : Res) :
    (setPc s.tasks i (.done r)).countP pendingPut + (if fresh then 0 else 1) =
      s.tasks.countP pendingPut ∧
    (setPc s.tasks i (.done r)).countP (fun t => bufPc t.pc) + (if fresh then 0 else 1) =
      wokenPutBuf s := by
  constructor
  · have h := countPc_set pendingPc hi (.done r)
    cases fresh <;> simpa [pendingPc, pendingPut] using h
  · have h := countPc_set bufPc hi (.done r)
    cases fresh <;> simpa [bufPc, wokenBuf_count] using h

private theorem queueInv_putBufBody {sz : Nat} {s : St} {i : Nat}
    (hq : QueueInv sz s) (v : Val) (fresh : Bool) (w : Wake)
    (hi : pcOf s i = some (if fresh then .putLocked v else .woken (.putBuf v) w))
    (hcap : s.ch.sz = sz) (hz : 0 < sz) :
    QueueInv sz (putBufBody (s.addAvail (if fresh then 1 else 0)) i v) := by
  let bump : Int := if fresh then 1 else 0
  let bit : Nat := if fresh then 0 else 1
  have hbit : bit ≤ 1 := by cases fresh <;> decide
  have hbalance : (bit : Int) + bump = 1 := by cases fresh <;> rfl
  have hr : ∀ k, (if fresh then Pc.putLocked v else .woken (.putBuf v) w) ≠ .parked k := by
    cases fresh <;> simp
  have hh : ∀ v' t, (if fresh then Pc.putLocked v else .woken (.putBuf v) w) ≠ .handoff v' t := by
    cases fresh <;> simp
  cases hopen : s.ch.isOpen with
  | false =>
    have hc := (putBuf_done_counts v fresh w hi (.err s.ch.excp)).1
    change (setPc s.tasks i (.done (.err s.ch.excp))).countP pendingPut + bit = _ at hc
    obtain ⟨_, hqp, hqw⟩ := hq.closedQueues hopen
    have hf := queueInv_retask (pc := .done (.err s.ch.excp)) hq hi hr hh
      (by simp) (by simp) (by simp) s.ch.data (bump - 1)
      (by have ha := hq.availability; omega)
      hq.buffer hq.bufferedTake
      (by simp [hqp]) (by simp [hqp]) (by simp [hqw]) hq.takeErrorEmpty
    simpa [putBufBody, St.addAvail, St.finish, St.goto, hopen, bump, Int.add_assoc, Int.sub_eq_add_neg] using hf
  | true =>
    by_cases hfull : s.ch.data.length = s.ch.sz
    · have hc := countPc_set pendingPc hi (.parked (.putBuf v))
      have he : (setPc s.tasks i (.parked (.putBuf v))).countP pendingPut + bit =
          s.tasks.countP pendingPut + 1 := by
        cases fresh <;> simpa [pendingPc, pendingPut, bit] using hc
      have hp := queueInv_park hq hi hr hh .put (.putBuf v) bump hopen
        (by simp) (by simp [PutQueueKind, Nat.ne_of_gt hz]) (by simp)
        (by have ha := hq.availability; omega)
        (by simpa only [parkOn, St.parkPut, St.addAvail] using hq.bufferedTake)
        (by intro _ _; rw [hcap] at hfull; omega)
        (by intro he; omega)
        (by intro he; omega)
      simpa [putBufBody, St.addAvail, hopen, hfull, parkOn, bump] using hp
    · have hqn := queueInv_notify hq .take (by intro _; exact hz)
      have hin := notify_runnable hi hr .take
      have hc := putBuf_done_counts v fresh w hin (.ok (some v))
      have hpending : (setPc (notifyOn s .take).tasks i (.done (.ok (some v)))).countP pendingPut + bit =
          (notifyOn s .take).tasks.countP pendingPut := hc.1
      have hbuf : (setPc (notifyOn s .take).tasks i (.done (.ok (some v)))).countP (fun t => bufPc t.pc) + bit =
          wokenPutBuf (notifyOn s .take) := hc.2
      have hf := queueInv_retask (pc := .done (.ok (some v))) hqn hin hr hh
        (by simp) (by simp) (by simp) (s.ch.data ++ [v]) bump
        (by
          have ha := hqn.availability
          change s.ch.nAvail = (s.ch.data.length : Int) + _ at ha
          change s.ch.nAvail + bump = ((s.ch.data ++ [v]).length : Int) + _
          simp only [List.length_append, List.length_singleton, Int.natCast_add, Int.natCast_one]
          omega)
        (by
          have hb := hq.buffer
          simp only [List.length_append, List.length_singleton]
          rw [hcap] at hfull
          omega)
        (by simp [notifyOn, St.notifyTakeAll])
        (by
          intro hsz hqp
          have hb := hqn.bufferedPut hsz hqp
          change sz ≤ (s.ch.data ++ [v]).length +
            (setPc (notifyOn s .take).tasks i (.done (.ok (some v)))).countP (fun t => bufPc t.pc)
          change sz ≤ s.ch.data.length + wokenPutBuf (notifyOn s .take) at hb
          simp only [List.length_append, List.length_singleton]
          omega)
        (by intro he; omega)
        (by intro he; omega)
        (by
          intro j it e hj
          have he := hqn.wakeError j (.take it) e hj
          simp [notifyOn, St.notifyTakeAll, hopen] at he)
      simpa [putBufBody, St.addAvail, St.goto, St.finish, notifyOn, St.notifyTakeAll,
        hopen, hfull, bump] using hf

end JuliaLean.Channels

namespace JuliaLean.Channels

private theorem putUnb_done_count {s : St} {i : Nat} (v : Val) (fresh : Bool) (w : Wake)
    (hi : pcOf s i = some (if fresh then .putLocked v else .woken (.putUnb v) w))
    (r : Res) :
    (setPc s.tasks i (.done r)).countP pendingPut + (if fresh then 0 else 1) =
      s.tasks.countP pendingPut := by
  have h := countPc_set pendingPc hi (.done r)
  cases fresh <;> simpa [pendingPc, pendingPut] using h

private theorem queueInv_putUnbPark {s : St} {i : Nat}
    (hq : QueueInv 0 s) (v : Val) (fresh : Bool) (w : Wake)
    (hi : pcOf s i = some (if fresh then .putLocked v else .woken (.putUnb v) w))
    (hopen : s.ch.isOpen = true) (htake : s.ch.qTake = []) :
    QueueInv 0 (((s.addAvail (if fresh then 1 else 0)).notifyWaitAll .none).parkPut i (.putUnb v)) := by
  let bump : Int := if fresh then 1 else 0
  let bit : Nat := if fresh then 0 else 1
  have hbalance : (bit : Int) + bump = 1 := by cases fresh <;> rfl
  have hr : ∀ k, (if fresh then Pc.putLocked v else .woken (.putUnb v) w) ≠ .parked k := by
    cases fresh <;> simp
  have hh : ∀ v' t, (if fresh then Pc.putLocked v else .woken (.putUnb v) w) ≠ .handoff v' t := by
    cases fresh <;> simp
  have hqn := queueInv_notify hq .wait (by simp)
  have hin := notify_runnable hi hr .wait
  have hc := countPc_set pendingPc hin (.parked (.putUnb v))
  have he : (setPc (notifyOn s .wait).tasks i (.parked (.putUnb v))).countP pendingPut + bit =
      (notifyOn s .wait).tasks.countP pendingPut + 1 := by
    cases fresh <;> simpa [pendingPc, pendingPut, bit] using hc
  have hp := queueInv_park hqn hin hr hh .put (.putUnb v) bump hopen
    (by simp) (by simp [PutQueueKind]) (by simp)
    (by have ha := hqn.availability; omega)
    (by simp) (by simp)
    (by simp [parkOn, St.parkPut, St.addAvail, notifyOn, St.notifyWaitAll, htake])
    (by simp [parkOn, St.parkPut, St.addAvail, notifyOn, St.notifyWaitAll])
  simpa [parkOn, St.parkPut, St.addAvail, notifyOn, St.notifyWaitAll, bump] using hp

end JuliaLean.Channels

namespace JuliaLean.Channels

private theorem queueInv_putFailure {sz : Nat} {s : St} {i : Nat} {k : Park} {e : Exc}
    (hq : QueueInv sz s) (hi : pcOf s i = some (.woken k (.err e)))
    (hk : (∃ v, k = .putBuf v) ∨ ∃ v, k = .putUnb v) :
    QueueInv sz ((s.addAvail (-1)).finish i (.err e)) := by
  have hclosed := hq.wakeError i k e hi
  obtain ⟨_, hqp, hqw⟩ := hq.closedQueues hclosed
  have hc := countPc_set pendingPc hi (.done (.err e))
  have he : (setPc s.tasks i (.done (.err e))).countP pendingPut + 1 =
      s.tasks.countP pendingPut := by
    rcases hk with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> simpa [pendingPc, pendingPut] using hc
  have hf := queueInv_retask (pc := .done (.err e)) hq hi
    (by simp) (by simp) (by simp) (by simp) (by simp) s.ch.data (-1)
    (by have ha := hq.availability; omega)
    hq.buffer hq.bufferedTake (by simp [hqp]) (by simp [hqp]) (by simp [hqw]) hq.takeErrorEmpty
  simpa [St.addAvail, St.goto, St.finish] using hf

end JuliaLean.Channels

namespace JuliaLean.Channels.HandoffBegin

private def result (s : St) (i : Nat) (v : Val) (q : List Nat) (bump : Int) (t : Nat) : St :=
  (({s with ch := {s.ch with qTake := q}}.addAvail (bump - 1)).goto i (.handoff v t))

 theorem queueInv_handoff_begin {s : St} {i t : Nat} {v : Val} {old : Pc}
    {bump : Int} {q : List Nat}
    (hq : QueueInv 0 s) (hi : pcOf s i = some old)
    (hphase : (old = .putLocked v ∧ bump = 1) ∨ ∃ w, old = .woken (.putUnb v) w ∧ bump = 0)
    (hopen : s.ch.isOpen = true) (htake : s.ch.qTake = t :: q) :
    QueueInv 0 (result s i v q bump t) := by
  have oldNotPark : ∀ k, old ≠ .parked k := by
    rcases hphase with ⟨rfl, _⟩ | ⟨w, rfl, _⟩ <;> intros <;> simp
  have oldNotHandoff : ∀ x u, old ≠ .handoff x u := by
    rcases hphase with ⟨rfl, _⟩ | ⟨w, rfl, _⟩ <;> intros <;> simp
  obtain ⟨it, ht⟩ : ∃ it, pcOf s t = some (.parked (.takeUnb it)) := by
    obtain ⟨pc, hp, hk⟩ := hq.takeKinds t (by simp [htake])
    obtain ⟨it, rfl⟩ := (by simpa [TakeQueueKind] using hk : ∃ it, pc = .parked (.takeUnb it))
    exact ⟨it, hp⟩
  have hit : i ≠ t := by
    intro he
    subst t
    have he : old = .parked (.takeUnb it) := Option.some.inj (hi.symm.trans ht)
    exact oldNotPark _ he
  have sourceNotQueue : i ∉ s.ch.qTake ∧ i ∉ s.ch.qPut ∧ i ∉ s.ch.qWait := by
    constructor
    · intro hm
      obtain ⟨pc, hp, hk⟩ := hq.takeKinds i hm
      obtain ⟨b, rfl⟩ := (by simpa [TakeQueueKind] using hk : ∃ b, pc = .parked (.takeUnb b))
      exact oldNotPark _ (Option.some.inj (hi.symm.trans hp))
    · constructor
      · intro hm
        obtain ⟨pc, hp, hk⟩ := hq.putKinds i hm
        obtain ⟨x, rfl⟩ := (by simpa [PutQueueKind] using hk : ∃ x, pc = .parked (.putUnb x))
        exact oldNotPark _ (Option.some.inj (hi.symm.trans hp))
      · intro hm
        exact oldNotPark _ (Option.some.inj (hi.symm.trans (hq.waitKinds i hm).2))
  have htPut : t ∉ s.ch.qPut := by
    intro hm
    obtain ⟨pc, hp, hk⟩ := hq.putKinds t hm
    obtain ⟨x, rfl⟩ := (by simpa [PutQueueKind] using hk : ∃ x, pc = .parked (.putUnb x))
    rw [ht] at hp
    simp at hp
  have htWait : t ∉ s.ch.qWait := by
    intro hm
    have hh := (hq.waitKinds t hm).2
    rw [ht] at hh
    simp at hh
  have hnd : t ∉ q ∧ q.Nodup := by
    have hh := hq.takeNodup
    simpa [htake] using hh
  have look (j : Nat) : pcOf (result s i v q bump t) j =
      if j = i then some (.handoff v t) else pcOf s j := by
    simp only [pcOf, result, St.goto, St.addAvail, setPc_getElem?]
    by_cases hj : j = i
    · subst j
      simp only [ite_true, Option.map_map]
      have hmap : s.tasks[i]?.map (fun _ => Pc.handoff v t) = some (Pc.handoff v t) := by
        cases hg : s.tasks[i]? <;> simp_all [pcOf]
      exact hmap
    · simp [hj]
  obtain ⟨op, hgeti⟩ : ∃ op, s.tasks[i]? = some ⟨op, old⟩ := by
    cases hg : s.tasks[i]? with
    | none => simp [pcOf, hg] at hi
    | some ti =>
      have htipc : ti.pc = old := by simpa [pcOf, hg] using hi
      rcases ti with ⟨op, pc⟩
      simp only at htipc
      subst pc
      exact ⟨op, rfl⟩
  have hmetrics :
      ((result s i v q bump t).tasks.countP pendingPut : Int) + (1 - bump) = (s.tasks.countP pendingPut : Int) ∧
      (wokenPutUnb (result s i v q bump t) : Int) + (1 - bump) = (wokenPutUnb s : Int) ∧
      wokenPutBuf (result s i v q bump t) = wokenPutBuf s ∧ 0 ≤ bump ∧ bump ≤ 1 := by
    rcases hphase with ⟨rfl, rfl⟩ | ⟨w, rfl, rfl⟩
    · have hp : (result s i v q 1 t).tasks.countP pendingPut = s.tasks.countP pendingPut := by
        change (setPc s.tasks i (.handoff v t)).countP pendingPut + 0 =
          s.tasks.countP pendingPut + 0
        exact countP_setPc _ s.tasks i (.handoff v t) _ hgeti
      have hu : wokenPutUnb (result s i v q 1 t) = wokenPutUnb s := by
        unfold wokenPutUnb
        change (setPc s.tasks i (.handoff v t)).countP _ + 0 =
          s.tasks.countP _ + 0
        exact countP_setPc _ s.tasks i (.handoff v t) _ hgeti
      have hb : wokenPutBuf (result s i v q 1 t) = wokenPutBuf s := by
        unfold wokenPutBuf
        change (setPc s.tasks i (.handoff v t)).countP _ + 0 =
          s.tasks.countP _ + 0
        exact countP_setPc _ s.tasks i (.handoff v t) _ hgeti
      rw [hp, hu, hb]
      omega
    · have hp : (result s i v q 0 t).tasks.countP pendingPut + 1 = s.tasks.countP pendingPut := by
        change (setPc s.tasks i (.handoff v t)).countP pendingPut + 1 =
          s.tasks.countP pendingPut + 0
        exact countP_setPc _ s.tasks i (.handoff v t) _ hgeti
      have hu : wokenPutUnb (result s i v q 0 t) + 1 = wokenPutUnb s := by
        unfold wokenPutUnb
        change (setPc s.tasks i (.handoff v t)).countP _ + 1 =
          s.tasks.countP _ + 0
        exact countP_setPc _ s.tasks i (.handoff v t) _ hgeti
      have hb : wokenPutBuf (result s i v q 0 t) = wokenPutBuf s := by
        unfold wokenPutBuf
        change (setPc s.tasks i (.handoff v t)).countP _ + 0 =
          s.tasks.countP _ + 0
        exact countP_setPc _ s.tasks i (.handoff v t) _ hgeti
      omega
  have hav : (result s i v q bump t).ch.nAvail =
      ((result s i v q bump t).ch.data.length : Int) +
        ((result s i v q bump t).tasks.countP pendingPut : Int) := by
    have hh := hq.availability
    change s.ch.nAvail + (bump - 1) = (s.ch.data.length : Int) + _
    omega
  have htargetNoOldSender : ∀ j x, pcOf s j ≠ some (.handoff x t) := by
    intro j x hj
    have hh := (hq.handoff j x t hj).2.1
    exact hh (by simp [htake])
  constructor
  · intro hc
    have hh : s.ch.isOpen = false := hc
    simp [hopen] at hh
  · exact hav
  · exact hq.buffer
  · intro j hj
    change j ∈ q at hj
    obtain ⟨pc, hp, hk⟩ := hq.takeKinds j (by simp [htake, hj])
    refine ⟨pc, ?_, hk⟩
    have hji : j ≠ i := by intro he; subst j; exact sourceNotQueue.1 (by simp [htake, hj])
    simpa [look, hji] using hp
  · intro j hj
    obtain ⟨pc, hp, hk⟩ := hq.putKinds j hj
    refine ⟨pc, ?_, hk⟩
    have hji : j ≠ i := by intro he; subst j; exact sourceNotQueue.2.1 hj
    simpa [look, hji] using hp
  · intro j hj
    refine ⟨rfl, ?_⟩
    have hji : j ≠ i := by intro he; subst j; exact sourceNotQueue.2.2 hj
    simpa [look, hji] using (hq.waitKinds j hj).2
  · exact hnd.2
  · exact hq.putNodup
  · exact hq.waitNodup
  · intro j x u hj
    rw [look] at hj
    by_cases hji : j = i
    · subst j
      simp only [ite_true, Option.some.injEq, Pc.handoff.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      refine ⟨⟨it, ?_⟩, hnd.1, htPut, htWait, ?_⟩
      · simpa [look, Ne.symm hit] using ht
      · intro j' x' hj'
        rw [look] at hj'
        by_cases hj'i : j' = i
        · exact hj'i
        · rw [ite_eq_right hj'i] at hj'
          exact False.elim (htargetNoOldSender j' x' hj')
    · rw [ite_eq_right hji] at hj
      obtain ⟨⟨b, hu⟩, huT, huP, huW, huU⟩ := hq.handoff j x u hj
      have hui : u ≠ i := by
        intro he
        subst u
        exact oldNotPark _ (Option.some.inj (hi.symm.trans hu))
      have hut : u ≠ t := by intro he; subst u; exact htargetNoOldSender j x hj
      refine ⟨⟨b, ?_⟩, ?_, huP, huW, ?_⟩
      · simpa [look, hui] using hu
      · intro hm
        change u ∈ q at hm
        exact huT (by simp [htake, hm])
      · intro j' x' hj'
        rw [look] at hj'
        by_cases hj'i : j' = i
        · subst j'
          simp only [ite_true, Option.some.injEq, Pc.handoff.injEq] at hj'
          exact False.elim (hut hj'.2.symm)
        · rw [ite_eq_right hj'i] at hj'
          exact huU j' x' hj'
  · intro j k hj
    rw [look] at hj
    by_cases hji : j = i
    · simp [hji] at hj
    · rw [ite_eq_right hji] at hj
      rcases hq.parkedCovered j k hj with h | h | h | ⟨u, x, hu⟩
      · have hm : j = t ∨ j ∈ q := by simpa [htake] using h
        rcases hm with rfl | hm
        · exact Or.inr (Or.inr (Or.inr ⟨i, v, by simp [look]⟩))
        · exact Or.inl hm
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · have hui : u ≠ i := by
          intro he
          subst u
          exact oldNotHandoff _ _ (Option.some.inj (hi.symm.trans hu))
        exact Or.inr (Or.inr (Or.inr ⟨u, x, by simpa [look, hui] using hu⟩))
  · intro hh; omega
  · intro hh; omega
  · intro _ hput
    have hh := hq.unbufferedPut rfl hput
    rw [htake] at hh
    change q.length ≤ wokenPutUnb (result s i v q bump t)
    simp only [List.length_cons] at hh
    omega
  · intro _ hwait
    have hh := hq.unbufferedWait rfl hwait
    have ha := hq.availability
    have hb := hq.buffer
    change s.ch.nAvail + (bump - 1) = 0
    omega
  · intro j k w hj
    rw [look] at hj
    split at hj
    · simp at hj
    · exact hq.wakeValues j k w hj
  · intro j k e hj
    rw [look] at hj
    split at hj
    · simp at hj
    · exact hq.wakeError j k e hj
  · intro j b e hj
    rw [look] at hj
    split at hj
    · simp at hj
    · exact hq.takeErrorEmpty j b e hj

end JuliaLean.Channels.HandoffBegin
namespace JuliaLean.Channels

private theorem queueInv_putUnbBody {s : St} {i : Nat}
    (hq : QueueInv 0 s) (v : Val) (fresh : Bool) (w : Wake)
    (hi : pcOf s i = some (if fresh then .putLocked v else .woken (.putUnb v) w)) :
    QueueInv 0 (putUnbBody (s.addAvail (if fresh then 1 else 0)) i v) := by
  let bump : Int := if fresh then 1 else 0
  let bit : Nat := if fresh then 0 else 1
  have hbalance : (bit : Int) + bump = 1 := by cases fresh <;> rfl
  have hr : ∀ k, (if fresh then Pc.putLocked v else .woken (.putUnb v) w) ≠ .parked k := by
    cases fresh <;> simp
  have hh : ∀ v' t, (if fresh then Pc.putLocked v else .woken (.putUnb v) w) ≠ .handoff v' t := by
    cases fresh <;> simp
  cases hopen : s.ch.isOpen with
  | false =>
    have hc := putUnb_done_count v fresh w hi (.err s.ch.excp)
    change (setPc s.tasks i (.done (.err s.ch.excp))).countP pendingPut + bit = _ at hc
    obtain ⟨_, hqp, hqw⟩ := hq.closedQueues hopen
    have hf := queueInv_retask (pc := .done (.err s.ch.excp)) hq hi hr hh
      (by simp) (by simp) (by simp) s.ch.data (bump - 1)
      (by have ha := hq.availability; omega)
      hq.buffer hq.bufferedTake
      (by simp [hqp]) (by simp [hqp]) (by simp [hqw]) hq.takeErrorEmpty
    simpa [putUnbBody, St.addAvail, St.finish, St.goto, hopen, bump, Int.add_assoc, Int.sub_eq_add_neg] using hf
  | true =>
    cases ht : s.ch.qTake with
    | nil =>
      simpa [putUnbBody, St.addAvail, hopen, ht] using queueInv_putUnbPark hq v fresh w hi hopen ht
    | cons t q =>
      have hphase : ((if fresh then Pc.putLocked v else .woken (.putUnb v) w) = .putLocked v ∧ bump = 1) ∨
          ∃ w', (if fresh then Pc.putLocked v else .woken (.putUnb v) w) = .woken (.putUnb v) w' ∧ bump = 0 := by
        cases fresh
        · exact Or.inr ⟨w, rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
      have hp := HandoffBegin.queueInv_handoff_begin hq hi hphase hopen ht
      change QueueInv 0 (({s with ch := {s.ch with qTake := q}}.addAvail (bump - 1)).goto i (.handoff v t)) at hp
      simpa [putUnbBody, St.addAvail, St.goto, hopen, ht, bump, Int.add_assoc, Int.sub_eq_add_neg] using hp

theorem queueInv_step {sz : Nat} {ops : List Op} {s s' : St} {i : Nat}
    (hq : QueueInv sz s) (hf : FitInv sz ops s) (h : stepTask s i = some s') :
    QueueInv sz s' := by
  cases ht : s.tasks[i]? with
  | none => simp [stepTask, ht] at h
  | some t =>
    have hp := hf.fits t (List.mem_of_getElem? ht)
    rcases t with ⟨op, pc⟩
    have hi : pcOf s i = some pc := by simp [pcOf, ht]
    cases pc with
    | start =>
      cases op with
      | put v =>
        simp only [stepTask, ht] at h
        split at h <;> cases h
        all_goals exact queueInv_neutral hq hi (by trivial) (by trivial)
      | take =>
        simp only [stepTask, ht, Option.some.injEq] at h
        subst s'
        exact queueInv_takeBody hq hi (by trivial) hf.capacity false
      | iter =>
        simp only [stepTask, ht] at h
        split at h <;> cases h
        all_goals exact queueInv_neutral hq hi (by trivial) (by trivial)
      | fetch =>
        simp only [stepTask, ht] at h
        split at h <;> cases h
        · exact queueInv_neutral hq hi (by trivial) (by trivial)
        · exact queueInv_fetchBody hq hi (by trivial) (by have hc := hf.capacity; omega)
      | wait =>
        simp only [stepTask, ht] at h
        split at h <;> cases h
        all_goals exact queueInv_neutral hq hi (by trivial) (by trivial)
      | close e =>
        simp only [stepTask, ht, Option.some.injEq] at h
        subst s'
        exact queueInv_closeBody hq hi e
      | empty =>
        simp only [stepTask, ht, Option.some.injEq] at h
        subst s'
        exact queueInv_emptyBody hq hi (by trivial)
    | putLocked v =>
      change op = .put v at hp
      subst op
      simp only [stepTask, ht] at h
      split at h <;> cases h
      · have hz : sz = 0 := by have hc := hf.capacity; omega
        simpa [hz, St.addAvail] using queueInv_putUnbBody (by simpa only [hz] using hq) v true .none hi
      · exact queueInv_putBufBody hq v true .none hi hf.capacity (by have hc := hf.capacity; omega)
    | takeLocked it =>
      change op = .iter ∧ it = true at hp
      rcases hp with ⟨rfl, rfl⟩
      simp only [stepTask, ht, Option.some.injEq] at h
      subst s'
      exact queueInv_takeBody hq hi (by trivial) hf.capacity true
    | waitLocked =>
      change op = .wait at hp
      subst op
      simp only [stepTask, ht, Option.some.injEq] at h
      subst s'
      exact queueInv_waitBody hq hi (by trivial) hf.capacity
    | parked k => cases op <;> simp [stepTask, ht] at h
    | done r => cases op <;> simp [stepTask, ht] at h
    | handoff v j =>
      change op = .put v ∧ sz = 0 at hp
      rcases hp with ⟨rfl, _⟩
      simp only [stepTask, ht, Option.some.injEq] at h
      subst s'
      exact HandoffSupport.queueInv_handoff hq hi
    | woken k w =>
      cases k with
      | putBuf v =>
        change op = .put v ∧ 0 < sz at hp
        rcases hp with ⟨rfl, hsz⟩
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals first
          | exact queueInv_putFailure hq hi (Or.inl ⟨v, rfl⟩)
          | simpa [St.addAvail] using queueInv_putBufBody hq v false _ hi hf.capacity hsz
      | putUnb v =>
        change op = .put v ∧ sz = 0 at hp
        rcases hp with ⟨rfl, hsz⟩
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals first
          | exact queueInv_putFailure hq hi (Or.inr ⟨v, rfl⟩)
          | simpa [hsz, St.addAvail] using queueInv_putUnbBody (by simpa only [hsz] using hq) v false _ hi
      | take it =>
        cases it <;> simp only [PcFits, ParkFits] at hp <;>
          rcases hp with ⟨rfl, hsz⟩ <;> cases w <;>
          simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals first
          | exact queueInv_neutral hq hi (by trivial) (by trivial)
          | exact queueInv_takeBufBody hq hi (by trivial) hsz _
      | takeUnb it =>
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals exact queueInv_neutral hq hi (by trivial) (by trivial)
      | fetch =>
        change op = .fetch ∧ 0 < sz at hp
        rcases hp with ⟨rfl, hsz⟩
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals first
          | exact queueInv_neutral hq hi (by trivial) (by trivial)
          | exact queueInv_fetchBody hq hi (by trivial) hsz
      | wait =>
        change op = .wait at hp
        subst op
        cases w <;> simp only [stepTask, ht, Option.some.injEq] at h <;> subst s'
        all_goals first
          | exact queueInv_neutral hq hi (by trivial) (by trivial)
          | exact queueInv_waitBody hq hi (by trivial) hf.capacity

end JuliaLean.Channels
