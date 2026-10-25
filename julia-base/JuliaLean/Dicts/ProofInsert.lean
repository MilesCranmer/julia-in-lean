import JuliaLean.Dicts.ProofRehash
import JuliaLean.Dicts.InvAge

/-!
# Insertion: `ht_keyindex2_shorthash!`, `_setindex!`, `setindex!`

The insertion probe returns the slot of a present key, or a free slot on
the key's probe sequence; its `rehash!` tail call happens only when at least
`max(16, sz >> 6)` slots are filled, so each call at least doubles the size
and the fuel `count + 8` is never exhausted.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-- A free slot on the probe sequence of `q`. -/
def InsertSlot (o : KeyOps K) (t : Table K V) (q : K) (j : Nat) : Prop :=
  1 ≤ j ∧ j ≤ t.size ∧ isFilledB (t.slots j) = false ∧ Chain o t q j

/-! ## Storing a new key -/

theorem Inv.store {o : KeyOps K} (hl : o.Lawful) {t t' : Table K V} (hi : Inv o t) {j : Nat}
    {k : K} {v : V} (hj : InsertSlot o t k j) (habs : Absent o t k)
    (hs : t'.size = t.size) (hsl : t'.slots = upd t.slots j (shorthash7 (o.hash k)))
    (hk : t'.keys = upd t.keys j (some k)) (hv : t'.vals = upd t.vals j (some v))
    (hc : t'.count = t.count + 1) (hm : t'.maxprobe = t.maxprobe)
    (hf1 : 1 ≤ t'.idxfloor) (hf2 : t'.idxfloor ≤ t.idxfloor) (hf3 : t'.idxfloor ≤ j)
    (hp : 1 ≤ t'.popcursor) :
    Inv o t' ∧ List.Perm (tlist t') ((k, v) :: tlist t) := by
  obtain ⟨hj1, hj2, hjf, hjc⟩ := hj
  have hpow : IsPow t.size := by
    rcases hi.size with h | h
    · omega
    · exact h
  have hmp : t.maxprobe < t.size := by
    rcases hi.maxprobe with h | h
    · omega
    · exact h
  have hent : ∀ i, ent t' i = if i = j then some (k, v) else ent t i :=
    ent_store_eq (shorthash7_filled _) hsl hk hv
  have hnone : ent t j = none := ent_of_not_filled hjf
  have hstore := tlist_store (o := o) hs hj1 hj2 (fun i _ _ => hent i)
    (fun i b h1 h2 _ hb => habs b (mem_tlist.2 ⟨i, h1, h2, hb⟩))
    (fun b hb => by rw [hnone] at hb; cases hb)
  have hfilt : (tlist t).filter (fun b => !o.eq (k, v).1 b.1) = tlist t := by
    rw [List.filter_eq_self]
    intro b hb
    simp [habs b hb]
  rw [hfilt] at hstore
  have hne : ∀ p, 1 ≤ p → p ≤ t.size → t.slots p ≠ 0 → t'.slots p ≠ 0 := by
    intro p _ _ h0
    rw [hsl]
    by_cases hpj : p = j
    · rw [hpj, upd_same]; exact shorthash7_ne0 _
    · rw [upd_ne _ _ hpj]; exact h0
  refine ⟨⟨by rw [hs]; exact hi.size, by rw [hs]; exact hi.sizeLe, ?_, ?_, ?_, ?_, hf1, ?_, hp⟩,
    hstore⟩
  · intro i h1 h2
    rw [hs] at h2
    by_cases hij : i = j
    · subst hij
      refine Or.inr (Or.inr ⟨k, v, by rw [hk, upd_same], by rw [hv, upd_same],
        by rw [hsl, upd_same], ?_⟩)
      exact Chain.mono hpow hmp hs (by rw [hm]; exact Nat.le_refl _) hne hjc
    · refine SlotOK.transfer (hi.slot i h1 h2) (by rw [hsl, upd_ne _ _ hij])
        (by rw [hk, upd_ne _ _ hij]) (by rw [hv, upd_ne _ _ hij]) ?_
      intro k' hc'
      exact Chain.mono hpow hmp hs (by rw [hm]; exact Nat.le_refl _) hne hc'
  · intro i i' a b h1 h2 h1' h2' hne' ha hb
    rw [hs] at h2 h2'
    rw [hent] at ha hb
    by_cases hi1 : i = j
    · rw [ite_eq_left hi1] at ha
      cases ha
      have hi2 : i' ≠ j := fun h => hne' (hi1.trans h.symm)
      rw [ite_eq_right hi2] at hb
      exact habs b (mem_tlist.2 ⟨i', h1', h2', hb⟩)
    · rw [ite_eq_right hi1] at ha
      by_cases hi2 : i' = j
      · rw [ite_eq_left hi2] at hb
        cases hb
        exact eq_false_symm hl (habs a (mem_tlist.2 ⟨i, h1, h2, ha⟩))
      · rw [ite_eq_right hi2] at hb
        exact hi.distinct i i' a b h1 h2 h1' h2' hne' ha hb
  · rw [hc, hstore.length_eq, List.length_cons, hi.count]
  · right
    rw [hm, hs]
    exact hmp
  · intro i h1 h2 hfi
    rw [hs] at h2
    by_cases hij : i = j
    · rw [hij]; exact hf3
    · have : isFilledB (t.slots i) = true := by
        rw [hsl, upd_ne _ _ hij] at hfi; exact hfi
      exact Nat.le_trans hf2 (hi.floorLe i h1 h2 this)

/-! ## The first probe loop -/

/-- The hit test of the first loop of `ht_keyindex2_shorthash!`. -/
def hit1 (t : Table K V) (sh : Nat) (m : K → Bool) (index : Nat) : Bool :=
  if isMissingB (t.slots index) then false
  else if t.slots index == sh then keyMatch t m index else false

/-- The `avail` update of the first loop. -/
def avail1 (t : Table K V) (index : Nat) (avail : Int) : Int :=
  if isMissingB (t.slots index) ∧ avail == 0 then -(index : Int) else avail

theorem keyindex2Loop1_succ (t : Table K V) (sh : Nat) (m : K → Bool) (sz left iter index : Nat)
    (avail : Int) :
    keyindex2Loop1 t sh m sz (left + 1) iter index avail =
      if isEmptyB (t.slots index) then .found (if avail < 0 then avail else -(index : Int))
      else if hit1 t sh m index then .found (index : Int)
      else if iter + 1 > t.maxprobe then .broke (iter + 1) (nextIdx sz index) (avail1 t index avail)
      else keyindex2Loop1 t sh m sz left (iter + 1) (nextIdx sz index) (avail1 t index avail) := rfl

theorem hit1_eq {t : Table K V} {sh : Nat} (hsh : sh ≠ 127) (m : K → Bool) (j : Nat) :
    hit1 t sh m j = hitAt t sh m j := by
  unfold hit1 hitAt isMissingB
  by_cases hb : t.slots j = 127
  · have : (sh == 127) = false := by simp [hsh]
    simp [hb, this]
  · by_cases hs : t.slots j = sh
    · simp [hb, hs, hsh]
    · simp [hb, hs, Ne.symm hs]

/-- Probe positions before `a` are non-empty and miss. -/
def Before (t : Table K V) (sh : Nat) (m : K → Bool) (h a : Nat) : Prop :=
  ∀ e, e < a → t.slots (pr t.size h e) ≠ 0 ∧ hitAt t sh m (pr t.size h e) = false

/-- `avail` is `0` with no deleted slot before `a`, or a deleted slot before `a`. -/
def AvailOK (t : Table K V) (h a : Nat) (avail : Int) : Prop :=
  (avail = 0 ∧ ∀ e, e < a → t.slots (pr t.size h e) ≠ 127) ∨
  (∃ e, e < a ∧ avail = -(pr t.size h e : Int) ∧ t.slots (pr t.size h e) = 127)

theorem keyindex2Loop1_spec (t : Table K V) (sh : Nat) (m : K → Bool) (h : Nat) (hsh : sh ≠ 127)
    (hpow : IsPow t.size) (hh1 : 1 ≤ h) (hh2 : h ≤ t.size) (hmp : t.maxprobe < t.size) :
    ∀ left a avail, a + left = t.maxprobe + 1 → Before t sh m h a → AvailOK t h a avail →
      (∃ d, a ≤ d ∧ d ≤ t.maxprobe ∧ Before t sh m h d ∧ hitAt t sh m (pr t.size h d) = true ∧
        keyindex2Loop1 t sh m t.size left a (pr t.size h a) avail = .found (pr t.size h d : Int)) ∨
      (∃ d av, a ≤ d ∧ d ≤ t.maxprobe ∧ Before t sh m h d ∧ t.slots (pr t.size h d) = 0 ∧
        AvailOK t h d av ∧
        keyindex2Loop1 t sh m t.size left a (pr t.size h a) avail =
          .found (if av < 0 then av else -(pr t.size h d : Int))) ∨
      (Before t sh m h (t.maxprobe + 1) ∧ ∃ av, AvailOK t h (t.maxprobe + 1) av ∧
        keyindex2Loop1 t sh m t.size left a (pr t.size h a) avail =
          .broke (t.maxprobe + 1) (pr t.size h (t.maxprobe + 1)) av)
  | 0, a, avail, hal, hb, hav => by
    have ha : t.maxprobe + 1 = a := by omega
    right; right
    rw [ha]
    exact ⟨hb, avail, hav, rfl⟩
  | left + 1, a, avail, hal, hb, hav => by
    rw [keyindex2Loop1_succ]
    by_cases h0 : t.slots (pr t.size h a) = 0
    · right; left
      refine ⟨a, avail, Nat.le_refl _, by omega, hb, h0, hav, ?_⟩
      rw [ite_eq_left ((isEmptyB_iff _).2 h0)]
    · rw [ite_eq_right (fun he => h0 ((isEmptyB_iff _).1 he)), hit1_eq hsh]
      by_cases hh : hitAt t sh m (pr t.size h a) = true
      · left
        exact ⟨a, Nat.le_refl _, by omega, hb, hh, by rw [ite_eq_left hh]⟩
      · have hh' : hitAt t sh m (pr t.size h a) = false := Bool.eq_false_iff.2 hh
        rw [ite_eq_right hh]
        have hb' : Before t sh m h (a + 1) := by
          intro e he
          by_cases hea : e < a
          · exact hb e hea
          · have : e = a := by omega
            rw [this]
            exact ⟨h0, hh'⟩
        have hra := pr_range hpow hh1 hh2 (show a < t.size by omega)
        have hav' : AvailOK t h (a + 1) (avail1 t (pr t.size h a) avail) := by
          unfold avail1
          by_cases h127 : t.slots (pr t.size h a) = 127
          · rcases hav with ⟨hz, hall⟩ | ⟨e, he, hea, he127⟩
            · rw [ite_eq_left ⟨by simp [isMissingB, h127], by simp [hz]⟩]
              exact Or.inr ⟨a, by omega, rfl, h127⟩
            · have hre := pr_range hpow hh1 hh2 (show e < t.size by omega)
              rw [ite_eq_right (fun hc => by
                have := hc.2
                rw [hea] at this
                simp at this
                omega)]
              exact Or.inr ⟨e, by omega, hea, he127⟩
          · rw [ite_eq_right (fun hc => h127 (by simpa [isMissingB] using hc.1))]
            rcases hav with ⟨hz, hall⟩ | ⟨e, he, hea, he127⟩
            · refine Or.inl ⟨hz, fun e he => ?_⟩
              by_cases hea : e < a
              · exact hall e hea
              · have : e = a := by omega
                rw [this]
                exact h127
            · exact Or.inr ⟨e, by omega, hea, he127⟩
        by_cases hmpa : a + 1 > t.maxprobe
        · rw [ite_eq_left hmpa]
          right; right
          have e1 : t.maxprobe + 1 = a + 1 := by omega
          rw [e1]
          exact ⟨hb', _, hav', rfl⟩
        · rw [ite_eq_right hmpa]
          rcases keyindex2Loop1_spec t sh m h hsh hpow hh1 hh2 hmp left (a + 1) _ (by omega) hb' hav'
            with ⟨d, h2, h3, h4, h5, h6⟩ | ⟨d, av, h2, h3, h4, h5, h6, h7⟩ | h1
          · exact Or.inl ⟨d, by omega, h3, h4, h5, h6⟩
          · exact Or.inr (Or.inl ⟨d, av, by omega, h3, h4, h5, h6, h7⟩)
          · exact Or.inr (Or.inr h1)

/-! ## The second probe loop -/

theorem keyindex2Loop2_spec (t : Table K V) (h M : Nat) :
    ∀ left a, M ≤ a + left →
      (∃ d, a ≤ d ∧ d < M ∧ isFilledB (t.slots (pr t.size h d)) = false ∧
        (∀ e, a ≤ e → e < d → isFilledB (t.slots (pr t.size h e)) = true) ∧
        keyindex2Loop2 t t.size M left a (pr t.size h a) = some (d, pr t.size h d)) ∨
      ((∀ e, a ≤ e → e < M → isFilledB (t.slots (pr t.size h e)) = true) ∧
        keyindex2Loop2 t t.size M left a (pr t.size h a) = none)
  | 0, a, hM => Or.inr ⟨fun e h1 h2 => absurd h2 (by omega), rfl⟩
  | left + 1, a, hM => by
    have e1 : keyindex2Loop2 t t.size M (left + 1) a (pr t.size h a) =
        if a < M then (if ¬ isFilledB (t.slots (pr t.size h a)) then some (a, pr t.size h a)
          else keyindex2Loop2 t t.size M left (a + 1) (pr t.size h (a + 1))) else none := rfl
    rw [e1]
    by_cases haM : a < M
    · rw [ite_eq_left haM]
      cases hf : isFilledB (t.slots (pr t.size h a))
      · left
        refine ⟨a, Nat.le_refl _, haM, hf, fun e h1 h2 => absurd h2 (by omega), ?_⟩
        rw [ite_eq_left (by simp)]
      · rw [ite_eq_right (by simp)]
        rcases keyindex2Loop2_spec t h M left (a + 1) (by omega) with
          ⟨d, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
        · refine Or.inl ⟨d, by omega, h2, h3, fun e he1 he2 => ?_, h5⟩
          by_cases hea : e = a
          · rw [hea]; exact hf
          · exact h4 e (by omega) he2
        · refine Or.inr ⟨fun e he1 he2 => ?_, h2⟩
          by_cases hea : e = a
          · rw [hea]; exact hf
          · exact h1 e (by omega) he2
    · rw [ite_eq_right haM]
      exact Or.inr ⟨fun e h1 h2 => absurd h2 (by omega), rfl⟩

/-! ## Counting a window of filled slots -/

theorem length_filterMap_ent_eq {o : KeyOps K} {t : Table K V} (hi : Inv o t) :
    ∀ l : List Nat, (∀ p ∈ l, 1 ≤ p ∧ p ≤ t.size) →
      (l.filterMap (ent t)).length = (l.filter (fun p => isFilledB (t.slots p))).length
  | [], _ => rfl
  | p :: l, hl => by
    have hp := hl p List.mem_cons_self
    have ih := length_filterMap_ent_eq hi l (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    cases hf : isFilledB (t.slots p)
    · rw [List.filterMap_cons_none (ent_of_not_filled hf), List.filter_cons_of_neg (by simp [hf]), ih]
    · obtain ⟨k, v, -, -, he, -, -⟩ := hi.filled hp.1 hp.2 hf
      rw [List.filterMap_cons_some he, List.filter_cons_of_pos (p := fun x => isFilledB (t.slots x)) hf,
        List.length_cons,
        List.length_cons, ih]

theorem count_ge_window {o : KeyOps K} {t : Table K V} (hi : Inv o t) (hpow : IsPow t.size)
    {h M : Nat} (h1 : 1 ≤ h) (h2 : h ≤ t.size) (hM : M ≤ t.size)
    (hall : ∀ e, e < M → isFilledB (t.slots (pr t.size h e)) = true) : M ≤ t.count := by
  let L := (List.range M).map (pr t.size h)
  have hnd : L.Nodup := by
    show List.Pairwise (fun a b => a ≠ b) ((List.range M).map (pr t.size h))
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun hx hy hxy heq => hxy ?_) List.nodup_range
    rw [List.mem_range] at hx hy
    exact pr_inj hpow h1 h2 (by omega) (by omega) heq
  have hsub : L ⊆ (List.range' 1 t.size).filter (fun p => isFilledB (t.slots p)) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_range] at he
    have hr := pr_range hpow h1 h2 (show e < t.size by omega)
    rw [List.mem_filter, List.mem_range'_1]
    exact ⟨⟨hr.1, by omega⟩, hall e he⟩
  have hle := hnd.length_le_of_subset hsub
  have hlen : L.length = M := by simp [L]
  rw [hi.count]
  unfold tlist
  rw [length_filterMap_ent_eq hi _ (fun p hp => by rw [List.mem_range'_1] at hp; omega)]
  omega

theorem pow_le_window {sz : Nat} (h : IsPow sz) : sz ≤ 64 * max 16 (sz >>> 6) := by
  obtain ⟨p, hp, rfl⟩ := h
  rw [Nat.shiftRight_eq_div_pow]
  by_cases hp6 : 6 ≤ p
  · have e : 2 ^ p = 2 ^ 6 * 2 ^ (p - 6) := by rw [← Nat.pow_add]; congr 1; omega
    have : 2 ^ p / 2 ^ 6 = 2 ^ (p - 6) := by
      rw [e, Nat.mul_div_cancel_left _ (Nat.two_pow_pos 6)]
    rw [this]
    have : 2 ^ (p - 6) ≤ max 16 (2 ^ (p - 6)) := Nat.le_max_right _ _
    have h64 : (2 : Nat) ^ 6 = 64 := rfl
    omega
  · have : 2 ^ p ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
    have : 16 ≤ max 16 (2 ^ p / 2 ^ 6) := Nat.le_max_left _ _
    have h32 : (2 : Nat) ^ 5 = 32 := rfl
    omega

/-! ## `ht_keyindex2_shorthash!` -/

/-- The part of `ht_keyindex2_shorthash!` after the first loop, for a non-empty size. -/
def k2tail (o : KeyOps K) (fuel : Nat) (t : Table K V) (hq : JInt .u64) (m : K → Bool) :
    Probe1 → DR (Int × Nat × Table K V)
  | .found i => pure (i, shorthash7 hq, t)
  | .broke iter index avail =>
    if avail < 0 then pure (avail, shorthash7 hq, t) else
    match keyindex2Loop2 t t.size (max 16 (t.size >>> 6)) (max 16 (t.size >>> 6)) iter index with
    | some (iter, index) => pure (-(index : Int), shorthash7 hq, { t with maxprobe := iter })
    | none =>
      match fuel with
      | 0 => throw .diverges
      | fuel + 1 => rehash o t (if t.count > 64000 then t.size * 2 else t.size * 4) >>= fun t =>
          htKeyindex2 o fuel t hq m

theorem htKeyindex2_eq (o : KeyOps K) (fuel : Nat) (t : Table K V) (hq : JInt .u64) (m : K → Bool) :
    htKeyindex2 o fuel t hq m =
      if (t.size == 0) = true then
        (rehash o t 4 >>= fun t1 => pure (-((hashindex hq t1.size).1 : Int), shorthash7 hq, t1))
      else k2tail o fuel t hq m
        (keyindex2Loop1 t (shorthash7 hq) m t.size (t.maxprobe + 1) 0 (hashindex hq t.size).1 0) := by
  cases fuel <;> (rw [htKeyindex2] <;> rfl)

/-- Result of the insertion probe for key `q`. -/
structure K2Out (o : KeyOps K) (t : Table K V) (q : K) (idx : Int) (t' : Table K V) (n : Nat) :
    Prop where
  inv : Inv o t'
  perm : List.Perm (tlist t') (tlist t)
  count : t'.count = t.count
  age : AgeStep t t' n
  found : ∀ i e, 1 ≤ i → i ≤ t.size → ent t i = some e → o.eq q e.1 = true → idx = i ∧ t' = t
  absent : Absent o t q → idx < 0 ∧ InsertSlot o t' q (-idx).toNat

theorem Inv.maxprobe_up {o : KeyOps K} {t : Table K V} (hi : Inv o t) (hpow : IsPow t.size)
    {mp : Nat} (h1 : t.maxprobe ≤ mp) (h2 : mp < t.size) : Inv o { t with maxprobe := mp } := by
  have hmp : t.maxprobe < t.size := by omega
  refine ⟨hi.size, hi.sizeLe, fun i h1' h2' => ?_, hi.distinct, hi.count, Or.inr h2, hi.idxfloor,
    hi.floorLe, hi.popcursor⟩
  exact SlotOK.transfer (hi.slot i h1' h2') rfl rfl rfl
    (fun k hc => Chain.mono (t := t) hpow hmp rfl h1 (fun _ _ _ h => h) hc)

/-- A present key is hit before any empty slot of its probe sequence. -/
theorem present_hit {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t)
    (hpow : IsPow t.size) {q : K} {i : Nat} {e : K × V} (h1 : 1 ≤ i) (h2 : i ≤ t.size)
    (he : ent t i = some e) (hq : o.eq q e.1 = true) :
    ∃ d, d ≤ t.maxprobe ∧ i = pr t.size (home o t.size q) d ∧
      (∀ e', e' < d → t.slots (pr t.size (home o t.size q) e') ≠ 0) ∧
      hitAt t (shorthash7 (o.hash q)) (o.eq q) i = true := by
  obtain ⟨k, v, hk, -, hek, hs, d, hd, hid, hall⟩ := hi.filled h1 h2 (ent_some he).1
  rw [he] at hek
  cases hek
  have hh : home o t.size q = home o t.size k := home_eq_of_eq hl hq t.size
  refine ⟨d, hd, by rw [hh]; exact hid, by rw [hh]; exact hall, hitAt_of ?_ hk hq⟩
  rw [hs, hl.hash_eq q k hq]

/-- A key missed by every probe before an empty slot, or before `maxprobe`, is absent. -/
theorem absent_of_before {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t)
    (hpow : IsPow t.size) {q : K} {d : Nat}
    (hb : Before t (shorthash7 (o.hash q)) (o.eq q) (home o t.size q) d)
    (hend : t.slots (pr t.size (home o t.size q) d) = 0 ∨ t.maxprobe < d) : Absent o t q := by
  intro e he
  cases hq : o.eq q e.1
  · rfl
  · exfalso
    obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 he
    obtain ⟨d', hd', hid', hall', hhit'⟩ := present_hit hl hi hpow h1 h2 hei hq
    rcases Nat.lt_trichotomy d' d with hlt | heq | hgt
    · have := (hb d' hlt).2
      rw [← hid', hhit'] at this
      cases this
    · rcases hend with h0 | hlt
      · have hf := (ent_some hei).1
        rw [hid', heq, h0, isFilledB_zero] at hf
        cases hf
      · omega
    · rcases hend with h0 | hlt
      · exact hall' d hgt h0
      · omega

theorem k2tail_found {o : KeyOps K} {fuel : Nat} {t : Table K V} {hq : JInt .u64} {m : K → Bool}
    (i : Int) : k2tail o fuel t hq m (.found i) = .ok (i, shorthash7 hq, t) := rfl

theorem k2tail_neg {o : KeyOps K} {fuel : Nat} {t : Table K V} {hq : JInt .u64} {m : K → Bool}
    {iter index : Nat} {avail : Int} (h : avail < 0) :
    k2tail o fuel t hq m (.broke iter index avail) = .ok (avail, shorthash7 hq, t) := by
  cases fuel <;> (rw [k2tail, ite_eq_left h] <;> rfl)

theorem k2tail_some {o : KeyOps K} {fuel : Nat} {t : Table K V} {hq : JInt .u64} {m : K → Bool}
    {iter index d j : Nat} {avail : Int} (h : ¬ avail < 0)
    (h2 : keyindex2Loop2 t t.size (max 16 (t.size >>> 6)) (max 16 (t.size >>> 6)) iter index =
      some (d, j)) :
    k2tail o fuel t hq m (.broke iter index avail) =
      .ok (-(j : Int), shorthash7 hq, { t with maxprobe := d }) := by
  cases fuel <;> (rw [k2tail, ite_eq_right h, h2] <;> rfl)

theorem k2tail_none_succ {o : KeyOps K} {f : Nat} {t : Table K V} {hq : JInt .u64} {m : K → Bool}
    {iter index : Nat} {avail : Int} (h : ¬ avail < 0)
    (h2 : keyindex2Loop2 t t.size (max 16 (t.size >>> 6)) (max 16 (t.size >>> 6)) iter index =
      none) :
    k2tail o (f + 1) t hq m (.broke iter index avail) =
      (rehash o t (if t.count > 64000 then t.size * 2 else t.size * 4) >>= fun t =>
        htKeyindex2 o f t hq m) := by
  rw [k2tail, ite_eq_right h, h2] <;> rfl

/-- One unfolding of `ht_keyindex2_shorthash!`, given the result for smaller fuel. -/
theorem htKeyindex2_main {o : KeyOps K} (hl : o.Lawful) (q : K) (fuel : Nat)
    (IH : ∀ f, fuel = f + 1 → ∀ t : Table K V, Inv o t → t.count < 2 ^ 33 →
      (t.size = 0 ∨ 64 * t.count < t.size * 2 ^ f) →
      ∃ idx t' n, htKeyindex2 o f t (o.hash q) (o.eq q) = .ok (idx, shorthash7 (o.hash q), t') ∧
        n ≤ 2 * f + 2 ∧ K2Out o t q idx t' n)
    (t : Table K V) (hi : Inv o t) (hc : t.count < 2 ^ 33)
    (hf : t.size = 0 ∨ 64 * t.count < t.size * 2 ^ fuel) :
    ∃ idx t' n, htKeyindex2 o fuel t (o.hash q) (o.eq q) = .ok (idx, shorthash7 (o.hash q), t') ∧
      n ≤ 2 * fuel + 2 ∧ K2Out o t q idx t' n := by
  rw [htKeyindex2_eq]
  by_cases hs0 : t.size = 0
  · -- an empty table gets 16 slots
    have hc0 : t.count = 0 := by have := hi.count_le_size; omega
    rw [ite_eq_left (by simp [hs0])]
    obtain ⟨t1, h1, hi1, hp1, hs1, hc1, ha1⟩ :=
      rehash_spec hi 4 (by have := (tableszNat_pow 4).ge; omega)
        (by have := tableszNat_le 4; omega)
    rw [bind_of_ok h1]
    have hpow1 : IsPow t1.size := by rw [hs1]; exact tableszNat_pow 4
    have hhr := home_range hpow1 q (o := o)
    have hnil : tlist t = [] := List.length_eq_zero_iff.1 (by rw [← hi.count]; exact hc0)
    have hnil1 : tlist t1 = [] := List.length_eq_zero_iff.1 (by simp [hp1.length_eq, hnil])
    refine ⟨-((home o t1.size q : Nat) : Int), t1, 1, rfl, by omega,
      ⟨hi1, hp1, hc1, AgeStep.of_pos (by rw [ha1, ite_eq_left hc0, bump_eq]) (by omega),
       fun i e h1 h2 _ _ => absurd h2 (by omega), fun _ => ⟨by omega, ?_⟩⟩⟩
    rw [show (-(-((home o t1.size q : Nat) : Int))).toNat = home o t1.size q by omega]
    refine ⟨hhr.1, hhr.2, ?_, 0, Nat.zero_le _, rfl, fun e he => absurd he (by omega)⟩
    cases hfill : isFilledB (t1.slots (home o t1.size q))
    · rfl
    · obtain ⟨k, v, -, -, he, -, -⟩ := hi1.filled hhr.1 hhr.2 hfill
      have hm : (k, v) ∈ tlist t1 := mem_tlist.2 ⟨_, hhr.1, hhr.2, he⟩
      rw [hnil1] at hm
      cases hm
  · have hpow : IsPow t.size := by
      rcases hi.size with h | h
      · exact absurd h hs0
      · exact h
    have hmp : t.maxprobe < t.size := by
      rcases hi.maxprobe with h | h
      · exact absurd h hs0
      · exact h
    rw [ite_eq_right (by simp [hs0])]
    have hhr := home_range hpow q (o := o)
    have hsh : shorthash7 (o.hash q) ≠ 127 := shorthash7_ne127 _
    rcases keyindex2Loop1_spec t (shorthash7 (o.hash q)) (o.eq q) (home o t.size q) hsh hpow
        hhr.1 hhr.2 hmp (t.maxprobe + 1) 0 0 (by omega) (fun e he => absurd he (by omega))
        (Or.inl ⟨rfl, fun e he => absurd he (by omega)⟩)
      with ⟨d, -, hd, hbd, hhit, hres⟩ | ⟨d, av, -, hd, hbd, hd0, hav, hres⟩ | ⟨hbm, av, hav, hres⟩
    · -- the key is present
      have hres' : keyindex2Loop1 t (shorthash7 (o.hash q)) (o.eq q) t.size (t.maxprobe + 1) 0
          (hashindex (o.hash q) t.size).1 0 = .found (pr t.size (home o t.size q) d : Int) := hres
      rw [hres', k2tail_found]
      obtain ⟨hs', k', hk', hm'⟩ := hitAt_true hhit
      have hdr := pr_range hpow hhr.1 hhr.2 (show d < t.size by omega)
      have hfill : isFilledB (t.slots (pr t.size (home o t.size q) d)) = true := by
        rw [hs']; exact shorthash7_filled _
      obtain ⟨k2, v2, hk2, -, he2, -, -⟩ := hi.filled hdr.1 hdr.2 hfill
      rw [hk'] at hk2
      cases hk2
      refine ⟨_, t, 0, rfl, by omega, hi, List.Perm.refl _, rfl, AgeStep.refl t, ?_, ?_⟩
      · intro i e h1 h2 he hq
        refine ⟨?_, rfl⟩
        by_cases hi' : pr t.size (home o t.size q) d = i
        · rw [hi']
        · exfalso
          have := hi.distinct _ i _ _ hdr.1 hdr.2 h1 h2 hi' he2 he
          dsimp only at this
          rw [eq_trans' hl hm' hq] at this
          cases this
      · intro habs
        exfalso
        have := habs _ (mem_tlist.2 ⟨_, hdr.1, hdr.2, he2⟩)
        dsimp only at this
        rw [hm'] at this
        cases this
    · -- an empty slot ends the probe: the key is absent
      have hres' : keyindex2Loop1 t (shorthash7 (o.hash q)) (o.eq q) t.size (t.maxprobe + 1) 0
          (hashindex (o.hash q) t.size).1 0 =
            .found (if av < 0 then av else -(pr t.size (home o t.size q) d : Int)) := hres
      rw [hres', k2tail_found]
      have habs : Absent o t q := absent_of_before hl hi hpow hbd (Or.inl hd0)
      refine ⟨_, t, 0, rfl, by omega, hi, List.Perm.refl _, rfl, AgeStep.refl t,
        fun i e h1 h2 he hq => ?_, fun _ => ?_⟩
      · have := habs e (mem_tlist.2 ⟨i, h1, h2, he⟩)
        rw [hq] at this
        cases this
      · by_cases hav0 : av < 0
        · rw [ite_eq_left hav0]
          rcases hav with ⟨hz, -⟩ | ⟨e, he, hea, he127⟩
          · omega
          · have hre := pr_range hpow hhr.1 hhr.2 (show e < t.size by omega)
            refine ⟨hav0, ?_⟩
            rw [hea, show (-(-((pr t.size (home o t.size q) e : Nat) : Int))).toNat =
              pr t.size (home o t.size q) e by omega]
            exact ⟨hre.1, hre.2, by rw [he127]; exact isFilledB_127, e, by omega, rfl,
              fun e' he' => (hbd e' (by omega)).1⟩
        · rw [ite_eq_right hav0]
          have hdr := pr_range hpow hhr.1 hhr.2 (show d < t.size by omega)
          refine ⟨by omega, ?_⟩
          rw [show (-(-((pr t.size (home o t.size q) d : Nat) : Int))).toNat =
            pr t.size (home o t.size q) d by omega]
          exact ⟨hdr.1, hdr.2, by rw [hd0]; exact isFilledB_zero, d, hd, rfl,
            fun e' he' => (hbd e' he').1⟩
    · -- no hit and no empty slot within maxprobe: the key is absent
      have hres' : keyindex2Loop1 t (shorthash7 (o.hash q)) (o.eq q) t.size (t.maxprobe + 1) 0
          (hashindex (o.hash q) t.size).1 0 =
            .broke (t.maxprobe + 1) (pr t.size (home o t.size q) (t.maxprobe + 1)) av := hres
      rw [hres']
      have habs : Absent o t q := absent_of_before hl hi hpow hbm (Or.inr (by omega))
      have hnf : ∀ i e, 1 ≤ i → i ≤ t.size → ent t i = some e → o.eq q e.1 = true → False := by
        intro i e h1 h2 he hq
        have := habs e (mem_tlist.2 ⟨i, h1, h2, he⟩)
        rw [hq] at this
        cases this
      by_cases hav0 : av < 0
      · rw [k2tail_neg hav0]
        refine ⟨av, t, 0, rfl, by omega, hi, List.Perm.refl _, rfl, AgeStep.refl t,
          fun i e h1 h2 he hq => (hnf i e h1 h2 he hq).elim, fun _ => ⟨hav0, ?_⟩⟩
        rcases hav with ⟨hz, -⟩ | ⟨e, he, hea, he127⟩
        · omega
        · have hre := pr_range hpow hhr.1 hhr.2 (show e < t.size by omega)
          rw [hea, show (-(-((pr t.size (home o t.size q) e : Nat) : Int))).toNat =
            pr t.size (home o t.size q) e by omega]
          exact ⟨hre.1, hre.2, by rw [he127]; exact isFilledB_127, e, by omega, rfl,
            fun e' he' => (hbm e' (by omega)).1⟩
      · -- every probe within maxprobe is filled
        have hfilled : ∀ e, e ≤ t.maxprobe → isFilledB (t.slots (pr t.size (home o t.size q) e)) = true := by
          intro e he
          have hre := pr_range hpow hhr.1 hhr.2 (show e < t.size by omega)
          rcases hi.byte hre.1 hre.2 with h | h | h
          · exact absurd h (hbm e (by omega)).1
          · rcases hav with ⟨-, hall⟩ | ⟨e', he', hea, -⟩
            · exact absurd h (hall e (by omega))
            · have hre' := pr_range hpow hhr.1 hhr.2 (show e' < t.size by omega)
              omega
          · exact h
        have h16 := hpow.ge
        have hM : max 16 (t.size >>> 6) ≤ t.size := by
          rw [Nat.shiftRight_eq_div_pow]
          have : t.size / 2 ^ 6 ≤ t.size := Nat.div_le_self _ _
          omega
        rcases keyindex2Loop2_spec t (home o t.size q) (max 16 (t.size >>> 6)) (max 16 (t.size >>> 6))
            (t.maxprobe + 1) (by omega) with ⟨d, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
        · -- a free slot beyond maxprobe
          rw [k2tail_some hav0 h5]
          have hdr := pr_range hpow hhr.1 hhr.2 (show d < t.size by omega)
          refine ⟨_, { t with maxprobe := d }, 0, rfl, by omega,
            ⟨hi.maxprobe_up hpow (by omega) (by omega), List.Perm.refl _, rfl,
             ⟨(ageAdd_zero _).symm, fun _ => ⟨rfl, rfl, rfl, by show t.maxprobe ≤ d; omega⟩⟩,
             fun i e h1 h2 he hq => (hnf i e h1 h2 he hq).elim, fun _ => ⟨by omega, ?_⟩⟩⟩
          rw [show (-(-((pr t.size (home o t.size q) d : Nat) : Int))).toNat =
            pr t.size (home o t.size q) d by omega]
          refine ⟨hdr.1, hdr.2, h3, d, Nat.le_refl _, rfl, fun e he => ?_⟩
          show t.slots (pr t.size (home o t.size q) e) ≠ 0
          by_cases hem : e ≤ t.maxprobe
          · exact filled_ne_zero (hfilled e hem)
          · exact filled_ne_zero (h4 e (by omega) he)
        · -- the window is full: rehash and probe again
          have hall : ∀ e, e < max 16 (t.size >>> 6) →
              isFilledB (t.slots (pr t.size (home o t.size q) e)) = true := by
            intro e he
            by_cases hem : e ≤ t.maxprobe
            · exact hfilled e hem
            · exact h1 e (by omega) he
          have hcM := count_ge_window hi hpow hhr.1 hhr.2 hM hall
          have hwin := pow_le_window hpow
          cases fuel with
          | zero =>
            exfalso
            rcases hf with h | h
            · exact hs0 h
            · rw [Nat.pow_zero, Nat.mul_one] at h
              omega
          | succ f =>
            rw [k2tail_none_succ hav0 h2]
            have hc0 : t.count ≠ 0 := by omega
            have hpow0 : IsPow (if t.count > 64000 then t.size * 2 else t.size * 4) := by
              split
              · exact hpow.double
              · exact hpow.quad
            have htab := tableszNat_of_pow hpow0
            have hge : 2 * t.size ≤ (if t.count > 64000 then t.size * 2 else t.size * 4) := by
              split <;> omega
            have hle4 : (if t.count > 64000 then t.size * 2 else t.size * 4) ≤ 4 * t.size := by
              split <;> omega
            have hcs := hi.count_le_size
            obtain ⟨t1, h1', hi1, hp1, hs1, hc1, ha1⟩ := rehash_spec hi
              (if t.count > 64000 then t.size * 2 else t.size * 4) (by rw [htab]; omega)
              (by rw [htab]; omega)
            rw [bind_of_ok h1']
            have hf1 : t1.size = 0 ∨ 64 * t1.count < t1.size * 2 ^ f := by
              right
              rcases hf with h | h
              · exact absurd h hs0
              · have e1 : t.size * 2 ^ (f + 1) = 2 * t.size * 2 ^ f := by
                  rw [Nat.pow_succ, Nat.mul_comm (2 ^ f) 2, ← Nat.mul_assoc, Nat.mul_comm t.size 2]
                have e2 : 2 * t.size * 2 ^ f ≤ t1.size * 2 ^ f :=
                  Nat.mul_le_mul_right _ (by rw [hs1, htab]; exact hge)
                rw [hc1]
                omega
            obtain ⟨idx, t2, n1, h2', hn1, hout⟩ := IH f rfl t1 hi1 (by rw [hc1]; exact hc) hf1
            refine ⟨idx, t2, 2 + n1, h2', by omega, ⟨hout.inv, hout.perm.trans hp1,
              hout.count.trans hc1, ?_, fun i e h1 h2 he hq => (hnf i e h1 h2 he hq).elim,
              fun _ => hout.absent (fun e he => habs e (hp1.mem_iff.1 he))⟩⟩
            exact (AgeStep.of_pos (by rw [ha1, ite_eq_right hc0, bump_bump]) (by omega)).trans
              hout.age

theorem htKeyindex2_spec {o : KeyOps K} (hl : o.Lawful) (q : K) :
    ∀ fuel (t : Table K V), Inv o t → t.count < 2 ^ 33 →
      (t.size = 0 ∨ 64 * t.count < t.size * 2 ^ fuel) →
      ∃ idx t' n, htKeyindex2 o fuel t (o.hash q) (o.eq q) = .ok (idx, shorthash7 (o.hash q), t') ∧
        n ≤ 2 * fuel + 2 ∧ K2Out o t q idx t' n := by
  intro fuel
  induction fuel with
  | zero => exact htKeyindex2_main hl q 0 (fun f h => absurd h (by omega))
  | succ f ih =>
    exact htKeyindex2_main hl q (f + 1) (fun f' h => by
      have : f' = f := by omega
      subst this
      exact ih)

theorem keyindex2_spec {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t)
    (hc : t.count < 2 ^ 33) (q : K) :
    ∃ idx t' n, keyindex2 o t (o.hash q) (o.eq q) = .ok (idx, shorthash7 (o.hash q), t') ∧
      n ≤ 2 * t.count + 18 ∧ K2Out o t q idx t' n := by
  have hf : t.size = 0 ∨ 64 * t.count < t.size * 2 ^ (t.count + 8) := by
    rcases hi.size with h | h
    · exact Or.inl h
    · right
      have h16 := h.ge
      have h1 : t.count < 2 ^ t.count := Nat.lt_two_pow_self
      have h2 : 2 ^ (t.count + 8) = 2 ^ t.count * 2 ^ 8 := Nat.pow_add 2 t.count 8
      have h3 : 16 * 2 ^ (t.count + 8) ≤ t.size * 2 ^ (t.count + 8) := Nat.mul_le_mul_right _ h16
      omega
  obtain ⟨idx, t', n, h1, h2, h3⟩ := htKeyindex2_spec hl q (t.count + 8) t hi hc hf
  exact ⟨idx, t', n, h1, by omega, h3⟩

end JuliaLean.Dicts
