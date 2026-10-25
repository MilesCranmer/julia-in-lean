import JuliaLean.Dicts.ProofSet

/-!
# `_delete!`, `delete!`, `pop!(d, k)` and `pop!(d, k, default)`

`_delete!` empties the slot when the next slot is empty, together with the
run of deleted slots before it (which may wrap from index 1 to `size`), and
otherwise leaves a `0x7f` tombstone. A key whose probe chain crossed a cleared
slot would have had to cross the empty slot after the run, so every chain of a
remaining key survives.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-! ## Walking backwards -/

/-- `r` backward steps from `i`. -/
def bk (sz i : Nat) : Nat → Nat
  | 0 => i
  | r + 1 => prevIdx sz (bk sz i r)

theorem bk_range {sz i : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i) (h2 : i ≤ sz) :
    ∀ r, 1 ≤ bk sz i r ∧ bk sz i r ≤ sz
  | 0 => ⟨h1, h2⟩
  | r + 1 => by
    have ih := bk_range h hs h1 h2 r
    exact (nextIdx_prevIdx h hs ih.1 ih.2).2

theorem next_bk {sz i : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i) (h2 : i ≤ sz)
    (r : Nat) : nextIdx sz (bk sz i (r + 1)) = bk sz i r := by
  have ih := bk_range h hs h1 h2 r
  exact (nextIdx_prevIdx h hs ih.1 ih.2).1

/-- Slots after emptying `bk 0, ..., bk (r-1)`. -/
def clr (sz i : Nat) (S : Nat → Nat) : Nat → Nat → Nat
  | 0 => S
  | r + 1 => upd (clr sz i S r) (bk sz i r) 0

theorem clr_spec (sz i : Nat) (S : Nat → Nat) : ∀ r p,
    (clr sz i S r p = S p ∧ ∀ s, s < r → p ≠ bk sz i s) ∨
      (clr sz i S r p = 0 ∧ ∃ s, s < r ∧ p = bk sz i s)
  | 0, _ => Or.inl ⟨rfl, fun s hs => absurd hs (by omega)⟩
  | r + 1, p => by
    have e : clr sz i S (r + 1) p = upd (clr sz i S r) (bk sz i r) 0 p := rfl
    rw [e]
    by_cases hp : p = bk sz i r
    · exact Or.inr ⟨by rw [hp, upd_same], r, by omega, hp⟩
    · rw [upd_ne _ _ hp]
      rcases clr_spec sz i S r p with ⟨h1, h2⟩ | ⟨h1, s, hs, h2⟩
      · refine Or.inl ⟨h1, fun s hs => ?_⟩
        by_cases hsr : s = r
        · rw [hsr]; exact hp
        · exact h2 s (by omega)
      · exact Or.inr ⟨h1, s, by omega, h2⟩

/-- The tombstone-clearing loop empties `bk 0, ..., bk (R-1)` for some `R ≥ 1`,
all of which except `bk 0` held `0x7f`. -/
theorem deleteBack_spec {sz i : Nat} (S : Nat → Nat) :
    ∀ left r (ndel : Int), 1 ≤ r + left → (∀ s, 1 ≤ s → s ≤ r → S (bk sz i s) = 127) →
      ∃ R nd, 1 ≤ R ∧ (∀ s, 1 ≤ s → s < R → S (bk sz i s) = 127) ∧
        deleteBack sz left (clr sz i S r) (bk sz i r) ndel = (clr sz i S R, nd)
  | 0, r, ndel, hr, hS => ⟨r, ndel, by omega, fun s hs1 hs2 => hS s hs1 (by omega), rfl⟩
  | left + 1, r, ndel, _, hS => by
    have e : deleteBack sz (left + 1) (clr sz i S r) (bk sz i r) ndel =
        if isMissingB (clr sz i S (r + 1) (bk sz i (r + 1))) then
          deleteBack sz left (clr sz i S (r + 1)) (bk sz i (r + 1)) (ndel - 1)
        else (clr sz i S (r + 1), ndel - 1) := rfl
    rw [e]
    by_cases hm : isMissingB (clr sz i S (r + 1) (bk sz i (r + 1))) = true
    · rw [if_pos hm]
      have h127 : clr sz i S (r + 1) (bk sz i (r + 1)) = 127 := by
        unfold isMissingB at hm
        simpa using hm
      have hS' : S (bk sz i (r + 1)) = 127 := by
        rcases clr_spec sz i S (r + 1) (bk sz i (r + 1)) with ⟨ha, -⟩ | ⟨ha, -⟩
        · rw [← ha]; exact h127
        · rw [ha] at h127; cases h127
      exact deleteBack_spec S left (r + 1) (ndel - 1) (by omega) (fun s hs1 hs2 => by
        by_cases hsr : s = r + 1
        · rw [hsr]; exact hS'
        · exact hS s hs1 (by omega))
    · rw [if_neg hm]
      exact ⟨r + 1, ndel - 1, by omega, fun s hs1 hs2 => hS s hs1 (by omega), rfl⟩

/-! ## `_delete!` -/

/-- `_delete!` with the computed slot bytes and tombstone count `D`. -/
def delT (t : Table K V) (i : Nat) (D : (Nat → Nat) × Int) : Table K V :=
  { t with keys := upd t.keys i none, vals := upd t.vals i none, slots := D.1,
           ndel := ((t.ndel : Int) + D.2).toNat, count := t.count - 1, age := bump t.age }

/-- The slot bytes and tombstone change computed by `_delete!`. -/
def delD (t : Table K V) (i : Nat) : (Nat → Nat) × Int :=
  if isEmptyB (t.slots (nextIdx t.size i)) then deleteBack t.size (t.size + 1) t.slots i 1
  else (upd t.slots i 127, 1)

theorem deleteAt_eq (t : Table K V) (i : Nat) : deleteAt t i = delT t i (delD t i) := by
  simp only [deleteAt, delD]
  generalize (if isEmptyB (t.slots (nextIdx t.size i)) = true then
    deleteBack t.size (t.size + 1) t.slots i 1 else (upd t.slots i 127, 1)) = D
  cases D
  rfl

theorem ent_congr {t t' : Table K V} {p : Nat} (hs : t'.slots p = t.slots p)
    (hk : t'.keys p = t.keys p) (hv : t'.vals p = t.vals p) : ent t' p = ent t p := by
  unfold ent
  rw [hs, hk, hv]

/-- Clearing the entry at `i` with new slot bytes that keep every remaining chain. -/
theorem Inv.clear {o : KeyOps K} (hl : o.Lawful) {t t' : Table K V} (hi : Inv o t) {i : Nat}
    (h1 : 1 ≤ i) (h2 : i ≤ t.size) {e : K × V} (he : ent t i = some e)
    (hs : t'.size = t.size) (hk : t'.keys = upd t.keys i none) (hv : t'.vals = upd t.vals i none)
    (hc : t'.count = t.count - 1) (hm : t'.maxprobe = t.maxprobe) (hf : t'.idxfloor = t.idxfloor)
    (hp : t'.popcursor = t.popcursor)
    (hA : t'.slots i = 0 ∨ t'.slots i = 127)
    (hB : ∀ p, p ≠ i → t'.slots p = t.slots p ∨ (t.slots p = 127 ∧ t'.slots p = 0))
    (hC : ∀ q hh d, isFilledB (t.slots q) = true → q ≠ i → q = pr t.size hh d → d < t.size →
      1 ≤ hh → hh ≤ t.size → (∀ e, e < d → t.slots (pr t.size hh e) ≠ 0) →
      ∀ e, e < d → t'.slots (pr t.size hh e) ≠ 0) :
    Inv o t' ∧ tlist t' = (tlist t).filter (fun b => !o.eq e.1 b.1) := by
  have hnfi : isFilledB (t'.slots i) = false := by
    rcases hA with h | h <;> rw [h] <;> decide
  have hent : ∀ p, ent t' p = if p = i then none else ent t p := by
    intro p
    by_cases hpi : p = i
    · rw [if_pos hpi, hpi]
      exact ent_of_not_filled hnfi
    · rw [if_neg hpi]
      rcases hB p hpi with h | ⟨h127, h0⟩
      · exact ent_congr h (by rw [hk, upd_ne _ _ hpi]) (by rw [hv, upd_ne _ _ hpi])
      · rw [ent_of_not_filled (by rw [h0]; decide), ent_of_not_filled (by rw [h127]; decide)]
  have hdis : ∀ p b, 1 ≤ p → p ≤ t.size → p ≠ i → ent t p = some b → o.eq e.1 b.1 = false :=
    fun p b hp1 hp2 hpi hb => hi.distinct i p e b h1 h2 hp1 hp2 (Ne.symm hpi) he hb
  have hsame : ∀ b, ent t i = some b → o.eq e.1 b.1 = true := by
    intro b hb
    rw [he] at hb
    cases hb
    exact hl.refl _
  have htl : tlist t' = (tlist t).filter (fun b => !o.eq e.1 b.1) :=
    tlist_clear hs (fun p _ _ => hent p) hdis hsame
  have hself := tlist_store (o := o) (t := t) (t' := t) (e := e) rfl h1 h2
    (fun p _ _ => by
      by_cases hp : p = i
      · rw [if_pos hp, hp, he]
      · rw [if_neg hp]) hdis hsame
  have hlen : (tlist t).length = (tlist t').length + 1 := by
    rw [htl, hself.length_eq, List.length_cons]
  have hpow : IsPow t.size := by
    rcases hi.size with h | h
    · omega
    · exact h
  have hmp : t.maxprobe < t.size := by
    rcases hi.maxprobe with h | h
    · omega
    · exact h
  refine ⟨⟨by rw [hs]; exact hi.size, by rw [hs]; exact hi.sizeLe, fun p hp1 hp2 => ?_, ?_, ?_,
    by rw [hm, hs]; exact hi.maxprobe, by rw [hf]; exact hi.idxfloor, fun p hp1 hp2 hfp => ?_,
    by rw [hp]; exact hi.popcursor⟩, htl⟩
  · rw [hs] at hp2
    by_cases hpi : p = i
    · rw [hpi]
      rcases hA with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hi.slot p hp1 hp2 with h0 | h127 | ⟨k, v, hkp, hvp, hsp, d, hd, hid, hall⟩
      · left
        rcases hB p hpi with h | ⟨h, -⟩
        · rw [h, h0]
        · rw [h0] at h; exact absurd h (by decide)
      · rcases hB p hpi with h | ⟨-, h⟩
        · exact Or.inr (Or.inl (by rw [h, h127]))
        · exact Or.inl h
      · have hsp' : t'.slots p = t.slots p := by
          rcases hB p hpi with h | ⟨h, -⟩
          · exact h
          · rw [hsp] at h; exact absurd h (shorthash7_ne127 _)
        have hfp : isFilledB (t.slots p) = true := by rw [hsp]; exact shorthash7_filled _
        have hhr := home_range hpow k (o := o)
        refine Or.inr (Or.inr ⟨k, v, by rw [hk, upd_ne _ _ hpi]; exact hkp,
          by rw [hv, upd_ne _ _ hpi]; exact hvp, by rw [hsp', hsp], d, by rw [hm]; exact hd,
          by rw [hs]; exact hid, ?_⟩)
        rw [hs]
        exact hC p (home o t.size k) d hfp hpi hid (by omega) hhr.1 hhr.2 hall
  · intro a b a' b' ha1 ha2 hb1 hb2 hab hea heb
    rw [hs] at ha2 hb2
    rw [hent] at hea heb
    by_cases hai : a = i
    · rw [if_pos hai] at hea; cases hea
    · by_cases hbi : b = i
      · rw [if_pos hbi] at heb; cases heb
      · rw [if_neg hai] at hea
        rw [if_neg hbi] at heb
        exact hi.distinct a b a' b' ha1 ha2 hb1 hb2 hab hea heb
  · have := hi.count
    omega
  · rw [hs] at hp2
    have hpi : p ≠ i := fun h => by rw [h, hnfi] at hfp; cases hfp
    have hfp' : isFilledB (t.slots p) = true := by
      rcases hB p hpi with h | ⟨-, h⟩
      · rw [← h]; exact hfp
      · rw [h] at hfp; cases hfp
    rw [hf]
    exact hi.floorLe p hp1 hp2 hfp'

/-- Positions `e + s` on a probe sequence through `bk r` walk forward to `bk (r - s)`. -/
theorem pr_bk {sz i hh e r : Nat} (hp : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i) (h2 : i ≤ sz)
    (hpr : pr sz hh e = bk sz i r) : ∀ s, s ≤ r → pr sz hh (e + s) = bk sz i (r - s)
  | 0, _ => hpr
  | s + 1, hsr => by
    rw [← Nat.add_assoc, pr_succ, pr_bk hp hs h1 h2 hpr s (by omega),
      show r - s = r - (s + 1) + 1 by omega, next_bk hp hs h1 h2]

theorem deleteAt_spec {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t) {i : Nat}
    (h1 : 1 ≤ i) (h2 : i ≤ t.size) {e : K × V} (he : ent t i = some e) :
    Inv o (deleteAt t i) ∧ tlist (deleteAt t i) = (tlist t).filter (fun b => !o.eq e.1 b.1) ∧
      (deleteAt t i).count = t.count - 1 ∧ (deleteAt t i).age = bump t.age ∧
      (deleteAt t i).size = t.size ∧ (deleteAt t i).keys = upd t.keys i none ∧
      (deleteAt t i).vals = upd t.vals i none ∧
      (deleteAt t i).idxfloor = t.idxfloor ∧ (deleteAt t i).popcursor = t.popcursor ∧
      (deleteAt t i).maxprobe = t.maxprobe ∧
      isFilledB ((deleteAt t i).slots i) = false ∧
      ∀ p, p ≠ i → isFilledB ((deleteAt t i).slots p) = isFilledB (t.slots p) := by
  have hpow : IsPow t.size := by
    rcases hi.size with h | h
    · omega
    · exact h
  have hs64 : t.size ≤ 2 ^ 64 := by have := hi.sizeLe; omega
  have hfi := (ent_some he).1
  -- the facts about the new slot bytes used by `Inv.clear`
  have key : ((delD t i).1 i = 0 ∨ (delD t i).1 i = 127) ∧
      (∀ p, p ≠ i → (delD t i).1 p = t.slots p ∨ (t.slots p = 127 ∧ (delD t i).1 p = 0)) ∧
      (∀ q hh d, isFilledB (t.slots q) = true → q ≠ i → q = pr t.size hh d → d < t.size →
        1 ≤ hh → hh ≤ t.size → (∀ e, e < d → t.slots (pr t.size hh e) ≠ 0) →
        ∀ e, e < d → (delD t i).1 (pr t.size hh e) ≠ 0) := by
    unfold delD
    by_cases hE : isEmptyB (t.slots (nextIdx t.size i)) = true
    · rw [if_pos hE]
      have hE0 : t.slots (nextIdx t.size i) = 0 := (isEmptyB_iff _).1 hE
      obtain ⟨R, nd, hR, h127, hdb⟩ := deleteBack_spec (sz := t.size) (i := i) t.slots (t.size + 1) 0 1
        (by omega) (fun s hs1 hs2 => absurd hs2 (by omega))
      have hdb' : deleteBack t.size (t.size + 1) t.slots i 1 = (clr t.size i t.slots R, nd) := hdb
      rw [hdb']
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rcases clr_spec t.size i t.slots R i with ⟨-, hne⟩ | ⟨h0, -⟩
        · exact absurd rfl (hne 0 (by omega))
        · exact Or.inl h0
      · intro p hpi
        rcases clr_spec t.size i t.slots R p with ⟨h, -⟩ | ⟨h0, s, hs, hps⟩
        · exact Or.inl h
        · have hs0 : s ≠ 0 := fun h => hpi (by rw [hps, h] <;> rfl)
          exact Or.inr ⟨by rw [hps]; exact h127 s (by omega) hs, h0⟩
      · intro q hh d hqf hqi hq hd hh1 hh2 hall e' he' hS0
        have ht0 := hall e' he'
        rcases clr_spec t.size i t.slots R (pr t.size hh e') with ⟨hc, -⟩ | ⟨-, r, hr, hpr⟩
        · rw [hc] at hS0; exact ht0 hS0
        · have hpos := pr_bk hpow hs64 h1 h2 hpr
          rcases Nat.lt_or_ge (e' + r) d with hlt | hge
          · have hnext : pr t.size hh (e' + r + 1) = nextIdx t.size i := by
              rw [pr_succ, hpos r (Nat.le_refl _), Nat.sub_self]
              rfl
            by_cases hd' : e' + r + 1 = d
            · rw [← hd', hnext] at hq
              rw [hq, hE0, isFilledB_zero] at hqf
              cases hqf
            · have := hall (e' + r + 1) (by omega)
              rw [hnext] at this
              exact this hE0
          · have hq' := hpos (d - e') (by omega)
            rw [show e' + (d - e') = d by omega, ← hq] at hq'
            by_cases hz : r - (d - e') = 0
            · rw [hz] at hq'
              exact hqi hq'
            · have := h127 (r - (d - e')) (by omega) (by omega)
              rw [← hq'] at this
              rw [this, isFilledB_127] at hqf
              cases hqf
    · rw [if_neg hE]
      dsimp only
      refine ⟨Or.inr (upd_same _ _ _), fun p hpi => Or.inl (upd_ne _ _ hpi), ?_⟩
      intro q hh d _ _ _ _ _ _ hall e' he' hS0
      by_cases hpi : pr t.size hh e' = i
      · rw [hpi, upd_same] at hS0; cases hS0
      · rw [upd_ne _ _ hpi] at hS0; exact hall e' he' hS0
  obtain ⟨hA, hB, hC⟩ := key
  obtain ⟨hI, htl⟩ := Inv.clear (t' := delT t i (delD t i)) hl hi h1 h2 he rfl rfl rfl rfl rfl rfl rfl
    hA hB hC
  rw [deleteAt_eq]
  refine ⟨hI, htl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun p hpi => ?_⟩
  · show isFilledB ((delD t i).1 i) = false
    rcases hA with h | h <;> rw [h] <;> decide
  · show isFilledB ((delD t i).1 p) = isFilledB (t.slots p)
    rcases hB p hpi with h | ⟨h127, h0⟩
    · rw [h]
    · rw [h127, h0]; decide

/-! ## `delete!` and `pop!` -/

theorem dictDelete_of {o : KeyOps K} {t : Table K V} {key : K} {idx : Int}
    (h : htKeyindex t (o.hash key) (o.eq key) = .ok idx) :
    dictDelete o t key = if idx > 0 then pure (deleteAt t idx.toNat) else pure t := by
  unfold dictDelete
  rw [h]
  rfl

theorem popKey_of {o : KeyOps K} {t : Table K V} {key : K} {idx : Int}
    (h : htKeyindex t (o.hash key) (o.eq key) = .ok idx) :
    popKey o t key = if idx > 0 then
      (valAt t idx.toNat >>= fun v => pure (v, deleteAt t idx.toNat)) else throw .keyError := by
  unfold popKey
  rw [h]
  rfl

theorem popKeyDefault_of {o : KeyOps K} {t : Table K V} {key : K} {d : V} {idx : Int}
    (h : htKeyindex t (o.hash key) (o.eq key) = .ok idx) :
    popKeyDefault o t key d = if idx > 0 then
      (valAt t idx.toNat >>= fun v => pure (v, deleteAt t idx.toNat)) else pure (d, t) := by
  unfold popKeyDefault
  rw [h]
  rfl

theorem Rep.find_slot {o : KeyOps K} {t : Table K V} {m : RMap K V} (h : Rep o t m) {k : K}
    {e : K × V} (hrf : rfind o m k = some e) :
    ∃ i, 1 ≤ i ∧ i ≤ t.size ∧ ent t i = some e ∧ o.eq k e.1 = true := by
  obtain ⟨hem, hq⟩ := rfind_some hrf
  obtain ⟨i, h1, h2, hei⟩ := mem_tlist.1 (h.2.mem_iff.2 hem)
  exact ⟨i, h1, h2, hei, hq⟩

theorem Rep.absent {o : KeyOps K} {t : Table K V} {m : RMap K V} (h : Rep o t m) {k : K}
    (hrf : rfind o m k = none) : Absent o t k :=
  fun e he => (rfind_eq_none_iff.1 hrf) e (h.2.mem_iff.1 he)

/-- Deleting the stored entry `e`, `isequal` to `k`. -/
theorem Rep.deleteAt {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V} (h : Rep o t m)
    {k : K} {i : Nat} {e : K × V} (h1 : 1 ≤ i) (h2 : i ≤ t.size) (he : ent t i = some e)
    (hq : o.eq k e.1 = true) : Rep o (deleteAt t i) (rdel o m k) ∧ AgeStep t (deleteAt t i) 1 := by
  obtain ⟨hI, htl, -, hage, -⟩ := deleteAt_spec hl h.1 h1 h2 he
  refine ⟨⟨hI, ?_⟩, AgeStep.of_pos (by rw [hage, bump_eq]) (by omega)⟩
  rw [htl]
  have hf : (tlist t).filter (fun b => !o.eq e.1 b.1) = (tlist t).filter (fun b => !o.eq k b.1) :=
    List.filter_congr (fun b _ => by
      show (!o.eq e.1 b.1) = (!o.eq k b.1)
      rw [eq_congr_left hl hq])
  rw [hf]
  exact h.2.filter _

theorem Rep.dictDelete {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V}
    (h : Rep o t m) (k : K) :
    ∃ t', dictDelete o t k = .ok t' ∧ Rep o t' (rdel o m k) ∧ ∃ n, n ≤ 1 ∧ AgeStep t t' n := by
  rcases present_or_absent o t k with ⟨i, ⟨k0, v0⟩, h1, h2, he, hq⟩ | habs
  · rw [dictDelete_of (htKeyindex_found hl h.1 h1 h2 he hq), if_pos (by omega), Int.toNat_natCast]
    obtain ⟨hr, ha⟩ := h.deleteAt hl h1 h2 he hq
    exact ⟨_, rfl, hr, 1, Nat.le_refl _, ha⟩
  · rw [dictDelete_of (htKeyindex_absent h.1 habs), if_neg (by omega)]
    have hm : rdel o m k = m := rdel_of_absent fun b hb => habs b (h.2.mem_iff.2 hb)
    rw [hm]
    exact ⟨t, rfl, h, 0, Nat.zero_le _, AgeStep.refl t⟩

theorem Rep.popKey_found {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V}
    (h : Rep o t m) {k : K} {e : K × V} (hrf : rfind o m k = some e) :
    ∃ t', popKey o t k = .ok (e.2, t') ∧ Rep o t' (rdel o m k) ∧ AgeStep t t' 1 := by
  obtain ⟨i, h1, h2, he, hq⟩ := h.find_slot hrf
  obtain ⟨k0, v0⟩ := e
  rw [popKey_of (htKeyindex_found hl h.1 h1 h2 he hq), if_pos (by omega), Int.toNat_natCast,
    valAt_of_ent he]
  obtain ⟨hr, ha⟩ := h.deleteAt hl h1 h2 he hq
  exact ⟨_, rfl, hr, ha⟩

theorem Rep.popKey_absent {o : KeyOps K} {t : Table K V} {m : RMap K V} (h : Rep o t m) {k : K}
    (hrf : rfind o m k = none) : popKey o t k = .error .keyError := by
  rw [popKey_of (htKeyindex_absent h.1 (h.absent hrf)), if_neg (by omega)] <;> rfl

theorem Rep.popKeyDefault {o : KeyOps K} (hl : o.Lawful) {t : Table K V} {m : RMap K V}
    (h : Rep o t m) (k : K) (d : V) :
    ∃ t', popKeyDefault o t k d = .ok ((rlookup o m k).getD d, t') ∧ Rep o t' (rdel o m k) ∧
      ∃ n, n ≤ 1 ∧ AgeStep t t' n := by
  cases hrf : rfind o m k with
  | some e =>
    obtain ⟨i, h1, h2, he, hq⟩ := h.find_slot hrf
    have hlk : (rlookup o m k).getD d = e.2 := by unfold rlookup; rw [hrf] <;> rfl
    rw [hlk]
    obtain ⟨k0, v0⟩ := e
    rw [popKeyDefault_of (htKeyindex_found hl h.1 h1 h2 he hq), if_pos (by omega),
      Int.toNat_natCast, valAt_of_ent he]
    obtain ⟨hr, ha⟩ := h.deleteAt hl h1 h2 he hq
    exact ⟨_, rfl, hr, 1, Nat.le_refl _, ha⟩
  | none =>
    have hlk : (rlookup o m k).getD d = d := by unfold rlookup; rw [hrf] <;> rfl
    rw [hlk, popKeyDefault_of (htKeyindex_absent h.1 (h.absent hrf)), if_neg (by omega)]
    have hm : rdel o m k = m := rdel_of_absent fun b hb => (rfind_eq_none_iff.1 hrf) b hb
    rw [hm]
    exact ⟨t, rfl, h, 0, Nat.zero_le _, AgeStep.refl t⟩

end JuliaLean.Dicts
