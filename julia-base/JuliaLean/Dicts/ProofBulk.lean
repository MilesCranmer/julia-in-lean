import JuliaLean.Dicts.ProofDelete

/-!
# `empty!`, `filter!` and `sizehint!`

`filter!` deletes while scanning forward; `_delete!` changes only the deleted
slot and `0x7f` slots, so every filled slot after the scan position keeps its
pair. `sizehint!` with `n ≤ 2^61` computes `3n` and `cld(3n, 2)` without
wrapping, and a size of at least `1.5 * count` keeps every pair.
-/

namespace JuliaLean.Dicts

variable {K V : Type}

/-! ## `empty!` -/

theorem emptyBang_spec {o : KeyOps K} {t : Table K V} (hi : Inv o t) :
    Rep o (emptyBang t) [] ∧ AgeStep t (emptyBang t) 1 ∧ (emptyBang t).count = 0 := by
  have hnil : tlist (emptyBang t) = [] :=
    filterMap_ent_nil (emptyBang t).size 1 (fun _ _ _ => isFilledB_zero)
  have hnone : ∀ p, ent (emptyBang t) p = none := fun p => ent_of_not_filled isFilledB_zero
  refine ⟨⟨⟨hi.size, hi.sizeLe, fun _ _ _ => Or.inl rfl, ?_, by rw [hnil]; rfl, ?_,
    Nat.le_max_left _ _, fun p _ _ hf => ?_, Nat.le_refl _⟩, by rw [hnil]⟩,
    AgeStep.of_pos (bump_eq _) (by omega), rfl⟩
  · intro a b a' b' _ _ _ _ _ ha _
    rw [hnone] at ha
    cases ha
  · rcases hi.size with h | h
    · exact Or.inl h
    · exact Or.inr (show 0 < t.size by have := h.ge; omega)
  · rw [show (emptyBang t).slots p = 0 from rfl, isFilledB_zero] at hf
    cases hf

/-! ## `filter!` -/

/-- One iteration of the `filter!` loop at index `i + 1`. -/
def fstep (pred : K → V → Bool) (t : Table K V) (i : Nat) : DR (Table K V) :=
  if isFilledB (t.slots (i + 1)) then do
    let (k, v) ← entryAt t (i + 1)
    pure (if pred k v then t else deleteAt t (i + 1))
  else pure t

theorem filterBang_eq (t : Table K V) (pred : K → V → Bool) :
    filterBang t pred = if t.count == 0 then pure t else (List.range t.size).foldlM (fstep pred) t :=
  rfl

theorem fstep_keep {pred : K → V → Bool} {t : Table K V} {i : Nat} {k : K} {v : V}
    (he : ent t (i + 1) = some (k, v)) (hp : pred k v = true) : fstep pred t i = .ok t := by
  unfold fstep
  rw [if_pos (ent_some he).1, entryAt_of_ent he]
  show (pure (if pred k v then t else deleteAt t (i + 1)) : DR (Table K V)) = _
  rw [if_pos hp]
  rfl

theorem fstep_drop {pred : K → V → Bool} {t : Table K V} {i : Nat} {k : K} {v : V}
    (he : ent t (i + 1) = some (k, v)) (hp : pred k v = false) :
    fstep pred t i = .ok (deleteAt t (i + 1)) := by
  unfold fstep
  rw [if_pos (ent_some he).1, entryAt_of_ent he]
  show (pure (if pred k v then t else deleteAt t (i + 1)) : DR (Table K V)) = _
  rw [if_neg (by rw [hp]; decide)]
  rfl

theorem fstep_skip {pred : K → V → Bool} {t : Table K V} {i : Nat}
    (hf : isFilledB (t.slots (i + 1)) = false) : fstep pred t i = .ok t := by
  unfold fstep
  rw [if_neg (by rw [hf]; decide)]
  rfl

theorem ent_eq_of {t t' : Table K V} {p : Nat}
    (hf : isFilledB (t'.slots p) = isFilledB (t.slots p)) (hk : t'.keys p = t.keys p)
    (hv : t'.vals p = t.vals p) : ent t' p = ent t p := by
  unfold ent
  rw [hf, hk, hv]

/-- The state of the `filter!` loop after `n` iterations. -/
structure FInv (o : KeyOps K) (pred : K → V → Bool) (t : Table K V) (n : Nat) (T : Table K V) :
    Prop where
  inv : Inv o T
  size : T.size = t.size
  ent : ∀ p, 1 ≤ p → p ≤ t.size →
    ent T p = if p ≤ n then (ent t p).filter (fun e => pred e.1 e.2) else ent t p
  filled : ∀ p, n < p → p ≤ t.size → isFilledB (T.slots p) = isFilledB (t.slots p)
  age : ∃ k, T.count + k = t.count ∧ AgeStep t T k

theorem filter_fold {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t)
    (pred : K → V → Bool) :
    ∀ n, n ≤ t.size → ∃ T, (List.range n).foldlM (fstep pred) t = .ok T ∧ FInv o pred t n T
  | 0, _ => ⟨t, rfl, ⟨hi, rfl, fun p h1 _ => by rw [if_neg (by omega)], fun _ _ _ => rfl,
      0, rfl, AgeStep.refl t⟩⟩
  | n + 1, hn => by
    obtain ⟨T, h1, hF⟩ := filter_fold hl hi pred n (by omega)
    have hfold : (List.range (n + 1)).foldlM (fstep pred) t = fstep pred T n := by
      rw [List.range_succ, List.foldlM_append, h1]
      simp only [except_ok_bind, List.foldlM_cons, List.foldlM_nil]
      cases fstep pred T n <;> rfl
    rw [hfold]
    have hT1 : 1 ≤ n + 1 := by omega
    have hT2 : n + 1 ≤ T.size := by rw [hF.size]; exact hn
    have hfe : isFilledB (T.slots (n + 1)) = isFilledB (t.slots (n + 1)) :=
      hF.filled (n + 1) (by omega) hn
    have hee : ent T (n + 1) = ent t (n + 1) := by rw [hF.ent (n + 1) hT1 hn, if_neg (by omega)]
    obtain ⟨kk, hkk, hage⟩ := hF.age
    -- entries below the new index are as before
    have hlow : ∀ T' : Table K V, (∀ p, p ≠ n + 1 → ent T' p = ent T p) →
        ent T' (n + 1) = (ent t (n + 1)).filter (fun e => pred e.1 e.2) →
        ∀ p, 1 ≤ p → p ≤ t.size →
          ent T' p = if p ≤ n + 1 then (ent t p).filter (fun e => pred e.1 e.2) else ent t p := by
      intro T' hT' hnew p hp1 hp2
      by_cases hpn : p = n + 1
      · rw [hpn, if_pos (Nat.le_refl _)]
        exact hnew
      · rw [hT' p hpn, hF.ent p hp1 hp2]
        by_cases hle : p ≤ n
        · rw [if_pos hle, if_pos (by omega)]
        · rw [if_neg hle, if_neg (by omega)]
    cases hft : isFilledB (t.slots (n + 1)) with
    | false =>
      have hfT : isFilledB (T.slots (n + 1)) = false := by rw [hfe, hft]
      refine ⟨T, fstep_skip hfT, ⟨hF.inv, hF.size, hlow T (fun _ _ => rfl) ?_, fun p hp1 hp2 =>
        hF.filled p (by omega) hp2, kk, hkk, hage⟩⟩
      rw [hee, ent_of_not_filled hft]
      rfl
    | true =>
      obtain ⟨k, v, -, -, het, -, -⟩ := hi.filled hT1 hn hft
      have heT : ent T (n + 1) = some (k, v) := by rw [hee, het]
      cases hp : pred k v with
      | true =>
        refine ⟨T, fstep_keep heT hp, ⟨hF.inv, hF.size, hlow T (fun _ _ => rfl) ?_,
          fun p hp1 hp2 => hF.filled p (by omega) hp2, kk, hkk, hage⟩⟩
        rw [hee, het]
        show some (k, v) = (if pred k v then some (k, v) else none)
        rw [hp]
        rfl
      | false =>
        obtain ⟨hI, -, hc, hag, hs, hk, hv, -, -, -, hnf, hfil⟩ := deleteAt_spec hl hF.inv hT1 hT2 heT
        have hcpos := hF.inv.count_pos hT1 hT2 heT
        refine ⟨deleteAt T (n + 1), fstep_drop heT hp, ⟨hI, by rw [hs, hF.size],
          hlow _ (fun p hpn => ent_eq_of (hfil p hpn) (by rw [hk, upd_ne _ _ hpn])
            (by rw [hv, upd_ne _ _ hpn])) ?_,
          fun p hp1 hp2 => by rw [hfil p (by omega)]; exact hF.filled p (by omega) hp2,
          kk + 1, by omega, hage.trans (AgeStep.of_pos (by rw [hag, bump_eq]) (by omega))⟩⟩
        rw [ent_of_not_filled hnf, het]
        show none = (if pred k v then some (k, v) else none)
        rw [hp]
        rfl

theorem filterBang_spec {o : KeyOps K} (hl : o.Lawful) {t : Table K V} (hi : Inv o t)
    (pred : K → V → Bool) :
    ∃ t', filterBang t pred = .ok t' ∧ Inv o t' ∧
      tlist t' = (tlist t).filter (fun e => pred e.1 e.2) ∧ ∃ n, n ≤ t.count ∧ AgeStep t t' n := by
  rw [filterBang_eq]
  by_cases hc0 : t.count = 0
  · rw [if_pos (by simp [hc0])]
    have hnil : tlist t = [] := List.length_eq_zero_iff.1 (by rw [← hi.count]; exact hc0)
    exact ⟨t, rfl, hi, by rw [hnil]; rfl, 0, Nat.zero_le _, AgeStep.refl t⟩
  · rw [if_neg (by simp [hc0])]
    obtain ⟨T, h1, hF⟩ := filter_fold hl hi pred t.size (Nat.le_refl _)
    obtain ⟨kk, hkk, hage⟩ := hF.age
    refine ⟨T, h1, hF.inv, ?_, kk, by omega, hage⟩
    unfold tlist
    rw [hF.size, List.filter_filterMap]
    apply filterMap_congr_mem
    intro p hp
    rw [List.mem_range'_1] at hp
    rw [hF.ent p hp.1 (by omega), if_pos (by omega)]

/-! ## `sizehint!` -/

/-- `min(max(newsz, length(d)), max_values(T))`. -/
def hintM (o : KeyOps K) (t : Table K V) (n : JInt .i64) : JInt .i64 :=
  let len : JInt .i64 := JInt.lit .i64 t.count
  let m1 := if len.val < n.val then n else len
  if o.maxValues.val < m1.val then o.maxValues else m1

def hintTail (o : KeyOps K) (t : Table K V) (shrink : Bool) (c : JInt .i64) : DR (Table K V) :=
  let newsz := tableszI64 c
  if (if shrink then newsz.val = t.size else newsz.val ≤ t.size) then pure t
  else rehash o t newsz.val.toNat

/-- `sizehint!` after `min(max(...))`: the `cld` match with the rest of the body in each arm,
as the `do` elaborator places it. -/
def hintMatch (o : KeyOps K) (t : Table K V) (shrink : Bool) (x : Jl (JInt .i64)) :
    DR (Table K V) :=
  match x with
  | .ok c => (pure c : DR (JInt .i64)) >>= fun c => hintTail o t shrink c
  | .error e => (throw (.jl e) : DR (JInt .i64)) >>= fun c => hintTail o t shrink c

theorem sizehint_eq (o : KeyOps K) (t : Table K V) (n : JInt .i64) (shrink : Bool) :
    sizehint o t n shrink =
      hintMatch o t shrink (JInt.cld (JInt.lit .i64 3 * hintM o t n) (JInt.lit .i64 2)) :=
  rfl

theorem i64_min : IntTy.min .i64 = -2 ^ 63 := by decide
theorem i64_max : IntTy.max .i64 = 2 ^ 63 - 1 := by decide

theorem i64_range (a : JInt .i64) : -2 ^ 63 ≤ a.val ∧ a.val ≤ 2 ^ 63 - 1 := by
  have h := a.property
  have h1 := i64_min
  have h2 := i64_max
  omega

theorem wrap_i64_val {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) :
    (JInt.wrap .i64 x).val = x :=
  wrapInt_of_inRange .i64 x ⟨by rw [i64_min]; exact h1, by rw [i64_max]; exact h2⟩

theorem lit_i64_val {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) :
    (JInt.lit .i64 x).val = x := wrap_i64_val h1 h2

theorem hintM_spec {o : KeyOps K} (hmv : MaxValuesOK o) {t : Table K V} (hi : Inv o t)
    (hc : t.count ≤ 2 ^ 40) {n : JInt .i64} (hn : n.val ≤ 2 ^ 61) :
    (t.count : Int) ≤ (hintM o t n).val ∧ (hintM o t n).val ≤ 2 ^ 61 := by
  have hlen : (JInt.lit .i64 (t.count : Int)).val = t.count := lit_i64_val (by omega) (by omega)
  have hmv' : 2 ^ 62 ≤ o.maxValues.val ∨ (t.count : Int) ≤ o.maxValues.val := by
    rcases hmv with h | h
    · exact Or.inl h
    · right
      have hp : ((tlist t).map Prod.fst).Pairwise (fun a b => o.eq a b = false) := by
        rw [List.pairwise_map]
        exact tlist_pairwise hi
      have := h _ hp
      rw [List.length_map, ← hi.count] at this
      exact this
  unfold hintM
  dsimp only
  by_cases h1 : (JInt.lit .i64 (t.count : Int)).val < n.val
  · rw [if_pos h1]
    by_cases h2 : o.maxValues.val < n.val
    · rw [if_pos h2]
      omega
    · rw [if_neg h2]
      omega
  · rw [if_neg h1]
    by_cases h2 : o.maxValues.val < (JInt.lit .i64 (t.count : Int)).val
    · rw [if_pos h2]
      omega
    · rw [if_neg h2]
      omega

theorem cld_spec (M : JInt .i64) (h0 : 0 ≤ M.val) (h1 : M.val ≤ 2 ^ 61) :
    ∃ c : JInt .i64, JInt.cld (JInt.lit .i64 3 * M) (JInt.lit .i64 2) = .ok c ∧
      3 * M.val ≤ 2 * c.val ∧ c.val ≤ 2 ^ 62 := by
  have h3 : (JInt.lit .i64 3).val = 3 := by decide
  have h2 : (JInt.lit .i64 2).val = 2 := by decide
  have ha : (JInt.lit .i64 3 * M).val = 3 * M.val := by
    show (JInt.wrap .i64 ((JInt.lit .i64 3).val * M.val)).val = 3 * M.val
    rw [h3]
    exact wrap_i64_val (by omega) (by omega)
  generalize JInt.lit .i64 3 * M = a at ha
  have hd : (JInt.wrap .i64 (a.val.tdiv (JInt.lit .i64 2).val)).val = a.val / 2 := by
    rw [h2, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    exact wrap_i64_val (by omega) (by omega)
  have hdiv : JInt.div a (JInt.lit .i64 2) = .ok (JInt.wrap .i64 (a.val.tdiv (JInt.lit .i64 2).val)) := by
    unfold JInt.div
    rw [if_neg (by rw [h2]; decide), if_neg (fun h => by rw [h2] at h; exact absurd h.2.2 (by decide))]
  generalize JInt.wrap .i64 (a.val.tdiv (JInt.lit .i64 2).val) = d at hd hdiv
  have hd2 : (d * JInt.lit .i64 2).val = 2 * d.val := by
    show (JInt.wrap .i64 (d.val * (JInt.lit .i64 2).val)).val = 2 * d.val
    rw [h2, wrap_i64_val (by omega) (by omega)]
    omega
  unfold JInt.cld
  rw [hdiv]
  refine ⟨_, rfl, ?_⟩
  show 3 * M.val ≤ 2 * (JInt.wrap .i64 (d.val + (JInt.lit .i64 _).val)).val ∧
    (JInt.wrap .i64 (d.val + (JInt.lit .i64 _).val)).val ≤ 2 ^ 62
  by_cases hC : (¬ IntTy.i64.signed = true ∨ (a.val > 0 ↔ (JInt.lit .i64 2).val > 0)) ∧
      (d * JInt.lit .i64 2).val ≠ a.val
  · rw [if_pos hC]
    have h1' : (JInt.lit .i64 1).val = 1 := by decide
    rw [h1', wrap_i64_val (by omega) (by omega)]
    omega
  · rw [if_neg hC]
    have h0' : (JInt.lit .i64 0).val = 0 := by decide
    rw [h0', wrap_i64_val (by omega) (by omega)]
    rw [hd2, h2] at hC
    have hs : IntTy.i64.signed = true := rfl
    rw [hs] at hC
    by_cases hz : a.val = 0
    · omega
    · have : 2 * d.val = a.val := by
        apply Classical.byContradiction
        intro hne
        exact hC ⟨Or.inr ⟨fun _ => by decide, fun _ => by omega⟩, hne⟩
      omega

theorem tableszNat_le_pow {x : Nat} (h : x ≤ 2 ^ 62) : tableszNat x ≤ 2 ^ 62 := by
  unfold tableszNat
  split
  · omega
  · have hlog : Nat.log2 (x - 1) < 62 := (Nat.log2_lt (by omega)).2 (by omega)
    exact Nat.pow_le_pow_right (by decide) (by omega)

theorem tableszI64_val (c : JInt .i64) (h0 : 0 ≤ c.val) (h1 : c.val ≤ 2 ^ 62) :
    (tableszI64 c).val = (tableszNat c.val.toNat : Int) := by
  unfold tableszI64 tableszNat
  by_cases h : c.val < 16
  · rw [if_pos h, if_pos (by omega)]
    decide
  · rw [if_neg h, if_neg (by omega)]
    have hlog : Nat.log2 (c.val.toNat - 1) < 62 := (Nat.log2_lt (by omega)).2 (by omega)
    have hp : 2 ^ (Nat.log2 (c.val.toNat - 1) + 1) ≤ 2 ^ 62 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [show ((2 : Int) ^ (Nat.log2 (c.val.toNat - 1) + 1)) =
      ((2 ^ (Nat.log2 (c.val.toNat - 1) + 1) : Nat) : Int) from (Int.natCast_pow 2 _).symm]
    generalize 2 ^ (Nat.log2 (c.val.toNat - 1) + 1) = N at hp ⊢
    exact wrap_i64_val (by omega) (by omega)

theorem sizehint_spec {o : KeyOps K} (hmv : MaxValuesOK o) {t : Table K V} (hi : Inv o t)
    (hc : t.count ≤ 2 ^ 40) (n : JInt .i64) (hn : n.val ≤ 2 ^ 61) (shrink : Bool) :
    ∃ t', sizehint o t n shrink = .ok t' ∧ Inv o t' ∧ List.Perm (tlist t') (tlist t) ∧
      t'.count = t.count ∧ ∃ k, k ≤ 2 ∧ AgeStep t t' k := by
  obtain ⟨hm1, hm2⟩ := hintM_spec hmv hi hc hn
  obtain ⟨c, hcld, hc1, hc2⟩ := cld_spec (hintM o t n) (by omega) hm2
  have e : sizehint o t n shrink = hintTail o t shrink c := by
    rw [sizehint_eq, hcld] <;> rfl
  rw [e]
  unfold hintTail
  dsimp only
  rw [tableszI64_val c (by omega) hc2]
  by_cases hk : (if shrink then ((tableszNat c.val.toNat : Nat) : Int) = t.size
      else ((tableszNat c.val.toNat : Nat) : Int) ≤ t.size)
  · rw [if_pos hk]
    exact ⟨t, rfl, hi, List.Perm.refl _, rfl, 0, Nat.zero_le _, AgeStep.refl t⟩
  · rw [if_neg hk, Int.toNat_natCast]
    have hle := tableszNat_le_pow (show c.val.toNat ≤ 2 ^ 62 by omega)
    have hge := tableszNat_ge c.val.toNat
    have hpow := tableszNat_pow c.val.toNat
    have h16 := hpow.ge
    obtain ⟨t', h1, hi', hp', -, hc', ha'⟩ := rehash_spec hi (tableszNat c.val.toNat)
      (by rw [tableszNat_of_pow hpow]; omega) (by rw [tableszNat_of_pow hpow]; exact hle)
    refine ⟨t', h1, hi', hp', hc', ?_⟩
    by_cases hc0 : t.count = 0
    · exact ⟨1, by omega, AgeStep.of_pos (by rw [ha', if_pos hc0, bump_eq]) (by omega)⟩
    · exact ⟨2, Nat.le_refl _, AgeStep.of_pos (by rw [ha', if_neg hc0, bump_bump]) (by omega)⟩

end JuliaLean.Dicts
