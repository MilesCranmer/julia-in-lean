import JuliaLean.AbstractArraySpecs.CopyRowsProps
import JuliaLean.AbstractArraySpecs.CopyProofs

/-! Proofs of the `copyto!`/`copy!`/`copyto_axcheck!` row contracts. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean


theorem lt_iff_val (a b : I64) : a < b ↔ a.val < b.val := Iff.rfl
theorem le_iff_val (a b : I64) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl
/-! ## Lists -/

theorem spliceAt_nil {α : Type} (d : List α) (p : Nat) : spliceAt d [] p = d := by
  simp [spliceAt]

theorem spliceAt_succ {α : Type} (y : α) (d xs : List α) (p : Nat) :
    spliceAt (y :: d) xs (p + 1) = y :: spliceAt d xs p := by
  unfold spliceAt
  rw [show p + 1 + xs.length = (p + xs.length) + 1 by omega]
  simp

theorem spliceAt_cons {α : Type} (d : List α) (x : α) (xs : List α) :
    ∀ (j : Nat), j < d.length → spliceAt (d.set j x) xs (j + 1) = spliceAt d (x :: xs) j := by
  induction d with
  | nil => intro j h; simp at h
  | cons y ys ih =>
    intro j hj
    cases j with
    | zero =>
      unfold spliceAt
      rw [show 0 + (x :: xs).length = xs.length + 1 by simp,
        show 0 + 1 + xs.length = xs.length + 1 by omega]
      simp
    | succ j =>
      rw [List.set_cons_succ, spliceAt_succ, spliceAt_succ, ih j (by simp at hj; omega)]

theorem spliceAt_length {α : Type} (d xs : List α) (p : Nat) (h : p + xs.length ≤ d.length) :
    (spliceAt d xs p).length = d.length := by
  simp only [spliceAt, List.length_append, List.length_take, List.length_drop]; omega

/-! ## Arrays with replaced elements -/

theorem wf_data {α : Type} (A : Arr α) (d : List α) (hA : A.WF) (hd : d.length = A.data.length) :
    ({ A with data := d } : Arr α).WF :=
  ⟨hA.1, by rw [← hA.2.1]; exact congrArg _ hd, hA.2.2⟩

theorem setindex_none {α : Type} (A : Arr α) (hA : A.WF) (k : I64) (v : α)
    (h : refLinPos A k.val = none) : setindex A v [k] = .error .boundsError := by
  rw [(indexing_linear A hA k).2 v, refSet_eq]
  show storeAt A (refLinPos A k.val) v = _
  rw [h]; rfl

theorem getindex_lin {α : Type} (A : Arr α) (hA : A.WF) (k : I64) (p : Nat)
    (h : refLinPos A k.val = some p) :
    getindex A [k] = .ok (A.data[p]'(refPos_lt A hA [k] p h)) :=
  getindex_at A hA [k] p (Or.inr rfl) h

/-- A valid linear index `k` at position `p` is `lo + p`, exactly. -/
theorem linpos_val {α : Type} (A : Arr α) (hA : A.WF) (k : I64) (p : Nat)
    (h : refLinPos A k.val = some p) :
    k.val = wrapInt .i64 ((linearAxis A).lo.val + p) ∧ p < A.data.length := by
  have e := refLinPos_some A hA k.val p h
  have hb := bnd k
  refine ⟨by rw [← e, wrap_id _ hb.1 hb.2], refPos_lt A hA [k] p h⟩

/-! ## Writing consecutive linear indices -/

theorem writeLinear_from {α : Type} (A : Arr α) (hA : A.WF) : ∀ (xs : List α) (j : Nat) (d : List α) (i : I64),
    d.length = A.data.length → j ≤ A.data.length → i.val = wrapInt .i64 ((linearAxis A).lo.val + j) →
    writeLinear { A with data := d } i xs =
      if j + xs.length ≤ A.data.length then .ok { A with data := spliceAt d xs j } else .error .boundsError := by
  intro xs
  induction xs with
  | nil =>
    intro j d i _ hj _
    simp only [writeLinear, spliceAt_nil, List.length_nil, Nat.add_zero, if_pos hj]
  | cons x xs ih =>
    intro j d i hd hj hi
    have hD := wf_data A d hA hd
    have hst := refLin_step A hA j hj
    by_cases h1 : j < A.data.length
    · rw [if_pos h1] at hst
      have hp : refPos { A with data := d } [i] = some j := by
        rw [refPos_data]; show refLinPos A i.val = some j; rw [hi, hst]
      rw [writeLinear, setindex_at _ hD [i] j x (Or.inr rfl) hp, bind_ok]
      refine (ih (j + 1) (d.set j x) (i + i64 1) (by simp [hd]) h1
        (by rw [vadd, one_val, hi, wrap_add']; congr 1 <;> omega)).trans ?_
      rw [spliceAt_cons d x xs j (by omega)]
      by_cases h2 : j + 1 + xs.length ≤ A.data.length
      · rw [if_pos h2, if_pos (by simp; omega)]
      · rw [if_neg h2, if_neg (by simp; omega)]
    · rw [if_neg h1] at hst
      have hp : refLinPos { A with data := d } i.val = none := by
        show refLinPos A i.val = none; rw [hi, hst]
      rw [writeLinear, setindex_none _ hD i x hp, bind_err, if_neg (by simp; omega)]

/-- `writeLinear` from a linear index `k`: the reference contract. -/
theorem writeLinear_spec {α : Type} (A : Arr α) (hA : A.WF) (k : I64) (xs : List α) (hne : xs ≠ []) :
    writeLinear A k xs = match fitsAt A k xs.length with
      | some p => .ok { A with data := spliceAt A.data xs p }
      | none => .error .boundsError := by
  unfold fitsAt
  rcases hp : refLinPos A k.val with _ | p
  · obtain ⟨x, xs', rfl⟩ := List.exists_cons_of_ne_nil hne
    rw [writeLinear, setindex_none A hA k x hp, bind_err]
  · obtain ⟨hk, hlt⟩ := linpos_val A hA k p hp
    have h := writeLinear_from A hA xs p A.data k rfl (Nat.le_of_lt hlt) hk
    simp only [] at h ⊢
    rw [h]
    split <;> rfl

theorem writeLinear_nil {α : Type} (A : Arr α) (k : I64) : writeLinear A k [] = .ok A := rfl

/-! ## `copyto!(dest, src)` with an iterable -/

theorem copyIterLoop_from {α : Type} (dest : Arr α) (hd : dest.WF) : ∀ (xs : List α) (j : Nat) (d : List α)
    (st : IterState), GoodE dest j st → d.length = dest.data.length → j ≤ dest.data.length →
    copyIterLoop dest { dest with data := d } (eachindexStep dest st) xs =
      if j + xs.length ≤ dest.data.length then .ok { dest with data := spliceAt d xs j }
      else .error .argumentError := by
  intro xs
  induction xs with
  | nil =>
    intro j d st _ _ hj
    rw [if_pos (by simp; omega)]
    cases eachindexStep dest st <;> simp [copyIterLoop, spliceAt_nil]
  | cons x xs ih =>
    intro j d st hg hd' hj
    have hD := wf_data dest d hd hd'
    obtain ⟨s1, s2⟩ := each_step dest hd j st hg hj
    by_cases h1 : j < dest.data.length
    · obtain ⟨I, st', hs, hIl, hIp, hg'⟩ := s1 h1
      rw [hs, copyIterLoop, setindex_at _ hD I j x hIl (by rw [refPos_data]; exact hIp), bind_ok]
      refine (ih (j + 1) (d.set j x) st' hg' (by simp [hd']) h1).trans ?_
      rw [spliceAt_cons d x xs j (by omega)]
      by_cases h2 : j + 1 + xs.length ≤ dest.data.length
      · rw [if_pos h2, if_pos (by simp; omega)]
      · rw [if_neg h2, if_neg (by simp; omega)]
    · rw [s2 (by omega), copyIterLoop, if_neg (by simp; omega)]

theorem copytoIterPrefix_proven : CopytoIterPrefix := by
  intro α dest src hd
  have h := copyIterLoop_from dest hd src 0 dest.data (eachStart dest) (goodE_start dest) rfl (Nat.zero_le _)
  have e : copytoIter dest src = copyIterLoop dest { dest with data := dest.data }
      (eachindexStep dest (eachStart dest)) src := rfl
  refine ⟨fun hle => ?_, fun hlt => ⟨.argumentError, ?_⟩⟩
  · rw [e, h, if_pos (by omega)]
  · rw [e, h, if_neg (by omega)]

/-! ## `copyto!(dest, dstart, src)` with an iterable -/

theorem n_le_room {α : Type} (A : Arr α) (hA : A.WF) (k : I64) (p : Nat) (hp : refLinPos A k.val = some p)
    (n : I64) : decide (n ≤ (linearAxis A).hi - k + i64 1) = decide (n.val ≤ A.data.length - p) := by
  obtain ⟨hk, hlt⟩ := linpos_val A hA k p hp
  have hhi := linAx_len A hA
  have hlo := bnd (linearAxis A).lo
  have hhb := bnd (linearAxis A).hi
  have hkb := bnd k
  have hl : (A.data.length : Int) ≤ 9223372036854775807 := by
    have := hA.2.1; have := hA.2.2; rw [tmax_eq] at this; omega
  rw [wrap_id _ (by omega) (by omega)] at hk
  rw [decide_le64, vadd, vsub, one_val]
  rw [wrap_id ((linearAxis A).hi.val - k.val) (by omega) (by omega),
    wrap_id ((linearAxis A).hi.val - k.val + 1) (by omega) (by omega)]
  simp only [decide_eq_decide]
  omega

theorem copytoIterAt_spec : CopytoIterAtSpec := by
  intro α hasLen dest dstart src hd hsl
  have hl := lengthA_val dest hd
  by_cases hne : src = []
  · subst hne
    simp only [copytoIterAt, if_true]
    split
    · simp only [List.length_nil]; rfl
    · rfl
  rw [if_neg hne]
  have hlen1 : 1 ≤ src.length := by
    cases src with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hn : (i64 src.length).val = src.length := by rw [vlit, wrap_id _ (by omega) (by rw [tmax_eq] at hsl; omega)]
  have hn0 : (i64 src.length == i64 0) = false := by rw [beq64, hn, zero_val]; simp; omega
  have hw := writeLinear_spec dest hd dstart src hne
  unfold copytoIterAt
  simp only []
  split
  · rename_i hc
    simp only [hn0, Bool.false_eq_true, if_false]
    unfold fitsAt at hw ⊢
    rcases hp : refLinPos dest dstart.val with _ | p
    · have hcb : checkbounds dest [dstart] = .error .boundsError := by
        simp only [checkbounds, checkboundsBool, checkindex_linear dest hd, hp, Option.isSome_none,
          Bool.false_eq_true, if_false]
      rw [hcb, bind_err]
    · have hcb : checkbounds dest [dstart] = .ok () := by
        simp only [checkbounds, checkboundsBool, checkindex_linear dest hd, hp, Option.isSome_some, if_true]
      rw [hcb, bind_ok]
      simp only [n_le_room dest hd dstart p hp, hn]
      rw [hp] at hw
      simp only [] at hw ⊢
      by_cases h2 : p + src.length ≤ dest.data.length
      · rw [if_pos h2] at hw ⊢
        have hd2 : decide ((src.length : Int) ≤ (dest.data.length : Int) - (p : Int)) = true := by
          simp only [decide_eq_true_eq]; omega
        simp only [hd2, Bool.not_true, Bool.false_eq_true, if_false]
        exact hw
      · rw [if_neg h2]
        have hd2 : decide ((src.length : Int) ≤ (dest.data.length : Int) - (p : Int)) = false := by
          simp only [decide_eq_false_iff_not]; omega
        simp only [hd2, Bool.not_false, if_true]
  · exact hw

/-! ## Skipping the first elements of an iterable -/

theorem skipSrc_eq {α : Type} : ∀ (k : Nat) (xs : List α),
    skipSrc k xs = if k ≤ xs.length then .ok (xs.drop k) else .error .argumentError := by
  intro k
  induction k with
  | zero => intro xs; simp [skipSrc]
  | succ k ih =>
    intro xs
    cases xs with
    | nil => simp [skipSrc]
    | cons x xs => rw [skipSrc, ih xs]; simp

theorem copytoIterFrom_spec : CopytoIterFromSpec := by
  intro α dest dstart src sstart hd
  have hb := bnd sstart
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · unfold copytoIterFrom
    by_cases hs : sstart.val < 1
    · refine ⟨.argumentError, ?_⟩
      rw [if_pos (by rw [lt_iff_val]; rw [one_val]; exact hs)]
    · rw [if_neg (by rw [lt_iff_val, one_val]; exact hs), skipSrc_eq]
      have hlt : (src.length : Int) < sstart.val := by omega
      by_cases hk : (sstart.val - 1).toNat ≤ src.length
      · rw [if_pos hk, bind_ok]
        have : src.drop (sstart.val - 1).toNat = [] := List.drop_eq_nil_of_le (by omega)
        rw [this]; exact ⟨.argumentError, rfl⟩
      · rw [if_neg hk, bind_err]; exact ⟨.argumentError, rfl⟩
  · unfold copytoIterFrom
    rw [if_neg (by rw [lt_iff_val, one_val]; omega), skipSrc_eq, if_pos (by omega), bind_ok]
    have hne : src.drop (sstart.val - 1).toNat ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hne
    have hw := writeLinear_spec dest hd dstart _ hne
    rw [hy] at hw ⊢
    exact hw

/-! ## `copyto!(dest, dstart, src, sstart, n)` with an iterable -/

theorem inAx_linear {α : Type} (A : Arr α) (hA : A.WF) (k : I64) :
    inAx k (linearAxis A) = (refLinPos A k.val).isSome := by
  rw [← checkindex_linear A hA k, checkindex_eq (linearAxis_wf A hA)]
  unfold inAx
  rw [decide_le64, decide_le64]
  simp only [Bool.decide_and]

/-- The `dstart`/`n` test of the three-index copies. -/
theorem room_check {α : Type} (A : Arr α) (hA : A.WF) (k n : I64) :
    (checkindex (linearAxis A) k && decide (n ≤ (linearAxis A).hi - k + i64 1)) =
      (fitsAt A k n.val.toNat).isSome ∨ n.val < 0 := by
  have hnb := bnd n
  rw [checkindex_linear A hA k]
  unfold fitsAt
  rcases hp : refLinPos A k.val with _ | p
  · left; rfl
  · by_cases hn : n.val < 0
    · right; exact hn
    · left
      simp only [Option.isSome_some, Bool.true_and, n_le_room A hA k p hp]
      by_cases h2 : p + n.val.toNat ≤ A.data.length
      · rw [if_pos h2]; simp only [Option.isSome_some, decide_eq_true_eq]; omega
      · rw [if_neg h2]; simp only [Option.isSome_none, decide_eq_false_iff_not]; omega

theorem room_check' {α : Type} (A : Arr α) (hA : A.WF) (k n : I64) (hn : 0 ≤ n.val) :
    (checkindex (linearAxis A) k && decide (n ≤ (linearAxis A).hi - k + i64 1)) =
      (fitsAt A k n.val.toNat).isSome := by
  rcases room_check A hA k n with h | h
  · exact h
  · omega

theorem takeLoop_from {α : Type} (A : Arr α) (hA : A.WF) : ∀ (xs : List α) (j : Nat) (d : List α) (i : I64),
    d.length = A.data.length → j < A.data.length → j + 1 + xs.length ≤ A.data.length →
    i.val = (linearAxis A).lo.val + j →
    ∃ i', takeLoop { A with data := d } i xs = .ok ({ A with data := spliceAt d xs (j + 1) }, i') ∧
      i'.val = (linearAxis A).lo.val + j + xs.length := by
  have hhi := linAx_len A hA
  have hlo := bnd (linearAxis A).lo
  have hhb := bnd (linearAxis A).hi
  intro xs
  induction xs with
  | nil => intro j d i _ _ _ hi; exact ⟨i, by simp [takeLoop, spliceAt_nil], by simp [hi]⟩
  | cons x xs ih =>
    intro j d i hd hj hle hi
    have hD := wf_data A d hA hd
    have hj1 : j + 1 < A.data.length := by simp at hle; omega
    have hst := refLin_step A hA (j + 1) (by omega)
    rw [if_pos hj1] at hst
    have hi1 : (i + i64 1).val = (linearAxis A).lo.val + (j + 1 : Nat) := by
      rw [vadd, one_val, hi, wrap_id _ (by omega) (by omega)]; push_cast; omega
    have hp : refPos { A with data := d } [i + i64 1] = some (j + 1) := by
      rw [refPos_data]; show refLinPos A (i + i64 1).val = some (j + 1)
      rw [hi1, ← wrap_id ((linearAxis A).lo.val + ((j + 1 : Nat) : Int)) (by omega) (by omega), hst]
    rw [takeLoop, setindex_at _ hD [i + i64 1] (j + 1) x (Or.inr rfl) hp, bind_ok]
    obtain ⟨i', h1, h2⟩ := ih (j + 1) (d.set (j + 1) x) (i + i64 1) (by simp [hd]) hj1
      (by simp at hle; omega) hi1
    refine ⟨i', h1.trans ?_, by rw [h2]; simp; omega⟩
    rw [spliceAt_cons d x xs (j + 1) (by omega)]

theorem copytoIterN_spec : CopytoIterNSpec := by
  intro α dest dstart src sstart n hd
  have hnb := bnd n
  have hsb := bnd sstart
  have hdb := bnd dstart
  have hhi := linAx_len dest hd
  have hlo := bnd (linearAxis dest).lo
  have hhb := bnd (linearAxis dest).hi
  have hbt : 0 ≤ n.val → (inAx dstart (linearAxis dest) && decide (n ≤ (linearAxis dest).hi - dstart + i64 1)) =
      (fitsAt dest dstart n.val.toNat).isSome := by
    intro hn
    rw [inAx_linear dest hd, ← checkindex_linear dest hd]
    exact room_check' dest hd dstart n hn
  have hn0 : n.val = 0 ↔ (n == i64 0) = true := by rw [beq64, zero_val]; simp
  refine ⟨fun h0 => ?_, fun hpos h1 h2 p hp => ?_, fun hne hnot => ?_⟩
  · unfold copytoIterN
    rw [if_neg (by rw [lt_iff_val, zero_val]; omega), if_pos (hn0.mp h0)]
  · -- success
    have hfit := hp
    unfold fitsAt at hfit
    rcases hlp : refLinPos dest dstart.val with _ | p'
    · rw [hlp] at hfit; simp at hfit
    rw [hlp] at hfit
    simp only [] at hfit
    by_cases hroom : p' + n.val.toNat ≤ dest.data.length
    · rw [if_pos hroom] at hfit
      simp only [Option.some.injEq] at hfit
      subst hfit
      obtain ⟨hk, hlt⟩ := linpos_val dest hd dstart p' hlp
      rw [wrap_id _ (by omega) (by omega)] at hk
      have hb : (inAx dstart (linearAxis dest) && decide (n ≤ (linearAxis dest).hi - dstart + i64 1)) = true := by
        rw [hbt (by omega), hp]; rfl
      have hkl : (sstart.val - 1).toNat + n.val.toNat ≤ src.length := by omega
      have hne : src.drop (sstart.val - 1).toNat ≠ [] := by
        intro e; have := congrArg List.length e; simp at this; omega
      obtain ⟨val, rest, hy⟩ := List.exists_cons_of_ne_nil hne
      have hrl : rest.length = src.length - (sstart.val - 1).toNat - 1 := by
        have := congrArg List.length hy; simp at this; omega
      unfold copytoIterN
      rw [if_neg (by rw [lt_iff_val, zero_val]; omega), if_neg (by rw [← hn0]; omega),
        if_neg (by rw [lt_iff_val, one_val]; omega)]
      simp only [hb, Bool.not_true, Bool.false_eq_true, if_false]
      rw [skipSrc_eq, if_pos (by omega), bind_ok, hy]
      simp only []
      have hpos0 : refPos dest [dstart] = some p' := hlp
      rw [setindex_at dest hd [dstart] p' val (Or.inr rfl) hpos0, bind_ok]
      have htl : (rest.take (n.val - 1).toNat).length = n.val.toNat - 1 := by simp; omega
      obtain ⟨i', ht, hi'⟩ := takeLoop_from dest hd (rest.take (n.val - 1).toNat) p' (dest.data.set p' val)
        dstart (by simp) hlt (by rw [htl]; omega) hk
      rw [ht, bind_ok]
      simp only []
      have hdmax : (dstart + n - i64 1).val = dstart.val + n.val - 1 := by
        rw [vsub, vadd, one_val, wi, wi]; omega
      have hdm : ¬ i' < dstart + n - i64 1 := by
        rw [lt_iff_val, hdmax, hi', htl]; omega
      rw [if_neg hdm, spliceAt_cons dest.data val _ p' hlt]
      congr 3
      obtain ⟨m, hm⟩ : ∃ m, n.val.toNat = m + 1 := ⟨n.val.toNat - 1, by omega⟩
      rw [hm, List.take_succ_cons, show (n.val - 1).toNat = m by omega]
    · rw [if_neg hroom] at hfit; simp at hfit
  · -- failure
    unfold copytoIterN
    by_cases hneg : n.val < 0
    · exact ⟨.argumentError, by rw [if_pos (by rw [lt_iff_val, zero_val]; exact hneg)]⟩
    rw [if_neg (by rw [lt_iff_val, zero_val]; exact hneg), if_neg (by rw [← hn0]; exact hne)]
    by_cases hs1 : sstart.val < 1
    · exact ⟨.argumentError, by rw [if_pos (by rw [lt_iff_val, one_val]; exact hs1)]⟩
    rw [if_neg (by rw [lt_iff_val, one_val]; exact hs1)]
    by_cases hf : (fitsAt dest dstart n.val.toNat).isSome
    · have hb : (inAx dstart (linearAxis dest) && decide (n ≤ (linearAxis dest).hi - dstart + i64 1)) = true := by
        rw [hbt (by omega)]; exact hf
      simp only [hb, Bool.not_true, Bool.false_eq_true, if_false]
      have hshort : ¬ (sstart.val - 1 + n.val ≤ src.length) := fun h => hnot ⟨by omega, by omega, h, hf⟩
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp hf
      have hfit := hp'
      unfold fitsAt at hfit
      rcases hlp : refLinPos dest dstart.val with _ | p
      · rw [hlp] at hfit; simp at hfit
      rw [hlp] at hfit
      simp only [] at hfit
      by_cases hroom : p + n.val.toNat ≤ dest.data.length
      · rw [if_pos hroom] at hfit
        obtain ⟨hk, hlt⟩ := linpos_val dest hd dstart p hlp
        rw [wrap_id _ (by omega) (by omega)] at hk
        rw [skipSrc_eq]
        by_cases hk1 : (sstart.val - 1).toNat ≤ src.length
        · rw [if_pos hk1, bind_ok]
          rcases hy : src.drop (sstart.val - 1).toNat with _ | ⟨val, rest⟩
          · exact ⟨.argumentError, rfl⟩
          · have hrl : rest.length + 1 = src.length - (sstart.val - 1).toNat := by
              have := congrArg List.length hy; simp at this; omega
            simp only []
            have hpos0 : refPos dest [dstart] = some p := hlp
            rw [setindex_at dest hd [dstart] p val (Or.inr rfl) hpos0, bind_ok]
            have htl : (rest.take (n.val - 1).toNat).length = rest.length := by simp; omega
            obtain ⟨i', ht, hi'⟩ := takeLoop_from dest hd (rest.take (n.val - 1).toNat) p (dest.data.set p val)
              dstart (by simp) hlt (by rw [htl]; omega) hk
            rw [ht, bind_ok]
            simp only []
            have hdmax : (dstart + n - i64 1).val = dstart.val + n.val - 1 := by
              rw [vsub, vadd, one_val, wi, wi]; omega
            have hdm : i' < dstart + n - i64 1 := by
              rw [lt_iff_val, hdmax, hi', htl]; omega
            exact ⟨.boundsError, by rw [if_pos hdm]⟩
        · rw [if_neg hk1, bind_err]; exact ⟨.argumentError, rfl⟩
      · rw [if_neg hroom] at hfit; simp at hfit
    · have hb : (inAx dstart (linearAxis dest) && decide (n ≤ (linearAxis dest).hi - dstart + i64 1)) = false := by
        rw [hbt (by omega)]; simpa using hf
      exact ⟨.boundsError, by simp only [hb, Bool.not_false, if_true]⟩

/-! ## `copyto!(dest, dstart, src, sstart, n)` for arrays -/

theorem copyNLoop_from {α : Type} (dest src : Arr α) (hd : dest.WF) (hs : src.WF) (dstart sstart : I64)
    (p q : Nat) (hdp : dstart.val = (linearAxis dest).lo.val + p)
    (hsq : sstart.val = (linearAxis src).lo.val + q) :
    ∀ (k i : Nat) (d : List α), d.length = dest.data.length → p + i + k ≤ dest.data.length →
      q + i + k ≤ src.data.length →
      copyNLoop src dstart sstart k i { dest with data := d } =
        .ok { dest with data := spliceAt d ((src.data.drop (q + i)).take k) (p + i) } := by
  intro k
  induction k with
  | zero => intro i d _ _ _; simp [copyNLoop, spliceAt_nil]
  | succ k ih =>
    intro i d hd' hpk hqk
    have hp1 : p + (i + 1) + k ≤ dest.data.length := by omega
    have hq1 : q + (i + 1) + k ≤ src.data.length := by omega
    have hpi : p + i < d.length := by omega
    have hqi : q + i < src.data.length := by omega
    have hpi' : p + i < dest.data.length := by omega
    have hsl : (src.data.length : Int) ≤ 9223372036854775807 := by
      have := hs.2.1; have := hs.2.2; rw [tmax_eq] at this; omega
    have hiv : (i64 (i : Int)).val = i := by rw [vlit, wrap_id _ (by omega) (by omega)]
    have hD := wf_data dest d hd hd'
    have hsrc := refLin_step src hs (q + i) (Nat.le_of_lt hqi)
    rw [if_pos hqi] at hsrc
    have hdst := refLin_step dest hd (p + i) (Nat.le_of_lt hpi')
    rw [if_pos hpi'] at hdst
    have hsv : (sstart + i64 (i : Int)).val = wrapInt .i64 ((linearAxis src).lo.val + ((q + i : Nat) : Int)) := by
      rw [vadd, hiv, hsq, Int.natCast_add, Int.add_assoc]
    have hdv : (dstart + i64 (i : Int)).val = wrapInt .i64 ((linearAxis dest).lo.val + ((p + i : Nat) : Int)) := by
      rw [vadd, hiv, hdp, Int.natCast_add, Int.add_assoc]
    have hps : refLinPos src (sstart + i64 (i : Int)).val = some (q + i) := by rw [hsv, hsrc]
    have hpd : refPos { dest with data := d } [dstart + i64 (i : Int)] = some (p + i) := by
      rw [refPos_data]; show refLinPos dest (dstart + i64 (i : Int)).val = some (p + i); rw [hdv, hdst]
    rw [copyNLoop, getindex_lin src hs _ (q + i) hps, bind_ok,
      setindex_at _ hD [dstart + i64 (i : Int)] (p + i) _ (Or.inr rfl) hpd, bind_ok]
    refine (ih (i + 1) (d.set (p + i) _) (by rw [List.length_set]; exact hd') hp1 hq1).trans ?_
    rw [show p + (i + 1) = p + i + 1 from (Nat.add_assoc p i 1).symm, spliceAt_cons d _ _ (p + i) hpi,
      show q + (i + 1) = q + i + 1 from (Nat.add_assoc q i 1).symm]
    rw [List.drop_eq_getElem_cons hqi, List.take_succ_cons]

theorem copytoN_spec : CopytoNSpec := by
  intro α aliased dest dstart src sstart n hd hs
  have hnb := bnd n
  have hn0 : n.val = 0 ↔ (n == i64 0) = true := by rw [beq64, zero_val]; simp
  refine ⟨fun h0 => ?_, fun hneg => ?_, fun hpos => ?_⟩
  · unfold copytoN; rw [if_pos (hn0.mp h0)]
  · exact ⟨.argumentError, by
      unfold copytoN; rw [if_neg (by rw [← hn0]; omega), if_pos (by rw [lt_iff_val, zero_val]; exact hneg)]⟩
  · unfold copytoN
    rw [if_neg (by rw [← hn0]; omega), if_neg (by rw [lt_iff_val, zero_val]; omega)]
    simp only [room_check' dest hd dstart n (by omega), room_check' src hs sstart n (by omega), unaliasA_eq]
    rcases hfd : fitsAt dest dstart n.val.toNat with _ | p
    · simp
    rcases hfs : fitsAt src sstart n.val.toNat with _ | q
    · simp
    simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, if_false]
    unfold fitsAt at hfd hfs
    rcases hlp : refLinPos dest dstart.val with _ | p' <;> rw [hlp] at hfd <;> simp only [] at hfd
    · simp at hfd
    rcases hlq : refLinPos src sstart.val with _ | q' <;> rw [hlq] at hfs <;> simp only [] at hfs
    · simp at hfs
    split at hfd <;> rename_i hroom <;> simp only [Option.some.injEq, reduceCtorEq] at hfd
    split at hfs <;> rename_i hroom' <;> simp only [Option.some.injEq, reduceCtorEq] at hfs
    subst hfd; subst hfs
    have hk := refLinPos_some dest hd _ _ hlp
    have hq := refLinPos_some src hs _ _ hlq
    have h := copyNLoop_from dest src hd hs dstart sstart p' q' hk hq n.val.toNat 0 dest.data rfl
      (by omega) (by omega)
    simpa using h

theorem copytoAt_spec : CopytoAtSpec := by
  intro α aliased dest dstart src hd hs
  have hl := lengthA_val src hs
  obtain ⟨h0, -, hpos⟩ := copytoN_spec aliased dest dstart src (linearAxis src).lo (lengthA src) hd hs
  unfold copytoAt
  by_cases he : src.data = []
  · rw [if_pos he]; exact h0 (by rw [hl, he]; rfl)
  rw [if_neg he]
  have hlen : 1 ≤ src.data.length := by
    cases h : src.data with
    | nil => exact absurd h he
    | cons _ _ => simp
  rw [hpos (by omega)]
  have hs0 : fitsAt src (linearAxis src).lo (lengthA src).val.toNat = some 0 := by
    have hst := refLin_step src hs 0 (by omega)
    rw [if_pos (by omega), show ((linearAxis src).lo.val + ((0 : Nat) : Int)) = (linearAxis src).lo.val by simp,
      wrap_id _ (bnd _).1 (bnd _).2] at hst
    unfold fitsAt; rw [hst]; simp only []; rw [if_pos (by omega)]
  rw [hs0, show (lengthA src).val.toNat = src.data.length by omega]
  cases fitsAt dest dstart src.data.length <;> simp

theorem copytoFrom_spec : CopytoFromSpec := by
  intro α aliased dest dstart src sstart hd hs
  unfold copytoFrom
  simp only [checkindex_linear src hs]
  rcases hq : refLinPos src sstart.val with _ | q
  · simp
  simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, if_false]
  obtain ⟨hk, hlt⟩ := linpos_val src hs sstart q hq
  have hhi := linAx_len src hs
  have hlo := bnd (linearAxis src).lo
  have hhb := bnd (linearAxis src).hi
  have hkb := bnd sstart
  have hsl : (src.data.length : Int) ≤ 9223372036854775807 := by
    have := hs.2.1; have := hs.2.2; rw [tmax_eq] at this; omega
  rw [wrap_id _ (by omega) (by omega)] at hk
  obtain ⟨n, hn⟩ : ∃ n : I64, n = (linearAxis src).hi - sstart + i64 1 := ⟨_, rfl⟩
  rw [← hn]
  have hnv : n.val = src.data.length - q := by
    rw [hn, vadd, vsub, one_val, wrap_id ((linearAxis src).hi.val - sstart.val) (by omega) (by omega),
      wrap_id _ (by omega) (by omega)]
    omega
  obtain ⟨-, -, hpos⟩ := copytoN_spec aliased dest dstart src sstart n hd hs
  rw [hpos (by omega)]
  have hfs : fitsAt src sstart n.val.toNat = some q := by
    unfold fitsAt; rw [hq]; simp only []; rw [if_pos (by omega)]
  rw [hfs, show n.val.toNat = src.data.length - q by omega]
  have ht : (src.data.drop q).take (src.data.length - q) = src.data.drop q :=
    List.take_of_length_le (by simp)
  cases fitsAt dest dstart (src.data.length - q) <;> simp [ht]

/-! ## Rectangular blocks -/

/-- `ys` are `x, x + s, x + 2s, ...` computed with wrapping `Int` additions. -/
def Chain (s : I64) : I64 → List I64 → Prop
  | _, [] => True
  | x, y :: ys => y = x ∧ Chain s (x + s) ys

theorem Rg.at_succ (r : Rg) (k : Nat) : r.at (k + 1) = r.at k + r.step := by
  apply ext64
  rw [vadd]
  show wrapInt .i64 _ = wrapInt .i64 (wrapInt .i64 _ + _)
  rw [wrap_add']
  congr 1
  push_cast
  rw [Int.add_mul, Int.one_mul, Int.add_assoc]

theorem Rg.at_zero (r : Rg) : r.at 0 = r.first := by
  apply ext64
  show wrapInt .i64 (r.first.val + ((0 : Nat) : Int) * r.step.val) = r.first.val
  rw [show ((0 : Nat) : Int) * r.step.val = 0 by simp, Int.add_zero, wrap_id _ (bnd _).1 (bnd _).2]

theorem elemsFrom_chain (r : Rg) : ∀ (m k : Nat), Chain r.step (r.at k) (r.elemsFrom k m) := by
  intro m
  induction m with
  | zero => intro k; trivial
  | succ m ih => intro k; exact ⟨rfl, by rw [← Rg.at_succ]; exact ih (k + 1)⟩

theorem elems_chain (r : Rg) : Chain r.step r.first r.elems := by
  have := elemsFrom_chain r r.len 0
  rwa [Rg.at_zero] at this

theorem elemsFrom_length (r : Rg) : ∀ (m k : Nat), (r.elemsFrom k m).length = m := by
  intro m; induction m with
  | zero => intro k; rfl
  | succ m ih => intro k; simp [Rg.elemsFrom, ih]

theorem elems_length (r : Rg) : r.elems.length = r.len := elemsFrom_length r r.len 0

theorem mem_elemsFrom (r : Rg) : ∀ (m k : Nat) (x : I64),
    x ∈ r.elemsFrom k m ↔ ∃ j, k ≤ j ∧ j < k + m ∧ x = r.at j := by
  intro m
  induction m with
  | zero => intro k x; simp [Rg.elemsFrom]; intro j h1 h2; omega
  | succ m ih =>
    intro k x
    simp only [Rg.elemsFrom, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨j, h1, h2, rfl⟩)
      · exact ⟨k, Nat.le_refl _, by omega, rfl⟩
      · exact ⟨j, by omega, by omega, rfl⟩
    · rintro ⟨j, h1, h2, rfl⟩
      by_cases hj : j = k
      · left; rw [hj]
      · right; exact ⟨j, by omega, by omega, rfl⟩

theorem Rg.at_val (r : Rg) (hr : r.WF) (k : Nat) (hk : k < r.len) :
    (r.at k).val = r.first.val + (k : Int) * r.step.val := by
  obtain ⟨-, h⟩ := hr
  obtain ⟨h1, h2⟩ := h k hk
  show wrapInt .i64 _ = _
  rw [tmin_eq] at h1; rw [tmax_eq] at h2
  exact wrap_id _ h1 h2

/-- A range lies in an axis exactly when its first and last elements do. -/
theorem checkindexRg_eq (inds : Ax) (hi : inds.WF) (r : Rg) (hr : r.WF) :
    checkindexRg inds r = decide (∀ x ∈ r.elems, inAxis inds x) := by
  unfold checkindexRg
  rw [checkindex_eq hi, checkindex_eq hi]
  have hm : ∀ x, x ∈ r.elems ↔ ∃ j, j < r.len ∧ x = r.at j := by
    intro x; unfold Rg.elems; rw [mem_elemsFrom]; simp
  by_cases h0 : r.len = 0
  · simp only [h0, decide_true, Bool.true_or]
    symm; simp only [decide_eq_true_eq]
    intro x hx; obtain ⟨j, hj, -⟩ := (hm x).mp hx; omega
  simp only [h0, decide_false, Bool.false_or]
  have hf : r.first = r.at 0 := (Rg.at_zero r).symm
  have hv0 := Rg.at_val r hr 0 (by omega)
  have hvl := Rg.at_val r hr (r.len - 1) (by omega)
  by_cases hall : ∀ x ∈ r.elems, inAxis inds x
  · rw [decide_eq_true hall]
    have a0 := hall (r.at 0) ((hm _).mpr ⟨0, by omega, rfl⟩)
    have al := hall (r.at (r.len - 1)) ((hm _).mpr ⟨r.len - 1, by omega, rfl⟩)
    unfold inAxis at a0 al
    rw [hf]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨a0, al⟩
  · rw [decide_eq_false hall]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases ha : inds.lo.val ≤ r.first.val ∧ r.first.val ≤ inds.hi.val
    · by_cases hb : inds.lo.val ≤ (r.at (r.len - 1)).val ∧ (r.at (r.len - 1)).val ≤ inds.hi.val
      · exfalso
        obtain ⟨a1, a2⟩ := ha
        obtain ⟨b1, b2⟩ := hb
        apply hall
        intro x hx
        obtain ⟨j, hj, rfl⟩ := (hm x).mp hx
        have hvj := Rg.at_val r hr j hj
        rw [hvl] at b1 b2
        unfold inAxis
        rw [hvj]
        -- j * s lies between 0 and (len - 1) * s
        have hj' : (j : Int) ≤ ((r.len - 1 : Nat) : Int) := by omega
        rcases Int.le_total 0 r.step.val with hs | hs
        · have m1 : 0 ≤ (j : Int) * r.step.val := Int.mul_nonneg (by omega) hs
          have m2 : (j : Int) * r.step.val ≤ ((r.len - 1 : Nat) : Int) * r.step.val :=
            Int.mul_le_mul_of_nonneg_right hj' hs
          constructor <;> omega
        · have m1 : (j : Int) * r.step.val ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hs
          have m2 : ((r.len - 1 : Nat) : Int) * r.step.val ≤ (j : Int) * r.step.val :=
            Int.mul_le_mul_of_nonpos_right hj' hs
          constructor <;> omega
      · exact Or.inr hb
    · exact Or.inl ha

theorem oneTo1_wf : (oneTo (i64 1)).WF := oneTo_wf (by decide)

theorem checkboundsRgs_eq' (axs : List Ax) (hwf : ∀ r ∈ axs, r.WF) (h1 : 1 ≤ axs.length)
    (h2 : axs.length ≤ 2) (ir jr : Rg) (hir : ir.WF) (hjr : jr.WF) :
    checkboundsRgs axs [ir, jr] = decide ((∀ x ∈ ir.elems, inAxis ((axs[0]?).getD (oneTo (i64 1))) x) ∧
      (∀ y ∈ jr.elems, inAxis ((axs[1]?).getD (oneTo (i64 1))) y)) := by
  rcases axs with _ | ⟨r, _ | ⟨r2, _ | ⟨r3, rs⟩⟩⟩
  · simp at h1
  · have hr : r.WF := hwf r (List.mem_singleton_self r)
    show (checkindexRg r ir && (checkindexRg (oneTo (i64 1)) jr && true)) = _
    rw [checkindexRg_eq r hr ir hir, checkindexRg_eq _ oneTo1_wf jr hjr, Bool.and_true]
    exact (Bool.decide_and _ _).symm.trans (decide_eq_decide.mpr Iff.rfl)
  · have hr : r.WF := hwf r (by simp)
    have hr2 : r2.WF := hwf r2 (by simp)
    show (checkindexRg r ir && (checkindexRg r2 jr && true)) = _
    rw [checkindexRg_eq r hr ir hir, checkindexRg_eq r2 hr2 jr hjr, Bool.and_true]
    exact (Bool.decide_and _ _).symm.trans (decide_eq_decide.mpr Iff.rfl)
  · simp at h2

theorem checkboundsRgs_eq {α : Type} (A : Arr α) (hA : A.WF) (h1 : 1 ≤ A.axes.length)
    (h2 : A.axes.length ≤ 2) (ir jr : Rg) (hir : ir.WF) (hjr : jr.WF) :
    checkboundsRgs A.axes [ir, jr] = decide (blockInBounds A ir jr) := by
  rw [checkboundsRgs_eq' A.axes hA.1 h1 h2 ir jr hir hjr]
  exact decide_eq_decide.mpr Iff.rfl

theorem refSet_shape {α : Type} (D : Arr α) (v : α) (I : List I64) (D' : Arr α)
    (h : refSet D v I = .ok D') : D'.axes = D.axes ∧ D'.style = D.style ∧ D'.data.length = D.data.length := by
  unfold refSet at h
  split at h
  · split at h
    · simp only [Except.ok.injEq] at h; subst h; simp
    · simp at h
  · simp at h

/-- One column of the block copy. -/
theorem blockInner_eq {α : Type} (A : Arr α) (hA : A.WF) (hA2 : A.axes.length ≤ 2) (B0 : Arr α)
    (hB0 : B0.WF) (hB2 : B0.axes.length ≤ 2) (s jd js : I64) :
    ∀ (iss ids : List I64) (idest : I64) (D : Arr α), Chain s idest ids → ids.length = iss.length →
      D.axes = B0.axes → D.style = B0.style → D.data.length = B0.data.length →
      blockInner A s jd js idest iss D =
        (ids.zip iss).foldlM (fun D ip => do
          let v ← refGet A [ip.2, js]
          refSet D v [ip.1, jd]) D := by
  intro iss
  induction iss with
  | nil => intro ids idest D _ hl _ _ _; cases ids with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons is iss ih =>
    intro ids idest D hc hl hax hst hlen
    cases ids with
    | nil => simp at hl
    | cons y ys =>
      obtain ⟨rfl, hc'⟩ := hc
      have hD : D.WF := ⟨hax ▸ hB0.1, by rw [hax, hlen]; exact hB0.2.1, by rw [hax]; exact hB0.2.2⟩
      rw [blockInner, List.zip_cons_cons, List.foldlM_cons,
        (indexing_extra A hA [is, js] (by simp; omega)).1]
      simp only [bind_assoc]
      cases hg : refGet A [is, js] with
      | error e => rfl
      | ok v =>
        simp only [bind_ok]
        rw [(indexing_extra D hD [y, jd] (by simp; rw [hax]; omega)).2 v]
        cases hset : refSet D v [y, jd] with
        | error e => rfl
        | ok D' =>
          simp only [bind_ok]
          obtain ⟨a1, a2, a3⟩ := refSet_shape D v [y, jd] D' hset
          exact ih ys (y + s) D' hc' (by simpa using hl) (a1.trans hax) (a2.trans hst) (a3.trans hlen)

theorem blockOuter_eq {α : Type} (A : Arr α) (hA : A.WF) (hA2 : A.axes.length ≤ 2) (B0 : Arr α)
    (hB0 : B0.WF) (hB2 : B0.axes.length ≤ 2) (ird : Rg) (irs : List I64) (hl : ird.elems.length = irs.length)
    (t : I64) :
    ∀ (jss jds : List I64) (jdest : I64) (D : Arr α), Chain t jdest jds → jds.length = jss.length →
      D.axes = B0.axes → D.style = B0.style → D.data.length = B0.data.length →
      blockOuter A ird t irs jdest jss D =
        (jds.zip jss).foldlM (fun D jq =>
          (ird.elems.zip irs).foldlM (fun D ip => do
            let v ← refGet A [ip.2, jq.2]
            refSet D v [ip.1, jq.1]) D) D := by
  have hfold : ∀ (l : List (I64 × I64)) (jq : I64 × I64) (D D' : Arr α),
      l.foldlM (fun D ip => do let v ← refGet A [ip.2, jq.2]; refSet D v [ip.1, jq.1]) D = .ok D' →
      D'.axes = D.axes ∧ D'.style = D.style ∧ D'.data.length = D.data.length := by
    intro l
    induction l with
    | nil => intro jq D D' h; simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp
    | cons ip l ih =>
      intro jq D D' h
      rw [List.foldlM_cons] at h
      cases hg : refGet A [ip.2, jq.2] with
      | error e => rw [hg] at h; simp [bind_err] at h
      | ok v =>
        rw [hg] at h
        simp only [bind_ok] at h
        cases hset : refSet D v [ip.1, jq.1] with
        | error e => rw [hset] at h; simp [bind_err] at h
        | ok D1 =>
          rw [hset, bind_ok] at h
          obtain ⟨a1, a2, a3⟩ := ih jq D1 D' h
          obtain ⟨b1, b2, b3⟩ := refSet_shape D v _ D1 hset
          exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩
  intro jss
  induction jss with
  | nil => intro jds jdest D _ hl' _ _ _; cases jds with
    | nil => rfl
    | cons _ _ => simp at hl'
  | cons js jss ih =>
    intro jds jdest D hc hl' hax hst hlen
    cases jds with
    | nil => simp at hl'
    | cons y ys =>
      obtain ⟨rfl, hc'⟩ := hc
      rw [blockOuter, List.zip_cons_cons, List.foldlM_cons,
        blockInner_eq A hA hA2 B0 hB0 hB2 ird.step y js irs ird.elems ird.first D (elems_chain ird) hl hax hst hlen]
      cases hin : (ird.elems.zip irs).foldlM (fun D ip => do
          let v ← refGet A [ip.2, js]
          refSet D v [ip.1, y]) D with
      | error e => rfl
      | ok D' =>
        simp only [bind_ok]
        obtain ⟨a1, a2, a3⟩ := hfold _ (y, js) D D' hin
        exact ih ys (y + t) D' hc' (by simpa using hl') (a1.trans hax) (a2.trans hst) (a3.trans hlen)

theorem i64_nat_inj (a b : Nat) (ha : (a : Int) ≤ tmax) (hb : (b : Int) ≤ tmax) :
    i64 a = i64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    rw [vlit, vlit, wrap_id _ (by omega) (by rw [tmax_eq] at ha; omega),
      wrap_id _ (by omega) (by rw [tmax_eq] at hb; omega)] at this
    omega
  · intro h; rw [h]

theorem copytoBlock_spec : CopytoBlockSpec := by
  intro α aliased B A ird jrd irs jrs hB hA hB2 hA2 hB1 hA1 hird hjrd hirs hjrs
  unfold copytoBlock
  have e1 := i64_nat_inj ird.len irs.len hird.1 hirs.1
  have e2 := i64_nat_inj jrd.len jrs.len hjrd.1 hjrs.1
  by_cases h1 : ird.len ≠ irs.len
  · rw [if_pos (fun h => h1 (e1.mp h)), if_pos (Or.inl h1)]
  have h1' : ird.len = irs.len := by omega
  rw [if_neg (fun h => h (e1.mpr h1'))]
  by_cases h2 : jrd.len ≠ jrs.len
  · rw [if_pos (fun h => h2 (e2.mp h)), if_pos (Or.inr h2)]
  have h2' : jrd.len = jrs.len := by omega
  rw [if_neg (fun h => h (e2.mpr h2')), if_neg (show ¬(ird.len ≠ irs.len ∨ jrd.len ≠ jrs.len) by omega)]
  rw [checkboundsRgs_eq B hB hB1 hB2 ird jrd hird hjrd, checkboundsRgs_eq A hA hA1 hA2 irs jrs hirs hjrs]
  by_cases hb1 : blockInBounds B ird jrd
  · by_cases hb2 : blockInBounds A irs jrs
    · simp only [hb1, hb2, and_self, if_true, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
        unaliasA_eq]
      exact blockOuter_eq A hA hA2 B hB hB2 ird irs.elems (by rw [elems_length, elems_length, h1'])
        jrd.step jrs.elems jrd.elems jrd.first B (elems_chain jrd)
        (by rw [elems_length, elems_length, h2']) rfl rfl rfl
    · simp only [hb1, hb2, and_false, if_false, decide_true, decide_false, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, if_true, bind_err]
  · simp only [hb1, false_and, if_false, decide_false, Bool.not_false, if_true, bind_err]

/-! ## Axes agreement -/

theorem axEq_iff {r s : Ax} (hr : r.WF) (hs : s.WF) :
    axEq r s = decide ((r.len = 0 ∧ s.len = 0) ∨ (r.lo = s.lo ∧ r.hi = s.hi)) := by
  have := len_def r; have := len_def s
  have hr0 := hr.2.1; have hs0 := hs.2.1
  have lr := axLength_val hr; have ls := axLength_val hs
  have iff_lo : r.lo = s.lo ↔ r.lo.val = s.lo.val := ⟨congrArg _, ext64⟩
  have iff_hi : r.hi = s.hi ↔ r.hi.val = s.hi.val := ⟨congrArg _, ext64⟩
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, iff_lo, iff_hi]
  unfold axEq axIsEmpty
  simp only [decide_lt64, beq64, one_val]
  split
  · rename_i he; simp only [decide_eq_true_eq] at he
    simp only [decide_eq_true_eq]; constructor <;> intro h <;> omega
  · split
    · rename_i he h1; simp only [decide_eq_true_eq] at he h1
      simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> intro h <;> omega
    · rename_i he h1; simp only [decide_eq_true_eq] at he h1
      simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> intro h <;> omega

theorem axesEq_iff : ∀ (a b : List Ax), (∀ r ∈ a, r.WF) → (∀ r ∈ b, r.WF) →
    axesEq a b = decide (sameAxes a b) := by
  intro a
  induction a with
  | nil => intro b _ _; cases b <;> rfl
  | cons r rs ih =>
    intro b ha hb
    cases b with
    | nil => rfl
    | cons s ss =>
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_iff]
      simp only [axesEq, Bool.and_eq_true, axEq_iff (ha r (by simp)) (hb s (by simp)),
        ih ss (fun x hx => ha x (by simp [hx])) (fun x hx => hb x (by simp [hx])), decide_eq_true_iff]
      exact Iff.rfl

theorem sameAxes_totalLen : ∀ (a b : List Ax), sameAxes a b → totalLen a = totalLen b := by
  intro a
  induction a with
  | nil => intro b h; cases b with
    | nil => rfl
    | cons _ _ => exact absurd h id
  | cons r rs ih =>
    intro b h
    cases b with
    | nil => exact absurd h id
    | cons s ss =>
      obtain ⟨h1, h2⟩ := h
      rw [totalLen_cons, totalLen_cons]
      rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; simp
      · rw [len_def, len_def, e1, e2, ih ss h2]

theorem checkaxs_spec : CheckaxsSpec := by
  intro axd axs hd hs
  unfold checkaxs
  rw [axesEq_iff axd axs hd hs]
  by_cases h : sameAxes axd axs
  · simp only [decide_eq_true h, if_true, if_pos h]
  · simp only [decide_eq_false h, Bool.false_eq_true, if_false, if_neg h]

/-- Arrays with agreeing axes have the same number of elements, so `copyto!` replaces all
of `dest`. -/
theorem copytoA_same {α : Type} (destBit aliased : Bool) (dest src : Arr α) (hd : dest.WF) (hs : src.WF)
    (hbit : destBit = true → dest.style = .linear ∧ ∀ r ∈ dest.axes, r.kind = .oneTo)
    (hl : src.data.length = dest.data.length) :
    copytoA destBit aliased dest src = .ok { dest with data := src.data } := by
  rw [(copytoPrefix_proven destBit aliased dest src hd hs hbit).1 (by omega),
    List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem sameAxes_len {α : Type} (dest src : Arr α) (hd : dest.WF) (hs : src.WF)
    (h : sameAxes dest.axes src.axes) : src.data.length = dest.data.length := by
  have := sameAxes_totalLen _ _ h
  have := hd.2.1; have := hs.2.1
  omega

theorem copytoAxcheck_spec : CopytoAxcheckSpec := by
  intro α destBit aliased dest src hd hs hbit
  unfold copytoAxcheck
  rw [checkaxs_spec dest.axes src.axes hd.1 hs.1]
  by_cases h : sameAxes dest.axes src.axes
  · rw [if_pos h, if_pos h, bind_ok]
    exact copytoA_same destBit aliased dest src hd hs hbit (sameAxes_len dest src hd hs h)
  · rw [if_neg h, if_neg h, bind_err]

theorem copyBangArray_spec : CopyBangArraySpec := by
  intro α destBit aliased dst src hd hs hbit
  unfold copyBangA
  rw [axesEq_iff dst.axes src.axes hd.1 hs.1]
  by_cases h : sameAxes dst.axes src.axes
  · simp only [decide_eq_true h, Bool.not_true, Bool.false_eq_true, if_false, if_pos h]
    exact copytoA_same destBit aliased dst src hd hs hbit (sameAxes_len dst src hd hs h)
  · simp only [decide_eq_false h, Bool.not_false, if_true, if_neg h]

theorem copyBangVector_spec : CopyBangVectorSpec := by
  intro α resize destBit aliased dst src hR hd hs hd1 hs1 hbit
  have hld := lengthA_val dst hd
  have hls := lengthA_val src hs
  refine ⟨fun hne => ⟨.argumentError, ?_⟩, fun heq => ?_⟩
  · have hb : ((linearAxis dst).lo == (linearAxis src).lo) = false := by
      rw [beq64]; simp only [decide_eq_false_iff_not]; intro e; exact hne (ext64 e)
    unfold copyBangV
    simp only [hb, Bool.not_false, if_true]
  · have hb : ((linearAxis dst).lo == (linearAxis src).lo) = true := by rw [heq]; exact beq_self_eq_true _
    unfold copyBangV
    simp only [hb, Bool.not_true, Bool.false_eq_true, if_false]
    by_cases hl : lengthA dst = lengthA src
    · rw [if_neg (fun h => h hl), bind_ok]
      have hl' : src.data.length = dst.data.length := by
        have := congrArg Subtype.val hl; omega
      exact ⟨_, copytoA_same destBit aliased dst src hd hs hbit hl', rfl, heq⟩
    · rw [if_pos hl]
      obtain ⟨d', hres, hwf, hax1, hlen, hlo, hsty, hkind⟩ := hR dst (lengthA src) hd hd1 (by omega)
      rw [hres, bind_ok]
      have hbit' : destBit = true → d'.style = .linear ∧ ∀ r ∈ d'.axes, r.kind = .oneTo := by
        intro hb
        obtain ⟨h1, h2⟩ := hbit hb
        refine ⟨hsty.trans h1, fun r hr => ?_⟩
        have : r.kind ∈ dst.axes.map (·.kind) := by rw [← hkind]; exact List.mem_map_of_mem hr
        obtain ⟨r0, hr0, e⟩ := List.mem_map.mp this
        rw [← e]; exact h2 r0 hr0
      have hl' : src.data.length = d'.data.length := by omega
      exact ⟨_, copytoA_same destBit aliased d' src hwf hs hbit' hl', rfl, by rw [← heq, ← hlo]; rfl⟩

end JuliaLean.AbstractArraySpecs
