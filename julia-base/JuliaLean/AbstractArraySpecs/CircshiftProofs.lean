import JuliaLean.AbstractArraySpecs.MutRowsProofs

/-! Proof of the `circshift!` contract: the three `reverse!` calls rotate the vector. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean

/-- `d` with its `L` elements from position `P` reversed. -/
def revSeg {α : Type} (d : List α) (P L : Nat) : List α :=
  d.take P ++ ((d.drop P).take L).reverse ++ d.drop (P + L)

theorem getElem_idx {α : Type} (l : List α) {i j : Nat} (h : i = j) (hi : i < l.length) (hj : j < l.length) :
    l[i] = l[j] := by
  subst h; rfl

theorem revSeg_length {α : Type} (d : List α) (P L : Nat) (h : P + L ≤ d.length) :
    (revSeg d P L).length = d.length := by
  simp only [revSeg, List.length_append, List.length_reverse, List.length_take, List.length_drop]
  omega

theorem revSeg_getElem {α : Type} (d : List α) (P L : Nat) (h : P + L ≤ d.length) (t : Nat)
    (ht : t < (revSeg d P L).length) :
    (revSeg d P L)[t] = if hm : P ≤ t ∧ t < P + L then d[2 * P + L - 1 - t]'(by omega)
      else d[t]'(by rw [revSeg_length d P L h] at ht; exact ht) := by
  have hl1 : (d.take P).length = P := by simp only [List.length_take]; omega
  have hl2' : ((d.drop P).take L).length = L := by
    simp only [List.length_take, List.length_drop]; omega
  have hl2 : ((d.drop P).take L).reverse.length = L := by rw [List.length_reverse, hl2']
  have hl3 : (d.take P ++ ((d.drop P).take L).reverse).length = P + L := by
    rw [List.length_append, hl1, hl2]
  simp only [revSeg, List.getElem_append, hl1, hl2, hl2', hl3, List.getElem_take, List.getElem_reverse,
    List.getElem_drop]
  repeat' split
  all_goals first | rfl | omega | (apply getElem_idx; omega)

theorem revSeg_short {α : Type} (d : List α) (P L : Nat) (h : P + L ≤ d.length) (hL : L ≤ 1) :
    revSeg d P L = d := by
  apply List.ext_getElem (revSeg_length d P L h)
  intro t h1 h2
  rw [revSeg_getElem d P L h t h1]
  split
  · apply getElem_idx; omega
  · rfl

theorem revSeg_step {α : Type} (d : List α) (P L : Nat) (h : P + L ≤ d.length) (hL : 2 ≤ L) :
    revSeg ((d.set P (d[P + L - 1]'(by omega))).set (P + L - 1) (d[P]'(by omega))) (P + 1) (L - 2) =
      revSeg d P L := by
  have hs : ((d.set P (d[P + L - 1]'(by omega))).set (P + L - 1) (d[P]'(by omega))).length = d.length := by simp
  have hle : P + 1 + (L - 2) ≤ ((d.set P (d[P + L - 1]'(by omega))).set (P + L - 1) (d[P]'(by omega))).length := by
    rw [hs]; omega
  apply List.ext_getElem (by rw [revSeg_length _ _ _ hle, revSeg_length d P L h, hs])
  intro t h1 h2
  rw [revSeg_getElem _ _ _ hle t h1, revSeg_getElem d P L h t h2]
  simp only [List.getElem_set]
  repeat' split
  all_goals first | rfl | omega | (apply getElem_idx; omega)

/-- The swap loop of `reverse!(v, s, n)` with `k` iterations left, at positions `P` and
`P + L - 1`, reverses those `L` elements. -/
theorem revLoop_spec {α : Type} (v : Arr α) (hv : v.WF) (h1 : v.axes.length = 1) :
    ∀ (k P L : Nat) (d : List α) (i r : I64), d.length = v.data.length → P + L ≤ v.data.length → L / 2 = k →
      i.val = (linearAxis v).lo.val + P → r.val = (linearAxis v).lo.val + P + L - 1 →
      revLoop k { v with data := d } i r = .ok { v with data := revSeg d P L } := by
  have hhi := linAx_len v hv
  have hlo := bnd (linearAxis v).lo
  have hhb := bnd (linearAxis v).hi
  have spos : ∀ (d : List α) (x : I64) (q : Nat), q < v.data.length → x.val = (linearAxis v).lo.val + q →
      refPos { v with data := d } [x] = some q := by
    intro d x q hq hx
    have hst := refLin_step v hv q (by omega)
    rw [if_pos hq] at hst
    rw [refPos_data]
    show refLinPos v x.val = some q
    rw [hx, ← wrap_id ((linearAxis v).lo.val + q) (by omega) (by omega), hst]
  intro k
  induction k with
  | zero =>
    intro P L d i r hd hPL hk _ _
    rw [revSeg_short d P L (by omega) (by omega)]
    rfl
  | succ k ih =>
    intro P L d i r hd hPL hk hi hr
    have hL : 2 ≤ L := by omega
    have hD := wf_data v d hv hd
    have hpr := spos d r (P + L - 1) (by omega) (by rw [hr]; omega)
    have hpi := spos d i P (by omega) hi
    have hpr1 := spos (d.set P (d[P + L - 1]'(by omega))) r (P + L - 1) (by omega) (by rw [hr]; omega)
    have hD1 := wf_data v (d.set P (d[P + L - 1]'(by omega))) hv (by simp [hd])
    have hi1 : (i + i64 1).val = (linearAxis v).lo.val + (P + 1 : Nat) := by
      rw [vadd, one_val, hi, wrap_id _ (by omega) (by omega)]; push_cast; omega
    have hr1 : (r - i64 1).val = (linearAxis v).lo.val + (P + 1 : Nat) + (L - 2 : Nat) - 1 := by
      rw [vsub, one_val, hr, wrap_id _ (by omega) (by omega)]; push_cast; omega
    have hd2 : ((d.set P (d[P + L - 1]'(by omega))).set (P + L - 1) (d[P]'(by omega))).length = v.data.length := by
      simp [hd]
    simp only [revLoop]
    rw [getindex_at _ hD [r] (P + L - 1) (Or.inr rfl) hpr, bind_ok,
      getindex_at _ hD [i] P (Or.inr rfl) hpi, bind_ok]
    dsimp only
    rw [setindex_at _ hD [i] P _ (Or.inr rfl) hpi, bind_ok]
    dsimp only
    rw [setindex_at _ hD1 [r] (P + L - 1) _ (Or.inr rfl) hpr1, bind_ok]
    dsimp only
    refine (ih (P + 1) (L - 2) _ _ _ hd2 (by omega) (by omega) hi1 hr1).trans ?_
    rw [revSeg_step d P L (by omega) hL]

/-- `reverse!(w, s, n)` for positions `P` to `P + L - 1` of a vector `w` with the axes and
style of `v` (`L ≥ 1`). -/
theorem reverseRange_spec {α : Type} (v : Arr α) (hv : v.WF) (h1 : v.axes.length = 1) (w : Arr α)
    (hax : w.axes = v.axes) (hsty : w.style = v.style) (hwl : w.data.length = v.data.length) (s n : I64)
    (P L : Nat) (hPL : P + L ≤ v.data.length) (hL : 1 ≤ L) (hs : s.val = (linearAxis v).lo.val + P)
    (hn : n.val = (linearAxis v).lo.val + P + L - 1) :
    reverseRange w s n = .ok { v with data := revSeg w.data P L } := by
  have hhi := linAx_len v hv
  have hlo := bnd (linearAxis v).lo
  have hhb := bnd (linearAxis v).hi
  have hlt := hv.2.2
  have hlen := hv.2.1
  rw [tmax_eq] at hlt
  obtain ⟨wax, wst, wd⟩ := w
  dsimp only at hax hsty hwl ⊢
  subst hax hsty
  have hlin : linearAxis ({ axes := v.axes, style := v.style, data := wd } : Arr α) = linearAxis v := rfl
  unfold reverseRange
  rw [hlin]
  by_cases hgt : n > s
  · have hL2 : 2 ≤ L := by rw [gt_iff_lt, lt_iff_val] at hgt; omega
    rw [if_pos hgt]
    dsimp only
    rw [if_neg (by rw [le_iff_val, le_iff_val]; omega), if_neg (by rw [le_iff_val, le_iff_val]; omega)]
    have hm1 : (n - i64 1 - s).val = (L : Int) - 2 := by
      rw [vsub, vsub, one_val, hn, hs, wrap_id ((linearAxis v).lo.val + P + L - 1 - 1) (by omega) (by omega),
        wrap_id _ (by omega) (by omega)]
      omega
    have hmv : (midpoint s (n - i64 1)).val = (linearAxis v).lo.val + P + ((L : Int) - 2) / 2 := by
      unfold midpoint
      rw [vadd, vlit, hm1, wu, Int.emod_eq_of_lt (by omega) (by omega), hs,
        wrap_id (((L : Int) - 2) / 2) (by omega) (by omega), wrap_id _ (by omega) (by omega)]
    have hsm : s ≤ midpoint s (n - i64 1) := by rw [le_iff_val, hmv, hs]; omega
    rw [if_pos hsm]
    have hk : ((midpoint s (n - i64 1)).val - s.val + 1).toNat = L / 2 := by
      rw [hmv, hs, show (linearAxis v).lo.val + ↑P + ((L : Int) - 2) / 2 - ((linearAxis v).lo.val + ↑P) + 1 =
        ((L / 2 : Nat) : Int) by omega, Int.toNat_natCast]
    rw [hk]
    exact revLoop_spec v hv h1 (L / 2) P L wd s n hwl hPL rfl hs hn
  · have hL1 : L = 1 := by rw [gt_iff_lt, lt_iff_val] at hgt; omega
    rw [if_neg hgt, revSeg_short wd P L (by omega) (by omega)]

theorem circshift_proven : CircshiftSpec := by
  intro α a shift ha h1
  dsimp only
  have hl := lengthA_val a ha
  have hhi := linAx_len a ha
  have hlo := bnd (linearAxis a).lo
  have hhb := bnd (linearAxis a).hi
  have hlt := ha.2.2
  have hlen := ha.2.1
  rw [tmax_eq] at hlt
  unfold circshiftBang
  dsimp only
  by_cases h0 : a.data.length = 0
  · rw [beq64, hl, zero_val, if_pos (by simp [h0])]
    cases a with
    | mk ax st dat =>
      dsimp only at h0 ⊢
      obtain rfl := List.eq_nil_of_length_eq_zero h0
      simp
  · rw [beq64, hl, zero_val, if_neg (by simp [h0])]
    have hq0 : 0 ≤ shift % (a.data.length : Int) := Int.emod_nonneg _ (by omega)
    have hq1 : shift % (a.data.length : Int) < a.data.length := Int.emod_lt_of_pos _ (by omega)
    have hmod : (modI shift (lengthA a)).val = shift % (a.data.length : Int) := by
      unfold modI; rw [hl, vlit, wrap_id _ (by omega) (by omega)]
    obtain ⟨q, hq⟩ : ∃ q : Nat, shift % (a.data.length : Int) = q := ⟨_, (Int.toNat_of_nonneg hq0).symm⟩
    rw [hq] at hmod hq1
    rw [hq, Int.toNat_natCast]
    by_cases hqz : q = 0
    · rw [beq64, hmod, zero_val, if_pos (by simp [hqz]), hqz, Nat.sub_zero, List.drop_length, List.take_length,
        List.nil_append]
    · rw [beq64, hmod, zero_val, if_neg (by simp [hqz])]
      have hq1' : q < a.data.length := by omega
      have hl1 : (revSeg a.data 0 (a.data.length - q)).length = a.data.length := revSeg_length _ _ _ (by omega)
      have hl2 : (revSeg (revSeg a.data 0 (a.data.length - q)) (a.data.length - q) q).length = a.data.length := by
        rw [revSeg_length _ _ _ (by omega), hl1]
      rw [reverseRange_spec a ha h1 a rfl rfl rfl (linearAxis a).lo ((linearAxis a).hi - modI shift (lengthA a)) 0
        (a.data.length - q) (by omega) (by omega) (by omega)
        (by rw [vsub, hmod, wrap_id _ (by omega) (by omega)]; omega), bind_ok]
      try dsimp only
      rw [reverseRange_spec a ha h1 { a with data := revSeg a.data 0 (a.data.length - q) } rfl rfl hl1
        ((linearAxis a).hi - modI shift (lengthA a) + i64 1)
        (linearAxis ({ a with data := revSeg a.data 0 (a.data.length - q) } : Arr α)).hi (a.data.length - q) q
        (by omega) (by omega)
        (by rw [vadd, vsub, hmod, one_val, wrap_id ((linearAxis a).hi.val - q) (by omega) (by omega),
              wrap_id _ (by omega) (by omega)]; omega)
        (by show (linearAxis a).hi.val = _; omega), bind_ok]
      try dsimp only
      rw [reverseRange_spec a ha h1
        { a with data := revSeg (revSeg a.data 0 (a.data.length - q)) (a.data.length - q) q } rfl rfl hl2
        (linearAxis ({ a with data := revSeg (revSeg a.data 0 (a.data.length - q)) (a.data.length - q) q } : Arr α)).lo
        (linearAxis ({ a with data := revSeg (revSeg a.data 0 (a.data.length - q)) (a.data.length - q) q } : Arr α)).hi
        0 a.data.length (by omega) (by omega)
        (by show (linearAxis a).lo.val = _; omega)
        (by show (linearAxis a).hi.val = _; omega)]
      try dsimp only
      congr 2
      have g1 := revSeg_getElem a.data 0 (a.data.length - q) (by omega)
      have g2 := revSeg_getElem (revSeg a.data 0 (a.data.length - q)) (a.data.length - q) q (by omega)
      have g3 := revSeg_getElem (revSeg (revSeg a.data 0 (a.data.length - q)) (a.data.length - q) q) 0
        a.data.length (by omega)
      apply List.ext_getElem (by
        rw [revSeg_length _ _ _ (by omega), hl2, List.length_append, List.length_drop, List.length_take]
        omega)
      intro t ht1 ht2
      have ht : t < a.data.length := by rw [revSeg_length _ _ _ (by omega), hl2] at ht1; exact ht1
      rw [g3, List.getElem_append]
      simp only [g2, g1, List.getElem_drop, List.getElem_take, List.length_drop]
      repeat' split
      all_goals first | rfl | omega | (apply getElem_idx; omega)

end JuliaLean.AbstractArraySpecs
