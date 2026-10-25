import JuliaLean.ReinterpretArrays.BytesProps
import JuliaLean.ReinterpretArrays.Wrap

/-!
Proofs of `RaGetCorrect` and `RaSetCorrect`: `_getindex_ra` and `_setindex_ra!`
(`base/reinterpretarray.jl`) read and write exactly the addressed bytes of the parent column.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

namespace BytesProof

/-! ## Monad and `Int` arithmetic -/

theorem bind_ok {α β : Type} (x : α) (f : α → Jl β) : ((Except.ok x : Jl α) >>= f) = f x := rfl

theorem bind_err {α β : Type} (e : JlError) (f : α → Jl β) :
    ((Except.error e : Jl α) >>= f) = .error e := rfl

theorem pure_ok {α : Type} (x : α) : (pure x : Jl α) = .ok x := rfl

theorem i64_min_nonpos : IntTy.min .i64 ≤ 0 := by decide

theorem i64_one_le_max : (1 : Int) ≤ IntTy.max .i64 := by decide

theorem wrapInt_nat (k : Nat) (h : (k : Int) ≤ IntTy.max .i64) : wrapInt .i64 (k : Int) = k :=
  wrapInt_of_inRange .i64 (k : Int) ⟨Int.le_trans i64_min_nonpos (Int.natCast_nonneg k), h⟩

theorem val_wrap (t : IntTy) (x : Int) : (JInt.wrap t x).val = wrapInt t x := rfl

theorem lit_nat (k : Nat) (h : (k : Int) ≤ IntTy.max .i64) : (JInt.lit .i64 (k : Int)).val = k := by
  rw [val_lit]
  exact wrapInt_nat k h

theorem wrap_nat (k : Nat) (h : (k : Int) ≤ IntTy.max .i64) :
    (JInt.wrap .i64 (k : Int)).val = k := by
  rw [val_wrap]
  exact wrapInt_nat k h

theorem mul_nat {a b : JInt64} {m n : Nat} (ha : a.val = m) (hb : b.val = n)
    (h : ((m * n : Nat) : Int) ≤ IntTy.max .i64) : (a * b).val = ((m * n : Nat) : Int) := by
  rw [val_mul, ha, hb, ← Int.natCast_mul]
  exact wrapInt_nat _ h

/-- A natural number below the column's byte count fits in an `Int`. -/
theorem fits {k P : Nat} (hP : (P : Int) ≤ IntTy.max .i64) (h : k ≤ P) :
    (k : Int) ≤ IntTy.max .i64 :=
  Int.le_trans (Int.ofNat_le.mpr h) hP

theorem div_nat {a b : JInt64} {m n : Nat} (ha : a.val = m) (hb : b.val = n) (hn : 0 < n) :
    JInt.div a b = .ok (JInt.wrap .i64 ((m / n : Nat) : Int)) := by
  unfold JInt.div
  rw [ite_eq_right (by omega), ite_eq_right (fun h => by have := h.2.2; omega), ha, hb]
  rw [show (m : Int).tdiv (n : Int) = ((m / n : Nat) : Int) from rfl]

theorem rem_nat {a b : JInt64} {m n : Nat} (ha : a.val = m) (hb : b.val = n) (hn : 0 < n) :
    JInt.remInt a b = .ok (JInt.wrap .i64 ((m % n : Nat) : Int)) := by
  unfold JInt.remInt
  rw [ite_eq_right (by omega), ha, hb]
  rw [show (m : Int).tmod (n : Int) = ((m % n : Nat) : Int) from rfl]

theorem lt_of_mul_lt {a b s : Nat} (h : a * s < b * s) : a < b := by
  rcases Nat.lt_or_ge a b with h' | h'
  · exact h'
  · have := Nat.mul_le_mul_right s h'
    omega

theorem le_of_mul_le {a b s : Nat} (hs : 0 < s) (h : a * s ≤ b * s) : a ≤ b := by
  rcases Nat.lt_or_ge b a with h' | h'
  · have := Nat.mul_le_mul_right s (show b + 1 ≤ a from h')
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · exact h'

/-- With `aligned_sizeof(T)` dividing `aligned_sizeof(S)`, an element of `T` starting at a
multiple of `aligned_sizeof(T)` never straddles two parent elements. -/
theorem rem_add_le {k sS sT : Nat} (hS : 0 < sS) (h : sS % sT = 0) :
    k * sT % sS + sT ≤ sS := by
  obtain ⟨m, hm⟩ : ∃ m, sS = m * sT :=
    ⟨sS / sT, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm⟩
  subst hm
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      simp at hS
    · exact h0
  rw [Nat.mul_mod_mul_right]
  have h2 := Nat.mul_le_mul_right sT (show k % m + 1 ≤ m from Nat.mod_lt k hm0)
  rw [Nat.add_mul, Nat.one_mul] at h2
  exact h2

/-! ## Byte lists -/

theorem take_app_add (a b : Bytes) (i : Nat) : (a ++ b).take (a.length + i) = a ++ b.take i := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.cons_append, List.length_cons, show a.length + 1 + i = (a.length + i) + 1 by omega,
      List.take_succ_cons, ih]
    rfl

theorem drop_app_add (a b : Bytes) (i : Nat) : (a ++ b).drop (a.length + i) = b.drop i := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.cons_append, List.length_cons, show a.length + 1 + i = (a.length + i) + 1 by omega,
      List.drop_succ_cons, ih]

theorem take_app_le : ∀ (a b : Bytes) (i : Nat), i ≤ a.length → (a ++ b).take i = a.take i
  | _, _, 0, _ => by simp
  | [], _, _ + 1, h => by simp at h
  | x :: a, b, i + 1, h => by
    rw [List.cons_append, List.take_succ_cons, List.take_succ_cons,
      take_app_le a b i (by simp at h; omega)]

theorem drop_app_le : ∀ (a b : Bytes) (i : Nat), i ≤ a.length → (a ++ b).drop i = a.drop i ++ b
  | _, _, 0, _ => by simp
  | [], _, _ + 1, h => by simp at h
  | x :: a, b, i + 1, h => by
    rw [List.cons_append, List.drop_succ_cons, List.drop_succ_cons,
      drop_app_le a b i (by simp at h; omega)]

theorem take_app (a b : Bytes) (m : Nat) : (a ++ b).take m = a.take m ++ b.take (m - a.length) := by
  by_cases h : m ≤ a.length
  · rw [take_app_le _ _ _ h, show m - a.length = 0 by omega, List.take_zero, List.append_nil]
  · have := take_app_add a b (m - a.length)
    rw [show a.length + (m - a.length) = m by omega] at this
    rw [this, List.take_of_length_le (show a.length ≤ m by omega)]

/-! ## Well-formed columns -/

theorem wf_cons {sS : Nat} {s : Bytes} {c : List Bytes} (h : WellFormed sS (s :: c)) :
    s.length = sS ∧ WellFormed sS c :=
  ⟨h s (by simp), fun x hx => h x (by simp [hx])⟩

theorem wf_drop {sS : Nat} {c : List Bytes} (h : WellFormed sS c) (j : Nat) :
    WellFormed sS (c.drop j) := fun x hx => h x (List.mem_of_mem_drop hx)

theorem wf_take {sS : Nat} {c : List Bytes} (h : WellFormed sS c) (j : Nat) :
    WellFormed sS (c.take j) := fun x hx => h x (List.mem_of_mem_take hx)

theorem wf_set {sS : Nat} {c : List Bytes} (h : WellFormed sS c) (e : Nat) (y : Bytes)
    (hy : y.length = sS) : WellFormed sS (c.set e y) := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | hx
  · exact h x hx
  · rw [hx]
    exact hy

theorem length_flatten_wf {sS : Nat} : ∀ (c : List Bytes), WellFormed sS c →
    c.flatten.length = c.length * sS
  | [], _ => by simp
  | s :: c, h => by
    obtain ⟨hs, hc⟩ := wf_cons h
    rw [List.flatten_cons, List.length_append, hs, length_flatten_wf c hc, List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem flatten_drop_mul {sS : Nat} : ∀ (c : List Bytes) (j : Nat), WellFormed sS c →
    (c.drop j).flatten = c.flatten.drop (j * sS)
  | [], _, _ => by simp
  | s :: c, 0, _ => by simp
  | s :: c, j + 1, h => by
    obtain ⟨hs, hc⟩ := wf_cons h
    rw [List.drop_succ_cons, flatten_drop_mul c j hc, List.flatten_cons,
      show (j + 1) * sS = s.length + j * sS by rw [hs, Nat.add_mul, Nat.one_mul, Nat.add_comm],
      drop_app_add]

theorem flatten_take_mul {sS : Nat} : ∀ (c : List Bytes) (n : Nat), WellFormed sS c →
    (c.take n).flatten = c.flatten.take (n * sS)
  | [], _, _ => by simp
  | s :: c, 0, _ => by simp
  | s :: c, n + 1, h => by
    obtain ⟨hs, hc⟩ := wf_cons h
    rw [List.take_succ_cons, List.flatten_cons, flatten_take_mul c n hc, List.flatten_cons,
      show (n + 1) * sS = s.length + n * sS by rw [hs, Nat.add_mul, Nat.one_mul, Nat.add_comm],
      take_app_add]

theorem length_flatten_take {sS : Nat} (c : List Bytes) (h : WellFormed sS c) (e : Nat)
    (he : e ≤ c.length) : (c.take e).flatten.length = e * sS := by
  rw [length_flatten_wf _ (wf_take h e), List.length_take, Nat.min_eq_left he]

theorem flatten_split (c : List Bytes) (e : Nat) (he : e < c.length) :
    c.flatten = (c.take e).flatten ++ (c[e] ++ (c.drop (e + 1)).flatten) := by
  have h : c = c.take e ++ c[e] :: c.drop (e + 1) := by
    rw [← List.drop_eq_getElem_cons he, List.take_append_drop]
  conv => lhs; rw [h]
  rw [List.flatten_append, List.flatten_cons]

theorem set_split : ∀ (c : List Bytes) (e : Nat) (y : Bytes), e < c.length →
    c.set e y = c.take e ++ y :: c.drop (e + 1)
  | [], _, _, h => by simp at h
  | s :: c, 0, y, _ => by simp
  | s :: c, e + 1, y, h => by
    rw [List.set_cons_succ, set_split c e y (by simp at h; omega)]
    simp

theorem drop_flatten_at {sS : Nat} (c : List Bytes) (h : WellFormed sS c) (e r : Nat)
    (he : e < c.length) (hr : r ≤ sS) :
    c.flatten.drop (e * sS + r) = c[e].drop r ++ (c.drop (e + 1)).flatten := by
  rw [flatten_split c e he, ← length_flatten_take c h e (Nat.le_of_lt he), drop_app_add,
    drop_app_le _ _ _ (by rw [h _ (List.getElem_mem he)]; exact hr)]

/-! ## `overwrite` -/

theorem overwrite_length (d s : Bytes) (o : Nat) (h : o + s.length ≤ d.length) :
    (overwrite d o s).length = d.length := by
  simp only [overwrite, List.length_append, List.length_take, List.length_drop]
  omega

theorem overwrite_getElem? (d s : Bytes) (o i : Nat) (h : o + s.length ≤ d.length) :
    (overwrite d o s)[i]? =
      if i < o then d[i]? else if i < o + s.length then s[i - o]? else d[i]? := by
  have ht : (d.take o).length = o := by rw [List.length_take]; omega
  unfold overwrite
  rw [List.append_assoc]
  by_cases h1 : i < o
  · rw [ite_eq_left h1, List.getElem?_append_left (by rw [ht]; exact h1), List.getElem?_take,
      ite_eq_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by rw [ht]; omega), ht]
    by_cases h2 : i < o + s.length
    · rw [ite_eq_left h2, List.getElem?_append_left (by omega)]
    · rw [ite_eq_right h2, List.getElem?_append_right (by omega), List.getElem?_drop,
        show o + s.length + (i - o - s.length) = i by omega]

theorem overwrite_overwrite (d s1 s2 : Bytes) (o : Nat)
    (h : o + s1.length + s2.length ≤ d.length) :
    overwrite (overwrite d o s1) (o + s1.length) s2 = overwrite d o (s1 ++ s2) := by
  have h1 : o + s1.length ≤ d.length := by omega
  apply List.ext_getElem?
  intro i
  rw [overwrite_getElem? (overwrite d o s1) s2 (o + s1.length) i
      (by rw [overwrite_length _ _ _ h1]; omega),
    overwrite_getElem? d s1 o i h1,
    overwrite_getElem? d (s1 ++ s2) o i (by rw [List.length_append]; omega),
    List.getElem?_append, List.length_append]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | (congr 1; omega)

theorem overwrite_nil (d : Bytes) (o : Nat) : overwrite d o [] = d := by
  simp [overwrite]

theorem overwrite_full (X w : Bytes) (h : w.length = X.length) : overwrite X 0 w = w := by
  unfold overwrite
  rw [List.take_zero, List.nil_append, Nat.zero_add, List.drop_of_length_le (by omega),
    List.append_nil]

theorem overwrite_app (A X B w : Bytes) (r : Nat) (h : r + w.length ≤ X.length) :
    overwrite (A ++ (X ++ B)) (A.length + r) w = A ++ (overwrite X r w ++ B) := by
  unfold overwrite
  rw [take_app_add, take_app_le _ _ _ (by omega), Nat.add_assoc, drop_app_add,
    drop_app_le _ _ _ h]
  simp only [List.append_assoc]

theorem set_overwrite_flatten {sS : Nat} (c : List Bytes) (hc : WellFormed sS c) (e r : Nat)
    (he : e < c.length) (w : Bytes) (hw : r + w.length ≤ sS) :
    (c.set e (overwrite c[e] r w)).flatten = overwrite c.flatten (e * sS + r) w := by
  have hce : c[e].length = sS := hc _ (List.getElem_mem he)
  rw [set_split c e _ he, List.flatten_append, List.flatten_cons, flatten_split c e he,
    ← length_flatten_take c hc e (Nat.le_of_lt he),
    overwrite_app _ _ _ _ _ (by rw [hce]; exact hw)]

theorem set_flatten {sS : Nat} (c : List Bytes) (hc : WellFormed sS c) (e : Nat)
    (he : e < c.length) (y : Bytes) (hy : y.length = sS) :
    (c.set e y).flatten = overwrite c.flatten (e * sS) y := by
  have hce : c[e].length = sS := hc _ (List.getElem_mem he)
  have := set_overwrite_flatten c hc e 0 he y (by omega)
  rw [overwrite_full _ _ (by rw [hy, hce]), Nat.add_zero] at this
  exact this

/-! ## Column access -/

theorem colGet_ok (c : List Bytes) (j : Int) (e : Nat) (hj : j = (e : Int) + 1)
    (he : e < c.length) : colGet c j = .ok c[e] := by
  unfold colGet
  rw [ite_eq_left ⟨by omega, by omega⟩, show (j - 1).toNat = e by omega]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he]

theorem colSet_ok (c : List Bytes) (j : Int) (e : Nat) (y : Bytes) (hj : j = (e : Int) + 1)
    (he : e < c.length) : colSet c j y = .ok (c.set e y) := by
  unfold colSet
  rw [ite_eq_left ⟨by omega, by omega⟩, show (j - 1).toNat = e by omega]

theorem mapM_colGet (col : List Bytes) (base : Nat) : ∀ (n s : Nat), base + s + n ≤ col.length →
    (List.range' s n).mapM (fun i : Nat => colGet col ((base : Int) + ((i : Int) + 1))) =
      .ok ((col.drop (base + s)).take n)
  | 0, _, _ => rfl
  | n + 1, s, h => by
    have hs : base + s < col.length := by omega
    rw [List.range'_succ, List.mapM_cons, colGet_ok col _ (base + s) (by omega) hs,
      mapM_colGet col base n (s + 1) (by omega), List.drop_eq_getElem_cons hs,
      List.take_succ_cons, show base + (s + 1) = base + s + 1 by omega]
    rfl

theorem foldlM_colSet {sS : Nat} (v F : Bytes) (base : Nat) :
    ∀ (n s : Nat) (c : List Bytes), WellFormed sS c → c.length * sS = F.length →
    base + s + n ≤ c.length → (s + n) * sS ≤ v.length →
    c.flatten = overwrite F (base * sS) (v.take (s * sS)) →
    ∃ c', (List.range' s n).foldlM (fun c (i : Nat) => colSet c ((base : Int) + ((i : Int) + 1))
        ((v.drop (i * sS)).take sS)) c = .ok c' ∧
      WellFormed sS c' ∧ c'.length = c.length ∧
      c'.flatten = overwrite F (base * sS) (v.take ((s + n) * sS))
  | 0, _, c, hc, _, _, _, hfl => ⟨c, rfl, hc, rfl, by rw [Nat.add_zero]; exact hfl⟩
  | n + 1, s, c, hc, hcl, hb, hvl, hfl => by
    have he : base + s < c.length := by omega
    have hs1 : (s + 1) * sS ≤ v.length :=
      Nat.le_trans (Nat.mul_le_mul_right sS (by omega)) hvl
    rw [Nat.add_mul, Nat.one_mul] at hs1
    have hw : ((v.drop (s * sS)).take sS).length = sS := by
      rw [List.length_take, List.length_drop]
      omega
    have hbF : (base + s + 1) * sS ≤ F.length := by
      rw [← hcl]
      exact Nat.mul_le_mul_right sS (by omega)
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at hbF
    have hset := colSet_ok c ((base : Int) + ((s : Int) + 1)) (base + s)
      ((v.drop (s * sS)).take sS) (by omega) he
    have htl : (v.take (s * sS)).length = s * sS := by
      rw [List.length_take]
      omega
    obtain ⟨c', hrun, h1, h2, h3⟩ := foldlM_colSet v F base n (s + 1)
      (c.set (base + s) ((v.drop (s * sS)).take sS)) (wf_set hc _ _ hw)
      (by rw [List.length_set]; exact hcl) (by rw [List.length_set]; omega)
      (by rw [show s + 1 + n = s + (n + 1) by omega]; exact hvl)
      (by
        rw [set_flatten c hc _ he _ hw, hfl,
          show (base + s) * sS = base * sS + (v.take (s * sS)).length by
            rw [htl, Nat.add_mul],
          overwrite_overwrite F _ _ _ (by rw [htl, hw]; omega),
          show (s + 1) * sS = s * sS + sS by rw [Nat.add_mul, Nat.one_mul], List.take_add])
    refine ⟨c', ?_, h1, by rw [h2, List.length_set], ?_⟩
    · rw [List.range'_succ, List.foldlM_cons, hset, bind_ok]
      exact hrun
    · rw [h3, show s + 1 + n = s + (n + 1) by omega]

/-! ## Byte loops -/

theorem raGetLoop_ok (sS sT : Nat) : ∀ (elems : List Bytes) (sidx copied : Nat) (acc : Bytes),
    WellFormed sS elems → sidx ≤ sS → copied ≤ sT →
    sT - copied ≤ (elems.flatten.drop sidx).length →
    raGetLoop sS sT sidx copied elems acc =
      .ok (acc ++ (elems.flatten.drop sidx).take (sT - copied))
  | [], sidx, copied, acc, _, _, _, h => by
    simp only [List.flatten_nil, List.drop_nil, List.length_nil] at h
    rw [raGetLoop, ite_eq_right (by omega), show sT - copied = 0 by omega]
    simp
  | s :: rest, sidx, copied, acc, hwf, hs, hc, h => by
    obtain ⟨hsl, hwr⟩ := wf_cons hwf
    rw [List.flatten_cons, drop_app_le _ _ _ (by omega)] at h ⊢
    rw [List.length_append, List.length_drop] at h
    by_cases hlt : copied < sT
    · rw [raGetLoop, ite_eq_left hlt]
      dsimp only
      have e1 : (s.drop sidx).take (min (sS - sidx) (sT - copied)) =
          (s.drop sidx).take (sT - copied) := by
        by_cases hm : sS - sidx ≤ sT - copied
        · rw [Nat.min_eq_left hm, List.take_of_length_le (by rw [List.length_drop]; omega),
            List.take_of_length_le (by rw [List.length_drop]; omega)]
        · rw [Nat.min_eq_right (by omega)]
      have e2 : sT - (copied + min (sS - sidx) (sT - copied)) =
          sT - copied - (s.drop sidx).length := by
        rw [List.length_drop]
        omega
      rw [raGetLoop_ok sS sT rest 0 (copied + min (sS - sidx) (sT - copied)) _ hwr (Nat.zero_le _)
          (by omega) (by rw [List.drop_zero]; omega),
        List.drop_zero, e1, e2, take_app]
      simp only [List.append_assoc]
    · rw [raGetLoop, ite_eq_right hlt, show sT - copied = 0 by omega]
      simp

theorem raSetMain_ok {sS sT : Nat} (hS : 0 < sS) (q p : Nat) (v F : Bytes) (hv : v.length = sT)
    (hpF : p + sT ≤ F.length) :
    ∀ (fuel : Nat) (c : List Bytes) (s : Bytes) (copied : Nat) (i : Int) (e : Nat),
    WellFormed sS c → c.length * sS = F.length → s.length = sS → copied ≤ sT →
    c.flatten = overwrite F p (v.take copied) →
    (copied < sT → p + copied = e * sS ∧ (q : Int) + i = e + 1) → sT - copied ≤ fuel →
    ∃ c' s' copied' i' e',
      raSet.raSetMain sS sT (q : Int) v c s copied i fuel = .ok (c', s', copied', i') ∧
      WellFormed sS c' ∧ c'.length = c.length ∧ copied' ≤ sT ∧
      c'.flatten = overwrite F p (v.take copied') ∧
      (copied' < sT → p + copied' = e' * sS ∧ (q : Int) + i' = e' + 1) ∧
      ¬ (copied' < sT ∧ sT - copied' > sS)
  | 0, c, s, copied, i, e, hc, _, _, hcp, hfl, hinv, hfuel =>
    ⟨c, s, copied, i, e, rfl, hc, rfl, hcp, hfl, hinv, by omega⟩
  | fuel + 1, c, s, copied, i, e, hc, hcl, hs, hcp, hfl, hinv, hfuel => by
    by_cases hcond : copied < sT ∧ sT - copied > sS
    · obtain ⟨he1, hqi⟩ := hinv hcond.1
      have heL : e < c.length := lt_of_mul_lt (by omega : e * sS < c.length * sS)
      have hw : ((v.drop copied).take (min sS (sT - copied))).length = sS := by
        rw [List.length_take, List.length_drop, hv]
        omega
      have hov : overwrite s 0 ((v.drop copied).take (min sS (sT - copied))) =
          (v.drop copied).take (min sS (sT - copied)) := overwrite_full _ _ (by rw [hw, hs])
      have hset := colSet_ok c ((q : Int) + i) e ((v.drop copied).take (min sS (sT - copied)))
        hqi heL
      have htl : (v.take copied).length = copied := by
        rw [List.length_take, hv]
        omega
      obtain ⟨c', s', cp', i', e', hrun, h1, h2, h3, h4, h5, h6⟩ :=
        raSetMain_ok hS q p v F hv hpF fuel
          (c.set e ((v.drop copied).take (min sS (sT - copied))))
          ((v.drop copied).take (min sS (sT - copied))) (copied + min sS (sT - copied)) (i + 1)
          (e + 1) (wf_set hc e _ hw) (by rw [List.length_set]; exact hcl) hw (by omega)
          (by
            rw [set_flatten c hc e heL _ hw, hfl,
              show e * sS = p + (v.take copied).length by rw [htl]; omega,
              overwrite_overwrite F _ _ _ (by rw [htl, hw]; omega), ← List.take_add])
          (fun _ => ⟨by rw [Nat.add_mul, Nat.one_mul]; omega, by omega⟩) (by omega)
      refine ⟨c', s', cp', i', e', ?_, h1, by rw [h2, List.length_set], h3, h4, h5, h6⟩
      simp only [raSet.raSetMain]
      rw [ite_eq_left hcond]
      simp only [hov, hset, bind_ok]
      exact hrun
    · refine ⟨c, s, copied, i, e, ?_, hc, rfl, hcp, hfl, hinv, hcond⟩
      simp only [raSet.raSetMain]
      rw [ite_eq_right hcond]

theorem raSetTail_ok {sS sT : Nat} (q p : Nat) (v F : Bytes) (hv : v.length = sT)
    (hpF : p + sT ≤ F.length) (c : List Bytes) (copied : Nat) (i : Int) (e : Nat)
    (hc : WellFormed sS c) (hcl : c.length * sS = F.length) (hcp : copied ≤ sT)
    (hfl : c.flatten = overwrite F p (v.take copied))
    (hinv : copied < sT → p + copied = e * sS ∧ (q : Int) + i = e + 1)
    (hstop : ¬ (copied < sT ∧ sT - copied > sS)) :
    ∃ c', (if copied < sT then (colGet c ((q : Int) + i) >>= fun s =>
        colSet c ((q : Int) + i) (overwrite s 0 ((v.drop copied).take (min sS (sT - copied)))))
      else pure c) = .ok c' ∧ WellFormed sS c' ∧ c'.length = c.length ∧
      c'.flatten = overwrite F p v := by
  by_cases hlt : copied < sT
  · obtain ⟨he1, hqi⟩ := hinv hlt
    have heL : e < c.length := lt_of_mul_lt (by omega : e * sS < c.length * sS)
    have hce : c[e].length = sS := hc _ (List.getElem_mem heL)
    have hwl : ((v.drop copied).take (min sS (sT - copied))).length = sT - copied := by
      rw [List.length_take, List.length_drop, hv]
      omega
    have htl : (v.take copied).length = copied := by
      rw [List.length_take, hv]
      omega
    rw [ite_eq_left hlt, colGet_ok c _ e hqi heL]
    simp only [bind_ok]
    rw [colSet_ok c _ e _ hqi heL]
    refine ⟨_, rfl, wf_set hc e _ ?_, by rw [List.length_set], ?_⟩
    · rw [overwrite_length _ _ _ (by rw [hwl, hce]; omega), hce]
    · rw [set_overwrite_flatten c hc e 0 heL _ (by rw [hwl]; omega), Nat.add_zero, hfl,
        show e * sS = p + (v.take copied).length by rw [htl]; omega,
        overwrite_overwrite F _ _ _ (by rw [htl, hwl]; omega), ← List.take_add,
        List.take_of_length_le (by rw [hv]; omega)]
  · rw [ite_eq_right hlt]
    refine ⟨c, rfl, hc, rfl, ?_⟩
    rw [hfl, List.take_of_length_le (by rw [hv]; omega)]

/-! ## Sizes and indices -/

theorem lit_mul_lit (L sS : Nat) (hB : ((L * sS : Nat) : Int) ≤ IntTy.max .i64) :
    (JInt.lit .i64 (L : Int) * JInt.lit .i64 (sS : Int)).val = ((L * sS : Nat) : Int) := by
  rw [val_mul, val_lit, val_lit, wrapInt_mul, ← Int.natCast_mul]
  exact wrapInt_nat _ hB

theorem newCheck_mod {sS sT P : Nat} {d : JInt64} (hT : 0 < sT) (hTM : (sT : Int) ≤ IntTy.max .i64)
    (hmul : (d * JInt.lit .i64 (sS : Int)).val = (P : Int))
    (hchk : raNewCheck sS sT d = .ok ()) : P % sT = 0 := by
  have hTv : (JInt.lit .i64 (sT : Int)).val = sT := lit_nat sT hTM
  have hr : (JInt.wrap .i64 ((P % sT : Nat) : Int)).val = ((P % sT : Nat) : Int) :=
    wrap_nat _ (Int.le_trans (Int.ofNat_le.mpr (Nat.le_of_lt (Nat.mod_lt _ hT))) hTM)
  have e : raNewCheck sS sT d = (JInt.remInt (d * JInt.lit .i64 (sS : Int)) (JInt.lit .i64 (sT : Int))
      >>= fun r => if r.val = 0 then pure () else throw (JlError.argumentError
        "non-integral first dimension")) := by
    unfold raNewCheck
    exact ite_eq_right (Nat.pos_iff_ne_zero.mp hT)
  by_cases h0 : (JInt.wrap .i64 ((P % sT : Nat) : Int)).val = 0
  · rw [hr] at h0
    exact Int.ofNat_inj.mp h0
  · have hbad : raNewCheck sS sT d = .error (.argumentError "non-integral first dimension") := by
      rw [e, rem_nat hmul hTv hT, bind_ok]
      exact ite_eq_right h0
    rw [hbad] at hchk
    exact absurd hchk (fun h => nomatch h)

theorem size1_val {sS sT P : Nat} {d sz1 : JInt64} (hT : 0 < sT)
    (hTM : (sT : Int) ≤ IntTy.max .i64) (hB : (P : Int) ≤ IntTy.max .i64)
    (hmul : (d * JInt.lit .i64 (sS : Int)).val = (P : Int))
    (hsz : raSize1 sS sT d = .ok sz1) : sz1.val = ((P / sT : Nat) : Int) := by
  have hTv : (JInt.lit .i64 (sT : Int)).val = sT := lit_nat sT hTM
  have e : raSize1 sS sT d = JInt.div (d * JInt.lit .i64 (sS : Int)) (JInt.lit .i64 (sT : Int)) := by
    unfold raSize1
    exact ite_eq_right (Nat.pos_iff_ne_zero.mp hT)
  have h2 : JInt.wrap .i64 ((P / sT : Nat) : Int) = sz1 :=
    Except.ok.inj ((div_nat hmul hTv hT).symm.trans (e.symm.trans hsz))
  subst h2
  exact wrap_nat _ (fits hB (Nat.div_le_self _ _))

theorem size_facts {sS sT : Nat} {col : List Bytes} {sz1 : JInt64} (hT : 0 < sT)
    (hTM : sT ≤ IntTy.max .i64) (hLS : col.length * sS ≤ IntTy.max .i64)
    (hchk : raNewCheck sS sT (JInt.lit .i64 col.length) = .ok ())
    (hsz : raSize1 sS sT (JInt.lit .i64 col.length) = .ok sz1) :
    ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64 ∧
      ∃ N : Nat, sz1.val = N ∧ N * sT = col.length * sS := by
  have hB : ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64 := by exact_mod_cast hLS
  have hmul := lit_mul_lit col.length sS hB
  have hmod := newCheck_mod hT hTM hmul hchk
  exact ⟨hB, col.length * sS / sT, size1_val hT hTM hB hmul hsz,
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)⟩

theorem index_facts {sS sT : Nat} {col : List Bytes} {i1 : JInt64} {k : Nat} (hS : 0 < sS)
    (hT : 0 < sT) (hk : i1.val = (k : Int) + 1) (hkb : k * sT + sT ≤ col.length * sS)
    (hB : ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64) :
    JInt.div ((i1 - JInt.lit .i64 1) * JInt.lit .i64 (sT : Int)) (JInt.lit .i64 (sS : Int)) =
        .ok (JInt.wrap .i64 ((k * sT / sS : Nat) : Int)) ∧
      JInt.remInt ((i1 - JInt.lit .i64 1) * JInt.lit .i64 (sT : Int)) (JInt.lit .i64 (sS : Int)) =
        .ok (JInt.wrap .i64 ((k * sT % sS : Nat) : Int)) ∧
      (JInt.wrap .i64 ((k * sT / sS : Nat) : Int)).val = ((k * sT / sS : Nat) : Int) ∧
      (JInt.wrap .i64 ((k * sT % sS : Nat) : Int)).val = ((k * sT % sS : Nat) : Int) := by
  have hL1 : 1 ≤ col.length := by
    rcases Nat.eq_zero_or_pos col.length with h0 | h0
    · rw [h0, Nat.zero_mul] at hkb
      omega
    · exact h0
  have hSle : sS ≤ col.length * sS := by
    have := Nat.mul_le_mul_right sS hL1
    rw [Nat.one_mul] at this
    exact this
  have hkle : k ≤ k * sT := by
    have := Nat.mul_le_mul_left k (show 1 ≤ sT by omega)
    rw [Nat.mul_one] at this
    exact this
  have h1v : (JInt.lit .i64 1).val = 1 := by
    rw [val_lit]
    exact wrapInt_of_inRange .i64 1 ⟨Int.le_trans i64_min_nonpos (by decide), i64_one_le_max⟩
  have hkP : k * sT ≤ col.length * sS := Nat.le_trans (Nat.le_add_right _ _) hkb
  have hsub : (i1 - JInt.lit .i64 1).val = (k : Int) := by
    rw [val_sub, hk, h1v, show (k : Int) + 1 - 1 = k by omega]
    exact wrapInt_nat k (fits hB (Nat.le_trans hkle hkP))
  have hTv := lit_nat sT (fits hB (Nat.le_trans (Nat.le_add_left _ _) hkb))
  have hSv := lit_nat sS (fits hB hSle)
  have hx := mul_nat hsub hTv (fits hB hkP)
  have hqle : k * sT / sS ≤ k * sT := Nat.div_le_self _ _
  have hrl : k * sT % sS < sS := Nat.mod_lt _ hS
  exact ⟨div_nat hx hSv hS, rem_nat hx hSv hS, wrap_nat _ (fits hB (Nat.le_trans hqle hkP)),
    wrap_nat _ (fits hB (Nat.le_trans (Nat.le_of_lt hrl) hSle))⟩

end BytesProof

open BytesProof

/-- `reinterpret(T, A)[i1, J...]` returns exactly bytes `(i1-1)*sT+1 : i1*sT` of the parent
column and throws `BoundsError` outside `1:size(R, 1)`. -/
theorem raGetCorrect : RaGetCorrect := by
  intro sS sT scalar col i1 sz1 hS hT hTM hsc hwf hLS hchk hsz
  obtain ⟨hB, N, hN, hNT⟩ := size_facts hT hTM hLS hchk hsz
  have hT0 : ¬ sT = 0 := by omega
  have hFl : col.flatten.length = col.length * sS := length_flatten_wf col hwf
  by_cases hin : 1 ≤ i1.val ∧ i1.val ≤ sz1.val
  · rw [ite_eq_left hin]
    obtain ⟨k, hk⟩ : ∃ k : Nat, i1.val = (k : Int) + 1 := ⟨(i1.val - 1).toNat, by omega⟩
    have hkN : k + 1 ≤ N := by omega
    have hkb : k * sT + sT ≤ col.length * sS := by
      have := Nat.mul_le_mul_right sT hkN
      rw [Nat.add_mul, Nat.one_mul, hNT] at this
      exact this
    have hexp : expectedBytes sT col i1.val = (col.flatten.drop (k * sT)).take sT := by
      unfold expectedBytes
      rw [show i1.val.toNat - 1 = k by omega]
    rw [hexp]
    cases scalar with
    | true =>
      have hST : sS = sT := hsc rfl
      subst hST
      have hkL : k < col.length := lt_of_mul_lt (by omega : k * sS < col.length * sS)
      have hck : col[k].length = sS := hwf _ (List.getElem_mem hkL)
      simp only [raGet, hT0, ↓reduceIte]
      rw [colGet_ok col i1.val k hk hkL, ← flatten_drop_mul col k hwf,
        List.drop_eq_getElem_cons hkL, List.flatten_cons,
        take_app_le _ _ _ (Nat.le_of_eq hck.symm), List.take_of_length_le (Nat.le_of_eq hck)]
    | false =>
      obtain ⟨hdiv, hrem, hqv, hrv⟩ := index_facts hS hT hk hkb hB
      have hcf : checkFirst sz1 i1 = .ok () := by
        unfold checkFirst
        rw [ite_eq_left hin]
      have hdm : k * sT / sS * sS + k * sT % sS = k * sT := by
        have := Nat.div_add_mod (k * sT) sS
        have h2 := Nat.mul_comm sS (k * sT / sS)
        omega
      have hrl : k * sT % sS < sS := Nat.mod_lt _ hS
      simp only [raGet, hT0, ↓reduceIte, Bool.false_eq_true, hcf, bind_ok, hdiv, hrem, hqv, hrv,
        Int.toNat_natCast]
      by_cases h1 : sT % sS = 0
      · rw [ite_eq_left h1]
        obtain ⟨n, hn⟩ : ∃ n, sT = n * sS :=
          ⟨sT / sS, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h1)).symm⟩
        have hn' : sT / sS = n := by rw [hn, Nat.mul_div_cancel _ hS]
        have hq : k * sT / sS = k * n := by rw [hn, ← Nat.mul_assoc, Nat.mul_div_cancel _ hS]
        have hkn : k * n + n ≤ col.length := by
          apply le_of_mul_le hS
          rw [Nat.add_mul, Nat.mul_assoc, ← hn]
          exact hkb
        rw [hq, hn', List.range_eq_range', mapM_colGet col (k * n) n 0 (by omega), bind_ok,
          pure_ok, Nat.add_zero, flatten_take_mul _ n (wf_drop hwf _), flatten_drop_mul col _ hwf,
          Nat.mul_assoc, ← hn]
      · rw [ite_eq_right h1]
        have hqL : k * sT / sS < col.length :=
          lt_of_mul_lt (by omega : k * sT / sS * sS < col.length * sS)
        by_cases h2 : sS % sT = 0
        · rw [ite_eq_left h2]
          have hrs : k * sT % sS + sT ≤ sS := rem_add_le hS h2
          have hce : col[k * sT / sS].length = sS := hwf _ (List.getElem_mem hqL)
          rw [colGet_ok col _ (k * sT / sS) rfl hqL, bind_ok, pure_ok,
            show col.flatten.drop (k * sT) = col.flatten.drop (k * sT / sS * sS + k * sT % sS) by
              rw [hdm],
            drop_flatten_at col hwf _ _ hqL (by omega),
            take_app_le _ _ _ (by rw [List.length_drop, hce]; omega)]
        · rw [ite_eq_right h2]
          have hlen : sT - 0 ≤ ((col.drop (k * sT / sS)).flatten.drop (k * sT % sS)).length := by
            rw [flatten_drop_mul col _ hwf, List.drop_drop, hdm, List.length_drop, hFl]
            omega
          rw [raGetLoop_ok sS sT (col.drop (k * sT / sS)) (k * sT % sS) 0 [] (wf_drop hwf _)
              (Nat.le_of_lt hrl) (Nat.zero_le _) hlen,
            flatten_drop_mul col _ hwf, List.drop_drop, hdm, List.nil_append, Nat.sub_zero]
  · rw [ite_eq_right hin]
    cases scalar with
    | true =>
      have hST : sS = sT := hsc rfl
      subst hST
      have hNL : N = col.length := Nat.eq_of_mul_eq_mul_right hS hNT
      simp only [raGet, hT0, ↓reduceIte]
      unfold colGet
      rw [ite_eq_right (by omega)]
    | false =>
      have hcf : checkFirst sz1 i1 = .error .boundsError := by
        unfold checkFirst
        rw [ite_eq_right hin]
      simp only [raGet, hT0, ↓reduceIte, Bool.false_eq_true, hcf, bind_err]

/-- `reinterpret(T, A)[i1, J...] = v` overwrites exactly bytes `(i1-1)*sT+1 : i1*sT` of the parent
column with `v`, keeps every other byte, and throws `BoundsError` outside `1:size(R, 1)`. -/
theorem raSetCorrect : RaSetCorrect := by
  intro sS sT scalar col i1 sz1 v hS hT hTM hsc hwf hv hLS hchk hsz
  obtain ⟨hB, N, hN, hNT⟩ := size_facts hT hTM hLS hchk hsz
  have hT0 : ¬ sT = 0 := by omega
  have hFl : col.flatten.length = col.length * sS := length_flatten_wf col hwf
  by_cases hin : 1 ≤ i1.val ∧ i1.val ≤ sz1.val
  · rw [ite_eq_left hin]
    obtain ⟨k, hk⟩ : ∃ k : Nat, i1.val = (k : Int) + 1 := ⟨(i1.val - 1).toNat, by omega⟩
    have hkN : k + 1 ≤ N := by omega
    have hkb : k * sT + sT ≤ col.length * sS := by
      have := Nat.mul_le_mul_right sT hkN
      rw [Nat.add_mul, Nat.one_mul, hNT] at this
      exact this
    rw [show i1.val.toNat - 1 = k by omega]
    cases scalar with
    | true =>
      have hST : sS = sT := hsc rfl
      subst hST
      have hkL : k < col.length := lt_of_mul_lt (by omega : k * sS < col.length * sS)
      refine ⟨col.set k v, ?_, wf_set hwf k v hv, by rw [List.length_set],
        set_flatten col hwf k hkL v hv⟩
      simp only [raSet, hT0, ↓reduceIte]
      exact colSet_ok col i1.val k v hk hkL
    | false =>
      obtain ⟨hdiv, hrem, hqv, hrv⟩ := index_facts hS hT hk hkb hB
      have hcf : checkFirst sz1 i1 = .ok () := by
        unfold checkFirst
        rw [ite_eq_left hin]
      have hdm : k * sT / sS * sS + k * sT % sS = k * sT := by
        have := Nat.div_add_mod (k * sT) sS
        have h2 := Nat.mul_comm sS (k * sT / sS)
        omega
      have hrl : k * sT % sS < sS := Nat.mod_lt _ hS
      have hpF : k * sT + sT ≤ col.flatten.length := by
        rw [hFl]
        exact hkb
      simp only [raSet, hT0, ↓reduceIte, Bool.false_eq_true, hcf, bind_ok, hdiv, hrem, hqv, hrv,
        Int.toNat_natCast]
      by_cases h1 : sT % sS = 0
      · rw [ite_eq_left h1]
        obtain ⟨n, hn⟩ : ∃ n, sT = n * sS :=
          ⟨sT / sS, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h1)).symm⟩
        have hn' : sT / sS = n := by rw [hn, Nat.mul_div_cancel _ hS]
        have hq : k * sT / sS = k * n := by rw [hn, ← Nat.mul_assoc, Nat.mul_div_cancel _ hS]
        have hkn : k * n + n ≤ col.length := by
          apply le_of_mul_le hS
          rw [Nat.add_mul, Nat.mul_assoc, ← hn]
          exact hkb
        rw [hq, hn', List.range_eq_range']
        obtain ⟨c', hrun, h1', h2', h3'⟩ := foldlM_colSet v col.flatten (k * n) n 0 col hwf
          hFl.symm (by omega) (Nat.le_of_eq (by rw [Nat.zero_add, hv, hn]))
          (by rw [Nat.zero_mul, List.take_zero, overwrite_nil])
        refine ⟨c', hrun, h1', h2', ?_⟩
        rw [h3', Nat.zero_add, List.take_of_length_le (Nat.le_of_eq (by rw [hv, hn])),
          Nat.mul_assoc, ← hn]
      · rw [ite_eq_right h1]
        have hqL : k * sT / sS < col.length :=
          lt_of_mul_lt (by omega : k * sT / sS * sS < col.length * sS)
        have hce : col[k * sT / sS].length = sS := hwf _ (List.getElem_mem hqL)
        by_cases h2 : sS % sT = 0
        · rw [ite_eq_left h2]
          have hrs : k * sT % sS + sT ≤ sS := rem_add_le hS h2
          rw [colGet_ok col _ (k * sT / sS) rfl hqL, bind_ok,
            colSet_ok col _ (k * sT / sS) _ rfl hqL]
          refine ⟨_, rfl, wf_set hwf _ _ ?_, by rw [List.length_set], ?_⟩
          · rw [overwrite_length _ _ _ (by rw [hce, hv]; omega), hce]
          · rw [set_overwrite_flatten col hwf _ _ hqL v (by rw [hv]; omega), hdm]
        · rw [ite_eq_right h2]
          by_cases hr0 : k * sT % sS = 0
          · simp only [hr0, ne_eq, eq_self, not_true_eq_false, ↓reduceIte, pure_ok, bind_ok]
            obtain ⟨c', s', cp', i', e', hrun, h1', h2', h3', h4', h5', h6'⟩ :=
              raSetMain_ok hS (k * sT / sS) (k * sT) v col.flatten hv hpF sT col
                (List.replicate sS 0) 0 1 (k * sT / sS) hwf hFl.symm (by simp) (Nat.zero_le _)
                (by rw [List.take_zero, overwrite_nil]) (fun _ => ⟨by omega, by omega⟩)
                (by omega)
            rw [hrun, bind_ok]
            obtain ⟨c'', hc1, hc2, hc3, hc4⟩ := raSetTail_ok (k * sT / sS) (k * sT) v col.flatten
              hv hpF c' cp' i' e' h1' (by rw [h2']; exact hFl.symm) h3' h4' h5' h6'
            exact ⟨c'', hc1, hc2, by rw [hc3, h2'], hc4⟩
          · have hg := colGet_ok col ((k * sT / sS : Nat) + 1 : Int) (k * sT / sS) rfl hqL
            have hwl : (v.take (min (sS - k * sT % sS) sT)).length = min (sS - k * sT % sS) sT := by
              rw [List.length_take, hv]
              omega
            have hs1 : (overwrite col[k * sT / sS] (k * sT % sS)
                (v.take (min (sS - k * sT % sS) sT))).length = sS := by
              rw [overwrite_length _ _ _ (by rw [hwl, hce]; omega), hce]
            have hs := colSet_ok col ((k * sT / sS : Nat) + 1 : Int) (k * sT / sS)
              (overwrite col[k * sT / sS] (k * sT % sS) (v.take (min (sS - k * sT % sS) sT)))
              rfl hqL
            simp only [hr0, ne_eq, not_false_eq_true, ↓reduceIte, hg, bind_ok, hs, pure_ok,
              Nat.zero_add, Int.reduceAdd]
            obtain ⟨c', s', cp', i', e', hrun, h1', h2', h3', h4', h5', h6'⟩ :=
              raSetMain_ok hS (k * sT / sS) (k * sT) v col.flatten hv hpF sT
                (col.set (k * sT / sS) (overwrite col[k * sT / sS] (k * sT % sS)
                  (v.take (min (sS - k * sT % sS) sT))))
                (overwrite col[k * sT / sS] (k * sT % sS) (v.take (min (sS - k * sT % sS) sT)))
                (min (sS - k * sT % sS) sT) 2 (k * sT / sS + 1) (wf_set hwf _ _ hs1)
                (by rw [List.length_set]; exact hFl.symm) hs1 (by omega)
                (by rw [set_overwrite_flatten col hwf _ _ hqL _ (by rw [hwl]; omega), hdm])
                (fun _ => ⟨by rw [Nat.add_mul, Nat.one_mul]; omega, by omega⟩) (by omega)
            rw [hrun, bind_ok]
            obtain ⟨c'', hc1, hc2, hc3, hc4⟩ := raSetTail_ok (k * sT / sS) (k * sT) v col.flatten
              hv hpF c' cp' i' e' h1' (by rw [h2', List.length_set]; exact hFl.symm) h3' h4' h5'
              h6'
            exact ⟨c'', hc1, hc2, by rw [hc3, h2', List.length_set], hc4⟩
  · rw [ite_eq_right hin]
    cases scalar with
    | true =>
      have hST : sS = sT := hsc rfl
      subst hST
      have hNL : N = col.length := Nat.eq_of_mul_eq_mul_right hS hNT
      simp only [raSet, hT0, ↓reduceIte]
      unfold colSet
      rw [ite_eq_right (by omega)]
    | false =>
      have hcf : checkFirst sz1 i1 = .error .boundsError := by
        unfold checkFirst
        rw [ite_eq_right hin]
      simp only [raSet, hT0, ↓reduceIte, Bool.false_eq_true, hcf, bind_err]

end JuliaLean.ReinterpretArrays
