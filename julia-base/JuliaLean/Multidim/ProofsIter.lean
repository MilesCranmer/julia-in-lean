import JuliaLean.Multidim.Props

/-! Proofs that `CartesianIndices` iteration (forward and reverse) enumerates `elems R`
in order, and that `findfirst` on an array with no empty dimension returns `firstTrue`. -/

namespace JuliaLean.Multidim

/-! ## One range -/

/-- The `j`-th element of `r`. -/
private def ge (r : Rng) (j : Nat) : I64 := JInt.wrap .i64 (r.elem j)

/-- The result of `iterNext`/`revNext` for an `inc`/`dec` outcome. -/
private def opt (p : Bool × List I64) : Option (List I64) := if p.1 then some p.2 else none

private theorem ge_val {r : Rng} (hr : r.WF) {j : Nat} (hj : j < r.len) :
    (ge r j).val = r.elem j :=
  wrapInt_of_inRange .i64 _ (hr.2 j hj)

private theorem ge_inj {r : Rng} (hr : r.WF) {j j' : Nat} (hj : j < r.len) (hj' : j' < r.len)
    (h : ge r j = ge r j') : j = j' := by
  have h1 := congrArg Subtype.val h
  rw [ge_val hr hj, ge_val hr hj'] at h1
  simp only [Rng.elem] at h1
  have h2 : (j : Int) * r.step.val = (j' : Int) * r.step.val := by omega
  have h3 := Int.eq_of_mul_eq_mul_right hr.1 h2
  omega

private theorem ge_zero (r : Rng) : ge r 0 = r.start := by
  apply Subtype.ext
  simp [ge, JInt.wrap, Rng.elem, wrapInt_of_inRange .i64 _ r.start.property]

private theorem last_eq {r : Rng} (hn : 0 < r.len) : r.last = ge r (r.len - 1) := by
  unfold Rng.last ge
  rw [show ((r.len : Int) - 1) = ((r.len - 1 : Nat) : Int) by omega]

private theorem ge_succ {r : Rng} (hr : r.WF) {j : Nat} (hj : j < r.len) :
    ge r j + r.step = ge r (j + 1) := by
  apply Subtype.ext
  show wrapInt .i64 ((ge r j).val + r.step.val) = wrapInt .i64 (r.elem ((j + 1 : Nat) : Int))
  rw [ge_val hr hj]
  congr 1
  simp only [Rng.elem]
  rw [Int.natCast_add, Int.add_mul]
  omega

private theorem ge_pred {r : Rng} (hr : r.WF) {j : Nat} (hj : j < r.len) (h0 : 0 < j) :
    ge r j - r.step = ge r (j - 1) := by
  apply Subtype.ext
  show wrapInt .i64 ((ge r j).val - r.step.val) = wrapInt .i64 (r.elem ((j - 1 : Nat) : Int))
  rw [ge_val hr hj]
  congr 1
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Rng.elem, Nat.add_sub_cancel]
  rw [Int.natCast_add, Int.add_mul]
  omega

private theorem contains_ge (r : Rng) {j : Nat} (hj : j < r.len) : r.contains (ge r j) = true := by
  simp only [Rng.contains, Rng.elems, List.contains_iff_mem, List.mem_map, List.mem_range]
  exact ⟨j, hj, rfl⟩

private theorem contains_pos {r : Rng} {x : I64} (h : r.contains x = true) : 0 < r.len := by
  rcases Nat.eq_zero_or_pos r.len with h0 | h0
  · simp [Rng.contains, Rng.elems, h0] at h
  · exact h0

/-! ## Products -/

private theorem flatMap_length {α β : Type} (T : List α) (f : α → List β) (n : Nat)
    (hf : ∀ a, (f a).length = n) : (T.flatMap f).length = T.length * n := by
  induction T with
  | nil => simp
  | cons a T ih =>
    rw [List.flatMap_cons, List.length_append, hf, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

private theorem flatMap_getElem? {α β : Type} (T : List α) (f : α → List β) (n : Nat)
    (hf : ∀ a, (f a).length = n) (q : Nat) {j : Nat} (hj : j < n) :
    (T.flatMap f)[q * n + j]? = T[q]?.bind fun a => (f a)[j]? := by
  induction T generalizing q with
  | nil => simp
  | cons a T ih =>
    rw [List.flatMap_cons]
    cases q with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by rw [hf]; exact hj)]
      simp
    | succ q =>
      rw [List.getElem?_append_right (by rw [hf, Nat.succ_mul]; omega),
        show (q + 1) * n + j - (f a).length = q * n + j by rw [hf, Nat.succ_mul]; omega, ih]
      simp

private theorem elems_cons_length (r : Rng) (rs : List Rng) :
    (elems (r :: rs)).length = (elems rs).length * r.len := by
  simp only [elems]
  exact flatMap_length _ _ _ (fun t => by simp [Rng.elems])

private theorem elems_cons_getElem? (r : Rng) (rs : List Rng) (q : Nat) {j : Nat}
    (hj : j < r.len) :
    (elems (r :: rs))[q * r.len + j]? = (elems rs)[q]?.map fun t => ge r j :: t := by
  simp only [elems]
  rw [flatMap_getElem? _ _ r.len (fun t => by simp [Rng.elems]) q hj]
  cases (elems rs)[q]? <;> simp [Rng.elems, ge, hj]

private theorem elems_mem_length :
    ∀ (R : List Rng) (t : List I64), t ∈ elems R → t.length = R.length
  | [], t, h => by simp [elems] at h; simp [h]
  | r :: rs, t, h => by
    simp only [elems, List.mem_flatMap, List.mem_map] at h
    obtain ⟨u, hu, x, _, rfl⟩ := h
    simp [elems_mem_length rs u hu]

private theorem elems_pos : ∀ (R : List Rng), 0 < (elems R).length → ∀ r ∈ R, 0 < r.len
  | [], _ => by simp
  | r :: rs, h => by
    rw [elems_cons_length] at h
    have hn : 0 < r.len := by
      rcases Nat.eq_zero_or_pos r.len with h0 | h0
      · rw [h0, Nat.mul_zero] at h; omega
      · exact h0
    have hM : 0 < (elems rs).length := by
      rcases Nat.eq_zero_or_pos (elems rs).length with h0 | h0
      · rw [h0, Nat.zero_mul] at h; omega
      · exact h0
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact hn
    · exact elems_pos rs hM r' hr'

private theorem elems_pos' : ∀ (R : List Rng), (∀ r ∈ R, 0 < r.len) → 0 < (elems R).length
  | [], _ => by simp [elems]
  | r :: rs, h => by
    rw [elems_cons_length]
    exact Nat.mul_pos (elems_pos' rs fun r' hr' => h r' (by simp [hr'])) (h r (by simp))

/-- Decompose a valid index into the digit of the first dimension and the rest. -/
private theorem elems_cons_decomp {r : Rng} {rs : List Rng} {k : Nat} {s : List I64}
    (h : (elems (r :: rs))[k]? = some s) :
    0 < r.len ∧ ∃ q j t, j < r.len ∧ k = q * r.len + j ∧ (elems rs)[q]? = some t ∧
      s = ge r j :: t ∧ t.length = rs.length := by
  have hk : k < (elems (r :: rs)).length := by
    rcases Nat.lt_or_ge k (elems (r :: rs)).length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at h; cases h
  have hn : 0 < r.len := by
    rw [elems_cons_length] at hk
    rcases Nat.eq_zero_or_pos r.len with h0 | h0
    · rw [h0, Nat.mul_zero] at hk; omega
    · exact h0
  refine ⟨hn, ?_⟩
  obtain ⟨q, j, hj, rfl⟩ : ∃ q j, j < r.len ∧ k = q * r.len + j :=
    ⟨k / r.len, k % r.len, Nat.mod_lt _ hn, (Nat.div_add_mod' k r.len).symm⟩
  rw [elems_cons_getElem? r rs q hj] at h
  cases h' : (elems rs)[q]? with
  | none => rw [h'] at h; cases h
  | some t =>
    rw [h'] at h
    exact ⟨q, j, t, hj, rfl, h', (Option.some.inj h).symm,
      elems_mem_length rs t (List.mem_of_getElem? h')⟩

private theorem first_elem : ∀ (R : List Rng), (∀ r ∈ R, r.WF ∧ 0 < r.len) →
    (elems R)[0]? = some (R.map (·.start))
  | [], _ => by simp [elems]
  | r :: rs, h => by
    have := elems_cons_getElem? r rs 0 (h r (by simp)).2
    rw [Nat.zero_mul, Nat.zero_add] at this
    rw [this, first_elem rs fun r' hr' => h r' (by simp [hr']), ge_zero]
    simp

private theorem last_elem : ∀ (R : List Rng), (∀ r ∈ R, r.WF ∧ 0 < r.len) →
    (elems R)[(elems R).length - 1]? = some (R.map (·.last))
  | [], _ => by simp [elems]
  | r :: rs, h => by
    have hrs : ∀ r ∈ rs, r.WF ∧ 0 < r.len := fun r' hr' => h r' (by simp [hr'])
    have hn := (h r (by simp)).2
    have hM := elems_pos' rs fun r' hr' => (hrs r' hr').2
    have ih := last_elem rs hrs
    rw [elems_cons_length]
    obtain ⟨M, hM'⟩ : ∃ M, (elems rs).length = M + 1 := ⟨(elems rs).length - 1, by omega⟩
    rw [hM', Nat.add_sub_cancel] at ih
    rw [hM', show (M + 1) * r.len - 1 = M * r.len + (r.len - 1) by rw [Nat.succ_mul]; omega,
      elems_cons_getElem? r rs M (by omega : r.len - 1 < r.len), ih, ← last_eq hn]
    simp

/-! ## `inc` and `dec` on one dimension -/

private theorem inc_ne (s : I64) (t : List I64) (r : Rng) (rs : List Rng)
    (ht : t.length = rs.length) (h : s ≠ r.last) :
    inc (s :: t) (r :: rs) = (true, (s + r.step) :: t) := by
  cases t with
  | nil =>
    cases rs with
    | nil => simp [inc, h]
    | cons => simp at ht
  | cons s' ss =>
    cases rs with
    | nil => simp at ht
    | cons r' rs => simp [inc, h]

private theorem inc_eq (s : I64) (t : List I64) (r : Rng) (rs : List Rng)
    (ht : t.length = rs.length) (h : s = r.last) :
    opt (inc (s :: t) (r :: rs)) = (opt (inc t rs)).map (r.start :: ·) := by
  subst h
  cases t with
  | nil =>
    cases rs with
    | nil => simp [inc, opt]
    | cons => simp at ht
  | cons s' ss =>
    cases rs with
    | nil => simp at ht
    | cons r' rs =>
      simp only [inc, opt, ne_eq, not_true_eq_false, ↓reduceIte]
      split <;> simp_all

private theorem dec_ne (s : I64) (t : List I64) (r : Rng) (rs : List Rng)
    (ht : t.length = rs.length) (h : s ≠ r.start) :
    dec (s :: t) (r :: rs) = (true, (s - r.step) :: t) := by
  cases t with
  | nil =>
    cases rs with
    | nil => simp [dec, h]
    | cons => simp at ht
  | cons s' ss =>
    cases rs with
    | nil => simp at ht
    | cons r' rs => simp [dec, h]

private theorem dec_eq (s : I64) (t : List I64) (r : Rng) (rs : List Rng)
    (ht : t.length = rs.length) (h : s = r.start) :
    opt (dec (s :: t) (r :: rs)) = (opt (dec t rs)).map (r.last :: ·) := by
  subst h
  cases t with
  | nil =>
    cases rs with
    | nil => simp [dec, opt]
    | cons => simp at ht
  | cons s' ss =>
    cases rs with
    | nil => simp at ht
    | cons r' rs =>
      simp only [dec, opt, ne_eq, not_true_eq_false, ↓reduceIte]
      split <;> simp_all

/-! ## Forward and reverse steps -/

private theorem fw : ∀ (R : List Rng), (∀ r ∈ R, r.WF) → ∀ (k : Nat) (s : List I64),
    (elems R)[k]? = some s → opt (inc s R) = (elems R)[k + 1]?
  | [], _, k, s, h => by
    cases k with
    | zero => simp [elems] at h; subst h; simp [elems, inc, opt]
    | succ k => simp [elems] at h
  | r :: rs, hR, k, s, h => by
    have hr : r.WF := hR r (by simp)
    have hrs : ∀ r ∈ rs, r.WF := fun r' h' => hR r' (by simp [h'])
    obtain ⟨hn, q, j, t, hj, rfl, ht, rfl, htl⟩ := elems_cons_decomp h
    by_cases hj1 : j + 1 < r.len
    · have hne : ge r j ≠ r.last := by
        rw [last_eq hn]; intro he; have := ge_inj hr hj (by omega) he; omega
      rw [inc_ne _ _ _ _ htl hne, ge_succ hr hj, Nat.add_assoc,
        elems_cons_getElem? r rs q hj1, ht]
      rfl
    · have heq : ge r j = r.last := by
        rw [last_eq hn, show j = r.len - 1 by omega]
      rw [inc_eq _ _ _ _ htl heq, fw rs hrs q t ht,
        show q * r.len + j + 1 = (q + 1) * r.len + 0 by rw [Nat.succ_mul]; omega,
        elems_cons_getElem? r rs (q + 1) hn, ge_zero]

private theorem bw : ∀ (R : List Rng), (∀ r ∈ R, r.WF) → ∀ (k : Nat) (s : List I64),
    (elems R)[k]? = some s → opt (dec s R) = if k = 0 then none else (elems R)[k - 1]?
  | [], _, k, s, h => by
    cases k with
    | zero => simp [elems] at h; subst h; simp [dec, opt]
    | succ k => simp [elems] at h
  | r :: rs, hR, k, s, h => by
    have hr : r.WF := hR r (by simp)
    have hrs : ∀ r ∈ rs, r.WF := fun r' h' => hR r' (by simp [h'])
    obtain ⟨hn, q, j, t, hj, rfl, ht, rfl, htl⟩ := elems_cons_decomp h
    by_cases hj0 : 0 < j
    · have hne : ge r j ≠ r.start := by
        rw [← ge_zero]; intro he; have := ge_inj hr hj hn he; omega
      rw [dec_ne _ _ _ _ htl hne, ge_pred hr hj hj0,
        ite_eq_right (show ¬(q * r.len + j = 0) by omega),
        show q * r.len + j - 1 = q * r.len + (j - 1) by omega,
        elems_cons_getElem? r rs q (by omega : j - 1 < r.len), ht]
      rfl
    · obtain rfl : j = 0 := by omega
      rw [dec_eq _ _ _ _ htl (ge_zero r), bw rs hrs q t ht]
      cases q with
      | zero => simp
      | succ q =>
        rw [ite_eq_right (show ¬(q + 1 = 0) by omega),
          ite_eq_right (show ¬((q + 1) * r.len + 0 = 0) by rw [Nat.succ_mul]; omega),
          show (q + 1) * r.len + 0 - 1 = q * r.len + (r.len - 1) by rw [Nat.succ_mul]; omega,
          elems_cons_getElem? r rs q (by omega : r.len - 1 < r.len), Nat.add_sub_cancel,
          last_eq hn]

/-! ## Iteration order -/

theorem cartesianIterOrder : CartesianIterOrder := by
  intro R hR
  refine ⟨?_, fun k hk => ?_⟩
  · unfold iterFirst
    by_cases hp : ∀ r ∈ R, 0 < r.len
    · have hall : R.all (fun r => r.contains r.start) = true := List.all_eq_true.mpr fun r hr => by
        rw [← ge_zero r]; exact contains_ge r (hp r hr)
      rw [ite_eq_left hall, List.head?_eq_getElem?, first_elem R fun r hr => ⟨hR r hr, hp r hr⟩]
    · have hall : R.all (fun r => r.contains r.start) = false := by
        cases h : R.all (fun r => r.contains r.start) with
        | false => rfl
        | true => exact absurd (fun r hr => contains_pos (List.all_eq_true.mp h r hr)) hp
      have hnil : elems R = [] := by
        cases h : elems R with
        | nil => rfl
        | cons a l => exact absurd (elems_pos R (by simp [h])) hp
      rw [hall, hnil]
      rfl
  · rw [show (elems R).getD k [] = (elems R)[k] by simp [hk]]
    exact fw R hR k _ (List.getElem?_eq_getElem hk)

theorem cartesianRevOrder : CartesianRevOrder := by
  intro R hR
  refine ⟨?_, fun k hk => ?_⟩
  · unfold revFirst
    rw [List.head?_reverse, List.getLast?_eq_getElem?]
    by_cases hp : ∀ r ∈ R, 0 < r.len
    · have hall : R.all (fun r => r.contains r.last) = true := List.all_eq_true.mpr fun r hr => by
        rw [last_eq (hp r hr)]; exact contains_ge r (by have := hp r hr; omega)
      rw [ite_eq_left hall, last_elem R fun r hr => ⟨hR r hr, hp r hr⟩]
    · have hall : R.all (fun r => r.contains r.last) = false := by
        cases h : R.all (fun r => r.contains r.last) with
        | false => rfl
        | true => exact absurd (fun r hr => contains_pos (List.all_eq_true.mp h r hr)) hp
      have hnil : elems R = [] := by
        cases h : elems R with
        | nil => rfl
        | cons a l => exact absurd (elems_pos R (by simp [h])) hp
      rw [hall, hnil]
      rfl
  · rw [show (elems R).reverse.getD k [] = (elems R)[(elems R).length - 1 - k] by
      simp [hk]]
    show opt (dec (elems R)[(elems R).length - 1 - k] R) = _
    rw [bw R hR _ _ (List.getElem?_eq_getElem
      (show (elems R).length - 1 - k < (elems R).length by omega))]
    by_cases hk1 : k + 1 < (elems R).length
    · rw [ite_eq_right (show ¬((elems R).length - 1 - k = 0) by omega),
        List.getElem?_reverse (show k + 1 < (elems R).length by omega)]
      congr 1
    · rw [ite_eq_left (show (elems R).length - 1 - k = 0 by omega),
        List.getElem?_eq_none (show (elems R).reverse.length ≤ k + 1 by simp; omega)]

/-! ## `findfirst` -/

local notation "U" => fun (n : Nat) => Rng.mk (i64 1) (i64 1) n

private theorem i64_val {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ 20) : (i64 x).val = x :=
  wrapInt_of_inRange .i64 x (by
    revert h1; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)

private theorem i64_one : (i64 1).val = 1 := i64_val (by omega) (by decide)

private theorem unit_wf {n : Nat} (hn : n < 2 ^ 20) : (U n).WF := by
  refine ⟨show (i64 1).val ≠ 0 by rw [i64_one]; decide, fun j hj => ?_⟩
  have hj' : j < n := hj
  simp only [Rng.elem, i64_one]
  revert hn; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega

private theorem unit_last (n : Nat) : (U n).last = i64 n := by
  show JInt.wrap .i64 ((i64 1).val + ((n : Int) - 1) * (i64 1).val) = JInt.wrap .i64 n
  rw [i64_one, Int.mul_one]
  congr 1
  omega

private theorem inAxes_cons (lo hi j : Int) (ax : List (Int × Int)) (J : List Int) :
    inAxes ((lo, hi) :: ax) (j :: J) = (decide (lo ≤ j ∧ j ≤ hi) && inAxes ax J) := by
  simp only [inAxes, List.length_cons, List.zip_cons_cons, List.all_cons]
  rw [show (J.length + 1 == ax.length + 1) = (J.length == ax.length) by
    cases h : J.length == ax.length <;> simp_all]
  exact Bool.and_left_comm _ _ _

private theorem elems_inAxes : ∀ (sz : List Nat) (t : List I64), (∀ n ∈ sz, n < 2 ^ 20) →
    t ∈ elems (sz.map U) → inAxes (oneAxes sz) (t.map (·.val)) = true
  | [], t, _, h => by simp [elems] at h; subst h; simp [inAxes, oneAxes]
  | n :: sz, t, hs, h => by
    simp only [List.map_cons, elems, List.mem_flatMap, List.mem_map] at h
    obtain ⟨u, hu, x, hx, rfl⟩ := h
    simp only [Rng.elems, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hn : n < 2 ^ 20 := hs n (by simp)
    have hv := ge_val (unit_wf hn) hj
    simp only [Rng.elem, i64_one] at hv
    rw [List.map_cons, show oneAxes (n :: sz) = (1, (n : Int)) :: oneAxes sz from rfl,
      inAxes_cons, elems_inAxes sz u (fun m hm => hs m (by simp [hm])) hu]
    show (decide (1 ≤ (ge (U n) j).val ∧ (ge (U n) j).val ≤ n) && true) = true
    rw [hv]
    simp only [Bool.and_true, decide_eq_true_eq]
    omega

private theorem foldl_len : ∀ (sz : List Nat) (a : Nat),
    sz.foldl (· * ·) a = a * (elems (sz.map U)).length
  | [], a => by simp [elems]
  | n :: sz, a => by
    rw [List.foldl_cons, foldl_len sz, List.map_cons, elems_cons_length]
    show a * n * _ = a * (_ * n)
    rw [Nat.mul_assoc, Nat.mul_comm n]

private theorem tupleLess_ge : ∀ (L : List Nat), (∀ n ∈ L, 0 < n ∧ n < 2 ^ 20) →
    tupleLess (L.map fun (n : Nat) => i64 n) (L.map fun _ => i64 1) = false
  | [], _ => rfl
  | n :: L, h => by
    have hn := h n (by simp)
    simp only [List.map_cons, tupleLess]
    rw [tupleLess_ge L (fun m hm => h m (by simp [hm])),
      i64_val (x := (n : Int)) (by omega) (by exact_mod_cast hn.2), i64_one]
    simp
    omega

private theorem loop (sz : List Nat) (A : List Int → Bool) (hs : ∀ n ∈ sz, 0 < n ∧ n < 2 ^ 20) :
    ∀ (fuel k : Nat) (hk : k < (elems (sz.map U)).length), (elems (sz.map U)).length ≤ fuel + k →
    findLoop sz A fuel (elems (sz.map U))[k] =
      .ok (((elems (sz.map U)).drop k).find? fun I => A (I.map (·.val))) := by
  have hwf : ∀ r ∈ sz.map U, r.WF ∧ 0 < r.len := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hr
    exact ⟨unit_wf (hs n hn).2, (hs n hn).1⟩
  have hlast := last_elem _ hwf
  rw [List.map_map] at hlast
  have hlast' : (sz.map U).map (·.last) = sz.map fun (n : Nat) => i64 n := by
    rw [List.map_map]; exact List.map_congr_left fun n _ => unit_last n
  rw [List.map_map] at hlast'
  intro fuel
  induction fuel with
  | zero => intro k hk h; omega
  | succ fuel ih =>
    intro k hk hf
    have hin := elems_inAxes sz _ (fun n hn => (hs n hn).2) (List.getElem_mem hk)
    rw [findLoop, List.drop_eq_getElem_cons hk, List.find?_cons]
    simp only [hin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases hA : A ((elems (sz.map U))[k].map (·.val))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hfk := fw _ (fun r hr => (hwf r hr).1) k _ (List.getElem?_eq_getElem hk)
      by_cases hl : (elems (sz.map U))[k] = sz.map fun (n : Nat) => i64 n
      · rw [ite_eq_left hl]
        have hfl := fw _ (fun r hr => (hwf r hr).1) _ _ hlast
        rw [hlast', ← hl, hfk,
          show (elems (sz.map U)).length - 1 + 1 = (elems (sz.map U)).length by omega,
          List.getElem?_eq_none (Nat.le_refl _)] at hfl
        have : (elems (sz.map U)).length ≤ k + 1 := by
          rcases Nat.lt_or_ge (k + 1) (elems (sz.map U)).length with h1 | h1
          · rw [List.getElem?_eq_getElem h1] at hfl; cases hfl
          · exact h1
        rw [List.drop_eq_nil_of_le this]
        rfl
      · rw [ite_eq_right hl]
        have hk1 : k + 1 < (elems (sz.map U)).length := by
          rcases Nat.lt_or_ge (k + 1) (elems (sz.map U)).length with h1 | h1
          · exact h1
          · exfalso; apply hl
            have h2 := hlast
            rw [hlast', show (elems (sz.map U)).length - 1 = k by omega,
              List.getElem?_eq_getElem hk] at h2
            exact Option.some.inj h2
        rw [List.getElem?_eq_getElem hk1] at hfk
        have hp : inc (elems (sz.map U))[k] (sz.map U) = (true, (elems (sz.map U))[k + 1]) := by
          unfold opt at hfk
          split at hfk
          · rename_i hc
            exact Prod.ext hc (Option.some.inj hfk)
          · cases hfk
        rw [hp]
        exact ih (k + 1) hk1 (by omega)
    · rfl

theorem findfirstNonempty : FindfirstNonempty := by
  intro sz A hs
  have hwf : ∀ r ∈ sz.map U, r.WF ∧ 0 < r.len := by
    intro r hr
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hr
    exact ⟨unit_wf (hs n hn).2, (hs n hn).1⟩
  have hpos := elems_pos' _ fun r hr => (hwf r hr).2
  have hfirst := first_elem _ hwf
  rw [List.map_map, List.getElem?_eq_getElem hpos] at hfirst
  have hstart : sz.map (fun _ => i64 1) = (elems (sz.map U))[0] :=
    (Option.some.inj hfirst).symm
  have hci : ciLess (sz.map fun (n : Nat) => i64 n) (sz.map fun _ => i64 1) = false := by
    unfold ciLess
    rw [show (sz.map fun (n : Nat) => i64 n).reverse = sz.reverse.map fun (n : Nat) => i64 n by simp,
      show (sz.map fun _ => i64 1).reverse = sz.reverse.map fun _ => i64 1 by simp]
    exact tupleLess_ge _ fun n hn => hs n (List.mem_reverse.mp hn)
  unfold findfirst findnext
  simp only [hci, Bool.false_eq_true, ↓reduceIte]
  rw [hstart, loop sz A hs (sz.foldl (· * ·) 1 + 1) 0 hpos (by rw [foldl_len, Nat.one_mul]; omega)]
  rfl

end JuliaLean.Multidim
