import JuliaLean.base.multidimensional
import JuliaLean.Registry.Types

/-!
# Properties of `base/multidimensional.jl`

Specifications refer to the source-mirrored definitions. Established range and tuple
lemmas are reused through explicit equivalence proofs, rather than keeping properties
about an old implementation.
-/
namespace JuliaLean.Proofs.base.multidimensional

open JuliaLean JuliaLean.base.multidimensional

deriving instance DecidableEq for Except

private theorem wrapInt_congr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;> simp at h ⊢ <;> omega

private theorem wrapInt_emod_self (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

private theorem wrapInt_mul_left (t : IntTy) (a b : Int) : wrapInt t (wrapInt t a * b) = wrapInt t (a * b) :=
  wrapInt_congr t (by rw [Int.mul_emod, wrapInt_emod_self, ← Int.mul_emod])

private theorem wrapInt_sub_right (t : IntTy) (a b : Int) : wrapInt t (a - wrapInt t b) = wrapInt t (a - b) :=
  wrapInt_congr t (by cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega)

private theorem two_pow_pos_int (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  have := Nat.pow_pos (n := n) (by decide : 0 < 2); omega

private theorem toJInt_ofInt_val (t : IntTy) (z : Int) :
    (JuliaLean.C.toJInt t (BitVec.ofInt t.bits z)).val = wrapInt t z := by
  change wrapInt t (if t.signed then (BitVec.ofInt t.bits z).toInt else ((BitVec.ofInt t.bits z).toNat : Int)) = wrapInt t z
  apply wrapInt_congr
  split
  · rw [BitVec.toInt_ofInt]; exact Int.bmod_emod
  · rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have := two_pow_pos_int t.bits; omega)), Int.emod_emod]

private theorem sub_int_val {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.sub x y).val = wrapInt t (x.val - y.val) := by
  simp only [JuliaLean.base.int.sub, JuliaLean.base.int.sub_int, JuliaLean.C.jlSubInt, JuliaLean.C.fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, toJInt_ofInt_val, Int.sub_eq_add_neg]

private theorem mul_int_val {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.mul x y).val = wrapInt t (x.val * y.val) := by
  simp only [JuliaLean.base.int.mul, JuliaLean.base.int.mul_int, JuliaLean.C.jlMulInt, JuliaLean.C.fromJInt]
  rw [← BitVec.ofInt_mul, toJInt_ofInt_val]

private theorem eq_int_eq {t : IntTy} (x y : JInt t) :
    JuliaLean.base.int.eq_int x y = decide (x.val = y.val) := by
  simp only [JuliaLean.base.int.eq_int, JuliaLean.C.jlEqInt]
  by_cases h : x.val = y.val
  · simp [JuliaLean.C.fromJInt, show x = y from Subtype.ext h]
  · have : JuliaLean.C.fromJInt x ≠ JuliaLean.C.fromJInt y := by
      intro hb; apply h
      rw [← wrapInt_of_inRange t x.val x.property, ← wrapInt_of_inRange t y.val y.property,
        ← toJInt_ofInt_val, ← toJInt_ofInt_val]
      exact congrArg (fun b => (JuliaLean.C.toJInt t b).val) hb
    simp [h, this]

local notation "I64Min" => (-9223372036854775808 : Int)
local notation "I64Max" => (9223372036854775807 : Int)

private theorem int_val (x : Int) (h1 : I64Min ≤ x) (h2 : x ≤ I64Max) :
    (int x).val = x :=
  wrapInt_of_inRange .i64 x (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)

private theorem le_i64Max_of_le_max {x : Int} (h : x ≤ IntTy.max .i64) : x ≤ I64Max := by
  revert h; simp [IntTy.max, IntTy.signed, IntTy.bits]

private theorem i64Min_le_of_min_le {x : Int} (h : IntTy.min .i64 ≤ x) : I64Min ≤ x := by
  revert h; simp [IntTy.min, IntTy.signed, IntTy.bits]

private theorem int_one : (int 1).val = 1 := int_val 1 (by omega) (by omega)
private theorem int_two : (int 2).val = 2 := int_val 2 (by omega) (by omega)

private theorem bind_ok {α β : Type} (x : α) (f : α → Result β) :
    (Bind.bind (Except.ok x : Result α) f) = f x := rfl

private theorem tupleGet_one {α : Type} (x : α) (xs : List α) :
    tupleGet (x :: xs) (int 1) = .ok x := by
  unfold tupleGet
  rw [int_one]
  rfl

private theorem tupleGet_two {α : Type} (x y : α) (xs : List α) :
    tupleGet (x :: y :: xs) (int 2) = .ok y := by
  unfold tupleGet
  rw [int_two]
  rfl

private theorem vectorRead_one {α : Type} (x : α) :
    vectorRead [x] (int 1) = .ok x := by
  unfold vectorRead JuliaLean.base.array.vectorGet
  rw [int_one]
  rfl

/-- Column-major product of component ranges (first dimension fastest, as documented
at `base/multidimensional.jl:216-225`). -/
def elems : List Rng → List (List I64)
  | [] => [[]]
  | r :: rs => (elems rs).flatMap fun t => r.elems.map fun x => x :: t

/-- The `j`-th element of `r`. -/
private def ge (r : Rng) (j : Nat) : I64 := JInt.wrap .i64 (r.elem j)

/-- The result of `cartesianIterateNext`/`reverseIterateNext` projected to the next coordinate tuple. -/
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

/-! ## `increment` and `decrement` on one dimension -/

private theorem inc_ne (s : I64) (t : List I64) (r : Rng) (rs : List Rng)
    (ht : t.length = rs.length) (h : s ≠ r.last) :
    increment (s :: t) (r :: rs) = (true, (s + r.step) :: t) := by
  cases t with
  | nil =>
    cases rs with
    | nil => simp [increment, incSingle, h]
    | cons => simp at ht
  | cons s' ss =>
    cases rs with
    | nil => simp at ht
    | cons r' rs => simp [increment, incCons, h]

private theorem inc_eq (s : I64) (t : List I64) (r : Rng) (rs : List Rng)
    (ht : t.length = rs.length) (h : s = r.last) :
    opt (increment (s :: t) (r :: rs)) = (opt (increment t rs)).map (r.start :: ·) := by
  subst h
  cases t with
  | nil =>
    cases rs with
    | nil => simp [increment, incSingle, incEmpty, opt]
    | cons => simp at ht
  | cons s' ss =>
    cases rs with
    | nil => simp at ht
    | cons r' rs =>
      simp only [increment, incCons, opt]
      split <;> simp_all

private theorem dec_ne (s : I64) (t : List I64) (r : Rng) (rs : List Rng)
    (ht : t.length = rs.length) (h : s ≠ r.start) :
    decrement (s :: t) (r :: rs) = (true, (s - r.step) :: t) := by
  cases t with
  | nil =>
    cases rs with
    | nil => simp [decrement, decSingle, h]
    | cons => simp at ht
  | cons s' ss =>
    cases rs with
    | nil => simp at ht
    | cons r' rs => simp [decrement, decCons, h]

private theorem dec_eq (s : I64) (t : List I64) (r : Rng) (rs : List Rng)
    (ht : t.length = rs.length) (h : s = r.start) :
    opt (decrement (s :: t) (r :: rs)) = (opt (decrement t rs)).map (r.last :: ·) := by
  subst h
  cases t with
  | nil =>
    cases rs with
    | nil => simp [decrement, decSingle, decEmpty, opt]
    | cons => simp at ht
  | cons s' ss =>
    cases rs with
    | nil => simp at ht
    | cons r' rs =>
      simp only [decrement, decCons, opt]
      split <;> simp_all

/-! ## Forward and reverse steps -/

private theorem fw : ∀ (R : List Rng), (∀ r ∈ R, r.WF) → ∀ (k : Nat) (s : List I64),
    (elems R)[k]? = some s → opt (increment s R) = (elems R)[k + 1]?
  | [], _, k, s, h => by
    cases k with
    | zero => simp [elems] at h; subst h; simp [elems, increment, incEmpty, opt]
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
    (elems R)[k]? = some s → opt (decrement s R) = if k = 0 then none else (elems R)[k - 1]?
  | [], _, k, s, h => by
    cases k with
    | zero => simp [elems] at h; subst h; simp [decrement, decEmpty, opt]
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

private theorem zipWith_map_self {A B C : Type} (f : A → B) (g : B → A → C) (xs : List A) :
    List.zipWith g (xs.map f) xs = xs.map (fun x => g (f x) x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem next_eq_opt (ranges : CIs) (state : CI) :
    cartesianIterateNext increment ranges state = (opt (increment state ranges)).map (fun x => (x, x)) := by
  simp only [cartesianIterateNext, opt]
  cases increment state ranges with
  | mk valid value => cases valid <;> rfl

private theorem reverse_next_eq_opt (ranges : CIs) (state : CI) :
    reverseIterateNext decrement ranges state = (opt (decrement state ranges)).map (fun x => (x, x)) := by
  simp only [reverseIterateNext, opt]
  cases decrement state ranges with
  | mk valid value => cases valid <;> rfl

/-- Forward iteration has the documented nested-loop order, including exhaustion. -/
def CartesianIterOrder : Prop :=
  ∀ ranges : CIs, (∀ r ∈ ranges, r.WF) →
    cartesianIterateFirst ranges = (elems ranges).head?.map (fun x => (x, x)) ∧
    ∀ k, k < (elems ranges).length →
      cartesianIterateNext increment ranges ((elems ranges).getD k []) =
        ((elems ranges)[k + 1]?).map (fun x => (x, x))

theorem cartesianIterOrder : CartesianIterOrder := by
  intro R hR
  refine ⟨?_, fun k hk => ?_⟩
  · simp only [cartesianIterateFirst, zipWith_map_self, List.all_map, Function.comp_def, id_eq]
    by_cases hp : ∀ r ∈ R, 0 < r.len
    · have hall : R.all (fun r => r.contains r.start) = true := List.all_eq_true.mpr fun r hr => by
        rw [← ge_zero r]; exact contains_ge r (hp r hr)
      rw [hall, List.head?_eq_getElem?, first_elem R fun r hr => ⟨hR r hr, hp r hr⟩]
      rfl
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
  · rw [next_eq_opt, show (elems R).getD k [] = (elems R)[k] by simp [hk],
      fw R hR k _ (List.getElem?_eq_getElem hk)]

/-- Reverse iteration visits the same indices in the opposite order. -/
def CartesianRevOrder : Prop :=
  ∀ ranges : CIs, (∀ r ∈ ranges, r.WF) →
    reverseIterateFirst ranges = (elems ranges).reverse.head?.map (fun x => (x, x)) ∧
    ∀ k, k < (elems ranges).length →
      reverseIterateNext decrement ranges ((elems ranges).reverse.getD k []) =
        ((elems ranges).reverse[k + 1]?).map (fun x => (x, x))

theorem cartesianRevOrder : CartesianRevOrder := by
  intro R hR
  refine ⟨?_, fun k hk => ?_⟩
  · simp only [reverseIterateFirst, cartesianIndicesLast, zipWith_map_self, List.all_map, Function.comp_def, id_eq]
    rw [List.head?_reverse, List.getLast?_eq_getElem?]
    by_cases hp : ∀ r ∈ R, 0 < r.len
    · have hall : R.all (fun r => r.contains r.last) = true := List.all_eq_true.mpr fun r hr => by
        rw [last_eq (hp r hr)]; exact contains_ge r (by have := hp r hr; omega)
      rw [hall, last_elem R fun r hr => ⟨hR r hr, hp r hr⟩]
      rfl
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
  · rw [reverse_next_eq_opt, show (elems R).reverse.getD k [] = (elems R)[(elems R).length - 1 - k] by
      simp [hk]]
    rw [bw R hR _ _ (List.getElem?_eq_getElem
      (show (elems R).length - 1 - k < (elems R).length by omega))]
    by_cases hk1 : k + 1 < (elems R).length
    · rw [ite_eq_right (show ¬((elems R).length - 1 - k = 0) by omega),
        List.getElem?_reverse (show k + 1 < (elems R).length by omega),
        show (elems R).length - 1 - k - 1 = (elems R).length - 1 - (k + 1) by omega]
    · rw [ite_eq_left (show (elems R).length - 1 - k = 0 by omega),
        List.getElem?_eq_none (show (elems R).reverse.length ≤ k + 1 by simp; omega)]

/-- The documented strict-total-order law for tuples of machine integers. -/
def TupleIntegerOrder (less : CI → CI → Bool) : Prop :=
  ∀ a b c : CI, a.length = b.length → b.length = c.length →
    less a a = false ∧ (less a b = true → less b c = true → less a c = true) ∧
      (less a b = true ∨ a = b ∨ less b a = true)

/-- Cartesian comparison preserves the integer-tuple order interface. -/
def CartesianIslessOrder : Prop :=
  ∀ tupleLess : CI → CI → Bool, TupleIntegerOrder tupleLess →
  ∀ a b c : CI, a.length = b.length → b.length = c.length →
    cartesianIsless tupleLess a a = false ∧
    (cartesianIsless tupleLess a b = true → cartesianIsless tupleLess b c = true →
      cartesianIsless tupleLess a c = true) ∧
    (cartesianIsless tupleLess a b = true ∨ a = b ∨ cartesianIsless tupleLess b a = true)

theorem cartesianIslessOrder : CartesianIslessOrder := by
  intro tupleLess law a b c hab hbc
  have ordered := law a.reverse b.reverse c.reverse (by simpa using hab) (by simpa using hbc)
  refine ⟨ordered.1, ordered.2.1, ?_⟩
  rcases ordered.2.2 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (List.reverse_inj.mp h))
  · exact Or.inr (Or.inr h)

private theorem nodup_iff_count (l : List Int) : l.Nodup ↔ ∀ a, l.count a ≤ 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.nodup_cons, ih]
    constructor
    · rintro ⟨hb, h⟩ a
      rw [List.count_cons]
      by_cases hab : b = a
      · subst hab; rw [List.count_eq_zero_of_not_mem hb]; simp
      · have := h a
        rw [ite_eq_right (by simpa using hab)]; omega
    · intro h
      refine ⟨fun hb => ?_, fun a => ?_⟩
      · have h1 := h b
        have h2 := List.count_pos_iff.mpr hb
        rw [List.count_cons, ite_eq_left (beq_self_eq_true b)] at h1
        omega
      · have h1 := h a
        rw [List.count_cons] at h1
        split at h1 <;> omega

private theorem filter_len_succ (l : List Int) (N : Nat) :
    (l.filter fun d => decide (1 ≤ d ∧ d ≤ ((N + 1 : Nat) : Int))).length =
      (l.filter fun d => decide (1 ≤ d ∧ d ≤ (N : Int))).length + l.count ((N : Int) + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.count_cons, decide_eq_true_eq, beq_iff_eq]
    split <;> split <;> split <;> (try simp only [List.length_cons]) <;> omega

private theorem filter_length_eq_iff {α : Type} (p : α → Bool) : ∀ l : List α,
    (l.filter p).length ≤ l.length ∧ ((l.filter p).length = l.length ↔ ∀ x ∈ l, p x = true)
  | [] => by simp
  | a :: l => by
    obtain ⟨h1, h2⟩ := filter_length_eq_iff p l
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.forall_mem_cons]
      simp only [List.length_cons, ha, true_and]
      refine ⟨by omega, ?_⟩
      rw [← h2]
      constructor <;> intro h <;> omega
    · rw [List.filter_cons_of_neg ha, List.forall_mem_cons]
      simp only [List.length_cons]
      exact ⟨by omega, fun h => by omega, fun h => absurd h.1 ha⟩

private theorem once_le (dims : List Int) : ∀ N : Nat,
    ((List.range N).map fun (i : Nat) => decide (dims.count ((i : Int) + 1) = 1)).count true ≤
      (dims.filter fun d => decide (1 ≤ d ∧ d ≤ (N : Int))).length ∧
    (((List.range N).map fun (i : Nat) => decide (dims.count ((i : Int) + 1) = 1)).count true =
      (dims.filter fun d => decide (1 ≤ d ∧ d ≤ (N : Int))).length ↔
      ∀ i < N, dims.count ((i : Int) + 1) ≤ 1)
  | 0 => by
    have h0 : (dims.filter fun d => decide (1 ≤ d ∧ d ≤ ((0 : Nat) : Int))) = [] :=
      List.filter_eq_nil_iff.mpr fun a _ => by simp only [decide_eq_true_eq]; omega
    rw [h0]; simp
  | N + 1 => by
    obtain ⟨ih1, ih2⟩ := once_le dims N
    have hA : ((List.range (N + 1)).map fun (i : Nat) =>
          decide (dims.count ((i : Int) + 1) = 1)).count true =
        ((List.range N).map fun (i : Nat) => decide (dims.count ((i : Int) + 1) = 1)).count true +
          (if dims.count ((N : Int) + 1) = 1 then 1 else 0) := by
      by_cases hc : dims.count ((N : Int) + 1) = 1 <;>
        simp [List.range_succ, List.count_append, hc]
    rw [hA, filter_len_succ]
    refine ⟨by split <;> omega, ⟨fun h i hi => ?_, fun h => ?_⟩⟩
    · rcases Nat.lt_or_ge i N with hi' | hi'
      · exact ih2.mp (by split at h <;> omega) i hi'
      · have : i = N := by omega
        subst this
        split at h <;> omega
    · have e1 := ih2.mpr (fun i hi => h i (by omega))
      have e2 := h N (by omega)
      split <;> omega

private theorem filter_value_eq_count {Z : Type} (value : Z → Int) (xs : List Z) (x : Int) :
    (xs.filter (fun d => value d == x)).length = (xs.map value).count x := by
  induction xs with
  | nil => rfl
  | cons a xs ih => by_cases h : value a = x <;> simp_all

private theorem count_eq_one_iff_contains {l : List Int} (hnd : l.Nodup) (x : Int) :
    decide (l.count x = 1) = l.contains x := by
  have hle : l.count x ≤ 1 := (nodup_iff_count l).mp hnd x
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, List.contains_iff_mem, ← List.count_pos_iff]
  omega

private theorem zipWith_ite_all_true (reverse : Rng → Rng) :
    ∀ (ranges : CIs) (flags : List Bool),
      flags.length = ranges.length → (∀ b ∈ flags, b = true) →
      List.zipWith (fun r f => if f then reverse r else r) ranges flags = ranges.map reverse
  | [], [], _, _ => rfl
  | _ :: _, [], h, _ | [], _ :: _, h, _ => by simp at h
  | r :: rs, b :: bs, hlen, hall => by
    have hb : b = true := hall b (by simp)
    subst hb
    simp [zipWith_ite_all_true reverse rs bs (Nat.succ.inj hlen) (fun b' hb' => hall b' (by simp [hb']))]

private theorem zipWith_map_decide_contains (reverse : Rng → Rng) (l : List Int) :
    ∀ (ranges : CIs) (idxs : List Nat),
      List.zipWith (fun r f => if f then reverse r else r) ranges
        (idxs.map fun (i : Nat) => l.contains ((i : Int) + 1)) =
      List.zipWith (fun r (i : Nat) => if l.contains ((i : Int) + 1) then reverse r else r) ranges idxs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | r :: rs, i :: is => by
    simp only [List.map_cons, List.zipWith_cons_cons, zipWith_map_decide_contains reverse l rs is]

def returns (result : Result A) : Bool := match result with
  | .ok _ => true
  | .error _ => false

private theorem foldl_add_ite_eq_filter_length {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (acc : Nat),
      xs.foldl (fun a x => a + if p x then 1 else 0) acc = acc + (xs.filter p).length
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.filter_cons, foldl_add_ite_eq_filter_length p xs]
    cases p x <;> simp <;> omega

private theorem foldl_bool_eq_count_true :
    ∀ (bs : List Bool) (acc : Nat),
      bs.foldl (fun a b => a + if b then 1 else 0) acc = acc + bs.count true
  | [], acc => by simp
  | b :: bs, acc => by
    simp only [List.foldl_cons, List.count_cons, foldl_bool_eq_count_true bs]
    cases b <;> simp <;> omega

/-- Full specification of `_reverse` on `CartesianIndices` across colon, single-dimension,
1D tuple, and multi-dimension overloads for any `Integer` dimension type `Z`:
multi-dimension `_reverse` succeeds with the selected axes reversed iff the dimensions are
distinct and in `1:ndims(iter)` (throwing `ArgumentError` otherwise), and single-dimension
`_reverse` reverses the selected axis iff `1 <= dim <= ndims(iter)`. -/
def ReverseDimsCheck : Prop :=
  ∀ (Z : Type) (value : Z → Int) (reverse : Rng → Rng) (ranges : CIs),
    reverseCartesianAll reverse ranges = ranges.map reverse ∧
    (∀ dim : Z,
      reverseCartesianOneDimension (fun rs d => reverseCartesianDimension value reverse rs d) ranges dim =
        reverseCartesianDimension value reverse ranges dim ∧
      (¬ (1 ≤ value dim ∧ value dim ≤ ranges.length) →
        reverseCartesianDimension value reverse ranges dim =
          .error (.argumentError ("invalid dimension " ++ toString (value dim) ++ " in reverse"))) ∧
      (∀ (h : 1 ≤ value dim ∧ value dim ≤ ranges.length), (ranges.length : Int) ≤ IntTy.max .i64 →
        reverseCartesianDimension value reverse ranges dim =
          .ok (ranges.set ((value dim).toNat - 1)
            (reverse (ranges[(value dim).toNat - 1]'(by omega)))))) ∧
    (∀ dims : List Z,
      (((dims.map value).Nodup ∧ ∀ d ∈ dims, 1 ≤ value d ∧ value d ≤ ranges.length) →
        reverseCartesianDimensions value reverse ranges dims =
          .ok (List.zipWith (fun r (i : Nat) =>
            if (dims.map value).contains ((i : Int) + 1) then reverse r else r)
            ranges (List.range ranges.length))) ∧
      (¬ ((dims.map value).Nodup ∧ ∀ d ∈ dims, 1 ≤ value d ∧ value d ≤ ranges.length) →
        reverseCartesianDimensions value reverse ranges dims =
          .error (.argumentError ("invalid dimensions " ++ toString (dims.map value) ++ " in reverse"))))

theorem reverseDimsCheck : ReverseDimsCheck := by
  intro Z value reverse ranges
  refine ⟨rfl, fun dim => ⟨rfl, fun hbad => ?_, fun hgood hmax => ?_⟩, fun dims => ?_⟩
  · unfold reverseCartesianDimension
    have hnot : (!(1 ≤ value dim ∧ value dim ≤ (ranges.length : Int))) = true := by simp [hbad]
    rw [ite_eq_left hnot]; rfl
  · unfold reverseCartesianDimension
    have hmax' := le_i64Max_of_le_max hmax
    have hnot : ¬ (!(1 ≤ value dim ∧ value dim ≤ (ranges.length : Int))) = true := by simp [hgood]
    dsimp (config := { proj := false, iota := false }) only
    rw [ite_eq_right hnot]
    have hval : (int (value dim)).val = value dim := int_val (value dim) (by omega) (by omega)
    have hk : (value dim).toNat - 1 < ranges.length := by omega
    by_cases h1 : (ranges.length == 1) = true
    · rw [ite_eq_left h1]
      rcases ranges with _ | ⟨r, _ | _⟩
      · simp at h1
      · have h0 : (value dim).toNat - 1 = 0 := by simp at hgood; omega
        simp [reverseCartesianAll, h0, pure, Except.pure]
      · simp at h1
    · rw [ite_eq_right h1]
      have htup : tupleGet ranges (int (value dim)) = .ok (ranges[(value dim).toNat - 1]'hk) := by
        unfold tupleGet
        rw [hval, ite_eq_left (by omega), List.getElem?_eq_getElem hk]
      rw [htup, bind_ok]; rfl
  · let l := dims.map value
    obtain ⟨hle, heq⟩ := once_le l ranges.length
    obtain ⟨fle, feq⟩ := filter_length_eq_iff (fun d => decide (1 ≤ d ∧ d ≤ (ranges.length : Int))) l
    have flags : ((List.range ranges.length).map fun (i : Nat) =>
        (dims.foldl (fun acc d => acc + if value d == (Int.ofNat i) + 1 then 1 else 0) (0 : Nat)) == 1) =
        ((List.range ranges.length).map fun (i : Nat) => decide (l.count ((i : Int) + 1) = 1)) := by
      apply List.map_congr_left
      intro i _
      rw [foldl_add_ite_eq_filter_length, Nat.zero_add, filter_value_eq_count]
      apply Bool.eq_iff_iff.mpr
      simp [l]
    have hiff : dims.length =
        (((List.range ranges.length).map fun (i : Nat) => decide (l.count ((i : Int) + 1) = 1)).count true) ↔
        (l.Nodup ∧ ∀ d ∈ dims, 1 ≤ value d ∧ value d ≤ ranges.length) := by
      have hlen_l : l.length = dims.length := List.length_map _
      constructor
      · intro h
        have hA := heq.mp (by omega)
        have hF := feq.mp (by omega)
        have hR : ∀ x ∈ l, 1 ≤ x ∧ x ≤ (ranges.length : Int) := fun x hx => by simpa using hF x hx
        refine ⟨(nodup_iff_count l).mpr fun a => ?_, fun d hd => hR (value d) (List.mem_map_of_mem hd)⟩
        by_cases ha : a ∈ l
        · have h1 := hR a ha
          have h2 := hA (a.toNat - 1) (by omega)
          have e : ((a.toNat - 1 : Nat) : Int) + 1 = a := by omega
          rwa [e] at h2
        · rw [List.count_eq_zero_of_not_mem ha]; omega
      · rintro ⟨hnd, hR⟩
        have hR' : ∀ x ∈ l, decide (1 ≤ x ∧ x ≤ (ranges.length : Int)) = true := by
          intro x hx
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
          simpa using hR d hd
        have hF := feq.mpr hR'
        have hA := heq.mpr (fun i _ => (nodup_iff_count l).mp hnd _)
        omega
    constructor
    · intro hgood
      have hcnt : dims.length =
          (((List.range ranges.length).map fun (i : Nat) => decide (l.count ((i : Int) + 1) = 1)).count true) :=
        hiff.mpr hgood
      have hflags_contains : ((List.range ranges.length).map fun (i : Nat) =>
          decide (l.count ((i : Int) + 1) = 1)) =
          ((List.range ranges.length).map fun (i : Nat) => l.contains ((i : Int) + 1)) := by
        apply List.map_congr_left
        intro i _
        exact count_eq_one_iff_contains hgood.1 _
      unfold reverseCartesianDimensions
      dsimp (config := { proj := false, iota := false }) only
      rw [foldl_bool_eq_count_true, Nat.zero_add, flags]
      have hne : ¬ (dims.length !=
          ((List.range ranges.length).map fun (i : Nat) => decide (l.count ((i : Int) + 1) = 1)).count true) = true := by
        simp [hcnt]
      rw [ite_eq_right hne]
      by_cases hfull : (dims.length == ranges.length) = true
      · rw [ite_eq_left hfull]
        have hfull_eq : dims.length = ranges.length := beq_iff_eq.mp hfull
        have hall : ∀ b ∈ (List.range ranges.length).map (fun (i : Nat) => l.contains ((i : Int) + 1)), b = true := by
          have h1 := hcnt
          rw [hflags_contains, hfull_eq] at h1
          have hlen_m : ((List.range ranges.length).map (fun (i : Nat) => l.contains ((i : Int) + 1))).length = ranges.length := by simp
          intro b hb
          exact (List.count_eq_length.mp (by rw [hlen_m]; exact h1.symm) b hb).symm
        rw [← zipWith_map_decide_contains reverse l ranges (List.range ranges.length),
          zipWith_ite_all_true reverse ranges _ (by simp) hall]
        rfl
      · rw [ite_eq_right hfull, hflags_contains, zipWith_map_decide_contains]
        rfl
    · intro hbad
      have hcnt : dims.length ≠
          (((List.range ranges.length).map fun (i : Nat) => decide (l.count ((i : Int) + 1) = 1)).count true) :=
        fun hc => hbad (hiff.mp hc)
      unfold reverseCartesianDimensions
      dsimp (config := { proj := false, iota := false }) only
      rw [foldl_bool_eq_count_true, Nat.zero_add, flags]
      have hne : (dims.length !=
          ((List.range ranges.length).map fun (i : Nat) => decide (l.count ((i : Int) + 1) = 1)).count true) = true := by
        simp [hcnt]
      rw [ite_eq_left hne]; rfl
/-! ## Conservative overlap detection (`mightalias` and `_indicesmightoverlap`) -/

open AliasData

/-- Paired index slots either are both `CartesianIndex{n}` arrays of the same rank `n`,
hit the conservative `.other` fallback, or are scalar/range/integer-array indices. -/
def slotCompat : Idx → Idx → Prop
  | .carts n xs, .carts m ys =>
    n = m ∧ (∀ s ∈ xs, s.length = n) ∧ (∀ s' ∈ ys, s'.length = m)
  | .carts _ _, .other _ => True
  | .other _, .carts _ _ => True
  | .carts _ _, _ => False
  | _, .carts _ _ => False
  | _, _ => True

inductive SlotsCompat : List Idx → List Idx → Prop
  | nil : SlotsCompat [] []
  | cons {a b : Idx} {as bs : List Idx} :
      slotCompat a b → SlotsCompat as bs → SlotsCompat (a :: as) (b :: bs)

private theorem mem_positions_cons {p : List Int} {i : Idx} {is : List Idx} :
    p ∈ positions (i :: is) → ∃ s ∈ i.subs, ∃ q ∈ positions is, p = s ++ q := by
  intro h
  simp only [positions, List.mem_flatMap, List.mem_map] at h
  obtain ⟨q, hq, s, hs, rfl⟩ := h
  exact ⟨s, hs, q, hq, rfl⟩

private theorem subs_noncart {i : Idx} (hi : ∀ n xs, i ≠ .carts n xs)
    (ho : ∀ subs, i ≠ .other subs) {s : List Int} (hs : s ∈ i.subs) :
    ∃ k, s = [k] ∧ Elem.int k ∈ i.elems := by
  have hsub : i.subs = i.elems.filterMap (fun | .int k => some [k] | .cart _ => none) := by
    cases i with
    | carts n xs => exact absurd rfl (hi n xs)
    | other subs => exact absurd rfl (ho subs)
    | _ => rfl
  rw [hsub, List.mem_filterMap] at hs
  obtain ⟨e, he, hes⟩ := hs
  cases e with
  | int k => simp at hes; exact ⟨k, hes.symm, he⟩
  | cart _ => simp at hes

private theorem eqb_refl (x : Elem) : x.eqb x = true := by
  cases x <;> simp [Elem.eqb]

private theorem inIdx_of_mem {x : Elem} {A : Idx} (h : x ∈ A.elems) : inIdx x A = true := by
  unfold inIdx
  exact List.any_eq_true.mpr ⟨x, h, eqb_refl x⟩

private theorem mem_urange {k lo hi : Int} (h : Elem.int k ∈ (Idx.urange lo hi).elems) : lo ≤ k ∧ k ≤ hi := by
  simp only [Idx.elems, List.map_map, List.mem_map, List.mem_range, Function.comp_def, Elem.int.injEq] at h
  obtain ⟨m, hm, rfl⟩ := h
  omega

private theorem mem_scalar {k x : Int} (h : Elem.int k ∈ (Idx.scalar x).elems) : k = x := by
  simpa [Idx.elems] using h

private theorem eq_singleton_of_mem_len_one {α : Type} {xs : List α} {x : α}
    (hx : x ∈ xs) (hl : (xs.length == 1) = true) : xs = [x] := by
  rcases xs with _ | ⟨a, _ | ⟨b, xs⟩⟩
  · cases hx
  · simp only [List.mem_singleton] at hx; subst hx; rfl
  · simp at hl

private theorem arr_branch_elem {e : Elem} {A B : Idx} {left right : List Idx}
    (hA : e ∈ A.elems) (hB : e ∈ B.elems) (hn : Alias.overlap left right = .ok true) :
    indicesOverlapArrays (fun i : Idx => i.elems.length) (fun i n => vectorRead i.elems n)
      inIdx (fun _ _ => Alias.overlap left right) A B left right = .ok true := by
  have hB' : inIdx e B = true := inIdx_of_mem hB
  have hA' : inIdx e A = true := inIdx_of_mem hA
  unfold indicesOverlapArrays
  dsimp only
  by_cases h1A : (A.elems.length == 1) = true
  · have hea := eq_singleton_of_mem_len_one hA h1A
    have hv : vectorRead [e] (int 1) = .ok e := vectorRead_one _
    rw [ite_eq_left h1A, hea, hv]
    simp [hB', hn, bind, Except.bind]
  · rw [ite_eq_right h1A]
    by_cases h1B : (B.elems.length == 1) = true
    · have heb := eq_singleton_of_mem_len_one hB h1B
      have hv : vectorRead [e] (int 1) = .ok e := vectorRead_one _
      rw [ite_eq_left h1B, heb, hv]
      simp [hA', hn, bind, Except.bind]
    · rw [ite_eq_right h1B]; rfl

private theorem overlap_conservative {I J : List Idx} (hcompat : SlotsCompat I J)
    {p : List Int} (hpI : p ∈ positions I) (hpJ : p ∈ positions J) :
    Alias.overlap I J = .ok true := by
  induction hcompat generalizing p with
  | nil => rfl
  | @cons a b as bs hab hrest ih =>
    obtain ⟨s, hs, q, hq, rfl⟩ := mem_positions_cons hpI
    obtain ⟨s', hs', q', hq', heq⟩ := mem_positions_cons hpJ
    cases a with
    | other _ => rfl
    | carts n xs =>
      cases b with
      | other _ => rfl
      | carts m ys =>
        rcases hab with ⟨rfl, hxs, hys⟩
        simp only [Idx.subs] at hs hs'
        have hslen : s.length = s'.length := by rw [hxs s hs, hys s' hs']
        obtain ⟨rfl, rfl⟩ := List.append_inj heq hslen
        have hn := ih hq hq'
        have hA : Elem.cart s ∈ (Idx.carts n xs).elems := by simp [Idx.elems, hs]
        have hB : Elem.cart s ∈ (Idx.carts n ys).elems := by simp [Idx.elems, hs']
        exact arr_branch_elem hA hB hn
      | _ => exact False.elim hab
    | scalar x =>
      cases b with
      | other _ => rfl
      | carts _ _ => exact False.elim hab
      | scalar y =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have hx := mem_scalar hk; subst hx
        have hy := mem_scalar hk'; subst hy
        simp [Alias.overlap, indicesOverlapScalars, ih hq hq']
      | urange _ _ | srange _ _ _ | ints _ =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have hx := mem_scalar hk; subst hx
        simp [Alias.overlap, indicesOverlapScalarArray, inIdx_of_mem hk', ih hq hq']
    | urange alo ahi =>
      cases b with
      | other _ => rfl
      | carts _ _ => exact False.elim hab
      | scalar y =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have hy := mem_scalar hk'; subst hy
        simp [Alias.overlap, indicesOverlapArrayScalar, inIdx_of_mem hk, ih hq hq']
      | urange blo bhi =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have h1 := mem_urange hk
        have h2 := mem_urange hk'
        simp only [Alias.overlap, indicesOverlapUnitRanges]
        rw [ite_eq_left (by simp; omega), ih hq hq']
      | srange _ _ _ =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        simp [Alias.overlap, indicesOverlapRanges, ih hq hq', bind, Except.bind, pure, Except.pure]
        exact ⟨.int k, hk, .int k, hk', eqb_refl _⟩
      | ints _ =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact arr_branch_elem hk hk' (ih hq hq')
    | srange _ _ _ =>
      cases b with
      | other _ => rfl
      | carts _ _ => exact False.elim hab
      | scalar y =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have hy := mem_scalar hk'; subst hy
        simp [Alias.overlap, indicesOverlapArrayScalar, inIdx_of_mem hk, ih hq hq']
      | urange _ _ | srange _ _ _ =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        simp [Alias.overlap, indicesOverlapRanges, ih hq hq', bind, Except.bind, pure, Except.pure]
        exact ⟨.int k, hk, .int k, hk', eqb_refl _⟩
      | ints _ =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact arr_branch_elem hk hk' (ih hq hq')
    | ints _ =>
      cases b with
      | other _ => rfl
      | carts _ _ => exact False.elim hab
      | scalar y =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have hy := mem_scalar hk'; subst hy
        simp [Alias.overlap, indicesOverlapArrayScalar, inIdx_of_mem hk, ih hq hq']
      | urange _ _ | srange _ _ _ | ints _ =>
        obtain ⟨k, rfl, hk⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs
        obtain ⟨k', rfl, hk'⟩ := subs_noncart (by intro _ _ h; cases h) (by intro _ h; cases h) hs'
        simp only [List.singleton_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact arr_branch_elem hk hk' (ih hq hq')

/-- Generic and multi-dimensional overlap and parent-matching specification:
`parentsMatchAbstract`, `parentsMatchDense`, and `parentsMatchStrided` check identity or
`elsize`/`pointer`/`size` (or `strides`) equality across arbitrary parent types; the
`_indicesmightoverlap` methods (`indicesOverlapEmpty`, `indicesOverlapLeftEmpty`,
`indicesOverlapRightEmpty`, `indicesOverlapRanges`, `indicesOverlapUnitRanges`,
`indicesOverlapScalars`, `indicesOverlapScalarArray`, `indicesOverlapArrayScalar`,
`indicesOverlapArrays`, `indicesOverlapFallback`) and `mightaliasSubarray` are conservative
across scalar, `UnitRange`, `StepRange`, scalar-array, `CartesianIndex{n}`-array, and fallback
index types over any coordinate type `Z`, and reject mismatched index-tuple lengths with
`"malformed subarray"`. -/
def OverlapConservativeNoCarts : Prop :=
  (∀ (Z Par Ptr SZ ST ID : Type) [BEq Ptr] [BEq SZ] [BEq ST]
    (val : Z → Int) (I J : List (IdxZ Z))
    (parentA parentB : Par) (idEq : Par → Par → Bool)
    (elsize : Par → I64) (ptr : Par → Ptr) (sz : Par → SZ) (st : Par → ST)
    (dataids : Par → ID) (splatIds : List Idx → ID)
    (isdisjoint : ID → ID → Bool),
    let I' := I.map (IdxZ.toIdx val)
    let J' := J.map (IdxZ.toIdx val)
    SlotsCompat I' J' →
    ∀ p, p ∈ positions I' → p ∈ positions J' →
      Alias.overlap I' J' = .ok true ∧
      (idEq parentA parentB = true →
        mightaliasSubarray Prod.fst Prod.snd (fun _ => false) (parentsMatchAbstract idEq)
          Alias.overlap dataids splatIds isdisjoint (parentA, I') (parentB, J') = .ok true) ∧
      (elsize parentA = elsize parentB → (ptr parentA == ptr parentB) = true → (sz parentA == sz parentB) = true →
        mightaliasSubarray Prod.fst Prod.snd (fun _ => false) (parentsMatchDense elsize ptr sz)
          Alias.overlap dataids splatIds isdisjoint (parentA, I') (parentB, J') = .ok true) ∧
      (elsize parentA = elsize parentB → (ptr parentA == ptr parentB) = true → (st parentA == st parentB) = true →
        mightaliasSubarray Prod.fst Prod.snd (fun _ => false) (parentsMatchStrided elsize ptr st)
          Alias.overlap dataids splatIds isdisjoint (parentA, I') (parentB, J') = .ok true)) ∧
  (∀ (V : Type) (parent : CellArray V) (I J : List Idx),
    SlotsCompat I J →
    ∀ p, p ∈ positions I → p ∈ positions J →
      Alias.overlap I J = .ok true ∧ Alias.mightalias (parent, I) (parent, J) = .ok true) ∧
  (∀ (b : Idx) (bs : List Idx),
    Alias.overlap [] (b :: bs) = .error (.errorException "malformed subarray") ∧
    Alias.overlap (b :: bs) [] = .error (.errorException "malformed subarray"))

theorem overlapConservativeNoCarts : OverlapConservativeNoCarts := by
  refine ⟨?_, fun V parent I J hcompat p hpI hpJ => ?_, fun _ _ => ⟨rfl, rfl⟩⟩
  · intro Z Par Ptr SZ ST ID _ _ _ val I J parentA parentB idEq elsize ptr sz st
      dataids splatIds isdisjoint
    dsimp only
    intro hcompat p hpI hpJ
    have hov := overlap_conservative hcompat hpI hpJ
    refine ⟨hov, fun hid => ?_, fun he hp hs => ?_, fun he hp hst => ?_⟩
    · simp [mightaliasSubarray, parentsMatchAbstract, hid, hov]
    · simp [mightaliasSubarray, parentsMatchDense, he, hp, hs, hov]
    · simp [mightaliasSubarray, parentsMatchStrided, he, hp, hst, hov]
  · have hov := overlap_conservative hcompat hpI hpJ
    exact ⟨hov, by simp [Alias.mightalias, mightaliasSubarray, parentsMatchAbstract, hov]⟩
/-! ## `diff` on vectors, ranges, and multidimensional arrays -/

private theorem unitRange_len_of_lt (n : Nat) (hn : (n : Int) ≤ IntTy.max .i64) :
    (unitRange (int 1) (int n)).len = n ∧
    (unitRange (int 1) (int n - int 1)).len = n - 1 ∧
    (unitRange (int 2) (int n)).len = n - 1 ∧
    (unitRange (int 1) (int n)).last = int n := by
  have hn62 : (n : Int) ≤ I64Max := le_i64Max_of_le_max hn
  have h1 : (int 1).val = 1 := int_one
  have h2 : (int 2).val = 2 := int_two
  have hn' : (int n).val = (n : Int) := int_val n (by omega) (by omega)
  have hm1 : (int n - int 1).val = (n : Int) - 1 := by
    change wrapInt .i64 ((int n).val - (int 1).val) = (n : Int) - 1
    rw [hn', h1]
    exact wrapInt_of_inRange .i64 _ (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega)
  have hlen1 : (unitRange (int 1) (int n)).len = n := by
    simp only [unitRange, hn', h1]; omega
  refine ⟨hlen1, ?_, ?_, ?_⟩
  · simp only [unitRange, hm1, h1]; omega
  · simp only [unitRange, hn', h2]; omega
  · unfold Rng.last Rng.elem
    apply congrArg (JInt.wrap .i64)
    have hst : (unitRange (int 1) (int n)).start = int 1 := rfl
    have hsp : (unitRange (int 1) (int n)).step = int 1 := rfl
    rw [hlen1, hst, hsp, h1]
    omega

/-- `diff(A; dims)` has the size of `A` with `size(A, dims)` reduced by one (not below zero),
and throws `ArgumentError` for `dims` outside `1:ndims(A)`, for any `Integer` dimension type `Z`. -/
def DiffSize : Prop :=
  ∀ (Z : Type) (value : Z → Int) (sz : List Nat) (dims : Z),
    (∀ n ∈ sz, (n : Int) ≤ IntTy.max .i64) →
    diffArray (fun _ => .ok ())
      (fun sz : List Nat => sz.map (fun (n : Nat) => unitRange (int 1) (int n)))
      Rng.last unitRange id
      (fun _ rs => .ok (cartesianIndicesSize (fun r => int r.len) rs))
      (fun r1 r0 => if r1 == r0 then .ok r1 else .error .dimensionMismatch)
      value sz.length sz dims =
      if 1 ≤ value dims ∧ value dims ≤ sz.length then
        .ok ((sz.set ((value dims).toNat - 1) (sz.getD ((value dims).toNat - 1) 0 - 1)).map
          (fun (n : Nat) => int n))
      else .error (.argumentError ("dimension " ++ toString (value dims) ++ " out of range (1:" ++ toString sz.length ++ ")"))

theorem diffSize_proven : DiffSize := by
  intro Z value sz d_arg hsz
  let dims := value d_arg
  change diffArray (fun _ => .ok ())
      (fun sz : List Nat => sz.map (fun (n : Nat) => unitRange (int 1) (int n)))
      Rng.last unitRange id
      (fun _ rs => .ok (cartesianIndicesSize (fun r => int r.len) rs))
      (fun r1 r0 => if r1 == r0 then .ok r1 else .error .dimensionMismatch)
      id sz.length sz dims =
      if 1 ≤ dims ∧ dims ≤ sz.length then
        .ok ((sz.set (dims.toNat - 1) (sz.getD (dims.toNat - 1) 0 - 1)).map
          (fun (n : Nat) => int n))
      else .error (.argumentError ("dimension " ++ toString dims ++ " out of range (1:" ++ toString sz.length ++ ")"))
  unfold diffArray
  dsimp only [id_eq, bind, Except.bind, pure, Except.pure]
  by_cases h : 1 ≤ dims ∧ dims ≤ (sz.length : Int)
  · rw [ite_eq_left h]
    have hnot : (!(1 ≤ dims ∧ dims ≤ (sz.length : Int))) = false := by simp [h]
    rw [ite_eq_right (by rw [hnot]; decide)]
    let target : CI := (sz.set (dims.toNat - 1) (sz.getD (dims.toNat - 1) 0 - 1)).map (fun (n : Nat) => int n)
    have hr0 : cartesianIndicesSize (fun r => int r.len)
        (List.map (fun (range, i) =>
          if (Int.ofNat i) + 1 == dims then unitRange (int 1) (range.last - int 1) else range)
          (sz.map (fun (n : Nat) => unitRange (int 1) (int n))).zipIdx) = target := by
      apply List.ext_getElem
      · simp [cartesianIndicesSize, target]
      · intro k hk1 hk2
        have hk : k < sz.length := by simpa [cartesianIndicesSize] using hk1
        have hlen := unitRange_len_of_lt sz[k] (hsz sz[k] (List.getElem_mem hk))
        simp only [cartesianIndicesSize, List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
          target, List.getElem_set, List.getD_eq_getElem?_getD]
        by_cases hd : (k : Int) + 1 = dims
        · have hd' : dims.toNat - 1 = k := by omega
          simp [hd, hd', List.getElem?_eq_getElem hk, hlen.2.2.2, hlen.2.1]
        · have hd' : dims.toNat - 1 ≠ k := by omega
          simp [hd, hd', hlen.1]
    have hr1 : cartesianIndicesSize (fun r => int r.len)
        (List.map (fun (range, i) =>
          if (Int.ofNat i) + 1 == dims then unitRange (int 2) range.last else range)
          (sz.map (fun (n : Nat) => unitRange (int 1) (int n))).zipIdx) = target := by
      apply List.ext_getElem
      · simp [cartesianIndicesSize, target]
      · intro k hk1 hk2
        have hk : k < sz.length := by simpa [cartesianIndicesSize] using hk1
        have hlen := unitRange_len_of_lt sz[k] (hsz sz[k] (List.getElem_mem hk))
        simp only [cartesianIndicesSize, List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
          target, List.getElem_set, List.getD_eq_getElem?_getD]
        by_cases hd : (k : Int) + 1 = dims
        · have hd' : dims.toNat - 1 = k := by omega
          simp [hd, hd', List.getElem?_eq_getElem hk, hlen.2.2.2, hlen.2.2.1]
        · have hd' : dims.toNat - 1 ≠ k := by omega
          simp [hd, hd', hlen.1]
    rw [hr1, hr0]
    simp only [beq_self_eq_true, ↓reduceIte]
    rfl
  · rw [ite_eq_right h]
    have hnot : (!(1 ≤ dims ∧ dims ≤ (sz.length : Int))) = true := by simp [h]
    rw [ite_eq_left hnot]
    rfl

private theorem vectorRead_getElem {α : Type} (v : List α) (hn : (v.length : Int) ≤ IntTy.max .i64)
    (k : Nat) (hk : k < v.length) : vectorRead v (int ((k + 1 : Nat) : Int)) = .ok (v[k]'hk) := by
  have hn62 : (v.length : Int) ≤ I64Max := le_i64Max_of_le_max hn
  have hv : (int ((k + 1 : Nat) : Int)).val = (k : Int) + 1 := by
    rw [int_val ((k + 1 : Nat) : Int) (by omega) (by omega)]; omega
  unfold vectorRead JuliaLean.base.array.vectorGet
  rw [hv, ite_eq_left (by omega), show ((k : Int) + 1 - 1).toNat = k by omega,
    List.getElem?_eq_getElem hk]
  rfl

private theorem mapM_range_eq {α β : Type} (m : Nat) (f : Nat → α) (g : α → Result β) (h : Nat → β)
    (hfg : ∀ k < m, g (f k) = .ok (h k)) :
    ((List.range m).map f).mapM g = .ok ((List.range m).map h) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [List.range_succ, ih (fun k hk => hfg k (by omega)), hfg m (by omega),
      bind, Except.bind, pure, Except.pure]

private theorem zipWith_map_range {α β γ : Type} (m : Nat) (f : α → β → γ) (g1 : Nat → α) (g2 : Nat → β) :
    List.zipWith f ((List.range m).map g1) ((List.range m).map g2) =
      (List.range m).map (fun k => f (g1 k) (g2 k)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp [List.range_succ, List.zipWith_append, ih]

/-- `diff(v)` on a vector or range has `length(v) - 1` entries (`0` for empty `v`) equal to
`v[i+1] - v[i]` in the element type `JInt t`, and `diff(r; dims)` accepts `dims == 1` and
throws `ArgumentError` for `dims != 1` across any `Integer` dimension type `Z`. -/
def ArrayDiffSpec : Prop :=
  ∀ (t : IntTy) (Z : Type) (value : Z → Int) (v : List (JInt t)),
    (v.length : Int) ≤ IntTy.max .i64 →
    (∃ out,
      diffVector (diffArray (fun _ => .ok ()) (fun xs => [unitRange (int 1) (int xs.length)])
        Rng.last unitRange id vectorSlice
        (fun hi lo => if hi.length == lo.length then .ok (List.zipWith JuliaLean.base.int.sub hi lo)
                      else .error .dimensionMismatch)
        (fun d : I64 => d.val) 1) v = .ok out ∧
      (∀ dims : Z, value dims = 1 →
        diffRange value (fun _ => int 1) (fun xs => int xs.length) vectorRead
          (fun a b => .ok (JuliaLean.base.int.sub a b)) (fun lo hi => (unitRange lo hi).elems) v dims = .ok out) ∧
      out.length = v.length - 1 ∧
      ∀ k (hk : k + 1 < v.length),
        out[k]? = some (JInt.wrap t (v[k + 1].val - v[k].val))) ∧
    ∀ dims : Z, value dims ≠ 1 →
      diffRange value (fun _ => int 1) (fun xs => int xs.length) vectorRead
        (fun a b => .ok (JuliaLean.base.int.sub a b)) (fun lo hi => (unitRange lo hi).elems) v dims =
          .error (.argumentError ("dimension " ++ toString (value dims) ++ " out of range (1:1)"))
private def zeroElem (t : IntTy) : JInt t := JInt.lit t 0

private def diffOut {t : IntTy} (v : List (JInt t)) : List (JInt t) :=
  (List.range (v.length - 1)).map fun k =>
    JuliaLean.base.int.sub (v.getD (k + 1) (zeroElem t)) (v.getD k (zeroElem t))

private theorem helem0_eq (hi : I64) (k : Nat) :
    JInt.wrap .i64 ((unitRange (int 1) hi).elem k) = int ((k + 1 : Nat) : Int) := by
  unfold Rng.elem
  apply congrArg (JInt.wrap .i64)
  have hst : (unitRange (int 1) hi).start = int 1 := rfl
  have hsp : (unitRange (int 1) hi).step = int 1 := rfl
  rw [hst, hsp, int_one]; omega

private theorem helem2_eq (hi : I64) (k : Nat) :
    JInt.wrap .i64 ((unitRange (int 2) hi).elem k) = int (((k + 1) + 1 : Nat) : Int) := by
  unfold Rng.elem
  apply congrArg (JInt.wrap .i64)
  have hst : (unitRange (int 2) hi).start = int 2 := rfl
  have hsp : (unitRange (int 2) hi).step = int 1 := rfl
  rw [hst, hsp, int_two, int_one]; omega

private theorem hr0_slice_eq {t : IntTy} (v : List (JInt t)) (hn : (v.length : Int) ≤ IntTy.max .i64) :
    ((unitRange (int 1) (int v.length - int 1)).elems).mapM (vectorRead v) =
      .ok ((List.range (v.length - 1)).map (fun k => v.getD k (zeroElem t))) := by
  have hlen := unitRange_len_of_lt v.length hn
  unfold Rng.elems
  rw [hlen.2.1]
  apply mapM_range_eq
  intro k hk
  have hk' : k < v.length := by omega
  rw [helem0_eq, vectorRead_getElem v hn k hk',
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]

private theorem hr1_slice_eq {t : IntTy} (v : List (JInt t)) (hn : (v.length : Int) ≤ IntTy.max .i64) :
    ((unitRange (int 2) (int v.length)).elems).mapM (vectorRead v) =
      .ok ((List.range (v.length - 1)).map (fun k => v.getD (k + 1) (zeroElem t))) := by
  have hlen := unitRange_len_of_lt v.length hn
  unfold Rng.elems
  rw [hlen.2.2.1]
  apply mapM_range_eq
  intro k hk
  have hk' : k + 1 < v.length := by omega
  rw [helem2_eq, vectorRead_getElem v hn (k + 1) hk',
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]


private theorem diffArray_hcond (dims : I64) (hdims : dims.val = 1) :
    ¬ (!(decide (1 ≤ dims.val ∧ dims.val ≤ ((1 : Nat) : Int)))) = true := by
  rw [hdims]; decide

private theorem diffArray_heq1 (dims : I64) (hdims : dims.val = 1) :
    ((Int.ofNat 0) + 1 == dims.val) = true := by
  rw [hdims]; rfl

private theorem rangeDiff_hcond {Z : Type} (value : Z → Int) (dims : Z) (hdims : value dims = 1) :
    ¬ (value dims != 1) = true := by
  rw [hdims]; decide

private theorem helem1_eq (n : Nat) (hn : (n : Int) ≤ IntTy.max .i64) (k : Nat) (hk : k < n - 1) :
    int ((k + 1 : Nat) : Int) + int 1 = int (((k + 1) + 1 : Nat) : Int) := by
  have hn62 : (n : Int) ≤ I64Max := le_i64Max_of_le_max hn
  apply congrArg (JInt.wrap .i64)
  rw [int_val ((k + 1 : Nat) : Int) (by omega) (by omega), int_one]
  omega

private theorem vectorSlice_r1 {t : IntTy} (v : List (JInt t)) (hn : (v.length : Int) ≤ IntTy.max .i64)
    (dims : I64) (hdims : dims.val = 1) :
    vectorSlice v (List.map (fun (range, i) =>
      if (Int.ofNat i) + 1 == dims.val then unitRange (int 2) range.last else range)
      [unitRange (int 1) (int v.length)].zipIdx) =
      .ok ((List.range (v.length - 1)).map (fun k => v.getD (k + 1) (zeroElem t))) := by
  have hlen := unitRange_len_of_lt v.length hn
  have hzip : [unitRange (int 1) (int v.length)].zipIdx = [(unitRange (int 1) (int v.length), 0)] := rfl
  have htup1 : tupleGet [unitRange (int 2) (int v.length)] (int 1) = .ok (unitRange (int 2) (int v.length)) :=
    tupleGet_one _ []
  unfold vectorSlice
  simp only [hzip, List.map, diffArray_heq1 dims hdims, hlen.2.2.2, ite_true]
  rw [htup1, bind_ok, hr1_slice_eq v hn]

private theorem vectorSlice_r0 {t : IntTy} (v : List (JInt t)) (hn : (v.length : Int) ≤ IntTy.max .i64)
    (dims : I64) (hdims : dims.val = 1) :
    vectorSlice v (List.map (fun (range, i) =>
      if (Int.ofNat i) + 1 == dims.val then unitRange (int 1) (range.last - int 1) else range)
      [unitRange (int 1) (int v.length)].zipIdx) =
      .ok ((List.range (v.length - 1)).map (fun k => v.getD k (zeroElem t))) := by
  have hlen := unitRange_len_of_lt v.length hn
  have hzip : [unitRange (int 1) (int v.length)].zipIdx = [(unitRange (int 1) (int v.length), 0)] := rfl
  have htup0 : tupleGet [unitRange (int 1) (int v.length - int 1)] (int 1) = .ok (unitRange (int 1) (int v.length - int 1)) :=
    tupleGet_one _ []
  unfold vectorSlice
  simp only [hzip, List.map, diffArray_heq1 dims hdims, hlen.2.2.2, ite_true]
  rw [htup0, bind_ok, hr0_slice_eq v hn]

private theorem diffArray_vector_eq {t : IntTy} (v : List (JInt t)) (hn : (v.length : Int) ≤ IntTy.max .i64)
    (dims : I64) (hdims : dims.val = 1) :
    diffArray (fun _ => .ok ()) (fun xs : List (JInt t) => [unitRange (int 1) (int xs.length)])
      Rng.last unitRange id vectorSlice
      (fun hi lo => if hi.length == lo.length then .ok (List.zipWith JuliaLean.base.int.sub hi lo)
                    else .error .dimensionMismatch)
      (fun d : I64 => d.val) 1 v dims = .ok (diffOut v) := by
  unfold diffArray
  rw [bind_ok, ite_eq_right (diffArray_hcond dims hdims)]
  dsimp (config := { proj := false, iota := false }) only [id_eq]
  rw [vectorSlice_r1 v hn dims hdims, bind_ok,
    vectorSlice_r0 v hn dims hdims, bind_ok, zipWith_map_range]
  have hlen_eq : (List.map (fun k => v.getD (k + 1) (zeroElem t)) (List.range (v.length - 1))).length ==
      (List.map (fun k => v.getD k (zeroElem t)) (List.range (v.length - 1))).length := by
    simp only [List.length_map, List.length_range, beq_self_eq_true]
  rw [ite_eq_left hlen_eq]
  rfl

private theorem vectorDiff_eq {t : IntTy} (v : List (JInt t)) (hn : (v.length : Int) ≤ IntTy.max .i64) :
    vectorDiff v = .ok (diffOut v) :=
  diffArray_vector_eq v hn (int 1) int_one

private theorem rangeDiff_eq_of_val {t : IntTy} {Z : Type} (value : Z → Int)
    (v : List (JInt t)) (hn : (v.length : Int) ≤ IntTy.max .i64)
    (dims : Z) (hdims : value dims = 1) :
    rangeDiff value v dims = .ok (diffOut v) := by
  have hlen := unitRange_len_of_lt v.length hn
  unfold rangeDiff diffRange diffOut
  rw [ite_eq_right (rangeDiff_hcond value dims hdims)]
  dsimp (config := { proj := false, iota := false }) only
  unfold Rng.elems
  rw [hlen.2.1]
  apply mapM_range_eq
  intro k hk
  have hk0 : k < v.length := by omega
  have hk1 : k + 1 < v.length := by omega
  rw [helem0_eq, helem1_eq v.length hn k hk, vectorRead_getElem v hn (k + 1) hk1, bind_ok,
    vectorRead_getElem v hn k hk0, bind_ok,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk0,
    Option.getD_some, Option.getD_some]

private theorem diffOut_getElem? {t : IntTy} (v : List (JInt t)) (k : Nat) (hk : k + 1 < v.length) :
    (diffOut v)[k]? = some (JuliaLean.base.int.sub (v[k + 1]'hk) (v[k]'(by omega))) := by
  unfold diffOut
  have hk' : k < v.length - 1 := by omega
  have hk0 : k < v.length := by omega
  rw [List.getElem?_map, List.getElem?_range hk', Option.map_some,
    List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk0,
    Option.getD_some, Option.getD_some]

theorem arrayDiffSpec : ArrayDiffSpec := by
  intro t Z value v hn
  refine ⟨⟨diffOut v, vectorDiff_eq v hn, fun dims hdims => rangeDiff_eq_of_val value v hn dims hdims,
    by simp [diffOut], fun k hk => ?_⟩, fun dims hdims => ?_⟩
  · rw [diffOut_getElem? v k hk]
    apply congrArg some
    apply Subtype.ext
    exact sub_int_val (v[k + 1]'hk) (v[k]'(by omega))
  · unfold diffRange
    dsimp only [bind, Except.bind, pure, Except.pure]
    have hne : (value dims != 1) = true := by simp [hdims]
    rw [ite_eq_left hne]; rfl

/-! ## `circshift!` and `circcopy!` on `GridArray` -/

local notation "Bnd" => (9223372036854775807 : Int)

private theorem int_zero : (int 0).val = 0 := int_val 0 (by omega) (by omega)

private theorem unitRange_start_val (lo hi : Int) (h1 : I64Min ≤ lo) (h2 : lo ≤ I64Max) :
    (unitRange (int lo) (int hi)).start.val = lo := int_val lo h1 h2

private theorem unitRange_step_val (lo hi : Int) : (unitRange (int lo) (int hi)).step.val = 1 := int_one

private theorem unitRange_len_eq (lo hi : Int)
    (h1 : I64Min ≤ lo) (h2 : lo ≤ I64Max) (h3 : I64Min ≤ hi) (h4 : hi ≤ I64Max) :
    (unitRange (int lo) (int hi)).len = (hi - lo + 1).toNat := by
  unfold unitRange
  rw [int_val lo h1 h2, int_val hi h3 h4]

private theorem unitRange_elem_eq (lo hi k : Int) (h1 : I64Min ≤ lo) (h2 : lo ≤ I64Max) :
    (unitRange (int lo) (int hi)).elem k = lo + k := by
  unfold Rng.elem
  rw [unitRange_start_val lo hi h1 h2, unitRange_step_val, Int.mul_one]

private theorem unitRange_last_eq (lo hi : Int) (h1 : I64Min ≤ lo) (hle : lo ≤ hi) (h4 : hi ≤ I64Max) :
    (unitRange (int lo) (int hi)).last = int hi := by
  unfold Rng.last
  apply congrArg (JInt.wrap .i64)
  rw [unitRange_elem_eq lo hi _ h1 (by omega), unitRange_len_eq lo hi h1 (by omega) (by omega) h4]
  omega

private theorem unitRange_contains_iff (lo hi : Int) (x : I64)
    (h1 : I64Min ≤ lo) (h2 : lo ≤ I64Max) (h3 : I64Min ≤ hi) (h4 : hi ≤ I64Max) :
    (unitRange (int lo) (int hi)).contains x = true ↔ lo ≤ x.val ∧ x.val ≤ hi := by
  unfold Rng.contains Rng.elems
  rw [List.contains_iff_mem, List.mem_map, unitRange_len_eq lo hi h1 h2 h3 h4]
  constructor
  · rintro ⟨k, hk, hkx⟩
    rw [List.mem_range] at hk
    rw [unitRange_elem_eq lo hi k h1 h2] at hkx
    have hval : (JInt.wrap .i64 (lo + (k : Int))).val = lo + k := int_val _ (by omega) (by omega)
    have hx : x.val = lo + k := by rw [← hkx, hval]
    omega
  · rintro ⟨hx1, hx2⟩
    refine ⟨(x.val - lo).toNat, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · rw [unitRange_elem_eq lo hi _ h1 h2]
      apply Subtype.ext
      change wrapInt .i64 (lo + ↑(x.val - lo).toNat) = x.val
      rw [show lo + ↑(x.val - lo).toNat = x.val by omega]
      exact wrapInt_of_inRange .i64 x.val x.property

private def inRegion (ranges : CIs) (J : CI) : Bool :=
  J.length == ranges.length && cartesianIndicesContains J ranges

private theorem inRegion_nil_nil : inRegion [] [] = true := rfl
private theorem inRegion_nil_cons (j : I64) (js : CI) : inRegion [] (j :: js) = false := rfl
private theorem inRegion_cons_nil (r : Rng) (rs : CIs) : inRegion (r :: rs) [] = false := rfl

private theorem inRegion_cons (r : Rng) (rs : CIs) (j : I64) (js : CI) :
    inRegion (r :: rs) (j :: js) = (r.contains j && inRegion rs js) := by
  have hlen : ((j :: js).length == (r :: rs).length) = (js.length == rs.length) := by simp
  unfold inRegion cartesianIndicesContains
  rw [hlen, List.zipWith_cons_cons, List.all_cons, id_eq]
  cases js.length == rs.length <;> cases r.contains j <;>
    cases (List.zipWith (fun i r => r.contains i) js rs).all id <;> rfl

private theorem inRegion_split (rd1 rd2 ind1 : Rng)
    (hcov : ∀ j : I64, (rd1.contains j || rd2.contains j) = ind1.contains j) :
    ∀ (rdest ti : CIs) (J : CI),
      (inRegion (rdest ++ rd1 :: ti) J || inRegion (rdest ++ rd2 :: ti) J) =
        inRegion (rdest ++ ind1 :: ti) J
  | [], ti, [] => rfl
  | [], ti, j :: js => by
    simp only [List.nil_append, inRegion_cons, ← hcov j]
    cases rd1.contains j <;> cases rd2.contains j <;> cases inRegion ti js <;> rfl
  | r :: rs, ti, [] => rfl
  | r :: rs, ti, j :: js => by
    simp only [List.cons_append, inRegion_cons, ← inRegion_split rd1 rd2 ind1 hcov rs ti js]
    cases r.contains j <;> rfl

private theorem mem_columnMajor_iff_inRegion : ∀ (ranges : CIs) (I : CI),
    I ∈ columnMajor (ranges.map Rng.elems) ↔ inRegion ranges I = true
  | [], [] => by simp [columnMajor, inRegion_nil_nil]
  | [], j :: js => by simp [columnMajor, inRegion_nil_cons]
  | r :: rs, [] => by simp [columnMajor, inRegion_cons_nil]
  | r :: rs, j :: js => by
    simp only [List.map_cons, columnMajor, List.mem_flatMap, List.mem_map, inRegion_cons,
      Bool.and_eq_true]
    have hj_iff : j ∈ r.elems ↔ r.contains j = true := List.contains_iff_mem.symm
    constructor
    · rintro ⟨t, ht, x, hx, hcons⟩
      injection hcons with hj ht'
      subst hj ht'
      exact ⟨hj_iff.mp hx, (mem_columnMajor_iff_inRegion rs t).mp ht⟩
    · rintro ⟨hj, hjs⟩
      exact ⟨js, (mem_columnMajor_iff_inRegion rs js).mpr hjs, j, hj_iff.mpr hj, rfl⟩

private theorem inRegion_of_any_empty : ∀ (ranges : CIs) (J : CI),
    ranges.any (·.len == 0) = true → inRegion ranges J = false
  | [], _, h => by simp at h
  | _ :: _, [], _ => rfl
  | r :: rs, j :: js, h => by
    rw [inRegion_cons]
    simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h0 | h0
    · have hc : r.contains j = false := by
        cases hc' : r.contains j with
        | false => rfl
        | true => have := contains_pos hc'; omega
      rw [hc]; rfl
    · rw [inRegion_of_any_empty rs js h0, Bool.and_false]

private def regionPoint1 (r : Rng) (i : I64) : I64 :=
  JInt.wrap .i64 (r.elem (i.val - 1).toNat)

private def regionPoint (ranges : CIs) (I : CI) : CI :=
  List.zipWith regionPoint1 ranges I

private theorem vectorRead_regionPoint1 (r : Rng) (hr : (r.len : Int) ≤ Bnd) (i : I64)
    (hi : (unitRange (int 1) (int r.len)).contains i = true) :
    vectorRead r.elems i = .ok (regionPoint1 r i) := by
  rw [unitRange_contains_iff 1 r.len i (by omega) (by omega) (by omega) (by omega)] at hi
  have hk : (i.val - 1).toNat < r.elems.length := by simp [Rng.elems]; omega
  have hr2 : (r.elems.length : Int) ≤ IntTy.max .i64 := by
    simp only [Rng.elems, List.length_map, List.length_range, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hi_eq : i = int (((i.val - 1).toNat + 1 : Nat) : Int) := by
    apply Subtype.ext
    rw [int_val _ (by omega) (by omega)]
    omega
  conv => lhs; rw [hi_eq]
  rw [vectorRead_getElem r.elems hr2 (i.val - 1).toNat hk]
  simp [Rng.elems, regionPoint1]

private theorem map_regionPoint1_elems (r : Rng) (hr : (r.len : Int) ≤ Bnd) :
    ((unitRange (int 1) (int r.len)).elems).map (regionPoint1 r) = r.elems := by
  have hr2 : (r.len : Int) ≤ IntTy.max .i64 := by
    simp only [IntTy.max, IntTy.signed, IntTy.bits]; omega
  have hlen := (unitRange_len_of_lt r.len hr2).1
  unfold Rng.elems
  rw [hlen, List.map_map]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  simp only [Function.comp_apply, helem0_eq, regionPoint1]
  have hv : (int ((k + 1 : Nat) : Int)).val = (k : Int) + 1 := by
    rw [int_val ((k + 1 : Nat) : Int) (by omega) (by omega)]; omega
  rw [show ((int ((k + 1 : Nat) : Int)).val - 1).toNat = k by rw [hv]; omega]

private theorem mapTupleM_regionPoint (ranges : CIs) : ∀ (I : CI),
    (∀ r ∈ ranges, (r.len : Int) ≤ Bnd) →
    inRegion (regionIndexAxes ranges) I = true →
    mapTupleM (fun range i => vectorRead range.elems i) ranges I = .ok (regionPoint ranges I) := by
  induction ranges with
  | nil =>
    intro I _ h
    cases I with
    | nil => rfl
    | cons _ _ => simp [regionIndexAxes, cartesianIndicesAxes, inRegion_nil_cons] at h
  | cons r rs ih =>
    intro I hb h
    cases I with
    | nil => simp [regionIndexAxes, cartesianIndicesAxes, inRegion_cons_nil] at h
    | cons i is =>
      simp only [regionIndexAxes, cartesianIndicesAxes, List.map_cons, inRegion_cons, Bool.and_eq_true] at h
      have hr : (r.len : Int) ≤ Bnd := hb r (by simp)
      have hrs : ∀ r' ∈ rs, (r'.len : Int) ≤ Bnd := fun r' hr' => hb r' (by simp [hr'])
      simp only [mapTupleM, regionPoint, List.zipWith_cons_cons]
      rw [vectorRead_regionPoint1 r hr i h.1, bind_ok, ih is hrs h.2, bind_ok]
      rfl

private theorem regionGet_eq_regionPoint (ranges : CIs) (hb : ∀ r ∈ ranges, (r.len : Int) ≤ Bnd)
    (I : CI) (hI : I ∈ columnMajor ((regionIndexAxes ranges).map Rng.elems)) :
    regionGet ranges I = .ok (regionPoint ranges I) := by
  have hin : inRegion (regionIndexAxes ranges) I = true :=
    (mem_columnMajor_iff_inRegion (regionIndexAxes ranges) I).mp hI
  have hcheck : (I.length == ranges.length && cartesianIndicesContains I (regionIndexAxes ranges)) = true := by
    simpa [inRegion, regionIndexAxes, cartesianIndicesAxes] using hin
  unfold regionGet cartesianIndicesGetindex
  dsimp (config := { proj := false, iota := false }) only
  rw [ite_eq_left hcheck, bind_ok, mapTupleM_regionPoint ranges I hb hin]

private theorem map_regionPoint_columnMajor : ∀ (ranges : CIs),
    (∀ r ∈ ranges, (r.len : Int) ≤ Bnd) →
    (columnMajor ((regionIndexAxes ranges).map Rng.elems)).map (regionPoint ranges) =
      columnMajor (ranges.map Rng.elems)
  | [], _ => rfl
  | r :: rs, hb => by
    unfold regionIndexAxes cartesianIndicesAxes
    simp only [List.map_cons, columnMajor, List.map_flatMap]
    rw [← map_regionPoint_columnMajor rs (fun r' hr' => hb r' (by simp [hr'])), List.flatMap_map]
    apply congrArg (List.flatMap · (columnMajor (List.map Rng.elems (regionIndexAxes rs))))
    funext t
    rw [List.map_map, ← map_regionPoint1_elems r (hb r (by simp)), List.map_map]
    rfl

private theorem sub_self_i64 (x : I64) : x - x = int 0 := by
  apply congrArg (JInt.wrap .i64); omega

private theorem add_int_zero (x : I64) : x + int 0 = x := by
  apply Subtype.ext
  change wrapInt .i64 (x.val + (int 0).val) = x.val
  rw [int_zero, Int.add_zero]
  exact wrapInt_of_inRange .i64 x.val x.property

private theorem cartesianAdd_sub_self (I : CI) : ∀ (F : CI),
    I.length = F.length → cartesianAdd I (cartesianSub F F) = I := by
  induction I with
  | nil =>
    intro F h
    cases F with
    | nil => rfl
    | cons _ _ => simp at h
  | cons i is ih =>
    intro F h
    cases F with
    | nil => simp at h
    | cons f fs =>
      simp only [cartesianSub, cartesianAdd, List.zipWith_cons_cons, sub_self_i64, add_int_zero]
      exact congrArg (i :: ·) (ih fs (Nat.succ.inj h))

private theorem regionIndexAxes_eq_of_len_eq : ∀ (Rd Rs : CIs),
    Rd.map Rng.len = Rs.map Rng.len → regionIndexAxes Rd = regionIndexAxes Rs
  | [], [], _ => rfl
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | rd :: rds, rs :: rss, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have ih := regionIndexAxes_eq_of_len_eq rds rss h.2
    unfold regionIndexAxes cartesianIndicesAxes at ih ⊢
    simp only [List.map_cons, h.1, ih]

private theorem forIn_copy_grid {VD VS : Type} (conv : VS → VD) (Rdest Rsrc : CIs) (delta : CI)
    (src : GridArray VS) (srcFn : CI → VS) (mapIdx : CI → CI) (xs : List CI)
    (hstep : ∀ I ∈ xs, ∃ K,
      regionGet Rsrc I = .ok K ∧
      regionGet Rdest (cartesianAdd I delta) = .ok (mapIdx I) ∧
      src.cells K = some (srcFn (mapIdx I)))
    (dest : GridArray VD) :
    ∃ out : GridArray VD,
      (do
        let mut d := dest
        for I in xs do
          let value ← GridArray.get src (← regionGet Rsrc I)
          d ← GridArray.set d (conv value) (← regionGet Rdest (cartesianAdd I delta))
        return d) = .ok out ∧
      out.identity = dest.identity ∧
      out.axes = dest.axes ∧
      ∀ J : CI, out.cells J =
        if J ∈ xs.map mapIdx then some (conv (srcFn J)) else dest.cells J := by
  induction xs generalizing dest with
  | nil =>
    exact ⟨dest, rfl, rfl, rfl, fun J => by simp⟩
  | cons I rest ih =>
    obtain ⟨K, hKs, hJd, hcell⟩ := hstep I (by simp)
    have hget : GridArray.get src K = .ok (srcFn (mapIdx I)) := by
      unfold GridArray.get; rw [hcell]
    let dest1 : GridArray VD :=
      { dest with cells := fun j => if j == mapIdx I then some (conv (srcFn (mapIdx I))) else dest.cells j }
    obtain ⟨out, hout, hid, hax, hcells⟩ :=
      ih (fun I' hI' => hstep I' (by simp [hI'])) dest1
    refine ⟨out, ?_, hid, hax, fun J => ?_⟩
    · simp only [List.forIn_cons, hKs, bind_ok, hget, hJd, GridArray.set]
      exact hout
    · rw [hcells J]
      simp only [dest1, List.map_cons, List.mem_cons]
      by_cases hmem : J ∈ rest.map mapIdx
      · simp [hmem]
      · by_cases heq : J = mapIdx I
        · subst heq; simp [hmem]
        · simp [hmem, heq]

private structure DimSpec where
  ad : Int
  as_ : Int
  l : Nat
  f : Int → Int

private def SubBlockOK (p : DimSpec) (rd rs : Rng) : Prop :=
  ∃ d_lo d_hi : Int,
    rd = unitRange (int d_lo) (int d_hi) ∧
    I64Min < p.ad ∧ p.ad + (p.l : Int) - 1 ≤ Bnd ∧
    I64Min < p.as_ ∧ p.as_ + (p.l : Int) - 1 ≤ Bnd ∧
    1 ≤ (p.l : Int) ∧ (p.l : Int) ≤ Bnd ∧
    p.ad ≤ d_lo ∧ d_lo ≤ p.ad + (p.l : Int) - 1 ∧ d_hi ≤ p.ad + (p.l : Int) - 1 ∧
    d_lo - 1 ≤ d_hi ∧
    (d_lo ≤ d_hi →
      ∃ s_lo s_hi : Int,
        rs = unitRange (int s_lo) (int s_hi) ∧
        p.as_ ≤ s_lo ∧ s_hi ≤ p.as_ + (p.l : Int) - 1 ∧
        d_hi - d_lo = s_hi - s_lo ∧
        ∀ j : Int, d_lo ≤ j → j ≤ d_hi → s_lo + (j - d_lo) = p.f j)

private def SubBlocksOK : List DimSpec → CIs → CIs → Prop
  | p :: ps, rd :: rds, rs :: rss => SubBlockOK p rd rs ∧ SubBlocksOK ps rds rss
  | [], [], [] => True
  | _, _, _ => False

private def destAxesOf (ps : List DimSpec) : CIs :=
  ps.map fun p => unitRange (int p.ad) (int (p.ad + (p.l : Int) - 1))

private def srcAxesOf (ps : List DimSpec) : CIs :=
  ps.map fun p => unitRange (int p.as_) (int (p.as_ + (p.l : Int) - 1))

private def applyFs (ps : List DimSpec) (J : CI) : CI :=
  List.zipWith (fun p (j : I64) => int (p.f j.val)) ps J

private theorem subBlocksOK_append : ∀ (ps1 ps2 : List DimSpec) (Rd1 Rd2 Rs1 Rs2 : CIs),
    SubBlocksOK ps1 Rd1 Rs1 → SubBlocksOK ps2 Rd2 Rs2 →
    SubBlocksOK (ps1 ++ ps2) (Rd1 ++ Rd2) (Rs1 ++ Rs2)
  | [], ps2, [], Rd2, [], Rs2, _, h2 => h2
  | p :: ps1, ps2, rd :: Rd1, Rd2, rs :: Rs1, Rs2, ⟨h, h1⟩, h2 =>
    ⟨h, subBlocksOK_append ps1 ps2 Rd1 Rd2 Rs1 Rs2 h1 h2⟩
  | _ :: _, _, [], _, _, _, h1, _ => by simp [SubBlocksOK] at h1
  | _ :: _, _, _ :: _, _, [], _, h1, _ => by simp [SubBlocksOK] at h1
  | [], _, _ :: _, _, _, _, h1, _ => by simp [SubBlocksOK] at h1
  | [], _, [], _, _ :: _, _, h1, _ => by simp [SubBlocksOK] at h1

private theorem subBlocksOK_lens : ∀ (ps : List DimSpec) (Rd Rs : CIs),
    SubBlocksOK ps Rd Rs → Rd.any (·.len == 0) = false →
    Rd.map Rng.len = Rs.map Rng.len ∧
    (∀ r ∈ Rd, (r.len : Int) ≤ Bnd) ∧ (∀ r ∈ Rs, (r.len : Int) ≤ Bnd)
  | [], [], [], _, _ => ⟨rfl, by simp, by simp⟩
  | p :: ps, rd :: Rd, rs :: Rs, ⟨h, hrest⟩, hany => by
    simp only [List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hany
    obtain ⟨d_lo, d_hi, rfl, had1, had2, has1, has2, hl1, hl2, hd1, hd1', hd2, hdle, hs_imp⟩ := h
    have hlen_d := unitRange_len_eq d_lo d_hi (by omega) (by omega) (by omega) (by omega)
    have hd_le : d_lo ≤ d_hi := by have := hany.1; rw [hlen_d] at this; omega
    obtain ⟨s_lo, s_hi, rfl, hs1, hs2, hdiff, _⟩ := hs_imp hd_le
    obtain ⟨heq, hb1, hb2⟩ := subBlocksOK_lens ps Rd Rs hrest hany.2
    have hlen_s := unitRange_len_eq s_lo s_hi (by omega) (by omega) (by omega) (by omega)
    refine ⟨by simp [hlen_d, hlen_s, hdiff, heq], ?_, ?_⟩
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · rw [hlen_d]; omega
      · exact hb1 r hr
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · rw [hlen_s]; omega
      · exact hb2 r hr
  | _ :: _, [], _, h, _ | _ :: _, _ :: _, [], h, _ | [], _ :: _, _, h, _ | [], [], _ :: _, h, _ => by
    simp [SubBlocksOK] at h

private theorem subBlocksOK_corners : ∀ (ps : List DimSpec) (Rd Rs : CIs),
    SubBlocksOK ps Rd Rs → Rd.any (·.len == 0) = false →
    inRegion (destAxesOf ps) (cartesianIndicesFirst Rd) = true ∧
    inRegion (destAxesOf ps) (cartesianIndicesLast Rd) = true ∧
    inRegion (srcAxesOf ps) (cartesianIndicesFirst Rs) = true ∧
    inRegion (srcAxesOf ps) (cartesianIndicesLast Rs) = true
  | [], [], [], _, _ => ⟨rfl, rfl, rfl, rfl⟩
  | p :: ps, rd :: Rd, rs :: Rs, ⟨h, hrest⟩, hany => by
    simp only [List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hany
    obtain ⟨d_lo, d_hi, rfl, had1, had2, has1, has2, hl1, hl2, hd1, hd1', hd2, hdle, hs_imp⟩ := h
    have hlen_d := unitRange_len_eq d_lo d_hi (by omega) (by omega) (by omega) (by omega)
    have hd_le : d_lo ≤ d_hi := by have := hany.1; rw [hlen_d] at this; omega
    obtain ⟨s_lo, s_hi, rfl, hs1, hs2, hdiff, _⟩ := hs_imp hd_le
    have hs_le : s_lo ≤ s_hi := by omega
    obtain ⟨c1, c2, c3, c4⟩ := subBlocksOK_corners ps Rd Rs hrest hany.2
    simp only [destAxesOf, srcAxesOf, cartesianIndicesFirst, cartesianIndicesLast,
      List.map_cons, inRegion_cons, Bool.and_eq_true]
    have hst_d : (unitRange (int d_lo) (int d_hi)).start = int d_lo := rfl
    have hst_s : (unitRange (int s_lo) (int s_hi)).start = int s_lo := rfl
    have hls_d := unitRange_last_eq d_lo d_hi (by omega) hd_le (by omega)
    have hls_s := unitRange_last_eq s_lo s_hi (by omega) hs_le (by omega)
    rw [hst_d, hst_s, hls_d, hls_s]
    rw [unitRange_contains_iff p.ad (p.ad + p.l - 1) (int d_lo) (by omega) (by omega) (by omega) (by omega),
      unitRange_contains_iff p.ad (p.ad + p.l - 1) (int d_hi) (by omega) (by omega) (by omega) (by omega),
      unitRange_contains_iff p.as_ (p.as_ + p.l - 1) (int s_lo) (by omega) (by omega) (by omega) (by omega),
      unitRange_contains_iff p.as_ (p.as_ + p.l - 1) (int s_hi) (by omega) (by omega) (by omega) (by omega),
      int_val d_lo (by omega) (by omega), int_val d_hi (by omega) (by omega),
      int_val s_lo (by omega) (by omega), int_val s_hi (by omega) (by omega)]
    exact ⟨⟨⟨hd1, by omega⟩, c1⟩, ⟨⟨by omega, hd2⟩, c2⟩,
      ⟨⟨hs1, by omega⟩, c3⟩, ⟨⟨by omega, hs2⟩, c4⟩⟩
  | _ :: _, [], _, h, _ | _ :: _, _ :: _, [], h, _ | [], _ :: _, _, h, _ | [], [], _ :: _, h, _ => by
    simp [SubBlocksOK] at h

private theorem subBlocksOK_regionPoint (ps : List DimSpec) : ∀ (Rd Rs : CIs) (I : CI),
    SubBlocksOK ps Rd Rs →
    inRegion (regionIndexAxes Rd) I = true →
    regionPoint Rs I = applyFs ps (regionPoint Rd I) := by
  induction ps with
  | nil =>
    intro Rd Rs I hok hI
    rcases Rd with _ | ⟨rd, Rd⟩ <;> rcases Rs with _ | ⟨rs, Rs⟩ <;> rcases I with _ | ⟨i, is⟩
    · rfl
    · simp [regionIndexAxes, cartesianIndicesAxes, inRegion_nil_cons] at hI
    · simp [SubBlocksOK] at hok
    · simp [SubBlocksOK] at hok
    · simp [SubBlocksOK] at hok
    · simp [SubBlocksOK] at hok
    · simp [SubBlocksOK] at hok
    · simp [SubBlocksOK] at hok
  | cons p ps ih =>
    intro Rd Rs I hok hI
    rcases Rd with _ | ⟨rd, Rd⟩ <;> rcases Rs with _ | ⟨rs, Rs⟩
    · simp [SubBlocksOK] at hok
    · simp [SubBlocksOK] at hok
    · simp [SubBlocksOK] at hok
    · rcases I with _ | ⟨i, is⟩
      · simp [regionIndexAxes, cartesianIndicesAxes, inRegion_cons_nil] at hI
      · obtain ⟨h, hrest⟩ := hok
        simp only [regionIndexAxes, cartesianIndicesAxes, List.map_cons, inRegion_cons, Bool.and_eq_true] at hI
        obtain ⟨d_lo, d_hi, rfl, had1, had2, has1, has2, hl1, hl2, hd1, hd1', hd2, hdle, hs_imp⟩ := h
        have hlen_d := unitRange_len_eq d_lo d_hi (by omega) (by omega) (by omega) (by omega)
        have hi_rng := hI.1
        rw [unitRange_contains_iff 1 (unitRange (int d_lo) (int d_hi)).len i
          (by omega) (by omega) (by omega) (by rw [hlen_d]; omega)] at hi_rng
        rw [hlen_d] at hi_rng
        obtain ⟨s_lo, s_hi, rfl, hs1, hs2, hdiff, hmap⟩ := hs_imp (by omega)
        simp only [regionPoint, applyFs, List.zipWith_cons_cons, List.cons.injEq]
        refine ⟨?_, ih Rd Rs is hrest hI.2⟩
        unfold regionPoint1
        rw [unitRange_elem_eq s_lo s_hi (i.val - 1).toNat (by omega) (by omega),
          unitRange_elem_eq d_lo d_hi (i.val - 1).toNat (by omega) (by omega)]
        have hd_val : (JInt.wrap .i64 (d_lo + ↑(i.val - 1).toNat)).val = d_lo + (i.val - 1) := by
          rw [show d_lo + ↑(i.val - 1).toNat = d_lo + (i.val - 1) by omega]
          exact int_val _ (by omega) (by omega)
        rw [hd_val]
        apply congrArg (JInt.wrap .i64)
        have hfj := hmap (d_lo + (i.val - 1)) (by omega) (by omega)
        omega

private theorem copyRegion_of_subBlocksOK {VD VS : Type} (conv : VS → VD) (ps : List DimSpec) (Rd Rs : CIs)
    (hok : SubBlocksOK ps Rd Rs) (dest : GridArray VD) (src : GridArray VS) (srcFn : CI → VS)
    (hdest_ax : dest.axes = destAxesOf ps) (hsrc_ax : src.axes = srcAxesOf ps)
    (hsrc_cells : ∀ K : CI, src.cells K = some (srcFn K)) :
    ∃ out : GridArray VD,
      GridArray.copyRegion conv dest Rd src Rs = .ok out ∧
      out.identity = dest.identity ∧
      out.axes = dest.axes ∧
      ∀ J : CI, out.cells J =
        if inRegion Rd J then some (conv (srcFn (applyFs ps J))) else dest.cells J := by
  unfold GridArray.copyRegion copytoCartesian
  by_cases he : Rd.any (·.len == 0) = true
  · rw [ite_eq_left he]
    refine ⟨dest, rfl, rfl, rfl, fun J => ?_⟩
    rw [inRegion_of_any_empty Rd J he]; rfl
  · have he' : Rd.any (·.len == 0) = false := Bool.eq_false_iff.mpr he
    rw [ite_eq_right he]
    obtain ⟨hlens, hbd, hbs⟩ := subBlocksOK_lens ps Rd Rs hok he'
    have hsize : ¬ (cartesianIndicesSize (fun r => int r.len) Rd !=
        cartesianIndicesSize (fun r => int r.len) Rs) = true := by
      have : cartesianIndicesSize (fun r => int r.len) Rd =
          cartesianIndicesSize (fun r => int r.len) Rs := by
        have hmap := congrArg (List.map (fun (n : Nat) => int (n : Int))) hlens
        rw [List.map_map, List.map_map] at hmap
        exact hmap
      simp [this]
    rw [ite_eq_right hsize, bind_ok]
    obtain ⟨c1, c2, c3, c4⟩ := subBlocksOK_corners ps Rd Rs hok he'
    have hcb1 : GridArray.checkbounds dest (cartesianIndicesFirst Rd) = .ok () := by
      unfold GridArray.checkbounds; rw [hdest_ax]; exact ite_eq_left c1
    have hcb2 : GridArray.checkbounds dest (cartesianIndicesLast Rd) = .ok () := by
      unfold GridArray.checkbounds; rw [hdest_ax]; exact ite_eq_left c2
    have hcb3 : GridArray.checkbounds src (cartesianIndicesFirst Rs) = .ok () := by
      unfold GridArray.checkbounds; rw [hsrc_ax]; exact ite_eq_left c3
    have hcb4 : GridArray.checkbounds src (cartesianIndicesLast Rs) = .ok () := by
      unfold GridArray.checkbounds; rw [hsrc_ax]; exact ite_eq_left c4
    dsimp (config := { proj := false, iota := false }) only
    rw [hcb1, bind_ok, hcb2, bind_ok, hcb3, bind_ok, hcb4, bind_ok]
    have hax_eq : regionIndexAxes Rs = regionIndexAxes Rd :=
      (regionIndexAxes_eq_of_len_eq Rd Rs hlens).symm
    let delta := cartesianSub (cartesianIndicesFirst (regionIndexAxes Rd))
      (cartesianIndicesFirst (regionIndexAxes Rs))
    obtain ⟨out, hout, hid, hax, hcells⟩ :=
      forIn_copy_grid conv Rd Rs delta src (fun J => srcFn (applyFs ps J)) (regionPoint Rd)
        (columnMajor ((regionIndexAxes Rs).map Rng.elems))
        (fun I hI => by
          have hI_d : I ∈ columnMajor ((regionIndexAxes Rd).map Rng.elems) := by
            rwa [← hax_eq]
          have hin_d : inRegion (regionIndexAxes Rd) I = true :=
            (mem_columnMajor_iff_inRegion (regionIndexAxes Rd) I).mp hI_d
          have hlen_I : I.length = (cartesianIndicesFirst (regionIndexAxes Rd)).length := by
            simp only [inRegion, Bool.and_eq_true, beq_iff_eq] at hin_d
            simp [cartesianIndicesFirst, hin_d.1]
          have hdelta : cartesianAdd I delta = I := by
            dsimp only [delta]
            rw [hax_eq]
            exact cartesianAdd_sub_self I _ hlen_I
          refine ⟨regionPoint Rs I, regionGet_eq_regionPoint Rs hbs I hI, ?_, ?_⟩
          · rw [hdelta, regionGet_eq_regionPoint Rd hbd I hI_d]
          · rw [hsrc_cells, subBlocksOK_regionPoint ps Rd Rs I hok hin_d])
        dest
    refine ⟨out, hout, hid, hax, fun J => ?_⟩
    rw [hcells J, hax_eq, map_regionPoint_columnMajor Rd hbd]
    by_cases hJ : inRegion Rd J = true
    · have hmem : J ∈ columnMajor (Rd.map Rng.elems) :=
        (mem_columnMajor_iff_inRegion Rd J).mpr hJ
      simp [hJ, hmem]
    · have hmem : J ∉ columnMajor (Rd.map Rng.elems) :=
        fun hm => hJ ((mem_columnMajor_iff_inRegion Rd J).mp hm)
      simp [hJ, hmem]

private theorem emod_of_eq (a t n q : Int) (h : a = t + n * q) (h0 : 0 ≤ t) (h1 : t < n) :
    a % n = t := by
  subst h; rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt h0 h1

private def AxisOK (p : Int × Int) : Prop :=
  p.1 ≤ p.2 ∧ I64Min < p.1 ∧ p.2 ≤ I64Max ∧ p.2 - p.1 + 1 ≤ I64Max

private def circSpec (ax : Int × Int) (d : Int) : DimSpec :=
  ⟨ax.1, ax.1, (ax.2 - ax.1 + 1).toNat, fun j => ax.1 + (j - ax.1 - d) % (ax.2 - ax.1 + 1)⟩

private def circSpecs (axs : List (Int × Int)) (sh : List Int) : List DimSpec :=
  List.zipWith circSpec axs sh

private theorem circshiftCons_step (ax : Int × Int) (d : Int) (hax : AxisOK ax) :
    let p := circSpec ax d
    let ind1 := unitRange (int p.ad) (int (p.ad + (p.l : Int) - 1))
    let s := int (d % (ax.2 - ax.1 + 1))
    let sf := ind1.start + s
    let sl := ind1.last - s
    let r1 := unitRange ind1.start (sf - int 1)
    let r2 := unitRange sf ind1.last
    let r3 := unitRange ind1.start sl
    let r4 := unitRange (sl + int 1) ind1.last
    (if (int ind1.len).val == 0 then (Except.error .divideError : Result I64)
     else .ok (int (d % (int ind1.len).val))) = .ok s ∧
    SubBlockOK p r1 r4 ∧
    SubBlockOK p r2 r3 ∧
    (∀ j : I64, (r1.contains j || r2.contains j) = ind1.contains j) := by
  intro p ind1 s sf sl r1 r2 r3 r4
  obtain ⟨hax1, hax2, hax3, hax4⟩ := hax
  let L := ax.2 - ax.1 + 1
  have hlen_nat : ((ax.2 - ax.1 + 1).toNat : Int) = L := by omega
  have hlen : ind1.len = (ax.2 - ax.1 + 1).toNat := by
    dsimp only [ind1, p, circSpec]
    rw [unitRange_len_eq ax.1 (ax.1 + ↑(ax.2 - ax.1 + 1).toNat - 1) (by omega) (by omega) (by omega) (by omega)]
    omega
  have hlen_val : (int ind1.len).val = L := by
    rw [hlen, int_val _ (by omega) (by omega)]; omega
  have hs0 : 0 ≤ d % L := Int.emod_nonneg _ (by omega)
  have hs1 : d % L < L := Int.emod_lt_of_pos _ (by omega)
  have hmod : (if (int ind1.len).val == 0 then (Except.error .divideError : Result I64)
      else .ok (int (d % (int ind1.len).val))) = .ok s := by
    rw [hlen_val, ite_eq_right (by simp [beq_iff_eq]; omega)]
  have hlast : ind1.last = int (ax.1 + L - 1) := by
    dsimp only [ind1, p, circSpec]
    rw [unitRange_last_eq _ _ (by omega) (by omega) (by omega), hlen_nat]
  have hsf : sf = int (ax.1 + d % L) := by
    dsimp only [sf, ind1, p, circSpec, s, L]
    change JInt.wrap .i64 ((int ax.1).val + (int (d % L)).val) = int (ax.1 + d % L)
    rw [int_val ax.1 (by omega) (by omega), int_val (d % L) (by omega) (by omega)]; rfl
  have hsf1 : sf - int 1 = int (ax.1 + d % L - 1) := by
    rw [hsf]
    change JInt.wrap .i64 ((int (ax.1 + d % L)).val - (int 1).val) = int (ax.1 + d % L - 1)
    rw [int_val (ax.1 + d % L) (by omega) (by omega), int_one]; rfl
  have hsl : sl = int (ax.1 + L - 1 - d % L) := by
    dsimp only [sl, s, L]
    rw [hlast]
    change JInt.wrap .i64 ((int (ax.1 + L - 1)).val - (int (d % L)).val) =
      int (ax.1 + L - 1 - d % L)
    rw [int_val (ax.1 + L - 1) (by omega) (by omega), int_val (d % L) (by omega) (by omega)]; rfl
  have hr1 : r1 = unitRange (int ax.1) (int (ax.1 + d % L - 1)) := by
    dsimp only [r1, ind1, p, circSpec]; rw [hsf1]; rfl
  have hr2 : r2 = unitRange (int (ax.1 + d % L)) (int (ax.1 + L - 1)) := by
    dsimp only [r2]; rw [hsf, hlast]
  have hr3 : r3 = unitRange (int ax.1) (int (ax.1 + L - 1 - d % L)) := by
    dsimp only [r3, ind1, p, circSpec]; rw [hsl]; rfl
  have hd := Int.mul_ediv_add_emod d L
  refine ⟨hmod, ?_, ?_, ?_⟩
  · unfold SubBlockOK
    refine ⟨ax.1, ax.1 + d % L - 1, hr1, ?_⟩
    dsimp only [p, circSpec, L] at hd hs0 hs1 ⊢
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, fun hd_le => ?_⟩
    have hsl1 : sl + int 1 = int (ax.1 + (ax.2 - ax.1 + 1) - d % (ax.2 - ax.1 + 1)) := by
      rw [hsl]
      change JInt.wrap .i64 ((int (ax.1 + (ax.2 - ax.1 + 1) - 1 - d % (ax.2 - ax.1 + 1))).val + (int 1).val) =
        int (ax.1 + (ax.2 - ax.1 + 1) - d % (ax.2 - ax.1 + 1))
      rw [int_val (ax.1 + (ax.2 - ax.1 + 1) - 1 - d % (ax.2 - ax.1 + 1)) (by omega) (by omega), int_one]
      exact congrArg (JInt.wrap .i64) (by omega)
    have hr4 : r4 = unitRange (int (ax.1 + (ax.2 - ax.1 + 1) - d % (ax.2 - ax.1 + 1)))
        (int (ax.1 + (ax.2 - ax.1 + 1) - 1)) := by
      dsimp only [r4]; rw [hsl1, hlast]
    refine ⟨ax.1 + (ax.2 - ax.1 + 1) - d % (ax.2 - ax.1 + 1),
      ax.1 + (ax.2 - ax.1 + 1) - 1, hr4, ?_⟩
    generalize d % (ax.2 - ax.1 + 1) = rem at *
    generalize d / (ax.2 - ax.1 + 1) = Q at *
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro j hj1 hj2
    rw [emod_of_eq (j - ax.1 - d) (j - ax.1 - rem + (ax.2 - ax.1 + 1)) (ax.2 - ax.1 + 1) (-(Q + 1))
      (by rw [Int.mul_neg, Int.mul_add, Int.mul_one]; omega) (by omega) (by omega)]
    omega
  · unfold SubBlockOK
    refine ⟨ax.1 + d % L, ax.1 + L - 1, hr2, ?_⟩
    dsimp only [p, circSpec, L] at hd hs0 hs1 ⊢
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, fun _ =>
        ⟨ax.1, ax.1 + (ax.2 - ax.1 + 1) - 1 - d % (ax.2 - ax.1 + 1), hr3, ?_⟩⟩
    generalize d % (ax.2 - ax.1 + 1) = rem at *
    generalize d / (ax.2 - ax.1 + 1) = Q at *
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro j hj1 hj2
    rw [emod_of_eq (j - ax.1 - d) (j - ax.1 - rem) (ax.2 - ax.1 + 1) (-Q)
      (by rw [Int.mul_neg]; omega) (by omega) (by omega)]
    omega
  · intro j
    rw [hr1, hr2]
    dsimp only [ind1, p, circSpec]
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true,
      unitRange_contains_iff ax.1 (ax.1 + d % L - 1) j (by omega) (by omega) (by omega) (by omega),
      unitRange_contains_iff (ax.1 + d % L) (ax.1 + L - 1) j (by omega) (by omega) (by omega) (by omega),
      unitRange_contains_iff ax.1 (ax.1 + ↑(ax.2 - ax.1 + 1).toNat - 1) j (by omega) (by omega) (by omega) (by omega)]
    omega

private theorem circshiftDispatch_spec {VD VS : Type} (conv : VS → VD) (sufAx : List (Int × Int))
    (hax_ok : ∀ p ∈ sufAx, AxisOK p) :
    ∀ (prePs : List DimSpec) (rdest rsrc : CIs) (sh : List Int)
      (dest : GridArray VD) (src : GridArray VS) (srcFn : CI → VS),
      sh.length = sufAx.length →
      SubBlocksOK prePs rdest rsrc →
      dest.axes = destAxesOf (prePs ++ circSpecs sufAx sh) →
      src.axes = srcAxesOf (prePs ++ circSpecs sufAx sh) →
      (∀ K : CI, src.cells K = some (srcFn K)) →
      ∃ out : GridArray VD,
        circshiftDispatch
          (fun (d : Int) l => if l.val == 0 then .error .divideError else .ok (int (d % l.val)))
          (fun r => int r.len) unitRange (GridArray.copyRegion conv)
          dest rdest src rsrc (destAxesOf (circSpecs sufAx sh)) sh = .ok out ∧
        out.identity = dest.identity ∧
        out.axes = dest.axes ∧
        ∀ J : CI, out.cells J =
          if inRegion (rdest ++ destAxesOf (circSpecs sufAx sh)) J
          then some (conv (srcFn (applyFs (prePs ++ circSpecs sufAx sh) J)))
          else dest.cells J := by
  induction sufAx with
  | nil =>
    intro prePs rdest rsrc sh dest src srcFn hsh hok hdest_ax hsrc_ax hsrc_cells
    cases sh with
    | nil =>
      simp only [circSpecs, List.zipWith_nil_left, destAxesOf, List.map_nil, List.append_nil] at hdest_ax hsrc_ax ⊢
      unfold circshiftDispatch circshiftBase
      exact copyRegion_of_subBlocksOK conv prePs rdest rsrc hok dest src srcFn hdest_ax hsrc_ax hsrc_cells
    | cons _ _ => simp at hsh
  | cons ax axs ih =>
    intro prePs rdest rsrc sh dest src srcFn hsh hok hdest_ax hsrc_ax hsrc_cells
    cases sh with
    | nil => simp at hsh
    | cons d ds =>
      have hax1 : AxisOK ax := hax_ok ax (by simp)
      have haxs : ∀ p ∈ axs, AxisOK p := fun p hp => hax_ok p (by simp [hp])
      have hds : ds.length = axs.length := Nat.succ.inj hsh
      let p := circSpec ax d
      obtain ⟨hmod, hok1, hok2, hcov⟩ := circshiftCons_step ax d hax1
      let ind1 := unitRange (int p.ad) (int (p.ad + (p.l : Int) - 1))
      let s := int (d % (ax.2 - ax.1 + 1))
      let sf := ind1.start + s
      let sl := ind1.last - s
      let r1 := unitRange ind1.start (sf - int 1)
      let r2 := unitRange sf ind1.last
      let r3 := unitRange ind1.start sl
      let r4 := unitRange (sl + int 1) ind1.last
      have hap : (prePs ++ [p]) ++ circSpecs axs ds = prePs ++ circSpecs (ax :: axs) (d :: ds) := by
        simp [circSpecs, p]
      have hok_1 : SubBlocksOK (prePs ++ [p]) (rdest ++ [r1]) (rsrc ++ [r4]) :=
        subBlocksOK_append prePs [p] rdest [r1] rsrc [r4] hok ⟨hok1, trivial⟩
      have hok_2 : SubBlocksOK (prePs ++ [p]) (rdest ++ [r2]) (rsrc ++ [r3]) :=
        subBlocksOK_append prePs [p] rdest [r2] rsrc [r3] hok ⟨hok2, trivial⟩
      obtain ⟨dest1, hrun1, hid1, hax_d1, hcells1⟩ :=
        ih haxs (prePs ++ [p]) (rdest ++ [r1]) (rsrc ++ [r4]) ds dest src srcFn hds hok_1
          (by rw [hap]; exact hdest_ax) (by rw [hap]; exact hsrc_ax) hsrc_cells
      obtain ⟨dest2, hrun2, hid2, hax_d2, hcells2⟩ :=
        ih haxs (prePs ++ [p]) (rdest ++ [r2]) (rsrc ++ [r3]) ds dest1 src srcFn hds hok_2
          (by rw [hax_d1, hap]; exact hdest_ax) (by rw [hap]; exact hsrc_ax) hsrc_cells
      refine ⟨dest2, ?_, by rw [hid2, hid1], by rw [hax_d2, hax_d1], fun J => ?_⟩
      · have hcons_ax : destAxesOf (circSpecs (ax :: axs) (d :: ds)) =
            ind1 :: destAxesOf (circSpecs axs ds) := rfl
        rw [hcons_ax, circshiftDispatch]
        unfold circshiftCons
        dsimp (config := { proj := false, iota := false }) only
        rw [hmod, bind_ok, hrun1, bind_ok, hrun2]
      · rw [hcells2 J, hcells1 J, hap]
        simp only [List.append_assoc, List.singleton_append]
        have hsp := inRegion_split r1 r2 ind1 hcov rdest (destAxesOf (circSpecs axs ds)) J
        change _ = if inRegion (rdest ++ ind1 :: destAxesOf (circSpecs axs ds)) J
          then some (conv (srcFn (applyFs (prePs ++ circSpecs (ax :: axs) (d :: ds)) J))) else dest.cells J
        rw [← hsp]
        cases inRegion (rdest ++ r1 :: destAxesOf (circSpecs axs ds)) J <;>
          cases inRegion (rdest ++ r2 :: destAxesOf (circSpecs axs ds)) J <;> rfl

private theorem destAxesOf_circSpecs : ∀ (axs : List (Int × Int)) (sh : List Int),
    (∀ p ∈ axs, AxisOK p) →
    sh.length = axs.length →
    destAxesOf (circSpecs axs sh) = axs.map (fun p => unitRange (int p.1) (int p.2)) ∧
    srcAxesOf (circSpecs axs sh) = axs.map (fun p => unitRange (int p.1) (int p.2))
  | [], [], _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | ax :: axs, d :: ds, hax, h => by
    obtain ⟨h1, h2, h3, h4⟩ := hax ax (by simp)
    obtain ⟨hd, hs⟩ := destAxesOf_circSpecs axs ds (fun p hp => hax p (by simp [hp])) (Nat.succ.inj h)
    have he : int (ax.1 + ↑(ax.2 - ax.1 + 1).toNat - 1) = int ax.2 :=
      congrArg (JInt.wrap .i64) (by omega)
    unfold destAxesOf circSpecs at hd
    unfold srcAxesOf circSpecs at hs
    unfold destAxesOf srcAxesOf circSpecs
    simp only [List.zipWith_cons_cons, List.map_cons, circSpec, he, hd, hs, and_self]

private theorem applyFs_circSpecs (axs : List (Int × Int)) : ∀ (sh : List Int) (J : CI),
    applyFs (circSpecs axs sh) J =
      (J.zip (axs.zip sh)).map fun (j, ax, s) => int (ax.1 + (j.val - ax.1 - s) % (ax.2 - ax.1 + 1)) := by
  induction axs with
  | nil => intro sh J; cases J <;> rfl
  | cons ax axs ih =>
    intro sh J
    cases sh with
    | nil => cases J <;> rfl
    | cons d ds =>
      cases J with
      | nil => rfl
      | cons j js =>
        have ih' := ih ds js
        unfold circSpecs applyFs at ih' ⊢
        simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons, circSpec, ih']

private theorem mapM_ok_eq_map {α β : Type} (f : α → β) : ∀ (xs : List α),
    (xs.mapM (fun x => (.ok (f x) : Result β))) = .ok (xs.map f)
  | [] => rfl
  | x :: xs => by
    simp only [List.mapM_cons, bind_ok, mapM_ok_eq_map f xs, List.map_cons]
    rfl

/-- The documented result of `circshift!`: `circshift!(dest, src, s)[J] == src[K]` where
each coordinate `K_d = first(ax_d) + mod(J_d - first(ax_d) - s_d, length(ax_d))`
(missing shifts are zero), across `circshiftEmpty`, `circshiftConvert`, `circshift`,
`circshiftCons`, and `circshiftBase`, for every `GridArray` with `Int64`-representable
unit-range axes (including offset axes), independent destination/source element types
`VD`/`VS`, and every tuple of shift amounts of any `Integer` type `S` no longer than `ndims(src)`. -/
def CircshiftFormula : Prop :=
  ∀ (VD VS S : Type) (conv : VS → VD) (toInt : S → Int)
    (axs : List (Int × Int)) (shifts : List S)
    (srcFn : CI → VS) (destCells : CI → Option VD),
    (∀ p ∈ axs, p.1 ≤ p.2 ∧ IntTy.min .i64 < p.1 ∧ p.2 ≤ IntTy.max .i64 ∧
      p.2 - p.1 + 1 ≤ IntTy.max .i64) →
    shifts.length ≤ axs.length →
    let axes := axs.map (fun p => unitRange (int p.1) (int p.2))
    let dest : GridArray VD := ⟨0, axes, destCells⟩
    let src : GridArray VS := ⟨1, axes, fun K => some (srcFn K)⟩
    let sh := shifts.map toInt
    circshiftEmpty (GridArray.copy conv) dest src = GridArray.copy conv dest src ∧
    circshiftConvert (fun s => .ok (toInt s)) (GridArray.circshift conv) dest src shifts =
      GridArray.circshift conv dest src sh ∧
    ∃ out : GridArray VD,
      GridArray.circshift conv dest src sh = .ok out ∧
      ∀ J : CI, (J.length == axes.length && cartesianIndicesContains J axes) = true →
        out.cells J = some (conv (srcFn
          ((J.zip (axs.zip (sh ++ List.replicate (axs.length - sh.length) 0))).map
            fun (j, ax, s) => int (ax.1 + (j.val - ax.1 - s) % (ax.2 - ax.1 + 1)))))

theorem circshiftFormula : CircshiftFormula := by
  intro VD VS S conv toInt axs shiftsRaw srcFn destCells haxs hlenRaw axes dest src shifts
  have hconv : circshiftConvert (fun s => .ok (toInt s)) (GridArray.circshift conv) dest src shiftsRaw =
      GridArray.circshift conv dest src shifts := by
    unfold circshiftConvert
    rw [mapM_ok_eq_map toInt shiftsRaw, bind_ok]
  refine ⟨rfl, hconv, ?_⟩
  have haxs_ok : ∀ p ∈ axs, AxisOK p := by
    intro p hp; obtain ⟨h1, h2, h3, h4⟩ := haxs p hp
    refine ⟨h1, ?_, le_i64Max_of_le_max h3, le_i64Max_of_le_max h4⟩
    revert h2; simp [IntTy.min, IntTy.signed, IntTy.bits]
  have hlen : shifts.length ≤ axs.length := by simp [shifts, hlenRaw]
  unfold GridArray.circshift JuliaLean.base.multidimensional.circshift
  dsimp (config := { proj := false, iota := false }) only
  have hid : (dest.identity == src.identity) = false := rfl
  have hax : (!(dest.axes == src.axes)) = false := by simp [dest, src]
  have haxes_len : src.axes.length = axs.length := by simp [src, axes]
  rw [ite_eq_right (by rw [hid]; decide), ite_eq_right (by rw [hax]; decide)]
  by_cases hempty : (src.axes.any (·.len == 0)) = true
  · rw [ite_eq_left hempty]
    refine ⟨dest, rfl, fun J hJ => ?_⟩
    exfalso
    have hfalse := inRegion_of_any_empty axes J hempty
    unfold inRegion at hfalse
    rw [hJ] at hfalse
    contradiction
  · rw [ite_eq_right hempty]
    have hgt : ¬ (shifts.length > axs.length) := by omega
    rw [haxes_len, ite_eq_right hgt, bind_ok]
    let sh := shifts ++ List.replicate (axs.length - shifts.length) 0
    have hsh_len : sh.length = axs.length := by simp [sh]; omega
    obtain ⟨hd_ax, hs_ax⟩ := destAxesOf_circSpecs axs sh haxs_ok hsh_len
    obtain ⟨out, hout, _, _, hcells⟩ :=
      circshiftDispatch_spec conv axs haxs_ok [] [] [] sh dest src srcFn hsh_len trivial
        (by simp [dest, axes, hd_ax]) (by simp [src, axes, hs_ax]) (fun K => rfl)
    simp only [hd_ax] at hout
    refine ⟨out, hout, fun J hJ => ?_⟩
    have hJ' := hcells J
    simp only [List.nil_append, hd_ax] at hJ'
    unfold inRegion at hJ'
    simp only [List.length_map] at hJ'
    rw [hJ, applyFs_circSpecs] at hJ'
    exact hJ'
private theorem fdiv_pos_eq_ediv (a : Int) : ∀ {b : Int}, 0 < b → a.fdiv b = a / b
  | .ofNat (n + 1), _ => by
    rcases a with (_ | m) | m
    · simp [Int.fdiv, Int.zero_ediv]
    · rfl
    · rfl
  | .ofNat 0, hb => by cases hb
  | .negSucc _, hb => by cases hb

private theorem intMod_pos (a b : I64) (hb : 0 < b.val) :
    intMod a b = .ok (int (a.val % b.val)) := by
  have hm1 : (JInt.lit IntTy.i64 (-1)).val = -1 := int_val (-1) (by omega) (by omega)
  have hne1 : ¬ JuliaLean.base.int.eq b (JuliaLean.base.int.lit IntTy.i64 (-1)) = true := by
    have hfst : (JuliaLean.base.int.promoteSameSign b (JuliaLean.base.int.lit IntTy.i64 (-1))).fst.val = b.val :=
      wrapInt_of_inRange .i64 b.val b.property
    have hsnd : (JuliaLean.base.int.promoteSameSign b (JuliaLean.base.int.lit IntTy.i64 (-1))).snd.val = -1 := by
      change wrapInt .i64 (JInt.lit .i64 (-1)).val = -1
      rw [hm1]; exact hm1
    unfold JuliaLean.base.int.eq JuliaLean.base.int.eqPromote JuliaLean.base.int.eqSame
    rw [ite_eq_left rfl, eq_int_eq, hfst, hsnd]; simp [show b.val ≠ -1 by omega]
  have hne0 : ¬ b.val = 0 := by omega
  unfold intMod JuliaLean.base.int.mod_BitSigned intFld
  rw [ite_eq_right hne1, ite_eq_right hne0]
  dsimp (config := { proj := false, iota := false }) only [bind, Except.bind, pure, Except.pure, Except.mapError]
  apply congrArg Except.ok
  apply Subtype.ext
  change (JuliaLean.base.int.sub a (JuliaLean.base.int.mul (JInt.lit .i64 (a.val.fdiv b.val)) b)).val =
    (int (a.val % b.val)).val
  rw [sub_int_val, mul_int_val]
  change wrapInt .i64 (a.val - wrapInt .i64 (wrapInt .i64 (a.val.fdiv b.val) * b.val)) =
    wrapInt .i64 (a.val % b.val)
  rw [wrapInt_mul_left, wrapInt_sub_right, fdiv_pos_eq_ediv a.val hb]
  have he := Int.mul_ediv_add_emod a.val b.val
  rw [show a.val - a.val / b.val * b.val = a.val % b.val by rw [Int.mul_comm]; omega]

private def copySpec (pd ps : Int × Int) : DimSpec :=
  ⟨pd.1, ps.1, (pd.2 - pd.1 + 1).toNat, fun j => ps.1 + (j - ps.1) % (ps.2 - ps.1 + 1)⟩

private def copySpecs (axd axs : List (Int × Int)) : List DimSpec :=
  List.zipWith copySpec axd axs

private theorem circcopyCons_step (pd ps : Int × Int)
    (hpd : AxisOK pd) (hps : AxisOK ps)
    (hdiff_i64 : I64Min ≤ ps.1 - pd.1 ∧ ps.1 - pd.1 ≤ I64Max)
    (hlen_eq : pd.2 - pd.1 + 1 = ps.2 - ps.1 + 1) :
    let p := copySpec pd ps
    let indd1 := unitRange (int p.ad) (int (p.ad + (p.l : Int) - 1))
    let inds1 := unitRange (int p.as_) (int (p.as_ + (p.l : Int) - 1))
    let l := int indd1.len
    let s := int ((ps.1 - pd.1) % (pd.2 - pd.1 + 1))
    let sdf := indd1.start + s
    let rd1 := unitRange indd1.start (sdf - int 1)
    let rd2 := unitRange sdf indd1.last
    let ssf := inds1.last - s
    let rs1 := unitRange inds1.start ssf
    let rs2 := unitRange (ssf + int 1) inds1.last
    intMod (inds1.start - indd1.start) l = .ok s ∧
    SubBlockOK p rd1 rs2 ∧
    SubBlockOK p rd2 rs1 ∧
    (∀ j : I64, (rd1.contains j || rd2.contains j) = indd1.contains j) := by
  intro p indd1 inds1 l s sdf rd1 rd2 ssf rs1 rs2
  obtain ⟨hpd1, hpd2, hpd3, hpd4⟩ := hpd
  obtain ⟨hps1, hps2, hps3, hps4⟩ := hps
  have hlen_nat : ((pd.2 - pd.1 + 1).toNat : Int) = pd.2 - pd.1 + 1 := by omega
  have hindd_len : indd1.len = (pd.2 - pd.1 + 1).toNat := by
    dsimp only [indd1, p, copySpec]
    rw [unitRange_len_eq pd.1 (pd.1 + ↑(pd.2 - pd.1 + 1).toNat - 1) (by omega) (by omega) (by omega) (by omega)]
    omega
  have hl_val : l.val = pd.2 - pd.1 + 1 := by
    dsimp only [l]; rw [hindd_len, int_val _ (by omega) (by omega)]; omega
  have hsub_val : (inds1.start - indd1.start).val = ps.1 - pd.1 := by
    dsimp only [inds1, indd1, p, copySpec]
    change (JInt.wrap .i64 ((int ps.1).val - (int pd.1).val)).val = ps.1 - pd.1
    rw [int_val ps.1 (by omega) (by omega), int_val pd.1 (by omega) (by omega)]
    exact int_val (ps.1 - pd.1) hdiff_i64.1 hdiff_i64.2
  have hmod : intMod (inds1.start - indd1.start) l = .ok s := by
    rw [intMod_pos _ _ (by rw [hl_val]; omega), hsub_val, hl_val]
  let L := pd.2 - pd.1 + 1
  have hs0 : 0 ≤ (ps.1 - pd.1) % L := Int.emod_nonneg _ (by omega)
  have hs1 : (ps.1 - pd.1) % L < L := Int.emod_lt_of_pos _ (by omega)
  have hlast_d : indd1.last = int (pd.1 + L - 1) := by
    dsimp only [indd1, p, copySpec, L]
    rw [unitRange_last_eq _ _ (by omega) (by omega) (by omega), hlen_nat]
  have hlast_s : inds1.last = int (ps.1 + L - 1) := by
    dsimp only [inds1, p, copySpec, L]
    rw [unitRange_last_eq _ _ (by omega) (by omega) (by omega), hlen_nat]
  have hsdf : sdf = int (pd.1 + (ps.1 - pd.1) % L) := by
    dsimp only [sdf, indd1, p, copySpec, s, L]
    change JInt.wrap .i64 ((int pd.1).val + (int ((ps.1 - pd.1) % L)).val) = int (pd.1 + (ps.1 - pd.1) % L)
    rw [int_val pd.1 (by omega) (by omega), int_val ((ps.1 - pd.1) % L) (by omega) (by omega)]; rfl
  have hsdf1 : sdf - int 1 = int (pd.1 + (ps.1 - pd.1) % L - 1) := by
    rw [hsdf]
    change JInt.wrap .i64 ((int (pd.1 + (ps.1 - pd.1) % L)).val - (int 1).val) =
      int (pd.1 + (ps.1 - pd.1) % L - 1)
    rw [int_val (pd.1 + (ps.1 - pd.1) % L) (by omega) (by omega), int_one]; rfl
  have hssf : ssf = int (ps.1 + L - 1 - (ps.1 - pd.1) % L) := by
    dsimp only [ssf, s, L]
    rw [hlast_s]
    change JInt.wrap .i64 ((int (ps.1 + L - 1)).val - (int ((ps.1 - pd.1) % L)).val) =
      int (ps.1 + L - 1 - (ps.1 - pd.1) % L)
    rw [int_val (ps.1 + L - 1) (by omega) (by omega),
      int_val ((ps.1 - pd.1) % L) (by omega) (by omega)]; rfl
  have hrd1 : rd1 = unitRange (int pd.1) (int (pd.1 + (ps.1 - pd.1) % L - 1)) := by
    dsimp only [rd1, indd1, p, copySpec]; rw [hsdf1]; rfl
  have hrd2 : rd2 = unitRange (int (pd.1 + (ps.1 - pd.1) % L)) (int (pd.1 + L - 1)) := by
    dsimp only [rd2]; rw [hsdf, hlast_d]
  have hrs1 : rs1 = unitRange (int ps.1) (int (ps.1 + L - 1 - (ps.1 - pd.1) % L)) := by
    dsimp only [rs1, inds1, p, copySpec]; rw [hssf]; rfl
  have hd := Int.mul_ediv_add_emod (ps.1 - pd.1) L
  refine ⟨hmod, ?_, ?_, ?_⟩
  · unfold SubBlockOK
    refine ⟨pd.1, pd.1 + (ps.1 - pd.1) % L - 1, hrd1, ?_⟩
    dsimp only [p, copySpec, L] at hd hs0 hs1 ⊢
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, fun hd_le => ?_⟩
    have hssf1 : ssf + int 1 = int (ps.1 + (pd.2 - pd.1 + 1) - (ps.1 - pd.1) % (pd.2 - pd.1 + 1)) := by
      rw [hssf]
      change JInt.wrap .i64 ((int (ps.1 + (pd.2 - pd.1 + 1) - 1 - (ps.1 - pd.1) % (pd.2 - pd.1 + 1))).val + (int 1).val) =
        int (ps.1 + (pd.2 - pd.1 + 1) - (ps.1 - pd.1) % (pd.2 - pd.1 + 1))
      rw [int_val (ps.1 + (pd.2 - pd.1 + 1) - 1 - (ps.1 - pd.1) % (pd.2 - pd.1 + 1)) (by omega) (by omega), int_one]
      exact congrArg (JInt.wrap .i64) (by omega)
    have hrs2 : rs2 = unitRange (int (ps.1 + (pd.2 - pd.1 + 1) - (ps.1 - pd.1) % (pd.2 - pd.1 + 1)))
        (int (ps.1 + (pd.2 - pd.1 + 1) - 1)) := by
      dsimp only [rs2]; rw [hssf1, hlast_s]
    refine ⟨ps.1 + (pd.2 - pd.1 + 1) - (ps.1 - pd.1) % (pd.2 - pd.1 + 1),
      ps.1 + (pd.2 - pd.1 + 1) - 1, hrs2, ?_⟩
    generalize (ps.1 - pd.1) % (pd.2 - pd.1 + 1) = rem at *
    generalize (ps.1 - pd.1) / (pd.2 - pd.1 + 1) = Q at *
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro j hj1 hj2
    rw [← hlen_eq, emod_of_eq (j - ps.1) (j - pd.1 - rem + (pd.2 - pd.1 + 1)) (pd.2 - pd.1 + 1) (-(Q + 1))
      (by rw [Int.mul_neg, Int.mul_add, Int.mul_one]; omega) (by omega) (by omega)]
    omega
  · unfold SubBlockOK
    refine ⟨pd.1 + (ps.1 - pd.1) % L, pd.1 + L - 1, hrd2, ?_⟩
    dsimp only [p, copySpec, L] at hd hs0 hs1 ⊢
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, fun _ =>
        ⟨ps.1, ps.1 + (pd.2 - pd.1 + 1) - 1 - (ps.1 - pd.1) % (pd.2 - pd.1 + 1), hrs1, ?_⟩⟩
    generalize (ps.1 - pd.1) % (pd.2 - pd.1 + 1) = rem at *
    generalize (ps.1 - pd.1) / (pd.2 - pd.1 + 1) = Q at *
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro j hj1 hj2
    rw [← hlen_eq, emod_of_eq (j - ps.1) (j - pd.1 - rem) (pd.2 - pd.1 + 1) (-Q)
      (by rw [Int.mul_neg]; omega) (by omega) (by omega)]
    omega
  · intro j
    rw [hrd1, hrd2]
    dsimp only [indd1, p, copySpec]
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true,
      unitRange_contains_iff pd.1 (pd.1 + (ps.1 - pd.1) % L - 1) j (by omega) (by omega) (by omega) (by omega),
      unitRange_contains_iff (pd.1 + (ps.1 - pd.1) % L) (pd.1 + L - 1) j
        (by omega) (by omega) (by omega) (by omega),
      unitRange_contains_iff pd.1 (pd.1 + ↑(pd.2 - pd.1 + 1).toNat - 1) j
        (by omega) (by omega) (by omega) (by omega)]
    omega

private theorem circcopyDispatch_spec {VD VS : Type} (conv : VS → VD) (axd : List (Int × Int)) :
    ∀ (axs : List (Int × Int)) (prePs : List DimSpec) (rdest rsrc : CIs)
      (dest : GridArray VD) (src : GridArray VS) (srcFn : CI → VS),
      (∀ p ∈ axd, AxisOK p) →
      (∀ p ∈ axs, AxisOK p) →
      (∀ pd ps, (pd, ps) ∈ axd.zip axs → I64Min ≤ ps.1 - pd.1 ∧ ps.1 - pd.1 ≤ I64Max) →
      axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
      SubBlocksOK prePs rdest rsrc →
      dest.axes = destAxesOf (prePs ++ copySpecs axd axs) →
      src.axes = srcAxesOf (prePs ++ copySpecs axd axs) →
      (∀ K : CI, src.cells K = some (srcFn K)) →
      ∃ out : GridArray VD,
        circcopyDispatch (fun r => int r.len) intMod unitRange (GridArray.copyRegion conv)
          dest rdest (destAxesOf (copySpecs axd axs))
          src rsrc (srcAxesOf (copySpecs axd axs)) = .ok out ∧
        out.identity = dest.identity ∧
        out.axes = dest.axes ∧
        ∀ J : CI, out.cells J =
          if inRegion (rdest ++ destAxesOf (copySpecs axd axs)) J
          then some (conv (srcFn (applyFs (prePs ++ copySpecs axd axs) J)))
          else dest.cells J := by
  induction axd with
  | nil =>
    intro axs prePs rdest rsrc dest src srcFn haxd haxs hdiff hlen hok hdest_ax hsrc_ax hsrc_cells
    cases axs with
    | nil =>
      simp only [copySpecs, List.zipWith_nil_left, destAxesOf, srcAxesOf, List.map_nil,
        List.append_nil] at hdest_ax hsrc_ax ⊢
      unfold circcopyDispatch circcopyBase
      exact copyRegion_of_subBlocksOK conv prePs rdest rsrc hok dest src srcFn hdest_ax hsrc_ax hsrc_cells
    | cons _ _ => simp at hlen
  | cons pd axd ih =>
    intro axs prePs rdest rsrc dest src srcFn haxd haxs hdiff hlen hok hdest_ax hsrc_ax hsrc_cells
    cases axs with
    | nil => simp at hlen
    | cons ps axs =>
      simp only [List.map_cons, List.cons.injEq] at hlen
      have hpd := haxd pd (by simp)
      have hps := haxs ps (by simp)
      have hps_pd := hdiff pd ps (by simp)
      have haxd' : ∀ p ∈ axd, AxisOK p := fun p hp => haxd p (by simp [hp])
      have haxs' : ∀ p ∈ axs, AxisOK p := fun p hp => haxs p (by simp [hp])
      have hdiff' : ∀ pd' ps', (pd', ps') ∈ axd.zip axs → I64Min ≤ ps'.1 - pd'.1 ∧ ps'.1 - pd'.1 ≤ I64Max :=
        fun pd' ps' hp => hdiff pd' ps' (by simp [hp])
      let p := copySpec pd ps
      obtain ⟨hmod, hok1, hok2, hcov⟩ := circcopyCons_step pd ps hpd hps hps_pd hlen.1
      let indd1 := unitRange (int p.ad) (int (p.ad + (p.l : Int) - 1))
      let inds1 := unitRange (int p.as_) (int (p.as_ + (p.l : Int) - 1))
      let l := int indd1.len
      let s := int ((ps.1 - pd.1) % (pd.2 - pd.1 + 1))
      let sdf := indd1.start + s
      let rd1 := unitRange indd1.start (sdf - int 1)
      let rd2 := unitRange sdf indd1.last
      let ssf := inds1.last - s
      let rs1 := unitRange inds1.start ssf
      let rs2 := unitRange (ssf + int 1) inds1.last
      have hap : (prePs ++ [p]) ++ copySpecs axd axs = prePs ++ copySpecs (pd :: axd) (ps :: axs) := by
        simp [copySpecs, p]
      have hok_1 : SubBlocksOK (prePs ++ [p]) (rdest ++ [rd1]) (rsrc ++ [rs2]) :=
        subBlocksOK_append prePs [p] rdest [rd1] rsrc [rs2] hok ⟨hok1, trivial⟩
      have hok_2 : SubBlocksOK (prePs ++ [p]) (rdest ++ [rd2]) (rsrc ++ [rs1]) :=
        subBlocksOK_append prePs [p] rdest [rd2] rsrc [rs1] hok ⟨hok2, trivial⟩
      obtain ⟨dest1, hrun1, hid1, hax1, hcells1⟩ :=
        ih axs (prePs ++ [p]) (rdest ++ [rd1]) (rsrc ++ [rs2]) dest src srcFn haxd' haxs' hdiff' hlen.2 hok_1
          (by rw [hap]; exact hdest_ax) (by rw [hap]; exact hsrc_ax) hsrc_cells
      obtain ⟨dest2, hrun2, hid2, hax2, hcells2⟩ :=
        ih axs (prePs ++ [p]) (rdest ++ [rd2]) (rsrc ++ [rs1]) dest1 src srcFn haxd' haxs' hdiff' hlen.2 hok_2
          (by rw [hax1, hap]; exact hdest_ax) (by rw [hap]; exact hsrc_ax) hsrc_cells
      refine ⟨dest2, ?_, by rw [hid2, hid1], by rw [hax2, hax1], fun J => ?_⟩
      · simp only [copySpecs, List.zipWith_cons_cons, destAxesOf, srcAxesOf, List.map_cons]
        rw [circcopyDispatch]
        unfold circcopyCons
        change (do
          let s ← intMod (inds1.start - indd1.start) l
          let sdf := indd1.start + s
          let rd1 := unitRange indd1.start (sdf - int 1)
          let rd2 := unitRange sdf indd1.last
          let ssf := inds1.last - s
          let rs1 := unitRange inds1.start ssf
          let rs2 := unitRange (ssf + int 1) inds1.last
          let dest ← circcopyDispatch _ _ _ _ dest (rdest ++ [rd1]) (destAxesOf (copySpecs axd axs))
            src (rsrc ++ [rs2]) (srcAxesOf (copySpecs axd axs))
          circcopyDispatch _ _ _ _ dest (rdest ++ [rd2]) (destAxesOf (copySpecs axd axs))
            src (rsrc ++ [rs1]) (srcAxesOf (copySpecs axd axs))) = .ok dest2
        rw [hmod, bind_ok]
        dsimp (config := { proj := false, iota := false }) only
        rw [hrun1, bind_ok, hrun2]
      · rw [hcells2 J, hcells1 J, hap]
        simp only [List.append_assoc, List.singleton_append]
        have hsp := inRegion_split rd1 rd2 indd1 hcov rdest (destAxesOf (copySpecs axd axs)) J
        change _ = if inRegion (rdest ++ indd1 :: destAxesOf (copySpecs axd axs)) J
          then some (conv (srcFn (applyFs (prePs ++ copySpecs (pd :: axd) (ps :: axs)) J))) else dest.cells J
        rw [← hsp]
        cases inRegion (rdest ++ rd1 :: destAxesOf (copySpecs axd axs)) J <;>
          cases inRegion (rdest ++ rd2 :: destAxesOf (copySpecs axd axs)) J <;> rfl

private theorem destAxesOf_copySpecs : ∀ (axd axs : List (Int × Int)),
    (∀ p ∈ axd, AxisOK p) →
    (∀ p ∈ axs, AxisOK p) →
    axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
    destAxesOf (copySpecs axd axs) = axd.map (fun p => unitRange (int p.1) (int p.2)) ∧
    srcAxesOf (copySpecs axd axs) = axs.map (fun p => unitRange (int p.1) (int p.2)) ∧
    (axd.map (fun p => unitRange (int p.1) (int p.2))).map (fun r => int r.len) =
      (axs.map (fun p => unitRange (int p.1) (int p.2))).map (fun r => int r.len)
  | [], [], _, _, _ => ⟨rfl, rfl, rfl⟩
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | pd :: axd, ps :: axs, haxd, haxs, hlen => by
    simp only [List.map_cons, List.cons.injEq] at hlen
    obtain ⟨hpd1, hpd2, hpd3, hpd4⟩ := haxd pd (by simp)
    obtain ⟨hps1, hps2, hps3, hps4⟩ := haxs ps (by simp)
    obtain ⟨hd, hs, hl⟩ := destAxesOf_copySpecs axd axs
      (fun p hp => haxd p (by simp [hp])) (fun p hp => haxs p (by simp [hp])) hlen.2
    have h1 : int (pd.1 + ↑(pd.2 - pd.1 + 1).toNat - 1) = int pd.2 :=
      congrArg (JInt.wrap .i64) (by omega)
    have h2 : int (ps.1 + ↑(pd.2 - pd.1 + 1).toNat - 1) = int ps.2 :=
      congrArg (JInt.wrap .i64) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · unfold destAxesOf copySpecs at hd ⊢
      simp only [List.zipWith_cons_cons, List.map_cons, copySpec, h1, hd]
    · unfold srcAxesOf copySpecs at hs ⊢
      simp only [List.zipWith_cons_cons, List.map_cons, copySpec, h2, hs]
    · simp only [List.map_cons, List.cons.injEq]
      refine ⟨?_, hl⟩
      rw [unitRange_len_eq pd.1 pd.2 (by omega) (by omega) (by omega) (by omega),
        unitRange_len_eq ps.1 ps.2 (by omega) (by omega) (by omega) (by omega), hlen.1]

private theorem applyFs_copySpecs (axd : List (Int × Int)) : ∀ (axs : List (Int × Int)) (J : CI),
    axd.length = axs.length →
    applyFs (copySpecs axd axs) J =
      (J.zip axs).map fun (j, s) => int (s.1 + (j.val - s.1) % (s.2 - s.1 + 1)) := by
  induction axd with
  | nil =>
    intro axs J h
    cases axs with
    | nil => cases J <;> rfl
    | cons _ _ => simp at h
  | cons pd axd ih =>
    intro axs J h
    cases axs with
    | nil => simp at h
    | cons ps axs =>
      cases J with
      | nil => rfl
      | cons j js =>
        have ih' := ih axs js (Nat.succ.inj h)
        unfold copySpecs applyFs at ih' ⊢
        simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons, copySpec, ih']

private theorem copy_fast_path_index (axd : List (Int × Int)) :
    ∀ (axs : List (Int × Int)) (J : CI),
      (∀ p ∈ axd, AxisOK p) →
      (∀ p ∈ axs, AxisOK p) →
      (∀ pd ps, (pd, ps) ∈ axd.zip axs → I64Min ≤ ps.1 - pd.1 ∧ ps.1 - pd.1 ≤ I64Max) →
      axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
      (List.zipWith (fun isrc idest => isrc.start - idest.start)
        (axs.map fun p => unitRange (int p.1) (int p.2))
        (axd.map fun p => unitRange (int p.1) (int p.2))).all (fun x => x == int 0) = true →
      inRegion (axd.map fun p => unitRange (int p.1) (int p.2)) J = true →
      (J.zip ((axs.map fun p => unitRange (int p.1) (int p.2)).zip
        (axd.map fun p => unitRange (int p.1) (int p.2)))).map
          (fun (j, s, d) => int (j.val - d.start.val + s.start.val)) =
      (J.zip axs).map (fun (j, s) => int (s.1 + (j.val - s.1) % (s.2 - s.1 + 1))) := by
  induction axd with
  | nil =>
    intro axs J _ _ _ hlen _ _
    cases axs with
    | nil => cases J <;> rfl
    | cons _ _ => simp at hlen
  | cons pd axd ih =>
    intro axs J haxd haxs hdiff hlen hall hin
    cases axs with
    | nil => simp at hlen
    | cons ps axs =>
      cases J with
      | nil => simp [inRegion_cons_nil] at hin
      | cons j js =>
        simp only [List.map_cons, List.cons.injEq] at hlen
        simp only [List.map_cons, List.zipWith_cons_cons, List.all_cons, Bool.and_eq_true,
          beq_iff_eq] at hall
        simp only [List.map_cons, inRegion_cons, Bool.and_eq_true] at hin
        obtain ⟨hpd1, hpd2, hpd3, hpd4⟩ := haxd pd (by simp)
        obtain ⟨hps1, hps2, hps3, hps4⟩ := haxs ps (by simp)
        have hps_pd_b := hdiff pd ps (by simp)
        have hsub : (unitRange (int ps.1) (int ps.2)).start.val -
            (unitRange (int pd.1) (int pd.2)).start.val = 0 := by
          have h0 := congrArg Subtype.val hall.1
          change (int ((int ps.1).val - (int pd.1).val)).val = (int 0).val at h0
          rw [int_val ps.1 (by omega) (by omega), int_val pd.1 (by omega) (by omega),
            int_zero, int_val (ps.1 - pd.1) hps_pd_b.1 hps_pd_b.2] at h0
          rw [unitRange_start_val ps.1 ps.2 (by omega) (by omega),
            unitRange_start_val pd.1 pd.2 (by omega) (by omega)]
          omega
        have hj_rng := hin.1
        rw [unitRange_contains_iff pd.1 pd.2 j (by omega) (by omega) (by omega) (by omega)] at hj_rng
        have hst_d := unitRange_start_val pd.1 pd.2 (by omega) (by omega)
        have hst_s := unitRange_start_val ps.1 ps.2 (by omega) (by omega)
        simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
        refine ⟨?_, ih axs js (fun p hp => haxd p (by simp [hp]))
          (fun p hp => haxs p (by simp [hp])) (fun pd' ps' hp => hdiff pd' ps' (by simp [hp]))
          hlen.2 hall.2 hin.2⟩
        rw [hst_d, hst_s]
        have hps_pd : ps.1 = pd.1 := by omega
        have hmod_eq : (j.val - ps.1) % (ps.2 - ps.1 + 1) = j.val - ps.1 :=
          Int.emod_eq_of_lt (by omega) (by omega)
        rw [hmod_eq]
        exact congrArg (JInt.wrap .i64) (by omega)

/-- `circcopy!(dest, src)` on nonempty arrays of the same size copies `src` with each
dimension indexed modulo its length: `dest[J] == src[K]` where `K ≡ J (mod size)` lies in
the axes of `src`, for all `Int64`-representable unit-range axes and start-index offsets. -/
def CirccopyNonempty : Prop :=
  ∀ (VD VS : Type) (conv : VS → VD) (axd axs : List (Int × Int))
    (destCells : CI → Option VD) (srcFn : CI → VS),
    (∀ p ∈ axd, p.1 ≤ p.2 ∧ IntTy.min .i64 < p.1 ∧ p.2 ≤ IntTy.max .i64 ∧
      p.2 - p.1 + 1 ≤ IntTy.max .i64) →
    (∀ p ∈ axs, p.1 ≤ p.2 ∧ IntTy.min .i64 < p.1 ∧ p.2 ≤ IntTy.max .i64 ∧
      p.2 - p.1 + 1 ≤ IntTy.max .i64) →
    (∀ pd ps, (pd, ps) ∈ axd.zip axs →
      IntTy.min .i64 ≤ ps.1 - pd.1 ∧ ps.1 - pd.1 ≤ IntTy.max .i64) →
    axd.map (fun p => p.2 - p.1 + 1) = axs.map (fun p => p.2 - p.1 + 1) →
    let destAxes := axd.map (fun p => unitRange (int p.1) (int p.2))
    let srcAxes := axs.map (fun p => unitRange (int p.1) (int p.2))
    let dest : GridArray VD := ⟨0, destAxes, destCells⟩
    let src : GridArray VS := ⟨1, srcAxes, fun K => some (srcFn K)⟩
    ∃ out : GridArray VD,
      GridArray.circcopy conv dest src = .ok out ∧
      ∀ J : CI, (J.length == destAxes.length && cartesianIndicesContains J destAxes) = true →
        out.cells J = some (conv (srcFn
          ((J.zip axs).map fun (j, s) => int (s.1 + (j.val - s.1) % (s.2 - s.1 + 1)))))

theorem circcopyNonempty : CirccopyNonempty := by
  intro VD VS conv axd axs destCells srcFn haxd haxs hdiff hlen destAxes srcAxes dest src
  have haxd_ok : ∀ p ∈ axd, AxisOK p := by
    intro p hp; obtain ⟨h1, h2, h3, h4⟩ := haxd p hp
    refine ⟨h1, ?_, le_i64Max_of_le_max h3, le_i64Max_of_le_max h4⟩
    revert h2; simp [IntTy.min, IntTy.signed, IntTy.bits]
  have haxs_ok : ∀ p ∈ axs, AxisOK p := by
    intro p hp; obtain ⟨h1, h2, h3, h4⟩ := haxs p hp
    refine ⟨h1, ?_, le_i64Max_of_le_max h3, le_i64Max_of_le_max h4⟩
    revert h2; simp [IntTy.min, IntTy.signed, IntTy.bits]
  have hdiff_ok : ∀ pd ps, (pd, ps) ∈ axd.zip axs → I64Min ≤ ps.1 - pd.1 ∧ ps.1 - pd.1 ≤ I64Max := by
    intro pd ps hp; obtain ⟨h1, h2⟩ := hdiff pd ps hp
    exact ⟨i64Min_le_of_min_le h1, le_i64Max_of_le_max h2⟩
  obtain ⟨hd_ax, hs_ax, hl_ax⟩ := destAxesOf_copySpecs axd axs haxd_ok haxs_ok hlen
  unfold GridArray.circcopy JuliaLean.base.multidimensional.circcopy
  dsimp (config := { proj := false, iota := false }) only
  have hid : (dest.identity == src.identity) = false := rfl
  have hsz : ¬ (src.axes.map (fun r => int r.len) != dest.axes.map (fun r => int r.len)) = true := by
    simp [dest, src, destAxes, srcAxes, hl_ax]
  rw [ite_eq_right (by rw [hid]; decide), ite_eq_right hsz]
  by_cases hall : (List.zipWith (fun isrc idest => isrc.start - idest.start) src.axes dest.axes).all
      (fun x => x == int 0) = true
  · rw [ite_eq_left hall]
    unfold GridArray.copy
    dsimp (config := { proj := false, iota := false }) only [bind, Except.bind, pure, Except.pure]
    refine ⟨_, rfl, fun J hJ => ?_⟩
    dsimp only
    rw [show (J.length == dest.axes.length && cartesianIndicesContains J dest.axes) = true from hJ,
      copy_fast_path_index axd axs J haxd_ok haxs_ok hdiff_ok hlen hall hJ]
    rfl
  · rw [ite_eq_right hall]
    obtain ⟨out, hout, _, _, hcells⟩ :=
      circcopyDispatch_spec conv axd axs [] [] [] dest src srcFn haxd_ok haxs_ok hdiff_ok hlen trivial
        (by simp [dest, destAxes, hd_ax]) (by simp [src, srcAxes, hs_ax]) (fun K => rfl)
    simp only [hd_ax, hs_ax] at hout
    refine ⟨out, hout, fun J hJ => ?_⟩
    have hJ' := hcells J
    simp only [List.nil_append, hd_ax] at hJ'
    unfold inRegion at hJ'
    have hlen_ax : axd.length = axs.length := by
      have := congrArg List.length hlen; simpa using this
    rw [hJ, applyFs_copySpecs axd axs J hlen_ax] at hJ'
    exact hJ'
/-- Cartesian range equality agrees with shape-and-element array equality. -/
def CartesianEqArrays : Prop :=
  ∀ ranges other : CIs, ranges.length = other.length →
    (∀ r ∈ ranges, r.WF) → (∀ r ∈ other, r.WF) →
    cartesianIndicesEq ordinalRangeEq ranges other =
      (cartesianIndicesSize (fun r => int r.len) ranges ==
        cartesianIndicesSize (fun r => int r.len) other &&
        columnMajor (ranges.map Rng.elems) == columnMajor (other.map Rng.elems))

theorem cartesianEqArrays_refuted : ¬ CartesianEqArrays := by
  intro h
  let empty : Rng := ⟨int 1, int 1, 0⟩
  let two : Rng := ⟨int 1, int 1, 2⟩
  let other : Rng := ⟨int 3, int 1, 2⟩
  have bad := h [empty, two] [empty, other] rfl
    (by intro r hr; simp [empty, two] at hr; rcases hr with rfl | rfl <;>
        simp [JuliaLean.base.multidimensional.Rng.WF, JuliaLean.base.multidimensional.Rng.elem, int,
          JInt.wrap, wrapInt, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max] <;> omega)
    (by intro r hr; simp [empty, other] at hr; rcases hr with rfl | rfl <;>
        simp [JuliaLean.base.multidimensional.Rng.WF, JuliaLean.base.multidimensional.Rng.elem, int,
          JInt.wrap, wrapInt, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max] <;> omega)
  have counter : cartesianIndicesEq ordinalRangeEq [empty, two] [empty, other] = false := by decide +kernel
  have expected : ((cartesianIndicesSize (fun r => int r.len) [empty, two] ==
      cartesianIndicesSize (fun r => int r.len) [empty, other]) &&
      columnMajor ([empty, two].map Rng.elems) == columnMajor ([empty, other].map Rng.elems)) = true := by decide +kernel
  rw [counter, expected] at bad
  contradiction

/-- Shape mismatches must be rejected even if the destination region is empty. -/
def CopytoSizeChecked : Prop :=
  ∀ (V : Type) (dest src : CellArray V) (Rd Rs : CIs),
    Rd.length = Rs.length →
    cartesianIndicesSize (fun r => int r.len) Rd ≠ cartesianIndicesSize (fun r => int r.len) Rs →
    ∃ msg, CellArray.copyRegion dest Rd src Rs = .error (.argumentError msg)

theorem copytoSizeChecked_refuted : ¬ CopytoSizeChecked := by
  intro h
  let dest : CellArray I64 := ⟨0, [⟨int 1, int 1, 2⟩], [some (int 0), some (int 0)]⟩
  let src : CellArray I64 := ⟨1, [⟨int 1, int 1, 3⟩], [some (int 1), some (int 2), some (int 3)]⟩
  obtain ⟨msg, bad⟩ := h I64 dest src [⟨int 1, int 1, 0⟩] [⟨int 1, int 1, 3⟩] rfl (by decide)
  have counter : CellArray.copyRegion dest [⟨int 1, int 1, 0⟩] src [⟨int 1, int 1, 3⟩] = .ok dest := by
    decide +kernel
  rw [counter] at bad
  contradiction

/-- Addition of coordinates is commutative despite machine-integer wrapping. -/
def CartesianAddCommutes : Prop := ∀ a b : CI, cartesianAdd a b = cartesianAdd b a

theorem cartesianAddCommutes : CartesianAddCommutes := by
  intro a
  induction a with
  | nil => intro b; cases b <;> rfl
  | cons x xs ih =>
    intro b
    cases b with
    | nil => rfl
    | cons y ys =>
      have comm : x + y = y + x := by
        apply Subtype.ext
        change wrapInt .i64 (x.val + y.val) = wrapInt .i64 (y.val + x.val)
        rw [Int.add_comm]
      change (x + y) :: cartesianAdd xs ys = (y + x) :: cartesianAdd ys xs
      rw [comm, ih]

private theorem coordinate_neg_twice (x : I64) : -(-x) = x := by
  apply Subtype.ext
  have bounds := x.property
  change wrapInt .i64 (-wrapInt .i64 (-x.val)) = x.val
  simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at bounds ⊢
  omega

/-- Negation is an involution, including the two's-complement minimum coordinate. -/
def CartesianNegInvolutive : Prop := ∀ index : CI, cartesianNeg (cartesianNeg index) = index

theorem cartesianNegInvolutive : CartesianNegInvolutive := by
  intro index
  induction index with
  | nil => rfl
  | cons x xs ih => simpa only [cartesianNeg, List.map_cons, coordinate_neg_twice] using congrArg (x :: ·) ih

private theorem zipWith_commutes (f : I64 → I64 → I64)
    (commutes : ∀ x y, f x y = f y x) (a b : CI) :
    List.zipWith f a b = List.zipWith f b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys => simp [commutes x y, ih]

/-- Coordinate-wise minimum and maximum are commutative. -/
def CartesianMinMaxCommutes : Prop := ∀ a b : CI,
  cartesianMin a b = cartesianMin b a ∧ cartesianMax a b = cartesianMax b a

theorem cartesianMinMaxCommutes : CartesianMinMaxCommutes := by
  intro a b
  constructor
  · apply zipWith_commutes
    intro x y
    by_cases h : x.val ≤ y.val <;> by_cases h' : y.val ≤ x.val
    · have equal : x = y := Subtype.ext (by omega)
      simp [equal]
    · simp [h, h']
    · simp [h, h']
    · omega
  · apply zipWith_commutes
    intro x y
    by_cases h : x.val ≤ y.val <;> by_cases h' : y.val ≤ x.val
    · have equal : x = y := Subtype.ext (by omega)
      simp [equal]
    · simp [h, h']
    · simp [h, h']
    · omega

/-! ## Logical mask selection -/

/-- With a valid output count, scanning returns the first true key in iterator order. -/
def LogicalSelection : Prop :=
  ∀ (M K S : Type) (readMask : M → K → Bool) (L : LogicalIndex M) (n : I64)
    (trace : List (K × S)), n ≤ L.sum →
    logicalIterate (fun m k => .ok (readMask m k)) L n trace =
      match trace.find? (fun pair => readMask L.mask pair.1) with
      | none => .error .typeError
      | some (key, state) => .ok (some (key, (n + int 1, state)))

private theorem scan_selection {M K S : Type} (readMask : M → K → Bool)
    (L : LogicalIndex M) (n : I64) (trace : List (K × S)) :
    logicalIterate.scan (fun m k => .ok (readMask m k)) L n trace =
      match trace.find? (fun pair => readMask L.mask pair.1) with
      | none => .error .typeError
      | some (key, state) => .ok (some (key, (n + int 1, state))) := by
  induction trace with
  | nil => rfl
  | cons pair rest ih =>
    cases pair with
    | mk key state =>
      cases h : readMask L.mask key <;>
        simp [logicalIterate.scan, List.find?, h, pure, Except.pure, bind, Except.bind, ih]

theorem logicalSelection : LogicalSelection := by
  intro M K S readMask L n trace valid
  rw [logicalIterate, ite_eq_right (by change ¬ L.sum.val < n.val; change n.val ≤ L.sum.val at valid; omega)]
  exact scan_selection readMask L n trace

/-- The retained mask's current true positions govern every iterator cursor.
The array getter is a foreign-file interface, required to read the specified
current Boolean cells at the underlying iterator's valid keys. -/
def LogicalIndexTracksMask : Prop :=
  ∀ (M K S : Type) (readMask : M → K → Result Bool) (mask : M)
    (before after : List Bool) (trace : List (K × S)) (position : Nat),
    before.length = after.length → trace.length = after.length →
    (after.length : Int) ≤ IntTy.max .i64 → position ≤ after.length →
    (∀ pair ∈ trace.zip after, readMask mask pair.1.1 = .ok pair.2) →
    let L : LogicalIndex M := ⟨mask, int (before.count true)⟩
    let n := int ((after.take position).count true + 1)
    (logicalIterate readMask L n (trace.drop position)).map
      (fun output => output.map (fun pair => pair.1)) =
      .ok ((((trace.drop position).zip (after.drop position)).find? (fun pair => pair.2)).map
        (fun pair => pair.1.1))

theorem logicalIndexTracksMask_refuted : ¬ LogicalIndexTracksMask := by
  intro h
  have bad := h (List Bool) I64 I64 vectorRead [true, true] [true, false] [true, true]
    [(int 1, int 2), (int 2, int 3)] 1 rfl rfl (by decide) (by decide)
    (by
      intro pair member
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide)
  have counter :
      ((logicalIterate vectorRead (⟨[true, true], int 1⟩ : LogicalIndex (List Bool))
        (int 2) [(int 2, int 3)]).map (fun output => output.map (fun pair => pair.1))) = .ok none := by
    decide +kernel
  change ((logicalIterate vectorRead (⟨[true, true], int 1⟩ : LogicalIndex (List Bool))
    (int 2) [(int 2, int 3)]).map (fun output => output.map (fun pair => pair.1))) =
      (Except.ok (some (int 2)) : LR (Option I64)) at bad
  rw [counter] at bad
  contradiction

/-! ## Generated traversal order -/

private theorem columnMajor_length (axes : List CI) :
    (columnMajor axes).length = (axes.map List.length).prod := by
  induction axes with
  | nil => rfl
  | cons axis rest ih =>
    have constantSum : ∀ xs : List CI,
        (xs.map (fun _ => axis.length)).sum = xs.length * axis.length := by
      intro xs
      induction xs with
      | nil => simp
      | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]
    simp [columnMajor, List.length_flatMap, constantSum, ih, Nat.mul_comm]

private theorem repeat_flatMap {A B : Type} (xs : List A) (ys : List B) :
    ys.flatMap (fun _ => xs) = (List.replicate ys.length xs).flatten := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [ih, List.replicate_succ]

private theorem columnMajor_order (axis : CI) (rest : List CI) :
    (columnMajor (axis :: rest)).filterMap List.head? =
      (List.replicate (rest.map List.length).prod axis).flatten := by
  simp only [columnMajor, List.filterMap_flatMap, List.filterMap_map]
  simp only [Function.comp_def, List.head?_cons, List.filterMap_some]
  rw [repeat_flatMap, columnMajor_length]

private theorem gatherLoop_linear_trace {Dest Src V : Type} (D : List I64)
    (getindex : Src → CI → Result V) (setindex : Dest → V → I64 → Result Dest)
    (contents : Dest → List V) (valOf : CI → V)
    (hset : ∀ a v k, contents a = contents a → ∃ a', setindex a v k = .ok a' ∧ contents a' = contents a ++ [v])
    (src : Src) (trace : List CI)
    (hget : ∀ coords ∈ trace, getindex src coords = .ok (valOf coords))
    (dest : Dest) (idx state : I64) :
    ∃ out, gatherLoop (m := Result) D (fun D s => .ok (precheckedLinearNext D s))
      getindex setindex src trace dest (idx, state) = .ok out ∧
      contents out = contents dest ++ trace.map valOf := by
  induction trace generalizing dest idx state with
  | nil =>
    exact ⟨dest, by simp [gatherLoop, pure, Except.pure], by simp⟩
  | cons coords rest ih =>
    have hg : getindex src coords = .ok (valOf coords) := hget coords (by simp)
    obtain ⟨dest', hs, hc⟩ := hset dest (valOf coords) idx rfl
    obtain ⟨out, hout, hcout⟩ := ih (fun c hc' => hget c (by simp [hc'])) dest'
      (state + int 1) (state + int 1)
    refine ⟨out, ?_, ?_⟩
    · simp only [gatherLoop, hg, hs, bind, Except.bind]
      exact hout
    · rw [hcout, hc, List.append_assoc, List.singleton_append, List.map_cons]

/-- The generated gather visits the first coordinate fastest, and performs one
write for every combination of selector elements using `_prechecked_iterate` on `LinearIndices`. -/
def GeneratedTraversal : Prop :=
  ∀ (Dest Src V : Type) (getindex : Src → CI → Result V) (setindex : Dest → V → I64 → Result Dest)
    (contents : Dest → List V) (valOf : CI → V) (dest : Dest) (src : Src) (axes : List CI),
    (axes.length : Int) ≤ IntTy.max .i64 →
    contents dest = [] →
    (∀ coords ∈ columnMajor axes, getindex src coords = .ok (valOf coords)) →
    (∀ a v k, ∃ a', setindex a v k = .ok a' ∧ contents a' = contents a ++ [v]) →
    ∃ output : Dest,
      unsafeGetindexBang
        (generateUnsafeGetindexBody (m := Result)
          (fun _ => List.replicate (axes.map List.length).prod (int 1))
          (fun D => .ok (precheckedLinearFirst (fun _ => int 1) D))
          (fun D s => .ok (precheckedLinearNext D s)) id getindex setindex)
        (int axes.length) dest src axes = .ok output ∧
      (contents output).length = (axes.map List.length).prod ∧
      contents output = (columnMajor axes).map valOf ∧
      ∀ axis rest, axes = axis :: rest →
        ((columnMajor axes).filterMap List.head?) = (List.replicate (rest.map List.length).prod axis).flatten

private theorem takeN_length {α : Type} : ∀ (xs : List α), takeN xs xs.length = xs
  | [] => rfl
  | x :: xs => by dsimp [takeN]; rw [takeN_length xs]

private theorem toNat_ofNat (n : Nat) : (n : Int).toNat = n := rfl

private theorem takeN_int_length {α : Type} (xs : List α) (h : (xs.length : Int) ≤ I64Max) :
    takeN xs (int xs.length).val.toNat = xs := by
  rw [int_val xs.length (by omega) (by omega), toNat_ofNat, takeN_length]

theorem generatedTraversal : GeneratedTraversal := by
  intro Dest Src V getindex setindex contents valOf dest src axes hlen hdest hget hset
  have htake := takeN_int_length axes (le_i64Max_of_le_max hlen)
  obtain ⟨out, hout, hcout⟩ := gatherLoop_linear_trace
    (List.replicate (axes.map List.length).prod (int 1))
    getindex setindex contents valOf (fun a v k _ => hset a v k)
    src (columnMajor axes) hget dest (int 1) (int 1)
  rw [hdest, List.nil_append] at hcout
  refine ⟨out, ?_, ?_, hcout, ?_⟩
  · dsimp only [unsafeGetindexBang, generateUnsafeGetindexBody, precheckedLinearFirst,
      bind, Except.bind, pure, Except.pure]
    rw [htake, List.map_id]
    exact hout
  · rw [hcout, List.length_map, columnMajor_length]
  · intro axis rest h
    rw [h]
    exact columnMajor_order axis rest

/-! ## Exception projections for runtime counterexamples -/

/-- Circular copying must succeed for distinct equal-size arrays, including empty axes. -/
def CirccopyCorrect : Prop :=
  ∀ (V : Type) (dest src : CellArray V), dest.identity ≠ src.identity →
    dest.axes.length = src.axes.length →
    (∀ r ∈ dest.axes, r.WF) → (∀ r ∈ src.axes, r.WF) →
    dest.axes.map (·.len) = src.axes.map (·.len) →
    dest.cells.length = (dest.axes.map (·.len)).prod →
    src.cells.length = (src.axes.map (·.len)).prod →
    ∃ out, circcopyOutcome dest src = .ok out

theorem circcopyCorrect_refuted : ¬ CirccopyCorrect := by
  intro h
  let dest : CellArray I64 := ⟨0, [⟨int 3, int 1, 0⟩], []⟩
  let src : CellArray I64 := ⟨1, [⟨int 1, int 1, 0⟩], []⟩
  obtain ⟨out, bad⟩ := h I64 dest src (by decide) rfl
    (by intro r hr; simp [dest] at hr; subst r; decide)
    (by intro r hr; simp [src] at hr; subst r; decide) rfl rfl rfl
  have counter : circcopyOutcome dest src = .error .divideError := by
    decide +kernel
  rw [counter] at bad
  contradiction

/-- Every valid permutation of a strided finite array succeeds, including offset axes. -/
def PermutedimsOffsetCorrect : Prop :=
  ∀ (V : Type) (source : CellArray V), (∀ r ∈ source.axes, r.WF) →
    source.cells.length = (source.axes.map (·.len)).prod →
    ∀ perm : CI, perm.length = source.axes.length → permutationValid perm = true →
      ∃ output, permutedArrayOutcome source perm = .ok output

theorem permutedimsOffsetCorrect_refuted : ¬ PermutedimsOffsetCorrect := by
  intro h
  let source : CellArray I64 := ⟨0, [⟨int 2, int 1, 2⟩], [some (int 7), some (int 8)]⟩
  obtain ⟨out, bad⟩ := h I64 source
    (by
      intro r hr
      simp [source] at hr
      subst r
      simp [JuliaLean.base.multidimensional.Rng.WF, JuliaLean.base.multidimensional.Rng.elem, int,
        JInt.wrap, wrapInt, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max]
      omega) rfl
    [int 1] rfl (by decide)
  have counter : permutedArrayOutcome source [int 1] =
      .error (.dimensionMismatch "destination tensor of incorrect size") := by decide +kernel
  rw [counter] at bad
  contradiction


/-- Aliasing detection must report a shared parent position, including one selected
through an array of CartesianIndex values. This is the condition that permits
assignment to preserve the original right-hand side. -/
def AliasAssignFresh : Prop :=
  ∀ (V : Type) (parent : CellArray V) (I J : List AliasData.Idx) (position : List Int),
    position ∈ AliasData.positions I → position ∈ AliasData.positions J →
    Alias.mightalias (parent, I) (parent, J) = .ok true

theorem aliasAssignFresh_refuted : ¬ AliasAssignFresh := by
  intro h
  let parent : CellArray I64 := ⟨0, [⟨int 1, int 1, 3⟩, ⟨int 1, int 1, 3⟩],
    ([1, 4, 7, 2, 5, 8, 3, 6, 9] : List Int).map (fun x => some (int x))⟩
  have bad := h I64 parent [.scalar 1, .urange 1 3]
    [.carts 2 [[3, 3], [2, 2], [1, 1]]] [1, 1] (by decide) (by decide)
  have counter :
      Alias.mightalias (parent, [.scalar 1, .urange 1 3])
        (parent, [.carts 2 [[3, 3], [2, 2], [1, 1]]]) = .ok false := by decide +kernel
  rw [counter] at bad
  contradiction

/-! ## Additional Cartesian algebra, iteration, split, and index-trait invariants -/

private theorem map_const_range (c : I64) : ∀ n : Nat,
    (List.range n).map (fun _ => c) = List.replicate n c
  | 0 => rfl
  | n + 1 => by simp [List.range_succ, map_const_range c n, List.replicate_succ']

private theorem add_zero_type_and_sub_self (a : CI) :
    cartesianAdd a (cartesianZeroType a.length) = a ∧
    cartesianSub a a = cartesianZeroType a.length := by
  unfold cartesianZeroType
  rw [map_const_range]
  induction a with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    unfold cartesianAdd cartesianSub at ih ⊢
    simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons,
      add_int_zero, sub_self_i64, ih.1, ih.2, and_self]
private theorem flattenDispatch_eq : ∀ (xss : List CI),
    flattenDispatch xss = .ok xss.flatten
  | [] => by rw [flattenDispatch]; rfl
  | [x] => by rw [flattenDispatch]; simp [flattenSingle]
  | h :: x :: xs => by
    have ih := flattenDispatch_eq (x :: xs)
    rw [flattenDispatch]
    unfold flattenCons flattenSingle
    rw [bind_ok, ih, bind_ok]
    rfl

/-- `CartesianIndex` construction, padding, flattening, accessors, coordinate scaling,
Boolean equality, additive identity/inverse for `zero`/`oneunit`, display, disabled
iteration/range errors, and injectivity of 1D `CartesianIndex` hashing when the
coordinate hash is injective. -/
def CartesianAlgebraAndHash : Prop :=
  (∀ (Z : Type) (toI64 : Z → I64) (xs : List Z) (one : Z) (N : Nat)
    (xss : List CI) (v : I64) (j : I64) (a : CI)
    (setidx : CI → I64 → I64 → Result CI),
    cartesianInner (μ := Result) (fun z => .ok (toI64 z)) xs = .ok (xs.map toI64) ∧
    cartesianTuple (μ := Result) (cartesianInner (fun z => .ok (toI64 z))) xs = .ok (xs.map toI64) ∧
    cartesianVarargs (μ := Result) (cartesianInner (fun z => .ok (toI64 z))) xs = .ok (xs.map toI64) ∧
    cartesianSizedVarargs (cartesianInner (fun z => .ok (toI64 z))) xs = .ok (xs.map toI64) ∧
    cartesianSizedIntegers (cartesianInner (fun z => .ok (toI64 z))) xs = .ok (xs.map toI64) ∧
    cartesianPad (fun ys o M => .ok (ys ++ List.replicate (M - ys.length) o))
      (cartesianInner (fun z => .ok (toI64 z))) one N xs =
        .ok ((xs ++ List.replicate (N - xs.length) one).map toI64) ∧
    cartesianDefault (cartesianPad (fun ys o M => .ok (ys ++ List.replicate (M - ys.length) o))
      .ok (int 1) N) = .ok (List.replicate N (int 1)) ∧
    cartesianIdentity a = a ∧
    cartesianToTuple a = a ∧
    ind2subCartesian () a = a ∧
    cartesianPos a = a ∧
    flattenEmpty = ([] : CI) ∧
    flattenSingle (fun x : CI => .ok x) a = .ok a ∧
    cartesianMixed flattenDispatch (cartesianMixedTuple (cartesianTuple (μ := Result) (cartesianInner .ok))) xss =
      .ok xss.flatten ∧
    cartesianLength a = int a.length ∧
    cartesianTypeLength N = int N ∧
    cartesianGetindex tupleGet a j = tupleGet a j ∧
    cartesianFirstindex (fun _ => int 1) a = int 1 ∧
    cartesianLastindex cartesianLength a = int a.length ∧
    cartesianSetindex setidx (cartesianTuple (cartesianInner .ok)) a v j = setidx a v j ∧
    cartesianZeroValue cartesianZeroType a = cartesianZeroType a.length ∧
    cartesianOneValue cartesianOneType a = cartesianOneType a.length) ∧
  (∀ (h : CI) (t : List CI),
    flattenCons (flattenSingle .ok) (fun _ => flattenDispatch t) h t =
      .ok (h :: t).flatten) ∧
  (∀ (Z : Type) (mul : Z → I64 → I64) (s : Z) (a : CI),
    cartesianScaleLeft (fun c x => .ok (mul c x)) (cartesianInner (μ := Result) .ok) s a =
      .ok (a.map (mul s)) ∧
    cartesianScaleRight (cartesianScaleLeft (fun c x => .ok (mul c x)) (cartesianInner (μ := Result) .ok)) a s =
      .ok (a.map (mul s))) ∧
  (∀ (A V T F E : Type) (get : A → CI → V → Result V) (arr : A) (a : CI) (dflt : V)
    (fieldtype : T → String → F) (eltype : F → E) (t : T)
    (convNum : I64 → Result V) (convTup : CI → Result V) (x : I64),
    arrayGetCartesian get arr a dflt = get arr a dflt ∧
    cartesianEltype fieldtype eltype t = eltype (fieldtype t "I") ∧
    cartesianConvertNumber (cartesianGetindex tupleGet) convNum [x] = convNum x ∧
    cartesianConvertTuple convTup a = convTup a) ∧
  (∀ (IO R Z : Type) (print : IO → String → Result IO) (join : IO → CI → String → Result IO)
    (printStep : IO → String → CI → String → CI → String → I64 → String → Result IO)
    (first step : R → CI) (len : R → I64) (io : IO) (a b : CI) (r : R) (z : Z)
    (showIdx : CI → String) (showL : Z → String),
    showCartesian print join io a =
      (do let io ← print io "CartesianIndex("; let io ← join io a ", "; print io ")") ∧
    showCartesianStepRange printStep first step len io r =
      printStep io "StepRangeLen(" (first r) ", " (step r) ", " (len r) ")" ∧
    cartesianIterateDisabled (fun msg => (.error (.errorException msg) : Result CI)) a =
      .error (.errorException "iteration is deliberately unsupported for CartesianIndex. Use `I` rather than `I...`, or use `Tuple(I)...`") ∧
    (cartesianRangeLengthDisabled a b z showIdx showL : Result R) =
      .error (.errorException ("range with a specified length is deliberately unsupported for CartesianIndex arguments. Use StepRangeLen(" ++
        showIdx a ++ ", " ++ showIdx b ++ ", " ++ showL z ++ ") to construct this range")) ∧
    cartesianRangeContainsWrongRank a r = false) ∧
  (∀ a b : CI, cartesianEq a b = true ↔ a = b) ∧
  (∀ N : Nat, (cartesianZeroType N).length = N ∧ (cartesianOneType N).length = N) ∧
  (∀ a : CI, cartesianAdd a (cartesianZeroType a.length) = a ∧
    cartesianSub a a = cartesianZeroType a.length) ∧
  (∀ (hash : I64 → JInt .u64 → JInt .u64),
    (∀ x y s, hash x s = hash y s → x = y) →
    ∀ x y seed, cartesianHash hash [x] seed = cartesianHash hash [y] seed → x = y)

theorem cartesianAlgebraAndHash : CartesianAlgebraAndHash := by
  refine ⟨?_, ?_, ?_, ?_,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩,
    fun a b => by simp [cartesianEq],
    fun N => by simp [cartesianZeroType, cartesianOneType],
    add_zero_type_and_sub_self, fun hash hinj x y seed h => hinj x y _ h⟩
  · intro Z toI64 xs one N xss v j a setidx
    have hm := mapM_ok_eq_map toI64 xs
    have hm_pad := mapM_ok_eq_map toI64 (xs ++ List.replicate (N - xs.length) one)
    have hm_fl : List.mapM (fun x => (.ok x : Result I64)) xss.flatten = .ok xss.flatten := by
      simpa using mapM_ok_eq_map id xss.flatten
    have hset_eq : cartesianSetindex setidx (cartesianTuple (cartesianInner .ok)) a v j = setidx a v j := by
      unfold cartesianSetindex cartesianTuple cartesianInner cartesianToTuple
      cases setidx a v j with
      | error _ => rfl
      | ok r => dsimp only [bind, Except.bind]; simpa using mapM_ok_eq_map id r
    rw [hset_eq]
    unfold cartesianTuple cartesianVarargs cartesianSizedVarargs cartesianSizedIntegers
      cartesianPad cartesianDefault cartesianInner cartesianIdentity
      ind2subCartesian cartesianPos flattenEmpty flattenSingle cartesianMixed cartesianMixedTuple
      cartesianLength cartesianTypeLength cartesianGetindex cartesianFirstindex
      cartesianLastindex cartesianZeroValue cartesianOneValue
    dsimp only
    simp [cartesianToTuple, List.nil_append, Nat.sub_zero, hm, hm_pad, flattenDispatch_eq, hm_fl,
      bind, Except.bind]
  · intro h t
    unfold flattenCons flattenSingle
    rw [bind_ok, flattenDispatch_eq, bind_ok]
    rfl
  · intro Z mul s a
    have hm := mapM_ok_eq_map (mul s) a
    have hm_id : List.mapM (fun x => (.ok x : Result I64)) (a.map (mul s)) = .ok (a.map (mul s)) := by
      simpa using mapM_ok_eq_map id (a.map (mul s))
    unfold cartesianScaleRight cartesianScaleLeft cartesianInner
    rw [hm, bind_ok, hm_id]
    exact ⟨rfl, rfl⟩
  · intro A V T F E get arr a dflt fieldtype eltype t convNum convTup x
    have ht1 : tupleGet [x] (int 1) = .ok x := tupleGet_one x []
    refine ⟨rfl, rfl, ?_, rfl⟩
    unfold cartesianConvertNumber cartesianGetindex
    rw [ht1, bind_ok]

private theorem mapTupleM_ok_iff {α β γ : Type} (f : α → β → γ) :
    ∀ (xs : List α) (ys : List β),
      mapTupleM (fun x y => (.ok (f x y) : Result γ)) xs ys =
        if xs.length = ys.length then .ok (List.zipWith f xs ys)
        else .error (.argumentError "tuple dimensions differ")
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [mapTupleM, bind_ok, mapTupleM_ok_iff f xs ys, List.length_cons, Nat.succ.injEq]
    by_cases h : xs.length = ys.length <;> simp [h, pure, Except.pure, bind, Except.bind]

private theorem subsetCartesian_refl (isempty : CIs → Bool) : ∀ (a : CIs),
    subsetCartesian isempty (· == ·) a a = true := by
  intro a
  unfold subsetCartesian
  cases isempty a with
  | true => rfl
  | false =>
    simp only [Bool.false_or]
    induction a with
    | nil => rfl
    | cons r rs ih => simp only [List.zipWith_cons_cons, List.all_cons, id_eq, beq_self_eq_true, Bool.true_and, ih]

private theorem split1_and_rest_eq {A : Type} (l : List A) : ∀ (r : List Bool),
    split1Dispatch l r = l.take r.length ∧ splitrestDispatch l r = l.drop r.length := by
  induction l with
  | nil => intro r; cases r <;> exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    intro r
    cases r with
    | nil => exact ⟨rfl, rfl⟩
    | cons b bs =>
      simp only [split1Dispatch, split1Cons, splitrestDispatch, splitrestCons,
        List.length_cons, List.take_succ_cons, List.drop_succ_cons, (ih bs).1, (ih bs).2, and_self]

/-- `CartesianIndices` constructors, `_convert2ind`, `show`, colon range construction,
conversions, rank-mismatch equality/membership, axes, scalar and range indexing, views,
`to_indices`, `in`, `intersect`, and `issubset`. -/
def CartesianIndicesAndRegions : Prop :=
  (∀ (I S J : CI) (iter a b : CIs) (subrange : Rng → I64 → Rng) (inter : Rng → Rng → Rng),
    cartesianColon (fun lo hi => .ok (unitRange lo hi)) I J =
      (if I.length = J.length then .ok (List.zipWith unitRange I J)
       else .error (.argumentError "tuple dimensions differ")) ∧
    (I.length = S.length →
      cartesianStepColon (fun lo st hi => .ok ({ start := lo, step := st, len := hi.val.toNat } : Rng)) I S J =
        (if I.length = J.length then
          .ok (List.zipWith (fun pair hi => ({ start := pair.1, step := pair.2, len := hi.val.toNat } : Rng)) (I.zip S) J)
         else .error (.argumentError "tuple dimensions differ"))) ∧
    cartesianIndicesGetindex (fun _ _ => .ok ()) (fun r i => .ok (r.start + (i - int 1) * r.step)) iter I =
      (if iter.length = I.length then .ok (List.zipWith (fun r i => r.start + (i - int 1) * r.step) iter I)
       else .error (.argumentError "tuple dimensions differ")) ∧
    cartesianIndicesGetindex (fun _ _ => .error .boundsError) (fun r i => .ok (r.start + (i - int 1) * r.step)) iter I =
      .error .boundsError ∧
    cartesianIndicesGetindexRanges (fun _ _ => .ok ()) (fun r i => .ok (subrange r i)) iter I =
      (if iter.length = I.length then .ok (List.zipWith subrange iter I)
       else .error (.argumentError "tuple dimensions differ")) ∧
    intersectCartesian (fun r1 r2 => .ok (inter r1 r2)) a b =
      (if a.length = b.length then .ok (List.zipWith inter a b)
       else .error (.argumentError "tuple dimensions differ")) ∧
    subsetCartesian (fun rs => rs.any (·.len == 0)) (· == ·) a a = true ∧
    subsetCartesian (fun rs => rs.any (·.len == 0)) (· == ·) a b =
      (a.any (·.len == 0) || (List.zipWith (· == ·) a b).all id) ∧
    cartesianIndicesContains [] [] = true ∧
    ∀ (i : I64) (is : CI) (r : Rng) (rs : CIs),
      cartesianIndicesContains (i :: is) (r :: rs) = (r.contains i && cartesianIndicesContains is rs)) ∧
  (∀ (A AX Tail O : Type) (toIdx : Rng → O) (toTail : List AX → List Tail → List O)
    (arr : A) (inds : List AX) (head : CIs) (head0 : O) (tail : List Tail),
    toIndicesCartesianRegion (splitTuple split1Dispatch splitrestDispatch)
      (fun _ r => .ok (toIdx r)) (fun _ rest tl => .ok (toTail rest tl)) arr inds head tail =
        .ok (head.map toIdx ++ toTail (inds.drop head.length) tail) ∧
    toIndicesCartesianRegionZero (fun _ rest tl => .ok (toTail rest tl)) arr inds head0 tail =
      .ok (head0 :: toTail inds tail)) ∧
  (∀ (R A U T IO : Type) (toRng : R → Rng) (rs : List R) (sz : CI) (arr : A) (axesOf : A → CIs)
    (toU : Rng → U) (prom : R → R → T) (r1 r2 : R) (r : Rng) (iter _C : CIs) (_I : CI)
    (_subR : Rng → Rng → Rng) (print : IO → String → Result IO) (showIO : IO → CIs → Result IO) (io : IO),
    cartesianIndicesEmpty = ([] : CIs) ∧
    cartesianIndicesRanges (fun x => .ok (toRng x)) rs = .ok (rs.map toRng) ∧
    cartesianIndicesMixed (convert2indInteger (fun n => .ok (unitRange (int 1) n)))
      (cartesianIndicesRanges .ok) sz = .ok (sz.map (unitRange (int 1))) ∧
    cartesianIndicesIndex (cartesianIndicesMixed
      (convert2indInteger (fun n => .ok (unitRange (int 1) n))) (cartesianIndicesRanges .ok)) sz =
      .ok (sz.map (unitRange (int 1))) ∧
    cartesianIndicesArray axesOf (cartesianIndicesRanges .ok) arr = .ok (axesOf arr) ∧
    convert2indBool (fun (b : JInt .i8) => unitRange (int 1) (int b.val)) true = unitRange (int 1) (int 1) ∧
    convert2indBool (fun (b : JInt .i8) => unitRange (int 1) (int b.val)) false = unitRange (int 1) (int 0) ∧
    convert2indUnitRange (·.start) Rng.last (fun lo hi => .ok (unitRange lo hi)) r =
      .ok (unitRange r.start r.last) ∧
    convert2indOrdinal (·.start) Rng.last (·.step)
      (fun lo st hi => .ok ({ start := lo, step := st, len := hi.val.toNat } : Rng)) r =
      .ok ({ start := r.start, step := r.step, len := r.last.val.toNat } : Rng) ∧
    xformIndex r = r ∧
    xformOneTo Rng.last r = r.last ∧
    showCartesianIndices print showIO xformIndex io iter =
      (do let io ← print io "CartesianIndices("; let io ← showIO io iter; print io ")") ∧
    showCartesianIndicesPlain showIO io iter = showIO io iter ∧
    cartesianIndicesPromote prom r1 r2 = prom r1 r2 ∧
    cartesianIndicesConvertEmpty iter = ([] : CIs) ∧
    cartesianIndicesConvertRanges (fun x => .ok (toU x)) iter = .ok (iter.map toU) ∧
    cartesianIndicesConvertAbstractUnit (cartesianIndicesConvertRanges .ok) iter = .ok iter ∧
    cartesianIndicesConvertUnitInt (cartesianIndicesConvertRanges .ok) (fun x => .ok (toU x)) iter =
      .ok (iter.map toU) ∧
    cartesianIndicesConvertUnit (cartesianIndicesConvertRanges .ok) (fun x => .ok (toU x)) iter =
      .ok (iter.map toU) ∧
    cartesianIndicesConvertVarargAbstractUnitInt (cartesianIndicesConvertRanges .ok) iter = .ok iter ∧
    cartesianIndicesConvertVarargAbstractUnit (cartesianIndicesConvertRanges .ok) iter = .ok iter ∧
    cartesianIndicesConvertVarargUnitInt (cartesianIndicesConvertRanges .ok) iter = .ok iter ∧
    cartesianIndicesConvertVarargUnit (cartesianIndicesConvertRanges .ok) iter = .ok iter ∧
    cartesianIndicesConvert (cartesianIndicesConvertRanges .ok) (cartesianIndicesRanges .ok) iter = .ok iter) ∧
  (∀ (A : Type) (arr : A) (axesOf : A → CIs) (iter C : CIs) (I : CI) (subR : Rng → Rng → Rng),
    cartesianIndicesEqWrongRank iter C = false ∧
    cartesianIndicesAxes (fun x => unitRange (int 1) (int x.len)) iter = regionIndexAxes iter ∧
    cartesianIndicesHasOffset (fun it => it.any (fun x => x.start != int 1)) iter =
      iter.any (fun x => x.start != int 1) ∧
    cartesianIndicesGetindexZero iter = ([] : CI) ∧
    cartesianIndicesGetindexRegion (cartesianIndicesGetindexRanges (fun _ _ => .ok ())
      (fun x c => .ok (subR x c))) iter C =
        (if iter.length = C.length then .ok (List.zipWith subR iter C)
         else .error (.argumentError "tuple dimensions differ")) ∧
    cartesianIndicesGetindexZeroRegion iter C = iter ∧
    cartesianIndicesViewRanges (cartesianIndicesGetindexRanges (fun _ _ => .ok ())
      (fun x _ => .ok x)) iter I =
        (if iter.length = I.length then .ok (List.zipWith (fun x _ => x) iter I)
         else .error (.argumentError "tuple dimensions differ")) ∧
    cartesianIndicesViewRegion (cartesianIndicesGetindexRegion
      (cartesianIndicesGetindexRanges (fun _ _ => .ok ()) (fun x c => .ok (subR x c)))) iter C =
        (if iter.length = C.length then .ok (List.zipWith subR iter C)
         else .error (.argumentError "tuple dimensions differ")) ∧
    eachindexCartesian axesOf arr = axesOf arr ∧
    cartesianIndicesSize (fun x => int x.len) iter = iter.map (fun x => int x.len) ∧
    cartesianIndicesStep iter = iter.map (·.step) ∧
    cartesianIndicesContainsWrongRank I iter = false ∧
    cartesianIndicesCopy iter = iter)

theorem cartesianIndicesAndRegions : CartesianIndicesAndRegions := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I S J iter a b subrange inter
    refine ⟨mapTupleM_ok_iff unitRange I J, fun hIS => ?_,
      by simpa [cartesianIndicesGetindex, bind_ok, pure, Except.pure] using
        mapTupleM_ok_iff (fun (r : Rng) (i : I64) => r.start + (i - int 1) * r.step) iter I,
      rfl,
      by simpa [cartesianIndicesGetindexRanges, bind_ok, pure, Except.pure] using
        mapTupleM_ok_iff subrange iter I,
      mapTupleM_ok_iff inter a b, subsetCartesian_refl _ a, rfl, rfl, fun _ _ _ _ => rfl⟩
    unfold cartesianStepColon
    have hlen : (I.zip S).length = I.length := by simp [hIS]
    dsimp only
    rw [mapTupleM_ok_iff (fun (pair : I64 × I64) (hi : I64) => ({ start := pair.1, step := pair.2, len := hi.val.toNat } : Rng)) (I.zip S) J, hlen]
  · intro A AX Tail O toIdx toTail arr inds head head0 tail
    have hsp := split1_and_rest_eq inds (List.replicate head.length true)
    simp only [List.length_replicate] at hsp
    unfold toIndicesCartesianRegion toIndicesCartesianRegionZero splitTuple
    dsimp only
    rw [hsp.2, mapM_ok_eq_map toIdx head, bind_ok]
    exact ⟨rfl, rfl⟩
  · intro R A U T IO toRng rs sz arr axesOf toU prom r1 r2 r iter C I subR print showIO io
    have hrs := mapM_ok_eq_map toRng rs
    have hsz := mapM_ok_eq_map (unitRange (int 1)) sz
    have hsz_ok : List.mapM (fun x => (.ok x : Result Rng)) (sz.map (unitRange (int 1))) =
        .ok (sz.map (unitRange (int 1))) := by simpa using mapM_ok_eq_map id (sz.map (unitRange (int 1)))
    have hit_ok : List.mapM (fun x => (.ok x : Result Rng)) iter = .ok iter := by
      simpa using mapM_ok_eq_map id iter
    have hit_u := mapM_ok_eq_map toU iter
    have hax_ok : List.mapM (fun x => (.ok x : Result Rng)) (axesOf arr) = .ok (axesOf arr) := by
      simpa using mapM_ok_eq_map id (axesOf arr)
    have hb1 : convert2indBool (fun (b : JInt .i8) => unitRange (int 1) (int b.val)) true =
        unitRange (int 1) (int 1) := by decide
    have hb0 : convert2indBool (fun (b : JInt .i8) => unitRange (int 1) (int b.val)) false =
        unitRange (int 1) (int 0) := by decide
    rw [hb1, hb0]
    unfold cartesianIndicesEmpty cartesianIndicesRanges cartesianIndicesMixed
      cartesianIndicesIndex cartesianIndicesArray convert2indInteger
      convert2indUnitRange convert2indOrdinal xformIndex xformOneTo showCartesianIndices
      showCartesianIndicesPlain cartesianIndicesPromote cartesianIndicesConvertEmpty
      cartesianIndicesConvertRanges cartesianIndicesConvertAbstractUnit
      cartesianIndicesConvertUnitInt cartesianIndicesConvertUnit
      cartesianIndicesConvertVarargAbstractUnitInt cartesianIndicesConvertVarargAbstractUnit
      cartesianIndicesConvertVarargUnitInt cartesianIndicesConvertVarargUnit
      cartesianIndicesConvert
    dsimp only
    simp [hrs, hsz, hsz_ok, hit_ok, hax_ok, hit_u, List.map_id', bind_ok]
  · intro A arr axesOf iter C I subR
    have hreg : cartesianIndicesGetindexRegion (cartesianIndicesGetindexRanges (fun _ _ => .ok ())
        (fun x c => .ok (subR x c))) iter C =
        (if iter.length = C.length then .ok (List.zipWith subR iter C)
         else .error (.argumentError "tuple dimensions differ")) := by
      simpa [cartesianIndicesGetindexRegion, cartesianIndicesGetindexRanges, bind_ok, pure, Except.pure] using
        mapTupleM_ok_iff subR iter C
    have hvreg : cartesianIndicesViewRegion (cartesianIndicesGetindexRegion
        (cartesianIndicesGetindexRanges (fun _ _ => .ok ()) (fun x c => .ok (subR x c)))) iter C =
        (if iter.length = C.length then .ok (List.zipWith subR iter C)
         else .error (.argumentError "tuple dimensions differ")) := hreg
    have hv : cartesianIndicesViewRanges (cartesianIndicesGetindexRanges (fun _ _ => .ok ())
        (fun x _ => .ok x)) iter I =
        (if iter.length = I.length then .ok (List.zipWith (fun x _ => x) iter I)
         else .error (.argumentError "tuple dimensions differ")) := by
      simpa [cartesianIndicesViewRanges, cartesianIndicesGetindexRanges, bind_ok, pure, Except.pure] using
        mapTupleM_ok_iff (fun (x : Rng) (_ : I64) => x) iter I
    rw [hreg, hvreg, hv]
    unfold cartesianIndicesEqWrongRank cartesianIndicesAxes
      cartesianIndicesHasOffset cartesianIndicesGetindexZero
      cartesianIndicesGetindexZeroRegion
      eachindexCartesian cartesianIndicesSize cartesianIndicesStep
      cartesianIndicesContainsWrongRank cartesianIndicesCopy regionIndexAxes
    simp [cartesianIndicesAxes]

/-- `Base.split` on tuples, `CartesianIndex`, and `CartesianIndices` partitions into `take N`
and `drop N`; zero-rank iteration yields `CartesianIndex()` once then stops; `inc`/`dec` and
`nextind`/`prevind` advance and invert coordinates along `CartesianIndices`; and partition
and SIMD iterators obey their exact step, boundary skip/length, and outer/inner range formulas. -/
def CartesianIterationAndSplit : Prop :=
  (∀ (A : Type) (xs : List A) (I : CI) (R : CIs) (n : Nat),
    splitTuple split1Dispatch splitrestDispatch xs n = (xs.take n, xs.drop n) ∧
    splitCartesian (splitTuple split1Dispatch splitrestDispatch) I n = (I.take n, I.drop n) ∧
    splitCartesianIndices (splitTuple split1Dispatch splitrestDispatch) R n = (R.take n, R.drop n)) ∧
  (cartesianIterateZero false = some ([], true) ∧ cartesianIterateZero true = none ∧
   reverseIterateZero false = some ([], true) ∧ reverseIterateZero true = none) ∧
  (∀ (state : CI) (indices : CIs),
    cartesianInc increment state indices = (increment state indices).2 ∧
    cartesianDec decrement state indices = (decrement state indices).2 ∧
    nextindCartesian id (cartesianInc increment) indices state = (increment state indices).2 ∧
    previndCartesian id (cartesianDec decrement) indices state = (decrement state indices).2) ∧
  (∀ (R : CIs), (∀ r ∈ R, r.WF) → ∀ k : Nat, k + 1 < (elems R).length →
    ∀ s s' : CI, (elems R)[k]? = some s → (elems R)[k + 1]? = some s' →
      nextindCartesian id (cartesianInc increment) R s = s' ∧
      previndCartesian id (cartesianDec decrement) R s' = s) ∧
  (∀ (iter : CIs) (state : CI) (n len : I64),
    partitionIterateFirst List.isEmpty cartesianIndicesFirst ([] : CIs) = none ∧
    (iter ≠ [] →
      partitionIterateFirst List.isEmpty cartesianIndicesFirst iter =
        some (cartesianIndicesFirst iter, (cartesianIndicesFirst iter, int 1))) ∧
    (n.val ≥ len.val →
      partitionIterateNext (fun _ => len) id (cartesianInc increment) iter state n = none) ∧
    (n.val < len.val →
      partitionIterateNext (fun _ => len) id (cartesianInc increment) iter state n =
        some ((increment state iter).2, ((increment state iter).2, n + int 1)))) ∧
  (∀ (q r axisFirst i mi : I64),
    partitionSplitdim1 (fun _ _ => .ok (q, r)) axisFirst i mi = .ok (q + int 1, r + axisFirst)) ∧
  (∀ (af al fl fr ol i : I64) (fO lO I : CI),
    partitionSkipLength af al fl fr ol i I =
      ((if i == int 1 then fl else af) - af,
       (if i == ol then fr else al) - (if i == int 1 then fl else af) + int 1, I) ∧
    partitionSkipLength2 af al fl fr fO lO I =
      ((if I == fO then fl else af) - af,
       (if I == lO then fr else al) - (if I == fO then fl else af) + int 1, I)) ∧
  (∀ (T E S R : Type) (elty itelty : T → E) (subty : E → T → Bool → S) (urty : E → R) (t : T)
    (r1 r2 : Rng) (oci : CIs) (I : CI) (i1 skip len n pf pl ol mi1 mi2 : I64)
    (enumF : CIs → List (I64 × CI)) (elemsF : CIs → List CI),
    simdOuterZero oci = oci ∧
    simdOuter (r1 :: oci) = oci ∧
    simdInnerZero oci I = int 1 ∧
    simdInner (fun r => int r.len) r1 oci I = int r1.len ∧
    simdIndexZero oci I i1 = cartesianIndicesFirst oci ∧
    simdIndex (fun r k => .ok (r.start + (k - int 1) * r.step)) (fun _ => int 1) r1 oci I i1 =
      .ok ((r1.start + ((i1 + int 1) - int 1) * r1.step) :: I) ∧
    partitionEltypeLinear elty subty t = subty (elty t) t true ∧
    partitionEltypeCartesian elty subty t = subty (elty t) t false ∧
    partitionIteratorEltype itelty t = itelty t ∧
    partitionEltypeOneTo elty urty t = urty (elty t) ∧
    partitionEltypeRange t = t ∧
    partitionRangeIteratorEltype itelty t = itelty t ∧
    partitionSimdInner () (skip, len, I) = len ∧
    partitionSimdIndex id (fun _ J k => simdIndex (fun r m => .ok (r.start + (m - int 1) * r.step)) (fun _ => int 1) r1 oci J k)
      (r1 :: oci) (skip, len, I) n = .ok ((r1.start + (((n + skip) + int 1) - int 1) * r1.step) :: I) ∧
    partitionSimdOuter (fun _ => [mi1]) (fun _ => r1 :: oci) (fun _ => r1) (·.start) Rng.last
      (fun _ => pf) (fun _ => pl) (fun x _ => .ok (x, int 0)) (fun _ => int 1)
      (fun rs _ _ => .ok rs) (fun rs _ _ => .ok rs) enumF (fun _ => ol) () =
        .ok ((enumF oci).map fun (i, J) =>
          partitionSkipLength r1.start r1.last (int 0 + r1.start) (int 0 + r1.start) ol i J) ∧
    partitionSimdOuter2 (fun _ => [mi1, mi2]) (fun _ => [r1, r2]) id (fun _ => r1) (·.start) Rng.last
      (fun _ => pf) (fun _ => pl) (fun _ _ x => .ok (x, x)) (fun r _ _ => .ok r) elemsF () =
        .ok ((elemsF [r2]).map fun J =>
          partitionSkipLength2 r1.start r1.last pf pl
            (cartesianIndicesFirst [r2]) (cartesianIndicesLast [r2]) J))

theorem cartesianIterationAndSplit : CartesianIterationAndSplit := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl⟩, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl⟩, ?_⟩
  · intro A xs I R n
    have hxs := split1_and_rest_eq xs (List.replicate n true)
    have hI := split1_and_rest_eq I (List.replicate n true)
    have hR := split1_and_rest_eq R (List.replicate n true)
    simp only [List.length_replicate] at hxs hI hR
    unfold splitCartesian splitCartesianIndices splitTuple
    dsimp only
    rw [hxs.1, hxs.2, hI.1, hI.2, hR.1, hR.2]
    exact ⟨rfl, rfl, rfl⟩
  · intro R hR k hk s s' hs hs'
    have hfw := fw R hR k s hs
    have hbw := bw R hR (k + 1) s' hs'
    rw [hs'] at hfw
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] at hbw
    rw [hs] at hbw
    unfold opt at hfw hbw
    unfold nextindCartesian previndCartesian cartesianInc cartesianDec
    dsimp only [id]
    constructor
    · cases hinc : increment s R with
      | mk valid next =>
        rw [hinc] at hfw
        cases valid with
        | false => simp at hfw
        | true => simp at hfw; exact hfw
    · cases hdec : decrement s' R with
      | mk valid prev =>
        rw [hdec] at hbw
        cases valid with
        | false => simp at hbw
        | true => simp at hbw; exact hbw
  · intro iter state n len
    refine ⟨rfl, fun hne => ?_, fun hge => ?_, fun hlt => ?_⟩
    · unfold partitionIterateFirst
      cases iter with
      | nil => exact absurd rfl hne
      | cons _ _ => rfl
    · unfold partitionIterateNext
      have h : n ≥ len := hge
      rw [ite_eq_left h]
    · unfold partitionIterateNext
      have h : ¬ (n ≥ len) := by change ¬ (len.val ≤ n.val); omega
      rw [ite_eq_right h]; rfl
  · intro T E S R elty itelty subty urty t r1 r2 oci I i1 skip len n pf pl ol mi1 mi2 enumF elemsF
    unfold partitionSimdOuter partitionSimdOuter2 partitionSkipLength partitionSkipLength2
      simdOuterZero simdOuter simdInnerZero simdInner simdIndexZero simdIndex
      partitionEltypeLinear partitionEltypeCartesian partitionIteratorEltype
      partitionEltypeOneTo partitionEltypeRange partitionRangeIteratorEltype
      partitionSimdInner partitionSimdIndex
    dsimp only [id]
    rw [tupleGet_one, tupleGet_two]
    simp [bind_ok, pure, Except.pure, List.tail_cons]

private theorem isassigned_eq_contains (iter : CIs) : ∀ (I : CI),
    iter.length = I.length →
    cartesianIndicesIsassigned Rng.contains iter I = cartesianIndicesContains I iter := by
  induction iter with
  | nil =>
    intro I h
    cases I with
    | nil => rfl
    | cons _ _ => simp at h
  | cons r rs ih =>
    intro I h
    cases I with
    | nil => simp at h
    | cons i is =>
      have ih' := ih is (Nat.succ.inj h)
      unfold cartesianIndicesIsassigned cartesianIndicesContains at ih' ⊢
      simp only [List.zip_cons_cons, List.zipWith_cons_cons, List.all_cons, id_eq, ih']

private theorem checkBooleanAxes_eq_beq (oneToOne : Rng) (is : CIs) : ∀ (as_ : CIs),
    checkBooleanAxesDispatch oneToOne is as_ =
      (if is.length ≤ as_.length then
        (List.zipWith (· == ·) is (as_.take is.length)).all id &&
          (as_.drop is.length).all (· == oneToOne)
       else false) := by
  induction is with
  | nil =>
    intro as_
    simp [checkBooleanAxesDispatch, checkBooleanAxesEmpty]
  | cons i is ih =>
    intro as_
    cases as_ with
    | nil => simp [checkBooleanAxesDispatch]
    | cons a as_ =>
      simp only [checkBooleanAxesDispatch, checkBooleanAxesCons, List.length_cons,
        Nat.add_le_add_iff_right, List.take_succ_cons, List.drop_succ_cons,
        List.zipWith_cons_cons, List.all_cons, id_eq, ih as_]
      by_cases hle : is.length ≤ as_.length
      · simp only [hle, ite_true, Bool.and_assoc]
      · simp only [hle, ite_false, Bool.and_false]

private theorem forIn_collect_append (xs : List CI) : ∀ (acc : List CI) (i : I64),
    (do
      let mut dest := acc
      let mut idx := i
      for a in xs do
        idx := idx + int 1
        dest ← (.ok (dest ++ [a]) : Result (List CI))
      return dest) = .ok (acc ++ xs) := by
  induction xs with
  | nil =>
    intro acc i
    simp [pure, Except.pure, bind, Except.bind]
  | cons a xs ih =>
    intro acc i
    have ih' := ih (acc ++ [a]) (i + int 1)
    dsimp only at ih' ⊢
    simp only [List.forIn_cons, pure, Except.pure, bind, Except.bind] at ih' ⊢
    rw [ih', List.append_assoc, List.singleton_append]

/-- Step-range membership for `CartesianIndex` (empty, constant-step, and nonzero-step search),
`isassigned` agreement with `in`, multi-array `eachindex` axis-agreement check, `LinearIndices`
unit-step check, full `collect` on `CartesianIndices`, index-trait rank/length/shape equations
for arbitrary tail callbacks, and full `_check_boolean_axes` characterization across all ranks. -/
def IndexTraitsAndQueries : Prop :=
  (∀ (r : CIs) (x : CI) (found : Option I64) (elemAt : I64 → CI),
    cartesianRangeContains (fun _ => true) cartesianIndicesFirst cartesianIndicesStep
      cartesianIndicesLast (fun _ _ _ _ => .ok found) (fun _ n => .ok (elemAt n)) x r = .ok false ∧
    cartesianRangeContains (fun _ => false) (fun _ => [int 1]) (fun _ => [int 0])
      cartesianIndicesLast (fun _ _ _ _ => .ok found) (fun _ n => .ok (elemAt n)) [int 1] r = .ok true ∧
    (∀ k : I64,
      cartesianRangeContains (fun _ => false) (fun _ => [int 1]) (fun _ => [int 2])
        (fun _ => [int 5]) (fun _ _ _ _ => .ok (some k)) (fun _ n => .ok (elemAt n)) [int 3] r =
        .ok (elemAt k == [int 3]))) ∧
  (∀ (iter : CIs) (I : CI), iter.length = I.length →
    cartesianIndicesIsassigned Rng.contains iter I = cartesianIndicesContains I iter) ∧
  (∀ (a : CIs) (bs : List CIs),
    eachindexCartesianMany id (cartesianIndicesRanges .ok) (fun _ _ => .error .dimensionMismatch) a bs =
      if bs.all (· == a) then .ok a else .error .dimensionMismatch) ∧
  (∀ (inds : CIs) (tyName : String),
    linearIndicesUnit (fun rs => linearIndices unitRange .ok rs (fun _ => tyName)) inds =
      linearIndices unitRange .ok inds (fun _ => tyName) ∧
    linearIndices unitRange (linearIndicesUnit .ok) inds (fun _ => tyName) =
      if inds.all (fun r => r.step.val == 1) then
        .ok (inds.map fun rng => unitRange rng.start rng.last)
      else .error (.argumentError ("LinearIndices for " ++ tyName ++ " with non-1 step size is not yet supported."))) ∧
  (∀ (inds : CIs),
    collectCartesianUnit regionIndexAxes
      (fun _ it => collectCartesian (fun _ => .ok ([] : List CI))
        (cartesianIndicesSize (fun r => int r.len))
        (fun rs => columnMajor (rs.map Rng.elems))
        (fun acc x _ => .ok (acc ++ [x])) it)
      inds = .ok (columnMajor (inds.map Rng.elems)) ∧
    collectCartesian (fun _ => .ok ([] : List CI)) (cartesianIndicesSize (fun r => int r.len))
      (fun rs => columnMajor (rs.map Rng.elems))
      (fun acc x _ => .ok (acc ++ [x])) inds = .ok (columnMajor (inds.map Rng.elems))) ∧
  (∀ (S A : Type) (axesOf : A → CIs) (sizeOf : A → CI) (lenOf : A → I64)
    (s : S) (head : CI) (a : A) (tail : List (IndexTraitItem S A)) (rest : List (Sum S A)) (N : Nat),
    indexNdimsEmpty = ([] : List Bool) ∧
    indexDimsumEmpty = ([] : List Bool) ∧
    indexLengthsEmpty = ([] : CI) ∧
    indexShapeEmpty = ([] : CIs) ∧
    indexSizesEmpty = ([] : CI) ∧
    indexNdimsScalar indexNdimsDispatch (IndexTraitItem.scalar s : IndexTraitItem S A) [] = [true] ∧
    indexNdimsScalar indexNdimsDispatch (IndexTraitItem.scalar s) tail = true :: indexNdimsDispatch tail ∧
    (indexNdimsCartesian indexNdimsDispatch head tail).length = head.length + (indexNdimsDispatch tail).length ∧
    (indexNdimsCartesianArray indexNdimsDispatch N a tail).length = N + (indexNdimsDispatch tail).length ∧
    indexDimsumScalar indexDimsumDispatch (IndexTraitItem.scalar s : IndexTraitItem S A) [] = [] ∧
    indexDimsumScalar indexDimsumDispatch (IndexTraitItem.scalar s) tail = indexDimsumDispatch tail ∧
    indexDimsumColon indexDimsumDispatch tail = true :: indexDimsumDispatch tail ∧
    indexDimsumMask indexDimsumDispatch a tail = true :: indexDimsumDispatch tail ∧
    (indexDimsumArray indexDimsumDispatch N a tail).length = N + (indexDimsumDispatch tail).length ∧
    indexLengthsScalar (indexLengthsDispatch lenOf) s ([] : List (Sum S A)) = [int 1] ∧
    indexLengthsScalar (indexLengthsDispatch lenOf) s rest = int 1 :: indexLengthsDispatch lenOf rest ∧
    indexLengthsArray lenOf (indexLengthsDispatch lenOf) a rest = lenOf a :: indexLengthsDispatch lenOf rest ∧
    indexShapeScalar (indexShapeDispatch axesOf) s ([] : List (Sum S A)) = ([] : CIs) ∧
    indexShapeScalar (indexShapeDispatch axesOf) s rest = indexShapeDispatch axesOf rest ∧
    indexShapeArray axesOf (indexShapeDispatch axesOf) a rest = axesOf a ++ indexShapeDispatch axesOf rest ∧
    indexSizesScalar (indexSizesDispatch sizeOf) s ([] : List (Sum S A)) = ([] : CI) ∧
    indexSizesScalar (indexSizesDispatch sizeOf) s rest = indexSizesDispatch sizeOf rest ∧
    indexSizesArray sizeOf (indexSizesDispatch sizeOf) a rest = sizeOf a ++ indexSizesDispatch sizeOf rest) ∧
  (∀ (oneToOne : Rng) (is as_ : CIs),
    checkBooleanAxesDispatch oneToOne is as_ =
      (if is.length ≤ as_.length then
        (List.zipWith (· == ·) is (as_.take is.length)).all id &&
          (as_.drop is.length).all (· == oneToOne)
       else false))

theorem indexTraitsAndQueries : IndexTraitsAndQueries := by
  refine ⟨?_, isassigned_eq_contains, ?_, ?_, ?_, ?_, checkBooleanAxes_eq_beq⟩
  · intro r x found elemAt
    refine ⟨rfl, ?_, fun k => ?_⟩
    · unfold cartesianRangeContains
      have hst : tupleGet [int 0] (int 1) = .ok (int 0) := tupleGet_one _ []
      have hz : ¬ ((int 0).val != 0) = true := by rw [int_zero]; decide
      have h01 : int (((0 : Nat) : Int) + 1) = int 1 := rfl
      simp only [List.length_singleton, List.range_one, List.forIn_cons, List.forIn_nil,
        h01, hst, bind_ok, hz, pure, Except.pure, beq_self_eq_true]
      rfl
    · unfold cartesianRangeContains
      have hst : tupleGet [int 2] (int 1) = .ok (int 2) := tupleGet_one _ []
      have hnz : ((int 2).val != 0) = true := by rw [int_two]; decide
      have hx : tupleGet [int 3] (int 1) = .ok (int 3) := tupleGet_one _ []
      have hf : tupleGet [int 1] (int 1) = .ok (int 1) := tupleGet_one _ []
      have hl : tupleGet [int 5] (int 1) = .ok (int 5) := tupleGet_one _ []
      have h01 : int (((0 : Nat) : Int) + 1) = int 1 := rfl
      simp only [List.length_singleton, List.range_one, List.forIn_cons, List.forIn_nil,
        h01, hst, bind_ok, hnz, ite_true, hx, hf, hl]
      rfl
  · intro a bs
    have ha : List.mapM (fun x => (.ok x : Result Rng)) a = .ok a := by simpa using mapM_ok_eq_map id a
    unfold eachindexCartesianMany cartesianIndicesRanges
    by_cases h : bs.all (· == a) = true <;> simp [h, ha, bind, Except.bind]
  · intro inds tyName
    refine ⟨rfl, ?_⟩
    unfold linearIndices linearIndicesUnit
    by_cases h : inds.all (fun r => r.step.val == 1) = true <;>
      simp [h, throw, throwThe, MonadExceptOf.throw]
  · intro inds
    have hc : collectCartesian (fun _ => .ok ([] : List CI)) (cartesianIndicesSize (fun r => int r.len))
        (fun rs => columnMajor (rs.map Rng.elems)) (fun acc x _ => .ok (acc ++ [x])) inds =
        .ok (columnMajor (inds.map Rng.elems)) := by
      unfold collectCartesian
      rw [bind_ok, forIn_collect_append (columnMajor (inds.map Rng.elems)) [] (int 0), List.nil_append]
    exact ⟨hc, hc⟩
  · intro S A axesOf sizeOf lenOf s head a tail rest N
    simp [indexNdimsDispatch, indexDimsumDispatch, indexLengthsDispatch, indexShapeDispatch, indexSizesDispatch,
      indexNdimsEmpty, indexDimsumEmpty, indexLengthsEmpty, indexShapeEmpty, indexSizesEmpty,
      indexNdimsScalar, indexNdimsCartesian, indexNdimsCartesianArray,
      indexDimsumScalar, indexDimsumColon, indexDimsumMask, indexDimsumArray,
      indexLengthsScalar, indexLengthsArray, indexShapeScalar, indexShapeArray,
      indexSizesScalar, indexSizesArray]

/-- Atomic memory indexing, Cartesian and boolean-mask `checkbounds`/`checkindex`,
`LogicalIndex` constructors/collection/BitArray iteration, `ensure_indexable`,
`to_indices`/`uncolon`, `_prechecked_iterate`, and multidimensional `getindex`/`setindex!`
with `_maybe_reshape` and `_generate_unsafe_setindex!_body`. -/
def LogicalAndMultidimIndexing : Prop :=
  (∀ (M Args I O : Type) (toIdx : M → List I → CI) (callC : M → Args → CI → Result O)
    (callL : M → Args → I64 → Result O) (toLin : M → CI → I64) (toSub : M → CI → CI)
    (isLin : M → Bool) (mem : M) (args : Args) (is : List I) (ci : CI),
    atomicMixed (toIndicesMixed (AX := Rng) (fun m _ xs => .ok (toIdx m xs))) callC mem args is = callC mem args (toIdx mem is) ∧
    atomicCartesian callC mem args ci = callC mem args ci ∧
    atomicIntegers (toIndicesMixed (AX := Rng) (fun m _ xs => .ok (toIdx m xs))) isLin (fun m c => .ok (toLin m c))
      (fun m c => .ok (toSub m c)) callL callC mem args is =
        (if isLin mem then callL mem args (toLin mem (toIdx mem is))
         else callC mem args (toSub mem (toIdx mem is)))) ∧
  (∀ (A AX I R M V : Type) [BEq AX] (axes : A → List AX) (axes1 : M → AX)
    (cbIA : List AX → List I → Bool) (cbRng : CIs → List I → Bool) (ciC : List AX → CI → Bool)
    (cbR : List AX → List R → Bool) (cbCIs : List AX → CIs → Bool)
    (eachLin : A → AX) (ndimsM : M → Nat)
    (isemptyR : R → Bool) (firstR lastR : R → CI) (toIdx : A → List I → CI)
    (getA : A → CI → Result V) (setA : A → V → CI → Result A)
    (a : A) (v : V) (inds : List AX) (ax : AX) (headC : CI) (headI : I) (tailI : List I)
    (tailR : List R) (rng : R) (cis : CIs) (oneToOne : Rng) (axesRng maskRng : CIs)
    (L : LogicalIndex M) (mask : M) (N : Nat),
    checkboundsCartesian axes
      (fun axL cs => match cs with
        | [] => true
        | h :: t => checkboundsIndicesCartesian (checkindexCartesian ciC) (fun _ _ => true) axL h t)
      a headC = (ciC ((axes a).take headC.length) headC && true) ∧
    checkboundsIndicesCartesian (checkindexCartesian ciC) cbIA inds headC tailI =
      (ciC (inds.take headC.length) headC && cbIA (inds.drop headC.length) tailI) ∧
    checkindexCartesian ciC inds headC = ciC inds headC ∧
    checkindexCartesianRange isemptyR firstR lastR (checkindexCartesian ciC) inds rng =
      (isemptyR rng || (ciC inds (firstR rng) && ciC inds (lastR rng))) ∧
    arrayGetMixed (toIndicesMixed (AX := Rng) (fun x _ xs => .ok (toIdx x xs))) getA a headI tailI =
      getA a (toIdx a (headI :: tailI)) ∧
    arraySetMixed (toIndicesMixed (AX := Rng) (fun x _ xs => .ok (toIdx x xs))) setA a v headI tailI =
      setA a v (toIdx a (headI :: tailI)) ∧
    checkboundsCartesianArray axes
      (fun axL cs => match cs with
        | [] => true
        | h :: t => checkboundsIndicesCartesianArray (checkindexCartesianIndices cbCIs) (fun _ _ => true) N axL h t)
      a cis = (cbCIs ((axes a).take N) cis && true) ∧
    checkboundsIndicesCartesianArray (checkindexCartesianIndices cbCIs) cbR N inds cis tailR =
      (cbCIs (inds.take N) cis && cbR (inds.drop N) tailR) ∧
    checkindexCartesianIndices cbCIs inds cis = cbCIs inds cis ∧
    checkboundsLogical (checkboundsVectorMask eachLin (checkindexVectorMask axes1)) a L =
      (axes1 L.mask == eachLin a) ∧
    checkindexLogicalAxis (checkindexRangeMask axes1) ax L = (axes1 L.mask == ax) ∧
    checkindexLogicalTuple (checkindexMaskTuple (fun _ => maskRng) (checkBooleanAxesDispatch oneToOne)) axesRng L =
      (if axesRng.length ≤ maskRng.length then
        (List.zipWith (· == ·) axesRng (maskRng.take axesRng.length)).all id &&
          (maskRng.drop axesRng.length).all (· == oneToOne)
       else false) ∧
    checkboundsMask (fun _ => axesRng)
      (fun axL ms => match ms with
        | [] => true
        | m :: t => checkboundsIndicesMask ndimsM
            (checkindexMaskTuple (fun _ => maskRng) (checkBooleanAxesDispatch oneToOne))
            (fun _ _ => true) axL m t)
      a mask =
        (checkBooleanAxesDispatch oneToOne (axesRng.take (ndimsM mask)) maskRng && true) ∧
    checkboundsVectorMask eachLin (checkindexVectorMask axes1) a mask = (axes1 mask == eachLin a) ∧
    checkboundsIndicesMask ndimsM
      (checkindexMaskTuple (fun _ => maskRng) (checkBooleanAxesDispatch oneToOne))
      cbRng axesRng mask tailI =
        (checkBooleanAxesDispatch oneToOne (axesRng.take (ndimsM mask)) maskRng &&
          cbRng (axesRng.drop (ndimsM mask)) tailI) ∧
    checkindexVectorMask axes1 ax mask = (axes1 mask == ax) ∧
    checkindexRangeMask axes1 ax mask = (axes1 mask == ax) ∧
    checkindexMaskTuple (fun _ => maskRng) (checkBooleanAxesDispatch oneToOne) axesRng mask =
      (if axesRng.length ≤ maskRng.length then
        (List.zipWith (· == ·) axesRng (maskRng.take axesRng.length)).all id &&
          (maskRng.drop axesRng.length).all (· == oneToOne)
       else false)) ∧
  (∀ (M K IO : Type) (cnt : M → I64) (mask : M)
    (readMaskI : M → I64 → LR Bool) (readMaskC : M → CI → LR Bool)
    (printI : IO → List I64 → LR IO) (printArrC : IO → List CI → LR IO) (io : IO)
    (axesM : M → CIs)
    (chunks : M → List I64) (ndims : M → I64) (tz clearLow : I64 → I64) (szM : M → CI)
    (ovf : I64 → CI → CI → I64 × CI) (mkK : I64 → CI → K)
    (c0 : I64) (cs : List I64) (i1 Bi : I64) (irest : CI),
    let stepOptI := fun (L' : LogicalIndex M) (p : I64 × CIs) =>
      logicalIterate readMaskI L' p.1 (linearIterTrace p.2)
    let stepOptC := fun (L' : LogicalIndex M) (p : I64 × CIs) =>
      logicalIterate readMaskC L' p.1 (cartesianIterTrace p.2)
    let stepListI := fun (L' : LogicalIndex M) (p : I64 × CIs) => do
      match ← stepOptI L' p with
      | none => .ok ([] : List I64)
      | some (k, _) => .ok [k]
    let stepListC := fun (L' : LogicalIndex M) (p : I64 × CIs) => do
      match ← stepOptC L' p with
      | none => .ok ([] : List CI)
      | some (k, _) => .ok [k]
    let bitStep := fun (ch : M → List I64) (L' : LogicalIndex M) (p : I64 × I64 × CI × I64) =>
      logicalBitIterate (int 0) ch tz clearLow szM (fun a b d => .ok (ovf a b d))
        (fun a b => .ok (mkK a b)) L' p.1 p.2.1 p.2.2.1 p.2.2.2
    logicalInner (fun m => .ok (cnt m)) mask = .ok ⟨mask, cnt mask⟩ ∧
    logicalVector (logicalInner (fun m => .ok (cnt m))) mask = .ok ⟨mask, cnt mask⟩ ∧
    logicalArray (logicalInner (fun m => .ok (cnt m))) mask = .ok ⟨mask, cnt mask⟩ ∧
    logicalExplicitInt (logicalInner (fun m => .ok (cnt m))) mask = .ok ⟨mask, cnt mask⟩ ∧
    logicalSize (⟨mask, cnt mask⟩ : LogicalIndex M) = [cnt mask] ∧
    (readMaskI mask (int 1) = .ok true → readMaskC mask [int 1] = .ok true →
      logicalCollect (logicalIterateIntFirst (fun _ => linearIndicesUnit .ok [unitRange (int 1) (int 1)]) stepListI) ⟨mask, int 1⟩ =
        .ok [int 1] ∧
      logicalShow (logicalCollect (logicalIterateIntFirst (fun _ => linearIndicesUnit .ok [unitRange (int 1) (int 1)]) stepListI)) printI io ⟨mask, int 1⟩ =
        printI io [int 1] ∧
      logicalPrintArray (logicalCollect (logicalIterateCartesianFirst (fun _ => [unitRange (int 1) (int 1)]) (cartesianIndicesRanges .ok) stepListC)) printArrC io ⟨mask, int 1⟩ =
        printArrC io [[int 1]]) ∧
    logicalIterateIntFirst (fun m => linearIndicesUnit .ok (axesM m)) stepOptI ⟨mask, cnt mask⟩ =
      logicalIterate readMaskI ⟨mask, cnt mask⟩ (int 1) (linearIterTrace (axesM mask)) ∧
    logicalIterateCartesianFirst axesM (cartesianIndicesRanges .ok) stepOptC ⟨mask, cnt mask⟩ =
      logicalIterate readMaskC ⟨mask, cnt mask⟩ (int 1) (cartesianIterTrace (axesM mask)) ∧
    logicalBitIntFirst chunks (bitStep chunks) ⟨mask, int 0⟩ = .ok none ∧
    logicalBitIntFirst (fun _ => c0 :: cs) (bitStep (fun _ => c0 :: cs)) ⟨mask, int 1⟩ =
      (do let r ← bitStep (fun _ => c0 :: cs) ⟨mask, int 1⟩ (int 1, int 1, [], c0); .ok (some r)) ∧
    logicalBitCartesianFirst chunks ndims (bitStep chunks) ⟨mask, int 0⟩ = .ok none ∧
    logicalBitCartesianFirst (fun _ => c0 :: cs) ndims (bitStep (fun _ => c0 :: cs)) ⟨mask, int 1⟩ =
      (do
        let r ← bitStep (fun _ => c0 :: cs) ⟨mask, int 1⟩
          (int 1, int 1, List.replicate ((ndims mask - int 1).val.toNat) (int 1), c0)
        .ok (some r)) ∧
    (c0 != int 0 →
      logicalBitIterate (int 0) chunks tz clearLow szM (fun a b d => .ok (ovf a b d))
        (fun a b => .ok (mkK a b)) ⟨mask, int 1⟩ i1 Bi irest c0 =
          let (i1', irest') := ovf (i1 + tz c0) irest (szM mask)
          .ok (some (mkK i1' irest', (i1' - tz c0, Bi, irest', clearLow c0)))) ∧
    (Bi.val ≥ (chunks mask).length →
      logicalBitIterate (int 0) chunks tz clearLow szM (fun a b d => .ok (ovf a b d))
        (fun a b => .ok (mkK a b)) ⟨mask, int 1⟩ i1 Bi irest (int 0) = .ok none)) ∧
  (∀ (A AX H I M O S R Z : Type) (L : LogicalIndex M) (c : O) (headI : I) (tailI : List I)
    (headH : H) (headCI : CI) (inds : List AX) (ax : AX) (a : A)
    (toIdxI : A → I64 → O) (toIdxH : A → H → O) (toInds : A → List AX → List I → List O)
    (style : A → S) (oneTo : I64 → AX) (slice : AX → O)
    (firstR : R → Z) (stepR : R → S) (addZ : Z → S → Z)
    (iter : CIs) (K i j : I64),
    ensureIndexableEmpty = ([] : List I) ∧
    ensureIndexableCons ensureIndexableDispatch headI tailI = headI :: ensureIndexableDispatch tailI ∧
    ensureIndexableLogical (fun _ => .ok c) (fun xs => .ok ((ensureIndexableDispatch xs).map (fun _ => c))) L tailI =
      .ok (c, (ensureIndexableDispatch tailI).map (fun _ => c)) ∧
    toIndicesMixed (fun x axL xs => .ok (toInds x axL xs)) a tailI = .ok (toInds a [] tailI) ∧
    dropZeroDim (fun xs => toInds a inds xs) headCI tailI = toInds a inds tailI ∧
    toIndicesCartesian (fun x k => .ok (toIdxI x k)) (fun x axL xs => .ok (toInds x axL xs))
      a inds headCI tailI =
        .ok (headCI.map (toIdxI a) ++ toInds a (inds.drop headCI.length) tailI) ∧
    toIndicesCartesianArray (fun x h => .ok (toIdxH x h)) (fun x axL xs => .ok (toInds x axL xs))
      headCI.length a inds headH tailI =
        .ok (toIdxH a headH :: toInds a (inds.drop headCI.length) tailI) ∧
    toIndicesMask (fun x h => .ok (toIdxH x h)) (fun x axL xs => .ok (toInds x axL xs))
      headCI.length a inds headH tailI =
        .ok (toIdxH a headH :: toInds a (inds.drop headCI.length) tailI) ∧
    toIndicesSingleMask style (fun _ x m => maybeLinearLogicalDefault (fun y _ => .ok (toIdxH y headH)) x m)
      a headH = .ok [toIdxH a headH] ∧
    maybeLinearLogicalLinear (logicalInner (fun _ => .ok K)) a headH = .ok ⟨headH, K⟩ ∧
    toIndicesColon (uncolonCons slice ax) (fun x axL xs => .ok (toInds x axL xs))
      a (ax :: inds) tailI = .ok (slice ax :: toInds a inds tailI) ∧
    uncolonEmpty oneTo slice = slice (oneTo (int 1)) ∧
    precheckedFirst (fun r => .ok (firstR r)) = (fun r => .ok (firstR r)) ∧
    precheckedNext (fun r s => .ok (addZ s (stepR r))) = (fun r s => .ok (addZ s (stepR r))) ∧
    precheckedUnitFirst firstR = (fun r => (firstR r, firstR r)) ∧
    precheckedUnitNext stepR (fun x y => .ok (addZ x y)) .ok =
      (fun r x => .ok (addZ x (stepR r), addZ x (stepR r))) ∧
    precheckedLinearFirst (fun _ : R => i) = (fun _ => (i, i)) ∧
    precheckedLinearNext (iter) i = (i + int 1, i + int 1) ∧
    precheckedCartesianFirst iter = (cartesianIndicesFirst iter, cartesianIndicesFirst iter) ∧
    precheckedCartesianNext (cartesianInc increment) iter headCI =
      ((increment headCI iter).2, (increment headCI iter).2) ∧
    precheckedSpecialFirst firstR = (fun r => (firstR r, firstR r)) ∧
    precheckedSpecialNext Prod.mk K i j =
      (let p := if i < K then (i + int 1, j) else (int 1, j + int 1); (p, p))) ∧
  (∀ (S A D I V : Type) (style : S) (a : A) (dest : D) (x : V) (is : List I) (idx0 : I) (k : I64)
    (resh : A → List Bool → Result A) (reshN : A → Nat → Result A)
    (getOne : A → List I64 → Result V) (setOneG : D → V → I64 → Result D)
    (genG : I64 → D → A → List I → Result D)
    (genS : I64 → A → V → List I → Result A) (setOne : A → V → List I64 → Result A) (N : Nat),
    getindexScalarZero x = x ∧
    getindexTupleCartesian tupleGet [k] (int 1) = .ok k ∧
    maybeReshapeLinear a is = a ∧
    maybeReshapeVector a is = a ∧
    maybeReshapeCartesian (fun _ => [true]) resh a is = resh a [true] ∧
    reshapeMatchingRank a N = a ∧
    reshapeDifferentRank reshN a N = reshN a N ∧
    getindexAbstract (fun _ _ => .ok ()) (fun _ y js => .ok (maybeReshapeLinear y js))
      (fun st y js => unsafeGetindex (fun _ => [int 1]) (fun _ _ => .ok dest)
        (fun _ => [int 1]) id (fun d s => throwChecksizeError d s)
        (unsafeGetindexBangOne (generateUnsafeGetindexBody
          (fun _ => [int 1])
          (fun D => .ok (precheckedLinearFirst (fun _ => int 1) D))
          (fun D s => .ok (precheckedLinearNext D s))
          (fun _ => [k]) getOne setOneG)) st y js) style a [idx0] =
      (do let v ← getOne a [k]; setOneG dest v (int 1)) ∧
    unsafeGetindex (fun _ => [int 1]) (fun _ _ => .ok dest) (fun _ => [int 2])
      id (fun d s => throwChecksizeError d s)
      (unsafeGetindexBangOne (generateUnsafeGetindexBody
        (fun _ => [int 1])
        (fun D => .ok (precheckedLinearFirst (fun _ => int 1) D))
        (fun D s => .ok (precheckedLinearNext D s))
        (fun _ => [k]) getOne setOneG)) style a [idx0] =
      .error (.dimensionMismatch "output array is the wrong size; expected , got ") ∧
    unsafeGetindexBang genG k dest a is = genG k dest a is ∧
    unsafeGetindexBangOne genG dest a is = genG (int 1) dest a is ∧
    unsafeGetindexBangTwo genG dest a is = genG (int 2) dest a is ∧
    unsafeSetindexBang genS k style a x is = genS k a x is ∧
    unsafeSetindexBangOne genS style a x is = genS (int 1) a x is ∧
    unsafeSetindexBangTwo genS style a x is = genS (int 2) a x is ∧
    setindexAbstract (fun _ _ => .ok ()) (fun _ y _ => .ok y)
      (unsafeSetindexBangOne (generateUnsafeSetindexBody (fun _ v => .ok v) (fun _ i => .ok i)
        (fun _ => [int 1]) (fun _ _ => .ok ()) (fun _ => [int 1])
        (fun _ => .ok (precheckedLinearFirst (fun _ => int 1) ()))
        (fun _ s => .ok (precheckedLinearNext () s)) (fun _ => [k])
        (fun v _ => .ok v) setOne)) style a x [idx0] =
          (do let _ ← setOne a x [k]; .ok a))

theorem logicalAndMultidimIndexing : LogicalAndMultidimIndexing := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro M Args I O toIdx callC callL toLin toSub isLin mem args is ci
    unfold atomicMixed atomicCartesian atomicIntegers toIndicesMixed cartesianToTuple
    by_cases h : isLin mem = true <;> simp [h, bind_ok]
  · intro A AX I R M V _ axes axes1 cbIA cbRng ciC cbR cbCIs
      eachLin ndimsM isemptyR firstR lastR toIdx getA setA a v inds ax headC headI tailI
      tailR rng cis oneToOne axesRng maskRng L mask N
    unfold checkboundsCartesian checkboundsIndicesCartesian checkindexCartesian
      checkindexCartesianRange arrayGetMixed arraySetMixed toIndicesMixed checkboundsCartesianArray
      checkboundsIndicesCartesianArray checkindexCartesianIndices checkboundsLogical
      checkindexLogicalAxis checkindexLogicalTuple checkboundsMask checkboundsVectorMask
      checkboundsIndicesMask checkindexVectorMask checkindexRangeMask checkindexMaskTuple
    rw [checkBooleanAxes_eq_beq]
    simp [bind_ok]
  · intro M K IO cnt mask readMaskI readMaskC printI printArrC io axesM chunks ndims
      tz clearLow szM ovf mkK c0 cs i1 Bi irest
    dsimp only
    have hgt1 : ¬ (int 1 > int 1) := by decide
    have h10 : (int 1 == int 0) = false := by decide
    have htup : tupleGet (c0 :: cs) (int 1) = .ok c0 := tupleGet_one c0 cs
    have htrI : linearIterTrace [unitRange (int 1) (int 1)] = [(int 1, int 1)] := by decide
    have htrC : cartesianIterTrace [unitRange (int 1) (int 1)] = [([int 1], [int 1])] := by decide
    have hax : List.mapM (fun x => (.ok x : Result Rng)) (axesM mask) = .ok (axesM mask) := by
      simpa using mapM_ok_eq_map id (axesM mask)
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun hrmI hrmC => ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · unfold logicalCollect logicalIterateIntFirst linearIndicesUnit
        dsimp only [bind, Except.bind]
        rw [htrI]
        unfold logicalIterate logicalIterate.scan
        dsimp only
        rw [ite_eq_right hgt1, hrmI, bind_ok]
        simp [List.forIn_cons, List.forIn_nil, pure, Except.pure, bind, Except.bind]
      · unfold logicalShow logicalCollect logicalIterateIntFirst linearIndicesUnit
        dsimp only [bind, Except.bind]
        rw [htrI]
        unfold logicalIterate logicalIterate.scan
        dsimp only
        rw [ite_eq_right hgt1, hrmI, bind_ok]
        simp [List.forIn_cons, List.forIn_nil, pure, Except.pure, bind, Except.bind]
      · unfold logicalPrintArray logicalCollect logicalIterateCartesianFirst cartesianIndicesRanges
        dsimp only [bind, Except.bind, pure, Except.pure, List.mapM, List.mapM.loop,
          List.reverse, List.reverseAux]
        rw [htrC]
        unfold logicalIterate logicalIterate.scan
        dsimp only
        rw [ite_eq_right hgt1, hrmC, bind_ok]
        simp [List.forIn_cons, List.forIn_nil, pure, Except.pure, bind, Except.bind]
    · unfold logicalIterateCartesianFirst cartesianIndicesRanges
      rw [hax, bind_ok]
    · unfold logicalBitIntFirst; simp [pure, Except.pure]
    · unfold logicalBitIntFirst; simp [h10, htup, bind_ok, pure, Except.pure]
    · unfold logicalBitCartesianFirst; simp [pure, Except.pure]
    · unfold logicalBitCartesianFirst; simp [h10, htup, bind_ok, pure, Except.pure]
    · intro hc0
      unfold logicalBitIterate logicalBitIterate.scan
      dsimp only
      rw [ite_eq_left hc0]
      rfl
    · intro hBi
      unfold logicalBitIterate logicalBitIterate.scan
      have hc0 : ¬ ((int 0 != int 0) = true) := by decide
      dsimp only
      rw [ite_eq_right hc0, ite_eq_left hBi]
      rfl
  · intro A AX H I M O S R Z L c headI tailI headH headCI inds ax a toIdxI toIdxH toInds
      style oneTo slice firstR stepR addZ iter K i j
    have hm := mapM_ok_eq_map (toIdxI a) headCI
    unfold ensureIndexableEmpty ensureIndexableCons ensureIndexableLogical toIndicesMixed
      dropZeroDim toIndicesCartesian toIndicesCartesianArray toIndicesMask toIndicesSingleMask
      maybeLinearLogicalDefault maybeLinearLogicalLinear logicalInner toIndicesColon
      uncolonEmpty uncolonCons precheckedFirst precheckedNext precheckedUnitFirst
      precheckedUnitNext precheckedLinearFirst precheckedLinearNext precheckedCartesianFirst
      precheckedCartesianNext cartesianInc precheckedSpecialFirst precheckedSpecialNext
    dsimp only [id, List.tail_cons]
    rw [hm]
    simp [bind_ok, pure, Except.pure]
  · intro S A D I V style a dest x is idx0 k resh reshN getOne setOneG genG genS setOne N
    have ht1 : tupleGet [k] (int 1) = .ok k := tupleGet_one k []
    have hneq : (([int 2] != [int 1])) = true := by decide
    have heq : ¬ ((List.map id [int 1] != List.map id [int 1]) = true) := by decide
    have htake1 : takeN [idx0] (int 1).val.toNat = [idx0] := by rw [int_one]; rfl
    have hget : getindexAbstract (fun _ _ => .ok ()) (fun _ y js => .ok (maybeReshapeLinear y js))
        (fun st y js => unsafeGetindex (fun _ => [int 1]) (fun _ _ => .ok dest)
          (fun _ => [int 1]) id (fun d s => throwChecksizeError d s)
          (unsafeGetindexBangOne (generateUnsafeGetindexBody
            (fun _ => [int 1])
            (fun D => .ok (precheckedLinearFirst (fun _ => int 1) D))
            (fun D s => .ok (precheckedLinearNext D s))
            (fun _ => [k]) getOne setOneG)) st y js) style a [idx0] =
        (do let v ← getOne a [k]; setOneG dest v (int 1)) := by
      unfold getindexAbstract maybeReshapeLinear unsafeGetindex unsafeGetindexBangOne
        generateUnsafeGetindexBody
      dsimp only [List.map_cons, List.map_nil, id]
      rw [bind_ok, bind_ok, bind_ok, ite_eq_right heq, bind_ok, htake1]
      dsimp only [List.map, columnMajor, List.flatMap, List.flatten, List.append, List.append_nil,
        precheckedLinearFirst, gatherLoop]
      cases getOne a [k] with
      | error _ => rfl
      | ok v =>
        dsimp only [bind, Except.bind]
        cases setOneG dest v (int 1) <;> rfl
    have hset : setindexAbstract (fun _ _ => .ok ()) (fun _ y _ => .ok y)
        (unsafeSetindexBangOne (generateUnsafeSetindexBody (fun _ v => .ok v) (fun _ i => .ok i)
          (fun _ => [int 1]) (fun _ _ => .ok ()) (fun _ => [int 1])
          (fun _ => .ok (precheckedLinearFirst (fun _ => int 1) ()))
          (fun _ s => .ok (precheckedLinearNext () s)) (fun _ => [k])
          (fun v _ => .ok v) setOne)) style a x [idx0] =
          (do let _ ← setOne a x [k]; .ok a) := by
      unfold setindexAbstract unsafeSetindexBangOne generateUnsafeSetindexBody
      have hm0 : List.mapM (fun i => (.ok i : Result I)) [idx0] = .ok [idx0] := rfl
      have hcm : columnMajor (List.map (fun (_ : I) => [k]) [idx0]) = [[k]] := rfl
      dsimp only
      rw [bind_ok, bind_ok, hm0, bind_ok, bind_ok, bind_ok, hcm]
      simp only [List.forIn_cons, List.forIn_nil, bind, Except.bind, pure, Except.pure]
      cases setOne a x [k] <;> rfl
    rw [hget, hset]
    unfold getindexScalarZero getindexTupleCartesian maybeReshapeLinear maybeReshapeVector
      maybeReshapeCartesian reshapeMatchingRank reshapeDifferentRank
      unsafeGetindex throwChecksizeError unsafeGetindexBang unsafeGetindexBangOne
      unsafeGetindexBangTwo unsafeSetindexBang unsafeSetindexBangOne unsafeSetindexBangTwo
    dsimp only
    rw [ht1]
    simp [List.map_cons, List.map_nil, hneq, bind, Except.bind]

/-- `BitArray` contiguous/range/general indexing, chunk copying (`copy_to_bitarray_chunks!`),
`fill!`, `isassigned`, `checkdims_perm`, `unique`/`_unique_dims`, `showarg`, `sortslices`/`_sortslices!`,
and 0D `Ref` indexing. -/
def BitArrayAndSliceOps : Prop :=
  (∀ (x : I64),
    tryBoolConversion (· == int 0) (· == int 1) x =
      (if x == int 0 || x == int 1 then .ok () else .error (.inexactError "try_bool_conversion")) ∧
    uncheckedBoolConvert (· == int 1) x = (x == int 1)) ∧
  (∀ (C A : Type) (getidx : A → I64 → Result I64) (setbit : C → Bool → I64 → Result C)
    (Bc : C) (src : A) (pos_s : I64)
    (readC : C → I64 → Result (JInt .u64)) (writeC : C → I64 → JInt .u64 → Result C)
    (bAnd bOr : JInt .u64 → JInt .u64 → JInt .u64) (bNot : JInt .u64 → JInt .u64)
    (shl : JInt .u64 → I64 → JInt .u64),
    copyToBitarrayChunks getidx (fun v => .ok (v == int 1)) setbit Bc (int 1) src pos_s (int 0) =
      some (.ok Bc) ∧
    copyToBitarrayChunksReal getidx (tryBoolConversion (· == int 0) (· == int 1))
      (uncheckedBoolConvert (· == int 1))
      (fun p => if p == int 1 then (int 1, int 0) else (int 0, int 63))
      readC writeC bAnd bOr bNot shl (fun _ => int 0)
      (fun a b => if a ≤ b then [a] else []) Bc (int 1) src pos_s (int 0) = .ok Bc) ∧
  (∀ (A C I V : Type) (chunks : A → C) (setChunks : A → C → A)
    (copyChunks : C → I64 → C → I64 → I64 → Result C)
    (copyChunksX : C → I64 → A → I64 → I64 → Result C)
    (fillChunks : C → Bool → I64 → I64 → Result C)
    (bitget : C → I64 → Result Bool) (bitset : C → Bool → I64 → Result C)
    (offset len firstI : I → I64) (sz : A → I64 → I64)
    (parent : V → A) (updChunks : V → C → V) (updParent : V → A → V)
    (X B : A) (viewData : V) (I0 : I) (e0 : I64) (bval : Bool),
    bitGetindexContiguous chunks setChunks copyChunks offset len X B I0 =
      (do let c ← copyChunks (chunks X) (int 1) (chunks B) (offset I0 + int 1) (len I0); .ok (setChunks X c)) ∧
    bitGetindexRanges chunks setChunks (fun _ => [len I0]) offset sz (fun _ _ => [])
      copyChunks X B I0 [] =
      (do let c ← copyChunks (chunks X) (int 1) (chunks B) (offset I0 + int 1) (len I0); .ok (setChunks X c)) ∧
    bitGetindexGeneral chunks setChunks sz (fun _ => [e0]) bitget bitset X B [I0] =
      (do
        let b ← bitget (chunks B) (int 1 + (e0 - int 1) * int 1)
        let c ← bitset (chunks X) b (int 0 + int 1)
        .ok (setChunks X c)) ∧
    bitSetindexContiguous (fun _ js => .ok js) (fun _ _ => .ok ()) (fun _ => int 0) offset
      (fun _ _ => .ok ()) chunks copyChunksX setChunks B X I0 = .ok B ∧
    bitSetindexRanges (fun _ js => .ok js) (fun _ _ => .ok ())
      (fun b x js => match js with
        | [] => .ok b
        | h :: t => bitUnsafeSetindexRanges chunks setChunks (fun _ => [len I0]) (fun _ => [len I0])
            (fun _ _ => .ok ()) (fun _ => true) offset sz (fun _ => []) copyChunksX b x h t)
      B X I0 [] = .ok B ∧
    bitUnsafeSetindexRanges chunks setChunks (fun _ => [len I0]) (fun _ => [len I0])
      (fun _ _ => .ok ()) (fun _ => true) offset sz (fun _ => []) copyChunksX B X I0 [] = .ok B ∧
    bitUnsafeSetindexRanges chunks setChunks (fun _ => [len I0]) (fun _ => [len I0])
      (fun _ _ => .ok ()) (fun _ => false) offset sz (fun _ => []) copyChunksX B X I0 [] =
      (do let c ← copyChunksX (chunks B) (offset I0 + int 1) X (int 1) (len I0); .ok (setChunks B c)) ∧
    bitSetindexAbstract (fun _ => ()) (fun _ js => .ok js)
      (fun _ b x js => match js with
        | [] => .ok b
        | h :: t => bitUnsafeSetindexRanges chunks setChunks (fun _ => [len I0]) (fun _ => [len I0])
            (fun _ _ => .ok ()) (fun _ => true) offset sz (fun _ => []) copyChunksX b x h t)
      B X I0 [] = .ok B ∧
    bitFillContiguous parent (fun _ => [I0]) (fun _ => int 0) firstI chunks
      (fun b => .ok b) fillChunks updChunks viewData bval = .ok viewData ∧
    bitFillRanges parent (fun _ => [I0])
      (fun b v _ => bitUnsafeFillIndices chunks setChunks (fun z => .ok z) (fun _ => [int 1])
        offset (fun _ => false) sz (fun _ => []) fillChunks b v I0 [])
      updParent viewData bval =
      (do
        let c ← fillChunks (chunks (parent viewData)) bval (offset I0 + int 1) (int 1)
        .ok (updParent viewData (setChunks (parent viewData) c))) ∧
    bitUnsafeFillIndices chunks setChunks (fun z => .ok z) (fun _ => [int 0])
      offset (fun _ => false) sz (fun _ => []) fillChunks B bval I0 [] = .ok B) ∧
  (∀ (A I V : Type) (sz : A → I64 → I64) (isa1 : A → I64 → Bool) (isaC : A → CI → Result Bool)
    (toIdx : A → List I → CI) (getA : A → CI → Result V)
    (B : A) (I0 i1 : I64) (ci : CI) (is : List I),
    bitIsassigned sz isa1 B I0 [] = isa1 B I0 ∧
    bitIsassigned sz isa1 B I0 [i1] =
      (if !(int 1 ≤ I0 ∧ I0 ≤ sz B (int 1)) then false
       else isa1 B (I0 + (i1 - int 1) * (int 1 * sz B (int 1)))) ∧
    isassignedCartesian isaC B ci = isaC B ci ∧
    isassignedMixed (fun a xs => .ok (toIdx a xs)) isaC B is = isaC B (toIdx B is) ∧
    isassignedIntegers (fun a xs => .ok (toIdx a xs)) (fun _ _ => false)
      (fun _ => true) (fun _ => 1) (fun _ _ => .ok I0) (fun _ c => .ok c)
      (fun a k => .ok (isa1 a k)) isaC getA (fun _ => true) (fun _ => true) B is = .ok false ∧
    isassignedIntegers (fun _ _ => .ok [I0]) (fun _ _ => true)
      (fun _ => true) (fun _ => 1) (fun _ _ => .ok I0) (fun _ c => .ok c)
      (fun a k => .ok (isa1 a k)) isaC (fun _ _ => (.error .boundsError : Result V))
      (fun e => e == .boundsError) (fun _ => false) B is = .ok false ∧
    isassignedIntegers (fun _ _ => .ok [I0]) (fun _ _ => true)
      (fun _ => true) (fun _ => 1) (fun _ _ => .ok I0) (fun _ c => .ok c)
      (fun a k => .ok (isa1 a k)) isaC getA
      (fun e => e == .boundsError) (fun _ => false) B is =
        (match getA B [I0] with
         | .ok _ => .ok true
         | .error e => if e == .boundsError then .ok false else .error e)) ∧
  (∀ (A BType AX P D K S I IO T R Z : Type) [BEq AX] (axesA : A → List AX) (axesB : BType → List AX)
    (dest : BType) (B : A) (perm : CI)
    (copyA : A → Result A) (selectA : A → Z → CI → Result A)
    (eachslice : A → D → Result S) (sortperm : S → K → Result P) (getRows : A → P → Result BType)
    (bAssign : I → I → I) (s1 s2 : I) (dims : D) (kws : K)
    (printP : IO → String → T → String → Result IO) (io : IO) (r : R) (t : T) (tl : Bool)
    (refGet : R → Result I) (refSet : R → I → Result R) (dim1 dim2 : Z)
    (dimVal : Z → Int),
    dimVal dim1 = 1 → dimVal dim2 = 2 →
    checkdimsPermArrays axesB axesA
      (checkdimsPerm List.length permutationValid
        (fun p => (List.range p.length).map fun (i : Nat) => int (Int.ofNat i + 1)) vectorRead)
      dest B perm =
      checkdimsPerm List.length permutationValid
        (fun p => (List.range p.length).map fun (i : Nat) => int (Int.ofNat i + 1)) vectorRead
        (axesB dest) (axesA B) perm ∧
    unique (fun a (_ : Unit) => uniqueDimsColon copyA a) B () = copyA B ∧
    unique (uniqueDims dimVal (fun _ => 1) copyA (fun _ _ => []) (fun _ => []) (fun _ => .ok ())
      (fun _ _ => .ok (JInt.wrap .u64 0)) (fun h _ _ => .ok h) (fun _ _ => .ok (int 0))
      (fun _ => .ok (JInt.wrap .u64 0)) (fun x _ => x) (fun _ => .ok ())
      (fun _ k => .ok k) (fun rw _ _ => .ok rw) (.ok ()) (fun d => .ok d)
      (fun d _ k => .ok (d, k)) (fun _ => [int 1]) (fun _ => .ok false) (fun _ => .ok false)
      (fun m _ => .ok m) (fun _ _ b => .ok b) id (fun _ => .ok false) (· == ·)
      .ok selectA) B dim2 = some (copyA B) ∧
    unique (uniqueDims dimVal (fun _ => 1) copyA (fun _ _ => [int 1]) (fun _ => [[int 1]]) (fun _ => .ok ())
      (fun _ _ => .ok (JInt.wrap .u64 0)) (fun h _ _ => .ok h) (fun _ _ => .ok (int 0))
      (fun _ => .ok (JInt.wrap .u64 0)) (fun x _ => x) (fun _ => .ok ())
      (fun _ k => .ok k) (fun rw _ _ => .ok rw) (.ok ()) (fun d => .ok d)
      (fun d _ k => .ok (d, k)) (fun _ => [int 1]) (fun _ => .ok false) (fun _ => .ok false)
      (fun m _ => .ok m) (fun _ _ b => .ok b) id (fun _ => .ok false) (· == ·)
      .ok selectA) B dim1 = some (selectA B dim1 [int 1]) ∧
    showargPairsInteger printP io r t tl = printP io "pairs(::" t ")" ∧
    showargPairsCartesian printP io r t tl = printP io "pairs(::" t ")" ∧
    showargPairsVector printP io r t tl = printP io "pairs(IndexCartesian(), ::" t ")" ∧
    sortslices (m := Result) (fun _ => true) (fun _ => true) eachslice sortperm getRows
      (fun _ => .ok dest) (fun _ _ _ _ => .ok ()) B dims kws =
      (do let p ← sortperm (← eachslice B dims) kws; getRows B p) ∧
    ((sortslices (m := StateT (List I) Result) (fun _ => false) (fun _ => true)
      (fun a d => StateT.lift (eachslice a d))
      (fun s kw => StateT.lift (sortperm s kw))
      (fun a p => StateT.lift (getRows a p))
      (fun _ => pure dest)
      (sortslicesBang (m := StateT (List I) Result)
        (fun _ _ => pure [s1, s2]) (fun _ _ => pure [s1, s2])
        id (fun _ _ => pure [int 2, int 1]) id id
        (fun vs i => StateT.lift (tupleGet vs i))
        (fun sl v => modify (fun acc => acc ++ [bAssign sl v])))
      B dims kws).run []) = .ok (dest, [bAssign s1 s2, bAssign s2 s1]) ∧
    refGetindexZero refGet r = refGet r ∧
    refSetindexZero refSet r s1 = refSet r s1)

theorem bitArrayAndSliceOps : BitArrayAndSliceOps := by
  refine ⟨fun x => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro C A getidx setbit Bc src pos_s readC writeC bAnd bOr bNot shl
    have hle : ¬ (int 1 ≤ int 1 + int 0 - int 1) := by decide
    have hne_pos : (int 1 + int 0 - int 1 == int 1) = false := by decide
    have h10 : ¬ (int 1 ≤ int 0) := by decide
    have h00 : ¬ (int 0 > int 0) := by decide
    constructor
    · rw [copyToBitarrayChunks, whileLoop]
      simp only [hle, ite_false, pure, Except.pure, bind, Except.bind]
    · unfold copyToBitarrayChunksReal
      simp [hne_pos, h10, h00, pure, Except.pure, bind, Except.bind]
  · intro A C I V chunks setChunks copyChunks copyChunksX fillChunks bitget bitset
      offset len firstI sz parent updChunks updParent X B viewData I0 e0 bval
    have ht_len : tupleGet [len I0] (int 1) = .ok (len I0) := tupleGet_one (len I0) []
    have ht_i0 : tupleGet [I0] (int 1) = .ok I0 := tupleGet_one I0 []
    have ht_1 : tupleGet [int 1] (int 1) = .ok (int 1) := tupleGet_one (int 1) []
    have ht_0 : tupleGet [int 0] (int 1) = .ok (int 0) := tupleGet_one (int 0) []
    have h10 : (int 1 == int 0) = false := by decide
    have h00 : (int 0 == int 0) = true := rfl
    have h_gr : bitGetindexRanges chunks setChunks (fun _ => [len I0]) offset sz (fun _ _ => [])
        copyChunks X B I0 [] =
        (do let c ← copyChunks (chunks X) (int 1) (chunks B) (offset I0 + int 1) (len I0); .ok (setChunks X c)) := by
      unfold bitGetindexRanges nestedLoops
      dsimp only
      rw [ht_len]
      simp only [List.tail_cons, List.append_nil, List.zipIdx_nil, List.forIn_nil,
        List.map_nil, List.reverse_nil, bind, Except.bind, pure, Except.pure]
      cases copyChunks (chunks X) (int 1) (chunks B) (offset I0 + int 1) (len I0) <;> rfl
    have h_gg : bitGetindexGeneral chunks setChunks sz (fun _ => [e0]) bitget bitset X B [I0] =
        (do
          let b ← bitget (chunks B) (int 1 + (e0 - int 1) * int 1)
          let c ← bitset (chunks X) b (int 0 + int 1)
          .ok (setChunks X c)) := by
      unfold bitGetindexGeneral forCartesian
      dsimp only
      simp only [List.length_singleton, List.range_one, List.forIn_cons, List.forIn_nil,
        List.map, List.zipIdx_cons, List.zipIdx_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, nestedLoops, List.foldlM_cons, List.foldlM_nil,
        List.zip_cons_cons, List.zip_nil_left, bind, Except.bind, pure, Except.pure]
      cases bitget (chunks B) (int 1 + (e0 - int 1) * int 1) with
      | error _ => rfl
      | ok b => dsimp only; cases bitset (chunks X) b (int 0 + int 1) <;> rfl
    have h_usr : bitUnsafeSetindexRanges chunks setChunks (fun _ => [len I0]) (fun _ => [len I0])
        (fun _ _ => .ok ()) (fun _ => false) offset sz (fun _ => []) copyChunksX B X I0 [] =
        (do let c ← copyChunksX (chunks B) (offset I0 + int 1) X (int 1) (len I0); .ok (setChunks B c)) := by
      unfold bitUnsafeSetindexRanges nestedLoops
      dsimp only
      rw [ht_len]
      simp only [Bool.false_eq_true, ite_false, List.tail_cons, List.append_nil,
        List.zipIdx_nil, List.forIn_nil, List.map_nil, List.reverse_nil,
        bind, Except.bind, pure, Except.pure]
      cases copyChunksX (chunks B) (offset I0 + int 1) X (int 1) (len I0) <;> rfl
    have h_fr : bitFillRanges parent (fun _ => [I0])
        (fun b v _ => bitUnsafeFillIndices chunks setChunks (fun z => .ok z) (fun _ => [int 1])
          offset (fun _ => false) sz (fun _ => []) fillChunks b v I0 [])
        updParent viewData bval =
        (do
          let c ← fillChunks (chunks (parent viewData)) bval (offset I0 + int 1) (int 1)
          .ok (updParent viewData (setChunks (parent viewData) c))) := by
      unfold bitFillRanges bitUnsafeFillIndices nestedLoops
      dsimp only
      rw [ht_1]
      simp only [h10, Bool.false_eq_true, ite_false, List.tail_cons, List.append_nil,
        List.zipIdx_nil, List.forIn_nil, List.map_nil, List.reverse_nil,
        bind, Except.bind, pure, Except.pure]
      cases fillChunks (chunks (parent viewData)) bval (offset I0 + int 1) (int 1) <;> rfl
    rw [h_gr, h_gg, h_usr, h_fr]
    unfold bitGetindexContiguous bitSetindexContiguous bitSetindexRanges
      bitUnsafeSetindexRanges bitSetindexAbstract bitFillContiguous bitUnsafeFillIndices
    dsimp only
    rw [ht_i0, ht_0]
    simp [ht_i0, bind, Except.bind, pure, Except.pure]
  · intro A I V sz isa1 isaC toIdx getA B I0 i1 ci is
    have h1 : bitIsassigned sz isa1 B I0 [] = isa1 B I0 := rfl
    have h2 : bitIsassigned sz isa1 B I0 [i1] =
        (if !(int 1 ≤ I0 ∧ I0 ≤ sz B (int 1)) then false
         else isa1 B (I0 + (i1 - int 1) * (int 1 * sz B (int 1)))) := by
      unfold bitIsassigned
      have h01 : int (((0 : Nat) : Int) + 1) = int 1 := rfl
      by_cases h : (!(int 1 ≤ I0 ∧ I0 ≤ sz B (int 1))) = true <;>
        simp only [h01, h, Bool.false_eq_true, List.zipIdx_cons, List.zipIdx_nil,
          List.forIn_cons, List.forIn_nil, ite_true, ite_false, Id.run, pure, bind]
    have h3 : isassignedCartesian isaC B ci = isaC B ci := rfl
    have h4 : isassignedMixed (fun a xs => .ok (toIdx a xs)) isaC B is = isaC B (toIdx B is) := rfl
    have h5 : isassignedIntegers (fun a xs => .ok (toIdx a xs)) (fun _ _ => false)
        (fun _ => true) (fun _ => 1) (fun _ _ => .ok I0) (fun _ c => .ok c)
        (fun a k => .ok (isa1 a k)) isaC getA (fun _ => true) (fun _ => true) B is = .ok false := rfl
    have h6 : isassignedIntegers (fun _ _ => .ok [I0]) (fun _ _ => true)
        (fun _ => true) (fun _ => 1) (fun _ _ => .ok I0) (fun _ c => .ok c)
        (fun a k => .ok (isa1 a k)) isaC (fun _ _ => (.error .boundsError : Result V))
        (fun e => e == .boundsError) (fun _ => false) B is = .ok false := rfl
    refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
    unfold isassignedIntegers
    dsimp only [bind, Except.bind, pure, Except.pure, List.length_singleton,
      bne_self_eq_false, Bool.and_false, Bool.not_true, ite_false]
    cases getA B [I0] with
    | ok v => rfl
    | error e => by_cases he : (e == .boundsError) = true <;> simp [he, throw, throwThe, MonadExceptOf.throw]
  · intro A BType AX P D K S I IO T R Z _ axesA axesB dest B perm copyA selectA
      eachslice sortperm getRows bAssign s1 s2 dims kws printP io r t tl refGet refSet
      dim1 dim2 dimVal hd1 hd2
    have hbad : (!(1 ≤ dimVal dim2 ∧ dimVal dim2 ≤ (1 : Nat))) = true := by
      rw [hd2]; decide
    have hgood : ¬ ((!(1 ≤ dimVal dim1 ∧ dimVal dim1 ≤ (1 : Nat))) = true) := by
      rw [hd1]; decide
    have hd1_i64 : int (dimVal dim1) = int 1 := by rw [hd1]
    have ht1 : tupleGet [int 1] (int 1) = .ok (int 1) := tupleGet_one (int 1) []
    have ht_s1 : tupleGet [s1, s2] (int 1) = .ok s1 := tupleGet_one s1 [s2]
    have ht_s2 : tupleGet [s1, s2] (int 2) = .ok s2 := tupleGet_two s1 s2 []
    refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
    · unfold unique uniqueDims; rw [ite_eq_left hbad]
    · unfold unique uniqueDims uniqueDims.initialState
      rw [ite_eq_right hgood]
      dsimp only
      rw [hd1_i64]
      simp only [ht1, List.forIn_cons, List.forIn_nil,
        beq_self_eq_true, Bool.not_true,
        pure, Except.pure, bind, Except.bind]
      cases selectA B dim1 [int 1] <;> rfl
    · unfold sortslices; simp [bind, Except.bind]
    · unfold sortslices sortslicesBang
      dsimp only [id, StateT.run, StateT.lift, pure, StateT.pure, bind, StateT.bind,
        modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
      simp only [Bool.false_and, Bool.false_eq_true, ite_false]
      rfl
/-! Nothing to promise (forwarding, constructor, and display wrappers; all also covered in registered properties):
- `cartesianInner@77` (`CartesianIndex{N}(index::NTuple{N,Integer}) where {N} = new(index)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianTuple@80` (`CartesianIndex(index::NTuple{N,Integer}) where {N} = CartesianIndex{N}(index)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianVarargs@81` (`CartesianIndex(index::Integer...) = CartesianIndex(index)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianSizedVarargs@82` (`CartesianIndex{N}(index::Vararg{Integer,N}) where {N} = CartesianIndex{N}(index)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianPad@84` (`CartesianIndex{N}(index::Tuple) where {N} = CartesianIndex{N}(fill_to_length(index, 1, Val(N)))`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianSizedIntegers@85` (`CartesianIndex{N}(index::Integer...) where {N} = CartesianIndex{N}(index)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianDefault@86` (`CartesianIndex{N}() where {N} = CartesianIndex{N}(())`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianIdentity@88` (`CartesianIndex{N}(index::CartesianIndex{N}) where {N} = index`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianMixed@89` (`CartesianIndex(index::Union{Integer, CartesianIndex}...) = CartesianIndex(flatten(index))`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `flattenEmpty@90` (`flatten(::Tuple{}) = ()`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `flattenSingle@91` (`flatten(I::Tuple{Any}) = Tuple(I[1])`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `flattenCons@92` (`@inline flatten(I::Tuple) = (Tuple(I[1])..., flatten(tail(I))...)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianMixedTuple@93` (`CartesianIndex(index::Tuple{Vararg{Union{Integer, CartesianIndex}}}) = CartesianIndex(index...)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `showCartesian@94` (`function show(io::IO, i::CartesianIndex)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianLength@101` (`length(::CartesianIndex{N}) where {N} = N`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianTypeLength@102` (`length(::Type{CartesianIndex{N}}) where {N} = N`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianGetindex@105` (`getindex(index::CartesianIndex, i::Integer) = index.I[i]`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianFirstindex@106` (`firstindex(index::CartesianIndex) = firstindex(index.I)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianLastindex@107` (`lastindex(index::CartesianIndex) = lastindex(index.I)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `arrayGetCartesian@108` (`Base.get(A::AbstractArray, I::CartesianIndex, default) = get(A, I.I, default)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianEltype@109` (`eltype(::Type{T}) where {T<:CartesianIndex} = eltype(fieldtype(T, :I))`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianToTuple@112` (`Tuple(index::CartesianIndex) = index.I`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianSetindex@114` (`Base.setindex(x::CartesianIndex,i,j) = CartesianIndex(Base.setindex(Tuple(x),i,j))`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianEq@117` (`Base.:(==)(a::CartesianIndex{N}, b::CartesianIndex{N}) where N = a.I == b.I`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianZeroValue@120` (`zero(::CartesianIndex{N}) where {N} = zero(CartesianIndex{N})`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianZeroType@121` (`zero(::Type{CartesianIndex{N}}) where {N} = CartesianIndex(ntuple(Returns(0), Val(N)))`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianOneValue@122` (`oneunit(::CartesianIndex{N}) where {N} = oneunit(CartesianIndex{N})`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianOneType@123` (`oneunit(::Type{CartesianIndex{N}}) where {N} = CartesianIndex(ntuple(Returns(1), Val(N)))`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianPos@126` (`@inline (+)(index::CartesianIndex) = index`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianNeg@127` (`@inline (-)(index::CartesianIndex{N}) where {N} =`): covered in `multidimensional-cartesian-neg-involutive`.
- `cartesianAdd@129` (`@inline (+)(index1::CartesianIndex{N}, index2::CartesianIndex{N}) where {N} =`): covered in `multidimensional-cartesian-add-commutes, multidimensional-cartesian-algebra-and-hash`.
- `cartesianSub@131` (`@inline (-)(index1::CartesianIndex{N}, index2::CartesianIndex{N}) where {N} =`): covered in `multidim-circshift-formula, multidim-circcopy-nonempty, multidimensional-cartesian-algebra-and-hash`.
- `cartesianMin@133` (`@inline min(index1::CartesianIndex{N}, index2::CartesianIndex{N}) where {N} =`): covered in `multidimensional-cartesian-minmax-commute`.
- `cartesianMax@135` (`@inline max(index1::CartesianIndex{N}, index2::CartesianIndex{N}) where {N} =`): covered in `multidimensional-cartesian-minmax-commute`.
- `cartesianScaleLeft@138` (`@inline (*)(a::Integer, index::CartesianIndex{N}) where {N} = CartesianIndex{N}(map(x->a*x, index.I))`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianScaleRight@139` (`@inline (*)(index::CartesianIndex, a::Integer) = *(a,index)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianIsless@142` (`isless(I1::CartesianIndex{N}, I2::CartesianIndex{N}) where {N} = isless(reverse(I1.I), reverse(I2.I))`): covered in `multidim-cartesian-isless`.
- `cartesianConvertNumber@145` (`convert(::Type{T}, index::CartesianIndex{1}) where {T<:Number} = convert(T, index[1])`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianConvertTuple@146` (`convert(::Type{T}, index::CartesianIndex) where {T<:Tuple} = convert(T, index.I)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianHash@150` (`function Base.hash(ci::CartesianIndex, h::UInt)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `nextindCartesian@159` (`function Base.nextind(a::AbstractArray{<:Any,N}, i::CartesianIndex{N}) where {N}`): covered in `multidimensional-cartesian-iteration-and-split`.
- `previndCartesian@165` (`function Base.prevind(a::AbstractArray{<:Any,N}, i::CartesianIndex{N}) where {N}`): covered in `multidimensional-cartesian-iteration-and-split`.
- `ind2subCartesian@172` (`Base._ind2sub(t::Tuple, ind::CartesianIndex) = Tuple(ind)`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianIterateDisabled@176` (`Base.iterate(::CartesianIndex) =`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianRangeLengthDisabled@180` (`Base.range_start_step_length(start::CartesianIndex, step::CartesianIndex, len::Integer) =`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `showCartesianStepRange@187` (`function show(io::IO, r::StepRangeLen{<:CartesianIndex})`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianRangeContainsWrongRank@192` (`Base.in(x::CartesianIndex, r::AbstractRange{<:CartesianIndex}) = false`): covered in `multidimensional-cartesian-algebra-and-hash`.
- `cartesianRangeContains@193` (`function Base.in(x::CartesianIndex{N}, r::AbstractRange{CartesianIndex{N}}) where {N}`): covered in `multidimensional-index-traits-and-queries`.
- `cartesianIndicesEmpty@298` (`CartesianIndices(::Tuple{}) = CartesianIndices{0,typeof(())}(())`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesRanges@299` (`function CartesianIndices(inds::NTuple{N,OrdinalRange{<:Integer, <:Integer}}) where {N}`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesIndex@304` (`CartesianIndices(index::CartesianIndex) = CartesianIndices(index.I)`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesMixed@305` (`CartesianIndices(inds::NTuple{N,Union{<:Integer,OrdinalRange{<:Integer}}}) where {N} =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesArray@308` (`CartesianIndices(A::AbstractArray) = CartesianIndices(axes(A))`): covered in `multidimensional-cartesian-indices-and-regions`.
- `convert2indBool@310` (`_convert2ind(sz::Bool) = Base.OneTo(Int8(sz))`): covered in `multidimensional-cartesian-indices-and-regions`.
- `convert2indInteger@311` (`_convert2ind(sz::Integer) = Base.oneto(sz)`): covered in `multidimensional-cartesian-indices-and-regions`.
- `convert2indUnitRange@312` (`_convert2ind(sz::AbstractUnitRange) = first(sz):last(sz)`): covered in `multidimensional-cartesian-indices-and-regions`.
- `convert2indOrdinal@313` (`_convert2ind(sz::OrdinalRange) = first(sz):step(sz):last(sz)`): covered in `multidimensional-cartesian-indices-and-regions`.
- `showCartesianIndices@315` (`function show(io::IO, iter::CartesianIndices)`): covered in `multidimensional-cartesian-indices-and-regions`.
- `xformIndex@320` (`_xform_index(i) = i`): covered in `multidimensional-cartesian-indices-and-regions`.
- `xformOneTo@321` (`_xform_index(i::OneTo) = i.stop`): covered in `multidimensional-cartesian-indices-and-regions`.
- `showCartesianIndicesPlain@322` (`show(io::IO, ::MIME"text/plain", iter::CartesianIndices) = show(io, iter)`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianColon@350` (`(:)(I::CartesianIndex{N}, J::CartesianIndex{N}) where N =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianStepColon@352` (`(:)(I::CartesianIndex{N}, S::CartesianIndex{N}, J::CartesianIndex{N}) where N =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesPromote@355` (`promote_rule(::Type{CartesianIndices{N,R1}}, ::Type{CartesianIndices{N,R2}}) where {N,R1,R2} =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvertEmpty@358` (`convert(::Type{Tuple{}}, R::CartesianIndices{0}) = ()`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvertRanges@360` (`@eval convert(::Type{NTuple{N,$RT}}, R::CartesianIndices{N}) where {N} =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvertAbstractUnit@363` (`convert(::Type{NTuple{N,AbstractUnitRange}}, R::CartesianIndices{N}) where {N} =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvertUnitInt@365` (`convert(::Type{NTuple{N,UnitRange{Int}}}, R::CartesianIndices{N}) where {N} =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvertUnit@367` (`convert(::Type{NTuple{N,UnitRange}}, R::CartesianIndices{N}) where {N} =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvertVarargAbstractUnitInt@369` (`convert(::Type{Tuple{Vararg{AbstractUnitRange{Int}}}}, R::CartesianIndices{N}) where {N} =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvertVarargAbstractUnit@371` (`convert(::Type{Tuple{Vararg{AbstractUnitRange}}}, R::CartesianIndices) =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvertVarargUnitInt@373` (`convert(::Type{Tuple{Vararg{UnitRange{Int}}}}, R::CartesianIndices{N}) where {N} =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvertVarargUnit@375` (`convert(::Type{Tuple{Vararg{UnitRange}}}, R::CartesianIndices) =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesConvert@378` (`convert(::Type{CartesianIndices{N,R}}, inds::CartesianIndices{N}) where {N,R} =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesEq@382` (`Base.:(==)(a::CartesianIndices{N}, b::CartesianIndices{N}) where N =`): covered in `multidim-cartesianindices-empty-eq, multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesEqWrongRank@384` (`Base.:(==)(a::CartesianIndices, b::CartesianIndices) = false`): covered in `multidim-cartesianindices-empty-eq, multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesAxes@387` (`Base.axes(iter::CartesianIndices{N,R}) where {N,R} = map(Base.axes1, iter.indices)`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesHasOffset@388` (`Base.has_offset_axes(iter::CartesianIndices) = Base.has_offset_axes(iter.indices...)`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesIsassigned@389` (`@propagate_inbounds function isassigned(iter::CartesianIndices{N,R}, I::Vararg{Int, N}) where {N,R}`): covered in `multidimensional-index-traits-and-queries`.
- `cartesianIndicesGetindexZero@397` (`@inline function Base.getindex(iter::CartesianIndices{0,R}) where {R}`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesGetindex@400` (`@inline function Base.getindex(iter::CartesianIndices{N,R}, I::Vararg{Int, N}) where {N,R}`): covered in `multidim-circshift-formula, multidim-circcopy-nonempty`.
- `cartesianIndicesGetindexRanges@413` (`@inline function Base.getindex(iter::CartesianIndices{N,R},`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesGetindexRegion@421` (`@propagate_inbounds function Base.getindex(iter::CartesianIndices{N},`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesGetindexZeroRegion@425` (`@inline Base.getindex(iter::CartesianIndices{0}, ::CartesianIndices{0}) = iter`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesViewRanges@428` (`@propagate_inbounds function Base.view(c::CartesianIndices{N}, r::Vararg{Union{OrdinalRange{<:Integer, <:Integer}, Colon},N}) where {N}`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesViewRegion@431` (`@propagate_inbounds function Base.view(c::CartesianIndices{N}, C::CartesianIndices{N}) where {N}`): covered in `multidimensional-cartesian-indices-and-regions`.
- `eachindexCartesian@435` (`eachindex(::IndexCartesian, A::AbstractArray) = CartesianIndices(axes(A))`): covered in `multidimensional-cartesian-indices-and-regions`.
- `eachindexCartesianMany@437` (`@inline function eachindex(::IndexCartesian, A::AbstractArray, B::AbstractArray...)`): covered in `multidimensional-index-traits-and-queries`.
- `cartesianIterateFirst@445` (`@inline function iterate(iter::CartesianIndices)`): covered in `multidim-cartesian-iterate`.
- `cartesianIterateNext@452` (`@inline function iterate(iter::CartesianIndices, state::CartesianIndex)`): covered in `multidim-cartesian-iterate`.
- `cartesianInc@459` (`@inline function inc(state, indices)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `incEmpty@468` (`__inc(::Tuple{}, ::Tuple{}) = false, ()`): covered in `multidim-cartesian-iterate`.
- `incSingle@469` (`@inline function __inc(state::Tuple{Int}, indices::Tuple{OrdinalRangeInt})`): covered in `multidim-cartesian-iterate`.
- `incCons@475` (`@inline function __inc(state::Tuple{Int,Int,Vararg{Int}}, indices::Tuple{OrdinalRangeInt,OrdinalRangeInt,Vararg{OrdinalRangeInt}})`): covered in `multidim-cartesian-iterate`.
- `cartesianIterateZero@486` (`iterate(iter::CartesianIndices{0}, done::Bool=false) = done ? nothing : (CartesianIndex(), true)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `cartesianIndicesSize@488` (`size(iter::CartesianIndices) = map(length, iter.indices)`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesStep@491` (`Base.step(iter::CartesianIndices) = CartesianIndex(map(step, iter.indices))`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesFirst@493` (`first(iter::CartesianIndices) = CartesianIndex(map(first, iter.indices))`): covered in `multidim-cartesian-iterate, multidim-cartesian-reverse-iterate, multidim-circshift-formula, multidim-circcopy-nonempty`.
- `cartesianIndicesLast@494` (`last(iter::CartesianIndices)  = CartesianIndex(map(last, iter.indices))`): covered in `multidim-cartesian-iterate, multidim-cartesian-reverse-iterate, multidim-circshift-formula, multidim-circcopy-nonempty`.
- `toIndicesCartesianRegion@497` (`@inline function to_indices(A, inds, I::Tuple{CartesianIndices{N}, Vararg}) where N`): covered in `multidimensional-cartesian-indices-and-regions`.
- `toIndicesCartesianRegionZero@502` (`@inline to_indices(A, inds, I::Tuple{CartesianIndices{0}, Vararg}) =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesContainsWrongRank@505` (`@inline in(i::CartesianIndex, r::CartesianIndices) = false`): covered in `multidimensional-cartesian-indices-and-regions`.
- `cartesianIndicesContains@506` (`@inline in(i::CartesianIndex{N}, r::CartesianIndices{N}) where {N} = all(map(in, i.I, r.indices))`): covered in `multidim-circshift-formula, multidim-circcopy-nonempty, multidimensional-index-traits-and-queries`.
- `cartesianIndicesCopy@508` (`copy(iter::CartesianIndices) = iter`): covered in `multidimensional-cartesian-indices-and-regions`.
- `simdOuterZero@510` (`simd_outer_range(iter::CartesianIndices{0}) = iter`): covered in `multidimensional-cartesian-iteration-and-split`.
- `simdOuter@511` (`function simd_outer_range(iter::CartesianIndices)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `simdInnerZero@515` (`simd_inner_length(iter::CartesianIndices{0}, ::CartesianIndex) = 1`): covered in `multidimensional-cartesian-iteration-and-split`.
- `simdInner@516` (`simd_inner_length(iter::CartesianIndices, I::CartesianIndex) = Base.length(iter.indices[1])`): covered in `multidimensional-cartesian-iteration-and-split`.
- `simdIndexZero@518` (`simd_index(iter::CartesianIndices{0}, ::CartesianIndex, I1::Int) = first(iter)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `simdIndex@519` (`@propagate_inbounds simd_index(iter::CartesianIndices, Ilast::CartesianIndex, I1::Int) =`): covered in `multidimensional-cartesian-iteration-and-split`.
- `splitTuple@523` (`@inline function split(t, V::Val)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `split1Cons@527` (`@inline _split1(t, ref) = (t[1], _split1(tail(t), tail(ref))...)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `splitrestCons@528` (`@inline _splitrest(t, ref) = _splitrest(tail(t), tail(ref))`): covered in `multidimensional-cartesian-iteration-and-split`.
- `split1EmptyEmpty@530` (`_split1(::Tuple{}, ::Tuple{}) = ()`): covered in `multidimensional-cartesian-iteration-and-split`.
- `split1EmptyRef@531` (`_split1(::Tuple{}, ref) = ()`): covered in `multidimensional-cartesian-iteration-and-split`.
- `split1TupleEmpty@532` (`_split1(t, ::Tuple{}) = ()`): covered in `multidimensional-cartesian-iteration-and-split`.
- `splitrestEmptyEmpty@533` (`_splitrest(::Tuple{}, ::Tuple{}) = ()`): covered in `multidimensional-cartesian-iteration-and-split`.
- `splitrestTupleEmpty@534` (`_splitrest(t, ::Tuple{}) = t`): covered in `multidimensional-cartesian-iteration-and-split`.
- `splitrestEmptyRef@535` (`_splitrest(::Tuple{}, ref) = ()`): covered in `multidimensional-cartesian-iteration-and-split`.
- `splitCartesian@537` (`@inline function split(I::CartesianIndex, V::Val)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `splitCartesianIndices@541` (`function split(R::CartesianIndices, V::Val)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `reverseCartesianAll@547` (`@inline function Base._reverse(iter::CartesianIndices, ::Colon)`): covered in `multidim-reverse-dims-check`.
- `reverseCartesianDimension@551` (`Base.@constprop :aggressive function Base._reverse(iter::CartesianIndices, dim::Integer)`): covered in `multidim-reverse-dims-check`.
- `reverseCartesianDimensions@558` (`Base.@constprop :aggressive function Base._reverse(iter::CartesianIndices, dims::Tuple{Vararg{Integer}})`): covered in `multidim-reverse-dims-check`.
- `reverseCartesianOneDimension@569` (`Base._reverse(iter::CartesianIndices{1}, dims::Tuple{Integer}) =`): covered in `multidim-reverse-dims-check`.
- `reverseIterateFirst@572` (`@inline function iterate(r::Reverse{<:CartesianIndices})`): covered in `multidim-cartesian-reverse-iterate`.
- `reverseIterateNext@579` (`@inline function iterate(r::Reverse{<:CartesianIndices}, state)`): covered in `multidim-cartesian-reverse-iterate`.
- `cartesianDec@586` (`@inline function dec(state, indices)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `decEmpty@592` (`@inline __dec(::Tuple{}, ::Tuple{}) = false, ()`): covered in `multidim-cartesian-reverse-iterate`.
- `decSingle@593` (`@inline function __dec(state::Tuple{Int}, indices::Tuple{OrdinalRangeInt})`): covered in `multidim-cartesian-reverse-iterate`.
- `decCons@599` (`@inline function __dec(state::Tuple{Int,Int,Vararg{Int}}, indices::Tuple{OrdinalRangeInt,OrdinalRangeInt,Vararg{OrdinalRangeInt}})`): covered in `multidim-cartesian-reverse-iterate`.
- `reverseIterateZero@610` (`iterate(iter::Reverse{<:CartesianIndices{0}}, state=false) = state ? nothing : (CartesianIndex(), true)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `linearIndicesUnit@612` (`function Base.LinearIndices(inds::CartesianIndices{N,R}) where {N,R<:NTuple{N, AbstractUnitRange}}`): covered in `multidimensional-index-traits-and-queries`.
- `linearIndices@615` (`function Base.LinearIndices(inds::CartesianIndices)`): covered in `multidimensional-index-traits-and-queries`.
- `collectCartesianUnit@631` (`function Base.collect(inds::CartesianIndices{N, R}) where {N,R<:NTuple{N, AbstractUnitRange}}`): covered in `multidimensional-index-traits-and-queries`.
- `collectCartesian@634` (`function Base.collect(inds::CartesianIndices)`): covered in `multidimensional-index-traits-and-queries`.
- `intersectCartesian@644` (`Base.intersect(a::CartesianIndices{N}, b::CartesianIndices{N}) where N =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `subsetCartesian@646` (`Base.issubset(a::CartesianIndices{N}, b::CartesianIndices{N}) where N =`): covered in `multidimensional-cartesian-indices-and-regions`.
- `partitionEltypeLinear@651` (`eltype(::Type{PartitionIterator{T}}) where {T<:ReshapedArrayLF} = SubArray{eltype(T), 1, T, Tuple{UnitRange{Int}}, true}`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionEltypeCartesian@652` (`eltype(::Type{PartitionIterator{T}}) where {T<:ReshapedArray} = SubArray{eltype(T), 1, T, Tuple{UnitRange{Int}}, false}`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionIteratorEltype@653` (`Iterators.IteratorEltype(::Type{<:PartitionIterator{T}}) where {T<:ReshapedArray} = Iterators.IteratorEltype(T)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionEltypeOneTo@655` (`eltype(::Type{PartitionIterator{T}}) where {T<:OneTo} = UnitRange{eltype(T)}`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionEltypeRange@656` (`eltype(::Type{PartitionIterator{T}}) where {T<:Union{UnitRange, StepRange, StepRangeLen, LinRange}} = T`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionRangeIteratorEltype@657` (`Iterators.IteratorEltype(::Type{<:PartitionIterator{T}}) where {T<:Union{OneTo, UnitRange, StepRange, StepRangeLen, LinRange}} = Iterators.IteratorEltype(T)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionIterateFirst@659` (`@inline function iterate(iter::CartesianPartition)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionIterateNext@664` (`@inline function iterate(iter::CartesianPartition, (state, n))`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionSimdOuter@670` (`@inline function simd_outer_range(iter::CartesianPartition)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionSplitdim1@677` (`function splitdim1(i, mi)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionSkipLength@688` (`@inline function skip_len_I(i::Int, I::CartesianIndex)`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionSimdOuter2@695` (`@inline function simd_outer_range(iter::CartesianPartition{CartesianIndex{2}})`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionSkipLength2@706` (`@inline function skip_len_I(I::CartesianIndex{1})`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionSimdInner@713` (`@inline simd_inner_length(iter::CartesianPartition, (_, len, _)::Tuple{Int,Int,CartesianIndex}) = len`): covered in `multidimensional-cartesian-iteration-and-split`.
- `partitionSimdIndex@714` (`@propagate_inbounds simd_index(iter::CartesianPartition, (skip, _, I)::Tuple{Int,Int,CartesianIndex}, n::Int) =`): covered in `multidimensional-cartesian-iteration-and-split`.
- `atomicMixed@735` (`function $fn($(args...), i::Union{Integer,CartesianIndex}...)`): covered in `multidimensional-logical-and-indexing`.
- `atomicCartesian@739` (`function $fn($(args...), i::CartesianIndex)`): covered in `multidimensional-logical-and-indexing`.
- `atomicIntegers@743` (`function $fn($(args...), i::Integer...)`): covered in `multidimensional-logical-and-indexing`.
- `checkboundsCartesian@757` (`@inline checkbounds(::Type{Bool}, A::AbstractArray, i::CartesianIndex) =`): covered in `multidimensional-logical-and-indexing`.
- `checkboundsIndicesCartesian@760` (`@inline function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{CartesianIndex,Vararg})`): covered in `multidimensional-logical-and-indexing`.
- `checkindexCartesian@764` (`@inline checkindex(::Type{Bool}, inds::Tuple, I::CartesianIndex) =`): covered in `multidimensional-logical-and-indexing`.
- `checkindexCartesianRange@766` (`@inline checkindex(::Type{Bool}, inds::Tuple, i::AbstractRange{<:CartesianIndex}) =`): covered in `multidimensional-logical-and-indexing`.
- `arrayGetMixed@772` (`@propagate_inbounds getindex(A::Array, i1::Union{Integer, CartesianIndex}, I::Union{Integer, CartesianIndex}...) =`): covered in `multidimensional-logical-and-indexing`.
- `arraySetMixed@774` (`@propagate_inbounds setindex!(A::Array, v, i1::Union{Integer, CartesianIndex}, I::Union{Integer, CartesianIndex}...) =`): covered in `multidimensional-logical-and-indexing`.
- `checkboundsCartesianArray@779` (`@inline checkbounds(::Type{Bool}, A::AbstractArray, i::AbstractArray{CartesianIndex{N}}) where {N} =`): covered in `multidimensional-logical-and-indexing`.
- `checkboundsIndicesCartesianArray@782` (`@inline function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{AbstractArray{CartesianIndex{N}},Vararg}) where N`): covered in `multidimensional-logical-and-indexing`.
- `checkindexCartesianIndices@786` (`@inline checkindex(::Type{Bool}, inds::Tuple, I::CartesianIndices) =`): covered in `multidimensional-logical-and-indexing`.
- `indexNdimsScalar@792` (`@inline index_ndims(i1, I...) = (true, index_ndims(I...)...)`): covered in `multidimensional-index-traits-and-queries`.
- `indexNdimsCartesian@793` (`@inline function index_ndims(i1::CartesianIndex, I...)`): covered in `multidimensional-index-traits-and-queries`.
- `indexNdimsCartesianArray@796` (`@inline function index_ndims(i1::AbstractArray{CartesianIndex{N}}, I...) where N`): covered in `multidimensional-index-traits-and-queries`.
- `indexNdimsEmpty@799` (`index_ndims() = ()`): covered in `multidimensional-index-traits-and-queries`.
- `indexDimsumScalar@803` (`@inline index_dimsum(i1, I...) = (index_dimsum(I...)...,)`): covered in `multidimensional-index-traits-and-queries`.
- `indexDimsumColon@804` (`@inline index_dimsum(::Colon, I...) = (true, index_dimsum(I...)...)`): covered in `multidimensional-index-traits-and-queries`.
- `indexDimsumMask@805` (`@inline index_dimsum(::AbstractArray{Bool}, I...) = (true, index_dimsum(I...)...)`): covered in `multidimensional-index-traits-and-queries`.
- `indexDimsumArray@806` (`@inline function index_dimsum(::AbstractArray{<:Any,N}, I...) where N`): covered in `multidimensional-index-traits-and-queries`.
- `indexDimsumEmpty@809` (`index_dimsum() = ()`): covered in `multidimensional-index-traits-and-queries`.
- `indexLengthsEmpty@812` (`index_lengths() = ()`): covered in `multidimensional-index-traits-and-queries`.
- `indexLengthsScalar@813` (`@inline index_lengths(::Real, rest...) = (1, index_lengths(rest...)...)`): covered in `multidimensional-index-traits-and-queries`.
- `indexLengthsArray@814` (`@inline index_lengths(A::AbstractArray, rest...) = (length(A), index_lengths(rest...)...)`): covered in `multidimensional-index-traits-and-queries`.
- `indexShapeEmpty@818` (`index_shape() = ()`): covered in `multidimensional-index-traits-and-queries`.
- `indexShapeScalar@819` (`@inline index_shape(::Real, rest...) = index_shape(rest...)`): covered in `multidimensional-index-traits-and-queries`.
- `indexShapeArray@820` (`@inline index_shape(A::AbstractArray, rest...) = (axes(A)..., index_shape(rest...)...)`): covered in `multidimensional-index-traits-and-queries`.
- `indexSizesEmpty@822` (`index_sizes() = ()`): covered in `multidimensional-index-traits-and-queries`.
- `indexSizesScalar@823` (`@inline index_sizes(::Real, rest...) = index_sizes(rest...)`): covered in `multidimensional-index-traits-and-queries`.
- `indexSizesArray@824` (`@inline index_sizes(A::AbstractArray, rest...) = (size(A)..., index_sizes(rest...)...)`): covered in `multidimensional-index-traits-and-queries`.
- `logicalInner@837` (`LogicalIndex{T,A}(mask::A) where {T,A<:AbstractArray{Bool}} = new(mask, count(mask))`): covered in `multidimensional-logical-and-indexing`.
- `logicalVector@839` (`LogicalIndex(mask::AbstractVector{Bool}) = LogicalIndex{Int, typeof(mask)}(mask)`): covered in `multidimensional-logical-and-indexing`.
- `logicalArray@840` (`LogicalIndex(mask::AbstractArray{Bool, N}) where {N} = LogicalIndex{CartesianIndex{N}, typeof(mask)}(mask)`): covered in `multidimensional-logical-and-indexing`.
- `logicalExplicitInt@841` (`LogicalIndex{Int}(mask::AbstractArray) = LogicalIndex{Int, typeof(mask)}(mask)`): covered in `multidimensional-logical-and-indexing`.
- `logicalSize@842` (`size(L::LogicalIndex) = (L.sum,)`): covered in `multidimensional-logical-and-indexing`.
- `logicalCollect@843` (`collect(L::LogicalIndex) = [i for i in L]`): covered in `multidimensional-logical-and-indexing`.
- `logicalShow@844` (`show(io::IO, r::LogicalIndex) = print(io,collect(r))`): covered in `multidimensional-logical-and-indexing`.
- `logicalPrintArray@845` (`print_array(io::IO, X::LogicalIndex) = print_array(io, collect(X))`): covered in `multidimensional-logical-and-indexing`.
- `logicalIterateIntFirst@851` (`@inline function iterate(L::LogicalIndex{Int})`): covered in `multidimensional-logical-and-indexing`.
- `logicalIterateCartesianFirst@855` (`@inline function iterate(L::LogicalIndex{<:CartesianIndex})`): covered in `multidimensional-logical-and-indexing`.
- `logicalIterate@859` (`@propagate_inbounds function iterate(L::LogicalIndex, s)`): covered in `multidimcov-multidimensional-repair-c2, multidimcov-logicalindex-mutable-mask`.
- `logicalBitIntFirst@874` (`@inline function iterate(L::LogicalIndex{Int,<:BitArray})`): covered in `multidimensional-logical-and-indexing`.
- `logicalBitCartesianFirst@879` (`@inline function iterate(L::LogicalIndex{<:CartesianIndex,<:BitArray})`): covered in `multidimensional-logical-and-indexing`.
- `logicalBitIterate@885` (`@inline function iterate(L::LogicalIndex{<:Any,<:BitArray}, (i1, Bi, irest, c))`): covered in `multidimensional-logical-and-indexing`.
- `checkboundsLogical@900` (`checkbounds(::Type{Bool}, A::AbstractArray, i::LogicalIndex) = checkbounds(Bool, A, i.mask)`): covered in `multidimensional-logical-and-indexing`.
- `checkindexLogicalAxis@902` (`checkindex(::Type{Bool}, inds::AbstractUnitRange, i::LogicalIndex) = checkindex(Bool, inds, i.mask)`): covered in `multidimensional-logical-and-indexing`.
- `checkindexLogicalTuple@903` (`checkindex(::Type{Bool}, inds::Tuple, i::LogicalIndex) = checkindex(Bool, inds, i.mask)`): covered in `multidimensional-logical-and-indexing`.
- `checkboundsMask@907` (`checkbounds(::Type{Bool}, A::AbstractArray, i::AbstractArray{Bool}) =`): covered in `multidimensional-logical-and-indexing`.
- `checkboundsVectorMask@910` (`checkbounds(::Type{Bool}, A::AbstractArray, i::AbstractVector{Bool}) =`): covered in `multidimensional-logical-and-indexing`.
- `checkboundsIndicesMask@912` (`@inline function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{AbstractArray{Bool},Vararg})`): covered in `multidimensional-logical-and-indexing`.
- `checkindexVectorMask@916` (`checkindex(::Type{Bool}, inds::AbstractUnitRange, I::AbstractVector{Bool}) = axes1(I) == inds`): covered in `multidimensional-logical-and-indexing`.
- `checkindexRangeMask@917` (`checkindex(::Type{Bool}, inds::AbstractUnitRange, I::AbstractRange{Bool}) = axes1(I) == inds`): covered in `multidimensional-logical-and-indexing`.
- `checkindexMaskTuple@918` (`checkindex(::Type{Bool}, inds::Tuple, I::AbstractArray{Bool}) = _check_boolean_axes(inds, axes(I))`): covered in `multidimensional-logical-and-indexing`.
- `checkBooleanAxesCons@919` (`_check_boolean_axes(inds::Tuple, axes::Tuple) = (inds[1] == axes[1]) && _check_boolean_axes(tail(inds), tail(axes))`): covered in `multidimensional-index-traits-and-queries`.
- `checkBooleanAxesEmpty@920` (`_check_boolean_axes(::Tuple{}, axes::Tuple) = all(==(OneTo(1)), axes)`): covered in `multidimensional-index-traits-and-queries`.
- `ensureIndexableEmpty@922` (`ensure_indexable(I::Tuple{}) = ()`): covered in `multidimensional-logical-and-indexing`.
- `ensureIndexableCons@923` (`@inline ensure_indexable(I::Tuple{Any, Vararg{Any}}) = (I[1], ensure_indexable(tail(I))...)`): covered in `multidimensional-logical-and-indexing`.
- `ensureIndexableLogical@924` (`@inline ensure_indexable(I::Tuple{LogicalIndex, Vararg{Any}}) = (collect(I[1]), ensure_indexable(tail(I))...)`): covered in `multidimensional-logical-and-indexing`.
- `toIndicesMixed@928` (`@inline to_indices(A, I::Tuple{Vararg{Union{Integer, CartesianIndex}}}) = to_indices(A, (), I)`): covered in `multidimensional-logical-and-indexing`.
- `dropZeroDim@929` (`_drop_zerodim(I::Tuple{CartesianIndex{0}, Vararg}) = (@inline; _drop_zerodim(tail(I)))`): covered in `multidimensional-logical-and-indexing`.
- `toIndicesCartesian@932` (`@inline function to_indices(A, inds, I::Tuple{CartesianIndex{N}, Vararg}) where N`): covered in `multidimensional-logical-and-indexing`.
- `toIndicesCartesianArray@937` (`@inline function to_indices(A, inds, I::Tuple{AbstractArray{CartesianIndex{N}}, Vararg}) where N`): covered in `multidimensional-logical-and-indexing`.
- `toIndicesMask@942` (`@inline function to_indices(A, inds, I::Tuple{AbstractArray{Bool, N}, Vararg}) where N`): covered in `multidimensional-logical-and-indexing`.
- `toIndicesSingleMask@947` (`@inline to_indices(A, I::Tuple{AbstractArray{Bool}}) = (_maybe_linear_logical_index(IndexStyle(A), A, I[1]),)`): covered in `multidimensional-logical-and-indexing`.
- `maybeLinearLogicalDefault@948` (`_maybe_linear_logical_index(::IndexStyle, A, i) = to_index(A, i)`): covered in `multidimensional-logical-and-indexing`.
- `maybeLinearLogicalLinear@949` (`_maybe_linear_logical_index(::IndexLinear, A, i) = LogicalIndex{Int}(i)`): covered in `multidimensional-logical-and-indexing`.
- `toIndicesColon@952` (`@inline to_indices(A, inds, I::Tuple{Colon, Vararg}) =`): covered in `multidimensional-logical-and-indexing`.
- `uncolonEmpty@955` (`uncolon(::Tuple{}) = Slice(OneTo(1))`): covered in `multidimensional-logical-and-indexing`.
- `uncolonCons@956` (`uncolon(inds::Tuple) = Slice(inds[1])`): covered in `multidimensional-logical-and-indexing`.
- `precheckedFirst@964` (`@propagate_inbounds _prechecked_iterate(iter) = iterate(iter)`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `precheckedNext@965` (`@propagate_inbounds _prechecked_iterate(iter, state) = iterate(iter, state)`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `precheckedUnitFirst@967` (`_prechecked_iterate(iter::AbstractUnitRange) = first(iter), first(iter)`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `precheckedUnitNext@968` (`function _prechecked_iterate(iter::AbstractUnitRange, i)`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `precheckedLinearFirst@972` (`_prechecked_iterate(iter::LinearIndices) = first(iter), first(iter)`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `precheckedLinearNext@973` (`function _prechecked_iterate(iter::LinearIndices, i)`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `precheckedCartesianFirst@977` (`_prechecked_iterate(iter::CartesianIndices) = first(iter), first(iter)`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `precheckedCartesianNext@978` (`function _prechecked_iterate(iter::CartesianIndices, i::CartesianIndex)`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `precheckedSpecialFirst@982` (`_prechecked_iterate(iter::SCartesianIndices2) = first(iter), first(iter)`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `precheckedSpecialNext@983` (`function _prechecked_iterate(iter::SCartesianIndices2{K}, (;i, j)) where {K}`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `getindexScalarZero@989` (`getindex(x::Union{Number,AbstractChar}, ::CartesianIndex{0}) = x`): covered in `multidimensional-logical-and-indexing`.
- `getindexTupleCartesian@990` (`getindex(t::Tuple,  i::CartesianIndex{1}) = getindex(t, i.I[1])`): covered in `multidimensional-logical-and-indexing`.
- `getindexAbstract@995` (`@inline function _getindex(l::IndexStyle, A::AbstractArray, I::Union{Real, AbstractArray}...)`): covered in `multidimensional-logical-and-indexing`.
- `maybeReshapeLinear@1000` (`_maybe_reshape(::IndexLinear, A::AbstractArray, I...) = A`): covered in `multidimensional-logical-and-indexing`.
- `maybeReshapeVector@1001` (`_maybe_reshape(::IndexCartesian, A::AbstractVector, I...) = A`): covered in `multidimensional-logical-and-indexing`.
- `maybeReshapeCartesian@1002` (`@inline _maybe_reshape(::IndexCartesian, A::AbstractArray, I...) = __maybe_reshape(A, index_ndims(I...))`): covered in `multidimensional-logical-and-indexing`.
- `reshapeMatchingRank@1003` (`@inline __maybe_reshape(A::AbstractArray{T,N}, ::NTuple{N,Any}) where {T,N} = A`): covered in `multidimensional-logical-and-indexing`.
- `reshapeDifferentRank@1004` (`@inline __maybe_reshape(A::AbstractArray, ::NTuple{N,Any}) where {N} = reshape(A, Val(N))`): covered in `multidimensional-logical-and-indexing`.
- `unsafeGetindex@1006` (`function _unsafe_getindex(::IndexStyle, A::AbstractArray, I::Vararg{Union{Real, AbstractArray}, N}) where N`): covered in `multidimensional-logical-and-indexing`.
- `generateUnsafeGetindexBody@1015` (`function _generate_unsafe_getindex!_body(N::Int)`): covered in `multidimcov-multidimensional-repair-d1`.
- `unsafeGetindexBang@1030` (`@generated function _unsafe_getindex!(dest::AbstractArray, src::AbstractArray, I::Vararg{Union{Real, AbstractArray}, N}) where N`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `unsafeGetindexBangOne@1035` (`@eval function _unsafe_getindex!(dest::AbstractArray, src::AbstractArray, I::Vararg{Union{Real, AbstractArray},1})`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `unsafeGetindexBangTwo@1039` (`@eval function _unsafe_getindex!(dest::AbstractArray, src::AbstractArray, I::Vararg{Union{Real, AbstractArray},2})`): covered in `multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing`.
- `throwChecksizeError@1043` (`@noinline throw_checksize_error(A, sz) = throw(DimensionMismatch("output array is the wrong size; expected $sz, got $(size(A))"))`): covered in `multidimensional-logical-and-indexing`.
- `setindexAbstract@1046` (`function _setindex!(l::IndexStyle, A::AbstractArray, x, I::Union{Real, AbstractArray}...)`): covered in `multidimensional-logical-and-indexing`.
- `generateUnsafeSetindexBody@1053` (`function _generate_unsafe_setindex!_body(N::Int)`): covered in `multidimensional-logical-and-indexing`.
- `unsafeSetindexBang@1069` (`@generated function _unsafe_setindex!(::IndexStyle, A::AbstractArray, x, I::Vararg{Union{Real,AbstractArray}, N}) where N`): covered in `multidimensional-logical-and-indexing`.
- `unsafeSetindexBangOne@1073` (`@eval function _unsafe_setindex!(::IndexStyle, A::AbstractArray, x, I::Vararg{Union{Real,AbstractArray},1})`): covered in `multidimensional-logical-and-indexing`.
- `unsafeSetindexBangTwo@1077` (`@eval function _unsafe_setindex!(::IndexStyle, A::AbstractArray, x, I::Vararg{Union{Real,AbstractArray},2})`): covered in `multidimensional-logical-and-indexing`.
- `diffVector@1081` (`diff(a::AbstractVector) = diff(a, dims=1)`): covered in `arrayops-diff`.
- `diffArray@1113` (`function diff(a::AbstractArray{T,N}; dims::Integer) where {T,N}`): covered in `arrayops-diff, multidim-diff-size`.
- `diffRange@1123` (`function diff(r::AbstractRange{T}; dims::Integer=1) where {T}`): covered in `arrayops-diff`.
- `mightaliasSubarray@1130` (`function mightalias(A::SubArray, B::SubArray)`): covered in `broadcastviews-overlap-conservative, broadcastviews-cartesian-alias`.
- `parentsMatchAbstract@1153` (`_parentsmatch(A::AbstractArray, B::AbstractArray) = A === B`): covered in `broadcastviews-overlap-conservative`.
- `parentsMatchDense@1154` (`_parentsmatch(A::DenseArray, B::DenseArray) = elsize(A) == elsize(B) && pointer(A) == pointer(B) && size(A) == size(B)`): covered in `broadcastviews-overlap-conservative`.
- `parentsMatchStrided@1155` (`_parentsmatch(A::StridedArray, B::StridedArray) = elsize(A) == elsize(B) && pointer(A) == pointer(B) && strides(A) == strides(B)`): covered in `broadcastviews-overlap-conservative`.
- `indicesOverlapEmpty@1158` (`_indicesmightoverlap(A::Tuple{}, B::Tuple{}) = true`): covered in `broadcastviews-overlap-conservative`.
- `indicesOverlapLeftEmpty@1159` (`_indicesmightoverlap(A::Tuple{}, B::Tuple) = error("malformed subarray")`): covered in `broadcastviews-overlap-conservative`.
- `indicesOverlapRightEmpty@1160` (`_indicesmightoverlap(A::Tuple, B::Tuple{}) = error("malformed subarray")`): covered in `broadcastviews-overlap-conservative`.
- `indicesOverlapRanges@1162` (`@inline function _indicesmightoverlap(A::Tuple{AbstractRange, Vararg{Any}}, B::Tuple{AbstractRange, Vararg{Any}})`): covered in `broadcastviews-overlap-conservative`.
- `indicesOverlapUnitRanges@1166` (`@inline function _indicesmightoverlap(A::Tuple{AbstractUnitRange, Vararg{Any}}, B::Tuple{AbstractUnitRange, Vararg{Any}})`): covered in `broadcastviews-overlap-conservative`.
- `indicesOverlapScalars@1170` (`@inline _indicesmightoverlap(A::Tuple{Real, Vararg{Any}}, B::Tuple{Real, Vararg{Any}}) =`): covered in `broadcastviews-overlap-conservative`.
- `indicesOverlapScalarArray@1172` (`@inline _indicesmightoverlap(A::Tuple{Real, Vararg{Any}}, B::Tuple{AbstractArray, Vararg{Any}}) =`): covered in `broadcastviews-overlap-conservative, broadcastviews-cartesian-alias`.
- `indicesOverlapArrayScalar@1174` (`@inline _indicesmightoverlap(A::Tuple{AbstractArray, Vararg{Any}}, B::Tuple{Real, Vararg{Any}}) =`): covered in `broadcastviews-overlap-conservative`.
- `indicesOverlapArrays@1177` (`@inline function _indicesmightoverlap(A::Tuple{AbstractArray, Vararg{Any}}, B::Tuple{AbstractArray, Vararg{Any}})`): covered in `broadcastviews-overlap-conservative`.
- `indicesOverlapFallback@1188` (`_indicesmightoverlap(A::Tuple{Any, Vararg{Any}}, B::Tuple{Any, Vararg{Any}}) = true`): covered in `broadcastviews-overlap-conservative`.
- `copytoCartesian@1190` (`function copyto!(dest::AbstractArray{T1,N}, Rdest::CartesianIndices{N},`): covered in `multidim-copyto-empty-size, multidim-circshift-formula, multidim-circcopy-nonempty`.
- `circshiftEmpty@1246` (`circshift!(dest::AbstractArray, src, ::Tuple{}) = copyto!(dest, src)`): covered in `multidim-circshift-formula`.
- `circshift@1257` (`@noinline function circshift!(dest::AbstractArray{T,N}, src, shiftamt::DimsInteger) where {T,N}`): covered in `multidim-circshift-formula`.
- `circshiftConvert@1265` (`circshift!(dest::AbstractArray, src, shiftamt) =`): covered in `multidim-circshift-formula`.
- `circshiftCons@1284` (`@inline function _circshift!(dest, rdest, src, rsrc,`): covered in `multidim-circshift-formula`.
- `circshiftBase@1297` (`function _circshift!(dest, rdest, src, rsrc, inds, shiftamt)`): covered in `multidim-circshift-formula`.
- `circcopy@1337` (`function circcopy!(dest, src)`): covered in `multidim-circcopy-empty, multidim-circcopy-nonempty`.
- `circcopyCons@1349` (`@inline function _circcopy!(dest, rdest, indsdest::Tuple{AbstractUnitRange,Vararg{Any}},`): covered in `multidim-circcopy-empty, multidim-circcopy-nonempty`.
- `circcopyBase@1364` (`function _circcopy!(dest, rdest, indsdest, src, rsrc, indssrc)`): covered in `multidim-circcopy-empty, multidim-circcopy-nonempty`.
- `bitGetindexContiguous@1374` (`@inline function _unsafe_getindex!(X::BitArray, B::BitArray, I0::Union{AbstractUnitRange{Int},Slice})`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitGetindexRanges@1380` (`@generated function _unsafe_getindex!(X::BitArray, B::BitArray,`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitGetindexGeneral@1419` (`@generated function _unsafe_getindex!(X::BitArray, B::BitArray, I::Union{Int,AbstractArray{Int}}...)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `copyToBitarrayChunks@1438` (`function copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::StridedArray, pos_s::Int, numbits::Int)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `tryBoolConversion@1455` (`@inline try_bool_conversion(x::Real) =`): covered in `multidimensional-bitarray-and-slice-ops`.
- `uncheckedBoolConvert@1457` (`@inline unchecked_bool_convert(x::Real) = x == 1`): covered in `multidimensional-bitarray-and-slice-ops`.
- `copyToBitarrayChunksReal@1459` (`function copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::StridedArray{<:Real}, pos_s::Int, numbits::Int)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitSetindexContiguous@1516` (`@inline function setindex!(B::BitArray, X::Union{StridedArray,BitArray}, J0::D) where {D<:Union{Colon,AbstractUnitRange{Int}}}`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitSetindexRanges@1527` (`@inline function setindex!(B::BitArray, X::Union{StridedArray,BitArray},`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitUnsafeSetindexRanges@1533` (`@generated function _unsafe_setindex!(B::BitArray, X::Union{StridedArray,BitArray},`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitSetindexAbstract@1568` (`@propagate_inbounds function setindex!(B::BitArray, X::AbstractArray,`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitFillContiguous@1574` (`function fill!(V::SubArray{Bool, <:Any, <:BitArray, <:Tuple{AbstractUnitRange{Int}}}, x)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitFillRanges@1583` (`fill!(V::SubArray{Bool, <:Any, <:BitArray, <:Tuple{AbstractUnitRange{Int}, Vararg{Union{Int,AbstractUnitRange{Int}}}}}, x) =`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitUnsafeFillIndices@1586` (`@generated function _unsafe_fill_indices!(B::BitArray, x,`): covered in `multidimensional-bitarray-and-slice-ops`.
- `bitIsassigned@1621` (`@generated function isassigned(B::BitArray, I_0::Int, I::Int...)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `isassignedCartesian@1637` (`@propagate_inbounds isassigned(A::AbstractArray, i::CartesianIndex) = isassigned(A, Tuple(i)...)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `isassignedMixed@1638` (`@propagate_inbounds function isassigned(A::AbstractArray, i::Union{Integer, CartesianIndex}...)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `isassignedIntegers@1641` (`@inline function isassigned(A::AbstractArray, i::Integer...)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `permutedims@1669` (`function permutedims(B::StridedArray, perm)`): covered in `multidimcov-permutedims-offset-view`.
- `checkdimsPermArrays@1678` (`checkdims_perm(P::AbstractArray{TP,N}, B::AbstractArray{TB,N}, perm) where {TP,TB,N} = checkdims_perm(axes(P), axes(B), perm)`): covered in `multidimcov-permutedims-offset-view, multidimensional-bitarray-and-slice-ops`.
- `checkdimsPerm@1679` (`function checkdims_perm(indsP::NTuple{N, AbstractUnitRange}, indsB::NTuple{N, AbstractUnitRange}, perm) where {N}`): covered in `multidimcov-permutedims-offset-view`.
- `permutedimsBang@1689` (`@eval @generated function permutedims!(P::$PT{$(V...)}, B::$BT{$(V...)}, perm) where $(V...)`): covered in `multidimcov-permutedims-offset-view`.
- `prehashedHash@1723` (`hash(x::Prehashed) = x.hash`): covered in `ranges-hash-short-equal-consistency`.
- `unique@1764` (`unique(A::AbstractArray; dims::D = :) where {D<:Union{Colon,Integer}} = _unique_dims(A, dims)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `uniqueDimsColon@1766` (`_unique_dims(A::AbstractArray, dims::Colon) = invoke(unique, Tuple{Any}, A)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `uniqueDims@1768` (`@generated function _unique_dims(A::AbstractArray{T,N}, dim::Integer) where {T,N}`): covered in `multidimensional-bitarray-and-slice-ops`.
- `showargPairsInteger@1839` (`function Base.showarg(io::IO, r::Iterators.Pairs{<:Integer, <:Any, <:Any, T}, toplevel) where T <: Union{AbstractVector, Tuple}`): covered in `multidimensional-bitarray-and-slice-ops`.
- `showargPairsCartesian@1842` (`function Base.showarg(io::IO, r::Iterators.Pairs{<:CartesianIndex, <:Any, <:Any, T}, toplevel) where T <: AbstractArray`): covered in `multidimensional-bitarray-and-slice-ops`.
- `showargPairsVector@1846` (`function Base.showarg(io::IO, r::Iterators.Pairs{<:CartesianIndex, <:Any, <:Any, T}, toplevel) where T<:AbstractVector`): covered in `multidimensional-bitarray-and-slice-ops`.
- `sortslices@1969` (`function sortslices(A::AbstractArray; dims::Union{Integer, Tuple{Vararg{Integer}}}, kws...)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `sortslicesBang@1981` (`function _sortslices!(B, A, ::Val{dims}; kws...) where dims`): covered in `multidimensional-bitarray-and-slice-ops`.
- `refGetindexZero@1992` (`getindex(b::Ref, ::CartesianIndex{0}) = getindex(b)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `refSetindexZero@1993` (`setindex!(b::Ref, x, ::CartesianIndex{0}) = setindex!(b, x)`): covered in `multidimensional-bitarray-and-slice-ops`.
- `hashFib@1997` (`function _hash_fib(A, h::UInt)`): covered in `ranges-hash-short-equal-consistency`.
- `unionSplitCons@2077` (`@inline function union_split(f, @nospecialize(x), ts::Tuple{Val{T}, Vararg{Val,N}}, args...) where {T, N}`): covered in `ranges-hash-short-equal-consistency`.
- `unionSplitEmpty@2084` (`@inline union_split(f, x, ::Tuple{}, args::Vararg{Any, N}) where {N} = f(x, args...)`): covered in `ranges-hash-short-equal-consistency`.
- `hashShaped@2086` (`function hash_shaped(A, h0::UInt, eltype_hint=())`): covered in `ranges-hash-short-equal-consistency`.
- `hashArray@2123` (`hash(A::AbstractArray, h::UInt) = hash_shaped(A, h ⊻ hash_abstractarray_seed)`): covered in `ranges-hash-short-equal-consistency`.
-/

/-- Foreign interfaces used by the array hashing methods. The Fibonacci branch
is instantiated with its source definition, including all of its foreign callees. -/
structure ShortHashCalls (A : Type) where
  Value : Type
  Axis : Type
  AxisValue : Type
  Length : Type
  FirstIndex : Type
  Offset : Type
  IndexN : Type
  IndexNI : Type
  Index : Type
  Limit : Type
  Key : Type
  KeySet : Type
  LinearMap : Type
  Tag : Type
  iterator : ForIn Result A Value
  axes : A → List Axis
  first : Axis → AxisValue
  last : Axis → AxisValue
  hashAxes : List AxisValue → JInt .u64 → Result (JInt .u64)
  length : A → Length
  lessLength : Length → I64 → Bool
  subtractLength : Length → I64 → Result Limit
  firstindex : A → FirstIndex
  subtractFirst : FirstIndex → I64 → Result Offset
  addN : Offset → I64 → Result IndexN
  addI : IndexN → I64 → Result IndexNI
  subtractOne : IndexNI → I64 → Result Index
  getindex : A → Index → Result Value
  getindexRemainder : A → IndexN → Result Value
  isa : Value → Tag → Bool
  hashValue : Value → JInt .u64 → Result (JInt .u64)
  leLimit : I64 → Limit → Bool
  leLength : I64 → Length → Bool
  hashMix : JInt .u64 → JInt .u64 → JInt .u64
  hashUInt : JInt .u64 → JInt .u64
  keys : A → Result KeySet
  linearIndices : KeySet → Result LinearMap
  vec : KeySet → Result KeySet
  lastKey : KeySet → Result Key
  keyToLinear : LinearMap → Key → Result I64
  linearToKey : KeySet → I64 → Result Key
  oneunit : I64 → I64
  firstLinear : KeySet → Result I64
  getindexFib : A → Key → Result Value
  mod1 : I64 → I64 → Result I64
  rem : I64 → I64 → Result I64
  hashKey : Key → JInt .u64 → Result (JInt .u64)
  findprevDistinct : Value → A → Key → Result (Option Key)

private theorem unionSplitHashDispatch_eq {V Tag : Type} (isa : V → Tag → Bool)
    (hash : V → JInt .u64 → Result (JInt .u64)) (value : V) :
    ∀ (hint : List Tag) (seed : JInt .u64),
      unionSplitHashDispatch isa hash value hint seed = hash value seed
  | [], _ => rfl
  | tag :: rest, seed => by
    unfold unionSplitHashDispatch unionSplitCons
    cases isa value tag
    · exact unionSplitHashDispatch_eq isa hash value rest seed
    · rfl

private theorem forIn_integer_values {V : Type} (value : V → Int)
    (hash : Int → JInt .u64 → JInt .u64) (xs : List V) (seed : JInt .u64) :
    (forIn xs seed (fun x h => .ok (.yield (hash (value x) h))) : Result (JInt .u64)) =
      .ok ((xs.map value).foldl (fun h x => hash x h) seed) := by
  induction xs generalizing seed with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, bind, Except.bind, List.map_cons, List.foldl_cons]
    exact ih _


/-- Equal integer-valued arrays with equal axes and contents have equal hashes
across the direct short branch (for any `union_split` type-hint list), the
8-stream unrolled + remainder branch, and the `_hash_fib` Fibonacci sampling
and collision loop; and `hash(x::Prehashed)` returns `x.hash`. -/
def ShortEqualArrayHashConsistency : Prop :=
  ∀ (A : Type) (c : ShortHashCalls A) (contents : A → List c.Value)
    (axisValue : c.AxisValue → Int) (elementValue : c.Value → Int)
    (integerHash : Int → JInt .u64 → JInt .u64)
    (tupleHash : List Int → JInt .u64 → JInt .u64),
    (∀ (a : A) (S : Type) (initial : S)
      (step : c.Value → S → Result (ForInStep S)),
      c.iterator.forIn a initial step = forIn (contents a) initial step) →
    (∀ values seed, c.hashAxes values seed = .ok (tupleHash (values.map axisValue) seed)) →
    (∀ value seed, c.hashValue value seed = .ok (integerHash (elementValue value) seed)) →
    ∀ (a b : A) (seed : JInt .u64) (hint : List c.Tag),
      ((c.axes a).map c.first).map axisValue = ((c.axes b).map c.first).map axisValue →
      ((c.axes a).map c.last).map axisValue = ((c.axes b).map c.last).map axisValue →
      (contents a).map elementValue = (contents b).map elementValue →
      let fibHash := hashFib c.keys c.linearIndices c.vec c.lastKey c.keyToLinear c.linearToKey
        c.oneunit c.firstLinear c.getindexFib c.mod1 c.rem c.hashKey c.hashValue
        c.hashMix c.hashUInt c.findprevDistinct
      let actualHash := fun arr s hnt => hashArray (fun x h =>
        @hashShaped A c.Value (List c.Tag) c.Axis c.AxisValue c.Length c.FirstIndex
          c.Offset c.IndexN c.IndexNI c.Index c.Limit c.iterator
          c.axes c.first c.last c.hashAxes c.length c.lessLength c.subtractLength
          c.firstindex c.subtractFirst c.addN c.addI c.subtractOne
          c.getindex c.getindexRemainder (unionSplitHashDispatch c.isa c.hashValue)
          c.leLimit c.leLength c.hashMix c.hashUInt
          fibHash x h hnt) arr s
      (∀ h : JInt .u64, prehashedHash h = h) ∧
      (∀ v s, unionSplitHashDispatch c.isa c.hashValue v hint s =
        .ok (integerHash (elementValue v) s)) ∧
      (c.lessLength (c.length a) (int 8) = true →
       c.lessLength (c.length b) (int 8) = true →
        ∃ result, actualHash a seed hint = some (.ok result) ∧
          actualHash b seed hint = some (.ok result)) ∧
      (c.length a = c.length b →
       c.firstindex a = c.firstindex b →
       (∀ idx, c.getindex a idx = c.getindex b idx) →
       (∀ idx, c.getindexRemainder a idx = c.getindexRemainder b idx) →
       c.keys a = c.keys b →
       (∀ k, c.getindexFib a k = c.getindexFib b k) →
       (∀ v k, c.findprevDistinct v a k = c.findprevDistinct v b k) →
        fibHash a seed = fibHash b seed ∧
        actualHash a seed hint = actualHash b seed hint)

theorem shortEqualArrayHashConsistency : ShortEqualArrayHashConsistency := by
  intro A c contents axisValue elementValue integerHash tupleHash iteration axesHash valueHash
    a b seed hint firstEqual lastEqual elementsEqual
  dsimp only
  let initial := JInt.wrap .u64 (Int.ofNat (Nat.xor seed.val.toNat 0x7e2d6fb6448beb77))
  let shape := tupleHash (((c.axes a).map c.last).map axisValue)
    (tupleHash (((c.axes a).map c.first).map axisValue) initial)
  let result := ((contents a).map elementValue).foldl (fun h x => integerHash x h) shape
  refine ⟨fun _ => rfl, fun v s => by rw [unionSplitHashDispatch_eq, valueHash],
    fun smallA smallB => ⟨result, ?_, ?_⟩,
    fun hlen hfirst hget hrem hkeys hgetFib hfind => ?_⟩
  · simp [hashArray, hashShaped, hashShaped.shapePrefix, hashShaped.shortChain,
      axesHash, smallA, unionSplitHashDispatch_eq, iteration, valueHash, forIn_integer_values,
      initial, shape, result, pure, Except.pure, bind, Except.bind]
  · simp [hashArray, hashShaped, hashShaped.shapePrefix, hashShaped.shortChain,
      axesHash, smallB, unionSplitHashDispatch_eq, iteration, ← firstEqual, ← lastEqual,
      valueHash, forIn_integer_values, ← elementsEqual,
      initial, shape, result, pure, Except.pure, bind, Except.bind]
  · have hfib_eq : ∀ h : JInt .u64,
        hashFib c.keys c.linearIndices c.vec c.lastKey c.keyToLinear c.linearToKey
          c.oneunit c.firstLinear c.getindexFib c.mod1 c.rem c.hashKey c.hashValue
          c.hashMix c.hashUInt c.findprevDistinct a h =
        hashFib c.keys c.linearIndices c.vec c.lastKey c.keyToLinear c.linearToKey
          c.oneunit c.firstLinear c.getindexFib c.mod1 c.rem c.hashKey c.hashValue
          c.hashMix c.hashUInt c.findprevDistinct b h := by
      intro h
      have hinit : hashFib.initialState c.keys c.linearIndices c.vec c.lastKey c.keyToLinear
          c.oneunit c.firstLinear a h =
          hashFib.initialState c.keys c.linearIndices c.vec c.lastKey c.keyToLinear
          c.oneunit c.firstLinear b h := by
        unfold hashFib.initialState; rw [hkeys]
      have hstep : ∀ ks map first,
          hashFib.step c.keyToLinear c.linearToKey c.getindexFib c.mod1 c.rem c.hashKey c.hashValue
            c.hashMix c.hashUInt c.findprevDistinct a h ks map first =
          hashFib.step c.keyToLinear c.linearToKey c.getindexFib c.mod1 c.rem c.hashKey c.hashValue
            c.hashMix c.hashUInt c.findprevDistinct b h ks map first := by
        intro ks map first
        funext state
        unfold hashFib.step
        simp only [hgetFib, hfind]
      unfold hashFib
      rw [hinit]
      cases hashFib.initialState c.keys c.linearIndices c.vec c.lastKey c.keyToLinear c.oneunit c.firstLinear b h with
      | error _ => rfl
      | ok val =>
        rcases val with ⟨ks, map, first, st⟩
        dsimp only
        rw [hstep ks map first]
    refine ⟨hfib_eq seed, ?_⟩
    unfold hashArray hashShaped
    have hpref : hashShaped.shapePrefix c.axes c.first c.last c.hashAxes c.length a initial =
        hashShaped.shapePrefix c.axes c.first c.last c.hashAxes c.length b initial := by
      unfold hashShaped.shapePrefix
      simp [axesHash, firstEqual, lastEqual, hlen, bind, Except.bind, pure, Except.pure]
    have hshort : ∀ h,
        @hashShaped.shortChain A c.Value (List c.Tag) c.iterator
          (unionSplitHashDispatch c.isa c.hashValue) a hint h =
        @hashShaped.shortChain A c.Value (List c.Tag) c.iterator
          (unionSplitHashDispatch c.isa c.hashValue) b hint h := by
      intro h
      simp [hashShaped.shortChain, unionSplitHashDispatch_eq, iteration, valueHash,
        forIn_integer_values, elementsEqual, bind, Except.bind, pure, Except.pure]
    have hspref : ∀ len,
        hashShaped.streamPrefix c.subtractLength c.firstindex c.subtractFirst a len =
        hashShaped.streamPrefix c.subtractLength c.firstindex c.subtractFirst b len := by
      intro len; unfold hashShaped.streamPrefix; rw [hfirst]
    have hsstep : ∀ off limit,
        hashShaped.streamStep c.addN c.addI c.subtractOne c.getindex
          (unionSplitHashDispatch c.isa c.hashValue) c.leLimit a hint off limit =
        hashShaped.streamStep c.addN c.addI c.subtractOne c.getindex
          (unionSplitHashDispatch c.isa c.hashValue) c.leLimit b hint off limit := by
      intro off limit; funext st; unfold hashShaped.streamStep; simp only [hget]
    have hrstep : ∀ off len,
        hashShaped.remainderStep c.addN c.getindexRemainder
          (unionSplitHashDispatch c.isa c.hashValue) c.leLength a hint off len =
        hashShaped.remainderStep c.addN c.getindexRemainder
          (unionSplitHashDispatch c.isa c.hashValue) c.leLength b hint off len := by
      intro off len; funext st; unfold hashShaped.remainderStep; simp only [hrem]
    dsimp only [initial] at hpref ⊢
    rw [hpref]
    cases hashShaped.shapePrefix c.axes c.first c.last c.hashAxes c.length b initial with
    | error _ => rfl
    | ok val =>
      rcases val with ⟨h, len⟩
      dsimp only
      by_cases h8 : c.lessLength len (int 8) = true
      · rw [ite_eq_left h8, ite_eq_left h8, hshort h]
      · rw [ite_eq_right h8, ite_eq_right h8]
        by_cases h32 : c.lessLength len (int 32768) = true
        · rw [ite_eq_left h32, ite_eq_left h32, hspref len]
          cases hashShaped.streamPrefix c.subtractLength c.firstindex c.subtractFirst b len with
          | error _ => rfl
          | ok pval =>
            rcases pval with ⟨off, limit⟩
            dsimp only
            rw [hsstep off limit, hrstep off len]
        · rw [ite_eq_right h32, ite_eq_right h32, hfib_eq h]
open JuliaLean.Registry

def entries : List Entry := [
  { id := "ranges-hash-short-equal-consistency", juliaFile := "base/multidimensional.jl",
    juliaFns := ["hash(::AbstractArray, ::UInt)", "hash_shaped", "_hash_fib", "union_split", "hash(::BitArray, ::UInt)"],
    statement := "Integer-valued arrays with equal axes and equal complete iteration contents hash equally in the direct branch, union_split dispatches matching element types to their specialized hash before falling back, _hash_fib folds sampled key-value stream hashes, and BitArray hash returns the prehashed UInt.",
    source := "Hash equality invariant; base/multidimensional.jl:1723,1997-2123", status := .proven,
    prop := ``ShortEqualArrayHashConsistency, thm := some ``shortEqualArrayHashConsistency,
    notes := "Generic over the element, axis, length and intermediate index types. Own-file union-split, Fibonacci, and BitArray callees use their source definitions." },
  { id := "multidimcov-multidimensional-repair-c2", juliaFile := "base/multidimensional.jl",
    juliaFns := ["iterate(::LogicalIndex, state)"],
    statement := "LogicalIndex scanning returns the first currently true mask position in iterator order.",
    source := "LogicalIndex docstring and iteration invariant", status := .proven,
    prop := ``LogicalSelection, thm := some ``logicalSelection },
  { id := "multidimcov-multidimensional-repair-d1", juliaFile := "base/multidimensional.jl",
    juliaFns := ["_generate_unsafe_getindex!_body", "_unsafe_getindex!", "_prechecked_iterate"],
    statement := "The generated gather visits the first dimension fastest and makes exactly the product of selector lengths writes.",
    source := "Base.Cartesian nested-loop invariant", status := .proven,
    prop := ``GeneratedTraversal, thm := some ``generatedTraversal },
  { id := "multidim-circcopy-empty", juliaFile := "base/multidimensional.jl",
    juliaFns := ["circcopy!", "_circcopy!"],
    statement := "Circular copying succeeds for equal-size distinct arrays, including empty axes.",
    source := "circcopy! docstring", status := .refuted,
    prop := ``CirccopyCorrect, thm := some ``circcopyCorrect_refuted,
    issue := "none found (existing repro and issue searches retained)" },
  { id := "multidimcov-logicalindex-mutable-mask", juliaFile := "base/multidimensional.jl",
    juliaFns := ["iterate(::LogicalIndex, state)"],
    statement := "LogicalIndex enumerates the current mask's true positions after mask mutation.",
    source := "LogicalIndex docstring", status := .refuted,
    prop := ``LogicalIndexTracksMask, thm := some ``logicalIndexTracksMask_refuted,
    issue := "none found (existing repro and issue searches retained)" },
  { id := "multidimcov-permutedims-offset-view", juliaFile := "base/multidimensional.jl",
    juliaFns := ["permutedims(::StridedArray, perm)", "permutedims!", "checkdims_perm"],
    statement := "A valid permutation succeeds for strided arrays with offset axes.",
    source := "permutedims documented contract", status := .refuted,
    prop := ``PermutedimsOffsetCorrect, thm := some ``permutedimsOffsetCorrect_refuted,
    issue := "none found (existing repro and issue searches retained)" },
  { id := "broadcastviews-cartesian-alias", juliaFile := "base/multidimensional.jl",
    juliaFns := ["mightalias(::SubArray, ::SubArray)", "_indicesmightoverlap"],
    statement := "Views sharing a parent position are detected as potentially aliasing, including CartesianIndex index arrays.",
    source := "mightalias conservative-test docstring", status := .refuted,
    prop := ``AliasAssignFresh, thm := some ``aliasAssignFresh_refuted,
    issue := "none found (existing repro and issue searches retained)" },
  { id := "multidim-cartesian-iterate", juliaFile := "base/multidimensional.jl",
    juliaFns := ["iterate(::CartesianIndices)", "__inc", "first(::CartesianIndices)", "last(::CartesianIndices)"],
    statement := "CartesianIndices iteration visits every index once in first-coordinate-fastest order, then stops.",
    source := "CartesianIndices docstring, base/multidimensional.jl:212-226", status := .proven,
    prop := ``CartesianIterOrder, thm := some ``cartesianIterOrder },
  { id := "multidim-cartesian-reverse-iterate", juliaFile := "base/multidimensional.jl",
    juliaFns := ["iterate(::Reverse{<:CartesianIndices})", "__dec", "first(::CartesianIndices)", "last(::CartesianIndices)"],
    statement := "Reverse iteration visits exactly the forward indices in reverse order.",
    source := "Iterators.reverse documented invariant", status := .proven,
    prop := ``CartesianRevOrder, thm := some ``cartesianRevOrder },
  { id := "multidim-cartesian-isless", juliaFile := "base/multidimensional.jl",
    juliaFns := ["isless(::CartesianIndex, ::CartesianIndex)"],
    statement := "CartesianIndex comparison is an irreflexive, transitive, total order for each rank.",
    source := "isless total-order invariant; base/multidimensional.jl:142", status := .proven,
    prop := ``CartesianIslessOrder, thm := some ``cartesianIslessOrder },
  { id := "multidim-reverse-dims-check", juliaFile := "base/multidimensional.jl",
    juliaFns := ["_reverse(::CartesianIndices, ::Colon)", "_reverse(::CartesianIndices, ::Integer)", "_reverse(::CartesianIndices, ::Tuple)", "_reverse(::CartesianIndices{1}, ::Tuple{Integer})"],
    statement := "Reverse on CartesianIndices reverses all axes on Colon, reverses axis d (with 1 <= d <= rank) on a single dimension or 1D tuple, and on a dimension tuple succeeds with the selected axes reversed iff the dimensions are distinct and between one and the rank.",
    source := "reverse dims invariant; base/multidimensional.jl:547-570", status := .proven,
    prop := ``ReverseDimsCheck, thm := some ``reverseDimsCheck },
  { id := "multidim-cartesianindices-empty-eq", juliaFile := "base/multidimensional.jl",
    juliaFns := ["==(::CartesianIndices, ::CartesianIndices)"],
    statement := "CartesianIndices equality agrees with equality of represented arrays.",
    source := "AbstractArray shape-and-element equality invariant", status := .refuted,
    prop := ``CartesianEqArrays, thm := some ``cartesianEqArrays_refuted,
    issue := "none found (existing repro and issue searches retained)" },
  { id := "multidim-copyto-empty-size", juliaFile := "base/multidimensional.jl",
    juliaFns := ["copyto!(::AbstractArray, ::CartesianIndices, ::AbstractArray, ::CartesianIndices)"],
    statement := "Region size mismatches throw ArgumentError, including empty destinations.",
    source := "base/multidimensional.jl:1218-1222: sizes of the two regions must match", status := .refuted,
    prop := ``CopytoSizeChecked, thm := some ``copytoSizeChecked_refuted,
    issue := "none found (existing repro and issue searches retained)" },
  { id := "multidimensional-cartesian-neg-involutive", juliaFile := "base/multidimensional.jl",
    juliaFns := ["-(::CartesianIndex)"],
    statement := "Negating a CartesianIndex twice restores every coordinate, including typemin(Int).",
    source := "coordinate arithmetic invariant", status := .proven,
    prop := ``CartesianNegInvolutive, thm := some ``cartesianNegInvolutive },
  { id := "multidimensional-cartesian-minmax-commute", juliaFile := "base/multidimensional.jl",
    juliaFns := ["min(::CartesianIndex, ::CartesianIndex)", "max(::CartesianIndex, ::CartesianIndex)"],
    statement := "Coordinate-wise minimum and maximum are commutative.",
    source := "coordinate lattice invariant", status := .proven,
    prop := ``CartesianMinMaxCommutes, thm := some ``cartesianMinMaxCommutes },
  { id := "multidimensional-cartesian-add-commutes", juliaFile := "base/multidimensional.jl",
    juliaFns := ["+(::CartesianIndex, ::CartesianIndex)"],
    statement := "CartesianIndex addition is commutative for every tuple of Int coordinates.",
    source := "coordinate arithmetic invariant", status := .proven,
    prop := ``CartesianAddCommutes, thm := some ``cartesianAddCommutes },
  { id := "arrayops-diff", juliaFile := "base/multidimensional.jl",
    juliaFns := ["diff(::AbstractVector)", "diff(::AbstractArray)", "diff(::AbstractRange)"],
    statement := "diff(v) on a vector or range with Int64-representable length has length(v)-1 entries (0 for empty v) equal to v[i+1] - v[i] in the element type, and diff(r; dims) throws ArgumentError for dims != 1 across any Integer dimension type.",
    source := "diff docstring, base/multidimensional.jl:1081-1126", status := .proven,
    prop := ``ArrayDiffSpec, thm := some ``arrayDiffSpec },
  { id := "multidim-diff-size", juliaFile := "base/multidimensional.jl",
    juliaFns := ["diff(::AbstractArray)"],
    statement := "diff(A; dims) on any array with Int64-representable axis lengths has the size of A with size(A, dims) reduced by one (not below zero), and throws ArgumentError for dims outside 1:ndims(A) across any Integer dimension type.",
    source := "diff docstring, base/multidimensional.jl:1113-1122", status := .proven,
    prop := ``DiffSize, thm := some ``diffSize_proven },
  { id := "broadcastviews-overlap-conservative", juliaFile := "base/multidimensional.jl",
    juliaFns := ["mightalias(::SubArray, ::SubArray)", "_indicesmightoverlap", "_parentsmatch"],
    statement := "Across all 14 _parentsmatch, _indicesmightoverlap, and mightalias methods and arbitrary scalar, range, and array index types (without CartesianIndex arrays), same-parent views return true whenever the two index sets share an in-bounds parent position, and mismatched-rank tuples throw ErrorException(\"malformed subarray\").",
    source := "mightalias docstring, base/multidimensional.jl:1130-1188", status := .proven,
    prop := ``OverlapConservativeNoCarts, thm := some ``overlapConservativeNoCarts },
  { id := "multidim-circshift-formula", juliaFile := "base/multidimensional.jl",
    juliaFns := ["circshift!", "_circshift!", "copyto!(::AbstractArray, ::CartesianIndices, ::AbstractArray, ::CartesianIndices)", "getindex(::CartesianIndices, ::Vararg{Int})", "in(::CartesianIndex, ::CartesianIndices)", "-(::CartesianIndex, ::CartesianIndex)"],
    statement := "circshift!(dest, src, s)[J] == src[mod.(J .- 1 .- s, n) .+ 1] for each dimension (missing shifts are zero, and empty shift tuples delegate to copyto!), for every array with Int64-representable dimensions and every tuple of shift amounts of any Integer type no longer than ndims(src).",
    source := "circshift! docstring, base/multidimensional.jl:1246-1299", status := .proven,
    prop := ``CircshiftFormula, thm := some ``circshiftFormula },
  { id := "multidim-circcopy-nonempty", juliaFile := "base/multidimensional.jl",
    juliaFns := ["circcopy!", "_circcopy!", "copyto!(::AbstractArray, ::CartesianIndices, ::AbstractArray, ::CartesianIndices)", "getindex(::CartesianIndices, ::Vararg{Int})", "in(::CartesianIndex, ::CartesianIndices)", "-(::CartesianIndex, ::CartesianIndex)"],
    statement := "circcopy!(dest, src) on nonempty arrays of the same size with Int64-representable axis bounds copies src with each dimension indexed modulo its length: dest[J] == src[K] where K ≡ J (mod size) lies in the axes of src.",
    source := "circcopy! docstring, base/multidimensional.jl:1337-1366", status := .proven,
    prop := ``CirccopyNonempty, thm := some ``circcopyNonempty },
  { id := "multidimensional-cartesian-algebra-and-hash", juliaFile := "base/multidimensional.jl",
    juliaFns := ["CartesianIndex", "flatten", "show(::IO, ::CartesianIndex)", "length(::CartesianIndex)", "length(::Type{<:CartesianIndex})", "getindex(::CartesianIndex, ::Integer)", "firstindex(::CartesianIndex)", "lastindex(::CartesianIndex)", "get(::AbstractArray, ::CartesianIndex, ::Any)", "eltype(::Type{T}) where {T<:CartesianIndex}", "Tuple(::CartesianIndex)", "setindex(::CartesianIndex, ::Any, ::Int)", "==(::CartesianIndex, ::CartesianIndex)", "zero(::CartesianIndex)", "zero(::Type{CartesianIndex{N}})", "oneunit(::CartesianIndex)", "oneunit(::Type{CartesianIndex{N}})", "+(::CartesianIndex)", "*(::Integer, ::CartesianIndex)", "*(::CartesianIndex, ::Integer)", "convert(::Type{T}, ::CartesianIndex{1})", "convert(::Type{T}, ::CartesianIndex)", "hash(::CartesianIndex, ::UInt)", "_ind2sub(::Tuple, ::CartesianIndex)", "iterate(::CartesianIndex)", "range_start_step_length(::CartesianIndex, ::CartesianIndex, ::Integer)", "show(::IO, ::StepRangeLen{<:CartesianIndex})", "in(::CartesianIndex, ::StepRangeLen)"],
    statement := "CartesianIndex constructors convert and pad coordinates to rank N; Tuple flattening concatenates nested tuples; == is structural equality; zero and oneunit have rank N with zero as additive/subtractive identity; scalar multiplication scales coordinates; setindex updates one coordinate; and 1D CartesianIndex hashing is injective whenever the coordinate hash is injective.",
    source := "CartesianIndex algebraic and hash invariants; base/multidimensional.jl:77-192", status := .proven,
    prop := ``CartesianAlgebraAndHash, thm := some ``cartesianAlgebraAndHash },
  { id := "multidimensional-cartesian-indices-and-regions", juliaFile := "base/multidimensional.jl",
    juliaFns := ["CartesianIndices", "_convert2ind", "show(::IO, ::CartesianIndices)", "_xform_index", "show(::IO, ::MIME\"text/plain\", ::CartesianIndices)", "(:)(::CartesianIndex, ::CartesianIndex)", "(:)(::CartesianIndex, ::CartesianIndex, ::CartesianIndex)", "promote_rule(::Type{CartesianIndices{N,R1}}, ::Type{CartesianIndices{N,R2}})", "convert(::Type{Tuple{}}, ::CartesianIndices{0})", "convert(::Type{NTuple{N,R}}, ::CartesianIndices{N})", "convert(::Type{NTuple{N,AbstractUnitRange{Int}}}, ::CartesianIndices{N})", "convert(::Type{NTuple{N,UnitRange{Int}}}, ::CartesianIndices{N})", "convert(::Type{NTuple{N,UnitRange}}, ::CartesianIndices{N})", "convert(::Type{Tuple{Vararg{AbstractUnitRange{Int}}}}, ::CartesianIndices{N})", "convert(::Type{Tuple{Vararg{AbstractUnitRange}}}, ::CartesianIndices)", "convert(::Type{Tuple{Vararg{UnitRange{Int}}}}, ::CartesianIndices{N})", "convert(::Type{Tuple{Vararg{UnitRange}}}, ::CartesianIndices)", "convert(::Type{CartesianIndices{N,R}}, ::CartesianIndices{N})", "==(::CartesianIndices, ::CartesianIndices)", "axes(::CartesianIndices)", "has_offset_axes(::CartesianIndices)", "getindex(::CartesianIndices{0})", "getindex(::CartesianIndices, ::Vararg{OrdinalRange{Int,Int}})", "getindex(::CartesianIndices, ::CartesianIndices)", "getindex(::CartesianIndices{0}, ::CartesianIndices{0})", "view(::CartesianIndices, ::Vararg{OrdinalRange{Int,Int}})", "view(::CartesianIndices, ::CartesianIndices)", "eachindex(::IndexCartesian, ::AbstractArray)", "size(::CartesianIndices)", "step(::CartesianIndices)", "to_indices(::Any, ::Tuple, ::Tuple{CartesianIndices, Vararg})", "to_indices(::Any, ::Tuple, ::Tuple{CartesianIndices{0}, Vararg})", "in(::CartesianIndex, ::CartesianIndices)", "copy(::CartesianIndices)", "intersect(::CartesianIndices, ::CartesianIndices)", "issubset(::CartesianIndices, ::CartesianIndices)"],
    statement := "CartesianIndices constructors and _convert2ind normalize integer, Bool, and range bounds; colon, range getindex, view, and intersect build elementwise ranges when ranks match and throw ArgumentError when tuple dimensions differ; issubset is reflexive and short-circuits on empty regions; and to_indices splits axes across N-dimensional and 0-dimensional CartesianIndices.",
    source := "CartesianIndices docstrings; base/multidimensional.jl:298-508,644-646", status := .proven,
    prop := ``CartesianIndicesAndRegions, thm := some ``cartesianIndicesAndRegions },
  { id := "multidimensional-cartesian-iteration-and-split", juliaFile := "base/multidimensional.jl",
    juliaFns := ["nextind(::AbstractArray, ::CartesianIndex)", "prevind(::AbstractArray, ::CartesianIndex)", "inc", "iterate(::CartesianIndices{0})", "simd_outer_range", "simd_inner_length", "simd_index", "split", "_split1", "_splitrest", "_reverse", "dec", "iterate(::Reverse{<:CartesianIndices{0}})", "eltype(::Type{PartitionIterator{T}})", "Iterators.IteratorEltype(::Type{<:PartitionIterator{T}})", "iterate(::CartesianPartition)", "splitdim1", "skip_len_I"],
    statement := "Base.split on tuples, CartesianIndex, and CartesianIndices partitions into take N and drop N; 0D CartesianIndices and its Reverse yield () once then stop; inc/dec and nextind/prevind advance and invert coordinates along CartesianIndices; and PartitionIterator and SIMD helpers obey their exact element-type, step, and boundary skip/length formulas.",
    source := "base/multidimensional.jl:159-169,459-715", status := .proven,
    prop := ``CartesianIterationAndSplit, thm := some ``cartesianIterationAndSplit },
  { id := "multidimensional-index-traits-and-queries", juliaFile := "base/multidimensional.jl",
    juliaFns := ["in(::CartesianIndex, ::StepRangeLen)", "isassigned(::CartesianIndices, ::Vararg{Int})", "eachindex(::IndexCartesian, ::AbstractArray, ::AbstractArray...)", "LinearIndices(::CartesianIndices)", "collect(::CartesianIndices)", "index_ndims", "index_dimsum", "index_lengths", "index_shape", "index_sizes", "_check_boolean_axes"],
    statement := "Cartesian StepRangeLen membership handles empty, zero-step, and nonzero-step ranges; CartesianIndices isassigned agrees with in; multi-array eachindex checks axis equality; LinearIndices checks unit steps; collect populates elements in order; index-trait helpers obey their recursive rank/length/shape equations for arbitrary tail callbacks; and _check_boolean_axes checks prefix axis agreement and trailing 1:1 axes.",
    source := "base/multidimensional.jl:193-920", status := .proven,
    prop := ``IndexTraitsAndQueries, thm := some ``indexTraitsAndQueries },
  { id := "multidimensional-logical-and-indexing", juliaFile := "base/multidimensional.jl",
    juliaFns := ["atomic_mem_index", "checkbounds(::Type{Bool}, ::AbstractArray, ::Union{CartesianIndex, AbstractArray{<:CartesianIndex}}...)", "checkbounds_indices", "checkindex(::Type{Bool}, ::Tuple, ::CartesianIndex)", "checkindex(::Type{Bool}, ::Tuple, ::Union{CartesianIndices, StepRangeLen{<:CartesianIndex}})", "getindex(::Array, ::Union{Int, CartesianIndex}, ::Union{Int, CartesianIndex}...)", "setindex!(::Array, ::Any, ::Union{Int, CartesianIndex}, ::Union{Int, CartesianIndex}...)", "checkindex(::Type{Bool}, ::Tuple, ::AbstractArray{<:CartesianIndex})", "LogicalIndex", "size(::LogicalIndex)", "collect(::LogicalIndex)", "show(::IO, ::LogicalIndex)", "print_array(::IO, ::LogicalIndex)", "iterate(::LogicalIndex)", "checkbounds(::Type{Bool}, ::AbstractArray, ::LogicalIndex)", "checkindex(::Type{Bool}, ::AbstractUnitRange, ::LogicalIndex)", "checkindex(::Type{Bool}, ::Tuple, ::LogicalIndex)", "checkbounds(::Type{Bool}, ::AbstractArray, ::AbstractArray{Bool})", "checkbounds(::Type{Bool}, ::AbstractVector, ::AbstractVector{Bool})", "checkindex(::Type{Bool}, ::AbstractUnitRange, ::AbstractVector{Bool})", "checkindex(::Type{Bool}, ::AbstractUnitRange, ::AbstractRange{Bool})", "checkindex(::Type{Bool}, ::Tuple, ::AbstractArray{Bool})", "ensure_indexable", "_drop_zerodim", "to_indices", "_maybe_linear_logical_index", "uncolon", "_prechecked_iterate", "getindex(::Number, ::CartesianIndex{0})", "getindex(::Tuple, ::CartesianIndex{1})", "_getindex", "_maybe_reshape", "__maybe_reshape", "_unsafe_getindex", "_unsafe_getindex!", "throw_checksize_error", "_setindex!", "_generate_unsafe_setindex!_body", "_unsafe_setindex!"],
    statement := "Atomic memory indexing dispatches linear vs subscripted coordinates; Cartesian and boolean-mask checkbounds/checkindex split axis tuples and check endpoints or mask axes; LogicalIndex collects iterator elements and BitArray iteration scans chunks using trailing zeros and low-bit clearing; to_indices and uncolon expand Cartesian, mask, and colon indices; _prechecked_iterate steps unit, linear, Cartesian, and 2D-reshaped cursors; and _getindex/_setindex! check destination sizes and write elements in column-major order.",
    source := "base/multidimensional.jl:735-1077", status := .proven,
    prop := ``LogicalAndMultidimIndexing, thm := some ``logicalAndMultidimIndexing },
  { id := "multidimensional-bitarray-and-slice-ops", juliaFile := "base/multidimensional.jl",
    juliaFns := ["_unsafe_getindex!(::BitArray, ::BitArray, ::AbstractUnitRange{Int})", "_unsafe_getindex!(::BitArray, ::BitArray, ::AbstractUnitRange{Int}, ::Vararg{Union{Int,AbstractUnitRange{Int}}})", "_unsafe_getindex!(::BitArray, ::BitArray, ::Vararg{Union{Int,AbstractVector{Int}}})", "copy_to_bitarray_chunks!", "try_bool_conversion", "unchecked_bool_convert", "setindex!(::BitArray, ::AbstractArray, ::Colon)", "setindex!(::BitArray, ::AbstractArray, ::AbstractUnitRange{Int}, ::Vararg{Union{Int,AbstractUnitRange{Int},Colon}})", "_unsafe_setindex!(::BitArray, ::AbstractArray, ::AbstractUnitRange{Int}, ::Vararg{Union{Int,AbstractUnitRange{Int}}})", "setindex!(::BitArray, ::AbstractArray, ::Union{AbstractArray,Colon}, ::Vararg{Union{Real,AbstractArray,Colon}})", "fill!(::SubArray{Bool,<:Any,BitArray}, ::Any)", "_unsafe_fill_indices!", "isassigned(::BitArray, ::Int, ::Vararg{Int})", "isassigned(::AbstractArray, ::CartesianIndex)", "isassigned(::AbstractArray, ::Union{Integer,CartesianIndex}...)", "isassigned(::AbstractArray, ::Integer...)", "checkdims_perm(::AbstractArray, ::AbstractArray, ::Tuple)", "unique(::AbstractArray; dims)", "_unique_dims", "showarg(::IO, ::Base.Pairs, ::Bool)", "sortslices", "_sortslices!", "getindex(::Ref, ::CartesianIndex{0})", "setindex!(::Ref, ::Any, ::CartesianIndex{0})"],
    statement := "BitArray contiguous, range, and general gather/scatter/fill copy and fill chunks at computed bit offsets while preserving empty targets; copy_to_bitarray_chunks! validates 0/1 source values via try_bool_conversion; BitArray and generic isassigned check per-dimension bounds and suppress bounds/undef errors; _unique_dims deduplicates slices along valid dimensions and copies out-of-range dimensions; and sortslices uses row permutation on 2D matrices with dims=1 and slice broadcast assignment otherwise.",
    source := "base/multidimensional.jl:1374-1993", status := .proven,
    prop := ``BitArrayAndSliceOps, thm := some ``bitArrayAndSliceOps }
]

end JuliaLean.Proofs.base.multidimensional

/-! Method coverage inventory for the pinned Julia source.

Julia line | Lean definition | Property ids or coverage status
--- | --- | ---
77 | `cartesianInner` | multidimensional-cartesian-algebra-and-hash
80 | `cartesianTuple` | multidimensional-cartesian-algebra-and-hash
81 | `cartesianVarargs` | multidimensional-cartesian-algebra-and-hash
82 | `cartesianSizedVarargs` | multidimensional-cartesian-algebra-and-hash
84 | `cartesianPad` | multidimensional-cartesian-algebra-and-hash
85 | `cartesianSizedIntegers` | multidimensional-cartesian-algebra-and-hash
86 | `cartesianDefault` | multidimensional-cartesian-algebra-and-hash
88 | `cartesianIdentity` | multidimensional-cartesian-algebra-and-hash
89 | `cartesianMixed` | multidimensional-cartesian-algebra-and-hash
90 | `flattenEmpty` | multidimensional-cartesian-algebra-and-hash
91 | `flattenSingle` | multidimensional-cartesian-algebra-and-hash
92 | `flattenCons` | multidimensional-cartesian-algebra-and-hash
93 | `cartesianMixedTuple` | multidimensional-cartesian-algebra-and-hash
94 | `showCartesian` | multidimensional-cartesian-algebra-and-hash
101 | `cartesianLength` | multidimensional-cartesian-algebra-and-hash
102 | `cartesianTypeLength` | multidimensional-cartesian-algebra-and-hash
105 | `cartesianGetindex` | multidimensional-cartesian-algebra-and-hash
106 | `cartesianFirstindex` | multidimensional-cartesian-algebra-and-hash
107 | `cartesianLastindex` | multidimensional-cartesian-algebra-and-hash
108 | `arrayGetCartesian` | multidimensional-cartesian-algebra-and-hash
109 | `cartesianEltype` | multidimensional-cartesian-algebra-and-hash
112 | `cartesianToTuple` | multidimensional-cartesian-algebra-and-hash
114 | `cartesianSetindex` | multidimensional-cartesian-algebra-and-hash
117 | `cartesianEq` | multidimensional-cartesian-algebra-and-hash
120 | `cartesianZeroValue` | multidimensional-cartesian-algebra-and-hash
121 | `cartesianZeroType` | multidimensional-cartesian-algebra-and-hash
122 | `cartesianOneValue` | multidimensional-cartesian-algebra-and-hash
123 | `cartesianOneType` | multidimensional-cartesian-algebra-and-hash
126 | `cartesianPos` | multidimensional-cartesian-algebra-and-hash
127 | `cartesianNeg` | multidimensional-cartesian-neg-involutive
129 | `cartesianAdd` | multidimensional-cartesian-add-commutes, multidimensional-cartesian-algebra-and-hash
131 | `cartesianSub` | multidim-circshift-formula, multidim-circcopy-nonempty, multidimensional-cartesian-algebra-and-hash
133 | `cartesianMin` | multidimensional-cartesian-minmax-commute
135 | `cartesianMax` | multidimensional-cartesian-minmax-commute
138 | `cartesianScaleLeft` | multidimensional-cartesian-algebra-and-hash
139 | `cartesianScaleRight` | multidimensional-cartesian-algebra-and-hash
142 | `cartesianIsless` | multidim-cartesian-isless
145 | `cartesianConvertNumber` | multidimensional-cartesian-algebra-and-hash
146 | `cartesianConvertTuple` | multidimensional-cartesian-algebra-and-hash
150 | `cartesianHash` | multidimensional-cartesian-algebra-and-hash
159 | `nextindCartesian` | multidimensional-cartesian-iteration-and-split
165 | `previndCartesian` | multidimensional-cartesian-iteration-and-split
172 | `ind2subCartesian` | multidimensional-cartesian-algebra-and-hash
176 | `cartesianIterateDisabled` | multidimensional-cartesian-algebra-and-hash
180 | `cartesianRangeLengthDisabled` | multidimensional-cartesian-algebra-and-hash
187 | `showCartesianStepRange` | multidimensional-cartesian-algebra-and-hash
192 | `cartesianRangeContainsWrongRank` | multidimensional-cartesian-algebra-and-hash
193 | `cartesianRangeContains` | multidimensional-index-traits-and-queries
298 | `cartesianIndicesEmpty` | multidimensional-cartesian-indices-and-regions
299 | `cartesianIndicesRanges` | multidimensional-cartesian-indices-and-regions
304 | `cartesianIndicesIndex` | multidimensional-cartesian-indices-and-regions
305 | `cartesianIndicesMixed` | multidimensional-cartesian-indices-and-regions
308 | `cartesianIndicesArray` | multidimensional-cartesian-indices-and-regions
310 | `convert2indBool` | multidimensional-cartesian-indices-and-regions
311 | `convert2indInteger` | multidimensional-cartesian-indices-and-regions
312 | `convert2indUnitRange` | multidimensional-cartesian-indices-and-regions
313 | `convert2indOrdinal` | multidimensional-cartesian-indices-and-regions
315 | `showCartesianIndices` | multidimensional-cartesian-indices-and-regions
320 | `xformIndex` | multidimensional-cartesian-indices-and-regions
321 | `xformOneTo` | multidimensional-cartesian-indices-and-regions
322 | `showCartesianIndicesPlain` | multidimensional-cartesian-indices-and-regions
350 | `cartesianColon` | multidimensional-cartesian-indices-and-regions
352 | `cartesianStepColon` | multidimensional-cartesian-indices-and-regions
355 | `cartesianIndicesPromote` | multidimensional-cartesian-indices-and-regions
358 | `cartesianIndicesConvertEmpty` | multidimensional-cartesian-indices-and-regions
360 | `cartesianIndicesConvertRanges` | multidimensional-cartesian-indices-and-regions
363 | `cartesianIndicesConvertAbstractUnit` | multidimensional-cartesian-indices-and-regions
365 | `cartesianIndicesConvertUnitInt` | multidimensional-cartesian-indices-and-regions
367 | `cartesianIndicesConvertUnit` | multidimensional-cartesian-indices-and-regions
369 | `cartesianIndicesConvertVarargAbstractUnitInt` | multidimensional-cartesian-indices-and-regions
371 | `cartesianIndicesConvertVarargAbstractUnit` | multidimensional-cartesian-indices-and-regions
373 | `cartesianIndicesConvertVarargUnitInt` | multidimensional-cartesian-indices-and-regions
375 | `cartesianIndicesConvertVarargUnit` | multidimensional-cartesian-indices-and-regions
378 | `cartesianIndicesConvert` | multidimensional-cartesian-indices-and-regions
382 | `cartesianIndicesEq` | multidim-cartesianindices-empty-eq, multidimensional-cartesian-indices-and-regions
384 | `cartesianIndicesEqWrongRank` | multidim-cartesianindices-empty-eq, multidimensional-cartesian-indices-and-regions
387 | `cartesianIndicesAxes` | multidimensional-cartesian-indices-and-regions
388 | `cartesianIndicesHasOffset` | multidimensional-cartesian-indices-and-regions
389 | `cartesianIndicesIsassigned` | multidimensional-index-traits-and-queries
397 | `cartesianIndicesGetindexZero` | multidimensional-cartesian-indices-and-regions
400 | `cartesianIndicesGetindex` | multidim-circshift-formula, multidim-circcopy-nonempty
413 | `cartesianIndicesGetindexRanges` | multidimensional-cartesian-indices-and-regions
421 | `cartesianIndicesGetindexRegion` | multidimensional-cartesian-indices-and-regions
425 | `cartesianIndicesGetindexZeroRegion` | multidimensional-cartesian-indices-and-regions
428 | `cartesianIndicesViewRanges` | multidimensional-cartesian-indices-and-regions
431 | `cartesianIndicesViewRegion` | multidimensional-cartesian-indices-and-regions
435 | `eachindexCartesian` | multidimensional-cartesian-indices-and-regions
437 | `eachindexCartesianMany` | multidimensional-index-traits-and-queries
445 | `cartesianIterateFirst` | multidim-cartesian-iterate
452 | `cartesianIterateNext` | multidim-cartesian-iterate
459 | `cartesianInc` | multidimensional-cartesian-iteration-and-split
468 | `incEmpty` | multidim-cartesian-iterate
469 | `incSingle` | multidim-cartesian-iterate
475 | `incCons` | multidim-cartesian-iterate
486 | `cartesianIterateZero` | multidimensional-cartesian-iteration-and-split
488 | `cartesianIndicesSize` | multidimensional-cartesian-indices-and-regions
491 | `cartesianIndicesStep` | multidimensional-cartesian-indices-and-regions
493 | `cartesianIndicesFirst` | multidim-cartesian-iterate, multidim-cartesian-reverse-iterate, multidim-circshift-formula, multidim-circcopy-nonempty
494 | `cartesianIndicesLast` | multidim-cartesian-iterate, multidim-cartesian-reverse-iterate, multidim-circshift-formula, multidim-circcopy-nonempty
497 | `toIndicesCartesianRegion` | multidimensional-cartesian-indices-and-regions
502 | `toIndicesCartesianRegionZero` | multidimensional-cartesian-indices-and-regions
505 | `cartesianIndicesContainsWrongRank` | multidimensional-cartesian-indices-and-regions
506 | `cartesianIndicesContains` | multidim-circshift-formula, multidim-circcopy-nonempty, multidimensional-index-traits-and-queries
508 | `cartesianIndicesCopy` | multidimensional-cartesian-indices-and-regions
510 | `simdOuterZero` | multidimensional-cartesian-iteration-and-split
511 | `simdOuter` | multidimensional-cartesian-iteration-and-split
515 | `simdInnerZero` | multidimensional-cartesian-iteration-and-split
516 | `simdInner` | multidimensional-cartesian-iteration-and-split
518 | `simdIndexZero` | multidimensional-cartesian-iteration-and-split
519 | `simdIndex` | multidimensional-cartesian-iteration-and-split
523 | `splitTuple` | multidimensional-cartesian-iteration-and-split
527 | `split1Cons` | multidimensional-cartesian-iteration-and-split
528 | `splitrestCons` | multidimensional-cartesian-iteration-and-split
530 | `split1EmptyEmpty` | multidimensional-cartesian-iteration-and-split
531 | `split1EmptyRef` | multidimensional-cartesian-iteration-and-split
532 | `split1TupleEmpty` | multidimensional-cartesian-iteration-and-split
533 | `splitrestEmptyEmpty` | multidimensional-cartesian-iteration-and-split
534 | `splitrestTupleEmpty` | multidimensional-cartesian-iteration-and-split
535 | `splitrestEmptyRef` | multidimensional-cartesian-iteration-and-split
537 | `splitCartesian` | multidimensional-cartesian-iteration-and-split
541 | `splitCartesianIndices` | multidimensional-cartesian-iteration-and-split
547 | `reverseCartesianAll` | multidim-reverse-dims-check
551 | `reverseCartesianDimension` | multidim-reverse-dims-check
558 | `reverseCartesianDimensions` | multidim-reverse-dims-check
569 | `reverseCartesianOneDimension` | multidim-reverse-dims-check
572 | `reverseIterateFirst` | multidim-cartesian-reverse-iterate
579 | `reverseIterateNext` | multidim-cartesian-reverse-iterate
586 | `cartesianDec` | multidimensional-cartesian-iteration-and-split
592 | `decEmpty` | multidim-cartesian-reverse-iterate
593 | `decSingle` | multidim-cartesian-reverse-iterate
599 | `decCons` | multidim-cartesian-reverse-iterate
610 | `reverseIterateZero` | multidimensional-cartesian-iteration-and-split
612 | `linearIndicesUnit` | multidimensional-index-traits-and-queries
615 | `linearIndices` | multidimensional-index-traits-and-queries
631 | `collectCartesianUnit` | multidimensional-index-traits-and-queries
634 | `collectCartesian` | multidimensional-index-traits-and-queries
644 | `intersectCartesian` | multidimensional-cartesian-indices-and-regions
646 | `subsetCartesian` | multidimensional-cartesian-indices-and-regions
651 | `partitionEltypeLinear` | multidimensional-cartesian-iteration-and-split
652 | `partitionEltypeCartesian` | multidimensional-cartesian-iteration-and-split
653 | `partitionIteratorEltype` | multidimensional-cartesian-iteration-and-split
655 | `partitionEltypeOneTo` | multidimensional-cartesian-iteration-and-split
656 | `partitionEltypeRange` | multidimensional-cartesian-iteration-and-split
657 | `partitionRangeIteratorEltype` | multidimensional-cartesian-iteration-and-split
659 | `partitionIterateFirst` | multidimensional-cartesian-iteration-and-split
664 | `partitionIterateNext` | multidimensional-cartesian-iteration-and-split
670 | `partitionSimdOuter` | multidimensional-cartesian-iteration-and-split
677 | `partitionSplitdim1` | multidimensional-cartesian-iteration-and-split
688 | `partitionSkipLength` | multidimensional-cartesian-iteration-and-split
695 | `partitionSimdOuter2` | multidimensional-cartesian-iteration-and-split
706 | `partitionSkipLength2` | multidimensional-cartesian-iteration-and-split
713 | `partitionSimdInner` | multidimensional-cartesian-iteration-and-split
714 | `partitionSimdIndex` | multidimensional-cartesian-iteration-and-split
735 | `atomicMixed` | multidimensional-logical-and-indexing
739 | `atomicCartesian` | multidimensional-logical-and-indexing
743 | `atomicIntegers` | multidimensional-logical-and-indexing
757 | `checkboundsCartesian` | multidimensional-logical-and-indexing
760 | `checkboundsIndicesCartesian` | multidimensional-logical-and-indexing
764 | `checkindexCartesian` | multidimensional-logical-and-indexing
766 | `checkindexCartesianRange` | multidimensional-logical-and-indexing
772 | `arrayGetMixed` | multidimensional-logical-and-indexing
774 | `arraySetMixed` | multidimensional-logical-and-indexing
779 | `checkboundsCartesianArray` | multidimensional-logical-and-indexing
782 | `checkboundsIndicesCartesianArray` | multidimensional-logical-and-indexing
786 | `checkindexCartesianIndices` | multidimensional-logical-and-indexing
792 | `indexNdimsScalar` | multidimensional-index-traits-and-queries
793 | `indexNdimsCartesian` | multidimensional-index-traits-and-queries
796 | `indexNdimsCartesianArray` | multidimensional-index-traits-and-queries
799 | `indexNdimsEmpty` | multidimensional-index-traits-and-queries
803 | `indexDimsumScalar` | multidimensional-index-traits-and-queries
804 | `indexDimsumColon` | multidimensional-index-traits-and-queries
805 | `indexDimsumMask` | multidimensional-index-traits-and-queries
806 | `indexDimsumArray` | multidimensional-index-traits-and-queries
809 | `indexDimsumEmpty` | multidimensional-index-traits-and-queries
812 | `indexLengthsEmpty` | multidimensional-index-traits-and-queries
813 | `indexLengthsScalar` | multidimensional-index-traits-and-queries
814 | `indexLengthsArray` | multidimensional-index-traits-and-queries
818 | `indexShapeEmpty` | multidimensional-index-traits-and-queries
819 | `indexShapeScalar` | multidimensional-index-traits-and-queries
820 | `indexShapeArray` | multidimensional-index-traits-and-queries
822 | `indexSizesEmpty` | multidimensional-index-traits-and-queries
823 | `indexSizesScalar` | multidimensional-index-traits-and-queries
824 | `indexSizesArray` | multidimensional-index-traits-and-queries
837 | `logicalInner` | multidimensional-logical-and-indexing
839 | `logicalVector` | multidimensional-logical-and-indexing
840 | `logicalArray` | multidimensional-logical-and-indexing
841 | `logicalExplicitInt` | multidimensional-logical-and-indexing
842 | `logicalSize` | multidimensional-logical-and-indexing
843 | `logicalCollect` | multidimensional-logical-and-indexing
844 | `logicalShow` | multidimensional-logical-and-indexing
845 | `logicalPrintArray` | multidimensional-logical-and-indexing
851 | `logicalIterateIntFirst` | multidimensional-logical-and-indexing
855 | `logicalIterateCartesianFirst` | multidimensional-logical-and-indexing
859 | `logicalIterate` | multidimcov-multidimensional-repair-c2, multidimcov-logicalindex-mutable-mask
874 | `logicalBitIntFirst` | multidimensional-logical-and-indexing
879 | `logicalBitCartesianFirst` | multidimensional-logical-and-indexing
885 | `logicalBitIterate` | multidimensional-logical-and-indexing
900 | `checkboundsLogical` | multidimensional-logical-and-indexing
902 | `checkindexLogicalAxis` | multidimensional-logical-and-indexing
903 | `checkindexLogicalTuple` | multidimensional-logical-and-indexing
907 | `checkboundsMask` | multidimensional-logical-and-indexing
910 | `checkboundsVectorMask` | multidimensional-logical-and-indexing
912 | `checkboundsIndicesMask` | multidimensional-logical-and-indexing
916 | `checkindexVectorMask` | multidimensional-logical-and-indexing
917 | `checkindexRangeMask` | multidimensional-logical-and-indexing
918 | `checkindexMaskTuple` | multidimensional-logical-and-indexing
919 | `checkBooleanAxesCons` | multidimensional-index-traits-and-queries
920 | `checkBooleanAxesEmpty` | multidimensional-index-traits-and-queries
922 | `ensureIndexableEmpty` | multidimensional-logical-and-indexing
923 | `ensureIndexableCons` | multidimensional-logical-and-indexing
924 | `ensureIndexableLogical` | multidimensional-logical-and-indexing
928 | `toIndicesMixed` | multidimensional-logical-and-indexing
929 | `dropZeroDim` | multidimensional-logical-and-indexing
932 | `toIndicesCartesian` | multidimensional-logical-and-indexing
937 | `toIndicesCartesianArray` | multidimensional-logical-and-indexing
942 | `toIndicesMask` | multidimensional-logical-and-indexing
947 | `toIndicesSingleMask` | multidimensional-logical-and-indexing
948 | `maybeLinearLogicalDefault` | multidimensional-logical-and-indexing
949 | `maybeLinearLogicalLinear` | multidimensional-logical-and-indexing
952 | `toIndicesColon` | multidimensional-logical-and-indexing
955 | `uncolonEmpty` | multidimensional-logical-and-indexing
956 | `uncolonCons` | multidimensional-logical-and-indexing
964 | `precheckedFirst` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
965 | `precheckedNext` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
967 | `precheckedUnitFirst` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
968 | `precheckedUnitNext` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
972 | `precheckedLinearFirst` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
973 | `precheckedLinearNext` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
977 | `precheckedCartesianFirst` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
978 | `precheckedCartesianNext` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
982 | `precheckedSpecialFirst` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
983 | `precheckedSpecialNext` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
989 | `getindexScalarZero` | multidimensional-logical-and-indexing
990 | `getindexTupleCartesian` | multidimensional-logical-and-indexing
995 | `getindexAbstract` | multidimensional-logical-and-indexing
1000 | `maybeReshapeLinear` | multidimensional-logical-and-indexing
1001 | `maybeReshapeVector` | multidimensional-logical-and-indexing
1002 | `maybeReshapeCartesian` | multidimensional-logical-and-indexing
1003 | `reshapeMatchingRank` | multidimensional-logical-and-indexing
1004 | `reshapeDifferentRank` | multidimensional-logical-and-indexing
1006 | `unsafeGetindex` | multidimensional-logical-and-indexing
1015 | `generateUnsafeGetindexBody` | multidimcov-multidimensional-repair-d1
1030 | `unsafeGetindexBang` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
1035 | `unsafeGetindexBangOne` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
1039 | `unsafeGetindexBangTwo` | multidimcov-multidimensional-repair-d1, multidimensional-logical-and-indexing
1043 | `throwChecksizeError` | multidimensional-logical-and-indexing
1046 | `setindexAbstract` | multidimensional-logical-and-indexing
1053 | `generateUnsafeSetindexBody` | multidimensional-logical-and-indexing
1069 | `unsafeSetindexBang` | multidimensional-logical-and-indexing
1073 | `unsafeSetindexBangOne` | multidimensional-logical-and-indexing
1077 | `unsafeSetindexBangTwo` | multidimensional-logical-and-indexing
1081 | `diffVector` | arrayops-diff
1113 | `diffArray` | arrayops-diff, multidim-diff-size
1123 | `diffRange` | arrayops-diff
1130 | `mightaliasSubarray` | broadcastviews-overlap-conservative, broadcastviews-cartesian-alias
1153 | `parentsMatchAbstract` | broadcastviews-overlap-conservative
1154 | `parentsMatchDense` | broadcastviews-overlap-conservative
1155 | `parentsMatchStrided` | broadcastviews-overlap-conservative
1158 | `indicesOverlapEmpty` | broadcastviews-overlap-conservative
1159 | `indicesOverlapLeftEmpty` | broadcastviews-overlap-conservative
1160 | `indicesOverlapRightEmpty` | broadcastviews-overlap-conservative
1162 | `indicesOverlapRanges` | broadcastviews-overlap-conservative
1166 | `indicesOverlapUnitRanges` | broadcastviews-overlap-conservative
1170 | `indicesOverlapScalars` | broadcastviews-overlap-conservative
1172 | `indicesOverlapScalarArray` | broadcastviews-overlap-conservative, broadcastviews-cartesian-alias
1174 | `indicesOverlapArrayScalar` | broadcastviews-overlap-conservative
1177 | `indicesOverlapArrays` | broadcastviews-overlap-conservative
1188 | `indicesOverlapFallback` | broadcastviews-overlap-conservative
1190 | `copytoCartesian` | multidim-copyto-empty-size, multidim-circshift-formula, multidim-circcopy-nonempty
1246 | `circshiftEmpty` | multidim-circshift-formula
1257 | `circshift` | multidim-circshift-formula
1265 | `circshiftConvert` | multidim-circshift-formula
1284 | `circshiftCons` | multidim-circshift-formula
1297 | `circshiftBase` | multidim-circshift-formula
1337 | `circcopy` | multidim-circcopy-empty, multidim-circcopy-nonempty
1349 | `circcopyCons` | multidim-circcopy-empty, multidim-circcopy-nonempty
1364 | `circcopyBase` | multidim-circcopy-empty, multidim-circcopy-nonempty
1374 | `bitGetindexContiguous` | multidimensional-bitarray-and-slice-ops
1380 | `bitGetindexRanges` | multidimensional-bitarray-and-slice-ops
1419 | `bitGetindexGeneral` | multidimensional-bitarray-and-slice-ops
1438 | `copyToBitarrayChunks` | multidimensional-bitarray-and-slice-ops
1455 | `tryBoolConversion` | multidimensional-bitarray-and-slice-ops
1457 | `uncheckedBoolConvert` | multidimensional-bitarray-and-slice-ops
1459 | `copyToBitarrayChunksReal` | multidimensional-bitarray-and-slice-ops
1516 | `bitSetindexContiguous` | multidimensional-bitarray-and-slice-ops
1527 | `bitSetindexRanges` | multidimensional-bitarray-and-slice-ops
1533 | `bitUnsafeSetindexRanges` | multidimensional-bitarray-and-slice-ops
1568 | `bitSetindexAbstract` | multidimensional-bitarray-and-slice-ops
1574 | `bitFillContiguous` | multidimensional-bitarray-and-slice-ops
1583 | `bitFillRanges` | multidimensional-bitarray-and-slice-ops
1586 | `bitUnsafeFillIndices` | multidimensional-bitarray-and-slice-ops
1621 | `bitIsassigned` | multidimensional-bitarray-and-slice-ops
1637 | `isassignedCartesian` | multidimensional-bitarray-and-slice-ops
1638 | `isassignedMixed` | multidimensional-bitarray-and-slice-ops
1641 | `isassignedIntegers` | multidimensional-bitarray-and-slice-ops
1669 | `permutedims` | multidimcov-permutedims-offset-view
1678 | `checkdimsPermArrays` | multidimcov-permutedims-offset-view, multidimensional-bitarray-and-slice-ops
1679 | `checkdimsPerm` | multidimcov-permutedims-offset-view
1689 | `permutedimsBang` | multidimcov-permutedims-offset-view
1723 | `prehashedHash` | ranges-hash-short-equal-consistency
1764 | `unique` | multidimensional-bitarray-and-slice-ops
1766 | `uniqueDimsColon` | multidimensional-bitarray-and-slice-ops
1768 | `uniqueDims` | multidimensional-bitarray-and-slice-ops
1839 | `showargPairsInteger` | multidimensional-bitarray-and-slice-ops
1842 | `showargPairsCartesian` | multidimensional-bitarray-and-slice-ops
1846 | `showargPairsVector` | multidimensional-bitarray-and-slice-ops
1969 | `sortslices` | multidimensional-bitarray-and-slice-ops
1981 | `sortslicesBang` | multidimensional-bitarray-and-slice-ops
1992 | `refGetindexZero` | multidimensional-bitarray-and-slice-ops
1993 | `refSetindexZero` | multidimensional-bitarray-and-slice-ops
1997 | `hashFib` | ranges-hash-short-equal-consistency
2077 | `unionSplitCons` | ranges-hash-short-equal-consistency
2084 | `unionSplitEmpty` | ranges-hash-short-equal-consistency
2086 | `hashShaped` | ranges-hash-short-equal-consistency
2123 | `hashArray` | ranges-hash-short-equal-consistency
-/
