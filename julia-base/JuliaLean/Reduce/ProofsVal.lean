import JuliaLean.Reduce.Props

/-!
Proofs of the `Val`-level properties: three-valued `any`/`all`, widened `sum` with
`init`, widened `cumprod`, and `accumulate` along a dimension.
-/

namespace JuliaLean.Reduce

/-! ### Wrapping arithmetic -/

theorem wrapInt_emod (t : IntTy) (x : Int) : wrapInt t x = wrapInt t (x % 2 ^ t.bits) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_emod_self (t : IntTy) (x : Int) : wrapInt t x % 2 ^ t.bits = x % 2 ^ t.bits := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_wrapInt (t : IntTy) (x : Int) : wrapInt t (wrapInt t x) = wrapInt t x :=
  wrapInt_of_inRange t _ (wrapInt_bounds t x)

theorem wrapInt_add (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a + wrapInt t b) = wrapInt t (a + b) := by
  rw [wrapInt_emod t (wrapInt t a + wrapInt t b), Int.add_emod, wrapInt_emod_self,
    wrapInt_emod_self, ← Int.add_emod, ← wrapInt_emod]

theorem wrapInt_mul (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a * wrapInt t b) = wrapInt t (a * b) := by
  rw [wrapInt_emod t (wrapInt t a * wrapInt t b), Int.mul_emod, wrapInt_emod_self,
    wrapInt_emod_self, ← Int.mul_emod, ← wrapInt_emod]

theorem rem_wrap_add {t : IntTy} (w : IntTy) (p : Int) (y : JInt t) :
    JInt.rem w (JInt.wrap w p) + JInt.rem w y = JInt.wrap w (p + y.val) :=
  Subtype.ext (by
    show wrapInt w (wrapInt w (wrapInt w p) + wrapInt w y.val) = wrapInt w (p + y.val)
    rw [wrapInt_wrapInt, wrapInt_add])

theorem rem_wrap_mul {t : IntTy} (w : IntTy) (p : Int) (y : JInt t) :
    JInt.rem w (JInt.wrap w p) * JInt.rem w y = JInt.wrap w (p * y.val) :=
  Subtype.ext (by
    show wrapInt w (wrapInt w (wrapInt w p) * wrapInt w y.val) = wrapInt w (p * y.val)
    rw [wrapInt_wrapInt, wrapInt_mul])

/-! ### `any` and `all` -/

section
variable {f : Val → Val} {x : Val}

theorem any_cons_missing (l : List Val) (hx : f x = .missing) :
    Vec.any f (x :: l) = (Vec.any f l).map fun r => if r = .bool false then .missing else r := by
  simp only [Vec.any, hx]

theorem any_cons_true (l : List Val) (hx : f x = .bool true) :
    Vec.any f (x :: l) = .ok (.bool true) := by
  simp only [Vec.any, hx]

theorem any_cons_false (l : List Val) (hx : f x = .bool false) :
    Vec.any f (x :: l) = Vec.any f l := by
  simp only [Vec.any, hx]

theorem all_cons_missing (l : List Val) (hx : f x = .missing) :
    Vec.all f (x :: l) = (Vec.all f l).map fun r => if r = .bool true then .missing else r := by
  simp only [Vec.all, hx]

theorem all_cons_false (l : List Val) (hx : f x = .bool false) :
    Vec.all f (x :: l) = .ok (.bool false) := by
  simp only [Vec.all, hx]

theorem all_cons_true (l : List Val) (hx : f x = .bool true) :
    Vec.all f (x :: l) = Vec.all f l := by
  simp only [Vec.all, hx]

end

theorem any_three (f : Val → Val) (v : List Val)
    (h : ∀ x ∈ v, f x = .missing ∨ f x = .bool true ∨ f x = .bool false) :
    Vec.any f v = .ok (if v.any (fun x => f x = .bool true) then .bool true
      else if v.any (fun x => f x = .missing) then .missing else .bool false) := by
  induction v with
  | nil => rfl
  | cons x rest ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.any_cons, List.any_cons]
    generalize rest.any (fun x => decide (f x = .bool true)) = A at ih ⊢
    generalize rest.any (fun x => decide (f x = .missing)) = B at ih ⊢
    rcases h x List.mem_cons_self with hx | hx | hx
    · rw [any_cons_missing _ hx, ih]
      cases A <;> cases B <;> simp [hx, Except.map]
    · rw [any_cons_true _ hx]
      simp [hx]
    · rw [any_cons_false _ hx, ih]
      cases A <;> cases B <;> simp [hx]

theorem all_three (f : Val → Val) (v : List Val)
    (h : ∀ x ∈ v, f x = .missing ∨ f x = .bool true ∨ f x = .bool false) :
    Vec.all f v = .ok (if v.any (fun x => f x = .bool false) then .bool false
      else if v.any (fun x => f x = .missing) then .missing else .bool true) := by
  induction v with
  | nil => rfl
  | cons x rest ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.any_cons, List.any_cons]
    generalize rest.any (fun x => decide (f x = .bool false)) = A at ih ⊢
    generalize rest.any (fun x => decide (f x = .missing)) = B at ih ⊢
    rcases h x List.mem_cons_self with hx | hx | hx
    · rw [all_cons_missing _ hx, ih]
      cases A <;> cases B <;> simp [hx, Except.map]
    · rw [all_cons_true _ hx, ih]
      cases A <;> cases B <;> simp [hx]
    · rw [all_cons_false _ hx]
      simp [hx]

theorem any_append (f : Val → Val) (v w : List Val) (h : Vec.any f v = .ok (.bool true)) :
    Vec.any f (v ++ w) = .ok (.bool true) := by
  induction v with
  | nil => simp [Vec.any] at h
  | cons x rest ih =>
    rw [List.cons_append]
    cases hx : f x with
    | missing =>
      rw [any_cons_missing _ hx] at h ⊢
      cases hr : Vec.any f rest with
      | error e => rw [hr] at h; simp [Except.map] at h
      | ok r =>
        rw [hr] at h
        have hr' : r = .bool true := by
          by_cases h2 : r = .bool false <;> simp [Except.map, h2] at h <;> exact h
        rw [ih (by rw [hr, hr'])]
        simp [Except.map]
    | bool b =>
      cases b
      · rw [any_cons_false _ hx] at h ⊢; exact ih h
      · exact any_cons_true _ hx
    | int t y => simp [Vec.any, hx] at h
    | f64 y => simp [Vec.any, hx] at h

theorem all_append (f : Val → Val) (v w : List Val) (h : Vec.all f v = .ok (.bool false)) :
    Vec.all f (v ++ w) = .ok (.bool false) := by
  induction v with
  | nil => simp [Vec.all] at h
  | cons x rest ih =>
    rw [List.cons_append]
    cases hx : f x with
    | missing =>
      rw [all_cons_missing _ hx] at h ⊢
      cases hr : Vec.all f rest with
      | error e => rw [hr] at h; simp [Except.map] at h
      | ok r =>
        rw [hr] at h
        have hr' : r = .bool false := by
          by_cases h2 : r = .bool true <;> simp [Except.map, h2] at h <;> exact h
        rw [ih (by rw [hr, hr'])]
        simp [Except.map]
    | bool b =>
      cases b
      · exact all_cons_false _ hx
      · rw [all_cons_true _ hx] at h ⊢; exact ih h
    | int t y => simp [Vec.all, hx] at h
    | f64 y => simp [Vec.all, hx] at h

theorem anyAllThreeValued_proven : AnyAllThreeValued :=
  fun f v => ⟨fun h => ⟨any_three f v h, all_three f v h⟩, any_append f v, all_append f v⟩

/-! ### `sum` with `init` -/

theorem addSum_wide {w t : IntTy} (hw : w = .i64 ∨ w = .u64) (ht : smallTy t = true)
    (a : JInt w) (y : JInt t) :
    Val.addSum (.int w a) (.int t y) = .int w (JInt.rem w a + JInt.rem w y) := by
  rcases hw with rfl | rfl <;> cases t <;> first | exact absurd ht (by decide) | rfl

theorem sum_fold {w t : IntTy} (hw : w = .i64 ∨ w = .u64) (ht : smallTy t = true) (p : Int)
    (xs : List (JInt t)) :
    (xs.map (Val.int t)).foldl Val.addSum (.int w (JInt.wrap w p)) =
      .int w (JInt.wrap w (p + (xs.map (·.val)).sum)) := by
  induction xs generalizing p with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [addSum_wide hw ht, rem_wrap_add, ih]
    simp [List.sum_cons, Int.add_assoc]

theorem lit_zero_val (s : IntTy) : (JInt.lit s 0).val = 0 := by
  cases s <;> simp [JInt.lit, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]

theorem sumInitWidened_proven : SumInitWidened := by
  intro t s v ht hs hne _
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hs' : Val.smallOrBool (.int s (JInt.lit s 0)) = true := hs
  have ht' : Val.smallOrBool (.int t x) = true := ht
  have key : ∀ w, (w = .i64 ∨ w = .u64) →
      Val.addSum (.int s (JInt.lit s 0)) (.int t x) = .int w (JInt.wrap w x.val) →
      Vec.sumInit (.int s (JInt.lit s 0)) (ints t (x :: rest)) =
        .int w (JInt.wrap w ((x :: rest).map (·.val)).sum) := by
    intro w hw h1
    show List.foldl Val.addSum _ (List.map (Val.int t) (x :: rest)) = _
    rw [List.map_cons, List.foldl_cons, h1, sum_fold hw ht]
    simp [List.sum_cons]
  by_cases hu : (Val.smallUnsigned s && Val.smallUnsigned t) = true
  · refine ⟨.u64, .inr rfl, key _ (.inr rfl) ?_⟩
    simp only [Val.addSum]
    simp only [hu, ↓reduceIte, Val.intVal, lit_zero_val, Int.zero_add]
  · refine ⟨.i64, .inl rfl, key _ (.inl rfl) ?_⟩
    simp only [Val.addSum]
    have hb : (Val.smallOrBool (.int s (JInt.lit s 0)) && Val.smallOrBool (.int t x)) = true := by
      simp [hs', ht']
    simp only [hu, hb, Bool.false_eq_true, ↓reduceIte, Val.intVal, lit_zero_val, Int.zero_add]

/-! ### `cumprod` -/

theorem accumulateVecDims_one {α β : Type} (op : β → α → β) (first copy : α → β)
    (init : Option β) (v : List α) :
    accumulateVecDims op first copy init v 1 = .ok (accumulateVec op first init v) := by
  simp [accumulateVecDims]

theorem mulProd_wide {w t : IntTy} (hw : w = .i64 ∨ w = .u64) (ht : smallTy t = true)
    (a : JInt w) (y : JInt t) :
    Val.mulProd (.int w a) (.int t y) = .int w (JInt.rem w a * JInt.rem w y) := by
  rcases hw with rfl | rfl <;> cases t <;> first | exact absurd ht (by decide) | rfl

theorem prod_loop {w t : IntTy} (hw : w = .i64 ∨ w = .u64) (ht : smallTy t = true) (p : Int)
    (xs : List (JInt t)) :
    accumulateLoop Val.mulProd (.int w (JInt.wrap w p)) (xs.map (Val.int t)) =
      (List.range xs.length).map fun k =>
        .int w (JInt.wrap w (p * ((xs.take (k + 1)).map (·.val)).prod)) := by
  induction xs generalizing p with
  | nil => simp [accumulateLoop]
  | cons y ys ih =>
    simp only [List.map_cons, accumulateLoop]
    rw [mulProd_wide hw ht, rem_wrap_mul, ih, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    simp [Function.comp_def, Int.mul_assoc]

theorem cumprod_gen {w t : IntTy} (hw : w = .i64 ∨ w = .u64) (ht : smallTy t = true)
    (hfirst : ∀ x : JInt t, Val.firstMulProd (.int t x) = .int w (JInt.wrap w x.val))
    (v : List (JInt t)) :
    accumulateVec Val.mulProd Val.firstMulProd none (v.map (Val.int t)) =
      (List.range v.length).map fun k =>
        .int w (JInt.wrap w ((v.take (k + 1)).map (·.val)).prod) := by
  cases v with
  | nil => simp [accumulateVec]
  | cons x rest =>
    simp only [List.map_cons, accumulateVec]
    rw [hfirst, prod_loop hw ht, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    simp [Function.comp_def]

theorem cumprodWidened_proven : CumprodWidened := by
  intro t v ht
  rw [accumulateVecDims_one]
  refine congrArg Except.ok ?_
  cases t <;>
    first
    | exact absurd ht (by decide)
    | exact cumprod_gen (w := .i64) (.inl rfl) ht (fun _ => rfl) v
    | exact cumprod_gen (w := .u64) (.inr rfl) ht (fun _ => rfl) v

/-! ### `accumulate` along a dimension -/

section
variable {α β : Type}

theorem accumulateLoop_length (op : β → α → β) (c : β) (l : List α) :
    (accumulateLoop op c l).length = l.length := by
  induction l generalizing c with
  | nil => rfl
  | cons x rest ih => simp [accumulateLoop, ih]

theorem accumulateVec_length (op : β → α → β) (first : α → β) (init : Option β) (l : List α) :
    (accumulateVec op first init l).length = l.length := by
  cases l with
  | nil => rfl
  | cons x rest => simp [accumulateVec, accumulateLoop_length]

/-- Entry `i` of chunk `j` of a concatenation of chunks of length `m`. -/
theorem flatten_getElem? (m i : Nat) (hi : i < m) :
    ∀ L : List (List β), (∀ l ∈ L, l.length = m) →
      ∀ j, L.flatten[m * j + i]? = (L.getD j [])[i]?
  | [], _, j => by simp
  | a :: L', hL, j => by
    have ha : a.length = m := hL a List.mem_cons_self
    have ih := flatten_getElem? m i hi L' (fun l hl => hL l (List.mem_cons_of_mem _ hl))
    rw [List.flatten_cons]
    cases j with
    | zero =>
      rw [List.getElem?_append_left (show m * 0 + i < a.length by rw [ha]; omega)]
      simp
    | succ j =>
      rw [List.getElem?_append_right (show a.length ≤ m * (j + 1) + i by
        rw [ha, Nat.mul_succ]; omega)]
      rw [show m * (j + 1) + i - a.length = m * j + i by rw [ha, Nat.mul_succ]; omega, ih j]
      simp

theorem col_mk (m n : Nat) (d : List α) (j : Nat) :
    Mat.col ⟨m, n, d⟩ j = (d.drop (m * j)).take m := rfl

theorem col_length (A : Mat α) (hA : A.WF) (j : Nat) (hj : j < A.n) :
    (A.col j).length = A.m := by
  have h1 : A.m * (j + 1) ≤ A.m * A.n := Nat.mul_le_mul_left _ hj
  rw [Nat.mul_succ] at h1
  have hA' : A.data.length = A.m * A.n := hA
  simp only [Mat.col, List.length_take, List.length_drop, hA']
  omega

theorem getD_of_lt (l : List β) (d : β) (j : Nat) (h : j < l.length) : l.getD j d = l[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem row_get [Inhabited β] (m n : Nat) (D : List β) (i j : Nat)
    (h : j < (Mat.row ⟨m, n, D⟩ i).length) :
    (Mat.row ⟨m, n, D⟩ i)[j] = D.getD (i + m * j) default := by
  simp [Mat.row]

theorem accumulateDimsScan_proven : AccumulateDimsScan := by
  intro α β _ _ op first copy init A v
  refine ⟨accumulateVecDims_one op first copy init v, fun hA => ?_, fun hA hn => ?_⟩
  · by_cases hm : A.m = 0
    · refine ⟨⟨A.m, A.n, []⟩, by simp [accumulateDims, hm], fun j _ => ?_⟩
      simp [Mat.col, hm, accumulateVec]
    · refine ⟨⟨A.m, A.n,
        ((List.range A.n).map fun j => accumulateVec op first init (A.col j)).flatten⟩,
        by simp [accumulateDims, hm], fun j hj => ?_⟩
      have hL : ∀ l ∈ (List.range A.n).map (fun j => accumulateVec op first init (A.col j)),
          l.length = A.m := by
        intro l hl
        simp only [List.mem_map, List.mem_range] at hl
        obtain ⟨k, hk, rfl⟩ := hl
        rw [accumulateVec_length, col_length A hA k hk]
      apply List.ext_getElem?
      intro i
      conv => lhs; rw [col_mk]
      by_cases hi : i < A.m
      · simp only [List.getElem?_take, hi, ↓reduceIte, List.getElem?_drop]
        rw [flatten_getElem? A.m i hi _ hL j]
        simp [hj, List.getD_eq_getElem?_getD]
      · simp only [List.getElem?_take, hi, ↓reduceIte]
        symm
        apply List.getElem?_eq_none
        rw [accumulateVec_length, col_length A hA j hj]
        omega
  · have hn' : A.n ≠ 0 := by omega
    refine ⟨⟨A.m, A.n, ((List.range A.n).map fun j =>
        ((List.range A.m).map fun i => accumulateVec op first init (A.row i)).map
          fun r => r.getD j default).flatten⟩,
      by simp [accumulateDims, hn'], fun i hi => ?_⟩
    have hL : ∀ l ∈ (List.range A.n).map (fun j =>
        ((List.range A.m).map fun i => accumulateVec op first init (A.row i)).map
          fun r => r.getD j default), l.length = A.m := by
      intro l hl
      simp only [List.mem_map, List.mem_range] at hl
      obtain ⟨k, _, rfl⟩ := hl
      simp
    have hrow : ∀ i, (A.row i).length = A.n := by intro i; simp [Mat.row]
    apply List.ext_getElem
    · rw [accumulateVec_length, hrow]; simp [Mat.row]
    · intro j h1 h2
      simp only [Mat.row, List.length_map, List.length_range] at h1
      conv => lhs; rw [row_get]
      rw [List.getD_eq_getElem?_getD, show i + A.m * j = A.m * j + i from Nat.add_comm _ _,
        flatten_getElem? A.m i hi _ hL j]
      have hacc : j < (accumulateVec op first init (A.row i)).length := by
        rw [accumulateVec_length, hrow]; exact h1
      simp [h1, hi, hacc, List.getD_eq_getElem?_getD]

end

end JuliaLean.Reduce
