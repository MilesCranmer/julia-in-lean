import JuliaLean.Proofs.base.accumulate.Contracts
import JuliaLean.Proofs.base.reduce.Values

namespace JuliaLean.Reduce

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
