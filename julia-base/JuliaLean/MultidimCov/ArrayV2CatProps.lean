import JuliaLean.MultidimCov.ArrayV2CollectProps

/-! Contracts of `hcat`/`vcat` of vectors (master `base/array.jl:2340-2366`). -/

namespace JuliaLean.MultidimCov.ArrayV2

/-- A fully assigned vector holding `xs`. -/
def HoldsVec (a : Arr JV) (xs : List JV) : Prop :=
  IsVec a xs.length ∧ Valid a ∧ contents a = xs.map some

theorem readVec_holds {a : Arr JV} {xs : List JV} (h : HoldsVec a xs) : readVec a = .ok xs := by
  obtain ⟨hv, _, hc⟩ := h
  have hl : length a = xs.length := length_vec a _ hv
  unfold readVec
  have key : ∀ (ks : List Nat), (∀ k ∈ ks, k < xs.length) →
      (ks.map fun (k : Nat) => ((k : Int) + 1)).mapM (getL a) = .ok (ks.map fun k => xs[k]!) := by
    intro ks hks
    induction ks with
    | nil => rfl
    | cons k ks ih =>
      have hk := hks k (by simp)
      have hg : getL a ((k : Int) + 1) = .ok xs[k]! := by
        unfold getL
        rw [if_pos (by simp [inBounds, hl]; omega)]
        have hk' : k < (contents a).length := by simp [contents_length, hl]; omega
        rw [← getElem_contents a k hk']
        simp [hc, getElem!_pos xs k hk]
      simp only [List.map_cons, List.mapM_cons, hg, bind_ok, ih (fun j hj => hks j (by simp [hj])), pure_ok]
  rw [hl, key _ (fun k hk => by simpa using hk)]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp at h1
  simp [getElem!_pos xs i h1, List.getElem?_eq_getElem h1]

theorem mapM_readVec : ∀ (vs : List (Arr JV)) (cols : List (List JV)), vs.length = cols.length →
    (∀ p ∈ vs.zip cols, HoldsVec p.1 p.2) → vs.mapM readVec = .ok cols
  | [], [], _, _ => rfl
  | v :: vs, c :: cs, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.mapM_cons, readVec_holds (h (v, c) (by simp)), bind_ok,
      mapM_readVec vs cs hl (fun p hp => h p (by simp [hp])), pure_ok]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- `hcat(V::Vector{T}...)` (docstring of `hcat`, base/abstractarray.jl: "Concatenate arrays
or numbers horizontally. Equivalent to `cat(A...; dims=2)`"): for vectors of one element
type `T` and equal length `h`, an `h × n` matrix with element type `T` holding the vectors
as columns; unequal lengths throw `DimensionMismatch`. -/
def P2340 : Prop := ∀ (T : VT) (v1 : Arr JV) (vs : List (Arr JV)) (cols : List (List JV)),
    (v1 :: vs).length = cols.length → (∀ p ∈ (v1 :: vs).zip cols, HoldsVec p.1 p.2) →
    (∀ c ∈ cols, ∀ x ∈ c, isaV x T = true) → cols.flatten.length < 2 ^ 58 →
    ((∀ c ∈ cols, c.length = length v1) →
      ∃ d, m2340 T v1 vs = .ok d ∧ d.et = T ∧ d.a.dims = [length v1, ((vs.length + 1 : Nat) : Int)] ∧
        contents d.a = cols.flatten.map some) ∧
    ((∃ v ∈ vs, length v ≠ length v1) → m2340 T v1 vs = .error .dimensionMismatch)

/-- A one-element vector. -/
def vec1 (x : JV) : Arr JV := ⟨⟨1, fun k => if k = 1 then some x else none⟩, 1, [1]⟩

theorem vec1_holds (x : JV) : HoldsVec (vec1 x) [x] := by
  refine ⟨rfl, by simp [Valid, vec1, length], ?_⟩
  simp [contents, vec1, length, Arr.at]

/-- `hcat(Any[1], Any[2])` is a `Matrix{Int}`: the comprehension takes its element type
from the values. -/
theorem hcat_any_narrows :
    ∃ d, m2340 .any (vec1 (.int 1)) [vec1 (.int 2)] = .ok d ∧ d.et = .int := by
  let it : Iter := ⟨[.int 1, .int 2], .shape [1, 2], none, .any, none⟩
  have hw : WFIter it := by
    refine ⟨by simp [it], by simp [it], by simp [it, subT], by simp [it], by simp [it]⟩
  obtain ⟨d, e, het, _⟩ := p833 it hw
  have hm : m2340 .any (vec1 (.int 1)) [vec1 (.int 2)] = m833 it := by
    unfold m2340
    have hr := mapM_readVec [vec1 (.int 1), vec1 (.int 2)] [[.int 1], [.int 2]] rfl
      (by simp [vec1_holds])
    simp only [vec1, length, List.foldr] at hr ⊢
    simp only [List.any_cons, List.any_nil, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, if_false]
    rw [hr, bind_ok]
    rfl
  exact ⟨d, hm ▸ e, by rw [het]; rfl⟩

theorem p2340_refuted : ¬ P2340 := by
  intro h
  obtain ⟨d, e, het⟩ := hcat_any_narrows
  obtain ⟨d', e', het', _⟩ := (h .any (vec1 (.int 1)) [vec1 (.int 2)] [[.int 1], [.int 2]] rfl
    (by simp [vec1_holds]) (by simp [isaV, subT]) (by simp)).1 (by simp [vec1, length])
  rw [e] at e'; cases e'
  rw [het] at het'; cases het'

/-! ### `vcat(arrays::Vector{T}...)` -/

/-- The destination during the copy loop: slots before `pre` are copied, the rest unset. -/
def CopyInv (arr : Arr JV) (N : Int) (pre : List (Option JV)) : Prop :=
  Valid arr ∧ arr.dims = [N] ∧ N ≤ 2 ^ 58 ∧ ∀ k : Nat, (k : Int) < N → arr.at ((k : Int) + 1) = (pre[k]?).getD none

theorem vcatCopy_spec : ∀ (as : List (Arr JV)) (arr : Arr JV) (N : Int) (pre : List (Option JV)),
    CopyInv arr N pre → (∀ a ∈ as, Valid a ∧ ∃ n, IsVec a n) →
    pre.length + (as.map fun a => (contents a).length).sum = N →
    ∃ arr', vcatCopy arr (pre.length + 1) as = .ok arr' ∧ CopyInv arr' N (pre ++ (as.map contents).flatten)
  | [], arr, N, pre, h, _, _ => ⟨arr, rfl, by simpa using h⟩
  | a :: as, arr, N, pre, h, ha, hl => by
    obtain ⟨⟨a1, a2, a3⟩, n, hn⟩ := ha a (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hla : (contents a).length = (length a).toNat := contents_length a
    simp only [List.map_cons, List.sum_cons] at hl
    have hN : length arr = N := length_vec arr N h2
    have hA : length a = ((contents a).length : Int) := by rw [hla]; omega
    have hrest : 0 ≤ (((as.map fun a => (contents a).length).sum : Nat) : Int) := by omega
    push_cast at hl
    have hpa : (pre.length : Int) + length a ≤ N := by omega
    obtain ⟨arr1, e1, hd1, ho1, hm1, hp1⟩ := p276 arr a (pre.length + 1) 1 (length a) h1
      ⟨a1, a2, a3⟩ a2 (by omega) (by omega) (Int.le_refl 1) (by omega) (by omega) (by omega)
    have hl1 : length arr1 = length arr := by simp [length, hd1]
    have hinv : CopyInv arr1 N (pre ++ contents a) := by
      refine ⟨⟨by rw [ho1]; exact h1.1, by rw [hl1]; exact h1.2.1, by rw [hl1, ho1, hm1]; exact h1.2.2⟩,
        by rw [hd1, h2], h3, fun k hk => ?_⟩
      rw [hp1 _ (by omega) (by omega)]
      by_cases hk2 : (pre.length : Int) + 1 ≤ (k : Int) + 1 ∧ (k : Int) + 1 < pre.length + 1 + length a
      · rw [if_pos hk2]
        have hj : k - pre.length < (contents a).length := by omega
        rw [List.getElem?_append_right (by omega), List.getElem?_eq_getElem hj, Option.getD_some,
          getElem_contents a _ hj]
        congr 1; omega
      · rw [if_neg hk2, h4 k hk]
        by_cases hk3 : k < pre.length
        · rw [List.getElem?_append_left hk3]
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    obtain ⟨arr', e', h'⟩ := vcatCopy_spec as arr1 N (pre ++ contents a) hinv (fun b hb => ha b (by simp [hb]))
      (by rw [List.length_append]; push_cast; omega)
    refine ⟨arr', ?_, by simpa using h'⟩
    unfold vcatCopy
    rw [if_neg (by omega)]
    rw [e1, bind_ok]
    have hidx : ((pre ++ contents a).length : Int) + 1 = pre.length + 1 + length a := by
      rw [List.length_append]; push_cast; omega
    rw [← hidx]; exact e'

theorem sum_length_nonneg : ∀ (as : List (Arr JV)), (∀ a ∈ as, Valid a) → 0 ≤ (as.map fun a => length a).sum
  | [], _ => by simp
  | a :: as, h => by
    simp only [List.map_cons, List.sum_cons]
    have := (h a (by simp)).2.1
    have := sum_length_nonneg as (fun b hb => h b (by simp [hb]))
    omega

theorem foldl_wrap_sum : ∀ (as : List (Arr JV)) (n : Int), 0 ≤ n → (∀ a ∈ as, Valid a) →
    n + (as.map fun a => length a).sum ≤ 2 ^ 58 →
    as.foldl (fun n a => wrap64 (n + length a)) n = n + (as.map fun a => length a).sum
  | [], n, _, _, _ => by simp
  | a :: as, n, h0, ha, hl => by
    have := (ha a (by simp)).2.1
    simp only [List.map_cons, List.sum_cons] at hl
    have hs : 0 ≤ (as.map fun a => length a).sum := sum_length_nonneg as (fun b hb => ha b (by simp [hb]))
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [wrap64_id (by omega) (by omega), foldl_wrap_sum as _ (by omega) (fun b hb => ha b (by simp [hb])) (by omega)]
    omega

/-- `vcat(arrays::Vector{T}...)` (docstring of `vcat`, base/abstractarray.jl: "Concatenate
arrays or numbers vertically. Equivalent to `cat(A...; dims=1)`"): a `Vector{T}` of the
total length holding the vectors' slots one after another (an `#undef` slot stays unset). -/
def P2351 : Prop := ∀ (T : VT) (arrays : List (Arr JV)), (∀ a ∈ arrays, Valid a ∧ ∃ n, IsVec a n) →
    (arrays.map fun a => length a).sum ≤ 2 ^ 58 →
    ∃ d, m2351 T arrays = .ok d ∧ d.et = T ∧ IsVec d.a (arrays.map fun a => length a).sum ∧
      contents d.a = (arrays.map contents).flatten

theorem p2351 : P2351 := by
  intro T arrays ha hl
  have hsum : (arrays.map fun a => (contents a).length).sum = (arrays.map fun a => length a).sum := by
    have : ∀ (as : List (Arr JV)), (∀ a ∈ as, Valid a ∧ ∃ n, IsVec a n) →
        ((as.map fun a => (contents a).length).sum : Int) = (as.map fun a => length a).sum := by
      intro as h
      induction as with
      | nil => simp
      | cons a as ih =>
        simp only [List.map_cons, List.sum_cons]
        have := (h a (by simp)).1.2.1
        push_cast
        rw [ih (fun b hb => h b (by simp [hb])), contents_length]; omega
    exact this arrays ha
  generalize hNdef : (arrays.map fun a => length a).sum = N at hl hsum ⊢
  have hN0 : 0 ≤ N := by rw [← hNdef]; exact sum_length_nonneg arrays (fun a h => (ha a h).1)
  have hw : arrays.foldl (fun n a => wrap64 (n + length a)) 0 = N := by
    have := foldl_wrap_sum arrays 0 (Int.le_refl 0) (fun a h => (ha a h).1) (by rw [hNdef]; omega)
    rw [this, hNdef]; omega
  obtain ⟨b, eb, hb⟩ := newArray_ok (α := JV) (dims := [N]) (by simpa using hN0) (by simp [typemaxInt]; omega)
  have hinv0 : CopyInv b N [] := by
    obtain ⟨bd, bv, bc⟩ := hb
    refine ⟨bv, bd, by omega, fun k hk => ?_⟩
    have hk' : k < (contents b).length := by simp [contents_length, length, bd]; omega
    rw [← getElem_contents b k hk']; simp [bc]
  obtain ⟨arr', e', h1, h2, h3, h4⟩ := vcatCopy_spec arrays b N [] hinv0 ha (by rw [List.length_nil]; push_cast; omega)
  have e'' : vcatCopy b 1 arrays = .ok arr' := by simpa using e'
  refine ⟨⟨T, arr'⟩, ?_, rfl, h2, ?_⟩
  · unfold m2351; rw [hw]; dsimp only; rw [eb, bind_ok, e'', bind_ok]; rfl
  · have hfl : (arrays.map contents).flatten.length = (arrays.map fun a => (contents a).length).sum := by
      rw [List.length_flatten, List.map_map]; rfl
    have hlen : ((arrays.map contents).flatten.length : Int) = N := by rw [hfl]; exact hsum
    apply contents_ext (by rw [show length arr' = N by simp [length, h2]]; omega)
    intro k hk
    rw [h4 k (by omega)]; simp [List.getElem?_eq_getElem hk]

/-! ### `hcat(A::Vector...)`, `vcat(A::Vector...)` through `cat` -/

theorem promote_step : ∀ t Q t' : VT, (subT t' Q = true ∨ (Q = .f64 ∧ t' = .int)) →
    (subT t' (promoteT t Q) = true ∨ (promoteT t Q = .f64 ∧ t' = .int)) := by
  intro t Q t'; cases t <;> cases Q <;> cases t' <;> decide

theorem promote_head : ∀ t Q : VT, subT t (promoteT t Q) = true ∨ (promoteT t Q = .f64 ∧ t = .int) := by
  intro t Q; cases t <;> cases Q <;> decide

/-- Every element type converts into `promote_eltype`: it is a subtype, or `Int` into `Float64`. -/
theorem promote_covers : ∀ (ets : List VT) (t : VT), t ∈ ets →
    subT t (promoteEltypes ets) = true ∨ (promoteEltypes ets = .f64 ∧ t = .int)
  | [], _, h => by simp at h
  | [u], t, h => by simp at h; subst h; exact Or.inl (subT_refl _)
  | u :: v :: ws, t, h => by
    simp only [List.mem_cons] at h
    show subT t (promoteT u (promoteEltypes (v :: ws))) = true ∨ (promoteT u (promoteEltypes (v :: ws)) = .f64 ∧ t = .int)
    rcases h with rfl | h
    · exact promote_head _ _
    · exact promote_step _ _ _ (promote_covers (v :: ws) t (by simpa using h))

theorem convert_covered {x : JV} {t P : VT} (hx : isaV x t = true) (h : subT t P = true ∨ (P = .f64 ∧ t = .int)) :
    ∃ y, convertV P x = .ok y := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact ⟨x, convertV_isa (subT_trans _ _ _ hx h)⟩
  · cases x with
    | int n => exact ⟨.f64 n, rfl⟩
    | f64 n => simp [isaV, typeofV, subT] at hx
    | str _ => simp [isaV, typeofV, subT] at hx

theorem convList_exists (conv : β → R α) : ∀ xs : List β, (∀ x ∈ xs, ∃ y, conv x = .ok y) →
    ∃ ys, convList conv xs = .ok ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := convList_exists conv xs (fun z hz => h z (by simp [hz]))
    exact ⟨y :: ys, by simp [convList, hy, hys]⟩

theorem mapM_readVecTA : ∀ (vs : List TA) (cols : List (List JV)), vs.length = cols.length →
    (∀ p ∈ vs.zip cols, HoldsVec p.1.a p.2) → vs.mapM (fun v => readVec v.a) = .ok cols
  | [], [], _, _ => rfl
  | v :: vs, c :: cs, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [List.mapM_cons, readVec_holds (h (v, c) (by simp)), bind_ok,
      mapM_readVecTA vs cs hl (fun p hp => h p (by simp [hp])), pure_ok]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem flatten_length_const : ∀ (cols : List (List JV)) (h : Nat), (∀ c ∈ cols, c.length = h) →
    cols.flatten.length = cols.length * h
  | [], _, _ => by simp
  | c :: cs, h, hc => by
    simp only [List.flatten_cons, List.length_append, List.length_cons, hc c (by simp),
      flatten_length_const cs h (fun d hd => hc d (by simp [hd]))]
    rw [Nat.succ_mul]; omega

/-- The hypotheses shared by the `cat` contracts: `cols[j]` is the content of the `j`th
vector, every element has that vector's element type. -/
def CatInput (v1 : TA) (vs : List TA) (cols : List (List JV)) : Prop :=
  (v1 :: vs).length = cols.length ∧ (∀ p ∈ (v1 :: vs).zip cols, HoldsVec p.1.a p.2 ∧ ∀ x ∈ p.2, isaV x p.1.et = true) ∧
    cols.flatten.length < 2 ^ 58

theorem cat_convert {v1 : TA} {vs : List TA} {cols : List (List JV)} (h : CatInput v1 vs cols) :
    ∃ ys, convList (convertV (promoteEltypes ((v1 :: vs).map TA.et))) cols.flatten = .ok ys := by
  obtain ⟨hl, hp, _⟩ := h
  apply convList_exists
  intro x hx
  obtain ⟨c, hc, hxc⟩ := List.mem_flatten.mp hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have hl' : vs.length + 1 = cols.length := by simpa using hl
  have hj' : j < (v1 :: vs).length := by simp only [List.length_cons]; omega
  have hpair : ((v1 :: vs)[j], cols[j]) ∈ (v1 :: vs).zip cols := by
    rw [List.mem_iff_getElem]; exact ⟨j, by simp; omega, by simp⟩
  have hisa := (hp _ hpair).2 x hxc
  exact convert_covered hisa (promote_covers _ _ (List.mem_map.mpr ⟨_, List.getElem_mem hj', rfl⟩))

/-- `hcat(A::Vector...) = cat(A...; dims=2)` (docstrings of `hcat`/`cat`,
base/abstractarray.jl): for vectors of equal length `h`, an `h × n` matrix whose element
type is `promote_type` of the element types, holding the vectors' elements converted to
it, column by column; unequal lengths throw `DimensionMismatch`. -/
def P2349 : Prop := ∀ (v1 : TA) (vs : List TA) (cols : List (List JV)), CatInput v1 vs cols →
    let T := promoteEltypes ((v1 :: vs).map TA.et)
    ((∀ c ∈ cols, c.length = length v1.a) →
      ∃ ys d, convList (convertV T) cols.flatten = .ok ys ∧ m2349 v1 vs = .ok d ∧ d.et = T ∧
        d.a.dims = [length v1.a, ((vs.length + 1 : Nat) : Int)] ∧ contents d.a = ys.map some) ∧
    ((∃ v ∈ vs, length v.a ≠ length v1.a) → m2349 v1 vs = .error .dimensionMismatch)

theorem p2349 : P2349 := by
  intro v1 vs cols hin T
  obtain ⟨ys, hys⟩ := cat_convert hin
  obtain ⟨hl, hp, hlen⟩ := hin
  refine ⟨fun heq => ?_, fun ⟨v, hv, hne⟩ => ?_⟩
  · have hv1 := (hp (v1, cols.headD []) (by cases cols <;> simp_all)).1
    have h0 : 0 ≤ length v1.a := hv1.2.1.2.1
    have hall : ∀ v ∈ vs, length v.a = length v1.a := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      have hj1 : j + 1 < (v1 :: vs).length := by simp; omega
      have hj2 : j + 1 < cols.length := by simp at hl; omega
      have hpair : ((v1 :: vs)[j + 1], cols[j + 1]) ∈ (v1 :: vs).zip cols := by
        rw [List.mem_iff_getElem]; exact ⟨j + 1, by simp; omega, by simp⟩
      have h1 := length_vec _ _ (hp _ hpair).1.1
      have h2 := heq _ (List.getElem_mem hj2)
      simp only [List.getElem_cons_succ] at h1
      rw [h1, h2]
    have hany : vs.any (fun v => length v.a != length v1.a) = false := by
      rw [List.any_eq_false]; intro v hv; simp [hall v hv]
    have hcols := mapM_readVecTA (v1 :: vs) cols hl (fun p hp' => (hp p hp').1)
    have hfl : (cols.flatten.length : Int) = length v1.a * ((vs.length + 1 : Nat) : Int) := by
      rw [flatten_length_const cols (length v1.a).toNat (fun c hc => by have := heq c hc; omega)]
      simp at hl; rw [← hl]; push_cast; rw [Int.toNat_of_nonneg h0, Int.mul_comm]
    obtain ⟨b, eb, hb⟩ := newArray_ok (α := JV) (dims := [length v1.a, ((vs.length + 1 : Nat) : Int)])
      (by simp; omega) (by simp [typemaxInt]; have := hfl; push_cast at this; rw [← this]; omega)
    refine ⟨ys, ⟨T, safeWrites b 1 ys⟩, hys, ?_, rfl, by rw [(safeWrites_spec ys b 1).1, hb.1], ?_⟩
    · unfold m2349 catCols; simp only []; rw [hany]; simp only [Bool.false_eq_true, if_false]
      rw [hcols, bind_ok, hys, bind_ok, eb, bind_ok]; rfl
    · apply contents_safeWrites_full
      have hyl := convList_length _ _ _ hys
      have hfb := fresh_length hb
      simp only [List.foldr_cons, List.foldr_nil, Int.mul_one] at hfb
      rw [hfb, ← hfl]; omega
  · have hany : vs.any (fun v => length v.a != length v1.a) = true := by
      rw [List.any_eq_true]; exact ⟨v, hv, by simp [hne]⟩
    unfold m2349 catCols; simp only []; rw [hany]; rfl

/-- `vcat(A::Vector...) = cat(A...; dims=1)` (docstrings of `vcat`/`cat`): a vector whose
element type is `promote_type` of the element types, holding all elements converted
to it, one vector after another. -/
def P2366 : Prop := ∀ (v1 : TA) (vs : List TA) (cols : List (List JV)), CatInput v1 vs cols →
    let T := promoteEltypes ((v1 :: vs).map TA.et)
    ∃ ys d, convList (convertV T) cols.flatten = .ok ys ∧ m2366 v1 vs = .ok d ∧ d.et = T ∧
      d.a.dims = [(cols.flatten.length : Int)] ∧ contents d.a = ys.map some

theorem p2366 : P2366 := by
  intro v1 vs cols hin T
  obtain ⟨ys, hys⟩ := cat_convert hin
  obtain ⟨hl, hp, hlen⟩ := hin
  have hcols := mapM_readVecTA (v1 :: vs) cols hl (fun p hp' => (hp p hp').1)
  have hyl := convList_length _ _ _ hys
  obtain ⟨b, eb, hb⟩ := newArray_ok (α := JV) (dims := [(ys.length : Int)]) (by simp) (by simp [typemaxInt]; omega)
  refine ⟨ys, ⟨T, safeWrites b 1 ys⟩, hys, ?_, rfl, by rw [(safeWrites_spec ys b 1).1, hb.1, hyl], ?_⟩
  · unfold m2366 catRows; simp only []; rw [hcols, bind_ok, hys, bind_ok, eb, bind_ok]; rfl
  · exact contents_safeWrites_full (by rw [fresh_length hb]; simp)

end JuliaLean.MultidimCov.ArrayV2
