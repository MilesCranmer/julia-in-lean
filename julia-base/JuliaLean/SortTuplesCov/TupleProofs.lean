import JuliaLean.SortTuplesCov.Tuple

/-! Proofs of the value-level tuple properties of `Tuple.lean`. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds argErr liftJ Idx getindex getindexColon
  getindexLogical ntupleInt splitRestVector checkLengthSplitRest restTuple indexedIterate
  fillToLength getfield_ok getfield_bounds mapM_range_ok mapM_map' mapM_slice)
open Tup

variable {α β : Type}

theorem tupleBasicsCorrect : TupleBasicsCorrect := by
  intro α t
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_⟩
  · intro d
    cases d with
    | int ty v => by_cases h : v.val = 1 <;> simp [size, idxIsOne, Idx.val, h]
    | bool b => cases b <;> rfl
  · intro i h1 h2
    obtain ⟨x, hx, hg⟩ := getfield_some (d := t) h1 h2
    refine ⟨x, hx, ?_, ?_⟩
    · simp only [iterate, if_pos (And.intro h1 h2), hg]; rfl
    · simp only [safeGetindex, if_pos h1, hx]
  · intro i h
    simp only [iterate, if_neg h]
  · intro ty i h1 h2
    rw [i64_min_eq] at h1
    rw [i64_max_eq] at h2
    have hc := convert_i64_ok i.val h1 h2
    have h1' : (JInt.lit .i64 1).val = 1 := by decide
    refine ⟨?_, ?_⟩
    · simp only [prevind, idxToInt, hc, liftJ, bind, Except.bind, pure, Except.pure]
      show Except.ok (JInt.wrap .i64 (i.val - (JInt.lit .i64 1).val)) = _
      rw [h1']
    · simp only [nextind, idxToInt, hc, liftJ, bind, Except.bind, pure, Except.pure]
      show Except.ok (JInt.wrap .i64 (i.val + (JInt.lit .i64 1).val)) = _
      rw [h1']
  · intro ty i h
    have hc : JInt.convert .i64 i.val = .error (.inexactError "Int64") := by
      unfold JInt.convert; rw [dif_neg h]; rfl
    exact ⟨by simp [prevind, idxToInt, hc, liftJ, bind, Except.bind],
      by simp [nextind, idxToInt, hc, liftJ, bind, Except.bind]⟩
  · cases t <;> rfl
  · cases t <;> rfl

/-! ### Vector indexing -/

theorem mapM_ok_mem {γ : Type} {l : List γ} {f : γ → R β} {xs : List β} (h : l.mapM f = .ok xs) :
    ∀ x ∈ l, ∃ y, f x = .ok y := by
  induction l generalizing xs with
  | nil => simp
  | cons a l ih =>
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => rw [ha] at h; cases h
    | ok y =>
      rw [ha] at h
      cases hl : l.mapM f with
      | error e => simp [hl, bind, Except.bind] at h
      | ok ys =>
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨y, ha⟩
        · exact ih hl x hx

theorem getindex_i64 (t : List α) (i : Nat) (hi : i < 2 ^ 62) :
    getindex t (.int .i64 (JInt.lit .i64 i)) = getfield t i := by
  simp only [getindex, if_true]
  rw [lit_i64_val _ (by omega) (by omega)]

theorem logical_aux (t : List α) (b : List Bool) (s : Nat) (P : List α)
    (hP : P.length = s) (hb : b.length = t.length) :
    (((List.range' s b.length).zip b).filterMap
        (fun (x : Nat × Bool) => if x.2 then some ((x.1 : Int) + 1) else none)).mapM
      (fun (i : Int) => getfield (P ++ t) i) =
      .ok ((t.zip b).filterMap fun (x : α × Bool) => if x.2 then some x.1 else none) := by
  induction t generalizing b s P with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ => simp at hb
  | cons a t ih =>
    cases b with
    | nil => simp at hb
    | cons c b =>
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons] at hb ⊢
      have ih' := ih b (s + 1) (P ++ [a]) (by simp [hP]) (by omega)
      rw [List.append_assoc, List.singleton_append] at ih'
      have hg : getfield (P ++ a :: t) ((s : Int) + 1) = .ok a := by
        rw [getfield_ok (P ++ a :: t) s (by simp [hP])]
        simp [List.getElem_append_right, hP]
      cases c with
      | true =>
        simp only [List.filterMap_cons, ↓reduceIte, List.mapM_cons, hg,
          JuliaLean.Tuples.R.bind_ok]
        rw [ih']
        rfl
      | false =>
        simp only [List.filterMap_cons, Bool.false_eq_true, ↓reduceIte]
        exact ih'

theorem tupleIndexVecCorrect : TupleIndexVecCorrect := by
  intro α t hlen
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    induction r with
    | nil => rfl
    | cons i r ih =>
      have hi := hr i (by simp)
      have hk : i - 1 < t.length := by omega
      have hg : getfield t (i : Int) = .ok t[i - 1] := by
        have := getfield_ok t (i - 1) hk
        rw [show ((i - 1 : Nat) : Int) + 1 = (i : Int) by omega] at this
        exact this
      simp only [getindexVec, List.map_cons, List.mapM_cons] at ih ⊢
      rw [getindex_i64 t i (by omega), hg, ih (fun j hj => hr j (by simp [hj]))]
      simp [List.filterMap_cons, List.getElem?_eq_getElem hk]
  · intro r hsmall ⟨i, hi, hout⟩
    cases h : getindexVec t (r.map fun (i : Nat) => Idx.int .i64 (JInt.lit .i64 (i : Int))) with
    | error e => exact ⟨e, rfl⟩
    | ok xs =>
      exfalso
      have := mapM_ok_mem h (Idx.int .i64 (JInt.lit .i64 (i : Int))) (List.mem_map.2 ⟨i, hi, rfl⟩)
      rw [getindex_i64 t i (hsmall i hi), getfield_bounds t i (by omega)] at this
      obtain ⟨y, hy⟩ := this
      cases hy
  · intro b hb
    simp only [getindexLogical, if_pos hb]
    have := logical_aux t b 0 [] rfl hb
    simpa [List.range_eq_range'] using this
  · intro b hb
    simp only [getindexLogical, if_neg hb]
  · intro f i
    simp only [getF, idxInRange, decide_eq_true_eq]

/-! ### Iteration protocol -/

theorem tupleIterProtocolCorrect : TupleIterProtocolCorrect := by
  intro α σ
  refine ⟨?_, ?_, ?_, fun _ _ => rfl, fun _ _ _ => rfl⟩
  · intro n lens
    simp only [keysMany, List.all_eq_true, beq_iff_eq]
  · intro t i h1 h2
    obtain ⟨x, hx, hg⟩ := getfield_some (d := t) (i := (i : Int)) (by omega) (by omega)
    refine ⟨x, by simpa using hx, ?_, ?_⟩
    · simp only [indexedIterate, hg]; rfl
    · simp only [indexedIterateArray, hg]; rfl
  · intro t i h
    have hb := getfield_bounds t (i : Int) (by omega)
    refine ⟨?_, ?_⟩
    · simp only [indexedIterate, hb]; rfl
    · simp only [indexedIterateArray, hb]; rfl

/-! ### `rest` -/

theorem ntupleInt_id_ok (n : Int) (h : 0 ≤ n) :
    ntupleInt (fun x => x) n = .ok ((List.range n.toNat).map fun k => k + 1) := by
  unfold ntupleInt
  by_cases h1 : 0 ≤ n ∧ n ≤ 10
  · rw [if_pos h1]
  · rw [if_neg h1, if_pos h]

theorem mapM_shift_ok (n : Nat) (f : Nat → R β) (L : List β) (hl : L.length = n)
    (h : ∀ k (hk : k < L.length), f (k + 1) = .ok L[k]) :
    ((List.range n).map fun k => k + 1).mapM f = .ok L := by
  rw [mapM_map']
  exact mapM_range_ok n _ L hl h

theorem restIdx_val (i k : Nat) (h1 : 1 ≤ i) (hik : i + k < 2 ^ 62) :
    (JInt.lit .i64 ((k + 1 : Nat) : Int) + JInt.lit .i64 i - JInt.lit .i64 1).val =
      ((i - 1 + k : Nat) : Int) + 1 := by
  have hi : (JInt.lit .i64 (i : Int)).val = i := lit_i64_val _ (by omega) (by omega)
  have h1v : (JInt.lit .i64 1).val = 1 := by decide
  have hx : (JInt.lit .i64 ((k + 1 : Nat) : Int)).val = (k : Int) + 1 :=
    lit_i64_val _ (by omega) (by omega)
  rw [sub_i64_val, add_i64_val, hx, hi, h1v] <;> (try rw [add_i64_val]) <;>
    (try rw [hx]) <;> (try rw [hi]) <;> (try rw [h1v]) <;> omega

theorem restTuple_ok (t : List α) (i : Nat) (h1 : 1 ≤ i) (h2 : i ≤ t.length + 1)
    (hl : t.length < 2 ^ 62) : restTuple t (JInt.lit .i64 i) = .ok (t.drop (i - 1)) := by
  have hn : (JInt.lit .i64 t.length - JInt.lit .i64 i + JInt.lit .i64 1).val =
      (t.length : Int) - i + 1 := by
    have hi : (JInt.lit .i64 (i : Int)).val = i := lit_i64_val _ (by omega) (by omega)
    have hL : (JInt.lit .i64 (t.length : Int)).val = t.length := lit_i64_val _ (by omega) (by omega)
    have h1v : (JInt.lit .i64 1).val = 1 := by decide
    rw [add_i64_val, sub_i64_val, hL, hi, h1v] <;> (try rw [sub_i64_val]) <;>
      (try rw [hL]) <;> (try rw [hi]) <;> (try rw [h1v]) <;> omega
  unfold restTuple
  rw [hn, ntupleInt_id_ok _ (by omega)]
  simp only [JuliaLean.Tuples.R.bind_ok]
  apply mapM_shift_ok
  · simp; omega
  · intro k hk
    simp only [List.length_drop] at hk
    rw [restIdx_val i k h1 (by omega), getfield_ok t _ (by omega), List.getElem_drop]

theorem restCorrect : RestCorrect := by
  intro α σ t
  refine ⟨rfl, fun i h1 h2 hl => restTuple_ok t i h1 h2 hl, ?_, ?_, ?_, fun _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩⟩
  · intro i hi hs hl
    have hiv : (JInt.lit .i64 (i : Int)).val = i := lit_i64_val _ (by omega) (by omega)
    have hL : (JInt.lit .i64 (t.length : Int)).val = t.length := lit_i64_val _ (by omega) (by omega)
    have h1v : (JInt.lit .i64 1).val = 1 := by decide
    have hn : (JInt.lit .i64 t.length - JInt.lit .i64 i + JInt.lit .i64 1).val =
        (t.length : Int) - i + 1 := by
      rw [add_i64_val, sub_i64_val, hL, hiv, h1v] <;> (try rw [sub_i64_val]) <;>
        (try rw [hL]) <;> (try rw [hiv]) <;> (try rw [h1v]) <;> omega
    unfold restTuple ntupleInt
    rw [hn, if_neg (by omega), if_neg (by omega)]
    exact ⟨_, rfl⟩
  · intro i hi hs hl
    have hiv : (JInt.lit .i64 (i : Int)).val = i := lit_i64_val _ (by omega) (by omega)
    have hL : (JInt.lit .i64 (t.length : Int)).val = t.length := lit_i64_val _ (by omega) (by omega)
    unfold restArray
    by_cases hle : i ≤ t.length
    · rw [colon_ok t _ _ (by rw [hiv, hL]; omega) (by rw [hiv, hL]; omega) (by rw [hiv]; omega)
        (by rw [hL]; omega)]
      rw [hiv, hL, List.take_of_length_le (by simp; omega)]
      exact congrArg (fun k => (Except.ok (List.drop k t) : R (List α))) (by omega)
    · rw [colon_empty t _ _ (by rw [hiv, hL]; omega) (by rw [hiv, hL]; omega),
        List.drop_of_length_le (by omega)]
  · intro i hi hlo hpos hl
    have hiv : (JInt.lit .i64 i).val = i := lit_i64_val _ (by omega) (by omega)
    have hL : (JInt.lit .i64 (t.length : Int)).val = t.length := lit_i64_val _ (by omega) (by omega)
    unfold restArray
    exact colon_bounds t _ _ (by rw [hiv, hL]; omega) (by rw [hiv, hL]; omega)
      (by rw [hiv]; omega)

/-! ### `split_rest` -/

theorem check_ok (len n : Nat) (h : n ≤ len) (hn : n < 2 ^ 62) :
    checkLengthSplitRest len (JInt.lit .i64 n) = .ok () := by
  unfold checkLengthSplitRest
  rw [lit_i64_val _ (by omega) (by omega), if_neg (by omega)]

theorem check_err (len n : Nat) (h : len < n) (hn : n < 2 ^ 62) :
    checkLengthSplitRest len (JInt.lit .i64 n) =
      argErr "The iterator only contains len elements, but at least n were requested." := by
  unfold checkLengthSplitRest
  rw [lit_i64_val _ (by omega) (by omega), if_pos (by omega)]

theorem split_vec (a : List α) (hl : a.length < 2 ^ 62) (m : JInt .i64) :
    splitRestVector a m (JInt.lit .i64 1) = (do
      checkLengthSplitRest a.length m
      pure ((if m.val ≥ 0 then (a.take (a.length - m.val.toNat)).map some
              else a.map some ++ List.replicate m.val.natAbs none),
            (if m.val ≥ 0 then a.drop (a.length - m.val.toNat) else []))) := by
  have h1v : (JInt.lit .i64 1).val = 1 := by decide
  unfold splitRestVector
  rw [h1v]
  by_cases ha : (1 : Int) ≤ a.length
  · rw [if_pos ha, if_pos (Int.le_refl 1)]
    simp
  · have : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp

theorem split_front (a : List α) (n : Nat) (hl : a.length < 2 ^ 62) (hle : n ≤ a.length) :
    getindexColon a (JInt.lit .i64 1) (JInt.lit .i64 a.length - JInt.lit .i64 n) =
      .ok (a.take (a.length - n)) := by
  have hnv : (JInt.lit .i64 (n : Int)).val = n := lit_i64_val _ (by omega) (by omega)
  have hL : (JInt.lit .i64 (a.length : Int)).val = a.length := lit_i64_val _ (by omega) (by omega)
  have h1v : (JInt.lit .i64 1).val = 1 := by decide
  have hLn : (JInt.lit .i64 (a.length : Int) - JInt.lit .i64 n).val = (a.length : Int) - n := by
    rw [sub_i64_val, hL, hnv] <;> (try rw [hL]) <;> (try rw [hnv]) <;> omega
  by_cases he : n = a.length
  · rw [colon_empty a _ _ (by rw [h1v, hLn]; omega) (by rw [h1v, hLn]; omega)]
    subst he; simp
  · rw [colon_ok a _ _ (by rw [h1v, hLn]; omega) (by rw [h1v, hLn]; omega) (by rw [h1v]; omega)
      (by rw [hLn]; omega), h1v, hLn]
    simp only [Int.sub_self, Int.toNat_zero, List.drop_zero]
    exact congrArg (fun k => (Except.ok (List.take k a) : R (List α))) (by omega)

theorem split_back (a : List α) (n : Nat) (hl : a.length < 2 ^ 62) (hle : n ≤ a.length) :
    getindexColon a (JInt.lit .i64 a.length - JInt.lit .i64 n + JInt.lit .i64 1)
      (JInt.lit .i64 a.length) = .ok (a.drop (a.length - n)) := by
  have hnv : (JInt.lit .i64 (n : Int)).val = n := lit_i64_val _ (by omega) (by omega)
  have hL : (JInt.lit .i64 (a.length : Int)).val = a.length := lit_i64_val _ (by omega) (by omega)
  have h1v : (JInt.lit .i64 1).val = 1 := by decide
  have hLn : (JInt.lit .i64 (a.length : Int) - JInt.lit .i64 n).val = (a.length : Int) - n := by
    rw [sub_i64_val, hL, hnv] <;> (try rw [hL]) <;> (try rw [hnv]) <;> omega
  have hLn1 : (JInt.lit .i64 (a.length : Int) - JInt.lit .i64 n + JInt.lit .i64 1).val =
      (a.length : Int) - n + 1 := by
    rw [add_i64_val, hLn, h1v] <;> (try rw [hLn]) <;> (try rw [h1v]) <;> omega
  by_cases he : n = 0
  · rw [colon_empty a _ _ (by rw [hLn1, hL]; omega) (by rw [hLn1, hL]; omega)]
    subst he; simp
  · rw [colon_ok a _ _ (by rw [hLn1, hL]; omega) (by rw [hLn1, hL]; omega)
      (by rw [hLn1]; omega) (by rw [hL]; omega), hLn1, hL,
      List.take_of_length_le (by simp; omega)]
    exact congrArg (fun k => (Except.ok (List.drop k a) : R (List α))) (by omega)

theorem split_array_ok (a : List α) (n : Nat) (hl : a.length < 2 ^ 62) (hn : n < 2 ^ 62)
    (hle : n ≤ a.length) :
    splitRestArray a (JInt.lit .i64 n) = .ok (a.take (a.length - n), a.drop (a.length - n)) := by
  simp only [splitRestArray, check_ok _ _ hle hn, split_front a n hl hle, split_back a n hl hle,
    JuliaLean.Tuples.R.bind_ok, JuliaLean.Tuples.R.pure_eq]

theorem split_iter_ok (a : List α) (n : Nat) (hl : a.length < 2 ^ 62) (hn : n < 2 ^ 62)
    (hle : n ≤ a.length) :
    splitRestIter false a (JInt.lit .i64 n) =
      .ok ((a.take (a.length - n)).map some, a.drop (a.length - n)) := by
  have hnv : (JInt.lit .i64 (n : Int)).val = n := lit_i64_val _ (by omega) (by omega)
  unfold splitRestIter
  rw [if_neg (by decide), split_vec a hl, check_ok _ _ hle hn, hnv]
  simp

theorem split_array_err (a : List α) (n : Nat) (hn : n < 2 ^ 62) (hgt : n > a.length) :
    splitRestArray a (JInt.lit .i64 n) =
      argErr "The iterator only contains len elements, but at least n were requested." := by
  unfold splitRestArray
  rw [check_err _ _ hgt hn]
  rfl

theorem split_iter_err (a : List α) (n : Nat) (hl : a.length < 2 ^ 62) (hn : n < 2 ^ 62)
    (hgt : n > a.length) :
    splitRestIter false a (JInt.lit .i64 n) =
      argErr "The iterator only contains len elements, but at least n were requested." := by
  unfold splitRestIter
  rw [if_neg (by decide), split_vec a hl, check_err _ _ hgt hn]
  rfl

theorem split_check (a : List α) (n : Nat) (hn : n < 2 ^ 62) :
    checkLengthSplitRest a.length (JInt.lit .i64 n) =
      if a.length < n then argErr "The iterator only contains len elements, but at least n were requested."
      else .ok () := by
  have hnv : (JInt.lit .i64 (n : Int)).val = n := lit_i64_val _ (by omega) (by omega)
  unfold checkLengthSplitRest
  rw [hnv]
  by_cases h : a.length < n
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem splitRestCorrect : SplitRestCorrect := by
  intro α a n hl hn
  exact ⟨fun hle => ⟨split_array_ok a n hl hn hle, split_iter_ok a n hl hn hle⟩,
    fun hgt => ⟨⟨_, split_array_err a n hn hgt⟩, ⟨_, split_iter_err a n hl hn hgt⟩⟩,
    ⟨_, rfl⟩, split_check a n hn⟩

/-! ### `map` over `n ≥ 3` tuples and `foreach` -/

theorem anyempty_iff : ∀ (ts : List (List α)), anyempty ts = true ↔ ∃ t ∈ ts, t = []
  | [] => by simp [anyempty]
  | [] :: _ => by simp [anyempty]
  | (a :: r) :: ts => by
    rw [show anyempty ((a :: r) :: ts) = anyempty ts from rfl, anyempty_iff ts]
    simp

theorem heads_ok : ∀ (ts : List (List α)), (∀ t ∈ ts, t ≠ []) →
    ∃ hs, ts.mapM List.head? = some hs ∧ heads ts = .ok hs
  | [], _ => ⟨[], rfl, rfl⟩
  | t :: ts, h => by
    obtain ⟨hs, h1, h2⟩ := heads_ok ts (fun u hu => h u (by simp [hu]))
    cases t with
    | nil => exact absurd rfl (h [] (by simp))
    | cons a r =>
      refine ⟨a :: hs, ?_, ?_⟩
      · simp [List.mapM_cons, h1]
      · show (do let x ← getfield (a :: r) 1; let r ← heads ts; pure (x :: r)) = _
        rw [h2]
        rfl

theorem heads_none : ∀ (ts : List (List α)), (∃ t ∈ ts, t = []) → ts.mapM List.head? = none
  | [], h => by simp at h
  | [] :: _, _ => by simp [List.mapM_cons]
  | (a :: r) :: ts, h => by
    have h' : ∃ t ∈ ts, t = [] := by
      obtain ⟨u, hu, rfl⟩ := h
      rcases List.mem_cons.1 hu with h | h
      · cases h
      · exact ⟨[], h, rfl⟩
    rw [List.mapM_cons, heads_none ts h']
    rfl

theorem tails_ok : ∀ (ts : List (List α)), (∀ t ∈ ts, t ≠ []) → tails ts = .ok (ts.map List.tail)
  | [], _ => rfl
  | t :: ts, h => by
    cases t with
    | nil => exact absurd rfl (h [] (by simp))
    | cons a r =>
      show (do let x ← JuliaLean.Tuples.tail (a :: r); let r ← tails ts; pure (x :: r)) = _
      rw [tails_ok ts (fun u hu => h u (by simp [hu]))]
      rfl

theorem mapRec_spec (f : List α → β) : ∀ (k : Nat) (ts : List (List α)), ts ≠ [] →
    mapRec f k ts = .ok ((zipN ts k).map f)
  | 0, _, _ => rfl
  | k + 1, ts, hne => by
    by_cases he : anyempty ts = true
    · have hn := heads_none ts ((anyempty_iff ts).1 he)
      simp only [mapRec, he, if_true, zipN, hn]
      rfl
    · have hall : ∀ t ∈ ts, t ≠ [] := by
        intro t ht heq
        exact he ((anyempty_iff ts).2 ⟨t, ht, heq⟩)
      obtain ⟨hs, h1, h2⟩ := heads_ok ts hall
      have hne' : ts.map List.tail ≠ [] := by simpa using hne
      have hie : ts.isEmpty = false := by cases ts <;> simp_all
      simp only [mapRec, he, Bool.false_eq_true, if_false, h2, tails_ok ts hall,
        JuliaLean.Tuples.R.bind_ok, mapRec_spec f k _ hne', zipN, h1, hie]
      rfl

theorem zipN_fuel : ∀ (K M : Nat) (ts : List (List α)), (∀ t ∈ ts, t.length ≤ K) →
    (∀ t ∈ ts, t.length ≤ M) → zipN ts K = zipN ts M
  | 0, 0, _, _, _ => rfl
  | 0, M + 1, ts, hK, _ => by
    simp only [zipN]
    cases hm : ts.mapM List.head? with
    | none => rfl
    | some h =>
      cases ts with
      | nil => rfl
      | cons t ts =>
        exfalso
        have : t = [] := List.eq_nil_of_length_eq_zero (by have := hK t (by simp); omega)
        rw [heads_none (t :: ts) ⟨t, by simp, this⟩] at hm
        cases hm
  | K + 1, 0, ts, _, hM => by
    simp only [zipN]
    cases hm : ts.mapM List.head? with
    | none => rfl
    | some h =>
      cases ts with
      | nil => rfl
      | cons t ts =>
        exfalso
        have : t = [] := List.eq_nil_of_length_eq_zero (by have := hM t (by simp); omega)
        rw [heads_none (t :: ts) ⟨t, by simp, this⟩] at hm
        cases hm
  | K + 1, M + 1, ts, hK, hM => by
    simp only [zipN]
    cases hm : ts.mapM List.head? with
    | none => rfl
    | some h =>
      by_cases hie : ts.isEmpty = true
      · simp [hie]
      · simp only [hie, Bool.false_eq_true, if_false]
        have hall : ∀ t ∈ ts, t ≠ [] := by
          intro t ht heq
          rw [heads_none ts ⟨t, ht, heq⟩] at hm
          cases hm
        congr 1
        apply zipN_fuel K M
        · intro u hu
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
          have := hK t ht; have := hall t ht
          cases t with
          | nil => exact absurd rfl this
          | cons _ r => simp at *; omega
        · intro u hu
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
          have := hM t ht; have := hall t ht
          cases t with
          | nil => exact absurd rfl this
          | cons _ r => simp at *; omega

theorem foldl_min_le : ∀ (l : List Nat) (init : Nat),
    l.foldl min init ≤ init ∧ ∀ x ∈ l, l.foldl min init ≤ x
  | [], init => by simp
  | x :: l, init => by
    have := foldl_min_le l (min init x)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨by omega, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · omega
    · exact this.2 y hy

theorem foldl_min_mem : ∀ (l : List Nat) (init : Nat), l.foldl min init = init ∨ l.foldl min init ∈ l
  | [], init => by simp
  | x :: l, init => by
    rcases foldl_min_mem l (min init x) with h | h
    · simp only [List.foldl_cons, h]
      by_cases hx : init ≤ x
      · left; omega
      · right; simp; omega
    · right; simp [h]

theorem foldl_max_ge : ∀ (l : List Nat) (init : Nat), init ≤ l.foldl max init ∧ ∀ x ∈ l, x ≤ l.foldl max init
  | [], init => by simp
  | x :: l, init => by
    have := foldl_max_ge l (max init x)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨by omega, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · omega
    · exact this.2 y hy

theorem column_ok (ts : List (List α)) (k : Nat) (h : ∀ t ∈ ts, k < t.length) :
    ts.mapM (fun t => getfield t ((k : Int) + 1)) = .ok (ts.filterMap fun t => t[k]?) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hk := h t (by simp)
    rw [List.mapM_cons, getfield_ok t k hk, JuliaLean.Tuples.R.bind_ok,
      ih (fun u hu => h u (by simp [hu]))]
    simp [List.filterMap_cons, List.getElem?_eq_getElem hk]

theorem mapNForeachCorrect : MapNForeachCorrect := by
  intro α β σ f ts h3
  have hne : ts ≠ [] := by intro h; subst h; simp at h3
  refine ⟨?_, ?_, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · intro hall K hK
    simp only [mapN, hall, Bool.false_eq_true, if_false]
    rw [mapRec_spec f _ ts hne, zipN_fuel _ K ts (fun t ht => (foldl_max_ge _ 0).2 _
      (List.mem_map.2 ⟨t, ht, rfl⟩)) hK]
  · intro hall
    have hmin := foldl_min_le (ts.map List.length) (ts.headD []).length
    have hle : ∀ t ∈ ts, (ts.map List.length).foldl min (ts.headD []).length ≤ t.length :=
      fun t ht => hmin.2 _ (List.mem_map.2 ⟨t, ht, rfl⟩)
    refine ⟨hle, ?_, ?_⟩
    · rcases foldl_min_mem (ts.map List.length) (ts.headD []).length with h | h
      · cases ts with
        | nil => exact absurd rfl hne
        | cons t ts => exact ⟨t, by simp, by simpa using h.symm⟩
      · obtain ⟨t, ht, e⟩ := List.mem_map.1 h
        exact ⟨t, ht, e⟩
    · simp only [mapN, hall, if_true, mapLoop]
      apply mapM_range_ok
      · simp
      · intro k hk
        simp only [List.length_map, List.length_range] at hk
        rw [column_ok ts k (fun t ht => by have := hle t ht; omega)]
        simp

/-! ### `sym_in`, `fill_to_length` -/

theorem symInCorrect : SymInCorrect := by
  intro x itr
  have key : symInLoop x itr = decide (x ∈ itr) := by
    induction itr with
    | nil => rfl
    | cons y r ih =>
      simp only [symInLoop, List.mem_cons]
      by_cases h : y = x
      · subst h; simp
      · simp [h, ih, Ne.symm h]
  exact ⟨key, key⟩

theorem fillToLengthSpecialized : FillToLengthSpecialized := by
  intro α t v a hl
  have hL : (JInt.lit .i64 (t.length : Int)).val = t.length := lit_i64_val _ (by omega) (by omega)
  refine ⟨?_, rfl, rfl, rfl⟩
  unfold fillToLength
  rw [if_pos hL.symm]

end JuliaLean.SortTuplesCov
