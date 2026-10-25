import JuliaLean.Iterators.Spec

namespace JuliaLean.Iterators
open JuliaLean

private theorem flatPure (a : α) : (pure a : M α) = .ok a := rfl
private theorem flatBind (a : α) (f : α → M β) : (.ok a >>= f) = f a := rfl
attribute [local simp] flatPure flatBind

private theorem flatIterVec (F : Nat) (t : Ty) (xs : List Val) (s : Option St) :
    iter F (.vec t xs) s = idxIter xs s := rfl
private theorem flatIterRepeated (F : Nat) (v : Val) (s : Option St) :
    iter F (.repeated v) s = .ok (some (v, .nothing)) := rfl
private theorem flatIterTake (F : Nat) (it : Itr) (m : JInt64) (s : Option St) :
    iter F (.take it m) s = (do
      let (n, rest) ← splitCountState s m
      if n ≤ i64 0 then pure none else
        match ← iter F it rest with
        | none => pure none
        | some (v, st) => pure (some (v, .tup [.int (n - i64 1).val, st]))) := rfl
private theorem flatIterStart (F : Nat) (outer : Itr) :
    iter F (.flatten outer) none = (do
      match ← iter F outer none with
      | none => pure none
      | some (v, so) =>
        flatLoop (fun s => iter F outer (some s)) F v so (← valIter v none)) := rfl

private inductive FlatChain (step : St → M (Option (Val × St))) :
    M (Option (Val × St)) → List Val → Prop where
  | nil {r} : r = .ok none → FlatChain step r []
  | cons {x s r xs} : r = .ok (some (x, s)) →
      FlatChain step (step s) xs → FlatChain step r (x :: xs)

private theorem flatChain_run {step : St → M (Option (Val × St))} {r xs}
    (h : FlatChain step r xs) (n : Nat) (hn : xs.length < n) :
    (do runFrom step n (← r)) = .ok xs := by
  induction h generalizing n with
  | nil he => simp [he, runFrom]
  | @cons x s r xs he h ih =>
    rw [he]
    cases n with
    | zero => simp at hn
    | succ n =>
      have hi := ih n (by simpa using hn)
      cases hs : step s with
      | error e =>
        rw [hs] at hi
        change Except.error e = Except.ok xs at hi
        cases hi
      | ok y =>
        simp only [hs, flatBind] at hi
        simp only [flatBind, runFrom, flatPure, hs]
        rw [hi]
        rfl

private theorem flat_idx (pre rest : List Val) :
    FlatChain (fun s => idxIter (pre ++ rest) (some s))
      (idxIter (pre ++ rest) (some (.int (pre.length + 1)))) rest := by
  induction rest generalizing pre with
  | nil =>
    apply FlatChain.nil
    simp [idxIter]
    omega
  | cons x xs ih =>
    have hi : (pre.length : Int) + 1 - 1 = pre.length := by omega
    have hg : (pre ++ x :: xs).getD pre.length .undef = x := by
      simp [List.getD, List.getElem?_append]
    have he : idxIter (pre ++ x :: xs) (some (.int (pre.length + 1))) =
        .ok (some (x, .int (pre.length + 2))) := by
      have hb : 1 ≤ (pre.length : Int) + 1 ∧
          (pre.length : Int) + 1 ≤ (pre ++ x :: xs).length := by
        simp only [List.length_append, List.length_cons, Int.natCast_add, Int.natCast_one]
        omega
      simp only [idxIter, if_pos hb, hi, Int.toNat_natCast, hg, flatPure]
      congr 3
    rw [he]
    apply FlatChain.cons rfl
    have ht := ih (pre ++ [x])
    simpa [List.append_assoc, Int.natCast_add, Int.add_assoc] using ht

private theorem flat_idx_start (xs : List Val) :
    FlatChain (fun s => idxIter xs (some s)) (idxIter xs none) xs := by
  have h := flat_idx [] xs
  cases xs with
  | nil => exact FlatChain.nil rfl
  | cons x xs =>
    have hb : (1 : Int) ≤ ((x :: xs).length : Int) := by simp; omega
    have he : idxIter (x :: xs) none = idxIter (x :: xs) (some (.int 1)) := by
      simp [idxIter, show (1 : Nat) ≤ (x :: xs).length from by simp, hb]
      omega
    rw [he]
    simpa only [List.nil_append, List.length_nil, Int.natCast_zero, Int.zero_add] using h

private theorem flat_state (outer : Itr) (F : Nat) (inner : Val) (so si : St) :
    iter F (.flatten outer) (some (.tup [so, .val inner, si])) =
      (do flatLoop (fun s => iter F outer (some s)) F inner so (← valIter inner (some si))) := by
  change (do
    match ← valIter inner (some si) with
    | some (item, si') => pure (some (item, St.tup [so, .val inner, si']))
    | none => flatLoop (fun s => iter F outer (some s)) F inner so none) = _
  cases valIter inner (some si) with
  | error e => rfl
  | ok r =>
    cases r with
    | none => rfl
    | some p => cases p; simp only [flatBind, flatLoop, flatPure]

private theorem flat_loop_chain (outer : Itr) (F : Nat) (vs : List (List Val))
    (so : St)
    (ho : FlatChain (fun s => iter F outer (some s))
      (iter F outer (some so)) (vs.map (.vec .int))) :
    ∀ (inner : Val) (r : M (Option (Val × St))) (xs : List Val),
      FlatChain (fun s => valIter inner (some s)) r xs →
      ∀ k, vs.length < k → k ≤ F →
      FlatChain (fun s => iter F (.flatten outer) (some s))
        (do flatLoop (fun s => iter F outer (some s)) k inner so (← r))
        (xs ++ vs.flatten) := by
  induction vs generalizing so with
  | nil =>
    intro inner r xs hi
    induction hi with
    | nil he =>
      intro k hk hF
      cases ho with
      | nil hout =>
        cases k with
        | zero => omega
        | succ k =>
          apply FlatChain.nil
          simp [he, flatLoop, hout]
    | @cons x si r xs he hi ih =>
      intro k hk hF
      simp only [List.cons_append]
      apply FlatChain.cons (s := .tup [so, .val inner, si]) (by simp [he, flatLoop])
      rw [flat_state]
      exact ih F (by omega) (by omega)
  | cons v vs ihOuter =>
    intro inner r xs hi
    induction hi with
    | nil he =>
      intro k hk hF
      cases ho with
      | cons hout ht =>
        cases k with
        | zero => omega
        | succ k =>
          simp only [List.nil_append, List.flatten_cons]
          simpa [he, flatLoop, hout, valIter] using
            ihOuter _ ht (.vec .int v) (idxIter v none) v (flat_idx_start v)
              k (by simp at hk; omega) (by omega)
    | @cons x si r xs he hi ih =>
      intro k hk hF
      simp only [List.cons_append]
      apply FlatChain.cons (s := .tup [so, .val inner, si]) (by simp [he, flatLoop])
      rw [flat_state]
      exact ih F (by omega) (by omega)


private theorem flat_start_chain (outer : Itr) (F : Nat) (vs : List (List Val))
    (ho : FlatChain (fun s => iter F outer (some s))
      (iter F outer none) (vs.map (.vec .int)))
    (hF : vs.length < F) :
    FlatChain (fun s => iter F (.flatten outer) (some s))
      (iter F (.flatten outer) none) vs.flatten := by
  cases vs with
  | nil =>
    cases ho with
    | nil he =>
      apply FlatChain.nil
      simp only [flatIterStart, he, flatBind, flatPure]
  | cons v vs =>
    cases ho with
    | cons he ht =>
      simp only [flatIterStart, he, flatBind, List.flatten_cons]
      exact flat_loop_chain outer F vs _ ht (.vec .int v) (idxIter v none) v
        (flat_idx_start v) F (by simp at hF; omega) (by omega)

theorem flattenCorrect : FlattenCorrect := by
  intro vs fuel h
  have ho : FlatChain (fun s => iter fuel (.vec (.vector .int) (vs.map (.vec .int))) (some s))
      (iter fuel (.vec (.vector .int) (vs.map (.vec .int))) none) (vs.map (.vec .int)) := by
    simpa only [flatIterVec] using flat_idx_start (vs.map (.vec .int))
  have hc := flat_start_chain _ fuel vs ho (by omega)
  exact flatChain_run hc fuel (by simpa only [List.length_flatten] using (show (vs.map List.length).sum < fuel from by omega))

private theorem flat_i64 (n : Int)
    (hn : IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max) : (i64 n).val = n :=
  wrapInt_of_inRange .i64 n hn

private theorem flatZero : (i64 0).val = 0 := flat_i64 0 (by decide)
private theorem flatOne : (i64 1).val = 1 := flat_i64 1 (by decide)

private theorem flat_sum_replicate (n k : Nat) : (List.replicate n k).sum = n * k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

private theorem flat_take_done (F : Nat) (it : Itr) (m n : JInt64)
    (st rest : Option St) (hn : n ≤ i64 0)
    (hs : splitCountState st m = .ok (n, rest)) :
    iter F (.take it m) st = .ok none := by
  rw [flatIterTake, hs]
  simp only [flatBind, if_pos hn, flatPure]

private theorem flat_repeat_zero (F : Nat) (v : Val) (m : JInt64) :
    iter F (.take (.repeated v) m) (some (.tup [.int 0, .nothing])) = .ok none := by
  apply flat_take_done F (.repeated v) m (i64 0) _ (some .nothing)
  · change (i64 0).val ≤ (i64 0).val
    exact Int.le_refl _
  · rfl

private theorem flat_decrement_nat (n : Nat) (hn : (n + 1 : Int) ≤ IntTy.i64.max) :
    (i64 (n + 1 : Int) - i64 1).val = n := by
  have hn0 : (i64 (n : Int)).val = n :=
    flat_i64 _ (by
      constructor
      · change -(2 ^ 63 : Int) ≤ n
        omega
      · omega)
  have hn1 : (i64 (n + 1 : Int)).val = n + 1 :=
    flat_i64 _ (by
      constructor
      · change -(2 ^ 63 : Int) ≤ n + 1
        omega
      · omega)
  change wrapInt .i64 ((i64 (n + 1 : Int)).val - (i64 1).val) = n
  rw [hn1, flatOne, Int.add_sub_cancel]
  exact hn0

private theorem flat_repeat_next (F : Nat) (v : Val) (m ni : JInt64) (k : Int)
    (hi : i64 k = ni) (hp : ¬ ni ≤ i64 0) :
    iter F (.take (.repeated v) m) (some (.tup [.int k, .nothing])) =
      .ok (some (v, .tup [.int (ni - i64 1).val, .nothing])) := by
  rw [flatIterTake]
  simp only [splitCountState, flatPure, flatBind, hi]
  rw [if_neg hp]
  simp only [flatIterRepeated, flatBind, flatPure]

private theorem flat_repeat_chain (F : Nat) (v : Val) (m : JInt64) (n : Nat)
    (hn : (n : Int) ≤ IntTy.i64.max) :
    FlatChain (fun s => iter F (.take (.repeated v) m) (some s))
      (iter F (.take (.repeated v) m) (some (.tup [.int n, .nothing])))
      (List.replicate n v) := by
  induction n with
  | zero =>
    apply FlatChain.nil
    simp only [Int.natCast_zero]
    exact flat_repeat_zero F v m
  | succ n ih =>
    have hn1 : (i64 (n + 1 : Int)).val = n + 1 :=
      flat_i64 _ (by
        constructor
        · change -(2 ^ 63 : Int) ≤ n + 1
          omega
        · omega)
    have hd := flat_decrement_nat n (by omega)
    rw [List.replicate_succ]
    apply FlatChain.cons (s := .tup [.int n, .nothing])
    · have hp : ¬ i64 ((n : Int) + 1) ≤ i64 0 := by
        change ¬ (i64 ((n : Int) + 1)).val ≤ (i64 0).val
        rw [hn1, flatZero]
        omega
      simpa only [Int.natCast_add, Int.natCast_one, hd] using
        flat_repeat_next F v m (i64 (n + 1 : Int)) (n + 1) rfl hp
    · exact ih (by omega)

private theorem flat_repeat_start (F : Nat) (v : Val) (m : JInt64) (hm : 0 ≤ m.val) :
    FlatChain (fun s => iter F (.take (.repeated v) m) (some s))
      (iter F (.take (.repeated v) m) none) (List.replicate m.val.toNat v) := by
  have hval : (m.val.toNat : Int) = m.val := Int.toNat_of_nonneg hm
  cases h : m.val.toNat with
  | zero =>
    apply FlatChain.nil
    have hz : m.val = 0 := by omega
    simp only [flatIterTake, splitCountState, flatPure, flatBind]
    rw [if_pos (show m ≤ i64 0 from by
      change m.val ≤ (i64 0).val
      rw [flatZero]
      omega)]
  | succ n =>
    have hd : (m - i64 1).val = n := by
      change wrapInt .i64 (m.val - (i64 1).val) = n
      rw [flatOne]
      have he : m.val - 1 = n := by omega
      rw [he]
      exact flat_i64 _ (by
        have hb := m.property
        constructor <;> simp [IntTy.min, IntTy.signed, IntTy.bits] at * <;> omega)
    rw [List.replicate_succ]
    apply FlatChain.cons (s := .tup [.int n, .nothing])
    · simp only [flatIterTake, flatIterRepeated, splitCountState, flatPure, flatBind, hd]
      rw [if_neg (show ¬ m ≤ i64 0 from by
        change ¬ m.val ≤ (i64 0).val
        rw [flatZero]
        omega)]
    · exact flat_repeat_chain F v m n (by have hb := m.property; omega)

theorem cycleNCorrect : CycleNCorrect := by
  intro xs m fuel hm hf
  refine ⟨.flatten (.take (.repeated (.vec .int xs)) m), ?_, ?_⟩
  · have hc : toInt m = .ok m := by
      simp [toInt, JInt.convert, m.property, liftJ]
    simp [cycleN, repeatedN, take, hc, mkTake,
      show ¬ m < i64 0 from by
        change ¬ m.val < (i64 0).val
        rw [flatZero]
        omega]
  · have ho : FlatChain (fun s => iter fuel (.take (.repeated (.vec .int xs)) m) (some s))
        (iter fuel (.take (.repeated (.vec .int xs)) m) none)
        ((List.replicate m.val.toNat xs).map (.vec .int)) := by
      simpa only [List.map_replicate] using flat_repeat_start fuel (.vec .int xs) m hm
    have hp : m.val.toNat ≤ (xs.length + 1) * m.val.toNat :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hc := flat_start_chain _ fuel (List.replicate m.val.toNat xs) ho
      (by simpa only [List.length_replicate] using (show m.val.toNat < fuel from by omega))
    exact flatChain_run hc fuel (by
      simp only [List.length_flatten, List.map_replicate, flat_sum_replicate]
      have hmul : m.val.toNat * xs.length ≤ (xs.length + 1) * m.val.toNat := by
        rw [Nat.mul_comm m.val.toNat xs.length]
        exact Nat.mul_le_mul_right _ (by omega)
      omega)

end JuliaLean.Iterators
