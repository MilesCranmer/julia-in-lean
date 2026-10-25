import JuliaLean.Iterators.Spec
import JuliaLean.Iterators.ProofsAList
import JuliaLean.Iterators.ProofsAIndex
import JuliaLean.Iterators.ProofsATake
import JuliaLean.Iterators.ProofsADrop
import JuliaLean.Iterators.ProofsAWhile
import JuliaLean.Iterators.ProofsACount
import JuliaLean.Iterators.ProofsAZip
import JuliaLean.Iterators.ProofsAFirst

namespace JuliaLean.Iterators
open JuliaLean
open ProofsAList
attribute [local simp] Bind.bind Pure.pure Except.bind Except.pure

 theorem onlyCorrect : OnlyCorrect := by
  intro xs fuel
  constructor
  · intro x hx
    subst xs
    rfl
  · intro h
    cases xs with
    | nil => exact ⟨_, rfl⟩
    | cons x xs =>
      cases xs with
      | nil => exact False.elim (h rfl)
      | cons y ys =>
        refine ⟨"Collection has multiple elements, must contain exactly 1 element", ?_⟩
        have h2 : (2 : Int) ≤ (ys.length : Int) + 1 + 1 := by omega
        simp [only, iter_vec, idxIter, List.getD, h2, jthrow]

 theorem firstLastVector : FirstLastVector := by
  intro t xs n fuel hn
  have hneg : ¬ n.val < 0 := by omega
  have hmin : (min n.val (xs.length : Int)).toNat = min n.val.toNat xs.length := by
    simp only [Int.min_def, Nat.min_def]
    split <;> split <;> omega
  simp only [firstN, lastN, if_neg hneg, hmin]
  constructor
  · congr 1
    simp
  · congr 1
    congr 1
    omega

theorem statefulConsistent : StatefulConsistent := by
  intro xs pos fuel sentinel hf
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [isempty, isdone0]
  · intro hp
    simp [popfirst, peek, hp, show ¬ xs.length ≤ pos by omega]
  · intro hp
    simp [popfirst, peek, hp, show ¬ pos < xs.length by omega]
  · simpa [collect, isz] using ProofsAList.elems_stateful xs pos fuel hf

theorem takeCorrect : TakeCorrect := by
  intro xs n hn hfits
  refine ⟨.take (vecI xs) n, ?_, ?_, ?_⟩
  · exact take_vec (ints xs) n hn
  · have hlen : (i64 (xs.map Val.int).length).val = xs.length := by
      simpa only [List.length_map] using fits_i64_length xs hfits
    change (do pure (jmin (← len (vecI xs)) n)) = _
    simp only [vecI, len, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [jmin_eq, hlen]
    apply congrArg Except.ok
    apply congrArg i64
    omega
  · intro fuel hf
    simpa [vecI, ints, List.map_take] using
      ProofsATake.elems_take_vec (ints xs) n fuel hn (by simpa [ints] using hf)

theorem takeTakeCorrect : TakeTakeCorrect := by
  intro xs a b ha hb
  let c := jmin b a
  have hc : 0 ≤ c.val := by dsimp [c]; rw [jmin_val]; omega
  refine ⟨.take (vecI xs) c, ?_, ?_⟩
  · rw [show take (vecI xs) a = .ok (.take (vecI xs) a) from take_vec (ints xs) a ha]
    change (do mkTake (vecI xs) (jmin (← toInt b) a)) = _
    rw [toInt_self]
    exact mkTake_ok _ c hc
  · intro fuel hf
    have he : c.val = min a.val b.val := by dsimp [c]; rw [jmin_val]; omega
    simpa [vecI, ints, List.map_take, he] using
      ProofsATake.elems_take_vec (ints xs) c fuel hc (by simpa [ints] using hf)

theorem dropCorrect : DropCorrect := by
  intro xs n hn hfits
  refine ⟨.drop (vecI xs) n, drop_vec (ints xs) n hn, ?_, ?_⟩
  · have hlen : (i64 (xs.map Val.int).length).val = xs.length := by
      simpa only [List.length_map] using fits_i64_length xs hfits
    change (do let m ← len (vecI xs); pure (if n < m then m - n else i64 0)) = _
    simp only [vecI, len, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have hl : (n < i64 (xs.map Val.int).length) ↔ n.val < (xs.length : Int) := by
      change (n.val < (i64 (xs.map Val.int).length).val) ↔ _
      rw [hlen]
    by_cases h : n.val < (xs.length : Int)
    · rw [if_pos (hl.mpr h)]
      apply congrArg Except.ok
      change i64 ((i64 (xs.map Val.int).length).val - n.val) = _
      rw [hlen]
      apply congrArg i64
      omega
    · rw [if_neg (fun hn => h (hl.mp hn))]
      apply congrArg Except.ok
      apply congrArg i64
      omega
  · intro fuel hf
    simpa [vecI, ints, List.map_drop] using
      ProofsADrop.elems_drop_vec (ints xs) n fuel (by simpa [ints] using hf)

theorem takeDropComplement : TakeDropComplement := by
  intro xs n t d fuel hn hf ht hd
  have ht' : take (vecI xs) n = .ok (.take (vecI xs) n) := take_vec (ints xs) n hn
  have hd' : drop (vecI xs) n = .ok (.drop (vecI xs) n) := drop_vec (ints xs) n hn
  rw [ht'] at ht
  rw [hd'] at hd
  cases ht
  cases hd
  rw [show elems fuel (.take (vecI xs) n) = .ok (ints (xs.take n.val.toNat)) by
    simpa [vecI, ints, List.map_take] using
      ProofsATake.elems_take_vec (ints xs) n fuel hn (by simpa [ints] using hf)]
  rw [show elems fuel (.drop (vecI xs) n) = .ok (ints (xs.drop n.val.toNat)) by
    simpa [vecI, ints, List.map_drop] using
      ProofsADrop.elems_drop_vec (ints xs) n fuel (by simpa [ints] using hf)]
  simp [ints, ← List.map_append, List.take_append_drop]

theorem takeWhileDropWhile : TakeWhileDropWhile := by
  intro pred xs fuel hf
  constructor
  · have hstart : iter fuel (.takeWhile pred (.vec .int xs)) none =
        ProofsAWhile.whileAt xs 0 pred := by
      simp only [ProofsAWhile.iter_takeWhile, iter_vec]
      rw [idxIter_start]
      rfl
    unfold elems
    rw [hstart]
    simpa using ProofsAWhile.run_whileAt xs fuel pred fuel 0 (by simpa using Nat.le_of_lt hf)
  · unfold elems
    simp only [ProofsAWhile.iter_dropWhile_none, ProofsAWhile.iter_dropWhile_some, iter_vec]
    rw [idxIter_start]
    have hi := ProofsAWhile.run_dropWhile xs pred fuel fuel 0
      (by simpa using Nat.le_of_lt hf) (by simpa using Nat.le_of_lt hf)
    cases hy : nextAt xs 0 (fun q => .int (q + 1)) <;>
      simpa only [List.drop_zero, hy, Bind.bind, Except.bind] using hi

end JuliaLean.Iterators
