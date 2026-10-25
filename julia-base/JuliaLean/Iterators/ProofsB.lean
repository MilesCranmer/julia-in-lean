import JuliaLean.Iterators.Spec
import JuliaLean.Iterators.ProofsBProduct
import JuliaLean.Iterators.ProofsBPartition
import JuliaLean.Iterators.ProofsBFlatten
import JuliaLean.Iterators.ProofsBTupleLength

namespace JuliaLean.Iterators
open JuliaLean
set_option maxRecDepth 4096
attribute [local simp] Bind.bind Pure.pure Except.bind Except.pure

private theorem okBind {α β : Type} (a : α) (f : α → M β) :
    (Except.ok a >>= f) = f a := rfl
attribute [local simp] okBind

private theorem pureOk {α : Type} (a : α) : (pure a : M α) = .ok a := rfl
attribute [local simp] pureOk

private theorem litValue (x : Int) (h : -(2^63) ≤ x ∧ x ≤ 2^63-1) :
    (i64 x).val = x := by
  exact wrapInt_of_inRange .i64 x h

private theorem toIntSelf (x : JInt64) : toInt x = .ok x := by
  simp only [toInt, JInt.convert, dite_eq_left x.property, liftJ]

private theorem takeIter (fuel : Nat) (it : Itr) (n : JInt64) (s : Option St) :
    iter fuel (.take it n) s = (do
      let (m, rest) ← splitCountState s n
      if m ≤ i64 0 then pure none else
      match ← iter fuel it rest with
      | none => pure none
      | some (y, s) => pure (some (y, .tup [.int (m - i64 1).val, s]))) := rfl

private theorem repeatedBase (fuel : Nat) (x : Val) (s : Option St) :
    iter fuel (.repeated x) s = .ok (some (x, .nothing)) := rfl

private theorem repeatedIter (fuel : Nat) (x : Val) (n : JInt64) (s : Option St) :
    iter fuel (.take (.repeated x) n) s = (do
      let (m, _) ← splitCountState s n
      if m ≤ i64 0 then pure none else
      pure (some (x, .tup [.int (m - i64 1).val, .nothing]))) := by
  simp only [takeIter, repeatedBase, okBind]

private theorem accIterNext (fuel : Nat) (f : Val → Val → Val)
    (xs : List Val) (init : Option Val) (a : Val) (s : St) :
    iter fuel (.accumulate f (.vec .int xs) init) (some (.tup [.val a, s])) = (do
      match ← idxIter xs (some s) with
      | none => pure none
      | some (x, s') => pure (some (f a x, .tup [.val (f a x), s']))) := rfl

private theorem accIterStart (fuel : Nat) (f : Val → Val → Val)
    (xs : List Val) (init : Option Val) :
    iter fuel (.accumulate f (.vec .int xs) init) none = (do
      match ← idxIter xs none with
      | none => pure none
      | some (x, s) =>
        let a := match init with | none => x | some a => f a x
        pure (some (a, .tup [.val a, s]))) := rfl

private theorem repTakeDone (F : Nat) (it : Itr) (m n : JInt64)
    (st rest : Option St) (hn : n ≤ i64 0)
    (hs : splitCountState st m = .ok (n, rest)) :
    iter F (.take it m) st = .ok none := by
  rw [takeIter, hs]
  simp only [okBind, if_pos hn, pureOk]

private theorem repZero (F : Nat) (v : Val) (m : JInt64) :
    iter F (.take (.repeated v) m) (some (.tup [.int 0, .nothing])) = .ok none := by
  apply repTakeDone F (.repeated v) m (i64 0) _ (some .nothing)
  · change (i64 0).val ≤ (i64 0).val
    exact Int.le_refl _
  · rfl

private theorem repLitZero : (i64 0).val = 0 := litValue 0 (by omega)
private theorem repLitOne : (i64 1).val = 1 := litValue 1 (by omega)

private theorem repDecrement (n : Nat) (hn : (n + 1 : Int) ≤ IntTy.i64.max) :
    (i64 (n + 1 : Int) - i64 1).val = n := by
  have hn0 : (i64 (n : Int)).val = n := litValue _ (by
    change -(2^63) ≤ (n : Int) ∧ (n : Int) ≤ 2^63-1
    change (n + 1 : Int) ≤ 2^63-1 at hn
    omega)
  have hn1 : (i64 (n + 1 : Int)).val = n + 1 := litValue _ (by
    change -(2^63) ≤ (n + 1 : Int) ∧ (n + 1 : Int) ≤ 2^63-1
    change (n + 1 : Int) ≤ 2^63-1 at hn
    omega)
  change wrapInt .i64 ((i64 (n + 1 : Int)).val - (i64 1).val) = n
  rw [hn1, repLitOne, Int.add_sub_cancel]
  exact hn0

private theorem repNext (F : Nat) (v : Val) (m ni : JInt64) (k : Int)
    (hi : i64 k = ni) (hp : ¬ ni ≤ i64 0) :
    iter F (.take (.repeated v) m) (some (.tup [.int k, .nothing])) =
      .ok (some (v, .tup [.int (ni - i64 1).val, .nothing])) := by
  rw [takeIter]
  simp only [splitCountState, pureOk, okBind, hi]
  rw [if_neg hp]
  simp only [repeatedBase, okBind, pureOk]

private theorem repeatedStep (fuel : Nat) (x : Val) (n : JInt64)
    (k : Nat) (hk : (k : Int) ≤ 2^63-1) :
    iter fuel (.take (.repeated x) n) (some (.tup [.int k, .nothing])) =
      if k = 0 then .ok none else
      .ok (some (x, .tup [.int (k - 1 : Nat), .nothing])) := by
  cases k with
  | zero => simpa only [Int.natCast_zero, ↓reduceIte] using repZero fuel x n
  | succ k =>
    have hv : (i64 (k + 1 : Int)).val = k + 1 := litValue _ (by omega)
    have hd := repDecrement k (by exact hk)
    have hp : ¬ i64 (k + 1 : Int) ≤ i64 0 := by
      change ¬ (i64 (k + 1 : Int)).val ≤ (i64 0).val
      rw [hv, repLitZero]
      omega
    simpa only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      Int.natCast_add, Int.natCast_one, hd] using
      repNext fuel x n (i64 (k + 1 : Int)) (k + 1) rfl hp

private theorem repeatedRun (fuel budget k : Nat) (x : Val) (n : JInt64)
    (hk : (k : Int) ≤ 2^63-1) (hb : k ≤ budget) :
    runFrom (fun s => iter fuel (.take (.repeated x) n) (some s)) budget
      (if k = 0 then none else some (x, .tup [.int (k - 1 : Nat), .nothing])) =
      .ok (List.replicate k x) := by
  induction k generalizing budget with
  | zero => simp [runFrom]
  | succ k ih =>
    cases budget with
    | zero => omega
    | succ b =>
      simp only [Nat.add_eq_zero_iff, Nat.succ_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, runFrom, repeatedStep fuel x n k (by omega)]
      by_cases he : k = 0
      · subst k; simp [runFrom]
      · simp only [he, ↓reduceIte, okBind]
        have hh := ih b (by omega) (by omega)
        simp only [he, ↓reduceIte] at hh
        rw [hh]
        rfl

theorem repeatedNCorrect : RepeatedNCorrect := by
  intro x n fuel hn hf
  have hc : repeatedN x n = .ok (.take (.repeated x) n) := by
    have hz := litValue 0 (by omega)
    have hlt : ¬ (n < i64 0) := by change ¬ (n.val < (i64 0).val); omega
    simp [repeatedN, toIntSelf, take, mkTake, hlt]
  refine ⟨.take (.repeated x) n, hc, ?_, ?_⟩
  · have hnat : (n.val.toNat : Int) = n.val := Int.toNat_of_nonneg hn
    have hmax : (n.val.toNat : Int) ≤ 2^63-1 := by
      have := n.property.2
      change n.val ≤ 2^63-1 at this
      omega
    have h := repeatedRun fuel fuel n.val.toNat x n hmax (by omega)
    have hz := litValue 0 (by omega)
    have ho := litValue 1 (by omega)
    have hs : (n - i64 1).val = n.val - 1 := by
      change wrapInt .i64 (n.val - (i64 1).val) = _
      rw [ho]
      apply wrapInt_of_inRange
      change -(2^63) ≤ n.val - 1 ∧ n.val - 1 ≤ 2^63-1
      omega
    by_cases he : n.val = 0
    · have hle : n ≤ i64 0 := by change n.val ≤ (i64 0).val; rw [hz]; omega
      simp only [elems, repeatedIter, splitCountState, okBind, if_pos hle, pureOk,
        runFrom, he, Int.toNat_zero, List.replicate_zero]
    · have hle : ¬ (n ≤ i64 0) := by change ¬ (n.val ≤ (i64 0).val); rw [hz]; omega
      have hne : n.val.toNat ≠ 0 := by omega
      simpa only [elems, repeatedIter, splitCountState, okBind, if_neg hle, pureOk,
        hs, if_neg hne, Int.ofNat_sub (by omega : 1 ≤ n.val.toNat), Int.natCast_one, hnat] using h
  · rfl


private theorem idxAt (xs : List Val) (i : Nat) :
    idxIter xs (some (.int (i + 1))) =
      match xs.drop i with
      | [] => .ok none
      | x :: _ => .ok (some (x, .int (i + 2))) := by
  simp only [idxIter]
  split
  next h =>
    have hi : i < xs.length := by omega
    have hd : xs.drop i ≠ [] := by simpa using hi
    cases he : xs.drop i with
    | nil => contradiction
    | cons x rest =>
      have hx : xs.getD i .undef = x := by
        have := congrArg (fun l : List Val => l.getD 0 .undef) he
        simpa using this
      change Except.ok (some (xs.getD ((↑i + 1 - 1 : Int).toNat) .undef, St.int (↑i + 1 + 1))) =
        Except.ok (some (x, St.int (↑i + 2)))
      rw [show ((↑i + 1 - 1 : Int).toNat) = i by omega, hx]
      congr 3 <;> omega
  next h =>
    have hi : xs.length ≤ i := by omega
    simp [List.drop_eq_nil_iff.mpr hi]

private theorem accRun (f : Val → Val → Val) (init : Option Val)
    (xs rest : List Val) (i fuel budget : Nat) (a : Val)
    (hd : xs.drop i = rest) (hb : rest.length < budget) :
    runFrom (fun s => iter fuel (.accumulate f (.vec .int xs) init) (some s))
      budget (some (a, .tup [.val a, .int (i + 1)])) =
      .ok (a :: accSpec.accFrom f a rest) := by
  induction rest generalizing i budget a with
  | nil =>
    cases budget with
    | zero => simp at hb
    | succ b => simp only [runFrom, accIterNext, idxAt, hd, okBind, pureOk, accSpec.accFrom]
  | cons x rest ih =>
    cases budget with
    | zero => simp at hb
    | succ b =>
      have hd' : xs.drop (i + 1) = rest := by
        rw [← List.drop_drop, hd]
        rfl
      have hh := ih (i + 1) b (f a x) hd' (by simp only [List.length_cons] at hb; omega)
      simp only [runFrom, accIterNext, idxAt, hd, okBind, pureOk]
      have hcast : ((i + 1 : Nat) : Int) + 1 = (i : Int) + 2 := by omega
      rw [hcast] at hh
      rw [hh]
      rfl

theorem accumulateCorrect : AccumulateCorrect := by
  intro f init xs fuel hf _
  constructor
  · cases xs with
    | nil => simp only [elems, accIterStart, idxIter, List.length_nil, Int.natCast_zero,
        show ¬ (1 ≤ (0 : Nat)) by omega, ↓reduceIte, pureOk, okBind, accSpec, runFrom]
    | cons x xs =>
      have h := accRun f init (x :: xs) xs 1 fuel fuel
        (match init with | none => x | some a => f a x) (by rfl) (by simp only [List.length_cons] at hf; omega)
      cases init <;> simpa only [elems, accIterStart, idxIter, List.length_cons,
        show 1 ≤ xs.length + 1 by omega, ↓reduceIte, List.getD_cons_zero,
        pureOk, okBind, accSpec, Int.natCast_one, Int.reduceAdd] using h
  · rfl

end JuliaLean.Iterators
