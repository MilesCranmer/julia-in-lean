import JuliaLean.Iterators.ProofsATake

set_option maxRecDepth 4096

namespace JuliaLean.Iterators

open JuliaLean

private theorem firstWrap (x : Int) (lo : -(2^63 : Int) ≤ x)
    (hi : x ≤ 2^63-1) : (i64 x).val = x :=
  wrapInt_of_inRange .i64 x ⟨lo, hi⟩

private theorem firstSub (m : Nat) (hm : m < 2^63-1) :
    (i64 (m+1) - i64 1).val = (m : Int) := by
  change wrapInt .i64 ((i64 (m+1)).val - (i64 1).val) = _
  rw [firstWrap (m+1) (by omega) (by omega), firstWrap 1 (by omega) (by omega)]
  have he : (m : Int) + 1 - 1 = m := by omega
  rw [he]
  exact wrapInt_of_inRange .i64 m ⟨by change -(2^63 : Int) ≤ (m : Int); omega,
    by change (m : Int) ≤ 2^63-1; omega⟩

private def firstState (m i : Nat) : St := .tup [.int m, .int (i+1)]

private theorem firstIterTake (lim : Nat) (it : Itr) (n : JInt64) (st : Option St) :
    iter lim (.take it n) st = (do
      let (m, rest) ← splitCountState st n
      if m ≤ i64 0 then pure none else
      match ← iter lim it rest with
      | none => pure none
      | some (x, s) => pure (some (x, .tup [.int (m-i64 1).val, s]))) := rfl

private theorem firstIterTuple (lim : Nat) (xs : List Val) (st : Option St) :
    iter lim (.tuple xs) st = idxIter xs st := rfl

private theorem firstTupleVec (fuel : Nat) (xs : List Val) (n : JInt64) (st : Option St) :
    iter fuel (.take (.tuple xs) n) st = iter fuel (.take (.vec .int xs) n) st := by
  simp only [firstIterTake, firstIterTuple, ProofsAList.iter_vec]

private theorem firstStep (xs : List Val) (n : JInt64) (fuel m i : Nat)
    (hm : m < 2^63-1) :
    iter fuel (.take (.tuple xs) n) (some (firstState (m+1) i)) =
      if i < xs.length then
        .ok (some (xs.getD i .undef, firstState m (i+1))) else .ok none := by
  have hw := firstWrap ((m+1 : Nat) : Int) (by omega) (by omega)
  have hs := firstSub m (by omega)
  rw [firstTupleVec]
  have ht := ProofsATake.iter_take_at xs fuel i n (i64 ((m+1 : Nat) : Int))
  simp only [hw] at ht
  rw [show firstState (m+1) i =
    .tup [.int ((m+1 : Nat) : Int), .int ((i : Int)+1)] from rfl, ht]
  unfold ProofsATake.takeAt
  rw [← ProofsAList.idxIter_at]
  have hp : ¬ (i64 ((m+1 : Nat) : Int)).val ≤ 0 := by rw [hw]; omega
  simp only [hp, ↓reduceIte, idxIter]
  have he : ((i : Int) + 1 - 1).toNat = i := by omega
  have hc : (1 ≤ (i : Int)+1 ∧ (i : Int)+1 ≤ xs.length) ↔ i < xs.length := by omega
  simp only [hc, he]
  by_cases hi : i < xs.length <;>
    simp only [hi, ↓reduceIte, Pure.pure, Except.pure, Bind.bind, Except.bind,
      Int.natCast_add, Int.natCast_one, hs, firstState]

private theorem firstZero (xs : List Val) (n : JInt64) (f i : Nat) :
    iter f (.take (.tuple xs) n) (some (firstState 0 i)) = .ok none := by
  unfold firstState
  rw [firstIterTake]
  simp only [splitCountState, Bind.bind, Except.bind, Pure.pure, Except.pure, Int.natCast_zero,
    show i64 0 ≤ i64 0 from Int.le_refl _, ↓reduceIte]

private theorem firstCopy (xs : List Val) (n : JInt64) (fuel m i f : Nat)
    (hm : m ≤ 2^63-1) (hf : xs.length - i < f) :
    (iter fuel (.take (.tuple xs) n) (some (firstState m i)) >>=
      copyFrom (fun s => iter fuel (.take (.tuple xs) n) (some s))
        f (min m (xs.length-i))) =
      .ok ((xs.drop i).take m) := by
  induction m generalizing i f with
  | zero => simp [firstZero, copyFrom, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | succ m ih =>
    rw [firstStep xs n fuel m i (by omega)]
    by_cases hi : i < xs.length
    · simp only [hi, ↓reduceIte, Bind.bind, Except.bind]
      cases f with
      | zero => omega
      | succ f =>
        have hd := List.drop_eq_getElem_cons hi
        have hg : xs.getD i .undef = xs[i] := by
          simp [List.getD, List.getElem?_eq_getElem hi]
        have he : min (m+1) (xs.length-i) = min m (xs.length-(i+1)) + 1 := by omega
        rw [he]
        simp only [copyFrom]
        rw [← bind_assoc, ih (i+1) f (by omega) (by omega)]
        simp only [hd, hg, List.take_succ_cons, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · have hd : xs.drop i = [] := List.drop_eq_nil_of_le (by omega)
      have he : xs.length-i = 0 := by omega
      simp [hi, he, copyFrom, hd, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem firstInitial (xs : List Val) (n : JInt64) (fuel : Nat)
    (hn : 0 ≤ n.val) :
    iter fuel (.take (.tuple xs) n) none =
      iter fuel (.take (.tuple xs) n) (some (firstState n.val.toNat 0)) := by
  rw [firstTupleVec, firstTupleVec, ProofsATake.iter_take_start]
  have ht := ProofsATake.iter_take_at xs fuel 0 n n
  have hs : firstState n.val.toNat 0 =
      .tup [.int n.val, .int (((0 : Nat) : Int)+1)] := by
    unfold firstState
    rw [Int.toNat_of_nonneg hn]
  rw [hs, ht]

private theorem firstTake (xs : List Val) (n : JInt64) (hn : 0 ≤ n.val) :
    take (.tuple xs) n = .ok (.take (.tuple xs) n) := by
  have he : toInt n = .ok n := by
    rcases n with ⟨v, h⟩
    simp [toInt, liftJ, JInt.convert, h]
  simp only [take, he, Bind.bind, Except.bind]
  unfold mkTake
  have h : ¬ n < i64 0 := by
    change ¬ n.val < (i64 0).val
    rw [firstWrap 0 (by omega) (by omega)]
    omega
  simp [h, Pure.pure, Except.pure]

private theorem firstCollectGeneral (it : Itr) (l : JInt64) (fuel : Nat)
    (hz : isz it = .hasLength) (ht : ieltype it = true) (hl : len it = .ok l) :
    collect fuel it = (do
      allocCheck l.val
      copyFrom (fun s => iter fuel it (some s)) fuel l.val.toNat
        (← iter fuel it none)) := by
  simp only [collect, hz, ht, hl, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rfl

private theorem firstMin (xs : List Val) (n : JInt64) (hn : 0 ≤ n.val)
    (hx : xs.length < 2^59) :
    (jmin (i64 xs.length) n).val = (min n.val.toNat xs.length : Nat) := by
  have hxw : (i64 xs.length).val = xs.length :=
    firstWrap xs.length (by omega) (by omega)
  unfold jmin
  split <;> rename_i h
  · have ht : n.val < (i64 xs.length).val := h
    rw [hxw] at ht
    omega
  · have ht : ¬ n.val < (i64 xs.length).val := h
    rw [hxw] at ht
    rw [hxw]
    omega

private theorem firstAlloc (k : Nat) (hkb : k < 2^59) : allocCheck (k : Int) = .ok () := by
    have hmod : (k : Int) % 2^64 = k := Int.emod_eq_of_lt (by omega) (by omega)
    unfold allocCheck
    split
    · rfl
    · rw [hmod]
      have hb : ¬ ((k : Int) ≥ maxIntVal - 1 ∨ (k : Int)*8 ≥ maxIntVal - 1) := by
        unfold maxIntVal
        omega
      simp only [hb, ↓reduceIte]
      rfl
private theorem firstCollectEval (it : Itr) (l : JInt64) (fuel k : Nat) (ys : List Val)
    (hz : isz it = .hasLength) (ht : ieltype it = true) (hl : len it = .ok l)
    (hk : l.val = (k : Int)) (ha : allocCheck (k : Int) = .ok ())
    (hc : (iter fuel it none >>= copyFrom (fun s => iter fuel it (some s)) fuel k) = .ok ys) :
    collect fuel it = .ok ys := by
  rw [firstCollectGeneral it l fuel hz ht hl, hk, ha]
  simpa only [Bind.bind, Except.bind, Int.toNat_natCast] using hc

private theorem firstNTupleReduce (xs : List Val) (n : JInt64) (fuel : Nat)
    (ht : take (.tuple xs) n = .ok (.take (.tuple xs) n)) :
    firstN fuel (.tuple xs) n = collect fuel (.take (.tuple xs) n) := by
  simp only [firstN, ht, Bind.bind, Except.bind]

theorem firstNTupleInt : FirstNTupleInt := by
  intro xs n fuel hn hxs hf
  have hx : xs.length < 2^59 := hxs
  let k := min n.val.toNat xs.length
  have hk : (jmin (i64 xs.length) n).val = (k : Int) := firstMin xs n hn hx
  have ha := firstAlloc k (by dsimp [k]; omega)
  have hc := firstCopy xs n fuel n.val.toNat 0 fuel
    (by have := n.property.2; change n.val ≤ 2^63-1 at this; omega) (by omega)
  simp only [Nat.sub_zero, List.drop_zero] at hc
  have hr : (iter fuel (.take (.tuple xs) n) none >>=
      copyFrom (fun s => iter fuel (.take (.tuple xs) n) (some s)) fuel k) =
      .ok (xs.take n.val.toNat) :=
    (congrArg (fun a => a >>=
      copyFrom (fun s => iter fuel (.take (.tuple xs) n) (some s)) fuel k)
      (firstInitial xs n fuel hn)).trans hc
  have hl : len (.take (.tuple xs) n) = .ok (jmin (i64 xs.length) n) := by
    simp [len, isz, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact (firstNTupleReduce xs n fuel (firstTake xs n hn)).trans
    (firstCollectEval (.take (.tuple xs) n) (jmin (i64 xs.length) n) fuel k
      (xs.take n.val.toNat) rfl rfl hl hk ha hr)

end JuliaLean.Iterators
