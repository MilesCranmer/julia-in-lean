import JuliaLean.Iterators.Spec

namespace JuliaLean.Iterators
open JuliaLean

set_option maxRecDepth 4096

private theorem partPure {α : Type} (a : α) : (pure a : M α) = .ok a := rfl

private theorem partBind {α β : Type} (a : α) (f : α → M β) :
    ((.ok a : M α) >>= f) = f a := rfl

private theorem partAssoc {α β γ : Type} (x : M α) (f : α → M β) (g : β → M γ) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
  cases x <;> rfl

private theorem partRunSucc (step : St → M (Option (Val × St))) (f : Nat) (x : Val) (s : St) :
    runFrom step (f+1) (some (x,s)) =
      (do let v ← step s
          let rest ← runFrom step f v
          pure (x :: rest)) := rfl

private theorem partSliceCount (a r : Nat) :
    ((r : Int)-((a : Int)+1)+1).toNat = r-a := by omega

private theorem partLit (x : Int) (h : -(2^63) ≤ x ∧ x ≤ 2^63-1) :
    (i64 x).val = x := wrapInt_of_inRange .i64 x h

private theorem partCount (L k i : Nat) (hk : 0 < k) :
    i < (L + k - 1) / k ↔ i * k < L := by
  have h := Nat.le_div_iff_mul_le hk (x := i + 1) (y := L + k - 1)
  rw [Nat.add_mul] at h
  simp only [Nat.one_mul] at h
  omega

private theorem partCount_le (L k : Nat) (hk : 0 < k) :
    (L + k - 1) / k ≤ L := by
  have h := partCount L k L hk
  have hm : L ≤ L * k := Nat.le_mul_of_pos_right L hk
  omega

private theorem partEnd (s : Int) (n : JInt64)
    (hs : 1 ≤ s) (hn : 1 ≤ n.val)
    (hb : s + n.val - 1 ≤ 2^63-1) :
    (i64 s + n - i64 1).val = s + n.val - 1 := by
  change wrapInt .i64 (wrapInt .i64 ((i64 s).val + n.val) - (i64 1).val) = _
  rw [partLit s (by omega), partLit 1 (by omega)]
  simp only [wrapInt, IntTy.signed, IntTy.bits]
  omega

private theorem partTake (xs : List Val) (a k : Nat) :
    (xs.drop a).take (min (a+k) xs.length - a) = (xs.drop a).take k := by
  by_cases h : a+k ≤ xs.length
  · rw [Nat.min_eq_left h]
    congr 1
    omega
  · rw [Nat.min_eq_right (by omega)]
    have hl : (xs.drop a).length = xs.length-a := List.length_drop
    rw [← hl, List.take_length]
    symm
    exact List.take_of_length_le (by rw [hl]; omega)

private theorem partIter (xs : List Val) (n : JInt64) (fuel : Nat) (s : Int) :
    iter fuel (.partition (.vec .int xs) n) (some (.int s)) =
      (if i64 xs.length < i64 s then pure none else
        let r := jmin (i64 s + n - i64 1) (i64 xs.length)
        if (i64 s).val < 1 then .error .oob else
        pure (some (.vec .int ((xs.drop ((i64 s).val-1).toNat).take
          (r.val-(i64 s).val+1).toNat), .int (r+i64 1).val))) := rfl

private theorem partStep (xs : List Val) (n : JInt64) (a fuel : Nat)
    (hn : 1 ≤ n.val) (hf : Fits xs) (ha : a ≤ xs.length)
    (hb : (a : Int) + n.val ≤ 2^63-1) :
    iter fuel (.partition (.vec .int xs) n) (some (.int ((a : Int)+1))) =
      if a < xs.length then
        .ok (some (.vec .int ((xs.drop a).take n.val.toNat),
          .int ((min (a+n.val.toNat) xs.length : Nat) + 1)))
      else .ok none := by
  have hlen : (i64 xs.length).val = xs.length := partLit _ (by unfold Fits at hf; omega)
  have hs : (i64 ((a : Int)+1)).val = (a : Int)+1 := partLit _ (by unfold Fits at hf; omega)
  have he := partEnd ((a : Int)+1) n (by omega) hn (by omega)
  have hk : (n.val.toNat : Int) = n.val := Int.toNat_of_nonneg (by omega)
  have hr : (jmin (i64 ((a : Int)+1) + n - i64 1) (i64 xs.length)).val =
      (min (a+n.val.toNat) xs.length : Nat) := by
    unfold jmin
    split <;> rename_i hc
    · rw [hlen]
      rw [Nat.min_eq_right]
      change (i64 xs.length).val < (i64 ((a : Int)+1) + n - i64 1).val at hc
      omega
    · rw [he]
      rw [Nat.min_eq_left]
      · omega
      · change ¬ (i64 xs.length).val < (i64 ((a : Int)+1) + n - i64 1).val at hc
        omega
  have hnext : (jmin (i64 ((a : Int)+1) + n - i64 1) (i64 xs.length) + i64 1).val =
      (min (a+n.val.toNat) xs.length : Nat) + 1 := by
    change wrapInt .i64 (_ + (i64 1).val) = _
    rw [hr, partLit 1 (by omega)]
    apply wrapInt_of_inRange
    change -(2^63) ≤ _ ∧ _ ≤ 2^63-1
    have hm := Nat.min_le_right (a+n.val.toNat) xs.length
    unfold Fits at hf
    omega
  rw [partIter]
  change (if (i64 xs.length).val < (i64 ((a : Int)+1)).val then _ else _) = _
  rw [hlen, hs]
  by_cases h : a < xs.length
  · rw [if_neg (by omega), if_pos h]
    simp only [show ¬ (a : Int)+1 < 1 by omega, ↓reduceIte, hs, hr, hnext]
    have ha' : (((a : Int)+1)-1).toNat = a := by omega
    have ht : (((min (a+n.val.toNat) xs.length : Nat) : Int) - ((a : Int)+1)+1).toNat =
        min (a+n.val.toNat) xs.length-a := partSliceCount a _
    simp only [ha', ht, partTake]
    rfl
  · rw [if_pos (by omega), if_neg h]
    rfl

private theorem partDone (xs : List Val) (n : JInt64) (fuel : Nat) (hf : Fits xs) :
    iter fuel (.partition (.vec .int xs) n) (some (.int ((xs.length : Int)+1))) = .ok none := by
  have hlen : (i64 xs.length).val = xs.length := partLit _ (by unfold Fits at hf; omega)
  have hs : (i64 ((xs.length : Int)+1)).val = (xs.length : Int)+1 :=
    partLit _ (by unfold Fits at hf; omega)
  rw [partIter]
  change (if (i64 xs.length).val < (i64 ((xs.length : Int)+1)).val then _ else _) = _
  rw [hlen, hs, if_pos (by omega)]
  rfl

private theorem partRun (xs : List Val) (n : JInt64) (fuel f i : Nat)
    (hn : 1 ≤ n.val) (hf : Fits xs)
    (hcount : (xs.length+n.val.toNat-1)/n.val.toNat-i ≤ f) :
    (do
      let v ← iter fuel (.partition (.vec .int xs) n)
        (some (.int ((min (i*n.val.toNat) xs.length : Nat)+1)))
      runFrom (fun s => iter fuel (.partition (.vec .int xs) n) (some s)) f v) =
    .ok ((List.range ((xs.length+n.val.toNat-1)/n.val.toNat-i)).map
      (fun j => .vec .int ((xs.drop ((i+j)*n.val.toNat)).take n.val.toNat))) := by
  have hk : 0 < n.val.toNat := by omega
  have hkn : (n.val.toNat : Int) = n.val := Int.toNat_of_nonneg (by omega)
  induction f generalizing i with
  | zero =>
    have hi : ¬ i < (xs.length+n.val.toNat-1)/n.val.toNat := by omega
    have he : xs.length ≤ i*n.val.toNat := by
      have := partCount xs.length n.val.toNat i hk
      omega
    simp only [Nat.min_eq_right he, partDone xs n fuel hf]
    have hz : (xs.length+n.val.toNat-1)/n.val.toNat-i = 0 := by omega
    simp only [hz, List.range_zero, List.map_nil]
    rfl
  | succ f ih =>
    by_cases hi : i < (xs.length+n.val.toNat-1)/n.val.toNat
    · have ha : i*n.val.toNat < xs.length := (partCount _ _ _ hk).mp hi
      have hb : ((i*n.val.toNat : Nat) : Int)+n.val ≤ 2^63-1 := by
        by_cases hz : i = 0
        · have hnmax : n.val ≤ 2^63-1 := n.property.2
          simpa only [hz, Nat.zero_mul, Int.natCast_zero, Int.zero_add] using hnmax
        · have hi1 : 1 ≤ i := by omega
          have hmul : n.val.toNat ≤ i*n.val.toNat := by
            have := Nat.mul_le_mul_right n.val.toNat hi1
            simpa using this
          unfold Fits at hf
          omega
      have hs := partStep xs n (i*n.val.toNat) fuel hn hf (by omega) hb
      rw [if_pos ha] at hs
      rw [Nat.min_eq_left (by omega), hs]
      rw [partBind, partRunSucc, ← partAssoc]
      have hc : (xs.length+n.val.toNat-1)/n.val.toNat-(i+1) ≤ f := by omega
      have hnxt : i*n.val.toNat+n.val.toNat = (i+1)*n.val.toNat := by
        simp [Nat.add_mul]
      rw [hnxt]
      have hh := ih (i+1) hc
      change (do
        let v ← iter fuel (.partition (.vec .int xs) n)
          (some (.int ((min ((i+1)*n.val.toNat) xs.length : Nat)+1)))
        runFrom (fun s => iter fuel (.partition (.vec .int xs) n) (some s)) f v) = _ at hh
      rw [hh]
      have hq : (xs.length+n.val.toNat-1)/n.val.toNat-i =
          ((xs.length+n.val.toNat-1)/n.val.toNat-(i+1))+1 := by omega
      rw [hq, List.range_succ_eq_map]
      simp only [partBind, partPure, List.map_cons, List.map_map, Nat.add_zero]
      apply congrArg Except.ok
      apply congrArg (List.cons (Val.vec .int ((xs.drop (i*n.val.toNat)).take n.val.toNat)))
      apply List.map_congr_left
      intro j hj
      exact congrArg (fun z : Nat => Val.vec .int ((xs.drop (z*n.val.toNat)).take n.val.toNat))
        (by omega : i+1+j = i+Nat.succ j)
    · have he : xs.length ≤ i*n.val.toNat := by
        have := partCount xs.length n.val.toNat i hk
        omega
      simp only [Nat.min_eq_right he, partDone xs n fuel hf]
      have hz : (xs.length+n.val.toNat-1)/n.val.toNat-i = 0 := by omega
      simp only [hz, List.range_zero, List.map_nil]
      rfl

private theorem partCeil (L k d : Nat) (hk : 0 < k)
    (hd0 : d*k ≤ L) (hd1 : L < d*k+k) :
    (L+k-1)/k = if d*k = L then d else d+1 := by
  split <;> rename_i he
  · apply Nat.div_eq_of_lt_le
    · omega
    · simp only [Nat.add_mul, Nat.one_mul]
      omega
  · apply Nat.div_eq_of_lt_le
    · simp only [Nat.add_mul, Nat.one_mul]
      omega
    · simp only [Nat.add_mul, Nat.one_mul]
      omega

private theorem partNatLit (d : Nat) (hd : d < 2^60) : (i64 d).val = d :=
  partLit _ (by omega)

private theorem partAddZero (x : JInt64) : x + i64 0 = x := by
  apply Subtype.ext
  change wrapInt .i64 (x.val+(i64 0).val) = x.val
  rw [partLit 0 (by omega), Int.add_zero]
  exact wrapInt_of_inRange .i64 _ x.property

private theorem partAddOne (d : Nat) (hd : d < 2^59) :
    i64 d + i64 1 = i64 (d+1 : Nat) := by
  apply Subtype.ext
  change wrapInt .i64 ((i64 d).val+(i64 1).val) = (i64 (d+1 : Nat)).val
  rw [partNatLit d (by omega), partLit 1 (by omega), partNatLit (d+1) (by omega)]
  apply wrapInt_of_inRange
  change -(2^63) ≤ _ ∧ _ ≤ 2^63-1
  omega

private theorem partCld (L : Nat) (n : JInt64) (hL : L < 2^59) (hn : 1 ≤ n.val) :
    JInt.cld (i64 L) n = .ok (i64 (((L : Int)+n.val-1)/n.val)) := by
  let k := n.val.toNat
  let d := L/k
  have hk : 0 < k := by dsimp [k]; omega
  have hki : (k : Int) = n.val := Int.toNat_of_nonneg (by omega)
  have hd0 : d*k ≤ L := by
    have := Nat.mul_div_le L k
    simpa [d, Nat.mul_comm] using this
  have hd1 : L < (d+1)*k := by
    have := Nat.lt_mul_div_succ L hk
    simpa [d, Nat.mul_comm] using this
  simp only [Nat.add_mul, Nat.one_mul] at hd1
  have hd : d ≤ L := Nat.div_le_self L k
  have hdi : 0 ≤ (d : Int) ∧ (d : Int) ≤ (L : Int) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr hd⟩
  have hlit : (i64 L).val = L := partNatLit _ (by omega)
  have hdlit : (i64 d).val = d := partNatLit _ (by omega)
  have hdiv : JInt.div (i64 L) n = .ok (i64 d) := by
    have hz : n.val ≠ 0 := by omega
    have hov : ¬ (IntTy.i64.signed ∧ (i64 L).val = IntTy.i64.min ∧ n.val = -1) := by
      intro h
      omega
    have htd : (L : Int).tdiv n.val = (d : Int) := by
      rw [Int.tdiv_eq_ediv, if_pos (Or.inl (by omega)), Int.add_zero, ← hki]
      exact (Int.natCast_ediv L k).symm
    simp only [JInt.div, hlit, hz, ↓reduceIte]
    rw [if_neg (by intro h; omega), htd]
    rfl
  have hprod : (i64 d * n).val = (d*k : Nat) := by
    change wrapInt .i64 ((i64 d).val*n.val) = _
    rw [hdlit, ← hki, ← Int.natCast_mul]
    apply wrapInt_of_inRange
    change -(2^63) ≤ _ ∧ _ ≤ 2^63-1
    omega
  have hqcast : (((L+k-1)/k : Nat) : Int) = ((L : Int)+n.val-1)/n.val := by
    rw [Int.natCast_ediv]
    have hnum : ((L+k-1 : Nat) : Int) = (L : Int)+n.val-1 := by omega
    rw [hnum, hki]
  have hcld : JInt.cld (i64 L) n =
      .ok (i64 d + JInt.lit .i64
        (if (¬ IntTy.i64.signed ∨ ((i64 L).val > 0 ↔ n.val > 0)) ∧
          (i64 d * n).val ≠ (i64 L).val then 1 else 0)) := by
    simp only [JInt.cld, hdiv]
    rfl
  rw [hcld, ← hqcast]
  have hceil := partCeil L k d hk hd0 hd1
  by_cases he : d*k = L
  · have hq : (L+k-1)/k = d := by simpa only [if_pos he] using hceil
    rw [hq]
    have hc : ¬ ((¬ IntTy.i64.signed ∨ ((i64 L).val > 0 ↔ n.val > 0)) ∧
        (i64 d*n).val ≠ (i64 L).val) := by rw [hprod, hlit, he]; simp
    rw [if_neg hc]
    apply congrArg Except.ok
    exact partAddZero (i64 d)
  · have hq : (L+k-1)/k = d+1 := by simpa only [if_neg he] using hceil
    rw [hq]
    have hc : (¬ IntTy.i64.signed ∨ ((i64 L).val > 0 ↔ n.val > 0)) ∧
        (i64 d*n).val ≠ (i64 L).val := by
      rw [hprod, hlit]
      constructor
      · right
        omega
      · omega
    rw [if_pos hc]
    apply congrArg Except.ok
    exact partAddOne d (by omega)

theorem partitionVectorCorrect : PartitionVectorCorrect := by
  intro xs n fuel hn hf hfu
  have hc : partition (.vec .int xs) n = .ok (.partition (.vec .int xs) n) := by
    have ht : toInt n = .ok n := by
      simp only [toInt, JInt.convert, dif_pos n.property, liftJ]
    simp only [partition, show ¬ n.val < 1 by omega, ↓reduceIte, ht]
    rfl
  refine ⟨.partition (.vec .int xs) n, hc, ?_, ?_⟩
  · have hk : 0 < n.val.toNat := by omega
    have hc' := partCount_le xs.length n.val.toNat hk
    have hr := partRun xs n fuel fuel 0 hn hf (by omega)
    have hi : iter fuel (.partition (.vec .int xs) n) none =
        iter fuel (.partition (.vec .int xs) n) (some (.int 1)) := rfl
    simp only [Nat.zero_mul, Nat.zero_add, Nat.zero_min, Int.natCast_zero,
      Int.zero_add, Nat.sub_zero] at hr
    unfold elems
    rw [hi]
    rw [hr]
    simp only [chunksSpec, List.map_map, Function.comp_def]
  · have hl : len (.partition (.vec .int xs) n) =
        liftJ (JInt.cld (i64 xs.length) n) := rfl
    rw [hl, partCld xs.length n hf hn]
    rfl

end JuliaLean.Iterators
