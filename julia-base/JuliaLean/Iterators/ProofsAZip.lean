import JuliaLean.Iterators.Spec

namespace JuliaLean.Iterators
open JuliaLean

private theorem azOkBind {α β : Type} (a : α) (f : α → M β) :
    (Except.ok a >>= f) = f a := rfl
private theorem azPureOk {α : Type} (a : α) : (pure a : M α) = .ok a := rfl
attribute [local simp] azOkBind azPureOk
private theorem azErrBind {α β : Type} (e : Err) (f : α → M β) :
    (Except.error e >>= f) = .error e := rfl
attribute [local simp] azErrBind

set_option maxRecDepth 4096

namespace ProofsAList
private def nextAt (xs : List Val) (p : Nat) (st : Nat → St) : M (Option (Val × St)) :=
  match xs.drop p with
  | [] => .ok none
  | x :: _ => .ok (some (x, st (p+1)))

private theorem getD_head_drop (xs : List Val) (p : Nat) :
    xs.getD p .undef = (xs.drop p).headD .undef := by
  induction xs generalizing p with
  | nil => simp
  | cons x xs ih =>
    cases p with
    | zero => rfl
    | succ p => simpa using ih p

private theorem idxIter_at (xs : List Val) (p : Nat) :
    idxIter xs (some (.int (p+1))) = nextAt xs p (fun q => .int (q+1)) := by
  have hg := getD_head_drop xs p
  have hl := List.length_drop (i := p) (l := xs)
  simp only [idxIter, nextAt]
  have hnat : ((p : Int)+1-1).toNat = p := by omega
  rw [hnat]
  cases hd : xs.drop p with
  | nil =>
    simp only [hd, List.length_nil] at hl
    simp [show ¬ (1 ≤ (p : Int)+1 ∧ (p : Int)+1 ≤ xs.length) by omega]
  | cons x ys =>
    simp only [hd, List.length_cons] at hl
    simp only [show 1 ≤ (p : Int)+1 ∧ (p : Int)+1 ≤ xs.length by omega, ↓reduceIte]
    rw [hg,hd]
    simp only [List.headD_cons]
    congr 3

private theorem idxIter_start (xs : List Val) :
    idxIter xs none = nextAt xs 0 (fun q => .int (q+1)) := by
  cases xs <;> simp [idxIter, nextAt, List.getD]
end ProofsAList

private inductive AZTrace (f : Option St → M (Option (Val × St))) : Option St → List Val → Prop
  | nil {s} : f s = .ok none → AZTrace f s []
  | cons {s t x xs} : f s = .ok (some (x,t)) → AZTrace f (some t) xs → AZTrace f s (x::xs)

private theorem azTrace_rebase {f : Option St → M (Option (Val × St))} {s t xs}
    (he : f s = f t) (h : AZTrace f t xs) : AZTrace f s xs := by
  cases h with
  | nil h => exact .nil (he.trans h)
  | cons h ht => exact .cons (he.trans h) ht

private theorem azVecIter (fuel : Nat) (xs : List Val) (s : Option St) :
    iter fuel (.vec .int xs) s = idxIter xs s := rfl
private theorem azRevIter (fuel : Nat) (xs : List Val) (s : Option St) :
    iter fuel (.reverse (.vec .int xs)) s = revIdxIter xs s := rfl

private theorem azEnumIter (fuel : Nat) (it : Itr) (s : Option St) :
    iter fuel (.enumerate it) s = (do
      let (i,rest) ← splitCountState s (i64 1)
      match ← iter fuel it rest with
      | none => pure none
      | some (x,t) => pure (some (.tup [.int i.val,x], .tup [.int (i+i64 1).val,t]))) := rfl

private theorem azDownIter (fuel : Nat) (it : Itr) (s : Option St) :
    iter fuel (.revEnum it) s = (do
      let (i,rest) ← match s with
        | none => do pure (← len it, none)
        | some t => splitCountState (some t) (i64 0)
      match ← iter fuel it rest with
      | none => pure none
      | some (x,t) => pure (some (.tup [.int i.val,x], .tup [.int (i-i64 1).val,t]))) := rfl

private theorem azTrace_run {f : Option St → M (Option (Val × St))} {s xs}
    (h : AZTrace f s xs) : ∀ k, xs.length < k →
    (do runFrom (fun t => f (some t)) k (← f s)) = .ok xs := by
  induction h with
  | nil h => intro k hk; simp [h, runFrom]
  | @cons s t x xs h ht ih =>
    intro k hk
    cases k with
    | zero => simp at hk
    | succ k =>
      simp only [h, azOkBind, runFrom]
      have he := ih k (by simpa using hk)
      cases hn : f (some t) with
      | error e => simp [hn] at he
      | ok v =>
        simp only [hn, azOkBind] at he ⊢
        rw [he]
        rfl

private def azZipState : Option (St × St) → Option St
  | none => none
  | some (a,b) => some (.tup [a,b])

private theorem azZip_iter (fuel : Nat) (a b : Itr)
    (ha : ∀ s, (match s with | none => isdone0 a | some s => isdoneS a s) = .ok none)
    (hb : ∀ s, (match s with | none => isdone0 b | some s => isdoneS b s) = .ok none)
    (s : Option (St × St)) :
    iter fuel (.zip [a,b]) (azZipState s) = (do
      match ← iter fuel a (s.map Prod.fst) with
      | none => pure none
      | some (x,sa) =>
        match ← iter fuel b (s.map Prod.snd) with
        | none => pure none
        | some (y,sb) => pure (some (.tup [x,y], .tup [sa,sb]))) := by
  conv =>
    lhs
    unfold iter
  cases s with
  | none =>
    simp only [azZipState, List.map_cons, List.map_nil, zipIsdones, ha none, hb none,
      azOkBind, List.any_cons, List.any_nil, List.all_cons, List.all_nil]
    cases hia : iter fuel a none <;> cases hib : iter fuel b none <;>
      simp_all [zipInOrder]
    all_goals split <;> simp_all [zipInOrder]
    all_goals split <;> simp_all [zipInOrder]
  | some s =>
    rcases s with ⟨sa,sb⟩
    simp only [azZipState, List.map_cons, List.map_nil, zipIsdones,
      ha (some sa), hb (some sb), azOkBind, List.any_cons, List.any_nil, List.all_cons, List.all_nil]
    cases hia : iter fuel a (some sa) <;> cases hib : iter fuel b (some sb) <;>
      simp_all [zipInOrder]
    all_goals split <;> simp_all [zipInOrder]
    all_goals split <;> simp_all [zipInOrder]

private theorem azZip_trace (fuel : Nat) (a b : Itr)
    (ha : ∀ s, (match s with | none => isdone0 a | some s => isdoneS a s) = .ok none)
    (hb : ∀ s, (match s with | none => isdone0 b | some s => isdoneS b s) = .ok none)
    {s : Option (St × St)} {xs ys : List Val}
    (hx : AZTrace (iter fuel a) (s.map Prod.fst) xs)
    (hy : AZTrace (iter fuel b) (s.map Prod.snd) ys) :
    AZTrace (iter fuel (.zip [a,b])) (azZipState s)
      (List.zipWith (fun x y => .tup [x,y]) xs ys) := by
  induction xs generalizing s ys with
  | nil =>
    cases hx with
    | nil hx => exact .nil (by simp [azZip_iter fuel a b ha hb, hx])
  | cons x xs ih =>
    cases hx with
    | @cons _ sa _ _ hx hxs =>
      cases hy with
      | nil hy => exact .nil (by simp [azZip_iter fuel a b ha hb, hx, hy])
      | @cons _ sb y ys hy hys =>
        exact .cons (by simp [azZip_iter fuel a b ha hb, hx, hy])
          (ih (s := some (sa,sb)) hxs hys)

private theorem azTrace_nextAt (xs : List Val) (st : Nat → St)
    (f : Option St → M (Option (Val × St)))
    (hs : ∀ p, p ≤ xs.length → f (some (st p)) = ProofsAList.nextAt xs p st)
    (k : Nat) : ∀ p, (xs.drop p).length ≤ k → p ≤ xs.length →
    AZTrace f (some (st p)) (xs.drop p) := by
  induction k with
  | zero =>
    intro p hk hp
    have hd : xs.drop p = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hd]
    exact .nil (by rw [hs p hp]; simp [ProofsAList.nextAt, hd])
  | succ k ih =>
    intro p hk hp
    cases hd : xs.drop p with
    | nil => exact .nil (by rw [hs p hp]; simp [ProofsAList.nextAt, hd])
    | cons x ys =>
      have hdrop : xs.drop (p+1) = ys := by
        rw [← List.drop_drop, hd]
        rfl
      have hl := List.length_drop (i := p) (l := xs)
      simp only [hd, List.length_cons] at hl hk
      refine .cons (t := st (p+1)) (by rw [hs p hp]; simp [ProofsAList.nextAt, hd]) ?_
      simpa only [hdrop] using ih (p+1) (by simpa [hdrop] using (show ys.length ≤ k by omega)) (by omega)

private theorem azTrace_vec (fuel : Nat) (xs : List Val) :
    AZTrace (iter fuel (.vec .int xs)) none xs := by
  have ht := azTrace_nextAt xs (fun q => .int (q+1)) (iter fuel (.vec .int xs))
    (fun p _ => ProofsAList.idxIter_at xs p) xs.length 0 (by simp) (by omega)
  have he : iter fuel (.vec .int xs) none =
      iter fuel (.vec .int xs) (some (.int (0+1))) := by
    exact (ProofsAList.idxIter_start xs).trans (ProofsAList.idxIter_at xs 0).symm
  simpa only [List.drop_zero] using azTrace_rebase he ht

private theorem azRev_at (xs : List Val) (p : Nat) (hp : p ≤ xs.length) :
    revIdxIter xs (some (.int ((xs.length : Int)-p))) =
      ProofsAList.nextAt xs.reverse p (fun q => .int ((xs.length : Int)-q)) := by
  have hl := List.length_drop (i := p) (l := xs.reverse)
  have hg := ProofsAList.getD_head_drop xs.reverse p
  simp only [revIdxIter, ProofsAList.nextAt]
  cases hd : xs.reverse.drop p with
  | nil =>
    simp only [hd, List.length_nil, List.length_reverse] at hl
    simp [show (xs.length : Int)-p < 1 by omega]
  | cons x ys =>
    simp only [hd, List.length_cons, List.length_reverse] at hl
    have hb : p < xs.length := by omega
    have hn : ((xs.length : Int)-p-1).toNat = xs.length-1-p := by omega
    have hv : xs.getD (xs.length-1-p) .undef = x := by
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_reverse hb,
        ← List.getD_eq_getElem?_getD, hg, hd]
      rfl
    simp only [show ¬ ((xs.length : Int)-p < 1) by omega, ↓reduceIte, hn, hv, azPureOk]
    rw [show (xs.length : Int)-p-1 = (xs.length : Int)-(p+1 : Nat) by omega]

private theorem azRev_start (xs : List Val) :
    revIdxIter xs none = revIdxIter xs (some (.int xs.length)) := by
  by_cases h : xs.length = 0
  · simp [revIdxIter, h]
  · have hi : ((xs.length : Int)-1).toNat = xs.length-1 := by omega
    have hn : ((xs.length-1 : Nat) : Int) = (xs.length : Int)-1 := by omega
    simp [revIdxIter, show ¬ xs.length < 1 by omega,
      show ¬ (xs.length : Int) < 1 by omega, hi, hn]

private theorem azTrace_rev (fuel : Nat) (xs : List Val) :
    AZTrace (iter fuel (.reverse (.vec .int xs))) none xs.reverse := by
  have ht := azTrace_nextAt xs.reverse (fun q => .int ((xs.length : Int)-q))
    (iter fuel (.reverse (.vec .int xs)))
    (fun p hp => azRev_at xs p (by simpa using hp)) xs.length 0 (by simp) (by omega)
  have he : iter fuel (.reverse (.vec .int xs)) none =
      iter fuel (.reverse (.vec .int xs)) (some (.int ((xs.length : Int)-0))) := by
    simpa only [azRevIter, Int.sub_zero] using azRev_start xs
  simpa only [List.drop_zero] using azTrace_rebase he ht

private theorem azI64 (x : Int) (h : -(2^63) ≤ x ∧ x ≤ 2^63-1) :
    (i64 x).val = x := wrapInt_of_inRange .i64 x h

private theorem azZip_elems (fuel : Nat) (a b : Itr) (xs ys : List Val)
    (ha : ∀ s, (match s with | none => isdone0 a | some s => isdoneS a s) = .ok none)
    (hb : ∀ s, (match s with | none => isdone0 b | some s => isdoneS b s) = .ok none)
    (hx : AZTrace (iter fuel a) none xs) (hy : AZTrace (iter fuel b) none ys)
    (hf : xs.length < fuel) :
    elems fuel (.zip [a,b]) = .ok (List.zipWith (fun x y => .tup [x,y]) xs ys) := by
  exact azTrace_run (azZip_trace fuel a b ha hb (s := none) hx hy) fuel (by
    rw [List.length_zipWith]
    omega)

theorem zipCorrect : ZipCorrect := by
  intro xs ys fuel hxs hys hf
  constructor
  · exact azZip_elems fuel _ _ xs ys
      (fun s => by cases s <;> rfl) (fun s => by cases s <;> rfl)
      (azTrace_vec fuel xs) (azTrace_vec fuel ys) hf
  · have hx := azI64 xs.length (by unfold Fits at hxs; omega)
    have hy := azI64 ys.length (by unfold Fits at hys; omega)
    change (Except.ok (jmin (i64 ys.length) (i64 xs.length)) : M JInt64) =
      Except.ok (i64 (min xs.length ys.length))
    have hc : (i64 xs.length < i64 ys.length) ↔ xs.length < ys.length := by
      change (i64 xs.length).val < (i64 ys.length).val ↔ _
      rw [hx,hy]
      omega
    by_cases h : xs.length < ys.length
    · have hm : min (xs.length : Int) ys.length = xs.length := by omega
      simp [jmin, hc, h, hm]
    · have hm : min (xs.length : Int) ys.length = ys.length := by omega
      simp [jmin, hc, h, hm]

theorem zipReverse : ZipReverse := by
  intro xs ys fuel hxs hys hf
  have hx := azI64 xs.length (by unfold Fits at hxs; omega)
  have hy := azI64 ys.length (by unfold Fits at hys; omega)
  have he : i64 xs.length = i64 ys.length ↔ xs.length = ys.length := by
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      rw [hx,hy] at hv
      omega
    · intro h; rw [h]
  constructor
  · intro h
    refine ⟨.zip [.reverse (.vec .int xs), .reverse (.vec .int ys)], ?_, ?_⟩
    · simp [reverse, zipLengthsFiniteEqual, isz, len, reverseList, he, h]
    · rw [List.reverse_zipWith h]
      exact azZip_elems fuel _ _ xs.reverse ys.reverse
        (fun s => by cases s <;> rfl) (fun s => by cases s <;> rfl)
        (azTrace_rev fuel xs) (azTrace_rev fuel ys) (by simpa using hf)
  · intro h
    refine ⟨"Cannot reverse zipped iterators of unknown, infinite, or unequal lengths", ?_⟩
    have hh : i64 ys.length ≠ i64 xs.length := by
      intro hh; exact h (he.mp hh.symm)
    simp [reverse, zipLengthsFiniteEqual, isz, len, hh, jthrow]

private def azCountState (i : Int) (s : Option St) : Option St :=
  some (.tup (.int i :: s.toList))

private theorem azInc (i : Int) (hi : 0 ≤ i) (hb : i+1 ≤ 2^63-1) :
    (i64 i + i64 1).val = i+1 := by
  change (i64 ((i64 i).val + (i64 1).val)).val = _
  rw [azI64 i (by omega), azI64 1 (by omega)]
  exact azI64 (i+1) (by omega)

private theorem azDec (i : Int) (hi : 0 ≤ i) (hb : i ≤ 2^63-1) :
    (i64 i - i64 1).val = i-1 := by
  change (i64 ((i64 i).val - (i64 1).val)).val = _
  rw [azI64 i (by omega), azI64 1 (by omega)]
  exact azI64 (i-1) (by omega)

private theorem azEnum_trace (fuel : Nat) (it : Itr) {s xs}
    (h : AZTrace (iter fuel it) s xs) (i : Int)
    (hi : 0 ≤ i) (hb : i + xs.length + 1 ≤ 2^63-1) :
    AZTrace (iter fuel (.enumerate it)) (azCountState i s) (enumSpec i xs) := by
  induction h generalizing i with
  | @nil s h =>
    apply AZTrace.nil
    cases s <;> simp [azEnumIter, azCountState, splitCountState, h]
  | @cons s t x xs h ht ih =>
    refine AZTrace.cons ?_ (ih (i+1) (by omega) (by simp only [List.length_cons] at hb; omega))
    cases s <;> simp [azEnumIter, azCountState, splitCountState, h,
      azI64 i (by simp only [List.length_cons] at hb; omega), azInc i hi (by
        simp only [List.length_cons] at hb; omega)]

private def azDown : Int → List Val → List Val
  | _, [] => []
  | i, x::xs => .tup [.int i,x] :: azDown (i-1) xs

private theorem azDown_trace (fuel : Nat) (it : Itr) {s xs}
    (h : AZTrace (iter fuel it) s xs) (i : Int)
    (hi : xs.length ≤ i) (hb : i ≤ 2^63-1) :
    AZTrace (iter fuel (.revEnum it)) (azCountState i s) (azDown i xs) := by
  induction h generalizing i with
  | @nil s h =>
    apply AZTrace.nil
    cases s <;> simp [azDownIter, azCountState, splitCountState, h]
  | @cons s t x xs h ht ih =>
    refine AZTrace.cons ?_ (ih (i-1) (by simp only [List.length_cons] at hi; omega) (by omega))
    have hi0 : 0 ≤ i := by simp only [List.length_cons] at hi; omega
    cases s <;> simp [azDownIter, azCountState, splitCountState, h,
      azI64 i (by omega), azDec i hi0 hb]

private theorem azDown_append (xs ys : List Val) (i : Int) :
    azDown i (xs ++ ys) = azDown i xs ++ azDown (i-xs.length) ys := by
  induction xs generalizing i with
  | nil => simp [azDown]
  | cons x xs ih =>
    simp only [List.cons_append, azDown, ih, List.length_cons]
    rw [show i-1-(xs.length : Int) = i-↑(xs.length+1) by omega]

private theorem azDown_reverse (xs : List Val) (i : Int) :
    azDown (i+xs.length-1) xs.reverse = (enumSpec i xs).reverse := by
  induction xs generalizing i with
  | nil => simp [azDown, enumSpec]
  | cons x xs ih =>
    simp only [List.reverse_cons, List.length_cons, azDown_append, azDown, enumSpec,
      List.reverse_cons, List.nil_append]
    rw [show i + ↑(xs.length+1)-1 = (i+1)+xs.length-1 by omega, ih]
    simp only [List.length_reverse]
    rw [show (i+1)+(xs.length : Int)-1-xs.length = i by omega]

theorem enumerateCorrect : EnumerateCorrect := by
  intro xs fuel hxs hf
  have hx := azI64 xs.length (by unfold Fits at hxs; omega)
  have ht := azEnum_trace fuel (.vec .int xs) (azTrace_vec fuel xs) 1 (by omega) (by
    unfold Fits at hxs; omega)
  have hd := azDown_trace fuel (.reverse (.vec .int xs)) (azTrace_rev fuel xs)
    xs.length (by simp) (by unfold Fits at hxs; omega)
  constructor
  · have he : iter fuel (.enumerate (.vec .int xs)) none =
        iter fuel (.enumerate (.vec .int xs)) (azCountState 1 none) := by rfl
    have ht' := azTrace_rebase he ht
    apply azTrace_run ht' fuel
    have hl : ∀ xs i, (enumSpec i xs).length = xs.length := by
      intro xs; induction xs with
      | nil => intro i; rfl
      | cons x xs ih => intro i; simp [enumSpec, ih]
    simpa only [hl] using hf
  · refine ⟨rfl, .revEnum (.reverse (.vec .int xs)), rfl, ?_⟩
    have he : iter fuel (.revEnum (.reverse (.vec .int xs))) none =
        iter fuel (.revEnum (.reverse (.vec .int xs))) (azCountState xs.length none) := by
      simp [azDownIter, azCountState, splitCountState, len, hx]
    have hd' := azTrace_rebase he hd
    have hl : ∀ xs i, (azDown i xs).length = xs.length := by
      intro xs; induction xs with
      | nil => intro i; rfl
      | cons x xs ih => intro i; simp [azDown, ih]
    have hr := azTrace_run hd' fuel (by simpa only [hl, List.length_reverse] using hf)
    have hs : azDown xs.length xs.reverse = (enumSpec 1 xs).reverse := by
      have hs := azDown_reverse xs 1
      rw [show (1 : Int)+xs.length-1 = xs.length by omega] at hs
      exact hs
    exact hr.trans (congrArg Except.ok hs)

end JuliaLean.Iterators
