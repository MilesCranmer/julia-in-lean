import JuliaLean.ArrayOps.PureProps

namespace JuliaLean.ArrayOps

open JuliaLean

@[simp] private theorem pure_bind_ok (x : α) (f : α → Jl β) :
    ((Except.ok x : Jl α) >>= f) = f x := rfl

@[simp] private theorem pure_bind_error (e : JlError) (f : α → Jl β) :
    ((Except.error e : Jl α) >>= f) = .error e := rfl

@[simp] private theorem pure_map_ok (f : α → β) (x : α) :
    (Except.ok x : Jl α).map f = .ok (f x) := rfl

@[simp] private theorem pure_map_error (f : α → β) (e : JlError) :
    (Except.error e : Jl α).map f = .error e := rfl

@[simp] private theorem pure_return (x : α) : (pure x : Jl α) = .ok x := rfl

@[simp] private theorem pure_raise (e : JlError) : (throw e : Jl α) = .error e := rfl

private theorem pure_wrap (x : Int) (h : IntTy.i64.min ≤ x ∧ x ≤ IntTy.i64.max) :
    (JInt.wrap .i64 x).val = x := wrapInt_of_inRange .i64 x h

private theorem pure_min : IntTy.i64.min = -9223372036854775808 := by decide
private theorem pure_max : IntTy.i64.max = 9223372036854775807 := by decide
private theorem pure_limit : (2 : Nat) ^ 62 = 4611686018427387904 := by decide

private theorem pure_read [Inhabited α] (p q : List α) (x : α) :
    (p ++ x :: q)[p.length]! = x := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
  simp

private theorem pure_set (p q : List α) (x y : α) :
    (p ++ x :: q).set p.length y = p ++ y :: q := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

private theorem pure_reverse_short (m : List α) (h : m.length ≤ 1) : m.reverse = m := by
  cases m with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys => simp only [List.length_cons] at h; omega

private theorem pure_swap_segment [Inhabited α] (k : Nat) :
    ∀ (p m q : List α) (i r : Int),
      i = (p.length : Int) + 1 → r = (p.length : Int) + m.length →
      (m.length = 2 * k ∨ m.length = 2 * k + 1) →
      swapLoop (p ++ m ++ q) i r k = p ++ m.reverse ++ q := by
  induction k with
  | zero =>
    intro p m q i r hi hr hm
    have hlen : m.length ≤ 1 := by omega
    rw [swapLoop, pure_reverse_short m hlen]
  | succ k ih =>
    intro p m q i r hi hr hm
    cases m with
    | nil => simp only [List.length_nil] at hm; omega
    | cons x xs =>
      rcases List.eq_nil_or_concat xs with rfl | ⟨mid, y, rfl⟩
      · simp only [List.length_cons, List.length_nil] at hm; omega
      · simp only [List.concat_eq_append] at hr hm ⊢
        have hm' : mid.length = 2 * k ∨ mid.length = 2 * k + 1 := by
          simp only [List.length_cons, List.length_append, List.length_nil] at hm
          omega
        have hi' : (i - 1).toNat = p.length := by omega
        have hr' : (r - 1).toNat = (p ++ x :: mid).length := by
          simp only [List.length_cons, List.length_append, List.length_nil] at hr ⊢
          omega
        have hreadi : (p ++ (x :: (mid ++ [y])) ++ q)[(i - 1).toNat]! = x := by
          rw [hi']; simpa only [List.append_assoc, List.cons_append] using
            pure_read p ((mid ++ [y]) ++ q) x
        have hreadr : (p ++ (x :: (mid ++ [y])) ++ q)[(r - 1).toNat]! = y := by
          rw [hr']; simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            pure_read (p ++ x :: mid) q y
        rw [swapLoop, hreadi, hreadr, hi']
        have hs₁ : (p ++ (x :: (mid ++ [y])) ++ q).set p.length y =
            (p ++ y :: mid) ++ y :: q := by
          simpa only [List.append_assoc, List.cons_append, List.nil_append] using
            pure_set p ((mid ++ [y]) ++ q) x y
        rw [hs₁]
        have hr'' : (r - 1).toNat = (p ++ y :: mid).length := by
          simp only [List.length_append, List.length_cons] at hr' ⊢
          exact hr'
        rw [hr'', pure_set]
        have hform : (p ++ y :: mid) ++ x :: q = (p ++ [y]) ++ mid ++ x :: q := by
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        rw [hform, ih (p ++ [y]) mid (x :: q) (i + 1) (r - 1)
          (by simp only [List.length_append, List.length_singleton]; omega)
          (by simp only [List.length_append, List.length_cons, List.length_nil] at hr ⊢; omega)
          hm']
        simp [List.reverse_append, List.append_assoc]

private theorem pure_reverse_window [Inhabited α] (v : List α) (s n : Int)
    (hs : 1 ≤ s) (hsn : s ≤ n) (hn : n ≤ v.length) :
    swapLoop v s n (midpoint s (n - 1) - s + 1).toNat =
      reverseWindow v s.toNat n.toNat := by
  let a := s.toNat - 1
  let b := n.toNat + 1 - s.toNat
  let p := v.take a
  let m := (v.drop a).take b
  let q := v.drop n.toNat
  have hab : a + b = n.toNat := by dsimp [a, b]; omega
  have hp : p.length = a := by dsimp [p]; rw [List.length_take]; omega
  have hm : m.length = b := by
    dsimp [m]
    simp only [List.length_take, List.length_drop]
    omega
  have hv : v = p ++ m ++ q := by
    dsimp [p, m, q]
    calc
      v = v.take a ++ v.drop a := (List.take_append_drop a v).symm
      _ = v.take a ++ ((v.drop a).take b ++ (v.drop a).drop b) := by
        exact congrArg (fun xs => v.take a ++ xs) (List.take_append_drop b (v.drop a)).symm
      _ = _ := by simp only [List.drop_drop, hab, List.append_assoc]
  have hk : b = 2 * (midpoint s (n - 1) - s + 1).toNat ∨
      b = 2 * (midpoint s (n - 1) - s + 1).toNat + 1 := by
    dsimp [b, midpoint]
    omega
  have h := pure_swap_segment (midpoint s (n - 1) - s + 1).toNat p m q s n
    (by rw [hp]; dsimp [a]; omega)
    (by rw [hp, hm]; dsimp [a, b]; omega)
    (by rw [hm]; exact hk)
  rw [← hv] at h
  exact h

theorem reverseBangSpec : ReverseBangSpec := by
  intro α _ s t v start stop _ hs₁ hs₂ hn₁ hn₂
  have hs : IntTy.i64.min ≤ start.val ∧ start.val ≤ IntTy.i64.max := ⟨hs₁, hs₂⟩
  have hn : IntTy.i64.min ≤ stop.val ∧ stop.val ≤ IntTy.i64.max := ⟨hn₁, hn₂⟩
  simp only [reverseBang, toInt, JInt.convert, dite_eq_left hs, dite_eq_left hn,
    pure_bind_ok, pure_return]
  constructor
  · intro h
    rw [if_neg (by omega)]
  · intro h₁ h₂ h₃
    by_cases hlt : start.val < stop.val
    · rw [if_pos hlt, if_neg (by omega), if_neg (by omega)]
      exact congrArg Except.ok (pure_reverse_window v start.val stop.val h₁ h₂ h₃)
    · have heq : stop.val = start.val := by omega
      rw [if_neg (by omega)]
      have h := pure_reverse_window v start.val stop.val h₁ h₂ h₃
      have hk : (midpoint start.val (stop.val - 1) - start.val + 1).toNat = 0 := by
        dsimp [midpoint]; omega
      rw [hk, swapLoop] at h
      exact congrArg Except.ok h

theorem copytoAliasSpec : CopytoAliasSpec := by
  intro α s t u a doffs soffs n _
  constructor
  · rfl
  · intro hd hs hn hdn hsn
    have hdz : doffs.val - 1 ≥ 0 := by omega
    have hnz : n.val ≥ 0 := by omega
    have hadd : (doffs.val - 1).toNat + n.val.toNat = (doffs.val - 1 + n.val).toNat := by omega
    simp only [copyto, Option.getD_none]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), hadd]

theorem linearCartesianRoundTrip : LinearCartesianRoundTrip := by
  intro n i
  have hi : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := i.property
  have hconv : toIndexGeneric i = .ok i := by
    simp only [toIndexGeneric, toInt, JInt.convert, dif_pos hi]
  simp only [cartesianGet, linearGet, hconv, pure_bind_ok, pure_return]
  by_cases h : 1 ≤ i.val ∧ i.val ≤ n <;>
    simp [h, linearOfCartesian]

private theorem pure_getAt_map (a : List α) (i : JInt64) :
    (getAt a i).map some =
      if 1 ≤ i.val ∧ i.val ≤ a.length then .ok a[(i.val - 1).toNat]?
      else .error .boundsError := by
  by_cases h : 1 ≤ i.val ∧ i.val ≤ a.length
  · simp only [getAt, dite_eq_left h, pure_map_ok, ite_eq_left h,
      List.getElem?_eq_getElem (by omega : (i.val - 1).toNat < a.length)]
  · simp [getAt, h]

theorem getindexCheckbounds : GetindexCheckbounds := by
  intro α t v i hv hi
  by_cases hr : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max
  · have hw : (JInt.wrap .i64 i.val).val = i.val := pure_wrap _ hr
    simp only [getindex, toIndexArray, toInt, JInt.convert, dite_eq_left hr]
    split <;> simp [pure_getAt_map, checkboundsInt, hw]
  · rcases hi with ht | hi
    · subst t
      have hb := i.property
      have hneg : (JInt.wrap .i64 i.val).val < 1 := by
        simp [JInt.wrap, wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hr hb ⊢
        omega
      have hout : ¬ (1 ≤ i.val ∧ i.val ≤ v.length) := by
        simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hr hb
        omega
      have hbad : ¬ (1 ≤ (JInt.wrap .i64 i.val).val ∧ (JInt.wrap .i64 i.val).val ≤ v.length) := by omega
      simp [getindex, toIndexArray, getAt, hbad, checkboundsInt, hout]
    · exact False.elim (hr hi)

private theorem pure_repeat_length (v : List α) (n : Nat) :
    (v.flatMap fun x => List.replicate n x).length = v.length * n := by
  induction v with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul, Nat.add_comm]

private theorem pure_checked_run (x y : JInt64) (result : Jl α) :
    (checkedMul64 x y >>= fun _ => result) =
      if IntTy.i64.min ≤ x.val * y.val ∧ x.val * y.val ≤ IntTy.i64.max
      then result else .error (.overflowError "checked_mul") := by
  unfold checkedMul64
  split <;> rfl

private theorem pure_repeat_nonneg (v : List α) (inner outer : JInt64)
    (hi : 0 ≤ inner.val) (ho : 0 ≤ outer.val) :
    repeatVec v (some inner) (some outer) =
      (do
        let _ ← checkedMul64 (JInt.wrap .i64 v.length) inner
        let w ← pure (v.flatMap fun x => List.replicate inner.val.toNat x)
        let _ ← checkedMul64 (JInt.wrap .i64 w.length) outer
        pure (List.flatten (List.replicate outer.val.toNat w))) := by
  rw [repeatVec.eq_1]
  generalize (JInt.wrap .i64) = wrap
  generalize checkedMul64 = mul
  simp only [decide_eq_false (Int.not_lt_of_ge hi), decide_eq_false (Int.not_lt_of_ge ho),
    Bool.false_eq_true, ↓reduceIte]

private theorem pure_checked_pair (x y z w : JInt64) (result : Jl α) :
    (checkedMul64 x y >>= fun _ => checkedMul64 z w >>= fun _ => result) =
      if IntTy.i64.min ≤ x.val * y.val ∧ x.val * y.val ≤ IntTy.i64.max then
        if IntTy.i64.min ≤ z.val * w.val ∧ z.val * w.val ≤ IntTy.i64.max
        then result else .error (.overflowError "checked_mul")
      else .error (.overflowError "checked_mul") := by
  rw [pure_checked_run, pure_checked_run]

private theorem pure_drop_pure (r : Jl δ) (x : α) (f : α → Jl β) :
    (r >>= fun _ => (pure x >>= f)) = (r >>= fun _ => f x) := by
  cases r <;> rfl

private theorem pure_repeat_eval (v : List α) (inner outer : JInt64)
    (hi : 0 ≤ inner.val) (ho : 0 ≤ outer.val) :
    repeatVec v (some inner) (some outer) =
      if IntTy.i64.min ≤ (JInt.wrap .i64 v.length).val * inner.val ∧
          (JInt.wrap .i64 v.length).val * inner.val ≤ IntTy.i64.max then
        if IntTy.i64.min ≤ (JInt.wrap .i64
            (v.flatMap fun x => List.replicate inner.val.toNat x).length).val * outer.val ∧
            (JInt.wrap .i64
              (v.flatMap fun x => List.replicate inner.val.toNat x).length).val * outer.val ≤ IntTy.i64.max
        then .ok (List.flatten (List.replicate outer.val.toNat
          (v.flatMap fun x => List.replicate inner.val.toNat x)))
        else .error (.overflowError "checked_mul")
      else .error (.overflowError "checked_mul") := by
  rw [pure_repeat_nonneg v inner outer hi ho, pure_drop_pure]
  simp only [pure_return]
  rw [pure_checked_pair]

theorem repeatSpec : RepeatSpec := by
  intro α v inner outer hv hi ho
  rw [pure_limit] at hv
  have hvRange : IntTy.i64.min ≤ (v.length : Int) ∧ (v.length : Int) ≤ IntTy.i64.max := by
    simp only [pure_min, pure_max]
    omega
  have hvWrap : (JInt.wrap .i64 v.length).val = v.length := pure_wrap _ hvRange
  have hprod : 0 ≤ (v.length : Int) * inner.val := Int.mul_nonneg (by omega) hi
  have hminzero : IntTy.i64.min ≤ 0 := by decide
  have hprodMin : IntTy.i64.min ≤ (v.length : Int) * inner.val :=
    Int.le_trans hminzero hprod
  have hlen : ((v.flatMap fun x => List.replicate inner.val.toNat x).length : Int) =
      (v.length : Int) * inner.val := by
    rw [pure_repeat_length]
    simp [Int.toNat_of_nonneg hi]
  rw [pure_repeat_eval v inner outer hi ho]
  simp only [hvWrap]
  by_cases h₁ : (v.length : Int) * inner.val ≤ IntTy.i64.max
  · have hp := And.intro hprodMin h₁
    rw [if_pos hp]
    have hwRange : IntTy.i64.min ≤
        ((v.flatMap fun x => List.replicate inner.val.toNat x).length : Int) ∧
        ((v.flatMap fun x => List.replicate inner.val.toNat x).length : Int) ≤ IntTy.i64.max := by
      rw [hlen]; exact hp
    have hwWrap : (JInt.wrap .i64
        (v.flatMap fun x => List.replicate inner.val.toNat x).length).val =
        (v.length : Int) * inner.val := by
      rw [show (JInt.wrap .i64
        (v.flatMap fun x => List.replicate inner.val.toNat x).length).val =
        ((v.flatMap fun x => List.replicate inner.val.toNat x).length : Int) from
          pure_wrap _ hwRange, hlen]
    rw [hwWrap]
    have hMin : IntTy.i64.min ≤ (v.length : Int) * inner.val * outer.val :=
      Int.le_trans hminzero (Int.mul_nonneg hprod ho)
    by_cases h₂ : (v.length : Int) * inner.val * outer.val ≤ IntTy.i64.max <;>
      simp only [h₁, h₂, hMin, and_self, true_and, and_false, ↓reduceIte, pure_bind_ok,
        pure_bind_error, pure_return]
  · simp [h₁]

private theorem pure_reverse_parts [Inhabited α] (p m q : List α)
    (hlen : (p ++ m ++ q).length < 2 ^ 62) :
    reverseBang (p ++ m ++ q) (JInt.wrap .i64 ((p.length : Int) + 1))
      (JInt.wrap .i64 ((p.length : Int) + m.length)) = .ok (p ++ m.reverse ++ q) := by
  have hlen' : p.length + m.length + q.length < 2 ^ 62 := by simpa [Nat.add_assoc] using hlen
  have hs : IntTy.i64.min ≤ (p.length : Int) + 1 ∧
      (p.length : Int) + 1 ≤ IntTy.i64.max := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  have hn : IntTy.i64.min ≤ (p.length : Int) + m.length ∧
      (p.length : Int) + m.length ≤ IntTy.i64.max := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  have hsval : (JInt.wrap .i64 ((p.length : Int) + 1)).val = (p.length : Int) + 1 :=
    pure_wrap _ hs
  have hnval : (JInt.wrap .i64 ((p.length : Int) + m.length)).val = (p.length : Int) + m.length :=
    pure_wrap _ hn
  have hspec := reverseBangSpec α .i64 .i64 (p ++ m ++ q)
    (JInt.wrap .i64 ((p.length : Int) + 1)) (JInt.wrap .i64 ((p.length : Int) + m.length))
    hlen (by rw [hsval]; exact hs.1) (by rw [hsval]; exact hs.2)
    (by rw [hnval]; exact hn.1) (by rw [hnval]; exact hn.2)
  by_cases hm : m = []
  · subst m
    simpa using hspec.1 (by rw [hsval, hnval]; simp only [List.length_nil, Int.natCast_zero]; omega)
  · have hmpos : 0 < m.length := List.length_pos_iff.mpr hm
    have heq := hspec.2 (by rw [hsval]; omega) (by rw [hsval, hnval]; omega)
      (by rw [hnval]; simp only [List.length_append]; omega)
    rw [hsval, hnval] at heq
    have hdrop : (p ++ m ++ q).drop (p.length + m.length) = q := by
      rw [← List.length_append, List.drop_left]
    have hwin : reverseWindow (p ++ m ++ q) (((p.length : Int) + 1).toNat)
        (((p.length : Int) + m.length).toNat) = p ++ m.reverse ++ q := by
      have hsNat : ((p.length : Int) + 1).toNat = p.length + 1 := by omega
      have hnNat : ((p.length : Int) + m.length).toNat = p.length + m.length := by omega
      simp only [reverseWindow, hsNat, hnNat, Nat.add_sub_cancel]
      rw [show p.length + m.length + 1 - (p.length + 1) = m.length by omega, hdrop]
      simp only [List.append_assoc, List.take_left, List.drop_left]
    simpa only [hwin] using heq

private theorem pure_reverse_prefix [Inhabited α] (a b : List α)
    (h : (a ++ b).length < 2 ^ 62) :
    reverseBang (a ++ b) (JInt.lit .i64 1) (JInt.wrap .i64 a.length) =
      .ok (a.reverse ++ b) := by
  simpa only [List.nil_append, List.length_nil, Int.natCast_zero, Int.zero_add, JInt.lit] using
    pure_reverse_parts ([] : List α) a b (by simpa only [List.nil_append] using h)

private theorem pure_reverse_suffix [Inhabited α] (a b : List α)
    (h : (a ++ b).length < 2 ^ 62) :
    reverseBang (a ++ b) (JInt.wrap .i64 ((a.length : Int) + 1))
      (JInt.wrap .i64 ((a.length : Int) + b.length)) = .ok (a ++ b.reverse) := by
  simpa only [List.append_nil] using
    pure_reverse_parts a b ([] : List α) (by simpa only [List.append_nil] using h)

private theorem pure_reverse_all [Inhabited α] (a : List α) (h : a.length < 2 ^ 62) :
    reverseBang a (JInt.lit .i64 1) (JInt.wrap .i64 a.length) = .ok a.reverse := by
  simpa only [List.nil_append, List.append_nil, List.length_nil, Int.natCast_zero,
    Int.zero_add, JInt.lit] using pure_reverse_parts ([] : List α) a ([] : List α)
      (by simpa only [List.nil_append, List.append_nil] using h)

theorem circshiftSpec : CircshiftSpec := by
  intro α _ t v k hv
  rw [pure_limit] at hv
  constructor
  · by_cases hn : v.length = 0
    · have he : v = [] := List.eq_nil_of_length_eq_zero hn
      subst v
      simp [circshiftBang, rotateRight]
    · have hmod₀ : 0 ≤ modShift k v.length := Int.emod_nonneg _ (by omega)
      have hmod₁ : modShift k v.length < (v.length : Int) := Int.emod_lt_of_pos _ (by omega)
      by_cases hs : modShift k v.length = 0
      · simp [circshiftBang, hn, hs, rotateRight]
      · let cut := v.length - (modShift k v.length).toNat
        let a := v.take cut
        let b := v.drop cut
        have hab : a ++ b = v := List.take_append_drop _ _
        have ha : a.length = cut := by dsimp [a]; rw [List.length_take]; omega
        have hb : b.length = (modShift k v.length).toNat := by
          dsimp [b]; rw [List.length_drop]; dsimp [cut]; omega
        have hnv : (JInt.wrap .i64 v.length).val = v.length := by
          apply pure_wrap
          simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
        have hcut : (v.length : Int) - modShift k v.length = a.length := by
          rw [ha]; dsimp [cut]; omega
        have htot : (a.length : Int) + b.length = v.length := by
          have := congrArg List.length hab
          simp only [List.length_append] at this
          omega
        have hlen : (a ++ b).length < 2 ^ 62 := by rw [hab, pure_limit]; exact hv
        have hlen₁ : (a.reverse ++ b).length < 2 ^ 62 := by
          simpa only [List.length_append, List.length_reverse] using hlen
        have hlen₂ : (a.reverse ++ b.reverse).length < 2 ^ 62 := by
          simpa only [List.length_append, List.length_reverse] using hlen
        have h₁ := pure_reverse_prefix a b hlen
        rw [hab] at h₁
        have h₂ := pure_reverse_suffix a.reverse b hlen₁
        simp only [List.length_reverse] at h₂
        have h₃ := pure_reverse_all (a.reverse ++ b.reverse) hlen₂
        simp only [List.length_append, List.length_reverse, Int.natCast_add, htot,
          List.reverse_append, List.reverse_reverse] at h₃
        rw [htot] at h₂
        rw [← hcut] at h₁ h₂
        unfold circshiftBang
        rw [ite_eq_right hn]
        dsimp only
        rw [ite_eq_right hs]
        generalize (@reverseBang α inferInstance .i64 .i64) = rev at h₁ h₂ h₃ ⊢
        rw [hnv, h₁, pure_bind_ok, h₂, pure_bind_ok, h₃]
        rfl
  · cases v with
    | nil => simp [circshift, rotateRight]
    | cons x xs => rfl

private def pure_test (f : α → Bool) (a : List α) (j : Int) : Bool :=
  (a[(j - 1).toNat]?.map f).getD false

private theorem pure_find_congr (xs : List α) (p q : α → Bool)
    (h : ∀ x ∈ xs, p x = q x) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.find?_cons, List.find?_cons, h x (by simp)]
    split
    · rfl
    · exact ih (fun y hy => h y (by simp [hy]))

private theorem pure_getAt_nat (a : List α) (hv : a.length < 2 ^ 62)
    (d : Nat) (hd : d < a.length) :
    getAt a (JInt.wrap .i64 ((d : Int) + 1)) = .ok a[d] := by
  have hr : IntTy.i64.min ≤ (d : Int) + 1 ∧ (d : Int) + 1 ≤ IntTy.i64.max := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
  have hw : (JInt.wrap .i64 ((d : Int) + 1)).val = (d : Int) + 1 :=
    pure_wrap _ hr
  have hbound : 1 ≤ (d : Int) + 1 ∧ (d : Int) + 1 ≤ a.length := by omega
  have hindex : ((d : Int) + 1 - 1).toNat = d := by omega
  simp only [getAt, hw, dite_eq_left hbound, hindex]

private theorem pure_test_nat (f : α → Bool) (a : List α) (d : Nat) (hd : d < a.length) :
    pure_test f a ((d : Int) + 1) = f a[d] := by
  simp [pure_test, List.getElem?_eq_getElem hd]

private theorem pure_next_loop (f : α → Bool) (a : List α) (hv : a.length < 2 ^ 62)
    (k : Nat) : ∀ d : Nat, d + k = a.length →
    (findnextLoop f a a.length ((d : Int) + 1) k).map (·.map (·.val)) =
      .ok (((List.range' d k).map (fun (n : Nat) => (n : Int) + 1)).find? (pure_test f a)) := by
  induction k with
  | zero => intro d hd; simp [findnextLoop]
  | succ k ih =>
    intro d hd
    have hdlt : d < a.length := by omega
    have hw : (JInt.wrap .i64 ((d : Int) + 1)).val = (d : Int) + 1 := by
      apply pure_wrap
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
    rw [findnextLoop, pure_getAt_nat a hv d hdlt]
    simp only [pure_bind_ok, List.range'_succ, List.map_cons, List.find?_cons,
      pure_test_nat f a d hdlt]
    cases hf : f a[d] with
    | true => simp [hf, hw]
    | false =>
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      by_cases he : (d : Int) + 1 = a.length
      · have hk : k = 0 := by omega
        subst k
        simp [he]
      · rw [if_neg he]
        have h := ih (d + 1) (by omega)
        simpa only [Int.natCast_add, Int.natCast_one, Int.add_assoc] using h

private theorem pure_prev_loop (f : α → Bool) (a : List α) (hv : a.length < 2 ^ 62)
    (k : Nat) (hk : k ≤ a.length) :
    (findprevLoop f a k k).map (·.map (·.val)) =
      .ok ((((List.range k).map (fun (n : Nat) => (n : Int) + 1)).reverse).find? (pure_test f a)) := by
  induction k with
  | zero => simp [findprevLoop]
  | succ k ih =>
    have hklt : k < a.length := by omega
    have hw : (JInt.wrap .i64 ((k : Int) + 1)).val = (k : Int) + 1 := by
      apply pure_wrap
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]; omega
    simp only [Int.natCast_add, Int.natCast_one]
    rw [findprevLoop, pure_getAt_nat a hv k hklt]
    simp only [pure_bind_ok, List.range_succ, List.map_append, List.map_cons,
      List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.find?_cons, pure_test_nat f a k hklt]
    cases hf : f a[k] with
    | true => simp [hf, hw]
    | false =>
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      by_cases he : (k : Int) + 1 = 1
      · have hkzero : k = 0 := by omega
        subst k
        simp
      · rw [if_neg he]
        simpa using ih (by omega)

private theorem pure_range_split (n d : Nat) (hd : d ≤ n) :
    List.range n = List.range d ++ List.range' d (n - d) := by
  simpa only [List.range_eq_range', Nat.zero_add, Nat.add_sub_cancel' hd] using
    (List.range'_append_1 (s := 0) (m := d) (n := n - d)).symm

private theorem pure_first_suffix (f : α → Bool) (a : List α) (i : Int)
    (hi : 1 ≤ i) (hil : i ≤ a.length) :
    firstAtLeast f a i =
      (((List.range' (i - 1).toNat (a.length - (i - 1).toNat)).map
        (fun (n : Nat) => (n : Int) + 1)).find? (pure_test f a)) := by
  unfold firstAtLeast
  rw [pure_range_split a.length (i - 1).toNat (by omega), List.map_append, List.find?_append]
  have hnone : ((List.range (i - 1).toNat).map (fun (n : Nat) => (n : Int) + 1)).find?
      (fun j => decide (i ≤ j) && pure_test f a j) = none := by
    apply List.find?_eq_none.mpr
    intro j hj
    rcases List.mem_map.mp hj with ⟨n, hn, rfl⟩
    have hn' : n < (i - 1).toNat := List.mem_range.mp hn
    simp [show ¬ i ≤ (n : Int) + 1 by omega]
  simp only [pure_test] at hnone
  rw [hnone]
  simp only [Option.none_or]
  apply pure_find_congr
  intro j hj
  rcases List.mem_map.mp hj with ⟨n, hn, rfl⟩
  have hn' := List.mem_range'_1.mp hn
  simp [show i ≤ (n : Int) + 1 by omega, pure_test]

private theorem pure_last_prefix (f : α → Bool) (a : List α) (i : Int)
    (hi : 1 ≤ i) (hil : i ≤ a.length) :
    lastUpTo f a i =
      ((((List.range i.toNat).map (fun (n : Nat) => (n : Int) + 1)).reverse).find? (pure_test f a)) := by
  unfold lastUpTo
  rw [pure_range_split a.length i.toNat (by omega), List.map_append, List.reverse_append,
    List.find?_append]
  have hnone : (((List.range' i.toNat (a.length - i.toNat)).map (fun (n : Nat) => (n : Int) + 1)).reverse).find?
      (fun j => decide (j ≤ i) && pure_test f a j) = none := by
    apply List.find?_eq_none.mpr
    intro j hj
    rcases List.mem_map.mp (List.mem_reverse.mp hj) with ⟨n, hn, rfl⟩
    have hn' := List.mem_range'_1.mp hn
    simp [show ¬ (n : Int) + 1 ≤ i by omega]
  simp only [pure_test] at hnone
  rw [hnone]
  simp only [Option.none_or]
  apply pure_find_congr
  intro j hj
  rcases List.mem_map.mp (List.mem_reverse.mp hj) with ⟨n, hn, rfl⟩
  have hn' := List.mem_range.mp hn
  simp [show (n : Int) + 1 ≤ i by omega, pure_test]

theorem findInRange : FindInRange := by
  intro α t f v i hv himin himax
  have hconv : toInt i = .ok ⟨i.val, himin, himax⟩ := by
    simp [toInt, JInt.convert, himin, himax]
  constructor
  · intro hi
    simp only [findnext, hconv, pure_bind_ok]
    by_cases hil : i.val ≤ v.length
    · rw [if_neg (by omega), pure_first_suffix f v i.val hi hil]
      have hk : ((v.length : Int) - i.val + 1).toNat = v.length - (i.val - 1).toNat := by omega
      have hd : ((i.val - 1).toNat : Int) + 1 = i.val := by omega
      rw [hk]
      have h := pure_next_loop f v hv (v.length - (i.val - 1).toNat)
        (i.val - 1).toNat (by omega)
      simpa only [hd] using h
    · rw [if_pos (by omega)]
      have hnone : firstAtLeast f v i.val = none := by
        unfold firstAtLeast
        apply List.find?_eq_none.mpr
        intro j hj
        rcases List.mem_map.mp hj with ⟨n, hn, rfl⟩
        have hn' := List.mem_range.mp hn
        simp [show ¬ i.val ≤ (n : Int) + 1 by omega]
      simp [hnone]
  · intro hil
    simp only [findprev, hconv, pure_bind_ok]
    by_cases hi : 1 ≤ i.val
    · rw [if_neg (by omega), pure_last_prefix f v i.val hi hil]
      have hd : (i.val.toNat : Int) = i.val := by omega
      rw [← hd]
      exact pure_prev_loop f v hv _ (by omega)
    · rw [if_pos (by omega)]
      have hnone : lastUpTo f v i.val = none := by
        unfold lastUpTo
        apply List.find?_eq_none.mpr
        intro j hj
        rcases List.mem_map.mp (List.mem_reverse.mp hj) with ⟨n, hn, rfl⟩
        have hn' := List.mem_range.mp hn
        simp [show ¬ (n : Int) + 1 ≤ i.val by omega]
      simp [hnone]

end JuliaLean.ArrayOps
