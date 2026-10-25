import JuliaLean.ArrayOps.VecProps

/-!
Proofs of the `Vector` mutation properties of `VecProps.lean` that hold.
-/

namespace JuliaLean.ArrayOps

open JuliaLean

/-! ### Integer facts -/

private theorem vp_i64_min : IntTy.min .i64 = -2 ^ 63 := by decide
private theorem vp_i64_max : IntTy.max .i64 = 2 ^ 63 - 1 := by decide

private theorem vp_r64 (x : JInt64) : -2 ^ 63 ≤ x.val ∧ x.val ≤ 2 ^ 63 - 1 := by
  have h := x.property
  have h1 := vp_i64_min
  have h2 := vp_i64_max
  omega

private theorem vp_wrap64v {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) :
    wrapInt .i64 x = x :=
  wrapInt_of_inRange .i64 x ⟨by rw [vp_i64_min]; exact h1, by rw [vp_i64_max]; exact h2⟩

private theorem vp_wrap64e {x y : Int} (h : x = y) (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) :
    wrapInt .i64 x = y := by
  rw [vp_wrap64v h1 h2, h]

private theorem vp_wrap_val {t : IntTy} (x : Int) : (JInt.wrap t x).val = wrapInt t x := rfl

private theorem vp_wrapP {t : IntTy} {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 2 ^ 63 - 1) :
    wrapInt (IntTy.promote .i64 t) x = x := by
  apply wrapInt_of_inRange
  cases t <;> simp [IntTy.promote, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max] <;> omega

private theorem vp_one : (JInt.lit .i64 1).val = 1 := wrapInt_of_inRange .i64 1 (by decide)

private theorem vp_toInt_ok {t : IntTy} {x : JInt t} {y : JInt64} (h : toInt x = .ok y) :
    y.val = x.val := by
  unfold toInt JInt.convert at h
  split at h
  · cases h; rfl
  · cases h

private theorem vp_toInt_of {t : IntTy} (x : JInt t) (h1 : -2 ^ 63 ≤ x.val)
    (h2 : x.val ≤ 2 ^ 63 - 1) : ∃ y : JInt64, toInt x = .ok y ∧ y.val = x.val := by
  have h : IntTy.min .i64 ≤ x.val ∧ x.val ≤ IntTy.max .i64 := by
    rw [vp_i64_min, vp_i64_max]; exact ⟨h1, h2⟩
  exact ⟨⟨x.val, h⟩, by unfold toInt JInt.convert; rw [dif_pos h], rfl⟩

private theorem vp_unitLength_val {t : IntTy} (lo hi : JInt t) (h1 : 1 ≤ lo.val)
    (h2 : lo.val ≤ hi.val) : (unitLength lo hi).val = hi.val - lo.val + 1 := by
  show wrapInt (unitLengthTy t) (hi.val - lo.val + 1) = _
  apply wrapInt_of_inRange
  have hb := hi.property
  cases t <;> simp [unitLengthTy, IntTy.bits, IntTy.min, IntTy.max, IntTy.signed] at hb ⊢ <;>
    omega

/-! ### List facts -/

section lists
variable {β γ : Type}

private theorem vp_map_take (f : β → γ) :
    ∀ (l : List β) (k : Nat), (l.take k).map f = (l.map f).take k
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: l, k + 1 => by simp [vp_map_take f l k]

private theorem vp_map_drop (f : β → γ) :
    ∀ (l : List β) (k : Nat), (l.drop k).map f = (l.map f).drop k
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: l, k + 1 => by simp [vp_map_drop f l k]

private theorem vp_take_set_succ : ∀ (v : List β) (k : Nat) (x : β), k < v.length →
    (v.set k x).take (k + 1) = v.take k ++ [x]
  | [], _, _, h => absurd h (by simp)
  | _ :: _, 0, _, _ => rfl
  | y :: ys, k + 1, x, h => by
    have ih := vp_take_set_succ ys k x (by simp at h; omega)
    simp only [List.set, List.take, ih, List.cons_append]

private theorem vp_take_set_ge : ∀ (v : List β) (k j : Nat) (x : β), k ≤ j →
    (v.set j x).take k = v.take k
  | [], _, _, _, _ => rfl
  | _ :: _, 0, _, _, _ => rfl
  | _ :: _, _ + 1, 0, _, h => absurd h (by omega)
  | y :: ys, k + 1, j + 1, x, h => by
    simp only [List.set, List.take, vp_take_set_ge ys k j x (by omega)]

private theorem vp_drop_set_lt : ∀ (v : List β) (k m : Nat) (x : β), k < m →
    (v.set k x).drop m = v.drop m
  | [], _, _, _, _ => rfl
  | _ :: _, _, 0, _, h => absurd h (by omega)
  | _ :: _, 0, _ + 1, _, _ => rfl
  | y :: ys, k + 1, m + 1, x, h => by
    simp only [List.set, List.drop, vp_drop_set_lt ys k m x (by omega)]

private theorem vp_drop_eq_cons : ∀ (l : List β) (m : Nat), m < l.length →
    ∃ x r, l.drop m = x :: r
  | [], _, h => absurd h (by simp)
  | x :: l, 0, _ => ⟨x, l, rfl⟩
  | _ :: l, m + 1, h => vp_drop_eq_cons l m (by simp at h; omega)

private theorem vp_drop_cons : ∀ (l : List β) (m : Nat) (x : β) (r : List β),
    l.drop m = x :: r → l[m]? = some x ∧ l.drop (m + 1) = r
  | [], _, _, _, h => by simp at h
  | y :: l, 0, x, r, h => by
    simp only [List.drop_zero, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | _ :: l, m + 1, x, r, h => vp_drop_cons l m x r h

private theorem vp_take_succ_of_drop : ∀ (l : List β) (m : Nat) (x : β) (r : List β),
    l.drop m = x :: r → l.take (m + 1) = l.take m ++ [x]
  | [], _, _, _, h => by simp at h
  | y :: l, 0, x, r, h => by
    simp only [List.drop_zero, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | y :: l, m + 1, x, r, h => by
    have ih := vp_take_succ_of_drop l m x r h
    simp only [List.take, ih, List.cons_append]

private theorem vp_drop_drop : ∀ (l : List β) (m j : Nat), (l.drop m).drop j = l.drop (m + j)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: l, m + 1, j => by
    rw [show m + 1 + j = (m + j) + 1 by omega]
    exact vp_drop_drop l m j

private theorem vp_drop_drop' (l : List β) (m j n : Nat) (h : m + j = n) :
    (l.drop m).drop j = l.drop n := by
  rw [vp_drop_drop, h]

private theorem vp_drop_shift (f : β → γ) (v : List γ) (a0 : List β) (B m : Nat)
    (hB : v.drop B = (a0.drop B).map f) (h : B ≤ m) : v.drop m = (a0.drop m).map f := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← vp_drop_drop, hB, ← vp_map_drop, vp_drop_drop]

private theorem vp_take_take_le : ∀ (l : List β) (k X : Nat), k ≤ X →
    (l.take X).take k = l.take k
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp
  | _ :: _, _ + 1, 0, h => absurd h (by omega)
  | y :: l, k + 1, X + 1, h => by
    simp only [List.take]
    rw [vp_take_take_le l k X (by omega)]

private theorem vp_take_append_le : ∀ (l1 l2 : List β) (k : Nat), k ≤ l1.length →
    (l1 ++ l2).take k = l1.take k
  | [], _, 0, _ => rfl
  | [], _, _ + 1, h => absurd h (by simp)
  | _ :: _, _, 0, _ => rfl
  | y :: l1, l2, k + 1, h => by
    simp only [List.cons_append, List.take]
    rw [vp_take_append_le l1 l2 k (by simp at h; omega)]

private theorem vp_drop_append_ge : ∀ (l1 l2 : List β) (j : Nat), l1.length ≤ j →
    (l1 ++ l2).drop j = l2.drop (j - l1.length)
  | [], _, _, _ => by simp
  | _ :: _, _, 0, h => absurd h (by simp)
  | y :: l1, l2, j + 1, h => by
    simp only [List.cons_append, List.drop, List.length_cons]
    rw [vp_drop_append_ge l1 l2 j (by simp at h; omega)]
    congr 1
    omega

private theorem vp_take_all : ∀ (l : List β) (k : Nat), l.length ≤ k → l.take k = l
  | [], _, _ => by simp
  | _ :: _, 0, h => absurd h (by simp)
  | y :: l, k + 1, h => by
    simp only [List.take]
    rw [vp_take_all l k (by simp at h; omega)]

private theorem vp_eraseIdx : ∀ (l : List β) (k : Nat), l.eraseIdx k = l.take k ++ l.drop (k + 1)
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | y :: l, k + 1 => by
    simp only [List.eraseIdx, List.take, List.drop, List.cons_append]
    rw [vp_eraseIdx l k]

private theorem vp_set_mid : ∀ (l r : List β) (y x : β) (k : Nat), k = l.length →
    (l ++ List.replicate 1 y ++ r).set k x = l ++ x :: r
  | [], r, y, x, _, h => by subst h; rfl
  | z :: l, r, y, x, k, h => by
    subst h
    simp only [List.cons_append, List.length_cons, List.set]
    rw [vp_set_mid l r y x l.length rfl]

private theorem vp_set_last (l : List β) (y x : β) (k : Nat) (h : k = l.length) :
    (l ++ List.replicate 1 y).set k x = l ++ [x] := by
  have := vp_set_mid l [] y x k h
  rwa [List.append_nil] at this

private theorem vp_dropLast_take : ∀ l : List β, l.dropLast = l.take (l.length - 1)
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
    have ih := vp_dropLast_take (y :: l)
    show x :: (y :: l).dropLast = x :: (y :: l).take ((y :: l).length - 1)
    rw [ih]

private theorem vp_getLast : ∀ l : List β, ((l.map some).getLast?).join = l.getLast?
  | [] => rfl
  | [_] => rfl
  | _ :: y :: l => vp_getLast (y :: l)

end lists

section
variable {α : Type}

/-! ### Primitive operations -/

private theorem vp_memref {t : IntTy} (len : Nat) (k : JInt t) (h1 : 1 ≤ k.val)
    (h2 : k.val ≤ len) (h3 : k.val ≤ 2 ^ 63 - 1) : memoryrefCheck len k = .ok () := by
  obtain ⟨y, hy, hyv⟩ := vp_toInt_of k (by omega) h3
  unfold memoryrefCheck
  rw [hy]
  simp only [bind, Except.bind]
  split
  · rfl
  · omega

private theorem vp_selfCopy {s t u : IntTy} (len : Nat) (d : JInt s) (so : JInt t) (n : JInt u)
    (h : n.val ≠ 0 → (1 ≤ d.val ∧ d.val ≤ len ∧ d.val ≤ 2 ^ 63 - 1) ∧
      (1 ≤ so.val ∧ so.val ≤ len ∧ so.val ≤ 2 ^ 63 - 1)) :
    selfCopyCheck len d so n = .ok () := by
  unfold selfCopyCheck
  split
  · rfl
  · rename_i hn
    obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := h hn
    rw [vp_memref len d h1 h2 h3]
    exact vp_memref len so h4 h5 h6

private theorem vp_deletebeg {t : IntTy} (a : Vec α) (d : JInt t) (h0 : 0 ≤ d.val)
    (h1 : d.val ≤ a.length) (h2 : d.val ≤ 2 ^ 63 - 1) :
    deletebeg a d = ⟨a.drop d.val.toNat, .ok ()⟩ := by
  obtain ⟨y, hy, hyv⟩ := vp_toInt_of d (by omega) h2
  unfold deletebeg
  rw [hy]
  dsimp only
  split
  · omega
  · rw [hyv]

private theorem vp_deleteend {t : IntTy} (a : Vec α) (d : JInt t) (h0 : 0 ≤ d.val)
    (h1 : d.val ≤ a.length) (h2 : d.val ≤ 2 ^ 63 - 1) :
    deleteend a d = ⟨a.take (a.length - d.val.toNat), .ok ()⟩ := by
  obtain ⟨y, hy, hyv⟩ := vp_toInt_of d (by omega) h2
  unfold deleteend
  rw [hy]
  dsimp only
  split
  · omega
  · rw [hyv]

private theorem vp_deleteend' {t : IntTy} (a : Vec α) (d : JInt t) (k : Nat) (h0 : 0 ≤ d.val)
    (h1 : d.val ≤ a.length) (h2 : d.val ≤ 2 ^ 63 - 1) (hk : (a.length : Int) - d.val = k) :
    deleteend a d = ⟨a.take k, .ok ()⟩ := by
  rw [vp_deleteend a d h0 h1 h2, show a.length - d.val.toNat = k by omega]

private theorem vp_growbeg {t : IntTy} (a : Vec α) (d : JInt t) (h0 : 0 ≤ d.val)
    (h2 : d.val ≤ 2 ^ 63 - 1) :
    growbeg a d = ⟨List.replicate d.val.toNat none ++ a, .ok ()⟩ := by
  obtain ⟨y, hy, hyv⟩ := vp_toInt_of d (by omega) h2
  unfold growbeg
  rw [hy]
  dsimp only
  split
  · simp [show d.val.toNat = 0 by omega]
  · split
    · omega
    · rw [hyv]

private theorem vp_growend {t : IntTy} (a : Vec α) (d : JInt t) (h0 : 0 ≤ d.val)
    (h2 : d.val ≤ 2 ^ 63 - 1) :
    growend a d = ⟨a ++ List.replicate d.val.toNat none, .ok ()⟩ := by
  obtain ⟨y, hy, hyv⟩ := vp_toInt_of d (by omega) h2
  unfold growend
  rw [hy]
  dsimp only
  split
  · omega
  · rw [hyv]

private theorem vp_growat {s t : IntTy} (a : Vec α) (i : JInt s) (d : JInt t)
    (hlen : a.length < 2 ^ 62) (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ a.length + 1)
    (hd0 : 0 ≤ d.val) (hd1 : d.val ≤ 2 ^ 63 - 1) :
    growat a i d = ⟨a.take (i.val - 1).toNat ++ List.replicate d.val.toNat none ++
      a.drop (i.val - 1).toNat, .ok ()⟩ := by
  have hmax := vp_i64_max
  obtain ⟨dj, hdj, hdjv⟩ := vp_toInt_of d (by omega) hd1
  obtain ⟨j, hj, hjv⟩ := vp_toInt_of i (by omega) (by omega)
  unfold growat
  rw [hdj, hj]
  dsimp only
  split
  · rw [vp_growbeg a dj (by omega) (by omega), show (i.val - 1).toNat = 0 by omega, hdjv]
    simp
  · split
    · rw [vp_growend a dj (by omega) (by omega), show (i.val - 1).toNat = a.length by omega, hdjv]
      simp
    · split
      · omega
      · split
        · omega
        · simp only [hjv, hdjv]

private theorem vp_growat' {s t : IntTy} (a : Vec α) (i : JInt s) (d : JInt t)
    (hlen : a.length < 2 ^ 62) (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ a.length + 1)
    (hd0 : 0 ≤ d.val) (hd1 : d.val ≤ 2 ^ 63 - 1) (k1 e : Nat)
    (hk1 : (i.val - 1).toNat = k1) (he : d.val.toNat = e) :
    growat a i d = ⟨a.take k1 ++ List.replicate e none ++ a.drop k1, .ok ()⟩ := by
  rw [vp_growat a i d hlen hi1 hi2 hd0 hd1, hk1, he]

/-- `_deleteat!(a, i, delta)` for an in-bounds block removes exactly that block. -/
private theorem vp_deleteatAt {s t : IntTy} (a : Vec α) (i : JInt s) (delta : JInt t)
    (hlen : a.length < 2 ^ 62) (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ a.length)
    (hd : 0 ≤ delta.val) (hid : i.val + delta.val ≤ a.length + 1) :
    deleteatAt a i delta =
      ⟨a.take (i.val - 1).toNat ++ a.drop (i.val - 1 + delta.val).toNat, .ok ()⟩ := by
  obtain ⟨j, hj, hjv⟩ := vp_toInt_of i (by omega) (by omega)
  have hone := vp_one
  have h3 : (addMixed j delta).val = j.val + delta.val := vp_wrapP (by omega) (by omega)
  have h4 : (addMixed (JInt.lit .i64 1) delta).val = 1 + delta.val := by
    show wrapInt _ ((JInt.lit .i64 1).val + delta.val) = _
    rw [hone]; exact vp_wrapP (by omega) (by omega)
  have h5 : (j - JInt.lit .i64 1).val = j.val - 1 := by
    show wrapInt .i64 (j.val - (JInt.lit .i64 1).val) = _
    rw [hone]; exact vp_wrap64v (by omega) (by omega)
  have h6 : (JInt.wrap (IntTy.promote .i64 t) ((a.length : Int) + 1 - delta.val - j.val)).val =
      (a.length : Int) + 1 - delta.val - j.val := vp_wrapP (by omega) (by omega)
  unfold deleteatAt
  rw [hj]
  dsimp only
  split
  · omega
  split
  · omega
  split
  · omega
  split
  · have hsc : selfCopyCheck a.length (addMixed (JInt.lit .i64 1) delta) (JInt.lit .i64 1)
        (j - JInt.lit .i64 1) = .ok () :=
      vp_selfCopy _ _ _ _ (fun _ => ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega⟩)
    rw [hsc, vp_deletebeg a delta hd (by omega) (by omega)]
    simp only [hjv]
  · have hsc : selfCopyCheck a.length j (addMixed j delta)
        (JInt.wrap (IntTy.promote .i64 t) ((a.length : Int) + 1 - delta.val - j.val)) = .ok () :=
      vp_selfCopy _ _ _ _ (fun _ => ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega⟩)
    rw [hsc, vp_deleteend a delta hd (by omega) (by omega)]
    simp only [hjv]

private theorem vp_deleteatAt' {s t : IntTy} (a : Vec α) (i : JInt s) (delta : JInt t)
    (k1 k2 : Nat) (hlen : a.length < 2 ^ 62) (hi1 : 1 ≤ i.val) (hi2 : i.val ≤ a.length)
    (hd : 0 ≤ delta.val) (hid : i.val + delta.val ≤ a.length + 1)
    (hk1 : (i.val - 1).toNat = k1) (hk2 : (i.val - 1 + delta.val).toNat = k2) :
    deleteatAt a i delta = ⟨a.take k1 ++ a.drop k2, .ok ()⟩ := by
  rw [vp_deleteatAt a i delta hlen hi1 hi2 hd hid, hk1, hk2]

private theorem vp_deleteatRange {t : IntTy} (a : Vec α) (lo hi : JInt t)
    (hlen : a.length < 2 ^ 62) (h1 : lo.val ≤ hi.val + 1)
    (h2 : lo.val > hi.val ∨ (1 ≤ lo.val ∧ hi.val ≤ a.length)) :
    deleteatRange a lo hi = ⟨a.take (lo.val - 1).toNat ++ a.drop hi.val.toNat, .ok ()⟩ := by
  unfold deleteatRange
  by_cases h : lo.val > hi.val
  · rw [if_pos h, show (lo.val - 1).toNat = hi.val.toNat by omega, List.take_append_drop]
  · rw [if_neg h]
    have hu := vp_unitLength_val lo hi (by omega) (by omega)
    rw [vp_deleteatAt a lo (unitLength lo hi) hlen (by omega) (by omega) (by omega) (by omega),
      show (lo.val - 1 + (unitLength lo hi).val).toNat = hi.val.toNat by omega]

private theorem vp_storeAll : ∀ (xs : List α) (v : Vec α) (s : Int) (S : Nat), s = S + 1 →
    S + xs.length ≤ v.length →
    storeAll Except.ok v s xs = ⟨v.take S ++ xs.map some ++ v.drop (S + xs.length), .ok ()⟩
  | [], v, _, S, _, _ => by simp [storeAll]
  | x :: xs, v, s, S, hs, hl => by
    simp only [List.length_cons] at hl
    have hS : S < v.length := by omega
    have hb : ¬ ¬ (1 ≤ s ∧ s ≤ (v.length : Int)) := by intro h; apply h; omega
    have ih := vp_storeAll xs (v.set S (some x)) (s + 1) (S + 1) (by omega)
      (by rw [List.length_set]; omega)
    simp only [storeAll, hb, ↓reduceIte, show (s - 1).toNat = S by omega, ih]
    rw [vp_take_set_succ v S (some x) hS, vp_drop_set_lt v S (S + 1 + xs.length) (some x) (by omega)]
    simp only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.length_cons, show S + 1 + xs.length = S + (xs.length + 1) by omega]

/-! ### Dequeue operations -/

theorem dequeueSpec : DequeueSpec := by
  intro α a x hlen
  have hone := vp_one
  have e1 : (JInt.lit .i64 1).val.toNat = 1 := by simp [hone]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold push
    rw [vp_growend (a.map some) (JInt.lit .i64 1) (by omega) (by omega), e1]
    dsimp only
    rw [vp_set_last (a.map some) none (some x) _ (by simp)]
    simp
  · unfold pushfirst
    rw [vp_growbeg (a.map some) (JInt.lit .i64 1) (by omega) (by omega), e1]
    rfl
  · cases a with
    | nil => rfl
    | cons y a' =>
      have hne : (List.map some (y :: a')).isEmpty = false := rfl
      have hne' : (y :: a').isEmpty = false := rfl
      simp only [pop, hne, hne', Bool.false_eq_true, ↓reduceIte]
      rw [vp_deleteend (List.map some (y :: a')) (JInt.lit .i64 1) (by omega)
        (by rw [hone]; simp only [List.length_map, List.length_cons]; omega) (by omega)]
      dsimp only
      rw [e1, vp_getLast, vp_dropLast_take (y :: a'), vp_map_take, List.length_map]
  · cases a with
    | nil => rfl
    | cons y a' =>
      have hne : (List.map some (y :: a')).isEmpty = false := rfl
      have hne' : (y :: a').isEmpty = false := rfl
      simp only [popfirst, hne, hne', Bool.false_eq_true, ↓reduceIte]
      rw [vp_deletebeg (List.map some (y :: a')) (JInt.lit .i64 1) (by omega)
        (by rw [hone]; simp only [List.length_map, List.length_cons]; omega) (by omega), e1]
      rfl

/-! ### `insert!` and `deleteat!` at an index -/

theorem insertSpec : InsertSpec := by
  intro α t a i x hlen
  have hone := vp_one
  have hmax := vp_i64_max
  have e1 : (JInt.lit .i64 1).val.toNat = 1 := by simp [hone]
  have hL : (a.map some).length = a.length := by simp
  obtain ⟨o, ho, hov⟩ := vp_toInt_of (JInt.lit .i64 1) (by omega) (by omega)
  cases hi : toInt i with
  | error e => simp only [insert, growat, ho, hi]
  | ok j =>
    have hjv := vp_toInt_ok hi
    dsimp only
    by_cases hb : 1 ≤ j.val ∧ j.val ≤ (a.length : Int) + 1
    · rw [if_pos hb]
      unfold insert
      rw [vp_growat' (a.map some) i (JInt.lit .i64 1) (by omega) (by omega) (by omega) (by omega)
        (by omega) (i.val - 1).toNat 1 rfl e1]
      dsimp only
      rw [vp_set_mid _ _ _ _ _ ?_, hjv]
      · simp only [List.map_append, List.map_cons, vp_map_take, vp_map_drop]
      · simp only [List.length_take, List.length_map]; omega
    · rw [if_neg hb]
      unfold insert growat
      rw [ho, hi]
      dsimp only
      rw [if_neg (show ¬ j.val = 1 by omega),
        if_neg (show ¬ (((a.map some).length : Int) < IntTy.i64.max ∧
          j.val = ((a.map some).length : Int) + 1) by omega),
        if_neg (show ¬ ¬ 0 ≤ o.val by omega),
        if_pos (show ¬ (1 < j.val ∧ j.val ≤ ((a.map some).length : Int)) by omega)]

theorem deleteatIndexSpec : DeleteatIndexSpec := by
  intro α t a i hlen
  have hone := vp_one
  have hL : (a.map some).length = a.length := by simp
  cases hi : toInt i with
  | error e => simp only [deleteatIndex, deleteatAt, hi]
  | ok j =>
    have hjv := vp_toInt_ok hi
    dsimp only
    by_cases hb : 1 ≤ j.val ∧ j.val ≤ (a.length : Int)
    · rw [if_pos hb]
      unfold deleteatIndex
      rw [vp_deleteatAt' (a.map some) i (JInt.lit .i64 1) (i.val - 1).toNat ((i.val - 1).toNat + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega) rfl (by omega),
        hjv, vp_eraseIdx, List.map_append, vp_map_take, vp_map_drop]
    · rw [if_neg hb]
      unfold deleteatIndex deleteatAt
      rw [hi]
      dsimp only
      rw [if_neg (show ¬ ¬ 0 ≤ (JInt.lit .i64 1).val by omega),
        if_pos (show ¬ (1 ≤ j.val ∧ j.val ≤ ((a.map some).length : Int)) by omega)]

/-! ### `deleteat!` on a range -/

theorem deleteatRangeInBounds : DeleteatRangeInBounds := by
  intro α t a lo hi hlen h1 h2
  have hL : (a.map some).length = a.length := by simp
  rw [vp_deleteatRange (a.map some) lo hi (by rw [hL]; exact hlen) h1 (by rw [hL]; exact h2)]
  by_cases h : lo.val > hi.val
  · rw [if_pos h, show (lo.val - 1).toNat = hi.val.toNat by omega, List.take_append_drop]
  · rw [if_neg h, List.map_append, vp_map_take, vp_map_drop]

/-! ### `deleteat!` with sorted indices -/

/-- `dropPositions` with the first element at position `s`. -/
private def vpDrop {β : Type} (S : List Int) : List β → Nat → List β
  | [], _ => []
  | x :: l, s => if (s : Int) ∈ S then vpDrop S l (s + 1) else x :: vpDrop S l (s + 1)

private theorem vp_zipIdx_drop {β : Type} (S : List Int) : ∀ (l : List β) (s : Nat),
    ((l.zipIdx s).filter fun p => decide ((p.2 : Int) ∉ S)).map Prod.fst = vpDrop S l s
  | [], _ => rfl
  | x :: l, s => by
    have ih := vp_zipIdx_drop S l (s + 1)
    by_cases h : (s : Int) ∈ S
    · simp only [List.zipIdx_cons, List.filter_cons, h, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte, vpDrop, ih]
    · simp only [List.zipIdx_cons, List.filter_cons, h, not_false_eq_true, decide_true,
        ↓reduceIte, vpDrop, ih, List.map_cons]

private theorem vp_dropPositions_eq {β : Type} (a : List β) (S : List Int) :
    dropPositions a S = vpDrop S a 1 :=
  vp_zipIdx_drop S a 1

private theorem vp_vpDrop_split {β : Type} (S : List Int) : ∀ (l : List β) (s m : Nat),
    vpDrop S l s = vpDrop S (l.take m) s ++ vpDrop S (l.drop m) (s + m)
  | [], _, _ => by simp [vpDrop]
  | x :: l, s, 0 => by simp [vpDrop]
  | x :: l, s, m + 1 => by
    have ih := vp_vpDrop_split S l (s + 1) m
    rw [show s + (m + 1) = s + 1 + m by omega]
    by_cases h : (s : Int) ∈ S
    · simp only [vpDrop, List.take, List.drop, h, ↓reduceIte, ih]
    · simp only [vpDrop, List.take, List.drop, h, ↓reduceIte, ih, List.cons_append]

private theorem vp_vpDrop_none {β : Type} (S : List Int) : ∀ (l : List β) (s : Nat),
    (∀ j : Int, (s : Int) ≤ j → j < s + l.length → j ∉ S) → vpDrop S l s = l
  | [], _, _ => rfl
  | x :: l, s, h => by
    have hs : (s : Int) ∉ S := h s (by omega) (by simp only [List.length_cons]; omega)
    have ih := vp_vpDrop_none S l (s + 1)
      (fun j h1 h2 => h j (by omega) (by simp only [List.length_cons]; omega))
    simp only [vpDrop, hs, ↓reduceIte, ih]

private theorem vp_vpDrop_mem {β : Type} (S : List Int) (x : β) (l : List β) (s : Nat)
    (h : (s : Int) ∈ S) : vpDrop S (x :: l) s = vpDrop S l (s + 1) := by
  simp only [vpDrop, h, ↓reduceIte]

/-- The compaction loop `while q < i; a[p] = a[q]; p += 1; q += 1; end`. -/
private theorem vp_compact : ∀ (k : Nat) (v : Vec α) (p q : Int) (P Q : Nat),
    p = P + 1 → q = Q + 1 → P ≤ Q → Q + k ≤ v.length →
    ∃ w, compact v p q k = (w, p + k, q + k) ∧ w.length = v.length ∧
      w.take (P + k) = v.take P ++ (v.drop Q).take k ∧ w.drop (Q + k) = v.drop (Q + k)
  | 0, v, p, q, P, Q, _, _, _, _ => ⟨v, by simp [compact], rfl, by simp, rfl⟩
  | k + 1, v, p, q, P, Q, hp, hq, hPQ, hk => by
    have hQ : Q < v.length := by omega
    obtain ⟨y, r, hr⟩ := vp_drop_eq_cons v Q hQ
    obtain ⟨hy, hr1⟩ := vp_drop_cons v Q y r hr
    have hc : copyItem v p q = v.set P y := by
      unfold copyItem
      rw [show (p - 1).toNat = P by omega, show (q - 1).toNat = Q by omega, hy] <;> rfl
    obtain ⟨w, hw, hwl, hwt, hwd⟩ := vp_compact k (v.set P y) (p + 1) (q + 1) (P + 1) (Q + 1)
      (by omega) (by omega) (by omega) (by rw [List.length_set]; omega)
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · show compact (copyItem v p q) (p + 1) (q + 1) k = _
      rw [hc, hw]
      congr 1
      congr 1 <;> omega
    · rw [hwl, List.length_set]
    · rw [show P + (k + 1) = P + 1 + k by omega, hwt, vp_take_set_succ v P y (by omega),
        vp_drop_set_lt v P (Q + 1) y (by omega), hr1, hr]
      simp
    · rw [show Q + (k + 1) = Q + 1 + k by omega, hwd, vp_drop_set_lt v P (Q + 1 + k) y (by omega)]

private theorem vp_deleteatLoop (a0 : List α) (S : List Int) (hn : a0.length < 2 ^ 62) :
    ∀ (rem : List JInt64) (v : Vec α) (p q : Int) (P Q : Nat) (K : List α),
    p = P + 1 → q = Q + 1 → P ≤ Q → Q ≤ a0.length → v.length = a0.length →
    v.take P = K.map some → v.drop Q = (a0.drop Q).map some →
    rem.Pairwise (fun i j => i.val < j.val) →
    (∀ i ∈ rem, (Q : Int) < i.val ∧ i.val ≤ a0.length) →
    (∀ x ∈ S, x ≤ Q ∨ x ∈ rem.map (·.val)) → (∀ i ∈ rem, i.val ∈ S) →
    deleteatLoop v a0.length p q rem = ⟨(K ++ vpDrop S (a0.drop Q) (Q + 1)).map some, .ok ()⟩
  | [], v, p, q, P, Q, K, hp, hq, hPQ, hQ, hv, hK, hD, _, _, hS, _ => by
    obtain ⟨w, hw, hwl, hwt, _⟩ := vp_compact (a0.length - Q) v p q P Q hp hq hPQ (by omega)
    have hc : ((a0.length : Int) + 1 - q).toNat = a0.length - Q := by omega
    have hnone : vpDrop S (a0.drop Q) (Q + 1) = a0.drop Q :=
      vp_vpDrop_none S _ _ (fun j h1 _ hj => by have := hS j hj; simp at this; omega)
    simp only [deleteatLoop, hc, hw]
    rw [vp_deleteend' w _ (P + (a0.length - Q)) ?_ ?_ ?_ ?_]
    · have ht : ((a0.drop Q).map some).take (a0.length - Q) = (a0.drop Q).map some :=
        vp_take_all _ _ (by simp)
      rw [hwt, hK, hD, ht, hnone, List.map_append]
    all_goals (simp (disch := omega) only [vp_wrap_val, vp_wrap64v] <;> omega)
  | i :: rest, v, p, q, P, Q, K, hp, hq, hPQ, hQ, hv, hK, hD, hpw, hbd, hS, hmem => by
    have hi := hbd i (by simp)
    have hpw' := List.pairwise_cons.mp hpw
    obtain ⟨I, hI⟩ : ∃ I : Nat, i.val = I + 1 := ⟨(i.val - 1).toNat, by omega⟩
    have hc : (i.val - q).toNat = I - Q := by omega
    obtain ⟨w, hw, hwl, hwt, hwd⟩ := vp_compact (I - Q) v p q P Q hp hq hPQ (by omega)
    have hchk : ¬ ¬ (q ≤ i.val ∧ i.val ≤ (a0.length : Int)) := by intro h; apply h; omega
    simp only [deleteatLoop, hchk, ↓reduceIte, hc, hw]
    have hdw : w.drop I = (a0.drop I).map some := by
      have h1 := hwd
      rw [show Q + (I - Q) = I by omega] at h1
      rw [h1]
      exact vp_drop_shift some v a0 Q I hD (by omega)
    have hS' : ∀ x ∈ S, x ≤ ((I + 1 : Nat) : Int) ∨ x ∈ rest.map (·.val) := by
      intro x hx
      rcases hS x hx with h | h
      · left; omega
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · left; omega
        · right; exact h
    have ih := vp_deleteatLoop a0 S hn rest w (p + ((I - Q : Nat) : Int)) (i.val + 1) (P + (I - Q))
      (I + 1) (K ++ (a0.drop Q).take (I - Q)) (by omega) (by omega) (by omega) (by omega)
      (by rw [hwl]; exact hv)
      (by rw [hwt, hK, hD, List.map_append, vp_map_take])
      (vp_drop_shift some w a0 I (I + 1) hdw (by omega)) hpw'.2
      (fun j hj => ⟨by have := hpw'.1 j hj; omega, (hbd j (by simp [hj])).2⟩) hS'
      (fun j hj => hmem j (by simp [hj]))
    rw [ih]
    obtain ⟨y, r, hyr⟩ := vp_drop_eq_cons a0 I (by omega)
    have hr := (vp_drop_cons a0 I y r hyr).2
    have hIS : ((I + 1 : Nat) : Int) ∈ S := by
      have h := hmem i (by simp)
      rw [hI] at h
      simpa using h
    have key : vpDrop S (a0.drop Q) (Q + 1) =
        (a0.drop Q).take (I - Q) ++ vpDrop S (a0.drop (I + 1)) (I + 1 + 1) := by
      rw [vp_vpDrop_split S (a0.drop Q) (Q + 1) (I - Q), vp_drop_drop,
        show Q + (I - Q) = I by omega, show Q + 1 + (I - Q) = I + 1 by omega, hyr,
        vp_vpDrop_mem S y r (I + 1) hIS, hr]
      congr 1
      apply vp_vpDrop_none
      intro j h1 h2 hj
      have hlt : ((a0.drop Q).take (I - Q)).length ≤ I - Q := by
        rw [List.length_take]; omega
      rcases hS j hj with h | h
      · omega
      · simp only [List.map_cons, List.mem_cons, List.mem_map] at h
        rcases h with h | ⟨x, hx, rfl⟩
        · omega
        · have := hpw'.1 x hx
          omega
    rw [key, List.append_assoc]

theorem deleteatSortedSpec : DeleteatSortedSpec := by
  intro α a inds hlen hs
  obtain ⟨hpw, hbd⟩ := hs
  rw [vp_dropPositions_eq]
  cases inds with
  | nil =>
    simp only [List.map_nil]
    rw [vp_vpDrop_none [] a 1 (fun j _ _ hj => by simp at hj)]
    rfl
  | cons p0 rest =>
    have hp0 := hbd p0 (by simp)
    have hpw' := List.pairwise_cons.mp hpw
    obtain ⟨P0, hP0⟩ : ∃ P0 : Nat, p0.val = P0 + 1 := ⟨(p0.val - 1).toNat, by omega⟩
    have hchk : ¬ ¬ (1 ≤ p0.val ∧ p0.val ≤ ((a.map some).length : Int)) := by
      intro h; apply h; simp only [List.length_map]; omega
    unfold deleteatInds
    dsimp only
    rw [if_neg hchk]
    simp only [List.length_map]
    have hS : ∀ x ∈ (p0 :: rest).map (·.val), x ≤ ((P0 + 1 : Nat) : Int) ∨
        x ∈ rest.map (·.val) := by
      intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · left; omega
      · right; exact hx
    have hmem : ∀ i ∈ rest, i.val ∈ (p0 :: rest).map (·.val) := by
      intro j hj
      simp only [List.map_cons, List.mem_cons, List.mem_map]
      exact Or.inr ⟨j, hj, rfl⟩
    rw [vp_deleteatLoop a _ hlen rest (a.map some) p0.val (p0.val + 1) P0 (P0 + 1) (a.take P0)
      hP0 (by omega) (by omega) (by omega) (by simp) (vp_map_take _ _ _).symm
      (vp_map_drop _ _ _).symm hpw'.2
      (fun j hj => ⟨by have := hpw'.1 j hj; omega, (hbd j (by simp [hj])).2⟩) hS hmem]
    obtain ⟨y, r, hyr⟩ := vp_drop_eq_cons a P0 (by omega)
    have hr := (vp_drop_cons a P0 y r hyr).2
    have hp0S : ((P0 + 1 : Nat) : Int) ∈ (p0 :: rest).map (·.val) := by
      simp only [List.map_cons, List.mem_cons]; left; omega
    rw [vp_vpDrop_split _ a 1 P0, show 1 + P0 = P0 + 1 by omega, hyr,
      vp_vpDrop_mem _ y r (P0 + 1) hp0S, ← hr, vp_vpDrop_none _ (a.take P0) 1 ?_]
    intro j _ h2 hj
    have hlt : (a.take P0).length ≤ P0 := by rw [List.length_take]; omega
    simp only [List.map_cons, List.mem_cons, List.mem_map] at hj
    rcases hj with h | ⟨x, hx, rfl⟩
    · omega
    · have := hpw'.1 x hx
      omega

/-! ### `deleteat!` with a mask -/

private theorem vp_maskLoop :
    ∀ (ms : List Bool) (rs : List α) (v : Vec α) (p q : Int) (P Q : Nat) (K : List α),
    p = P + 1 → q = Q + 1 → P ≤ Q → Q + rs.length = v.length → ms.length = rs.length →
    v.take P = K.map some → v.drop Q = rs.map some →
    ∃ w, maskLoop v p q ms = (w, p + (((rs.zip ms).filter (fun p => !p.2)).length : Int)) ∧
      w.length = v.length ∧
      w.take (P + ((rs.zip ms).filter (fun p => !p.2)).length) =
        (K ++ ((rs.zip ms).filter (fun p => !p.2)).map Prod.fst).map some
  | [], rs, v, p, _, P, _, K, _, _, _, _, _, hK, _ =>
    ⟨v, by simp [maskLoop], rfl, by simpa using hK⟩
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, hlen, _, _ => absurd hlen (by simp)
  | b :: ms, r :: rs, v, p, q, P, Q, K, hp, hq, hPQ, hQ, hlen, hK, hD => by
    simp only [List.length_cons] at hQ hlen
    obtain ⟨hy, hD1⟩ := vp_drop_cons v Q (some r) (rs.map some) (hD.trans rfl)
    have hc : copyItem v p q = v.set P (some r) := by
      unfold copyItem
      rw [show (p - 1).toNat = P by omega, show (q - 1).toNat = Q by omega, hy] <;> rfl
    have hPv : P < v.length := by omega
    have hstep : maskLoop v p q (b :: ms) =
        maskLoop (v.set P (some r)) (if b then p else p + 1) (q + 1) ms := by
      rw [← hc]; rfl
    cases b
    · obtain ⟨w, hw, hwl, hwt⟩ := vp_maskLoop ms rs (v.set P (some r)) (p + 1) (q + 1) (P + 1)
        (Q + 1) (K ++ [r]) (by omega) (by omega) (by omega) (by rw [List.length_set]; omega)
        (by omega) (by rw [vp_take_set_succ v P _ hPv, hK]; simp) (by
          rw [vp_drop_set_lt v P (Q + 1) _ (by omega)]; exact hD1)
      have e : ((r :: rs).zip (false :: ms)).filter (fun p => !p.2) =
          (r, false) :: (rs.zip ms).filter (fun p => !p.2) := by simp
      simp only [hstep, e, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.map_cons]
      refine ⟨w, ?_, by simp [hwl], ?_⟩
      · rw [hw]
        congr 1
        omega
      · rw [show P + (((rs.zip ms).filter (fun p => !p.2)).length + 1) =
          P + 1 + ((rs.zip ms).filter (fun p => !p.2)).length by omega, hwt]
        simp
    · obtain ⟨w, hw, hwl, hwt⟩ := vp_maskLoop ms rs (v.set P (some r)) p (q + 1) P (Q + 1) K
        hp (by omega) (by omega) (by rw [List.length_set]; omega) (by omega)
        (by rw [vp_take_set_ge v P P _ (Nat.le_refl _)]; exact hK)
        (by rw [vp_drop_set_lt v P (Q + 1) _ (by omega)]; exact hD1)
      have e : ((r :: rs).zip (true :: ms)).filter (fun p => !p.2) =
          (rs.zip ms).filter (fun p => !p.2) := by simp
      simp only [hstep, e, ↓reduceIte]
      exact ⟨w, hw, by simp [hwl], hwt⟩

theorem deleteatMaskSpec : DeleteatMaskSpec := by
  intro α a mask hlen
  have hL : (a.map some).length = a.length := by simp
  unfold deleteatMask
  by_cases hm : mask.length = a.length
  · rw [if_neg (show ¬ (mask.length ≠ (a.map some).length) by rw [hL]; exact fun h => h hm),
      if_pos hm]
    obtain ⟨w, hw, hwl, hwt⟩ := vp_maskLoop mask a (a.map some) 1 1 0 0 [] (by omega) (by omega)
      (Nat.le_refl _) (by simp) hm rfl rfl
    have hF : ((a.zip mask).filter (fun p => !p.2)).length ≤ a.length :=
      Nat.le_trans (List.length_filter_le _ _) (by simp only [List.length_zip]; omega)
    rw [hw]
    dsimp only
    rw [vp_deleteend' w _ ((a.zip mask).filter (fun p => !p.2)).length ?_ ?_ ?_ ?_]
    · simp only [Nat.zero_add, List.nil_append] at hwt
      rw [hwt, List.map_map]
    all_goals (simp (disch := omega) only [vp_wrap_val, vp_wrap64v] <;> omega)
  · rw [if_pos (show mask.length ≠ (a.map some).length by rw [hL]; exact hm), if_neg hm]

/-! ### `keepat!` -/

private theorem vp_sorted_len : ∀ (rem : List JInt64) (B n : Int), B ≤ n →
    rem.Pairwise (fun i j => i.val < j.val) → (∀ k ∈ rem, B < k.val ∧ k.val ≤ n) →
    (rem.length : Int) ≤ n - B
  | [], _, _, h, _, _ => by show ((0 : Nat) : Int) ≤ _; omega
  | k :: rest, B, n, _, hp, hb => by
    have hk := hb k (by simp)
    have hp' := List.pairwise_cons.mp hp
    have ih := vp_sorted_len rest k.val n hk.2 hp'.2
      (fun j hj => ⟨hp'.1 j hj, (hb j (by simp [hj])).2⟩)
    simp only [List.length_cons]
    omega

private theorem vp_keepatLoop (a0 : List α) :
    ∀ (rem : List JInt64) (v : Vec α) (i : Int) (prev : Option Int) (I B : Nat) (K : List α),
    i = I + 1 → I ≤ B → (prev = none ∧ B = 0 ∨ prev = some (B : Int)) →
    v.length = a0.length → v.take I = K.map some → v.drop B = (a0.drop B).map some →
    rem.Pairwise (fun i j => i.val < j.val) →
    (∀ k ∈ rem, (B : Int) < k.val ∧ k.val ≤ a0.length) →
    ∃ w, keepatLoop v i prev rem = ⟨w, .ok (i + rem.length)⟩ ∧ w.length = a0.length ∧
      w.take (I + rem.length) = (K ++ atPositions a0 (rem.map (·.val))).map some
  | [], v, i, _, I, _, K, _, _, _, hv, hK, _, _, _ =>
    ⟨v, by simp [keepatLoop], hv, by simpa [atPositions] using hK⟩
  | k :: rest, v, i, prev, I, B, K, hi, hIB, hprev, hv, hK, hB, hpw, hbd => by
    have hk := hbd k (by simp)
    have hpw' := List.pairwise_cons.mp hpw
    obtain ⟨kN, hkN⟩ : ∃ kN : Nat, k.val = kN + 1 := ⟨(k.val - 1).toNat, by omega⟩
    have hkn : kN < a0.length := by omega
    obtain ⟨y, r, hyr⟩ := vp_drop_eq_cons a0 kN hkn
    obtain ⟨hy, hr⟩ := vp_drop_cons a0 kN y r hyr
    have hvk : v.drop kN = some y :: r.map some := by
      rw [vp_drop_shift some v a0 B kN hB (by omega), hyr, List.map_cons]
    obtain ⟨hvy, hvd⟩ := vp_drop_cons v kN (some y) (r.map some) hvk
    have hstep : keepatLoop v i prev (k :: rest) =
        keepatLoop (if i ≠ k.val then copyItem v i k.val else v) (i + 1) (some k.val) rest := by
      have hb : ¬ ¬ (1 ≤ k.val ∧ k.val ≤ (v.length : Int)) := by intro h; apply h; omega
      rcases hprev with ⟨rfl, -⟩ | rfl
      · simp only [keepatLoop, Bool.false_eq_true, ↓reduceIte, hb]
      · have hlt : (B : Int) < k.val := hk.1
        simp only [keepatLoop, hlt, not_true_eq_false, decide_false, Bool.false_eq_true,
          ↓reduceIte, hb]
    have hnew : ∃ v', (if i ≠ k.val then copyItem v i k.val else v) = v' ∧
        v'.length = a0.length ∧ v'.take (I + 1) = (K ++ [y]).map some ∧
        v'.drop (kN + 1) = (a0.drop (kN + 1)).map some := by
      by_cases hik : i = k.val
      · have hIk : I = kN := by omega
        subst hIk
        refine ⟨v, if_neg (fun h => h hik), hv, ?_, ?_⟩
        · rw [vp_take_succ_of_drop v _ (some y) _ hvk, hK, List.map_append] <;> rfl
        · rw [hvd, hr]
      · refine ⟨v.set I (some y), ?_, by simp [hv], ?_, ?_⟩
        · rw [if_pos hik]
          unfold copyItem
          rw [show (i - 1).toNat = I by omega, show (k.val - 1).toNat = kN by omega, hvy] <;> rfl
        · rw [vp_take_set_succ v I _ (by omega), hK, List.map_append] <;> rfl
        · rw [vp_drop_set_lt v I (kN + 1) _ (by omega), hvd, hr]
    obtain ⟨v', hv'eq, hv'l, hv't, hv'd⟩ := hnew
    obtain ⟨w, hw, hwl, hwt⟩ := vp_keepatLoop a0 rest v' (i + 1) (some k.val) (I + 1) (kN + 1)
      (K ++ [y]) (by omega) (by omega) (Or.inr (congrArg some (by omega))) hv'l hv't hv'd hpw'.2
      (fun j hj => ⟨by have := hpw'.1 j hj; omega, (hbd j (by simp [hj])).2⟩)
    have hat : atPositions a0 ((k :: rest).map (·.val)) = y :: atPositions a0 (rest.map (·.val)) := by
      simp only [atPositions, List.map_cons, List.filterMap_cons,
        show (k.val - 1).toNat = kN by omega, hy]
    refine ⟨w, ?_, hwl, ?_⟩
    · rw [hstep, hv'eq, hw, show i + (((k :: rest).length : Nat) : Int) = i + 1 + rest.length by
        simp only [List.length_cons]; omega]
    · rw [show I + (k :: rest).length = I + 1 + rest.length by simp only [List.length_cons]; omega,
        hwt, hat]
      simp

theorem keepatSortedSpec : KeepatSortedSpec := by
  intro α a inds hlen hs
  obtain ⟨hpw, hbd⟩ := hs
  have hbd0 : ∀ k ∈ inds, ((0 : Nat) : Int) < k.val ∧ k.val ≤ a.length :=
    fun k hk => ⟨by have := (hbd k hk).1; omega, (hbd k hk).2⟩
  obtain ⟨w, hw, hwl, hwt⟩ := vp_keepatLoop a inds (a.map some) 1 none 0 0 [] (by omega)
    (Nat.le_refl _) (Or.inl ⟨rfl, rfl⟩) (by simp) rfl (by simp) hpw hbd0
  have hc := vp_sorted_len inds 0 a.length (by omega) hpw
    (fun k hk => ⟨by have := (hbd k hk).1; omega, (hbd k hk).2⟩)
  simp only [Nat.zero_add, List.nil_append] at hwt
  have hlo : (JInt.wrap .i64 (1 + (inds.length : Int))).val = 1 + inds.length :=
    vp_wrap64v (by omega) (by omega)
  have hhi : (JInt.wrap .i64 (w.length : Int)).val = a.length := by
    rw [hwl]; exact vp_wrap64v (by omega) (by omega)
  unfold keepat
  rw [hw]
  dsimp only
  rw [vp_deleteatRange w (JInt.wrap .i64 (1 + (inds.length : Int))) (JInt.wrap .i64 (w.length : Int))
    (by omega) (by rw [hlo, hhi]; omega) (by rw [hlo, hhi, hwl]; omega), hlo, hhi]
  have hd0 : w.drop (a.length : Int).toNat = [] := by
    rw [show (a.length : Int).toNat = w.length by omega]; simp
  rw [hd0, List.append_nil, show (1 + (inds.length : Int) - 1).toNat = inds.length by omega, hwt]

/-! ### `filter!` -/

private theorem vp_filterLoop (f : α → Bool) (L : Nat) :
    ∀ (R : List α) (v : Vec α) (K : List α), v.length = L → K.length + R.length ≤ L →
      v.take K.length = K.map some → v.drop (L - R.length) = R.map some →
      ∃ w, filterLoop f v (K.length + 1) (R.map some) = (w, (K ++ R.filter f).length + 1) ∧
        w.length = L ∧ w.take (K ++ R.filter f).length = (K ++ R.filter f).map some
  | [], v, K, hv, _, hK, _ => ⟨v, by simp [filterLoop], hv, by simpa using hK⟩
  | r :: R, v, K, hv, hKR, hK, hR => by
    simp only [List.length_cons] at hKR hR
    obtain ⟨_, h2⟩ := vp_drop_cons v (L - (R.length + 1)) (some r) (R.map some) (hR.trans rfl)
    rw [show L - (R.length + 1) + 1 = L - R.length by omega] at h2
    have hKv : K.length < v.length := by omega
    have hd1 : (v.set K.length (some r)).drop (L - R.length) = R.map some := by
      rw [vp_drop_set_lt v K.length (L - R.length) (some r) (by omega)]; exact h2
    have hstep : filterLoop f v (K.length + 1) ((r :: R).map some) =
        filterLoop f (v.set K.length (some r))
          (if f r then K.length + 1 + 1 else K.length + 1) (R.map some) := rfl
    rw [hstep]
    cases hfr : f r
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have e : K ++ (r :: R).filter f = K ++ R.filter f := by simp [List.filter_cons, hfr]
      rw [e]
      exact vp_filterLoop f L R (v.set K.length (some r)) K (by simp [hv]) (by omega)
        (by rw [vp_take_set_ge v K.length K.length _ (Nat.le_refl _)]; exact hK) hd1
    · simp only [↓reduceIte]
      have e : K ++ (r :: R).filter f = (K ++ [r]) ++ R.filter f := by simp [List.filter_cons, hfr]
      have e2 : (K ++ [r]).length = K.length + 1 := by simp
      obtain ⟨w, hw, hwl, hwt⟩ := vp_filterLoop f L R (v.set K.length (some r)) (K ++ [r])
        (by simp [hv]) (by simp; omega)
        (by rw [e2, vp_take_set_succ v K.length _ hKv, hK]; simp) hd1
      rw [e2] at hw
      rw [e]
      exact ⟨w, hw, hwl, hwt⟩

theorem filterBangSpec : FilterBangSpec := by
  intro α f a hlen
  obtain ⟨w, hw, hwl, hwt⟩ := vp_filterLoop f a.length a (a.map some) [] (by simp) (by simp) rfl
    (by simp)
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at hw hwt
  have hF : (a.filter f).length ≤ a.length := List.length_filter_le _ _
  unfold filterBang
  rw [hw]
  dsimp only
  split
  · rename_i h
    simp only [List.length_map] at h
    rw [← hwt, vp_take_all w (a.filter f).length (by omega)]
  · rw [Nat.add_sub_cancel, hwt]

/-! ### `splice!` -/

set_option maxHeartbeats 1000000 in
theorem spliceRangeSpec : SpliceRangeSpec := by
  intro α a f l ins hlen hins hf1 hf2 hl
  have hL : (a.map some).length = a.length := by simp
  have hbnd : ¬ ¬ (f.val > l.val ∨ (1 ≤ f.val ∧ l.val ≤ ((a.map some).length : Int))) := by
    intro h; apply h; rw [hL]; omega
  have hv : ((a.map some).drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat =
      ((a.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat).map some := by
    rw [vp_map_take, vp_map_drop]
  unfold spliceRange
  rewrite [if_neg hbnd]
  -- Opaque names for the concrete `Int` values, so that no proof unfolds `wrapInt` on them.
  generalize e1 : JInt.lit .i64 1 = one
  generalize e2 : JInt.wrap .i64 (ins.length : Int) = mw
  generalize JInt.wrap .i64 ((a.map some).length : Int) = nw
  have hone : one.val = 1 := by rewrite [← e1]; exact vp_one
  have hm : mw.val = ins.length := by
    rewrite [← e2]; exact vp_wrap64e rfl (by omega) (by omega)
  have hlf : (l - f).val = l.val - f.val := vp_wrap64e rfl (by omega) (by omega)
  have hd : (l - f + one).val = l.val - f.val + 1 := by
    show wrapInt .i64 ((l - f).val + one.val) = _
    rewrite [hlf, hone]; exact vp_wrap64e rfl (by omega) (by omega)
  dsimp only
  rewrite [hv]
  generalize nw - l = nl
  generalize f - one = fo
  by_cases hm0 : ins.length = 0
  · rewrite [if_pos (show (mw).val = 0 by rewrite [hm]; omega),
      vp_deleteatRange (a.map some) f l (by rewrite [hL]; omega) (by omega) (by rewrite [hL]; omega)]
    dsimp only
    obtain rfl : ins = [] := List.eq_nil_of_length_eq_zero hm0
    simp only [List.append_nil, List.map_append, vp_map_take, vp_map_drop]
  rewrite [if_neg (show ¬ (mw).val = 0 by rewrite [hm]; omega)]
  obtain ⟨K, hK⟩ : ∃ K : Nat, f.val = K + 1 := ⟨(f.val - 1).toNat, by omega⟩
  obtain ⟨Lc, hLc⟩ : ∃ Lc : Nat, l.val = Lc := ⟨l.val.toNat, by omega⟩
  rewrite [show (f.val - 1).toNat = K by omega, show l.val.toNat = Lc by omega]
  generalize ed : l - f + one = d
  have hd' : d.val = l.val - f.val + 1 := by rewrite [← ed]; exact hd
  clear hd hlf
  generalize edm : d - mw = dm
  have hdm : dm.val = l.val - f.val + 1 - ins.length := by
    rewrite [← edm]
    show wrapInt .i64 (d.val - mw.val) = _
    rewrite [hd', hm]; exact vp_wrap64e rfl (by omega) (by omega)
  generalize emd : mw - d = md
  have hmd : md.val = ins.length - (l.val - f.val + 1) := by
    rewrite [← emd]
    show wrapInt .i64 (mw.val - d.val) = _
    rewrite [hd', hm]; exact vp_wrap64e rfl (by omega) (by omega)
  generalize ex : l - dm + one = idx
  have hidx : idx.val = f.val + ins.length := by
    have h1 : (l - dm).val = f.val - 1 + ins.length := by
      show wrapInt .i64 (l.val - dm.val) = _
      rewrite [hdm]; exact vp_wrap64e (by omega) (by omega) (by omega)
    rewrite [← ex]
    show wrapInt .i64 ((l - dm).val + one.val) = _
    rewrite [h1, hone]; exact vp_wrap64e (by omega) (by omega) (by omega)
  generalize el : l + one = l1
  have hl1 : l1.val = l.val + 1 := by
    rewrite [← el]
    show wrapInt .i64 (l.val + one.val) = _
    rewrite [hone]; exact vp_wrap64e rfl (by omega) (by omega)
  by_cases hlt : (ins.length : Int) < l.val - f.val + 1
  · rewrite [if_pos (show mw.val < d.val by rewrite [hm, hd']; exact hlt)]
    by_cases hfront : fo.val < nl.val
    · rewrite [if_pos hfront,
        vp_deleteatAt' (a.map some) f dm K (Lc - ins.length) (by rewrite [hL]; omega) hf1
          (by rewrite [hL]; omega) (by rewrite [hdm]; omega) (by rewrite [hdm, hL]; omega)
          (by omega) (by rewrite [hdm]; omega)]
      dsimp only
      rewrite [vp_storeAll ins _ f.val K ?_ ?_, vp_take_append_le _ _ _ ?_,
        vp_take_take_le _ _ _ ?_, vp_drop_append_ge _ _ _ ?_, vp_drop_drop' _ _ _ Lc ?_]
      · dsimp only
        simp only [List.map_append, vp_map_take, vp_map_drop]
      all_goals first | omega | (simp only [List.length_append, List.length_take,
        List.length_drop, List.length_map, List.length_replicate]; omega)
    · rewrite [if_neg hfront,
        vp_deleteatAt' (a.map some) idx dm (K + ins.length) Lc (by rewrite [hL]; omega)
          (by rewrite [hidx]; omega) (by rewrite [hidx, hL]; omega) (by rewrite [hdm]; omega)
          (by rewrite [hidx, hdm, hL]; omega) (by rewrite [hidx]; omega)
          (by rewrite [hidx, hdm]; omega)]
      dsimp only
      rewrite [vp_storeAll ins _ f.val K ?_ ?_, vp_take_append_le _ _ _ ?_,
        vp_take_take_le _ _ _ ?_, vp_drop_append_ge _ _ _ ?_, vp_drop_drop' _ _ _ Lc ?_]
      · dsimp only
        simp only [List.map_append, vp_map_take, vp_map_drop]
      all_goals first | omega | (simp only [List.length_append, List.length_take,
        List.length_drop, List.length_map, List.length_replicate]; omega)
  · rewrite [if_neg (show ¬ mw.val < d.val by rewrite [hm, hd']; exact hlt)]
    by_cases hgt : l.val - f.val + 1 < (ins.length : Int)
    · rewrite [if_pos (show mw.val > d.val by rewrite [hm, hd']; exact hgt)]
      by_cases hfront : fo.val < nl.val
      · rewrite [if_pos hfront,
          vp_growat' (a.map some) f md (by rewrite [hL]; omega) hf1 (by rewrite [hL]; omega)
            (by rewrite [hmd]; omega) (by rewrite [hmd]; omega) K (ins.length - (Lc - K))
            (by omega) (by rewrite [hmd]; omega)]
        dsimp only
        rewrite [vp_storeAll ins _ f.val K ?_ ?_, vp_take_append_le _ _ _ ?_,
          vp_take_append_le _ _ _ ?_, vp_take_take_le _ _ _ ?_, vp_drop_append_ge _ _ _ ?_,
          vp_drop_drop' _ _ _ Lc ?_]
        · dsimp only
          simp only [List.map_append, vp_map_take, vp_map_drop]
        all_goals first | omega | (simp only [List.length_append, List.length_take,
          List.length_drop, List.length_map, List.length_replicate]; omega)
      · rewrite [if_neg hfront,
          vp_growat' (a.map some) l1 md (by rewrite [hL]; omega) (by rewrite [hl1]; omega)
            (by rewrite [hl1, hL]; omega) (by rewrite [hmd]; omega) (by rewrite [hmd]; omega) Lc
            (ins.length - (Lc - K)) (by rewrite [hl1]; omega) (by rewrite [hmd]; omega)]
        dsimp only
        rewrite [vp_storeAll ins _ f.val K ?_ ?_, vp_take_append_le _ _ _ ?_,
          vp_take_append_le _ _ _ ?_, vp_take_take_le _ _ _ ?_, vp_drop_append_ge _ _ _ ?_,
          vp_drop_drop' _ _ _ Lc ?_]
        · dsimp only
          simp only [List.map_append, vp_map_take, vp_map_drop]
        all_goals first | omega | (simp only [List.length_append, List.length_take,
          List.length_drop, List.length_map, List.length_replicate]; omega)
    · rewrite [if_neg (show ¬ mw.val > d.val by rewrite [hm, hd']; exact hgt)]
      dsimp only
      rewrite [vp_storeAll ins _ f.val K ?_ ?_, show K + ins.length = Lc by omega]
      · dsimp only
        simp only [List.map_append, vp_map_take, vp_map_drop]
      all_goals first | omega | (simp only [List.length_map]; omega)

/-! ### `resize!` -/

theorem resizeSpec : ResizeSpec := by
  intro α t a n first hlen
  have hL : (a.map some).length = a.length := by simp
  cases hn : toInt n with
  | error e => simp only [resize, hn]
  | ok nl =>
    have hr := vp_r64 nl
    dsimp only
    unfold resize
    rw [hn]
    dsimp only
    rw [hL]
    by_cases h1 : nl.val > (a.length : Int)
    · have hd : (JInt.wrap .i64 (nl.val - (a.length : Int))).val = nl.val - a.length :=
        vp_wrap64e rfl (by omega) (by omega)
      rw [if_pos h1, if_neg (show ¬ nl.val < 0 by omega)]
      cases first
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [vp_growend (a.map some) (JInt.wrap .i64 (nl.val - (a.length : Int))) (by omega)
          (by omega), hd, show (nl.val - (a.length : Int)).toNat = nl.val.toNat - a.length by omega,
          vp_take_all (a.map some ++ List.replicate (nl.val.toNat - a.length) none) nl.val.toNat
            (by simp only [List.length_append, List.length_map, List.length_replicate]; omega)]
      · simp only [↓reduceIte]
        rw [vp_growbeg (a.map some) (JInt.wrap .i64 (nl.val - (a.length : Int))) (by omega)
          (by omega), hd, show (nl.val - (a.length : Int)).toNat = nl.val.toNat - a.length by omega,
          show a.length - nl.val.toNat = 0 by omega, List.drop_zero]
    · rw [if_neg h1]
      by_cases h2 : nl.val ≠ (a.length : Int)
      · rw [if_pos h2]
        by_cases h3 : nl.val < 0
        · rw [if_pos h3, if_pos h3]
        · rw [if_neg h3, if_neg h3]
          have hd : (JInt.wrap .i64 ((a.length : Int) - nl.val)).val = a.length - nl.val :=
            vp_wrap64e rfl (by omega) (by omega)
          cases first
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [vp_deleteend (a.map some) (JInt.wrap .i64 ((a.length : Int) - nl.val)) (by omega)
              (by rw [hd, hL]; omega) (by omega), hd, hL,
              show a.length - ((a.length : Int) - nl.val).toNat = nl.val.toNat by omega,
              show nl.val.toNat - a.length = 0 by omega, List.replicate_zero, List.append_nil]
          · simp only [↓reduceIte]
            rw [vp_deletebeg (a.map some) (JInt.wrap .i64 ((a.length : Int) - nl.val)) (by omega)
              (by rw [hd, hL]; omega) (by omega), hd,
              show nl.val.toNat - a.length = 0 by omega, List.replicate_zero, List.nil_append,
              show ((a.length : Int) - nl.val).toNat = a.length - nl.val.toNat by omega]
      · rw [if_neg h2, if_neg (show ¬ nl.val < 0 by omega)]
        have he : nl.val.toNat = a.length := by omega
        cases first
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [he, Nat.sub_self, List.replicate_zero, List.append_nil,
            vp_take_all (a.map some) a.length (by simp)]
        · simp only [↓reduceIte]
          rw [he, Nat.sub_self, List.replicate_zero, List.nil_append, List.drop_zero]

/-! ### `append!` and `prepend!` -/

theorem appendSelfSpec : AppendSelfSpec := by
  intro α a s _
  exact ⟨rfl, rfl⟩

end

end JuliaLean.ArrayOps
