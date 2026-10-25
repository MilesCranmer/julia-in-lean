import JuliaLean.Strings.Props

/-!
# Characters of a String as a function of its bytes

`iterate(s::String, i)` (`base/strings/string.jl:508-538`) reads only the bytes
from `i` to the end of `s`. `dec l` is that computation on the byte list
`l = codeunits(s)[i:end]`: the character and the number of bytes it spans.
`decAll` repeats it, and equals `collect(s)` (`chars_eq_decAll`). This gives
`collect(a * b) == [collect(a); collect(b)]` when `b` does not start with a
continuation byte, and `collect(s) == [collect(s[1:p]); collect(s[p+1:end])]` at
every position `p` that iteration visits.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings

/-- `iterate` at the head of the byte list `l` (with `ncodeunits` at the end of
`l`): the character and its length in bytes. Mirrors `iterate(s, i)` and
`iterate_continued` (`base/strings/string.jl:508-538`) branch by branch. -/
def dec : List UInt8 → UInt32 × Nat
  | [] => (0, 1)
  | b0 :: r0 =>
    if !between b0 0x80 0xf7 then (b0.toUInt32 <<< 24, 1)
    else if b0.toUInt32 <<< 24 < 0xc0000000 then (b0.toUInt32 <<< 24, 1)
    else
      match r0 with
      | [] => (b0.toUInt32 <<< 24, 1)
      | b1 :: r1 =>
        if !isCont b1 then (b0.toUInt32 <<< 24, 1)
        else if (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) < 0xe0000000 then
          (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16, 2)
        else
          match r1 with
          | [] => (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16, 2)
          | b2 :: r2 =>
            if !isCont b2 then (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16, 2)
            else if (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) < 0xf0000000 then
              (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8, 3)
            else
              match r2 with
              | [] => (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8, 3)
              | b3 :: _ =>
                if !isCont b3 then (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8, 3)
                else (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32, 4)

theorem dec_len (l : List UInt8) (h : l ≠ []) : 1 ≤ (dec l).2 ∧ (dec l).2 ≤ l.length := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r⟩⟩⟩⟩
  · exact absurd rfl h
  all_goals (simp only [dec]; repeat' split) <;> simp <;> omega

theorem dec_le4 (l : List UInt8) : (dec l).2 ≤ 4 := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r⟩⟩⟩⟩
  all_goals (simp only [dec]; repeat' split) <;> simp

/-- Appending bytes that do not start with a continuation byte does not change
the first character. -/
theorem dec_append_noncont (l x : List UInt8) (h : l ≠ [])
    (hx : ∀ c t, x = c :: t → isCont c = false) : dec (l ++ x) = dec l := by
  rcases x with _ | ⟨c, t⟩
  · simp
  have hc := hx c t rfl
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r⟩⟩⟩⟩
  · exact absurd rfl h
  · simp only [List.cons_append, List.nil_append, dec, hc, Bool.not_false, ↓reduceIte]
  · simp only [List.cons_append, List.nil_append, dec, hc, Bool.not_false, ↓reduceIte]
  · simp only [List.cons_append, List.nil_append, dec, hc, Bool.not_false, ↓reduceIte]
  · simp only [List.cons_append, dec]

theorem dec_stop1 (b0 c : UInt8) (t : List UInt8) (hk : (dec (b0 :: c :: t)).2 ≤ 1) :
    dec (b0 :: c :: t) = dec [b0] := by
  cases hcv : isCont c
  · simp only [dec, hcv, Bool.not_false, ↓reduceIte]
  cases hb : between b0 0x80 0xf7
  · simp only [dec, hb, Bool.not_false, ↓reduceIte]
  by_cases hu : b0.toUInt32 <<< 24 < 0xc0000000
  · simp only [dec, hb, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exfalso
  simp only [dec, hb, hu, hcv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hk
  repeat' split at hk
  all_goals simp at hk

theorem dec_stop2 (b0 b1 c : UInt8) (t : List UInt8) (hk : (dec (b0 :: b1 :: c :: t)).2 ≤ 2) :
    dec (b0 :: b1 :: c :: t) = dec [b0, b1] := by
  cases hcv : isCont c
  · simp only [dec, hcv, Bool.not_false, ↓reduceIte]
  cases hb : between b0 0x80 0xf7
  · simp only [dec, hb, Bool.not_false, ↓reduceIte]
  by_cases hu : b0.toUInt32 <<< 24 < 0xc0000000
  · simp only [dec, hb, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hc1 : isCont b1
  · simp only [dec, hb, hu, hc1, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hu1 : (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) < 0xe0000000
  · simp only [dec, hb, hu, hc1, hu1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exfalso
  simp only [dec, hb, hu, hc1, hu1, hcv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hk
  repeat' split at hk
  all_goals simp at hk

theorem dec_stop3 (b0 b1 b2 c : UInt8) (t : List UInt8)
    (hk : (dec (b0 :: b1 :: b2 :: c :: t)).2 ≤ 3) : dec (b0 :: b1 :: b2 :: c :: t) = dec [b0, b1, b2] := by
  cases hcv : isCont c
  · simp only [dec, hcv, Bool.not_false, ↓reduceIte]
  cases hb : between b0 0x80 0xf7
  · simp only [dec, hb, Bool.not_false, ↓reduceIte]
  by_cases hu : b0.toUInt32 <<< 24 < 0xc0000000
  · simp only [dec, hb, hu, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hc1 : isCont b1
  · simp only [dec, hb, hu, hc1, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hu1 : (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) < 0xe0000000
  · simp only [dec, hb, hu, hc1, hu1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hc2 : isCont b2
  · simp only [dec, hb, hu, hc1, hu1, hc2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hu2 : (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) < 0xf0000000
  · simp only [dec, hb, hu, hc1, hu1, hc2, hu2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exfalso
  simp only [dec, hb, hu, hc1, hu1, hc2, hu2, hcv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hk
  simp at hk

/-- If the first character of `l ++ x` lies within `l`, it is the first
character of `l`. -/
theorem dec_append_stop (l x : List UInt8) (h : l ≠ []) (hk : (dec (l ++ x)).2 ≤ l.length) :
    dec (l ++ x) = dec l := by
  rcases x with _ | ⟨c, t⟩
  · simp
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r⟩⟩⟩⟩
  · exact absurd rfl h
  · exact dec_stop1 b0 c t hk
  · exact dec_stop2 b0 b1 c t hk
  · exact dec_stop3 b0 b1 b2 c t hk
  · simp only [List.cons_append, dec]

/-- `collect` over the byte list, character by character. -/
def decAll (l : List UInt8) : List UInt32 :=
  match l with
  | [] => []
  | b :: t => (dec (b :: t)).1 :: decAll ((b :: t).drop (dec (b :: t)).2)
termination_by l.length
decreasing_by
  have := dec_len (b :: t) (List.cons_ne_nil _ _)
  simp only [List.length_drop, List.length_cons] at this ⊢
  omega

theorem decAll_nil : decAll [] = [] := by rw [decAll]

theorem decAll_cons (l : List UInt8) (h : l ≠ []) :
    decAll l = (dec l).1 :: decAll (l.drop (dec l).2) := by
  rcases l with _ | ⟨b, t⟩
  · exact absurd rfl h
  · rw [decAll]

theorem decAll_length : ∀ (k : Nat) (l : List UInt8), l.length ≤ k → (decAll l).length ≤ l.length := by
  intro k
  induction k with
  | zero =>
    intro l hl
    have h0 : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0; rw [decAll_nil]; exact Nat.le_refl _
  | succ k ih =>
    intro l hl
    by_cases h : l = []
    · subst h; rw [decAll_nil]; exact Nat.le_refl _
    · have hd := dec_len l h
      rw [decAll_cons l h, List.length_cons]
      have := ih (l.drop (dec l).2) (by simp only [List.length_drop]; omega)
      simp only [List.length_drop] at this
      omega

theorem decAll_append_noncont (x : List UInt8) (hx : ∀ c t, x = c :: t → isCont c = false) :
    ∀ (k : Nat) (l : List UInt8), l.length ≤ k → decAll (l ++ x) = decAll l ++ decAll x := by
  intro k
  induction k with
  | zero =>
    intro l hl
    have h0 : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0; simp [decAll_nil]
  | succ k ih =>
    intro l hl
    by_cases h : l = []
    · subst h; simp [decAll_nil]
    · have hd := dec_len l h
      have he := dec_append_noncont l x h hx
      rw [decAll_cons (l ++ x) (by simp [h]), decAll_cons l h, he,
        List.drop_append_of_le_length hd.2, ih (l.drop (dec l).2) (by simp only [List.length_drop]; omega)]
      rfl

/-! ## Positions that iteration visits -/

/-- `p` (a byte count) is the start of a character in the walk of `decAll l`. -/
inductive Visits (l : List UInt8) : Nat → Prop
  | zero : Visits l 0
  | step {p : Nat} : Visits l p → p < l.length → Visits l (p + (dec (l.drop p)).2)

theorem visits_le {l : List UInt8} {p : Nat} (h : Visits l p) : p ≤ l.length := by
  induction h with
  | zero => omega
  | @step p _ hp _ =>
    have := dec_len (l.drop p) (by simp only [ne_eq, List.drop_eq_nil_iff]; omega)
    simp only [List.length_drop] at this
    omega

theorem visits_front {l : List UInt8} {p : Nat} (h : Visits l p) :
    p = 0 ∨ (l ≠ [] ∧ (dec l).2 ≤ p ∧ Visits (l.drop (dec l).2) (p - (dec l).2)) := by
  induction h with
  | zero => exact Or.inl rfl
  | @step p hv hp ih =>
    right
    have hl : l ≠ [] := by intro e; subst e; simp at hp
    refine ⟨hl, ?_⟩
    rcases ih with h0 | ⟨_, hk, hv'⟩
    · subst h0
      simp only [List.drop_zero, Nat.zero_add, Nat.le_refl, Nat.sub_self, true_and]
      exact .zero
    · have hlen := dec_len (l.drop p) (by simp only [ne_eq, List.drop_eq_nil_iff]; omega)
      refine ⟨by omega, ?_⟩
      have hs := Visits.step hv' (by simp only [List.length_drop]; omega)
      rw [List.drop_drop, show (dec l).2 + (p - (dec l).2) = p by omega] at hs
      rwa [show p - (dec l).2 + (dec (l.drop p)).2 = p + (dec (l.drop p)).2 - (dec l).2 by omega] at hs

/-- Splitting the walk at a visited position. -/
theorem decAll_split : ∀ (k : Nat) (l : List UInt8) (p : Nat), l.length ≤ k → Visits l p →
    decAll l = decAll (l.take p) ++ decAll (l.drop p) := by
  intro k
  induction k with
  | zero =>
    intro l p hl _
    have h0 : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h0; simp [decAll_nil]
  | succ k ih =>
    intro l p hl hv
    have hle := visits_le hv
    rcases visits_front hv with h0 | ⟨hne, hk, hv'⟩
    · subst h0; simp [decAll_nil]
    · have hd := dec_len l hne
      have hlpos : 0 < l.length := by
        rcases l with _ | ⟨_, _⟩
        · exact absurd rfl hne
        · simp
      have htp : l.take p ≠ [] := by
        simp only [ne_eq, List.take_eq_nil_iff, not_or]; exact ⟨by omega, hne⟩
      have hstop : dec (l.take p ++ l.drop p) = dec (l.take p) :=
        dec_append_stop _ _ htp (by rw [List.take_append_drop, List.length_take]; omega)
      rw [List.take_append_drop] at hstop
      have ih' := ih (l.drop (dec l).2) (p - (dec l).2) (by simp only [List.length_drop]; omega) hv'
      rw [decAll_cons l hne, decAll_cons (l.take p) htp, ← hstop, ih', List.drop_take, List.drop_drop,
        show (dec l).2 + (p - (dec l).2) = p by omega]
      rfl

theorem visits_take_step (l : List UInt8) (p : Nat) (hv : Visits l p) (hp : p < l.length) :
    decAll (l.take (p + (dec (l.drop p)).2)) = decAll (l.take p) ++ [(dec (l.drop p)).1] := by
  have hq := Visits.step hv hp
  have s1 := decAll_split _ l p (Nat.le_refl _) hv
  have s2 := decAll_split _ l _ (Nat.le_refl _) hq
  have hne : l.drop p ≠ [] := by simp only [ne_eq, List.drop_eq_nil_iff]; omega
  have s3 : decAll (l.drop p) = (dec (l.drop p)).1 :: decAll (l.drop (p + (dec (l.drop p)).2)) := by
    rw [decAll_cons _ hne, List.drop_drop]
  rw [s3, s2] at s1
  have e : decAll (l.take (p + (dec (l.drop p)).2)) ++ decAll (l.drop (p + (dec (l.drop p)).2)) =
      (decAll (l.take p) ++ [(dec (l.drop p)).1]) ++ decAll (l.drop (p + (dec (l.drop p)).2)) := by
    rw [s1, List.append_assoc]; rfl
  exact List.append_cancel_right e

/-! ## Bridge to `iterate` -/

theorem drop_cons_getD (l : List UInt8) (m : Nat) (h : m < l.length) :
    l.drop m = l.getD m 0 :: l.drop (m + 1) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some,
    List.drop_eq_getElem_cons h]

theorem add_ix_val (i : JInt64) (k : Int) (h0 : 0 ≤ k) (hk : k ≤ 4) (h1 : 0 ≤ i.val) (h2 : i.val < 2 ^ 62 + 8) :
    (i + ix k).val = i.val + k := by
  rw [add_val _ _ (by rw [ix_val k (by omega) (by omega)]; omega)
    (by rw [ix_val k (by omega) (by omega)]; omega), ix_val k (by omega) (by omega)]

theorem ixc1 : ix ((1 : Nat) : Int) = ix 1 := rfl
theorem ixc2 : ix ((2 : Nat) : Int) = ix 2 := rfl
theorem ixc3 : ix ((3 : Nat) : Int) = ix 3 := rfl
theorem ixc4 : ix ((4 : Nat) : Int) = ix 4 := rfl

/-- `iterate(s, i)` at an in-bounds index is `dec` of the bytes from `i` on. -/
theorem iter_dec (s : JStr) (i : JInt64) (h1 : 1 ≤ i.val) (h2 : i.val ≤ s.bytes.length) :
    iterate s i = some ((dec (s.bytes.drop (i.val - 1).toNat)).1,
      i + ix ((dec (s.bytes.drop (i.val - 1).toNat)).2 : Int)) := by
  have hsm := ncu_small s
  have e1 : (i + ix 1).val = i.val + 1 := add_ix_val i 1 (by omega) (by omega) (by omega) (by omega)
  have f2 : (i + ix 2).val = i.val + 2 := add_ix_val i 2 (by omega) (by omega) (by omega) (by omega)
  have f3 : (i + ix 3).val = i.val + 3 := add_ix_val i 3 (by omega) (by omega) (by omega) (by omega)
  have f4 : (i + ix 4).val = i.val + 4 := add_ix_val i 4 (by omega) (by omega) (by omega) (by omega)
  have p2 : i + ix 1 + ix 1 = i + ix 2 := Subtype.ext (by
    rw [add_ix_val (i + ix 1) 1 (by omega) (by omega) (by rw [e1]; omega) (by rw [e1]; omega), e1, f2]
      <;> omega)
  have q3 : i + ix 2 + ix 1 = i + ix 3 := Subtype.ext (by
    rw [add_ix_val (i + ix 2) 1 (by omega) (by omega) (by rw [f2]; omega) (by rw [f2]; omega), f2, f3]
      <;> omega)
  have q4 : i + ix 3 + ix 1 = i + ix 4 := Subtype.ext (by
    rw [add_ix_val (i + ix 3) 1 (by omega) (by omega) (by rw [f3]; omega) (by rw [f3]; omega), f3, f4]
      <;> omega)
  have c0 : cu s i = s.bytes.getD (i.val - 1).toNat 0 := by
    show s.bytes.getD (i.val.toNat - 1) 0 = _; congr 1; omega
  have c1 : cu s (i + ix 1) = s.bytes.getD ((i.val - 1).toNat + 1) 0 := by
    show s.bytes.getD ((i + ix 1).val.toNat - 1) 0 = _; rw [e1]; congr 1; omega
  have c2 : cu s (i + ix 2) = s.bytes.getD ((i.val - 1).toNat + 1 + 1) 0 := by
    show s.bytes.getD ((i + ix 2).val.toNat - 1) 0 = _; rw [f2]; congr 1; omega
  have c3 : cu s (i + ix 3) = s.bytes.getD ((i.val - 1).toNat + 1 + 1 + 1) 0 := by
    show s.bytes.getD ((i + ix 3).val.toNat - 1) 0 = _; rw [f3]; congr 1; omega
  rw [iterate_eq s i h1 h2, c0, drop_cons_getD s.bytes (i.val - 1).toNat (by omega)]
  by_cases g1 : i.val + 1 > (s.bytes.length : Int)
  · rw [List.drop_eq_nil_of_le (by omega)]
    simp only [iterateContinued, e1, ncu_val, g1, decide_true, ↓reduceIte]
    generalize s.bytes.getD (i.val - 1).toNat 0 = b0
    cases hb : between b0 0x80 0xf7 <;> by_cases hu : b0.toUInt32 <<< 24 < 0xc0000000 <;>
      simp only [dec, hb, hu, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, ixc1,
        decide_true, decide_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false, ite_self]
  · rw [drop_cons_getD s.bytes _ (by omega)]
    by_cases g2 : i.val + 2 > (s.bytes.length : Int)
    · rw [List.drop_eq_nil_of_le (by omega)]
      simp only [iterateContinued, e1, f2, p2, ncu_val, c1, g1, g2, decide_true, decide_false,
        Bool.true_or, ↓reduceIte]
      generalize s.bytes.getD (i.val - 1).toNat 0 = b0
      generalize s.bytes.getD ((i.val - 1).toNat + 1) 0 = b1
      cases hb : between b0 0x80 0xf7 <;> by_cases hu : b0.toUInt32 <<< 24 < 0xc0000000 <;>
        cases hc1 : isCont b1 <;>
        by_cases hu1 : (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) < 0xe0000000 <;>
        simp only [dec, hb, hu, hc1, hu1, Bool.not_true, Bool.not_false, Bool.false_eq_true,
          ↓reduceIte, ixc1, ixc2, decide_true, decide_false, Bool.true_or, Bool.false_or, Bool.or_true,
          Bool.or_false, ite_self]
    · rw [drop_cons_getD s.bytes _ (by omega)]
      by_cases g3 : i.val + 3 > (s.bytes.length : Int)
      · rw [List.drop_eq_nil_of_le (by omega)]
        simp only [iterateContinued, e1, f2, f3, p2, q3, ncu_val, c1, c2, g1, g2, g3, decide_true,
          decide_false, Bool.true_or, Bool.false_or, ↓reduceIte]
        generalize s.bytes.getD (i.val - 1).toNat 0 = b0
        generalize s.bytes.getD ((i.val - 1).toNat + 1) 0 = b1
        generalize s.bytes.getD ((i.val - 1).toNat + 1 + 1) 0 = b2
        cases hb : between b0 0x80 0xf7 <;> by_cases hu : b0.toUInt32 <<< 24 < 0xc0000000 <;>
          cases hc1 : isCont b1 <;>
          by_cases hu1 : (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) < 0xe0000000 <;>
          cases hc2 : isCont b2 <;>
          by_cases hu2 : (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) < 0xf0000000 <;>
          simp only [dec, hb, hu, hc1, hu1, hc2, hu2, Bool.not_true, Bool.not_false, Bool.false_eq_true,
            ↓reduceIte, ixc1, ixc2, ixc3, decide_true, decide_false, Bool.true_or, Bool.false_or,
            Bool.or_true, Bool.or_false, ite_self]
      · rw [drop_cons_getD s.bytes _ (by omega)]
        simp only [iterateContinued, e1, f2, f3, p2, q3, q4, ncu_val, c1, c2, c3, g1, g2, g3,
          decide_false, Bool.false_or, ↓reduceIte]
        generalize s.bytes.getD (i.val - 1).toNat 0 = b0
        generalize s.bytes.getD ((i.val - 1).toNat + 1) 0 = b1
        generalize s.bytes.getD ((i.val - 1).toNat + 1 + 1) 0 = b2
        generalize s.bytes.getD ((i.val - 1).toNat + 1 + 1 + 1) 0 = b3
        cases hb : between b0 0x80 0xf7 <;> by_cases hu : b0.toUInt32 <<< 24 < 0xc0000000 <;>
          cases hc1 : isCont b1 <;>
          by_cases hu1 : (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16) < 0xe0000000 <;>
          cases hc2 : isCont b2 <;>
          by_cases hu2 : (b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8) < 0xf0000000 <;>
          cases hc3 : isCont b3 <;>
          simp only [dec, hb, hu, hc1, hu1, hc2, hu2, hc3, Bool.not_true, Bool.not_false,
            Bool.false_eq_true, ↓reduceIte, ixc1, ixc2, ixc3, ixc4, decide_true, decide_false,
            Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false, ite_self]

/-- `collectFrom` with the iteration function as a parameter, so that proofs
never unfold `iterate` on a symbolic string. -/
def collectDec (g : JInt64 → Option (UInt32 × JInt64)) : Nat → JInt64 → List (UInt32 × JInt64)
  | 0, _ => []
  | k + 1, i =>
    collectFrom.match_1 (motive := fun _ => List (UInt32 × JInt64)) (g i) (fun _ => [])
      (fun c j => (c, i) :: collectDec g k j)

section
attribute [local irreducible] iterate
set_option smartUnfolding false in
theorem collectFrom_eq_collectDec (s : JStr) (k : Nat) (i : JInt64) :
    collectFrom s k i = collectDec (iterate s) k i := rfl
end

theorem collectDec_none (g : JInt64 → Option (UInt32 × JInt64)) (k : Nat) (i : JInt64) (h : g i = none) :
    collectDec g (k + 1) i = [] := by
  simp only [collectDec, h]

theorem collectDec_some (g : JInt64 → Option (UInt32 × JInt64)) (k : Nat) (i j : JInt64) (c : UInt32)
    (h : g i = some (c, j)) : collectDec g (k + 1) i = (c, i) :: collectDec g k j := by
  simp only [collectDec, h]

theorem drop_shift (l : List UInt8) (x : Int) (m : Nat) (h : 1 ≤ x) :
    (l.drop (x - 1).toNat).drop m = l.drop (x + (m : Int) - 1).toNat := by
  rw [List.drop_drop, show (x - 1).toNat + m = (x + (m : Int) - 1).toNat by omega]

theorem chars_from (s : JStr) (g : JInt64 → Option (UInt32 × JInt64)) (hg : ∀ i, g i = iterate s i) :
    ∀ (k : Nat) (i : JInt64), 1 ≤ i.val → i.val ≤ s.bytes.length + 1 →
    (s.bytes.length : Int) + 1 - i.val < k →
    (collectDec g k i).map (·.1) = decAll (s.bytes.drop (i.val - 1).toNat) := by
  have hsm := ncu_small s
  intro k
  induction k with
  | zero => intro i _ _ hk; omega
  | succ k ih =>
    intro i h1 h2 hk
    by_cases hend : i.val = s.bytes.length + 1
    · rw [collectDec_none g k i ((hg i).trans (iterate_end s i hend)), List.map_nil,
        List.drop_eq_nil_of_le (by omega), decAll_nil]
    · have hne : s.bytes.drop (i.val - 1).toNat ≠ [] := by
        simp only [ne_eq, List.drop_eq_nil_iff]; omega
      have hd := dec_len _ hne
      have h4 := dec_le4 (s.bytes.drop (i.val - 1).toNat)
      simp only [List.length_drop] at hd
      have hj := add_ix_val i ((dec (s.bytes.drop (i.val - 1).toNat)).2 : Int) (by omega) (by omega)
        (by omega) (by omega)
      have hrec := ih (i + ix ((dec (s.bytes.drop (i.val - 1).toNat)).2 : Int))
        (by rw [hj]; omega) (by rw [hj]; omega) (by rw [hj]; omega)
      rw [hj] at hrec
      rw [collectDec_some g k i _ _ ((hg i).trans (iter_dec s i h1 (by omega))), List.map_cons, hrec,
        decAll_cons _ hne, drop_shift s.bytes i.val _ h1]

/-- `collect(s)` is `decAll` of its bytes. -/
theorem chars_eq_decAll (s : JStr) : chars s = decAll s.bytes := by
  have hsm := ncu_small s
  unfold chars collectPairs
  rw [collectFrom_eq_collectDec, chars_from s (iterate s) (fun _ => rfl) _ (ix 1) (by simp)
    (by rw [ix1]; omega) (by rw [ix1]; omega), ix1]
  simp

/-- At a valid index, `s[i]` is the character `dec` reads and `nextind(s, i)` is
`i` plus its length. -/
theorem at_valid (s : JStr) (i : JInt64) (hv : validZ s i.val) :
    getindex s i = .ok (dec (s.bytes.drop (i.val - 1).toNat)).1 ∧
      nextZ s i.val = i.val + (dec (s.bytes.drop (i.val - 1).toNat)).2 := by
  have hsm := ncu_small s
  obtain ⟨h1, h2, h3⟩ := hv
  have hid := iter_dec s i h1 h2
  obtain ⟨c, j, hit, hj⟩ := iterate_valid s i ⟨h1, h2, h3⟩
  have h4 := dec_le4 (s.bytes.drop (i.val - 1).toNat)
  refine ⟨?_, ?_⟩
  · have hcu : codeunit s i = .ok (cu s i) := by
      unfold codeunit; rw [if_pos ⟨h1, by rw [ncu_val]; exact h2⟩]
    have hva : isvalidAt s i = true := (isvalidAt_iff s i).2 ⟨h1, h2, h3⟩
    have hgi : getindex s i = (if !between (cu s i) 0x80 0xf7 then .ok ((cu s i).toUInt32 <<< 24)
        else getindexContinued s i ((cu s i).toUInt32 <<< 24)) := by
      unfold getindex; rw [hcu]; rfl
    have hboth := (iterate_eq s i h1 h2).symm.trans hid
    rw [hgi]
    by_cases hb : (!between (cu s i) 0x80 0xf7) = true
    · rw [if_pos hb] at hboth ⊢
      simp only [Option.some.injEq, Prod.mk.injEq] at hboth
      rw [hboth.1]
    · rw [if_neg hb] at hboth ⊢
      by_cases hu : (cu s i).toUInt32 <<< 24 < 0xc0000000
      · have hic : iterateContinued s i ((cu s i).toUInt32 <<< 24) = ((cu s i).toUInt32 <<< 24, i + ix 1) := by
          unfold iterateContinued; rw [if_pos hu]
        have hgc : getindexContinued s i ((cu s i).toUInt32 <<< 24) = .ok ((cu s i).toUInt32 <<< 24) := by
          unfold getindexContinued; rw [if_pos hu, if_pos hva]
        rw [hic] at hboth
        simp only [Option.some.injEq, Prod.mk.injEq] at hboth
        rw [hgc, hboth.1]
      · have hgc : getindexContinued s i ((cu s i).toUInt32 <<< 24) =
            .ok (iterateContinued s i ((cu s i).toUInt32 <<< 24)).1 := by
          unfold getindexContinued; rw [if_neg hu]
        simp only [Option.some.injEq] at hboth
        rw [hgc, hboth]
  · rw [hid] at hit
    simp only [Option.some.injEq, Prod.mk.injEq] at hit
    rw [← hj, ← hit.2, add_ix_val _ _ (by omega) (by omega) (by omega) (by omega)]

theorem visits_valid (s : JStr) {p : Nat} (h : Visits s.bytes p) :
    p < s.bytes.length → validZ s (p + 1) := by
  have hsm := ncu_small s
  induction h with
  | zero => intro hn; exact valid_one s (by omega)
  | @step p hv hp ih =>
    intro hn
    have hvp := ih hp
    have hix : (ix ((p : Int) + 1)).val = p + 1 := ix_val _ (by omega) (by omega)
    have hvp' : validZ s (ix ((p : Int) + 1)).val := by rw [hix]; exact hvp
    have hat := (at_valid s _ hvp').2
    rw [hix, show ((p : Int) + 1 - 1).toNat = p by omega] at hat
    obtain ⟨_, _, _, n4⟩ := nextZ_nextValid s (p + 1) (by omega) (by omega)
    have := n4 (by rw [hat]; omega)
    rw [hat] at this
    have e : (p : Int) + 1 + ((dec (s.bytes.drop p)).2 : Int) =
        (((p + (dec (s.bytes.drop p)).2 : Nat)) : Int) + 1 := by omega
    rwa [e] at this

end JuliaLean.StringUtil
