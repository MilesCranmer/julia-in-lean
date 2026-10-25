import JuliaLean.Transcode.Valid
import JuliaLean.Strings.Length

/-!
# Bridges from the Transcode model to the String index theory

`containsnul(s::String)` and the generic `containsnul(::AbstractString)` agree,
and `length(s::String)` counts the characters of well-formed UTF-8.
-/

namespace JuliaLean.Transcode

open JuliaLean.Strings

/-! ## Iteration traces and `collect` -/

/-- `collectFrom` with the iteration function as a parameter, so its equation
lemmas never unfold `iterate`: whnf of `iterate s i` on a symbolic string does not
terminate in practice, so `collectFrom`'s own equation lemmas cannot be built. -/
def collectWith (g : JInt64 → Option (UInt32 × JInt64)) : Nat → JInt64 → List (UInt32 × JInt64)
  | 0, _ => []
  | k + 1, i =>
    collectFrom.match_1 (motive := fun _ => List (UInt32 × JInt64)) (g i) (fun _ => [])
      (fun c j => (c, i) :: collectWith g k j)

section
attribute [local irreducible] iterate
set_option smartUnfolding false in
theorem collectFrom_eq_collectWith (s : JStr) (k : Nat) (i : JInt64) :
    collectFrom s k i = collectWith (iterate s) k i := rfl
end

theorem collectWith_none (g : JInt64 → Option (UInt32 × JInt64)) (k : Nat) (i : JInt64)
    (h : g i = none) : collectWith g (k + 1) i = [] := by
  simp only [collectWith, h]

theorem collectWith_some (g : JInt64 → Option (UInt32 × JInt64)) (k : Nat) (i : JInt64)
    (c : UInt32) (j : JInt64) (h : g i = some (c, j)) :
    collectWith g (k + 1) i = (c, i) :: collectWith g k j := by
  simp only [collectWith, h]

theorem collectFrom_none (s : JStr) (k : Nat) (i : JInt64) (h : iterate s i = none) :
    collectFrom s (k + 1) i = [] :=
  (collectFrom_eq_collectWith s (k + 1) i).trans (collectWith_none (iterate s) k i h)

theorem collectFrom_some (s : JStr) (k : Nat) (i : JInt64) (c : UInt32) (j : JInt64)
    (h : iterate s i = some (c, j)) : collectFrom s (k + 1) i = (c, i) :: collectFrom s k j :=
  (collectFrom_eq_collectWith s (k + 1) i).trans ((collectWith_some (iterate s) k i c j h).trans
    (congrArg (List.cons (c, i)) (collectFrom_eq_collectWith s k j).symm))

theorem collectFrom_of_trace {s : JStr} {i : JInt64} {xs : List (UInt32 × JInt64)}
    (h : IterTrace s i xs) : ∀ k, xs.length < k → collectFrom s k i = xs := by
  induction h with
  | done h =>
    intro k hk
    cases k with
    | zero => exact absurd hk (Nat.not_lt_zero _)
    | succ k => exact collectFrom_none s k _ h
  | step h _ ih =>
    intro k hk
    cases k with
    | zero => exact absurd hk (Nat.not_lt_zero _)
    | succ k =>
      exact (collectFrom_some s k _ _ _ h).trans
        (congrArg (List.cons _) (ih k (Nat.lt_of_succ_lt_succ hk)))

theorem trace_mem_iterate {s : JStr} {i : JInt64} {xs : List (UInt32 × JInt64)}
    (h : IterTrace s i xs) : ∀ x ∈ xs, ∃ j, iterate s x.2 = some (x.1, j) := by
  induction h with
  | done _ => intro x hx; simp at hx
  | step h _ ih =>
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · subst hx; exact ⟨_, h⟩
    · exact ih x hx

theorem validFrom_length_le (s : JStr) : ∀ (k : Nat) (i : JInt64), (validFrom s k i).length ≤ k := by
  intro k
  induction k with
  | zero => intro i; simp [validFrom]
  | succ k ih =>
    intro i
    simp only [validFrom]
    split
    · simp only [List.length_cons]; have := ih (i + ix 1); omega
    · have := ih (i + ix 1); omega

theorem validZ_of_mem_validFrom (s : JStr) (r : Int) :
    ∀ (k : Nat) (i : JInt64), r ∈ validFrom s k i → validZ s r := by
  intro k
  induction k with
  | zero => intro i h; simp [validFrom] at h
  | succ k ih =>
    intro i h
    simp only [validFrom] at h
    split at h
    · rename_i hv
      rcases List.mem_cons.1 h with h | h
      · subst h; exact (isvalidAt_iff s i).1 hv
      · exact ih _ h
    · exact ih _ h

theorem mem_validFrom_of_validZ (s : JStr) (r : Int) (hr : validZ s r) :
    ∀ (k : Nat) (i : JInt64), 1 ≤ i.val → i.val + k ≤ s.bytes.length + 1 →
      i.val ≤ r → r < i.val + k → r ∈ validFrom s k i := by
  have hs := ncu_small s
  intro k
  induction k with
  | zero => intro i _ _ h1 h2; omega
  | succ k ih =>
    intro i h1 h2 h3 h4
    have e1 : (i + ix 1).val = i.val + 1 := add1_val _ (by omega) (by omega)
    simp only [validFrom]
    by_cases hi : r = i.val
    · subst hi
      simp only [(isvalidAt_iff s i).2 hr, ↓reduceIte]
      exact List.mem_cons_self
    · have hm := ih (i + ix 1) (by omega) (by omega) (by omega) (by omega)
      split
      · exact List.mem_cons_of_mem _ hm
      · exact hm

theorem chars_trace (s : JStr) : ∃ xs, IterTrace s (ix 1) xs ∧
    xs.map (fun x => x.2.val) = validIndices s ∧ chars s = xs.map (·.1) := by
  obtain ⟨xs, ht, hm⟩ := iterateVisitsValid_proven s
  refine ⟨xs, ht, hm, ?_⟩
  have hl : xs.length ≤ s.bytes.length := by
    have := congrArg List.length hm
    rw [List.length_map] at this
    rw [this]; exact validFrom_length_le s _ _
  unfold chars collectPairs
  rw [collectFrom_of_trace ht _ (by omega)]

/-! ## The top byte of a produced character -/

theorem shl16_small (b : UInt8) : (b.toUInt32 <<< 16).toNat < 2 ^ 24 := by
  rw [shl16_toNat]; have := UInt8.toNat_lt b; omega

theorem shl8_small (b : UInt8) : (b.toUInt32 <<< 8).toNat < 2 ^ 24 := by
  rw [shl8_toNat]; have := UInt8.toNat_lt b; omega

theorem shl0_small (b : UInt8) : b.toUInt32.toNat < 2 ^ 24 := by
  rw [UInt8.toNat_toUInt32]; have := UInt8.toNat_lt b; omega

/-- `iterate_continued` only ORs bytes below the top byte. -/
theorem iterateContinued_top (s : JStr) (i : JInt64) (u : UInt32) (l : Nat) (h : TopByte u l) :
    TopByte (iterateContinued s i u).1 l := by
  have h1 : ∀ b : UInt8, TopByte (u ||| b.toUInt32 <<< 16) l :=
    fun b => topByte_or _ _ _ h (shl16_small b)
  have h2 : ∀ b b' : UInt8, TopByte (u ||| b.toUInt32 <<< 16 ||| b'.toUInt32 <<< 8) l :=
    fun b b' => topByte_or _ _ _ (h1 b) (shl8_small b')
  have h3 : ∀ b b' b'' : UInt8,
      TopByte (u ||| b.toUInt32 <<< 16 ||| b'.toUInt32 <<< 8 ||| b''.toUInt32) l :=
    fun b b' b'' => topByte_or _ _ _ (h2 b b') (shl0_small b'')
  unfold iterateContinued
  split
  · exact h
  dsimp only
  split
  · exact h
  split
  · exact h
  split
  · exact h1 _
  split
  · exact h1 _
  split
  · exact h2 _ _
  split
  · exact h2 _ _
  · exact h3 _ _ _

/-! ## `containsnul` -/

/-- containsnul(s::String) (memchr for a zero byte) agrees with containsnul(::AbstractString) = '\0' in s. -/
theorem containsnul_agree (s : JStr) : containsnulStr s = containsnulAbs s := by
  have hs := ncu_small s
  obtain ⟨xs, ht, hmap, hch⟩ := chars_trace s
  unfold containsnulStr containsnulAbs
  rw [hch, Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  constructor
  · intro h0
    obtain ⟨m, hm, hm0⟩ := List.getElem_of_mem h0
    have hbv : bv s ((m : Int) + 1) = 0 := by
      unfold bv
      have e : ((m : Int) + 1).toNat - 1 = m := by omega
      rw [e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some, hm0]
      rfl
    have hv : validZ s ((m : Int) + 1) := ⟨by omega, by omega, thisZ_noncont s _ (by omega)⟩
    have hp : ((m : Int) + 1) ∈ validIndices s :=
      mem_validFrom_of_validZ s _ hv _ (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega)
        (by rw [ix1]; omega) (by rw [ix1]; omega)
    rw [← hmap] at hp
    obtain ⟨x, hx, hxp⟩ := List.mem_map.1 hp
    obtain ⟨j, hit⟩ := trace_mem_iterate ht x hx
    rw [iterate_eq s x.2 (by omega) (by omega)] at hit
    have hcu : cu s x.2 = 0 := UInt8.toNat_inj.1 (by rw [cu_toNat, hxp, hbv]; rfl)
    rw [hcu] at hit
    have hb : (!between (0 : UInt8) 0x80 0xf7) = true := by decide
    simp only [hb, ↓reduceIte] at hit
    have h1 : x.1 = 0 := by
      have := (Prod.mk.inj (Option.some.inj hit)).1
      rw [← this]; decide
    exact List.mem_map.2 ⟨x, hx, h1⟩
  · intro h0
    obtain ⟨x, hx, hx0⟩ := List.mem_map.1 h0
    have hmem : x.2.val ∈ validIndices s := by
      rw [← hmap]; exact List.mem_map_of_mem hx
    obtain ⟨h1, h2, _⟩ := validZ_of_mem_validFrom s _ _ _ hmem
    obtain ⟨j, hit⟩ := trace_mem_iterate ht x hx
    rw [iterate_eq s x.2 h1 h2] at hit
    have hcu0 : cu s x.2 = 0 := by
      by_cases hb : between (cu s x.2) 0x80 0xf7 = true
      · exfalso
        have hb' : (!between (cu s x.2) 0x80 0xf7) = false := by rw [hb]; rfl
        rw [hb'] at hit
        simp only [Bool.false_eq_true, ite_false, Option.some.injEq] at hit
        have htop := iterateContinued_top s x.2 _ _ (topByte_init (cu s x.2))
        rw [hit] at htop
        obtain ⟨r, _, hr⟩ := htop
        rw [hx0] at hr
        rw [between_eq] at hb
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        have : (0x80 : UInt8).toNat = 128 := rfl
        have : (0 : UInt32).toNat = 0 := rfl
        omega
      · have hb' : (!between (cu s x.2) 0x80 0xf7) = true := by
          cases h : between (cu s x.2) 0x80 0xf7
          · rfl
          · exact absurd h hb
        simp only [hb', ↓reduceIte] at hit
        have := (Prod.mk.inj (Option.some.inj hit)).1
        have h24 := shl24_toNat (cu s x.2)
        rw [this, hx0] at h24
        have : (0 : UInt32).toNat = 0 := rfl
        exact UInt8.toNat_inj.1 (by have : (0 : UInt8).toNat = 0 := rfl; omega)
    have hi : x.2.val.toNat - 1 < s.bytes.length := by omega
    unfold cu at hcu0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hcu0
    rw [← hcu0]
    exact List.getElem_mem hi

/-! ## `length` of well-formed UTF-8 -/

theorem u8_7f : (0x7f : UInt8).toNat = 127 := rfl
theorem u8_80 : (0x80 : UInt8).toNat = 128 := rfl
theorem u8_8f : (0x8f : UInt8).toNat = 143 := rfl
theorem u8_90 : (0x90 : UInt8).toNat = 144 := rfl
theorem u8_9f : (0x9f : UInt8).toNat = 159 := rfl
theorem u8_a0 : (0xa0 : UInt8).toNat = 160 := rfl
theorem u8_bf : (0xbf : UInt8).toNat = 191 := rfl
theorem u8_c2 : (0xc2 : UInt8).toNat = 194 := rfl
theorem u8_df : (0xdf : UInt8).toNat = 223 := rfl
theorem u8_e0 : (0xe0 : UInt8).toNat = 224 := rfl
theorem u8_e1 : (0xe1 : UInt8).toNat = 225 := rfl
theorem u8_ed : (0xed : UInt8).toNat = 237 := rfl
theorem u8_ef : (0xef : UInt8).toNat = 239 := rfl
theorem u8_f0 : (0xf0 : UInt8).toNat = 240 := rfl
theorem u8_f1 : (0xf1 : UInt8).toNat = 241 := rfl
theorem u8_f3 : (0xf3 : UInt8).toNat = 243 := rfl
theorem u8_f4 : (0xf4 : UInt8).toNat = 244 := rfl

/-- The byte classes of a well-formed character. -/
theorem wfChar_shape (c : List UInt8) (h : wfChar c = true) :
    (∃ a, c = [a] ∧ a.toNat < 128) ∨
    (∃ a b, c = [a, b] ∧ 192 ≤ a.toNat ∧ a.toNat < 224 ∧ 128 ≤ b.toNat ∧ b.toNat < 192) ∨
    (∃ a b d, c = [a, b, d] ∧ 224 ≤ a.toNat ∧ a.toNat < 240 ∧ 128 ≤ b.toNat ∧ b.toNat < 192 ∧
      128 ≤ d.toNat ∧ d.toNat < 192) ∨
    (∃ a b d e, c = [a, b, d, e] ∧ 240 ≤ a.toNat ∧ a.toNat ≤ 247 ∧ 128 ≤ b.toNat ∧
      b.toNat < 192 ∧ 128 ≤ d.toNat ∧ d.toNat < 192 ∧ 128 ≤ e.toNat ∧ e.toNat < 192) := by
  rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, _ | ⟨f, t⟩⟩⟩⟩⟩
  · simp [wfChar] at h
  · simp only [wfChar, decide_eq_true_eq, UInt8.le_iff_toNat_le, u8_7f] at h
    exact Or.inl ⟨a, rfl, by omega⟩
  · simp only [wfChar, isC, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, u8_80,
      u8_bf, u8_c2, u8_df] at h
    exact Or.inr (Or.inl ⟨a, b, rfl, by omega, by omega, by omega, by omega⟩)
  · simp only [wfChar, isC, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, u8_80,
      u8_bf, u8_a0, u8_9f, u8_e1, u8_ef, beq_iff_eq, ← UInt8.toNat_inj, u8_e0, u8_ed] at h
    obtain ⟨hd, h⟩ := h
    refine Or.inr (Or.inr (Or.inl ⟨a, b, d, rfl, ?_⟩))
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
    · split at h
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
  · simp only [wfChar, isC, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le, u8_80,
      u8_bf, u8_90, u8_8f, u8_f1, u8_f3, beq_iff_eq, ← UInt8.toNat_inj, u8_f0, u8_f4] at h
    obtain ⟨⟨hd, he⟩, h⟩ := h
    refine Or.inr (Or.inr (Or.inr ⟨a, b, d, e, rfl, ?_⟩))
    split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
    · split at h
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
  · simp [wfChar] at h

/-- The byte at position `pre.length + 1 + i` is the `i`-th byte of `c`. -/
theorem bv_at (s : JStr) (pre c t : List UInt8) (h : s.bytes = pre ++ (c ++ t)) (i : Nat)
    (p : Int) (hp : p = pre.length + 1 + i) (hi : i < c.length) :
    bv s p = (c.getD i 0).toNat := by
  unfold bv
  have e : p.toNat - 1 = pre.length + i := by omega
  rw [e, h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]

/-- A well-formed character starting at `p` has `length - 1` absorbed positions. -/
theorem absCnt_char (s : JStr) (pre c t : List UInt8) (h : s.bytes = pre ++ (c ++ t))
    (hc : wfChar c = true) (p : Int) (hp : p = pre.length + 1) :
    absCnt s c.length p + 1 = c.length := by
  have hp1 : 1 ≤ p := by omega
  rcases wfChar_shape c hc with ⟨a, rfl, ha⟩ | ⟨a, b, rfl, ha1, ha2, hb1, hb2⟩ |
      ⟨a, b, d, rfl, ha1, ha2, hb1, hb2, hd1, hd2⟩ |
      ⟨a, b, d, e, rfl, ha1, ha2, hb1, hb2, hd1, hd2, he1, he2⟩
  · have e0 : bv s p = a.toNat := bv_at s pre [a] t h 0 p (by omega) (by simp)
    show absCnt s (0 + 1) p + 1 = 1
    rw [absCnt_nabs s 0 p (cont_not_abs s p (by omega))]; rfl
  · have e0 : bv s p = a.toNat := bv_at s pre [a, b] t h 0 p (by omega) (by simp)
    have e1 : bv s (p + 1) = b.toNat := bv_at s pre [a, b] t h 1 _ (by omega) (by simp)
    have t1 := thisZ_lead1 s p (p + 1) rfl hp1 (by omega) (by omega)
    show absCnt s (1 + 1) p + 1 = 2
    rw [absCnt_nabs s 1 p (cont_not_abs s p (by omega)), absCnt_abs s 0 (p + 1) (by omega)]; rfl
  · have e0 : bv s p = a.toNat := bv_at s pre [a, b, d] t h 0 p (by omega) (by simp)
    have e1 : bv s (p + 1) = b.toNat := bv_at s pre [a, b, d] t h 1 _ (by omega) (by simp)
    have e2 : bv s (p + 1 + 1) = d.toNat := bv_at s pre [a, b, d] t h 2 _ (by omega) (by simp)
    have t1 := thisZ_lead1 s p (p + 1) rfl hp1 (by omega) (by omega)
    have t2 := thisZ_lead2 s p (p + 1 + 1) (by omega) hp1 (by omega) (by omega) (by omega)
    show absCnt s (2 + 1) p + 1 = 3
    rw [absCnt_nabs s 2 p (cont_not_abs s p (by omega))]
    show absCnt s (1 + 1) (p + 1) + 1 = 3
    rw [absCnt_abs s 1 (p + 1) (by omega), absCnt_abs s 0 (p + 1 + 1) (by omega)]; rfl
  · have e0 : bv s p = a.toNat := bv_at s pre [a, b, d, e] t h 0 p (by omega) (by simp)
    have e1 : bv s (p + 1) = b.toNat := bv_at s pre [a, b, d, e] t h 1 _ (by omega) (by simp)
    have e2 : bv s (p + 1 + 1) = d.toNat := bv_at s pre [a, b, d, e] t h 2 _ (by omega) (by simp)
    have e2' : bv s (p + 2) = d.toNat := bv_at s pre [a, b, d, e] t h 2 _ (by omega) (by simp)
    have e3 : bv s (p + 1 + 1 + 1) = e.toNat :=
      bv_at s pre [a, b, d, e] t h 3 _ (by omega) (by simp)
    have t1 := thisZ_lead1 s p (p + 1) rfl hp1 (by omega) (by omega)
    have t2 := thisZ_lead2 s p (p + 1 + 1) (by omega) hp1 (by omega) (by omega) (by omega)
    have t3 := thisZ_lead3 s p (p + 1 + 1 + 1) (by omega) hp1 (by omega) (by omega) (by omega)
      (by omega)
    show absCnt s (3 + 1) p + 1 = 4
    rw [absCnt_nabs s 3 p (cont_not_abs s p (by omega))]
    show absCnt s (2 + 1) (p + 1) + 1 = 4
    rw [absCnt_abs s 2 (p + 1) (by omega)]
    show 1 + absCnt s (1 + 1) (p + 1 + 1) + 1 = 4
    rw [absCnt_abs s 1 (p + 1 + 1) (by omega), absCnt_abs s 0 (p + 1 + 1 + 1) (by omega)]; rfl

theorem absCnt_add (s : JStr) : ∀ (a b : Nat) (p : Int),
    absCnt s (a + b) p = absCnt s a p + absCnt s b (p + a) := by
  intro a
  induction a with
  | zero => intro b p; simp [absCnt]
  | succ a ih =>
    intro b p
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [absCnt]
    rw [ih b (p + 1)]
    have e : p + 1 + (a : Int) = p + ((a + 1 : Nat) : Int) := by omega
    rw [e]; omega

theorem absCnt_chars (s : JStr) : ∀ (cs : List (List UInt8)) (pre : List UInt8) (p : Int),
    s.bytes = pre ++ cs.flatten → (∀ c ∈ cs, wfChar c = true) → p = pre.length + 1 →
    absCnt s cs.flatten.length p + cs.length = cs.flatten.length := by
  intro cs
  induction cs with
  | nil => intros; rfl
  | cons c cs ih =>
    intro pre p h hc hp
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [absCnt_add]
    have h1 := absCnt_char s pre c cs.flatten (by rw [h, List.flatten_cons])
      (hc c List.mem_cons_self) p hp
    have h2 := ih (pre ++ c) (p + c.length) (by rw [h, List.flatten_cons, List.append_assoc])
      (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')) (by rw [List.length_append]; omega)
    omega

/-- For well-formed UTF-8, Julia's length(s) is the number of characters. -/
theorem length_of_valid (s : JStr) (cs : List (List UInt8))
    (hc : ∀ c ∈ cs, wfChar c = true) (hs : s.bytes = cs.flatten) :
    (length s).val = cs.length := by
  have hsm := ncu_small s
  have hv := validFrom_absCnt s s.bytes.length (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega)
  rw [ix1] at hv
  have ha := absCnt_chars s cs [] 1 (by rw [hs]; rfl) hc (by simp)
  have hn : s.bytes.length = cs.flatten.length := by rw [hs]
  rw [length_validIndices]
  unfold validIndices
  rw [hn] at hv ⊢
  omega

end JuliaLean.Transcode
