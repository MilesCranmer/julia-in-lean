import JuliaLean.Strings.Props

/-!
# `length(s::String)` counts the iteration steps

`_length_continued` (`base/strings/string.jl:635-658`) starts from
`ncodeunits(s)` and subtracts one for every continuation byte that a lead byte
absorbs. A position `r` is absorbed exactly when `thisZ s r < r`.
-/

namespace JuliaLean.Strings

/-- The number of absorbed positions among `p, p+1, ..., p+k-1`. -/
def absCnt (s : JStr) : Nat → Int → Nat
  | 0, _ => 0
  | k + 1, p => (if thisZ s p < p then 1 else 0) + absCnt s k (p + 1)

theorem validFrom_absCnt (s : JStr) : ∀ (k : Nat) (i : JInt64), 1 ≤ i.val →
    i.val + k ≤ s.bytes.length + 1 → (validFrom s k i).length + absCnt s k i.val = k := by
  intro k
  induction k with
  | zero => intro i _ _; rfl
  | succ k ih =>
    intro i h1 h2
    have hs := ncu_small s
    have e1 : (i + ix 1).val = i.val + 1 := add1_val _ (by omega) (by omega)
    have hk := ih (i + ix 1) (by omega) (by omega)
    rw [e1] at hk
    simp only [validFrom, absCnt]
    rw [isvalidAt_eq]
    have hle := (thisZ_le s i.val).1
    by_cases hv : thisZ s i.val = i.val
    · have hvz : validZ s i.val := ⟨h1, by omega, hv⟩
      have hn : ¬ thisZ s i.val < i.val := by omega
      simp only [decide_eq_true_eq]
      rw [if_pos hvz, if_neg hn, List.length_cons]
      omega
    · have hvz : ¬ validZ s i.val := fun h => hv h.2.2
      have hn : thisZ s i.val < i.val := by omega
      simp only [decide_eq_true_eq]
      rw [if_neg hvz, if_pos hn]
      omega

/-- Structure of an absorbed position `r`: its character starts at a lead byte
`q = thisZ s r` at most three bytes back, and the bytes in between are
continuation bytes allowed by the lead byte. -/
theorem absorbed_struct (s : JStr) (r : Int) (h : thisZ s r < r) :
    1 ≤ thisZ s r ∧ r - 3 ≤ thisZ s r ∧ 192 ≤ bv s (thisZ s r) ∧ bv s (thisZ s r) ≤ 247 ∧
    (128 ≤ bv s r ∧ bv s r < 192) ∧
    (thisZ s r + 1 < r →
      (128 ≤ bv s (thisZ s r + 1) ∧ bv s (thisZ s r + 1) < 192) ∧ 224 ≤ bv s (thisZ s r)) ∧
    (thisZ s r + 2 < r →
      (128 ≤ bv s (thisZ s r + 2) ∧ bv s (thisZ s r + 2) < 192) ∧ 240 ≤ bv s (thisZ s r)) := by
  rcases thisZ_cases s r with h' | h' | h' | h'
  · omega
  · rw [h'.1]
    exact ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩,
      fun _ => by omega, fun _ => by omega⟩
  · rw [h'.1]
    have e1 : r - 2 + 1 = r - 1 := by omega
    rw [e1]
    exact ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩,
      fun _ => ⟨⟨by omega, by omega⟩, by omega⟩, fun _ => by omega⟩
  · rw [h'.1]
    have e1 : r - 3 + 1 = r - 2 := by omega
    have e2 : r - 3 + 2 = r - 1 := by omega
    rw [e1, e2]
    exact ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩,
      fun _ => ⟨⟨by omega, by omega⟩, by omega⟩, fun _ => ⟨⟨by omega, by omega⟩, by omega⟩⟩

/-- Every absorbed position after `p` belongs to a character starting at `p` or later. -/
abbrev LenInv (s : JStr) (p : Int) : Prop := ∀ r, p < r → thisZ s r < r → p ≤ thisZ s r

theorem inv_nonlead (s : JStr) (p : Int) (hI : LenInv s p)
    (hl : ¬ (192 ≤ bv s p ∧ bv s p ≤ 247)) :
    ¬ thisZ s (p + 1) < p + 1 ∧ LenInv s (p + 1) := by
  constructor
  · intro ha
    have h1 := hI (p + 1) (by omega) ha
    obtain ⟨_, s2, s3, s4, -⟩ := absorbed_struct s (p + 1) ha
    have hq : thisZ s (p + 1) = p := by omega
    rw [hq] at s3 s4; omega
  · intro r hr ha
    have h1 := hI r (by omega) ha
    obtain ⟨_, s2, s3, s4, -⟩ := absorbed_struct s r ha
    refine Classical.byContradiction fun hc => ?_
    have hq : thisZ s r = p := by omega
    rw [hq] at s3 s4; omega

theorem inv_lead1 (s : JStr) (p : Int) (hI : LenInv s p)
    (hstop : ¬ ((128 ≤ bv s (p + 1) ∧ bv s (p + 1) < 192) ∧ 224 ≤ bv s p)) :
    LenInv s (p + 1) := by
  intro r hr ha
  have h1 := hI r (by omega) ha
  obtain ⟨_, s2, _, _, _, s6, _⟩ := absorbed_struct s r ha
  refine Classical.byContradiction fun hc => ?_
  have hq : thisZ s r = p := by omega
  rw [hq] at s6
  exact hstop (s6 (by omega))

theorem inv_lead2 (s : JStr) (p : Int) (hI : LenInv s p)
    (hc1 : 128 ≤ bv s (p + 1) ∧ bv s (p + 1) < 192)
    (hstop : ¬ ((128 ≤ bv s (p + 2) ∧ bv s (p + 2) < 192) ∧ 240 ≤ bv s p)) :
    LenInv s (p + 2) := by
  intro r hr ha
  have h1 := hI r (by omega) ha
  obtain ⟨_, s2, s3, _, _, _, s7⟩ := absorbed_struct s r ha
  refine Classical.byContradiction fun hc => ?_
  by_cases hq : thisZ s r = p
  · rw [hq] at s7
    exact hstop (s7 (by omega))
  · have hq' : thisZ s r = p + 1 := by omega
    rw [hq'] at s3; omega

theorem inv_lead3 (s : JStr) (p : Int)
    (hc1 : 128 ≤ bv s (p + 1) ∧ bv s (p + 1) < 192)
    (hc2 : 128 ≤ bv s (p + 2) ∧ bv s (p + 2) < 192) :
    LenInv s (p + 3) := by
  intro r hr ha
  obtain ⟨_, s2, s3, _, _, _, _⟩ := absorbed_struct s r ha
  refine Classical.byContradiction fun hc => ?_
  by_cases hq : thisZ s r = p + 1
  · rw [hq] at s3; omega
  · have hq' : thisZ s r = p + 2 := by omega
    rw [hq'] at s3; omega

theorem abs_iff_cont (s : JStr) (r : Int) (hc : (128 ≤ bv s r ∧ bv s r < 192) → thisZ s r < r) :
    (thisZ s r < r ↔ (128 ≤ bv s r ∧ bv s r < 192)) :=
  ⟨fun ha => (absorbed_struct s r ha).2.2.2.2.1, hc⟩

theorem lead_cond_iff (b : UInt8) :
    (!(decide (0xc0 ≤ b) && decide (b ≤ 0xf7))) = true ↔ ¬ (192 ≤ b.toNat ∧ b.toNat ≤ 247) := by
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    UInt8.le_iff_toNat_le]
  have : (0xc0 : UInt8).toNat = 192 := rfl
  have : (0xf7 : UInt8).toNat = 247 := rfl
  omega

theorem cond_iff (x : Bool) (l m : UInt8) :
    (!(x && decide (l ≥ m))) = true ↔ ¬ (x = true ∧ m.toNat ≤ l.toNat) := by
  cases x <;> simp [UInt8.le_iff_toNat_le]

theorem isCont_cu (s : JStr) (i : JInt64) :
    isCont (cu s i) = true ↔ (128 ≤ bv s i.val ∧ bv s i.val < 192) := by
  rw [isCont_eq, cu_toNat]; simp

theorem absCnt_abs (s : JStr) (k : Nat) (p : Int) (h : thisZ s p < p) :
    absCnt s (k + 1) p = 1 + absCnt s k (p + 1) := by
  simp [absCnt, h]

theorem absCnt_nabs (s : JStr) (k : Nat) (p : Int) (h : ¬ thisZ s p < p) :
    absCnt s (k + 1) p = absCnt s k (p + 1) := by
  simp [absCnt, h]

theorem subB_val (c : JInt64) (b : Bool) (h1 : 0 ≤ c.val) (h2 : c.val ≤ 2 ^ 62) :
    (c - bInt b).val = c.val - (if b then 1 else 0) := by
  rw [sub_val _ _ (by rw [bInt_val]; split <;> omega) (by rw [bInt_val]; split <;> omega), bInt_val]

theorem cont_not_abs (s : JStr) (r : Int) (hc : ¬ (128 ≤ bv s r ∧ bv s r < 192)) :
    ¬ thisZ s r < r := fun h => hc (absorbed_struct s r h).2.2.2.2.1

theorem e224 : (0xe0 : UInt8).toNat = 224 := rfl
theorem e240 : (0xf0 : UInt8).toNat = 240 := rfl
theorem e192 : (0xc0 : UInt8).toNat = 192 := rfl
theorem e247 : (0xf7 : UInt8).toNat = 247 := rfl

theorem lenLoop_spec (s : JStr) : ∀ (k : Nat) (i c : JInt64), 1 ≤ i.val →
    i.val + k = s.bytes.length → LenInv s i.val →
    absCnt s k (i.val + 1) ≤ c.val → c.val ≤ 2 ^ 62 →
    (lenLoop s (ncodeunits s) k i (cu s i) c).val = c.val - absCnt s k (i.val + 1) := by
  have hs := ncu_small s
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i c hi1 hk hI hc1 hc2
    cases k with
    | zero => simp [lenLoop, absCnt]
    | succ k =>
      have e1 : (i + ix 1).val = i.val + 1 := add1_val _ (by omega) (by omega)
      simp only [lenLoop]
      split
      · rename_i hcnd
        rw [lead_cond_iff, cu_toNat] at hcnd
        obtain ⟨hna, hI1⟩ := inv_nonlead s i.val hI hcnd
        have hcnt := absCnt_nabs s k (i.val + 1) hna
        rw [hcnt] at hc1
        rw [ih k (by omega) _ _ (by rw [e1]; omega) (by rw [e1]; omega) (by rw [e1]; exact hI1)
          (by rw [e1]; exact hc1) hc2, e1, hcnt]
      · rename_i hcnd
        rw [lead_cond_iff, cu_toNat] at hcnd
        have hl : 192 ≤ bv s i.val ∧ bv s i.val ≤ 247 := Classical.byContradiction hcnd
        have hx := isCont_cu s (i + ix 1)
        rw [e1] at hx
        by_cases hc : 128 ≤ bv s (i.val + 1) ∧ bv s (i.val + 1) < 192
        · have hcnt := absCnt_abs s k (i.val + 1)
            (by rw [thisZ_lead1 s i.val (i.val + 1) rfl hi1 hl hc]; omega)
          rw [hcnt] at hc1
          rw [hx.2 hc]
          have ec := subB_val c true (by omega) hc2
          simp only [ite_true] at ec
          split
          · rename_i hcnd2
            rw [cond_iff, cu_toNat, e224] at hcnd2
            have hstop : ¬ ((128 ≤ bv s (i.val + 1) ∧ bv s (i.val + 1) < 192) ∧ 224 ≤ bv s i.val) :=
              fun h => hcnd2 ⟨rfl, h.2⟩
            rw [ih k (by omega) _ _ (by rw [e1]; omega) (by rw [e1]; omega)
              (by rw [e1]; exact inv_lead1 s i.val hI hstop) (by rw [ec, e1]; omega) (by rw [ec]; omega)]
            rw [ec, e1, hcnt]; omega
          · rename_i hcnd2
            rw [cond_iff, cu_toNat, e224] at hcnd2
            have h224 : 224 ≤ bv s i.val := Classical.byContradiction fun h => hcnd2 fun h' => h h'.2
            cases k with
            | zero =>
              dsimp only
              rw [ec, hcnt]; simp [absCnt]
            | succ k =>
              dsimp only
              have e2 : (i + ix 1 + ix 1).val = i.val + 2 := by
                rw [add1_val _ (by rw [e1]; omega) (by rw [e1]; omega), e1]; omega
              have ei : i.val + 1 + 1 = i.val + 2 := by omega
              rw [ei] at hcnt hc1
              have hx2 := isCont_cu s (i + ix 1 + ix 1)
              rw [e2] at hx2
              by_cases hc2' : 128 ≤ bv s (i.val + 2) ∧ bv s (i.val + 2) < 192
              · have hcnt2 := absCnt_abs s k (i.val + 2)
                  (by rw [thisZ_lead2 s i.val (i.val + 2) rfl hi1 ⟨h224, hl.2⟩ hc hc2']; omega)
                rw [hcnt2] at hc1
                rw [hx2.2 hc2']
                have ec2 := subB_val (c - bInt true) true (by rw [ec]; omega) (by rw [ec]; omega)
                simp only [ite_true] at ec2
                split
                · rename_i hcnd3
                  rw [cond_iff, cu_toNat, e240] at hcnd3
                  rw [ih k (by omega) _ _ (by rw [e2]; omega) (by rw [e2]; omega)
                    (by rw [e2]; exact inv_lead2 s i.val hI hc (fun h => hcnd3 ⟨rfl, h.2⟩))
                    (by rw [ec2, ec, e2]; omega) (by rw [ec2, ec]; omega)]
                  rw [ec2, ec, e2, hcnt, hcnt2]; omega
                · rename_i hcnd3
                  rw [cond_iff, cu_toNat, e240] at hcnd3
                  have h240 : 240 ≤ bv s i.val :=
                    Classical.byContradiction fun h => hcnd3 fun h' => h h'.2
                  cases k with
                  | zero =>
                    dsimp only
                    rw [ec2, ec, hcnt, hcnt2]; simp [absCnt]; omega
                  | succ k =>
                    dsimp only
                    have e3 : (i + ix 1 + ix 1 + ix 1).val = i.val + 3 := by
                      rw [add1_val _ (by rw [e2]; omega) (by rw [e2]; omega), e2]; omega
                    have ej : i.val + 2 + 1 = i.val + 3 := by omega
                    rw [ej] at hcnt2 hc1
                    have hx3 := isCont_cu s (i + ix 1 + ix 1 + ix 1)
                    rw [e3] at hx3
                    have hI3 : LenInv s (i + ix 1 + ix 1 + ix 1).val := by
                      rw [e3]; exact inv_lead3 s i.val hc hc2'
                    by_cases hc3 : 128 ≤ bv s (i.val + 3) ∧ bv s (i.val + 3) < 192
                    · have hcnt3 := absCnt_abs s k (i.val + 3)
                        (by rw [thisZ_lead3 s i.val (i.val + 3) rfl hi1 ⟨h240, hl.2⟩ hc hc2' hc3]; omega)
                      rw [hcnt3] at hc1
                      rw [hx3.2 hc3]
                      have ec3 := subB_val (c - bInt true - bInt true) true (by rw [ec2, ec]; omega)
                        (by rw [ec2, ec]; omega)
                      simp only [ite_true] at ec3
                      rw [ih k (by omega) _ _ (by rw [e3]; omega) (by rw [e3]; omega) hI3
                        (by rw [ec3, ec2, ec, e3]; omega) (by rw [ec3, ec2, ec]; omega)]
                      rw [ec3, ec2, ec, e3, hcnt, hcnt2, hcnt3]; omega
                    · have hcnt3 := absCnt_nabs s k (i.val + 3) (cont_not_abs s _ hc3)
                      rw [hcnt3] at hc1
                      have hf : isCont (cu s (i + ix 1 + ix 1 + ix 1)) = false := by
                        cases h : isCont (cu s (i + ix 1 + ix 1 + ix 1))
                        · rfl
                        · exact absurd (hx3.1 h) hc3
                      rw [hf]
                      have ec3 := subB_val (c - bInt true - bInt true) false (by rw [ec2, ec]; omega)
                        (by rw [ec2, ec]; omega)
                      simp only [Bool.false_eq_true, ite_false] at ec3
                      rw [ih k (by omega) _ _ (by rw [e3]; omega) (by rw [e3]; omega) hI3
                        (by rw [ec3, ec2, ec, e3]; omega) (by rw [ec3, ec2, ec]; omega)]
                      rw [ec3, ec2, ec, e3, hcnt, hcnt2, hcnt3]; omega
              · have hcnt2 := absCnt_nabs s k (i.val + 2) (cont_not_abs s _ hc2')
                rw [hcnt2] at hc1
                have hf : isCont (cu s (i + ix 1 + ix 1)) = false := by
                  cases h : isCont (cu s (i + ix 1 + ix 1))
                  · rfl
                  · exact absurd (hx2.1 h) hc2'
                rw [hf]
                have ec2 := subB_val (c - bInt true) false (by rw [ec]; omega) (by rw [ec]; omega)
                simp only [Bool.false_eq_true, ite_false] at ec2
                simp only [Bool.false_and, Bool.not_false, ite_true]
                rw [ih k (by omega) _ _ (by rw [e2]; omega) (by rw [e2]; omega)
                  (by rw [e2]; exact inv_lead2 s i.val hI hc (fun h => hc2' h.1))
                  (by rw [ec2, ec, e2]; omega) (by rw [ec2, ec]; omega)]
                rw [ec2, ec, e2, hcnt, hcnt2]; omega
        · have hcnt := absCnt_nabs s k (i.val + 1) (cont_not_abs s _ hc)
          rw [hcnt] at hc1
          have hf : isCont (cu s (i + ix 1)) = false := by
            cases h : isCont (cu s (i + ix 1))
            · rfl
            · exact absurd (hx.1 h) hc
          rw [hf]
          have ec := subB_val c false (by omega) hc2
          simp only [Bool.false_eq_true, ite_false] at ec
          simp only [Bool.false_and, Bool.not_false, ite_true]
          rw [ih k (by omega) _ _ (by rw [e1]; omega) (by rw [e1]; omega)
            (by rw [e1]; exact inv_lead1 s i.val hI (fun h => hc h.1))
            (by rw [ec, e1]; omega) (by rw [ec]; omega)]
          rw [ec, e1, hcnt]; omega

/-- `length(s)` counts the valid indices. -/
theorem length_validIndices (s : JStr) : (length s).val = (validIndices s).length := by
  have hs := ncu_small s
  have hv := validFrom_absCnt s s.bytes.length (ix 1) (by rw [ix1]; omega) (by rw [ix1]; omega)
  rw [ix1] at hv
  unfold validIndices
  unfold length lengthContinued
  rw [ncu_val, ix1]
  by_cases h1 : 1 < s.bytes.length
  · simp only [show decide ((1 : Int) < s.bytes.length) = true from decide_eq_true (by omega),
      Bool.not_true, Bool.false_eq_true, ite_false]
    obtain ⟨m, hm⟩ : ∃ m, s.bytes.length = m + 1 := ⟨s.bytes.length - 1, by omega⟩
    have hc0 := absCnt_nabs s m 1 (by rw [thisZ_one]; omega)
    rw [hm] at hv
    rw [hc0] at hv
    have e : ((s.bytes.length : Int) - 1).toNat = m := by omega
    rw [e]
    have hI : LenInv s (ix 1).val := fun r hr _ => by
      rw [ix1] at hr ⊢; exact thisZ_pos s r (by omega)
    have := lenLoop_spec s m (ix 1) (ncodeunits s) (by simp) (by rw [ix1]; omega) hI
      (by rw [ix1, ncu_val]; omega) (by rw [ncu_val]; omega)
    rw [ix1, ncu_val] at this
    rw [this, hm]; omega
  · simp only [show decide ((1 : Int) < s.bytes.length) = false from decide_eq_false (by omega),
      Bool.not_false, ite_true]
    rw [ncu_val]
    have : absCnt s s.bytes.length 1 = 0 := by
      rcases (show s.bytes.length = 0 ∨ s.bytes.length = 1 by omega) with h | h <;> rw [h]
      · rfl
      · simp [absCnt, thisZ_one]
    omega

theorem iterTrace_unique {s : JStr} {i : JInt64} {xs ys : List (UInt32 × JInt64)}
    (h1 : IterTrace s i xs) (h2 : IterTrace s i ys) : xs = ys := by
  induction h1 generalizing ys with
  | done h =>
    cases h2 with
    | done _ => rfl
    | step h' _ => rw [h] at h'; cases h'
  | step h _ ih =>
    cases h2 with
    | done h' => rw [h] at h'; cases h'
    | step h' t' =>
      rw [h] at h'; cases h'
      rw [ih t']

/-- `length(s)` equals the number of characters iteration yields, for any byte string. -/
def LengthIterateSteps : Prop :=
  ∀ (s : JStr) (xs : List (UInt32 × JInt64)), IterTrace s (ix 1) xs → (length s).val = xs.length

theorem lengthIterateSteps_proven : LengthIterateSteps := by
  intro s xs hx
  obtain ⟨ys, hy, hmap⟩ := iterateVisitsValid_proven s
  rw [iterTrace_unique hx hy, length_validIndices, ← hmap, List.length_map]

end JuliaLean.Strings
