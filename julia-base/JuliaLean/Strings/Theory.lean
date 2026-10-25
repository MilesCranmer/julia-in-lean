import JuliaLean.Strings.Search

/-!
# Index theory of the String model

Arithmetic lemmas, byte-class lemmas, and integer-level mirrors (`thisZ`,
`leadZ`, `nextZ`) of the index functions, with the bridge lemmas that connect
them to the `JInt` model. Positions are one-based `Int`s; `bv s p` is the byte
at position `p` as a natural number.
-/

namespace JuliaLean.Strings

/-! ## Int arithmetic far from overflow -/

theorem wrap64_val (x : Int) (h1 : -(2 ^ 63) ≤ x) (h2 : x < 2 ^ 63) :
    (JInt.wrap .i64 x).val = x := by
  show wrapInt .i64 x = x
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  constructor <;> simp <;> omega

theorem ix_val (x : Int) (h1 : -(2 ^ 63) ≤ x) (h2 : x < 2 ^ 63) : (ix x).val = x :=
  wrap64_val x h1 h2

theorem add_val (a b : JInt64) (h1 : -(2 ^ 63) ≤ a.val + b.val) (h2 : a.val + b.val < 2 ^ 63) :
    (a + b).val = a.val + b.val := wrap64_val _ h1 h2

theorem sub_val (a b : JInt64) (h1 : -(2 ^ 63) ≤ a.val - b.val) (h2 : a.val - b.val < 2 ^ 63) :
    (a - b).val = a.val - b.val := wrap64_val _ h1 h2

@[simp] theorem ix0 : (ix 0).val = 0 := rfl
@[simp] theorem ix1 : (ix 1).val = 1 := rfl
@[simp] theorem ix2 : (ix 2).val = 2 := rfl
@[simp] theorem ix3 : (ix 3).val = 3 := rfl

theorem ncu_val (s : JStr) : (ncodeunits s).val = s.bytes.length := by
  have := s.small
  exact ix_val _ (by omega) (by omega)

theorem ncu_small (s : JStr) : (s.bytes.length : Int) < 2 ^ 62 := by
  have := s.small; omega

theorem bInt_val (b : Bool) : (bInt b).val = if b then 1 else 0 := by
  cases b <;> rfl

/-! ## Byte classes -/

set_option maxRecDepth 100000 in
theorem isCont_table : ∀ n : Fin 256,
    isCont (UInt8.ofNat n.val) = decide (128 ≤ n.val ∧ n.val < 192) := by decide

theorem isCont_eq (b : UInt8) : isCont b = decide (128 ≤ b.toNat ∧ b.toNat < 192) := by
  have h := isCont_table ⟨b.toNat, UInt8.toNat_lt b⟩
  simpa [UInt8.ofNat_toNat] using h

theorem between_eq (b lo hi : UInt8) :
    between b lo hi = (decide (lo.toNat ≤ b.toNat) && decide (b.toNat ≤ hi.toNat)) := by
  simp [between, UInt8.le_iff_toNat_le]

theorem u8lt (a b : UInt8) : decide (a < b) = decide (a.toNat < b.toNat) := by
  simp [UInt8.lt_iff_toNat_lt]

theorem u8le (a b : UInt8) : decide (a ≤ b) = decide (a.toNat ≤ b.toNat) := by
  simp [UInt8.le_iff_toNat_le]

/-- The byte at one-based position `p`, as `cu` reads it. -/
def bv (s : JStr) (p : Int) : Nat := (s.bytes.getD (p.toNat - 1) 0).toNat

theorem cu_toNat (s : JStr) (i : JInt64) : (cu s i).toNat = bv s i.val := rfl

theorem bv_lt (s : JStr) (p : Int) : bv s p < 256 := UInt8.toNat_lt _

/-- Continuation byte. -/
abbrev cB (x : Nat) : Bool := decide (128 ≤ x ∧ x < 192)

/-! ## Integer-level mirrors -/

/-- `_thisind_str` for `1 ≤ p ≤ n`. -/
def thisZ (s : JStr) (p : Int) : Int :=
  if !(cB (bv s p) && decide (p - 1 > 0)) then p
  else if decide (192 ≤ bv s (p - 1)) && decide (bv s (p - 1) ≤ 247) then p - 1
  else if !(cB (bv s (p - 1)) && decide (p - 2 > 0)) then p
  else if decide (224 ≤ bv s (p - 2)) && decide (bv s (p - 2) ≤ 247) then p - 2
  else if !(cB (bv s (p - 2)) && decide (p - 3 > 0)) then p
  else if decide (240 ≤ bv s (p - 3)) && decide (bv s (p - 3) ≤ 247) then p - 3 else p

/-- `nextindFromLead` for a lead byte `l` at `p`, `n = ncodeunits`. -/
def leadZ (s : JStr) (p n : Int) (l : Nat) : Int :=
  if p + 1 > n then p + 1
  else if !cB (bv s (p + 1)) then p + 1
  else if decide (p + 2 > n) || decide (l < 224) then p + 2
  else if !cB (bv s (p + 2)) then p + 2
  else if decide (p + 3 > n) || decide (l < 240) then p + 3
  else if !cB (bv s (p + 3)) then p + 3 else p + 4

/-- `_nextind_str` for `1 ≤ p ≤ n`. -/
def nextZ (s : JStr) (p : Int) : Int :=
  let n : Int := s.bytes.length
  let l := bv s p
  if !(decide (128 ≤ l) && decide (l ≤ 247)) then p + 1
  else if l < 192 then
    if thisZ s p ≥ p then p + 1 else leadZ s (thisZ s p) n (bv s (thisZ s p))
  else leadZ s p n l

/-- Validity at the integer level. -/
abbrev validZ (s : JStr) (p : Int) : Prop := 1 ≤ p ∧ p ≤ s.bytes.length ∧ thisZ s p = p

theorem ite_val {c : Prop} [Decidable c] (a b : JInt64) :
    (if c then a else b).val = if c then a.val else b.val := by
  split <;> rfl

/-! ## Bridges -/

theorem thisind_mid (s : JStr) (i : JInt64) (h1 : 1 ≤ i.val) (h2 : i.val ≤ s.bytes.length) :
    ∃ j, thisind s i = .ok j ∧ j.val = thisZ s i.val := by
  have hs := ncu_small s
  have e1 : (i - ix 1).val = i.val - 1 := sub_val _ _ (by simp; omega) (by simp; omega)
  have e2 : (i - ix 2).val = i.val - 2 := sub_val _ _ (by simp; omega) (by simp; omega)
  have e3 : (i - ix 3).val = i.val - 3 := sub_val _ _ (by simp; omega) (by simp; omega)
  have en : (ncodeunits s + ix 1).val = s.bytes.length + 1 := by
    rw [add_val _ _ (by rw [ncu_val]; simp; omega) (by rw [ncu_val]; simp; omega), ncu_val]; simp
  have hz : ¬ i.val = 0 := by omega
  have hn : ¬ i.val = (ncodeunits s + ix 1).val := by omega
  have hb : betweenI i (ix 1) (ncodeunits s) = true := by
    unfold betweenI; rw [ncu_val, ix1]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  refine ⟨if !(isCont (cu s i) && decide ((i - ix 1).val > 0)) then i else thisindContinued s i,
    ?_, ?_⟩
  · unfold thisind
    simp only [hz, hn, hb, ite_false, Bool.not_true, Bool.false_eq_true]
    split <;> rfl
  · unfold thisindContinued thisZ
    simp only [ite_val, isCont_eq, between_eq, cu_toNat, e1, e2, e3, UInt8.toNat_ofNat]
    rfl

/-! ## Byte-level case analysis -/

/-- Split every `if` and close the arithmetic. -/
macro "bcases" : tactic =>
  `(tactic| ((repeat' split) <;> (try simp [cB] at *) <;> omega))

theorem thisZ_cases (s : JStr) (r : Int) :
    thisZ s r = r ∨
    (thisZ s r = r - 1 ∧ r - 1 > 0 ∧ 128 ≤ bv s r ∧ bv s r < 192 ∧
      192 ≤ bv s (r - 1) ∧ bv s (r - 1) ≤ 247) ∨
    (thisZ s r = r - 2 ∧ r - 2 > 0 ∧ 128 ≤ bv s r ∧ bv s r < 192 ∧
      128 ≤ bv s (r - 1) ∧ bv s (r - 1) < 192 ∧ 224 ≤ bv s (r - 2) ∧ bv s (r - 2) ≤ 247) ∨
    (thisZ s r = r - 3 ∧ r - 3 > 0 ∧ 128 ≤ bv s r ∧ bv s r < 192 ∧
      128 ≤ bv s (r - 1) ∧ bv s (r - 1) < 192 ∧ 128 ≤ bv s (r - 2) ∧ bv s (r - 2) < 192 ∧
      240 ≤ bv s (r - 3) ∧ bv s (r - 3) ≤ 247) := by
  unfold thisZ; bcases

theorem thisZ_le (s : JStr) (r : Int) : thisZ s r ≤ r ∧ r - 3 ≤ thisZ s r := by
  rcases thisZ_cases s r with h | h | h | h <;> omega

theorem thisZ_pos (s : JStr) (r : Int) (h : 1 ≤ r) : 1 ≤ thisZ s r := by
  rcases thisZ_cases s r with h' | h' | h' | h' <;> omega

theorem thisZ_noncont (s : JStr) (r : Int) (h : ¬ (128 ≤ bv s r ∧ bv s r < 192)) :
    thisZ s r = r := by
  rcases thisZ_cases s r with h' | h' | h' | h' <;> omega

theorem thisZ_one (s : JStr) : thisZ s 1 = 1 := by
  rcases thisZ_cases s 1 with h' | h' | h' | h' <;> omega

theorem thisZ_lead1 (s : JStr) (p r : Int) (hr : r = p + 1) (hp : 1 ≤ p)
    (hl : 192 ≤ bv s p ∧ bv s p ≤ 247) (hc : 128 ≤ bv s r ∧ bv s r < 192) : thisZ s r = p := by
  subst hr
  have e1 : p + 1 - 1 = p := by omega
  unfold thisZ; rw [e1]; bcases

theorem thisZ_lead2 (s : JStr) (p r : Int) (hr : r = p + 2) (hp : 1 ≤ p)
    (hl : 224 ≤ bv s p ∧ bv s p ≤ 247) (hc1 : 128 ≤ bv s (p + 1) ∧ bv s (p + 1) < 192)
    (hc : 128 ≤ bv s r ∧ bv s r < 192) : thisZ s r = p := by
  subst hr
  have e1 : p + 2 - 1 = p + 1 := by omega
  have e2 : p + 2 - 2 = p := by omega
  unfold thisZ; rw [e1, e2]; bcases

theorem thisZ_lead3 (s : JStr) (p r : Int) (hr : r = p + 3) (hp : 1 ≤ p)
    (hl : 240 ≤ bv s p ∧ bv s p ≤ 247) (hc1 : 128 ≤ bv s (p + 1) ∧ bv s (p + 1) < 192)
    (hc2 : 128 ≤ bv s (p + 2) ∧ bv s (p + 2) < 192)
    (hc : 128 ≤ bv s r ∧ bv s r < 192) : thisZ s r = p := by
  subst hr
  have e1 : p + 3 - 1 = p + 2 := by omega
  have e2 : p + 3 - 2 = p + 1 := by omega
  have e3 : p + 3 - 3 = p := by omega
  unfold thisZ; rw [e1, e2, e3]; bcases

/-- A valid position that is not a lead byte is followed by a valid position. -/
theorem thisZ_after_single (s : JStr) (p : Int) (hp : 1 ≤ p) (hv : thisZ s p = p)
    (hnl : ¬ (192 ≤ bv s p ∧ bv s p ≤ 247)) : thisZ s (p + 1) = p + 1 := by
  rcases thisZ_cases s (p + 1) with h | h | h | h
  · exact h
  · have e : p + 1 - 1 = p := by omega
    rw [e] at h; omega
  · have e1 : p + 1 - 1 = p := by omega
    have e2 : p + 1 - 2 = p - 1 := by omega
    rw [e1, e2] at h
    have := thisZ_lead1 s (p - 1) p (by omega) (by omega) (by omega) (by omega)
    omega
  · have e1 : p + 1 - 1 = p := by omega
    have e2 : p + 1 - 2 = p - 1 := by omega
    have e3 : p + 1 - 3 = p - 2 := by omega
    rw [e1, e2, e3] at h
    have e4 : p - 2 + 1 = p - 1 := by omega
    have := thisZ_lead2 s (p - 2) p (by omega) (by omega) (by omega) (by rw [e4]; omega) (by omega)
    omega

theorem leadZ_range (s : JStr) (p n : Int) (l : Nat) :
    p + 1 ≤ leadZ s p n l ∧ leadZ s p n l ≤ p + 4 ∧ (p ≤ n → leadZ s p n l ≤ n + 1) := by
  unfold leadZ; bcases

/-- Positions strictly inside a lead byte's sequence belong to it. -/
theorem leadZ_inside (s : JStr) (p r : Int) (hp : 1 ≤ p) (hl : 192 ≤ bv s p ∧ bv s p ≤ 247)
    (h1 : p < r) (h2 : r < leadZ s p s.bytes.length (bv s p)) : thisZ s r = p := by
  have hr : r = p + 1 ∨ r = p + 2 ∨ r = p + 3 := by
    have := leadZ_range s p s.bytes.length (bv s p); omega
  rcases hr with hr | hr | hr
  · apply thisZ_lead1 s p r hr hp hl
    subst hr; unfold leadZ at h2; revert h2; bcases
  · apply thisZ_lead2 s p r hr hp
    all_goals (subst hr; unfold leadZ at h2; revert h2; bcases)
  · apply thisZ_lead3 s p r hr hp
    all_goals (subst hr; unfold leadZ at h2; revert h2; bcases)

theorem bv_out (s : JStr) (p : Int) (h : p > s.bytes.length) : bv s p = 0 := by
  unfold bv
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `thisZ` at `p + k` when the bytes `p+1 .. p+k` are continuation bytes and the
lead byte at `p` is too short to reach `p + k`. -/
theorem thisZ_short (s : JStr) (p : Int) (hl : 192 ≤ bv s p ∧ bv s p ≤ 247) :
    (128 ≤ bv s (p + 1) ∧ bv s (p + 1) < 192 → bv s p < 224 → thisZ s (p + 2) = p + 2) ∧
    (128 ≤ bv s (p + 1) ∧ bv s (p + 1) < 192 → 128 ≤ bv s (p + 2) ∧ bv s (p + 2) < 192 →
      bv s p < 240 → thisZ s (p + 3) = p + 3) ∧
    (128 ≤ bv s (p + 1) ∧ bv s (p + 1) < 192 → 128 ≤ bv s (p + 2) ∧ bv s (p + 2) < 192 →
      128 ≤ bv s (p + 3) ∧ bv s (p + 3) < 192 → thisZ s (p + 4) = p + 4) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 h3 => ?_⟩
  · have e1 : p + 2 - 1 = p + 1 := by omega
    have e2 : p + 2 - 2 = p := by omega
    have e3 : p + 2 - 3 = p - 1 := by omega
    rcases thisZ_cases s (p + 2) with h | h | h | h <;> (try simp only [e1, e2, e3] at h) <;> omega
  · have e1 : p + 3 - 1 = p + 2 := by omega
    have e2 : p + 3 - 2 = p + 1 := by omega
    have e3 : p + 3 - 3 = p := by omega
    rcases thisZ_cases s (p + 3) with h | h | h | h <;> (try simp only [e1, e2, e3] at h) <;> omega
  · have e1 : p + 4 - 1 = p + 3 := by omega
    have e2 : p + 4 - 2 = p + 2 := by omega
    have e3 : p + 4 - 3 = p + 1 := by omega
    rcases thisZ_cases s (p + 4) with h | h | h | h <;> (try simp only [e1, e2, e3] at h) <;> omega

/-- The position after a lead byte's sequence is valid. -/
theorem leadZ_end (s : JStr) (p : Int) (hp : 1 ≤ p) (hl : 192 ≤ bv s p ∧ bv s p ≤ 247) :
    thisZ s (leadZ s p s.bytes.length (bv s p)) = leadZ s p s.bytes.length (bv s p) := by
  have hs := thisZ_short s p hl
  have out : ∀ q : Int, q > (s.bytes.length : Int) → thisZ s q = q := fun q hq =>
    thisZ_noncont s q (by rw [bv_out s q hq]; omega)
  unfold leadZ
  split
  · exact out _ (by omega)
  split
  · exact thisZ_noncont s _ (by simp_all [cB] <;> omega)
  split
  · by_cases hn : p + 2 > (s.bytes.length : Int)
    · exact out _ hn
    · exact hs.1 (by simp_all [cB] <;> omega) (by simp_all <;> omega)
  split
  · exact thisZ_noncont s _ (by simp_all [cB] <;> omega)
  split
  · by_cases hn : p + 3 > (s.bytes.length : Int)
    · exact out _ hn
    · exact hs.2.1 (by simp_all [cB] <;> omega) (by simp_all [cB] <;> omega) (by simp_all <;> omega)
  split
  · exact thisZ_noncont s _ (by simp_all [cB] <;> omega)
  · exact hs.2.2 (by simp_all [cB] <;> omega) (by simp_all [cB] <;> omega) (by simp_all [cB] <;> omega)

/-- An absorbed position lies inside the sequence of the lead byte `thisZ` finds. -/
theorem leadZ_covers (s : JStr) (p : Int) (hp1 : 1 ≤ p) (hpn : p ≤ s.bytes.length)
    (ht : thisZ s p < p) :
    192 ≤ bv s (thisZ s p) ∧ bv s (thisZ s p) ≤ 247 ∧ 1 ≤ thisZ s p ∧
    p < leadZ s (thisZ s p) s.bytes.length (bv s (thisZ s p)) := by
  rcases thisZ_cases s p with h | h | h | h
  · omega
  · rw [h.1]
    refine ⟨by omega, by omega, by omega, ?_⟩
    have e1 : p - 1 + 1 = p := by omega
    unfold leadZ; simp only [e1]; bcases
  · rw [h.1]
    refine ⟨by omega, by omega, by omega, ?_⟩
    have e1 : p - 2 + 1 = p - 1 := by omega
    have e2 : p - 2 + 2 = p := by omega
    unfold leadZ; simp only [e1, e2]; bcases
  · rw [h.1]
    refine ⟨by omega, by omega, by omega, ?_⟩
    have e1 : p - 3 + 1 = p - 2 := by omega
    have e2 : p - 3 + 2 = p - 1 := by omega
    have e3 : p - 3 + 3 = p := by omega
    unfold leadZ; simp only [e1, e2, e3]; bcases

/-- `_nextind_str` returns the next valid position (or `n + 1`). -/
theorem nextZ_spec (s : JStr) (p : Int) (hp1 : 1 ≤ p) (hpn : p ≤ s.bytes.length) :
    p < nextZ s p ∧ nextZ s p ≤ s.bytes.length + 1 ∧
    (∀ r, p < r → r < nextZ s p → thisZ s r < r) ∧
    (nextZ s p ≤ s.bytes.length → thisZ s (nextZ s p) = nextZ s p) := by
  unfold nextZ
  simp only
  split
  · rename_i hl
    refine ⟨by omega, by omega, fun r h1 h2 => by omega, fun _ => ?_⟩
    rcases thisZ_cases s (p + 1) with h | h | h | h
    · exact h
    all_goals (have e : p + 1 - 1 = p := by omega
               rw [e] at h; simp at hl; omega)
  split
  · rename_i hl hc
    split
    · rename_i hv
      have hv' : thisZ s p = p := by have := (thisZ_le s p).1; omega
      refine ⟨by omega, by omega, fun r h1 h2 => by omega, fun _ => ?_⟩
      exact thisZ_after_single s p hp1 hv' (by omega)
    · rename_i hv
      have hc := leadZ_covers s p hp1 hpn (by omega)
      have hr := leadZ_range s (thisZ s p) s.bytes.length (bv s (thisZ s p))
      refine ⟨hc.2.2.2, by have := (thisZ_le s p).1; omega, fun r h1 h2 => ?_, fun _ => ?_⟩
      · have := leadZ_inside s (thisZ s p) r hc.2.2.1 ⟨hc.1, hc.2.1⟩ (by omega) h2
        omega
      · exact leadZ_end s (thisZ s p) hc.2.2.1 ⟨hc.1, hc.2.1⟩
  · rename_i hl hc
    have hl' : 192 ≤ bv s p ∧ bv s p ≤ 247 := by simp at hl; omega
    have hr := leadZ_range s p s.bytes.length (bv s p)
    refine ⟨by omega, by omega, fun r h1 h2 => ?_, fun _ => leadZ_end s p hp1 hl'⟩
    have := leadZ_inside s p r hp1 hl' h1 h2
    omega

/-! ## Bridges from the `JInt` model to the mirrors -/

theorem isvalidAt_eq (s : JStr) (i : JInt64) : isvalidAt s i = decide (validZ s i.val) := by
  unfold isvalidAt validZ
  by_cases h : 1 ≤ i.val ∧ i.val ≤ s.bytes.length
  · obtain ⟨j, hj, hv⟩ := thisind_mid s i h.1 h.2
    rw [hj, ncu_val]
    simp only [hv]
    simp [h]
  · rw [ncu_val]
    simp only [decide_eq_false h, Bool.false_and]
    symm; simp only [decide_eq_false_iff_not]; omega

theorem add1_val (i : JInt64) (h1 : 0 ≤ i.val) (h2 : i.val < 2 ^ 62 + 8) :
    (i + ix 1).val = i.val + 1 := add_val _ _ (by simp; omega) (by simp; omega)

theorem nextindFromLead_val (s : JStr) (i : JInt64) (l : UInt8) (h1 : 1 ≤ i.val)
    (h2 : i.val ≤ s.bytes.length) :
    (nextindFromLead s i (ncodeunits s) l).val = leadZ s i.val s.bytes.length l.toNat := by
  have hs := ncu_small s
  have e1 : (i + ix 1).val = i.val + 1 := add1_val _ (by omega) (by omega)
  have e2 : (i + ix 1 + ix 1).val = i.val + 2 := by
    rw [add1_val _ (by omega) (by omega), e1]; omega
  have e3 : (i + ix 1 + ix 1 + ix 1).val = i.val + 3 := by
    rw [add1_val _ (by omega) (by omega), e2]; omega
  have e4 : (i + ix 1 + ix 1 + ix 1 + ix 1).val = i.val + 4 := by
    rw [add1_val _ (by omega) (by omega), e3]; omega
  unfold nextindFromLead leadZ
  simp only [ite_val, isCont_eq, cu_toNat, e1, e2, e3, e4, ncu_val, u8lt, UInt8.toNat_ofNat]
  try rfl

theorem nextind_mid (s : JStr) (i : JInt64) (h1 : 1 ≤ i.val) (h2 : i.val ≤ s.bytes.length) :
    ∃ j, nextind s i = .ok j ∧ j.val = nextZ s i.val := by
  have hs := ncu_small s
  have hz : ¬ i.val = 0 := by omega
  have hb : betweenI i (ix 1) (ncodeunits s) = true := by
    unfold betweenI; rw [ncu_val, ix1]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  have e1 : (i + ix 1).val = i.val + 1 := add1_val _ (by omega) (by omega)
  unfold nextind nextZ
  simp only [hz, hb, ite_false, Bool.not_true, Bool.false_eq_true, between_eq, cu_toNat,
    UInt8.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  split
  · rename_i hl
    refine ⟨_, rfl, ?_⟩
    rw [e1]
  · rename_i hl
    unfold nextindContinued
    by_cases hc : (cu s i) < 0xc0
    · have hc' : bv s i.val < 192 := by
        rw [UInt8.lt_iff_toNat_lt] at hc; simpa [cu_toNat] using hc
      rw [if_pos hc, if_pos hc']
      obtain ⟨t, ht, htv⟩ := thisind_mid s i h1 h2
      rw [ht]; simp only
      by_cases hge : t.val ≥ i.val
      · have hge' : thisZ s i.val ≥ i.val := by omega
        rw [if_pos hge, if_pos hge']; exact ⟨_, rfl, e1⟩
      · have hge' : ¬ thisZ s i.val ≥ i.val := by omega
        rw [if_neg hge, if_neg hge']
        have hcov := leadZ_covers s i.val h1 h2 (by omega)
        rw [← htv] at hcov
        have ht1 : 1 ≤ t.val := hcov.2.2.1
        have ht2 : t.val ≤ s.bytes.length := by omega
        have hl1 : ¬ ((decide (cu s t < 0x80) || decide (0xf8 ≤ cu s t)) = true) := by
          simp only [Bool.or_eq_true, decide_eq_true_eq, UInt8.lt_iff_toNat_lt,
            UInt8.le_iff_toNat_le, cu_toNat, UInt8.toNat_ofNat]
          omega
        have hl2 : (!decide (cu s t ≥ 0xc0)) = false := by
          simp only [Bool.not_eq_false', decide_eq_true_eq, ge_iff_le, UInt8.le_iff_toNat_le,
            cu_toNat, UInt8.toNat_ofNat]
          omega
        simp only [hl1, hl2, Bool.false_eq_true, ite_false]
        refine ⟨_, rfl, ?_⟩
        rw [nextindFromLead_val s t _ ht1 ht2, cu_toNat, htv]
    · have hc' : ¬ bv s i.val < 192 := by
        rw [UInt8.lt_iff_toNat_lt] at hc; simpa [cu_toNat] using hc
      rw [if_neg hc, if_neg hc']
      refine ⟨_, rfl, ?_⟩
      rw [nextindFromLead_val s i _ h1 h2, cu_toNat]

/-! ## The generic index loops -/

/-- `q` is the first valid position after `i`, or `n + 1` if there is none. -/
def NextValid (s : JStr) (i q : Int) : Prop :=
  i < q ∧ q ≤ s.bytes.length + 1 ∧ (∀ r, i < r → r < q → ¬ validZ s r) ∧
    (q ≤ s.bytes.length → validZ s q)

theorem nextValid_unique (s : JStr) (i q1 q2 : Int) (h1 : NextValid s i q1)
    (h2 : NextValid s i q2) : q1 = q2 := by
  rcases Int.lt_trichotomy q1 q2 with h | h | h
  · exact absurd (h1.2.2.2 (by have := h2.2.1; omega)) (h2.2.2.1 q1 h1.1 h)
  · exact h
  · exact absurd (h2.2.2.2 (by have := h1.2.1; omega)) (h1.2.2.1 q2 h2.1 h)

theorem nextZ_nextValid (s : JStr) (p : Int) (hp1 : 1 ≤ p) (hpn : p ≤ s.bytes.length) :
    NextValid s p (nextZ s p) := by
  obtain ⟨a, b, c, d⟩ := nextZ_spec s p hp1 hpn
  refine ⟨a, b, fun r h1 h2 hv => ?_, fun h => ⟨by omega, h, d h⟩⟩
  have := c r h1 h2; omega

theorem bInt_isvalid_val (s : JStr) (i : JInt64) :
    (bInt (isvalidAt s i)).val = if validZ s i.val then 1 else 0 := by
  rw [bInt_val, isvalidAt_eq]; by_cases h : validZ s i.val <;> simp [h]

theorem nextindNLoop_one (s : JStr) :
    ∀ (k : Nat) (i n : JInt64), n.val = 1 → 0 ≤ i.val → i.val ≤ s.bytes.length →
      (k : Int) = s.bytes.length - i.val →
      NextValid s i.val (nextindNLoop s (ncodeunits s) k i n).val := by
  have hs := ncu_small s
  intro k
  induction k with
  | zero =>
    intro i n hn h0 hi hk
    simp only [nextindNLoop]
    rw [add_val _ _ (by omega) (by omega), hn]
    exact ⟨by omega, by omega, fun r h1 h2 => by omega, fun h => by omega⟩
  | succ k ih =>
    intro i n hn h0 hi hk
    simp only [nextindNLoop, ncu_val]
    have hc : (decide (n.val > 0) && decide (i.val < (s.bytes.length : Int))) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    rw [if_pos hc]
    have e1 : (i + ix 1).val = i.val + 1 := add1_val _ (by omega) (by omega)
    by_cases hv : validZ s (i.val + 1)
    · have en : (n - bInt (isvalidAt s (i + ix 1))).val = 0 := by
        rw [sub_val _ _ (by rw [bInt_isvalid_val]; split <;> omega)
          (by rw [bInt_isvalid_val]; split <;> omega), bInt_isvalid_val, e1, if_pos hv]; omega
      have hres : ∀ k' (j m : JInt64), m.val = 0 → j.val = i.val + 1 →
          (nextindNLoop s (ncodeunits s) k' j m).val = i.val + 1 := by
        intro k' j m hm hj
        cases k' with
        | zero =>
          simp only [nextindNLoop]; rw [add_val _ _ (by omega) (by omega)]; omega
        | succ k' =>
          simp only [nextindNLoop]
          have : ¬ (decide (m.val > 0) && decide (j.val < (ncodeunits s).val)) = true := by
            rw [ncu_val]
            simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
          rw [if_neg this, add_val _ _ (by omega) (by omega)]; omega
      rw [hres k _ _ en e1]
      exact ⟨by omega, by omega, fun r h1 h2 => by omega, fun _ => hv⟩
    · have en : (n - bInt (isvalidAt s (i + ix 1))).val = 1 := by
        rw [sub_val _ _ (by rw [bInt_isvalid_val]; split <;> omega)
          (by rw [bInt_isvalid_val]; split <;> omega), bInt_isvalid_val, e1, if_neg hv]; omega
      have := ih (i + ix 1) _ en (by omega) (by omega) (by omega)
      rw [e1] at this
      obtain ⟨a, b, c, d⟩ := this
      refine ⟨by omega, b, fun r h1 h2 => ?_, d⟩
      by_cases hr : r = i.val + 1
      · rw [hr]; exact hv
      · exact c r (by omega) h2

/-- `q` is the last valid position before `i` (which exists when `i ≥ 2`). -/
def PrevValid (s : JStr) (i q : Int) : Prop :=
  1 ≤ q ∧ q < i ∧ validZ s q ∧ ∀ r, q < r → r < i → ¬ validZ s r

theorem prevValid_unique (s : JStr) (i q1 q2 : Int) (h1 : PrevValid s i q1)
    (h2 : PrevValid s i q2) : q1 = q2 := by
  rcases Int.lt_trichotomy q1 q2 with h | h | h
  · exact absurd h2.2.2.1 (h1.2.2.2 q2 h h2.2.1)
  · exact h
  · exact absurd h1.2.2.1 (h2.2.2.2 q1 h h1.2.1)

theorem valid_one (s : JStr) (h : 1 ≤ s.bytes.length) : validZ s 1 :=
  ⟨Int.le_refl 1, by omega, thisZ_one s⟩

theorem previndNLoop_one (s : JStr) :
    ∀ (k : Nat) (i n : JInt64), n.val = 1 → 2 ≤ i.val → i.val ≤ s.bytes.length + 1 →
      (k : Int) = i.val - 1 →
      PrevValid s i.val (previndNLoop s k i n).val := by
  have hs := ncu_small s
  intro k
  induction k with
  | zero => intro i n _ h2 _ hk; omega
  | succ k ih =>
    intro i n hn h2 hi hk
    simp only [previndNLoop]
    have hc : (decide (n.val > 0) && decide (1 < i.val)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    rw [if_pos hc]
    have e1 : (i - ix 1).val = i.val - 1 := sub_val _ _ (by simp; omega) (by simp; omega)
    by_cases hv : validZ s (i.val - 1)
    · have en : (n - bInt (isvalidAt s (i - ix 1))).val = 0 := by
        rw [sub_val _ _ (by rw [bInt_isvalid_val]; split <;> omega)
          (by rw [bInt_isvalid_val]; split <;> omega), bInt_isvalid_val, e1, if_pos hv]; omega
      have hres : ∀ k' (j m : JInt64), m.val = 0 → j.val = i.val - 1 →
          (previndNLoop s k' j m).val = i.val - 1 := by
        intro k' j m hm hj
        cases k' with
        | zero => simp only [previndNLoop]; rw [sub_val _ _ (by omega) (by omega)]; omega
        | succ k' =>
          simp only [previndNLoop]
          have : ¬ (decide (m.val > 0) && decide (1 < j.val)) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
          rw [if_neg this, sub_val _ _ (by omega) (by omega)]; omega
      rw [hres k _ _ en e1]
      exact ⟨by omega, by omega, hv, fun r h1 h2 => by omega⟩
    · have en : (n - bInt (isvalidAt s (i - ix 1))).val = 1 := by
        rw [sub_val _ _ (by rw [bInt_isvalid_val]; split <;> omega)
          (by rw [bInt_isvalid_val]; split <;> omega), bInt_isvalid_val, e1, if_neg hv]; omega
      have h1v : i.val - 1 ≠ 1 := by
        intro h; exact hv (by rw [h]; exact valid_one s (by omega))
      have := ih (i - ix 1) _ en (by omega) (by omega) (by omega)
      rw [e1] at this
      obtain ⟨a, b, c, d⟩ := this
      refine ⟨a, by omega, c, fun r h1 h2 => ?_⟩
      by_cases hr : r = i.val - 1
      · rw [hr]; exact hv
      · exact d r h1 (by omega)

/-! ## Index function results -/

theorem nextindN_one (s : JStr) (i : JInt64) (h0 : 0 ≤ i.val) (hi : i.val ≤ s.bytes.length) :
    ∃ j, nextindN s i (ix 1) = .ok j ∧ NextValid s i.val j.val := by
  have hb : betweenI i (ix 0) (ncodeunits s) = true := by
    unfold betweenI; rw [ncu_val, ix0]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  unfold nextindN
  simp only [ix1, hb, Bool.not_true, Bool.false_eq_true, ite_false]
  have h1 : ¬ (1 : Int) < 0 := by omega
  have h2 : ¬ (1 : Int) = 0 := by omega
  simp only [h1, h2, ite_false]
  exact ⟨_, rfl, nextindNLoop_one s _ i (ix 1) rfl h0 hi (by rw [ncu_val]; omega)⟩

theorem previndN_one (s : JStr) (i : JInt64) (h1 : 1 ≤ i.val) (hi : i.val ≤ s.bytes.length + 1) :
    ∃ j, previndN s i (ix 1) = .ok j ∧
      ((i.val = 1 ∧ j.val = 0) ∨ (2 ≤ i.val ∧ PrevValid s i.val j.val)) := by
  have hs := ncu_small s
  have ez : (ncodeunits s + ix 1).val = s.bytes.length + 1 := by
    rw [add_val _ _ (by rw [ncu_val]; simp; omega) (by rw [ncu_val]; simp; omega), ncu_val]; simp
  unfold previndN
  have hb : (decide (0 < i.val) && decide (i.val ≤ (ncodeunits s + ix 1).val)) = true := by
    rw [ez]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
  have ha : ¬ (1 : Int) < 0 := by omega
  have hc : ¬ (1 : Int) = 0 := by omega
  simp only [ix1, ha, hc, hb, Bool.not_true, Bool.false_eq_true, ite_false]
  refine ⟨_, rfl, ?_⟩
  by_cases h2 : i.val = 1
  · left
    refine ⟨h2, ?_⟩
    have : (i.val - 1).toNat = 0 := by omega
    rw [this]; simp only [previndNLoop]
    rw [sub_val _ _ (by simp; omega) (by simp; omega)]; simp; omega
  · right
    exact ⟨by omega, previndNLoop_one s _ i (ix 1) rfl (by omega) hi (by omega)⟩

theorem thisZ_idem (s : JStr) (p : Int) : thisZ s (thisZ s p) = thisZ s p := by
  rcases thisZ_cases s p with h | h | h | h
  · rw [h, h]
  all_goals (rw [h.1]; exact thisZ_noncont s _ (by omega))

theorem isvalidAt_iff (s : JStr) (i : JInt64) : isvalidAt s i = true ↔ validZ s i.val := by
  rw [isvalidAt_eq]; simp

theorem shl24_toNat (b : UInt8) : (b.toUInt32 <<< 24).toNat = b.toNat * 2 ^ 24 := by
  have := UInt8.toNat_lt b
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  have e : (24 : UInt32).toNat % 32 = 24 := rfl
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

theorem shl16_toNat (b : UInt8) : (b.toUInt32 <<< 16).toNat = b.toNat * 2 ^ 16 := by
  have := UInt8.toNat_lt b
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  have e : (16 : UInt32).toNat % 32 = 16 := rfl
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

theorem shl8_toNat (b : UInt8) : (b.toUInt32 <<< 8).toNat = b.toNat * 2 ^ 8 := by
  have := UInt8.toNat_lt b
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  have e : (8 : UInt32).toNat % 32 = 8 := rfl
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

/-- The top byte of a Char bit pattern under construction is `l`. -/
def TopByte (u : UInt32) (l : Nat) : Prop := ∃ r, r < 2 ^ 24 ∧ u.toNat = l * 2 ^ 24 + r

theorem topByte_init (b : UInt8) : TopByte (b.toUInt32 <<< 24) b.toNat :=
  ⟨0, by decide, by rw [shl24_toNat]; omega⟩

theorem topByte_or (u y : UInt32) (l : Nat) (h : TopByte u l) (hy : y.toNat < 2 ^ 24) :
    TopByte (u ||| y) l := by
  obtain ⟨r, hr, hu⟩ := h
  refine ⟨r ||| y.toNat, Nat.or_lt_two_pow hr hy, ?_⟩
  rw [UInt32.toNat_or, hu]
  have a1 : l * 2 ^ 24 + r = (l <<< 24) ||| r := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hr, Nat.shiftLeft_eq]
  rw [a1, Nat.or_assoc, ← Nat.shiftLeft_add_eq_or_of_lt (Nat.or_lt_two_pow hr hy), Nat.shiftLeft_eq]

theorem topByte_c0 {u : UInt32} {l : Nat} (h : TopByte u l) :
    decide (u < 0xc0000000) = decide (l < 192) := by
  obtain ⟨r, hr, hu⟩ := h
  have e : (0xc0000000 : UInt32).toNat = 192 * 2 ^ 24 := rfl
  simp only [decide_eq_decide, UInt32.lt_iff_toNat_lt, hu, e]; omega

theorem topByte_e0 {u : UInt32} {l : Nat} (h : TopByte u l) :
    decide (u < 0xe0000000) = decide (l < 224) := by
  obtain ⟨r, hr, hu⟩ := h
  have e : (0xe0000000 : UInt32).toNat = 224 * 2 ^ 24 := rfl
  simp only [decide_eq_decide, UInt32.lt_iff_toNat_lt, hu, e]; omega

theorem topByte_f0 {u : UInt32} {l : Nat} (h : TopByte u l) :
    decide (u < 0xf0000000) = decide (l < 240) := by
  obtain ⟨r, hr, hu⟩ := h
  have e : (0xf0000000 : UInt32).toNat = 240 * 2 ^ 24 := rfl
  simp only [decide_eq_decide, UInt32.lt_iff_toNat_lt, hu, e]; omega

theorem ite_snd {α β : Type} {c : Prop} [Decidable c] (x y : α × β) :
    (if c then x else y).2 = if c then x.2 else y.2 := by
  split <;> rfl

theorem iterateContinued_snd (s : JStr) (i : JInt64) (h1 : 1 ≤ i.val)
    (h2 : i.val ≤ s.bytes.length) (hl : 192 ≤ bv s i.val) :
    (iterateContinued s i ((cu s i).toUInt32 <<< 24)).2.val =
      leadZ s i.val s.bytes.length (bv s i.val) := by
  have hs := ncu_small s
  have e1 : (i + ix 1).val = i.val + 1 := add1_val _ (by omega) (by omega)
  have e2 : (i + ix 1 + ix 1).val = i.val + 2 := by
    rw [add1_val _ (by omega) (by omega), e1]; omega
  have e3 : (i + ix 1 + ix 1 + ix 1).val = i.val + 3 := by
    rw [add1_val _ (by omega) (by omega), e2]; omega
  have e4 : (i + ix 1 + ix 1 + ix 1 + ix 1).val = i.val + 4 := by
    rw [add1_val _ (by omega) (by omega), e3]; omega
  have t0 := topByte_init (cu s i)
  have t1 := topByte_or _ ((cu s (i + ix 1)).toUInt32 <<< 16) _ t0
    (by rw [shl16_toNat]; have := UInt8.toNat_lt (cu s (i + ix 1)); omega)
  have t2 := topByte_or _ ((cu s (i + ix 1 + ix 1)).toUInt32 <<< 8) _ t1
    (by rw [shl8_toNat]; have := UInt8.toNat_lt (cu s (i + ix 1 + ix 1)); omega)
  have c0 : (cu s i).toUInt32 <<< 24 < 0xc0000000 ↔ False := by
    have := topByte_c0 t0; rw [cu_toNat] at this
    constructor
    · intro h; have h' : decide ((cu s i).toUInt32 <<< 24 < 0xc0000000) = true := by simpa using h
      rw [this] at h'; simp at h'; omega
    · intro h; exact h.elim
  unfold iterateContinued
  simp only [c0, ite_false]
  simp only [ite_snd, ite_val, topByte_e0 t1, topByte_f0 t2, isCont_eq, cu_toNat, e1, e2, e3, e4,
    ncu_val]
  unfold leadZ
  rfl

theorem u64_val (i : JInt64) (h1 : 0 ≤ i.val) : (JInt.rem .u64 i).val = i.val := by
  show wrapInt .u64 i.val = i.val
  have := i.property.2
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, IntTy.max] at this ⊢
  constructor <;> simp at * <;> omega

theorem iterate_cond (s : JStr) (i : JInt64) (h1 : 1 ≤ i.val) (h2 : i.val ≤ s.bytes.length + 1) :
    (JInt.rem .u64 i - JInt.lit .u64 1).val = i.val - 1 := by
  have hs := ncu_small s
  show wrapInt .u64 ((JInt.rem .u64 i).val - (JInt.lit .u64 1).val) = i.val - 1
  rw [u64_val i (by omega)]
  have : (JInt.lit .u64 1).val = 1 := rfl
  rw [this]
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  constructor <;> simp <;> omega

theorem iterate_eq (s : JStr) (i : JInt64) (h1 : 1 ≤ i.val) (h2 : i.val ≤ s.bytes.length) :
    iterate s i = if !between (cu s i) 0x80 0xf7 then some ((cu s i).toUInt32 <<< 24, i + ix 1)
      else some (iterateContinued s i ((cu s i).toUInt32 <<< 24)) := by
  have hc : (!decide ((JInt.rem .u64 i - JInt.lit .u64 1).val < (ncodeunits s).val)) = false := by
    rw [iterate_cond s i h1 (by omega), ncu_val]; simp; omega
  unfold iterate
  rw [hc]
  rfl

theorem iterate_valid (s : JStr) (i : JInt64) (hv : validZ s i.val) :
    ∃ c j, iterate s i = some (c, j) ∧ j.val = nextZ s i.val := by
  obtain ⟨h1, h2, h3⟩ := hv
  have hs := ncu_small s
  have e1 : (i + ix 1).val = i.val + 1 := add1_val _ (by omega) (by omega)
  rw [iterate_eq s i h1 h2]
  have hbe : between (cu s i) 0x80 0xf7 = (decide (128 ≤ bv s i.val) && decide (bv s i.val ≤ 247)) := by
    rw [between_eq, cu_toNat]; rfl
  unfold nextZ
  simp only
  rw [hbe]
  by_cases hb : (!(decide (128 ≤ bv s i.val) && decide (bv s i.val ≤ 247))) = true
  · rw [if_pos hb, if_pos hb]
    exact ⟨_, _, rfl, e1⟩
  · rw [if_neg hb, if_neg hb]
    rcases hic : iterateContinued s i ((cu s i).toUInt32 <<< 24) with ⟨c, j⟩
    refine ⟨c, j, rfl, ?_⟩
    by_cases hcont : bv s i.val < 192
    · rw [if_pos hcont, if_pos (by omega)]
      have hlt : (cu s i).toUInt32 <<< 24 < 0xc0000000 := by
        have := topByte_c0 (topByte_init (cu s i)); rw [cu_toNat] at this
        have h' : decide (bv s i.val < 192) = true := by simpa using hcont
        rw [← this] at h'; simpa using h'
      have : (iterateContinued s i ((cu s i).toUInt32 <<< 24)).2 = i + ix 1 := by
        unfold iterateContinued; rw [if_pos hlt]
      rw [hic] at this
      simp only at this
      rw [this, e1]
    · rw [if_neg hcont]
      have := iterateContinued_snd s i h1 h2 (by omega)
      rw [hic] at this
      exact this

theorem iterate_end (s : JStr) (i : JInt64) (h : i.val = s.bytes.length + 1) :
    iterate s i = none := by
  unfold iterate
  have hc : (!decide ((JInt.rem .u64 i - JInt.lit .u64 1).val < (ncodeunits s).val)) = true := by
    rw [iterate_cond s i (by omega) (by omega), ncu_val]; simp; omega
  simp only [hc, ite_true]

theorem validFrom_drop (s : JStr) :
    ∀ (d k : Nat) (a : JInt64), 1 ≤ a.val → (k : Int) = s.bytes.length + 1 - a.val → d ≤ k →
      (∀ r, a.val ≤ r → r < a.val + d → ¬ validZ s r) →
      ∃ b : JInt64, b.val = a.val + d ∧ validFrom s k a = validFrom s (k - d) b := by
  have hs := ncu_small s
  intro d
  induction d with
  | zero => intro k a _ _ _ _; exact ⟨a, by simp, by simp⟩
  | succ d ih =>
    intro k a h1 hk hd hgap
    obtain ⟨b, hb, he⟩ := ih k a h1 hk (by omega) (fun r h1 h2 => hgap r h1 (by omega))
    have hkd : k - d = (k - (d + 1)) + 1 := by omega
    have hbv : ¬ validZ s b.val := hgap b.val (by omega) (by omega)
    refine ⟨b + ix 1, by rw [add1_val _ (by omega) (by omega)]; omega, ?_⟩
    rw [he, hkd]
    simp only [validFrom]
    rw [isvalidAt_eq]; simp [hbv]

/-- Iterating from a valid position visits exactly the valid positions from there on. -/
theorem trace_from (s : JStr) :
    ∀ (k : Nat) (i : JInt64), 1 ≤ i.val → i.val ≤ s.bytes.length + 1 →
      (k : Int) = s.bytes.length + 1 - i.val → (i.val ≤ s.bytes.length → validZ s i.val) →
      ∃ xs, IterTrace s i xs ∧ xs.map (fun x => x.2.val) = validFrom s k i := by
  have hs := ncu_small s
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i h1 h2 hk hv
    by_cases hend : i.val = s.bytes.length + 1
    · have : k = 0 := by omega
      subst this
      exact ⟨[], .done (iterate_end s i hend), rfl⟩
    · have hv' := hv (by omega)
      obtain ⟨c, j, hit, hj⟩ := iterate_valid s i hv'
      obtain ⟨q1, q2, q3, q4⟩ := nextZ_nextValid s i.val h1 (by omega)
      rw [← hj] at q1 q2 q3 q4
      have hk' : ((s.bytes.length + 1 - j.val).toNat : Int) = s.bytes.length + 1 - j.val := by
        omega
      obtain ⟨xs, htr, hmap⟩ := ih (s.bytes.length + 1 - j.val).toNat (by omega) j (by omega)
        q2 hk' q4
      refine ⟨(c, i) :: xs, .step hit htr, ?_⟩
      have hk1 : k = (k - 1) + 1 := by omega
      rw [hk1]
      simp only [validFrom]
      rw [isvalidAt_eq, decide_eq_true hv']
      simp only [ite_true, List.map_cons, List.cons.injEq, true_and]
      obtain ⟨b, hb, he⟩ := validFrom_drop s (j.val - (i.val + 1)).toNat (k - 1) (i + ix 1)
        (by rw [add1_val _ (by omega) (by omega)]; omega)
        (by rw [add1_val _ (by omega) (by omega)]; omega) (by omega)
        (fun r r1 r2 => by
          rw [add1_val _ (by omega) (by omega)] at r1 r2
          exact q3 r (by omega) (by omega))
      rw [add1_val _ (by omega) (by omega)] at hb
      have hbj : b = j := Subtype.ext (by omega)
      have hkk : k - 1 - (j.val - (i.val + 1)).toNat = (s.bytes.length + 1 - j.val).toNat := by
        omega
      rw [he, hbj, hmap, hkk]

end JuliaLean.Strings
