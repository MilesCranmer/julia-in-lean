import JuliaLean.BitArrays.Basic

/-!
# Proof of `FindAgrees`

Each search reads one masked chunk, then scans whole chunks, then (for
`findnext(!, B, i)`) the last, partial chunk. `trailing_zeros` / `top_set_bit`
give the lowest / highest set bit of a chunk, and a `find?` over `List.range` is
characterised by `find_some` / `find_rev_some`; the result is matched with the
generic search through `eq_some_fwd` / `eq_some_bwd`.
-/

namespace JuliaLean.BitArrays

namespace FindProof

/-! ## `find?` over `List.range` -/

theorem find_none (f : Nat → Bool) (n : Nat) :
    (List.range n).find? f = none ↔ ∀ q, q < n → f q = false := by
  rw [List.find?_eq_none]
  constructor
  · intro h q hq
    have := h q (List.mem_range.mpr hq)
    simpa using this
  · intro h q hq
    rw [h q (List.mem_range.mp hq)]
    decide

theorem find_rev_none (f : Nat → Bool) (n : Nat) :
    (List.range n).reverse.find? f = none ↔ ∀ q, q < n → f q = false := by
  rw [List.find?_eq_none]
  constructor
  · intro h q hq
    have := h q (List.mem_reverse.mpr (List.mem_range.mpr hq))
    simpa using this
  · intro h q hq
    rw [h q (List.mem_range.mp (List.mem_reverse.mp hq))]
    decide

theorem find_some (f : Nat → Bool) : ∀ (n p : Nat),
    (List.range n).find? f = some p ↔ (p < n ∧ f p = true ∧ ∀ q, q < p → f q = false)
  | 0, p => by simp
  | n + 1, p => by
    rw [List.range_succ, List.find?_append]
    cases h : (List.range n).find? f with
    | some p' =>
      obtain ⟨h1, h2, h3⟩ := (find_some f n p').mp h
      simp only [Option.or]
      constructor
      · intro e
        cases e
        exact ⟨by omega, h2, h3⟩
      · rintro ⟨_, hp, hmin⟩
        have : p = p' := by
          rcases Nat.lt_trichotomy p p' with hlt | heq | hgt
          · rw [h3 p hlt] at hp
            cases hp
          · exact heq
          · rw [hmin p' hgt] at h2
            cases h2
        rw [this]
    | none =>
      have hn := (find_none f n).mp h
      simp only [Option.or]
      cases hf : f n
      · simp only [List.find?_cons, hf, List.find?_nil, Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro e
          cases e
        · rintro ⟨hp1, hp2, _⟩
          by_cases hpn : p < n
          · rw [hn p hpn] at hp2
            cases hp2
          · have : p = n := by omega
            subst this
            rw [hf] at hp2
            cases hp2
      · simp only [List.find?_cons, hf, Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro e
          cases e
          exact ⟨by omega, hf, fun q hq => hn q hq⟩
        · rintro ⟨hp1, hp2, _⟩
          have : ¬ p < n := fun hlt => by rw [hn p hlt] at hp2; cases hp2
          have : p = n := by omega
          rw [this]

theorem find_rev_some (f : Nat → Bool) : ∀ (n p : Nat),
    (List.range n).reverse.find? f = some p ↔
      (p < n ∧ f p = true ∧ ∀ q, p < q → q < n → f q = false)
  | 0, p => by simp
  | n + 1, p => by
    have e : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by
      simp [List.range_succ]
    rw [e]
    cases hf : f n
    · simp only [List.find?_cons, hf, Bool.false_eq_true, ↓reduceIte]
      rw [find_rev_some f n p]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨by omega, h2, fun q hq1 hq2 => ?_⟩
        by_cases hqn : q < n
        · exact h3 q hq1 hqn
        · have : q = n := by omega
          rw [this]
          exact hf
      · rintro ⟨h1, h2, h3⟩
        have : p ≠ n := fun e => by rw [e, hf] at h2; cases h2
        exact ⟨by omega, h2, fun q hq1 hq2 => h3 q hq1 (by omega)⟩
    · simp only [List.find?_cons, hf, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro e
        cases e
        exact ⟨by omega, hf, fun q hq1 hq2 => by omega⟩
      · rintro ⟨h1, h2, h3⟩
        have : ¬ p < n := fun hlt => by rw [h3 n hlt (by omega)] at hf; cases hf
        have : p = n := by omega
        rw [this]

theorem eq_some_fwd (f : Nat → Bool) (n y : Nat) (hy : y < n) (hf : f y = true)
    (hmin : ∀ q, q < y → f q = false) :
    some (y + 1) = ((List.range n).find? f).map (· + 1) := by
  rw [(find_some f n y).mpr ⟨hy, hf, hmin⟩]
  rfl

theorem eq_none_fwd (f : Nat → Bool) (n : Nat) (h : ∀ q, q < n → f q = false) :
    none = ((List.range n).find? f).map (· + 1) := by
  rw [(find_none f n).mpr h]
  rfl

theorem eq_some_bwd (f : Nat → Bool) (n x : Nat) (hx : 1 ≤ x) (hy : x - 1 < n)
    (hf : f (x - 1) = true) (hmax : ∀ q, x - 1 < q → q < n → f q = false) :
    some x = ((List.range n).reverse.find? f).map (· + 1) := by
  rw [(find_rev_some f n (x - 1)).mpr ⟨hy, hf, hmax⟩]
  show some x = some (x - 1 + 1)
  congr 1
  omega

theorem eq_none_bwd (f : Nat → Bool) (n : Nat) (h : ∀ q, q < n → f q = false) :
    none = ((List.range n).reverse.find? f).map (· + 1) := by
  rw [(find_rev_none f n).mpr h]
  rfl

/-! ## Chunk bit counts -/

theorem tz_spec (x : U64) (hx : x ≠ 0) :
    trailingZeros x < 64 ∧ x.getLsbD (trailingZeros x) = true ∧
      ∀ j, j < trailingZeros x → x.getLsbD j = false := by
  unfold trailingZeros
  cases h : (List.range 64).find? (fun j => x.getLsbD j) with
  | none =>
    exfalso
    apply hx
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [show x.getLsbD j = false from (find_none _ 64).mp h j hj, getLsbD_zero64]
  | some p =>
    obtain ⟨h1, h2, h3⟩ := (find_some _ 64 p).mp h
    exact ⟨h1, h2, h3⟩

theorem top_spec (x : U64) (hx : x ≠ 0) :
    1 ≤ topSetBit x ∧ topSetBit x ≤ 64 ∧ x.getLsbD (topSetBit x - 1) = true ∧
      ∀ j, topSetBit x ≤ j → j < 64 → x.getLsbD j = false := by
  unfold topSetBit
  cases h : (List.range 64).reverse.find? (fun j => x.getLsbD j) with
  | none =>
    exfalso
    apply hx
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [show x.getLsbD j = false from (find_rev_none _ 64).mp h j hj, getLsbD_zero64]
  | some p =>
    obtain ⟨h1, h2, h3⟩ := (find_rev_some _ 64 p).mp h
    show 1 ≤ p + 1 ∧ p + 1 ≤ 64 ∧ x.getLsbD (p + 1 - 1) = true ∧
      ∀ j, p + 1 ≤ j → j < 64 → x.getLsbD j = false
    refine ⟨by omega, by omega, by rw [Nat.add_sub_cancel]; exact h2, fun j hj1 hj2 => h3 j (by omega) hj2⟩

/-! ## Bits -/

theorem cbit (l : List Bool) (c j : Nat) (hj : j < 64) :
    (cget (pack l) c).getLsbD j = l.getD (64 * (c - 1) + j) false := by
  rw [getLsbD_cget_lt _ _ hj, bitOf_pack]

theorem bit_q (l : List Bool) (c q : Nat) (hc : c = q / 64 + 1) :
    (cget (pack l) c).getLsbD (q % 64) = l.getD q false := by
  rw [cbit l c _ (Nat.mod_lt _ (by decide))]
  congr 1
  omega

theorem nbit (x : U64) (j : Nat) (hj : j < 64) : (~~~x).getLsbD j = !x.getLsbD j := by
  rw [getLsbD_not64, if_pos hj]

theorem getD_dflt (l : List Bool) (q : Nat) (d : Bool) (h : q < l.length) :
    l.getD q d = l.getD q false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem lt_of_getD (l : List Bool) (q : Nat) (h : l.getD q false = true) : q < l.length := by
  apply Nat.lt_of_not_le
  intro hle
  rw [getD_ge hle] at h
  cases h

theorem eq_of_bne_false {x y : U64} (h : (x != y) = false) : x = y := by
  cases hxy : x == y
  · simp [bne, hxy] at h
  · exact beq_iff_eq.mp hxy

theorem ne_of_bne_true {x y : U64} (h : (x != y) = true) : x ≠ y := by
  intro e
  subst e
  simp at h

theorem bne_true_of_ne {x y : U64} (h : x ≠ y) : (x != y) = true := by
  cases hxy : x == y
  · simp [bne, hxy]
  · exact absurd (beq_iff_eq.mp hxy) h

theorem not_ne_zero (x : U64) (h : x ≠ msk64) : ~~~x ≠ 0 := by
  intro hz
  apply h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := congrArg (fun z : U64 => z.getLsbD j) hz
  simp only [nbit x j hj, getLsbD_zero64] at this
  rw [getLsbD_msk64, if_pos hj]
  simpa using this

theorem msk64_bit (j : Nat) (hj : j < 64) : msk64.getLsbD j = true := by
  rw [getLsbD_msk64, if_pos hj]

/-! ## `findnext(B, i)` -/

theorem next_unsafe (l : List Bool) (st : Nat) (h1 : 1 ≤ st) (h2 : st ≤ l.length) :
    unsafeBitfindnext (pack l) st =
      ((List.range l.length).find? (fun p => decide (st ≤ p + 1) && l.getD p false)).map (· + 1) := by
  have hnc := pack_length l
  rw [numBitChunks_eq] at hnc
  simp only [unsafeBitfindnext]
  generalize hcs : div64 (st - 1) + 1 = cs
  generalize hw : mod64 (st - 1) = w
  have hcs' : cs = (st - 1) / 64 + 1 := by rw [← hcs]; rfl
  have hw' : w = (st - 1) % 64 := by rw [← hw]; rfl
  have hX : ∀ j, j < 64 → (cget (pack l) cs &&& msk64 <<< w).getLsbD j =
      (decide (w ≤ j) && l.getD (64 * (cs - 1) + j) false) := by
    intro j hj
    rw [BitVec.getLsbD_and, cbit l cs j hj, getLsbD_shl]
    by_cases hwj : w ≤ j
    · rw [if_pos ⟨hj, hwj⟩, msk64_bit _ (by omega), decide_eq_true hwj]
      simp
    · rw [if_neg (fun h => hwj h.2), decide_eq_false hwj]
      simp
  by_cases hX0 : (cget (pack l) cs &&& msk64 <<< w) = 0
  · rw [if_neg (by rw [hX0]; simp)]
    have hz : ∀ q, st ≤ q + 1 → q / 64 + 1 = cs → l.getD q false = false := by
      intro q hq hqc
      have := hX (q % 64) (Nat.mod_lt _ (by decide))
      rw [hX0, getLsbD_zero64, show 64 * (cs - 1) + q % 64 = q by omega,
        decide_eq_true (show w ≤ q % 64 by omega), Bool.true_and] at this
      exact this.symm
    cases hg : (List.range ((pack l).length - cs)).find? (fun j => cget (pack l) (cs + 1 + j) != 0) with
    | none =>
      have hg' := (find_none _ _).mp hg
      apply eq_none_fwd
      intro q hq
      show (decide (st ≤ q + 1) && l.getD q false) = false
      by_cases hq1 : st ≤ q + 1
      · have hlq : l.getD q false = false := by
          by_cases hqc : q / 64 + 1 = cs
          · exact hz q hq1 hqc
          · have hc0 := eq_of_bne_false (hg' (q / 64 - cs) (by omega))
            have := bit_q l (cs + 1 + (q / 64 - cs)) q (by omega)
            rw [hc0, getLsbD_zero64] at this
            exact this.symm
        rw [hlq, Bool.and_false]
      · rw [decide_eq_false hq1]
        rfl
    | some j =>
      obtain ⟨g1, g2, g3⟩ := (find_some _ _ j).mp hg
      obtain ⟨t1, t2, t3⟩ := tz_spec _ (ne_of_bne_true g2)
      show some ((cs + j) * 64 + trailingZeros (cget (pack l) (cs + 1 + j)) + 1) = _
      generalize ht : trailingZeros (cget (pack l) (cs + 1 + j)) = t at t1 t2 t3 ⊢
      have hlt : l.getD ((cs + j) * 64 + t) false = true := by
        rw [← bit_q l (cs + 1 + j) _ (by omega), show ((cs + j) * 64 + t) % 64 = t by omega]
        exact t2
      apply eq_some_fwd _ _ _ (lt_of_getD _ _ hlt)
      · show (decide (st ≤ (cs + j) * 64 + t + 1) && l.getD ((cs + j) * 64 + t) false) = true
        rw [hlt, decide_eq_true (show st ≤ (cs + j) * 64 + t + 1 by omega)]
        rfl
      · intro q hq
        show (decide (st ≤ q + 1) && l.getD q false) = false
        by_cases hq1 : st ≤ q + 1
        · have hlq : l.getD q false = false := by
            by_cases hqc : q / 64 + 1 = cs
            · exact hz q hq1 hqc
            · by_cases hqj : q / 64 < cs + j
              · have hc0 := eq_of_bne_false (g3 (q / 64 - cs) (by omega))
                have := bit_q l (cs + 1 + (q / 64 - cs)) q (by omega)
                rw [hc0, getLsbD_zero64] at this
                exact this.symm
              · have := bit_q l (cs + 1 + j) q (by omega)
                rw [t3 (q % 64) (by omega)] at this
                exact this.symm
          rw [hlq, Bool.and_false]
        · rw [decide_eq_false hq1]
          rfl
  · rw [if_pos (bne_true_of_ne hX0)]
    obtain ⟨t1, t2, t3⟩ := tz_spec _ hX0
    generalize ht : trailingZeros (cget (pack l) cs &&& msk64 <<< w) = t at t1 t2 t3 ⊢
    have hb2 : (decide (w ≤ t) && l.getD (64 * (cs - 1) + t) false) = true := by
      rw [← hX t t1]
      exact t2
    rw [Bool.and_eq_true, decide_eq_true_iff] at hb2
    obtain ⟨hwt, hlt⟩ := hb2
    rw [show 64 * (cs - 1) + t = (cs - 1) * 64 + t by omega] at hlt
    apply eq_some_fwd _ _ _ (lt_of_getD _ _ hlt)
    · show (decide (st ≤ (cs - 1) * 64 + t + 1) && l.getD ((cs - 1) * 64 + t) false) = true
      rw [hlt, decide_eq_true (show st ≤ (cs - 1) * 64 + t + 1 by omega)]
      rfl
    · intro q hq
      show (decide (st ≤ q + 1) && l.getD q false) = false
      by_cases hq1 : st ≤ q + 1
      · have := hX (q % 64) (Nat.mod_lt _ (by decide))
        rw [t3 (q % 64) (by omega), show 64 * (cs - 1) + q % 64 = q by omega,
          decide_eq_true (show w ≤ q % 64 by omega), Bool.true_and] at this
        rw [← this, Bool.and_false]
      · rw [decide_eq_false hq1]
        rfl

/-! ## `findprev(B, i)` -/

theorem prev_unsafe (l : List Bool) (st : Nat) (h1 : 1 ≤ st) (h2 : st ≤ l.length) :
    unsafeBitfindprev (pack l) st =
      ((List.range l.length).reverse.find? (fun p => decide (p + 1 ≤ st) && l.getD p false)).map (· + 1) := by
  have hnc := pack_length l
  rw [numBitChunks_eq] at hnc
  simp only [unsafeBitfindprev]
  generalize hcs : div64 (st - 1) + 1 = cs
  have hcs' : cs = (st - 1) / 64 + 1 := by rw [← hcs]; rfl
  have hX : ∀ j, j < 64 → (cget (pack l) cs &&& mskEnd st).getLsbD j =
      (decide (64 * (cs - 1) + j + 1 ≤ st) && l.getD (64 * (cs - 1) + j) false) := by
    intro j hj
    rw [BitVec.getLsbD_and, cbit l cs j hj, getLsbD_mskEnd, Bool.and_comm]
    congr 1
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  by_cases hX0 : (cget (pack l) cs &&& mskEnd st) = 0
  · rw [if_neg (by rw [hX0]; simp)]
    have hz : ∀ q, q + 1 ≤ st → q / 64 + 1 = cs → l.getD q false = false := by
      intro q hq hqc
      have := hX (q % 64) (Nat.mod_lt _ (by decide))
      rw [hX0, getLsbD_zero64, show 64 * (cs - 1) + q % 64 = q by omega,
        decide_eq_true (show q + 1 ≤ st by omega), Bool.true_and] at this
      exact this.symm
    cases hg : (List.range (cs - 1)).find? (fun j => cget (pack l) (cs - 1 - j) != 0) with
    | none =>
      have hg' := (find_none _ _).mp hg
      apply eq_none_bwd
      intro q hq
      show (decide (q + 1 ≤ st) && l.getD q false) = false
      by_cases hq1 : q + 1 ≤ st
      · have hlq : l.getD q false = false := by
          by_cases hqc : q / 64 + 1 = cs
          · exact hz q hq1 hqc
          · have hc0 := eq_of_bne_false (hg' (cs - 2 - q / 64) (by omega))
            have := bit_q l (cs - 1 - (cs - 2 - q / 64)) q (by omega)
            rw [hc0, getLsbD_zero64] at this
            exact this.symm
        rw [hlq, Bool.and_false]
      · rw [decide_eq_false hq1]
        rfl
    | some j =>
      obtain ⟨g1, g2, g3⟩ := (find_some _ _ j).mp hg
      obtain ⟨t1, t2, t3, t4⟩ := top_spec _ (ne_of_bne_true g2)
      show some ((cs - 2 - j) * 64 + topSetBit (cget (pack l) (cs - 1 - j))) = _
      generalize ht : topSetBit (cget (pack l) (cs - 1 - j)) = t at t1 t2 t3 t4 ⊢
      have hlt : l.getD ((cs - 2 - j) * 64 + t - 1) false = true := by
        rw [← bit_q l (cs - 1 - j) _ (by omega), show ((cs - 2 - j) * 64 + t - 1) % 64 = t - 1 by omega]
        exact t3
      apply eq_some_bwd _ _ _ (by omega) (lt_of_getD _ _ hlt)
      · show (decide ((cs - 2 - j) * 64 + t - 1 + 1 ≤ st) && l.getD ((cs - 2 - j) * 64 + t - 1) false) = true
        rw [hlt, decide_eq_true (show (cs - 2 - j) * 64 + t - 1 + 1 ≤ st by omega)]
        rfl
      · intro q hq hqn
        show (decide (q + 1 ≤ st) && l.getD q false) = false
        by_cases hq1 : q + 1 ≤ st
        · have hlq : l.getD q false = false := by
            by_cases hqc : q / 64 + 1 = cs
            · exact hz q hq1 hqc
            · by_cases hqj : cs - 2 - j < q / 64
              · have hc0 := eq_of_bne_false (g3 (cs - 2 - q / 64) (by omega))
                have := bit_q l (cs - 1 - (cs - 2 - q / 64)) q (by omega)
                rw [hc0, getLsbD_zero64] at this
                exact this.symm
              · have := bit_q l (cs - 1 - j) q (by omega)
                rw [t4 (q % 64) (by omega) (Nat.mod_lt _ (by decide))] at this
                exact this.symm
          rw [hlq, Bool.and_false]
        · rw [decide_eq_false hq1]
          rfl
  · rw [if_pos (bne_true_of_ne hX0)]
    obtain ⟨t1, t2, t3, t4⟩ := top_spec _ hX0
    generalize ht : topSetBit (cget (pack l) cs &&& mskEnd st) = t at t1 t2 t3 t4 ⊢
    have hb2 : (decide (64 * (cs - 1) + (t - 1) + 1 ≤ st) &&
        l.getD (64 * (cs - 1) + (t - 1)) false) = true := by
      rw [← hX (t - 1) (by omega)]
      exact t3
    rw [Bool.and_eq_true, decide_eq_true_iff] at hb2
    obtain ⟨hwt, hlt⟩ := hb2
    rw [show 64 * (cs - 1) + (t - 1) = (cs - 1) * 64 + t - 1 by omega] at hlt
    apply eq_some_bwd _ _ _ (by omega) (lt_of_getD _ _ hlt)
    · show (decide ((cs - 1) * 64 + t - 1 + 1 ≤ st) && l.getD ((cs - 1) * 64 + t - 1) false) = true
      rw [hlt, decide_eq_true (show (cs - 1) * 64 + t - 1 + 1 ≤ st by omega)]
      rfl
    · intro q hq hqn
      show (decide (q + 1 ≤ st) && l.getD q false) = false
      by_cases hq1 : q + 1 ≤ st
      · have := hX (q % 64) (Nat.mod_lt _ (by decide))
        rw [t4 (q % 64) (by omega) (Nat.mod_lt _ (by decide)), show 64 * (cs - 1) + q % 64 = q by omega,
          decide_eq_true (show q + 1 ≤ st by omega), Bool.true_and] at this
        rw [← this, Bool.and_false]
      · rw [decide_eq_false hq1]
        rfl

/-! ## `findnext(!, B, i)` -/

theorem nextnot_eq (l : List Bool) (i : JInt64) (h1 : 1 ≤ i.val) (h2 : i.val ≤ l.length) :
    findnextnot (BV.ofList l) i = .ok (((List.range l.length).find?
      (fun (p : Nat) => decide (i.val ≤ (p : Int) + 1) && l.getD p (!false) == false)).map (· + 1)) := by
  have hnc := pack_length l
  rw [numBitChunks_eq] at hnc
  simp only [findnextnot]
  rw [ofList_len, ofList_chunks, if_neg (show ¬¬(i.val > 0) by omega), if_neg (show ¬(i.val > (l.length : Int)) by omega),
    if_neg (show ¬((pack l).length = 0) by omega)]
  generalize hst : i.val.toNat = st
  have hst' : i.val = st := by omega
  generalize hcs : div64 (st - 1) + 1 = cs
  generalize hw : mod64 (st - 1) = w
  have hcs' : cs = (st - 1) / 64 + 1 := by rw [← hcs]; rfl
  have hw' : w = (st - 1) % 64 := by rw [← hw]; rfl
  -- value of the predicate at a valid position
  have hf : ∀ q, q < l.length → (decide (i.val ≤ (q : Int) + 1) && l.getD q (!false) == false) =
      (decide (st ≤ q + 1) && !l.getD q false) := by
    intro q hq
    rw [show (!false) = true from rfl, getD_dflt l q true hq,
      decide_eq_decide.mpr (show i.val ≤ (q : Int) + 1 ↔ st ≤ q + 1 by constructor <;> intro h <;> omega)]
    cases l.getD q false <;> rfl
  have hY : ∀ (c : Nat), ∀ j, j < 64 → (cget (pack l) c ||| ~~~(msk64 <<< w)).getLsbD j =
      (decide (j < w) || l.getD (64 * (c - 1) + j) false) := by
    intro c j hj
    rw [BitVec.getLsbD_or, cbit l c j hj, nbit _ j hj, getLsbD_shl]
    by_cases hwj : w ≤ j
    · rw [if_pos ⟨hj, hwj⟩, msk64_bit _ (by omega), decide_eq_false (show ¬ j < w by omega)]
      simp
    · rw [if_neg (fun h => hwj h.2), decide_eq_true (show j < w by omega)]
      simp
  -- the first chunk read: positions before the end of the chunk of `st`
  have hfirst : ∀ (c : Nat), c = cs → ∀ t, t < 64 →
      (~~~(cget (pack l) c ||| ~~~(msk64 <<< w))).getLsbD t = (decide (w ≤ t) && !l.getD (64 * (cs - 1) + t) false) := by
    intro c hc t ht
    subst hc
    rw [nbit _ t ht, hY _ t ht]
    by_cases hwt : w ≤ t
    · rw [decide_eq_false (show ¬ t < w by omega), decide_eq_true hwt]
      simp
    · rw [decide_eq_true (show t < w by omega), decide_eq_false hwt]
      simp
  by_cases hlt : cs < (pack l).length
  · rw [if_pos hlt]
    by_cases hY1 : (cget (pack l) cs ||| ~~~(msk64 <<< w)) = msk64
    · rw [if_neg (by rw [hY1]; simp)]
      have hall0 : ∀ q, st ≤ q + 1 → q / 64 + 1 = cs → l.getD q false = true := by
        intro q hq hqc
        have := hY cs (q % 64) (Nat.mod_lt _ (by decide))
        rw [hY1, msk64_bit _ (Nat.mod_lt _ (by decide)), show 64 * (cs - 1) + q % 64 = q by omega,
          decide_eq_false (show ¬ q % 64 < w by omega), Bool.false_or] at this
        exact this.symm
      cases hg : (List.range ((pack l).length - 1 - cs)).find? (fun j => cget (pack l) (cs + 1 + j) != msk64) with
      | some j =>
        obtain ⟨g1, g2, g3⟩ := (find_some _ _ j).mp hg
        obtain ⟨t1, t2, t3⟩ := tz_spec _ (not_ne_zero _ (ne_of_bne_true g2))
        show Except.ok (some ((cs + j) * 64 + trailingOnes (cget (pack l) (cs + 1 + j)) + 1)) = _
        unfold trailingOnes
        generalize ht : trailingZeros (~~~(cget (pack l) (cs + 1 + j))) = t at t1 t2 t3 ⊢
        have hl0 : l.getD ((cs + j) * 64 + t) false = false := by
          rw [← bit_q l (cs + 1 + j) _ (by omega), show ((cs + j) * 64 + t) % 64 = t by omega]
          rw [nbit _ t t1] at t2
          simpa using t2
        have hyn : (cs + j) * 64 + t < l.length := by omega
        congr 1
        apply eq_some_fwd _ _ _ hyn
        · rw [hf _ hyn, hl0, decide_eq_true (show st ≤ (cs + j) * 64 + t + 1 by omega)]
          rfl
        · intro q hq
          have hqn : q < l.length := by omega
          rw [hf _ hqn]
          by_cases hq1 : st ≤ q + 1
          · have hlq : l.getD q false = true := by
              by_cases hqc : q / 64 + 1 = cs
              · exact hall0 q hq1 hqc
              · by_cases hqj : q / 64 < cs + j
                · have hc0 := eq_of_bne_false (g3 (q / 64 - cs) (by omega))
                  have := bit_q l (cs + 1 + (q / 64 - cs)) q (by omega)
                  rw [hc0, msk64_bit _ (Nat.mod_lt _ (by decide))] at this
                  exact this.symm
                · have := bit_q l (cs + 1 + j) q (by omega)
                  have h3 := t3 (q % 64) (by omega)
                  rw [nbit _ _ (Nat.mod_lt _ (by decide)), this] at h3
                  simpa using h3
            rw [hlq, Bool.not_true, Bool.and_false]
          · rw [decide_eq_false hq1]
            rfl
      | none =>
        have hall := (find_none _ _).mp hg
        show (if (cget (pack l) (pack l).length != mskEnd l.length) = true then
          (Except.ok (some (((pack l).length - 1) * 64 + trailingOnes (cget (pack l) (pack l).length) + 1)) :
            Jl (Option Nat)) else Except.ok none) = _
        have hmid : ∀ q, cs ≤ q / 64 → q / 64 < (pack l).length - 1 → l.getD q false = true := by
          intro q hq1 hq2
          have hc0 := eq_of_bne_false (hall (q / 64 - cs) (by omega))
          have := bit_q l (cs + 1 + (q / 64 - cs)) q (by omega)
          rw [hc0, msk64_bit _ (Nat.mod_lt _ (by decide))] at this
          exact this.symm
        -- the last chunk against `_msk_end(length)`
        have hlast : ∀ q, q / 64 = (pack l).length - 1 →
            (cget (pack l) (pack l).length).getLsbD (q % 64) = l.getD q false :=
          fun q hq => bit_q l _ q (by omega)
        have hmskq : ∀ q, q / 64 = (pack l).length - 1 →
            (mskEnd l.length).getLsbD (q % 64) = decide (q < l.length) := by
          intro q hq
          rw [getLsbD_mskEnd]
          apply decide_eq_decide.mpr
          constructor <;> intro h <;> omega
        by_cases hCL : cget (pack l) (pack l).length = mskEnd l.length
        · rw [if_neg (by rw [hCL]; simp)]
          congr 1
          apply eq_none_fwd
          intro q hq
          rw [hf _ hq]
          by_cases hq1 : st ≤ q + 1
          · have hlq : l.getD q false = true := by
              by_cases hqc : q / 64 + 1 = cs
              · exact hall0 q hq1 hqc
              · by_cases hqj : q / 64 < (pack l).length - 1
                · exact hmid q (by omega) hqj
                · have := hlast q (by omega)
                  rw [hCL, hmskq q (by omega), decide_eq_true hq] at this
                  exact this.symm
            rw [hlq, Bool.not_true, Bool.and_false]
          · rw [decide_eq_false hq1]
            rfl
        · rw [if_pos (bne_true_of_ne hCL)]
          unfold trailingOnes
          -- a valid position of the last chunk holds `false`
          have hex : ∃ j, j < 64 ∧ 64 * ((pack l).length - 1) + j < l.length ∧
              l.getD (64 * ((pack l).length - 1) + j) false = false := by
            apply Classical.byContradiction
            intro hne
            apply hCL
            apply BitVec.eq_of_getLsbD_eq
            intro j hj
            have hb := hlast (64 * ((pack l).length - 1) + j) (by omega)
            have hm := hmskq (64 * ((pack l).length - 1) + j) (by omega)
            rw [show (64 * ((pack l).length - 1) + j) % 64 = j by omega] at hb hm
            rw [hb, hm]
            by_cases hv : 64 * ((pack l).length - 1) + j < l.length
            · rw [decide_eq_true hv]
              cases hb' : l.getD (64 * ((pack l).length - 1) + j) false
              · exact absurd ⟨j, hj, hv, hb'⟩ hne
              · rfl
            · rw [decide_eq_false hv, getD_ge (by omega)]
          obtain ⟨j0, hj0, hv0, hl0⟩ := hex
          have hZ0 : (~~~(cget (pack l) (pack l).length)).getLsbD j0 = true := by
            rw [nbit _ _ hj0, cbit l _ _ hj0, hl0]
            rfl
          have hZ : ~~~(cget (pack l) (pack l).length) ≠ 0 := by
            intro h
            rw [h, getLsbD_zero64] at hZ0
            cases hZ0
          obtain ⟨t1, t2, t3⟩ := tz_spec _ hZ
          show Except.ok (some (((pack l).length - 1) * 64 +
            trailingZeros (~~~(cget (pack l) (pack l).length)) + 1)) = _
          generalize ht : trailingZeros (~~~(cget (pack l) (pack l).length)) = t at t1 t2 t3 ⊢
          have htj : t ≤ j0 := by
            apply Nat.le_of_not_lt
            intro hlt'
            rw [t3 j0 hlt'] at hZ0
            cases hZ0
          have hlt0 : l.getD (((pack l).length - 1) * 64 + t) false = false := by
            rw [nbit _ t t1, cbit l _ _ t1] at t2
            rw [show ((pack l).length - 1) * 64 + t = 64 * ((pack l).length - 1) + t by omega]
            simpa using t2
          have hyn : ((pack l).length - 1) * 64 + t < l.length := by omega
          congr 1
          apply eq_some_fwd _ _ _ hyn
          · rw [hf _ hyn, hlt0, decide_eq_true (show st ≤ ((pack l).length - 1) * 64 + t + 1 by omega)]
            rfl
          · intro q hq
            have hqn : q < l.length := by omega
            rw [hf _ hqn]
            by_cases hq1 : st ≤ q + 1
            · have hlq : l.getD q false = true := by
                by_cases hqc : q / 64 + 1 = cs
                · exact hall0 q hq1 hqc
                · by_cases hqj : q / 64 < (pack l).length - 1
                  · exact hmid q (by omega) hqj
                  · have h3 := t3 (q % 64) (by omega)
                    rw [nbit _ _ (Nat.mod_lt _ (by decide)), hlast q (by omega)] at h3
                    simpa using h3
              rw [hlq, Bool.not_true, Bool.and_false]
            · rw [decide_eq_false hq1]
              rfl
    · rw [if_pos (bne_true_of_ne hY1)]
      unfold trailingOnes
      obtain ⟨t1, t2, t3⟩ := tz_spec _ (not_ne_zero _ hY1)
      show Except.ok (some ((cs - 1) * 64 + trailingZeros (~~~(cget (pack l) cs ||| ~~~(msk64 <<< w))) + 1)) = _
      generalize ht : trailingZeros (~~~(cget (pack l) cs ||| ~~~(msk64 <<< w))) = t at t1 t2 t3 ⊢
      rw [hfirst cs rfl t t1, Bool.and_eq_true, decide_eq_true_iff] at t2
      obtain ⟨hwt, hl0'⟩ := t2
      have hl0 : l.getD ((cs - 1) * 64 + t) false = false := by
        rw [show (cs - 1) * 64 + t = 64 * (cs - 1) + t by omega]
        simpa using hl0'
      have hyn : (cs - 1) * 64 + t < l.length := by omega
      congr 1
      apply eq_some_fwd _ _ _ hyn
      · rw [hf _ hyn, hl0, decide_eq_true (show st ≤ (cs - 1) * 64 + t + 1 by omega)]
        rfl
      · intro q hq
        have hqn : q < l.length := by omega
        rw [hf _ hqn]
        by_cases hq1 : st ≤ q + 1
        · have h3 := t3 (q % 64) (by omega)
          rw [hfirst cs rfl _ (Nat.mod_lt _ (by decide)), decide_eq_true (show w ≤ q % 64 by omega),
            Bool.true_and, show 64 * (cs - 1) + q % 64 = q by omega] at h3
          rw [show l.getD q false = true by simpa using h3, Bool.not_true, Bool.and_false]
        · rw [decide_eq_false hq1]
          rfl
  · rw [if_neg hlt]
    have hcsn : (pack l).length = cs := by omega
    rw [hcsn]
    have hmskq : ∀ q, q / 64 = cs - 1 → (mskEnd l.length).getLsbD (q % 64) = decide (q < l.length) := by
      intro q hq
      rw [getLsbD_mskEnd]
      apply decide_eq_decide.mpr
      constructor <;> intro h <;> omega
    by_cases hYL : (cget (pack l) cs ||| ~~~(msk64 <<< w)) = mskEnd l.length
    · rw [if_neg (by rw [hYL]; simp)]
      congr 1
      apply eq_none_fwd
      intro q hq
      rw [hf _ hq]
      by_cases hq1 : st ≤ q + 1
      · have := hY cs (q % 64) (Nat.mod_lt _ (by decide))
        rw [hYL, hmskq q (by omega), decide_eq_true hq, decide_eq_false (show ¬ q % 64 < w by omega),
          Bool.false_or, show 64 * (cs - 1) + q % 64 = q by omega] at this
        rw [← this, Bool.not_true, Bool.and_false]
      · rw [decide_eq_false hq1]
        rfl
    · rw [if_pos (bne_true_of_ne hYL)]
      unfold trailingOnes
      have hex : ∃ j, j < 64 ∧ w ≤ j ∧ 64 * (cs - 1) + j < l.length ∧
          l.getD (64 * (cs - 1) + j) false = false := by
        apply Classical.byContradiction
        intro hne
        apply hYL
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        have hm := hmskq (64 * (cs - 1) + j) (by omega)
        rw [show (64 * (cs - 1) + j) % 64 = j by omega] at hm
        rw [hY cs j hj, hm]
        by_cases hv : 64 * (cs - 1) + j < l.length
        · rw [decide_eq_true hv]
          by_cases hjw : j < w
          · rw [decide_eq_true hjw]
            rfl
          · rw [decide_eq_false hjw, Bool.false_or]
            cases hb' : l.getD (64 * (cs - 1) + j) false
            · exact absurd ⟨j, hj, by omega, hv, hb'⟩ hne
            · rfl
        · rw [decide_eq_false hv, decide_eq_false (show ¬ j < w by omega), getD_ge (by omega)]
          rfl
      obtain ⟨j0, hj0, hwj0, hv0, hl0⟩ := hex
      have hZ0 : (~~~(cget (pack l) cs ||| ~~~(msk64 <<< w))).getLsbD j0 = true := by
        rw [hfirst cs rfl j0 hj0, decide_eq_true hwj0, hl0]
        rfl
      have hZ : ~~~(cget (pack l) cs ||| ~~~(msk64 <<< w)) ≠ 0 := by
        intro h
        rw [h, getLsbD_zero64] at hZ0
        cases hZ0
      obtain ⟨t1, t2, t3⟩ := tz_spec _ hZ
      show Except.ok (some ((cs - 1) * 64 + trailingZeros (~~~(cget (pack l) cs ||| ~~~(msk64 <<< w))) + 1)) = _
      generalize ht : trailingZeros (~~~(cget (pack l) cs ||| ~~~(msk64 <<< w))) = t at t1 t2 t3 ⊢
      have htj : t ≤ j0 := by
        apply Nat.le_of_not_lt
        intro hlt'
        rw [t3 j0 hlt'] at hZ0
        cases hZ0
      rw [hfirst cs rfl t t1, Bool.and_eq_true, decide_eq_true_iff] at t2
      obtain ⟨hwt, hlt0'⟩ := t2
      have hlt0 : l.getD ((cs - 1) * 64 + t) false = false := by
        rw [show (cs - 1) * 64 + t = 64 * (cs - 1) + t by omega]
        simpa using hlt0'
      have hyn : (cs - 1) * 64 + t < l.length := by omega
      congr 1
      apply eq_some_fwd _ _ _ hyn
      · rw [hf _ hyn, hlt0, decide_eq_true (show st ≤ (cs - 1) * 64 + t + 1 by omega)]
        rfl
      · intro q hq
        have hqn : q < l.length := by omega
        rw [hf _ hqn]
        by_cases hq1 : st ≤ q + 1
        · have h3 := t3 (q % 64) (by omega)
          rw [hfirst cs rfl _ (Nat.mod_lt _ (by decide)), decide_eq_true (show w ≤ q % 64 by omega),
            Bool.true_and, show 64 * (cs - 1) + q % 64 = q by omega] at h3
          rw [show l.getD q false = true by simpa using h3, Bool.not_true, Bool.and_false]
        · rw [decide_eq_false hq1]
          rfl

/-! ## `findprev(!, B, i)` -/

theorem prevnot_eq (l : List Bool) (i : JInt64) (h1 : 1 ≤ i.val) (h2 : i.val ≤ l.length) :
    findprevnot (BV.ofList l) i = .ok (((List.range l.length).reverse.find?
      (fun (p : Nat) => decide ((p : Int) + 1 ≤ i.val) && l.getD p (!false) == false)).map (· + 1)) := by
  have hnc := pack_length l
  rw [numBitChunks_eq] at hnc
  simp only [findprevnot]
  rw [ofList_len, ofList_chunks, if_neg (show ¬¬(i.val > 0) by omega), if_neg (show ¬(i.val > (l.length : Int)) by omega)]
  generalize hst : i.val.toNat = st
  have hst' : i.val = st := by omega
  generalize hcs : div64 (st - 1) + 1 = cs
  have hcs' : cs = (st - 1) / 64 + 1 := by rw [← hcs]; rfl
  have hf : ∀ q, q < l.length → (decide ((q : Int) + 1 ≤ i.val) && l.getD q (!false) == false) =
      (decide (q + 1 ≤ st) && !l.getD q false) := by
    intro q hq
    rw [show (!false) = true from rfl, getD_dflt l q true hq,
      decide_eq_decide.mpr (show (q : Int) + 1 ≤ i.val ↔ q + 1 ≤ st by constructor <;> intro h <;> omega)]
    cases l.getD q false <;> rfl
  -- `~(chunk | ~_msk_end(st))` has the clear bits at positions up to `st`
  have hZ : ∀ (c : Nat), ∀ j, j < 64 → (~~~(cget (pack l) c ||| ~~~(mskEnd st))).getLsbD j =
      (decide (64 * (cs - 1) + j + 1 ≤ st) && !l.getD (64 * (c - 1) + j) false) := by
    intro c j hj
    rw [nbit _ j hj, BitVec.getLsbD_or, cbit l c j hj, nbit _ j hj, getLsbD_mskEnd]
    have e : decide (j < 64 ∧ (st % 64 = 0 ∨ j < st % 64)) = decide (64 * (cs - 1) + j + 1 ≤ st) :=
      decide_eq_decide.mpr (by constructor <;> intro h <;> omega)
    rw [e]
    cases decide (64 * (cs - 1) + j + 1 ≤ st) <;> cases l.getD (64 * (c - 1) + j) false <;> rfl
  by_cases hY1 : (cget (pack l) cs ||| ~~~(mskEnd st)) = msk64
  · rw [if_neg (by rw [hY1]; simp)]
    have hall0 : ∀ q, q + 1 ≤ st → q / 64 + 1 = cs → l.getD q false = true := by
      intro q hq hqc
      have := hZ cs (q % 64) (Nat.mod_lt _ (by decide))
      rw [hY1, show 64 * (cs - 1) + q % 64 = q by omega, decide_eq_true hq, Bool.true_and,
        nbit _ _ (Nat.mod_lt _ (by decide)), msk64_bit _ (Nat.mod_lt _ (by decide))] at this
      simpa using this
    congr 1
    cases hg : (List.range (cs - 1)).find? (fun j => cget (pack l) (cs - 1 - j) != msk64) with
    | none =>
      have hall := (find_none _ _).mp hg
      apply eq_none_bwd
      intro q hq
      rw [hf _ hq]
      by_cases hq1 : q + 1 ≤ st
      · have hlq : l.getD q false = true := by
          by_cases hqc : q / 64 + 1 = cs
          · exact hall0 q hq1 hqc
          · have hc0 := eq_of_bne_false (hall (cs - 2 - q / 64) (by omega))
            have := bit_q l (cs - 1 - (cs - 2 - q / 64)) q (by omega)
            rw [hc0, msk64_bit _ (Nat.mod_lt _ (by decide))] at this
            exact this.symm
        rw [hlq, Bool.not_true, Bool.and_false]
      · rw [decide_eq_false hq1]
        rfl
    | some j =>
      obtain ⟨g1, g2, g3⟩ := (find_some _ _ j).mp hg
      obtain ⟨t1, t2, t3, t4⟩ := top_spec _ (not_ne_zero _ (ne_of_bne_true g2))
      show some ((cs - 2 - j) * 64 + (64 - leadingOnes (cget (pack l) (cs - 1 - j)))) = _
      unfold leadingOnes
      generalize ht : topSetBit (~~~(cget (pack l) (cs - 1 - j))) = t at t1 t2 t3 t4 ⊢
      rw [show 64 - (64 - t) = t by omega]
      have hl0 : l.getD ((cs - 2 - j) * 64 + t - 1) false = false := by
        rw [nbit _ _ (by omega)] at t3
        rw [← bit_q l (cs - 1 - j) _ (by omega), show ((cs - 2 - j) * 64 + t - 1) % 64 = t - 1 by omega]
        simpa using t3
      have hyn : (cs - 2 - j) * 64 + t - 1 < l.length := by omega
      apply eq_some_bwd _ _ _ (by omega) hyn
      · rw [hf _ hyn, hl0, decide_eq_true (show (cs - 2 - j) * 64 + t - 1 + 1 ≤ st by omega)]
        rfl
      · intro q hq hqn
        rw [hf _ hqn]
        by_cases hq1 : q + 1 ≤ st
        · have hlq : l.getD q false = true := by
            by_cases hqc : q / 64 + 1 = cs
            · exact hall0 q hq1 hqc
            · by_cases hqj : cs - 2 - j < q / 64
              · have hc0 := eq_of_bne_false (g3 (cs - 2 - q / 64) (by omega))
                have := bit_q l (cs - 1 - (cs - 2 - q / 64)) q (by omega)
                rw [hc0, msk64_bit _ (Nat.mod_lt _ (by decide))] at this
                exact this.symm
              · have h4 := t4 (q % 64) (by omega) (Nat.mod_lt _ (by decide))
                rw [nbit _ _ (Nat.mod_lt _ (by decide)), bit_q l (cs - 1 - j) q (by omega)] at h4
                simpa using h4
          rw [hlq, Bool.not_true, Bool.and_false]
        · rw [decide_eq_false hq1]
          rfl
  · rw [if_pos (bne_true_of_ne hY1)]
    obtain ⟨t1, t2, t3, t4⟩ := top_spec _ (not_ne_zero _ hY1)
    show Except.ok (some ((cs - 1) * 64 + (64 - leadingOnes (cget (pack l) cs ||| ~~~(mskEnd st))))) = _
    unfold leadingOnes
    generalize ht : topSetBit (~~~(cget (pack l) cs ||| ~~~(mskEnd st))) = t at t1 t2 t3 t4 ⊢
    rw [show 64 - (64 - t) = t by omega]
    rw [hZ cs (t - 1) (by omega), Bool.and_eq_true, decide_eq_true_iff] at t3
    obtain ⟨hwt, hl0'⟩ := t3
    have hl0 : l.getD ((cs - 1) * 64 + t - 1) false = false := by
      rw [show (cs - 1) * 64 + t - 1 = 64 * (cs - 1) + (t - 1) by omega]
      simpa using hl0'
    have hyn : (cs - 1) * 64 + t - 1 < l.length := by omega
    congr 1
    apply eq_some_bwd _ _ _ (by omega) hyn
    · rw [hf _ hyn, hl0, decide_eq_true (show (cs - 1) * 64 + t - 1 + 1 ≤ st by omega)]
      rfl
    · intro q hq hqn
      rw [hf _ hqn]
      by_cases hq1 : q + 1 ≤ st
      · have h4 := t4 (q % 64) (by omega) (Nat.mod_lt _ (by decide))
        rw [hZ cs _ (Nat.mod_lt _ (by decide)), show 64 * (cs - 1) + q % 64 = q by omega,
          decide_eq_true (show q + 1 ≤ st by omega), Bool.true_and] at h4
        rw [show l.getD q false = true by simpa using h4, Bool.not_true, Bool.and_false]
      · rw [decide_eq_false hq1]
        rfl

/-! ## The four searches -/

theorem next_eq (l : List Bool) (i : JInt64) (h1 : 1 ≤ i.val) (h2 : i.val ≤ l.length) :
    findnext (BV.ofList l) i = .ok (((List.range l.length).find?
      (fun (p : Nat) => decide (i.val ≤ (p : Int) + 1) && l.getD p (!true) == true)).map (· + 1)) := by
  simp only [findnext]
  rw [ofList_len, ofList_chunks, if_neg (show ¬¬(i.val > 0) by omega), if_neg (show ¬(i.val > (l.length : Int)) by omega),
    next_unsafe l _ (by omega) (by omega)]
  have e : (fun (p : Nat) => decide (i.val.toNat ≤ p + 1) && l.getD p false) =
      (fun (p : Nat) => decide (i.val ≤ (p : Int) + 1) && l.getD p (!true) == true) := by
    funext p
    rw [show (!true) = false from rfl,
      decide_eq_decide.mpr (show i.val.toNat ≤ p + 1 ↔ i.val ≤ (p : Int) + 1 by constructor <;> intro h <;> omega)]
    cases l.getD p false <;> rfl
  exact congrArg (fun f => (Except.ok (((List.range l.length).find? f).map (· + 1)) : Jl (Option Nat))) e

theorem prev_eq (l : List Bool) (i : JInt64) (h1 : 1 ≤ i.val) (h2 : i.val ≤ l.length) :
    findprev (BV.ofList l) i = .ok (((List.range l.length).reverse.find?
      (fun (p : Nat) => decide ((p : Int) + 1 ≤ i.val) && l.getD p (!true) == true)).map (· + 1)) := by
  simp only [findprev]
  rw [ofList_len, ofList_chunks, if_neg (show ¬¬(i.val > 0) by omega), if_neg (show ¬(i.val > (l.length : Int)) by omega),
    prev_unsafe l _ (by omega) (by omega)]
  have e : (fun (p : Nat) => decide (p + 1 ≤ i.val.toNat) && l.getD p false) =
      (fun (p : Nat) => decide ((p : Int) + 1 ≤ i.val) && l.getD p (!true) == true) := by
    funext p
    rw [show (!true) = false from rfl,
      decide_eq_decide.mpr (show p + 1 ≤ i.val.toNat ↔ (p : Int) + 1 ≤ i.val by constructor <;> intro h <;> omega)]
    cases l.getD p false <;> rfl
  exact congrArg (fun f => (Except.ok (((List.range l.length).reverse.find? f).map (· + 1)) : Jl (Option Nat))) e

theorem fwd_spec (l : List Bool) (i : JInt64) (b : Bool) :
    kindOf (if b then findnext (BV.ofList l) i else findnextnot (BV.ofList l) i) =
      kindOf (if i.val < 1 then (.error .boundsError : Jl (Option Nat))
        else .ok (((List.range l.length).find? (fun (p : Nat) =>
          decide (i.val ≤ (p : Int) + 1) && l.getD p (!b) == b)).map (· + 1))) := by
  by_cases h1 : i.val < 1
  · rw [if_pos h1]
    cases b
    · show kindOf (findnextnot (BV.ofList l) i) = _
      simp only [findnextnot]
      rw [if_pos (show ¬(i.val > 0) by omega)]
      try rfl
    · show kindOf (findnext (BV.ofList l) i) = _
      simp only [findnext]
      rw [if_pos (show ¬(i.val > 0) by omega)]
      try rfl
  · rw [if_neg h1]
    by_cases h2 : i.val > l.length
    · have hnone : (List.range l.length).find? (fun (p : Nat) =>
          decide (i.val ≤ (p : Int) + 1) && l.getD p (!b) == b) = none := by
        apply (find_none _ _).mpr
        intro q hq
        show (decide (i.val ≤ (q : Int) + 1) && _) = false
        rw [decide_eq_false (show ¬(i.val ≤ (q : Int) + 1) by omega)]
        try rfl
      rw [hnone]
      cases b
      · show kindOf (findnextnot (BV.ofList l) i) = _
        simp only [findnextnot]
        rw [ofList_len, if_neg (show ¬¬(i.val > 0) by omega), if_pos h2]
        try rfl
      · show kindOf (findnext (BV.ofList l) i) = _
        simp only [findnext]
        rw [ofList_len, if_neg (show ¬¬(i.val > 0) by omega), if_pos h2]
        try rfl
    · cases b
      · show kindOf (findnextnot (BV.ofList l) i) = _
        rw [nextnot_eq l i (by omega) (by omega)]
        try rfl
      · show kindOf (findnext (BV.ofList l) i) = _
        rw [next_eq l i (by omega) (by omega)]
        try rfl

theorem bwd_spec (l : List Bool) (i : JInt64) (b : Bool) :
    kindOf (if b then findprev (BV.ofList l) i else findprevnot (BV.ofList l) i) =
      kindOf (if i.val > l.length then (.error .boundsError : Jl (Option Nat))
        else .ok (((List.range l.length).reverse.find? (fun (p : Nat) =>
          decide ((p : Int) + 1 ≤ i.val) && l.getD p (!b) == b)).map (· + 1))) := by
  by_cases h2 : i.val > l.length
  · rw [if_pos h2]
    cases b
    · show kindOf (findprevnot (BV.ofList l) i) = _
      simp only [findprevnot]
      rw [ofList_len, if_neg (show ¬¬(i.val > 0) by omega), if_pos h2]
      try rfl
    · show kindOf (findprev (BV.ofList l) i) = _
      simp only [findprev]
      rw [ofList_len, if_neg (show ¬¬(i.val > 0) by omega), if_pos h2]
      try rfl
  · rw [if_neg h2]
    by_cases h1 : i.val < 1
    · have hnone : (List.range l.length).reverse.find? (fun (p : Nat) =>
          decide ((p : Int) + 1 ≤ i.val) && l.getD p (!b) == b) = none := by
        apply (find_rev_none _ _).mpr
        intro q hq
        show (decide ((q : Int) + 1 ≤ i.val) && _) = false
        rw [decide_eq_false (show ¬((q : Int) + 1 ≤ i.val) by omega)]
        try rfl
      rw [hnone]
      cases b
      · show kindOf (findprevnot (BV.ofList l) i) = _
        simp only [findprevnot]
        rw [if_pos (show ¬(i.val > 0) by omega)]
        try rfl
      · show kindOf (findprev (BV.ofList l) i) = _
        simp only [findprev]
        rw [if_pos (show ¬(i.val > 0) by omega)]
        try rfl
    · cases b
      · show kindOf (findprevnot (BV.ofList l) i) = _
        rw [prevnot_eq l i (by omega) (by omega)]
        try rfl
      · show kindOf (findprev (BV.ofList l) i) = _
        rw [prev_eq l i (by omega) (by omega)]
        try rfl

end FindProof

open FindProof in
theorem findAgrees : FindAgrees := by
  intro l i b _
  exact ⟨fwd_spec l i b, bwd_spec l i b⟩

end JuliaLean.BitArrays
