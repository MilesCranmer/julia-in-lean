import JuliaLean.BitSetsCov.BitSetProof1
import JuliaLean.BitArrays.FindProof
import JuliaLean.BitArrays.RangeProof

/-!
# Iteration over a `BitSet`

`cpos w` lists the set bits of a chunk; iteration (`trailing_zeros` and
`_blsr`) walks them in order, chunk after chunk, so `elems s` is the list of
set positions of `s.bits` shifted by `64 * offset`.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays JuliaLean.BitArrays.BitSetProof

namespace BS

/-- The set bits of a chunk, in increasing order. -/
def cpos (w : U64) : List Nat := (List.range 64).filter (fun j => w.getLsbD j)

/-- The set positions (0-based) of a chunk vector. -/
def pos (bits : List U64) : List Nat := (List.range (64 * bits.length)).filter (bitOf bits)

/-- The value of position `p` of a `BitSet` at chunk offset `off`. -/
def elemAt (off : Int) (p : Nat) : JInt64 := JInt.wrap .i64 ((p : Int) + 64 * off)

theorem getLsbD_blsr (x : U64) (hx : x ≠ 0) (j : Nat) :
    (blsr x).getLsbD j = (x.getLsbD j && decide (j ≠ trailingZeros x)) := by
  obtain ⟨ht, hbit, hlow⟩ := FindProof.tz_spec x hx
  have hpos : 1 ≤ x.toNat := by
    rcases Nat.eq_zero_or_pos x.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hx
    · exact h
  have hle : (1 : U64) ≤ x := by
    rw [BitVec.le_def]; exact hpos
  have hsub : (x - 1).toNat = x.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le hle]; rfl
  have hmod : x.toNat % 2 ^ (trailingZeros x + 1) = 2 ^ trailingZeros x := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
    by_cases hi : i < trailingZeros x
    · have := hlow i hi
      rw [← BitVec.testBit_toNat] at this
      rw [this]; simp; omega
    · by_cases hi2 : i = trailingZeros x
      · subst hi2
        rw [← BitVec.testBit_toNat] at hbit
        rw [hbit]; simp
      · have h3 : ¬ i < trailingZeros x + 1 := by omega
        have h4 : trailingZeros x ≠ i := fun h => hi2 h.symm
        simp [h3, h4]
  have h2 : 1 ≤ 2 ^ trailingZeros x := Nat.one_le_two_pow
  have hpow : 2 ^ (trailingZeros x + 1) = 2 * 2 ^ trailingZeros x := by rw [Nat.pow_succ]; omega
  have hx' : x.toNat = 2 ^ (trailingZeros x + 1) * (x.toNat / 2 ^ (trailingZeros x + 1)) +
      2 ^ trailingZeros x := by
    have := Nat.div_add_mod x.toNat (2 ^ (trailingZeros x + 1))
    omega
  have hx1 : x.toNat - 1 = 2 ^ (trailingZeros x + 1) * (x.toNat / 2 ^ (trailingZeros x + 1)) +
      (2 ^ trailingZeros x - 1) := by omega
  show (x &&& (x - 1)).getLsbD j = _
  have hC : x.getLsbD j = (2 ^ (trailingZeros x + 1) * (x.toNat / 2 ^ (trailingZeros x + 1)) +
      2 ^ trailingZeros x).testBit j := by
    rw [← BitVec.testBit_toNat, ← hx']
  have hB : (x - 1).getLsbD j = (2 ^ (trailingZeros x + 1) * (x.toNat / 2 ^ (trailingZeros x + 1)) +
      (2 ^ trailingZeros x - 1)).testBit j := by
    rw [← BitVec.testBit_toNat, hsub, hx1]
  rw [BitVec.getLsbD_and, hB, hC, Nat.testBit_two_pow_mul_add _ (by omega) j,
    Nat.testBit_two_pow_mul_add _ (by omega) j]
  split
  · rw [Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases hj : j = trailingZeros x
    · subst hj; simp
    · have h' : trailingZeros x ≠ j := fun h => hj h.symm
      simp [hj, h']
  · rename_i hj
    have : j ≠ trailingZeros x := by omega
    simp [this]

theorem filter_split (p q : Nat → Bool) (t : Nat) (ht : p t = true) (hq : q t = false)
    (hlow : ∀ j, j < t → p j = false) (heq : ∀ j, j ≠ t → p j = q j) :
    ∀ n, (List.range n).filter p = (if t < n then [t] else []) ++ (List.range n).filter q := by
  have hqlow : ∀ j, j < t → q j = false := fun j hj => by rw [← heq j (by omega)]; exact hlow j hj
  have hnil : ∀ n, n ≤ t → (List.range n).filter q = [] := by
    intro n hn
    rw [List.filter_eq_nil_iff]
    intro j hj
    have := List.mem_range.mp hj
    simp [hqlow j (by omega)]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.filter_append, ih]
    by_cases hnt : n < t
    · rw [if_neg (by omega), if_neg (by omega)]
      simp [hlow n hnt, hqlow n hnt]
    · by_cases hn : n = t
      · subst hn
        rw [if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self _), hnil n (Nat.le_refl _)]
        simp [ht, hq]
      · rw [if_pos (by omega), if_pos (by omega)]
        simp [List.filter, heq n hn]

theorem cpos_blsr (w : U64) (hw : w ≠ 0) : cpos w = trailingZeros w :: cpos (blsr w) := by
  obtain ⟨ht, hbit, hlow⟩ := FindProof.tz_spec w hw
  unfold cpos
  rw [filter_split (fun j => w.getLsbD j) (fun j => (blsr w).getLsbD j) (trailingZeros w) hbit
    (by rw [getLsbD_blsr w hw]; simp) hlow
    (fun j hj => by rw [getLsbD_blsr w hw]; simp [hj]) 64, if_pos ht]
  rfl

theorem cpos_zero : cpos 0 = [] := by
  unfold cpos
  rw [List.filter_eq_nil_iff]
  intro j _
  simp

theorem cpos_eq_nil (w : U64) (h : cpos w = []) : w = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  unfold cpos at h
  rw [List.filter_eq_nil_iff] at h
  have := h j (List.mem_range.mpr hj)
  simpa using this

theorem bitOf_chunk (bits : List U64) (c j : Nat) (hj : j < 64) :
    bitOf bits (64 * c + j) = (bits.getD c 0).getLsbD j := by
  unfold bitOf
  rw [show (64 * c + j) / 64 = c by omega, show (64 * c + j) % 64 = j by omega]

/-- The set positions, chunk by chunk. -/
theorem pos_eq (bits : List U64) : ∀ n,
    (List.range (64 * n)).filter (bitOf bits) =
      (List.range n).flatMap (fun c => (cpos (bits.getD c 0)).map (64 * c + ·))
  | 0 => by simp
  | n + 1 => by
    rw [show 64 * (n + 1) = 64 * n + 64 by omega, List.range_add, List.filter_append, pos_eq bits n]
    rw [show List.range (n + 1) = List.range n ++ [n] from List.range_succ]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    rw [List.filter_map]
    unfold cpos
    congr 1
    apply List.filter_congr
    intro j hj
    have := List.mem_range.mp hj
    simp [Function.comp, bitOf_chunk bits n j this]

/-- The remaining positions from iteration state `(w, idx)`. -/
def rest (bits : List U64) (w : U64) (idx : Nat) : List Nat :=
  (cpos w).map (64 * (idx - 1) + ·) ++
    (List.range (bits.length - idx)).flatMap (fun k => (cpos (bits.getD (idx + k) 0)).map (64 * (idx + k) + ·))

theorem iterStep_nz (s : BitSetS) (fuel : Nat) (w : U64) (idx : Nat) (hw : w ≠ 0) :
    iterStep s fuel w idx =
      some (JInt.wrap .i64 (trailingZeros w + (shl6 ((idx : Int) - 1 + s.offset)).val), blsr w, idx) := by
  unfold iterStep
  exact if_pos hw

theorem iterStep_end (s : BitSetS) (fuel : Nat) (idx : Nat) (h : idx = s.bits.length) :
    iterStep s fuel 0 idx = none := by
  cases fuel <;> simp [iterStep, h]

theorem iterStep_next (s : BitSetS) (fuel : Nat) (idx : Nat) (h : idx < s.bits.length) :
    iterStep s (fuel + 1) 0 idx = iterStep s fuel (s.bits.getD idx 0) (idx + 1) := by
  simp [iterStep, show idx ≠ s.bits.length by omega, vget]

theorem iterStep_fuel (s : BitSetS) : ∀ (n : Nat) (f1 f2 : Nat) (w : U64) (idx : Nat),
    s.bits.length - idx ≤ n → n ≤ f1 → n ≤ f2 → idx ≤ s.bits.length →
    iterStep s f1 w idx = iterStep s f2 w idx
  | n, f1, f2, w, idx, hn, h1, h2, hi => by
    by_cases hw : w = 0
    · subst hw
      by_cases he : idx = s.bits.length
      · rw [iterStep_end s f1 idx he, iterStep_end s f2 idx he]
      · obtain ⟨g1, rfl⟩ : ∃ g, f1 = g + 1 := ⟨f1 - 1, by omega⟩
        obtain ⟨g2, rfl⟩ : ∃ g, f2 = g + 1 := ⟨f2 - 1, by omega⟩
        rw [iterStep_next s g1 idx (by omega), iterStep_next s g2 idx (by omega)]
        exact iterStep_fuel s (n - 1) g1 g2 _ (idx + 1) (by omega) (by omega) (by omega) (by omega)
    · rw [iterStep_nz s f1 w idx hw, iterStep_nz s f2 w idx hw]
termination_by n => n
decreasing_by omega

theorem wrap_add_wrap (a b : Int) : JInt.wrap .i64 (a + (JInt.wrap .i64 b).val) = JInt.wrap .i64 (a + b) := by
  apply Subtype.ext
  show wrapInt .i64 (a + wrapInt .i64 b) = wrapInt .i64 (a + b)
  simp only [wrapInt, IntTy.signed, IntTy.bits, if_true]
  omega

theorem elem_step (off : Int) (w : U64) (idx : Nat) (hidx : 1 ≤ idx) :
    JInt.wrap .i64 (trailingZeros w + (shl6 ((idx : Int) - 1 + off)).val) =
      elemAt off (64 * (idx - 1) + trailingZeros w) := by
  unfold shl6 elemAt
  rw [wrap_add_wrap]
  congr 1
  omega

theorem length_cpos (w : U64) : (cpos w).length ≤ 64 := by
  unfold cpos
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem rest_next (bits : List U64) (idx : Nat) (h : idx < bits.length) :
    rest bits 0 idx = rest bits (bits.getD idx 0) (idx + 1) := by
  unfold rest
  rw [cpos_zero, List.map_nil, List.nil_append,
    show bits.length - idx = (bits.length - (idx + 1)) + 1 by omega, List.range_succ_eq_map,
    List.flatMap_cons]
  simp only [Nat.add_zero, Nat.add_sub_cancel]
  congr 1
  simp only [List.flatMap_map]
  congr 1
  funext k
  rw [show idx + (k + 1) = idx + 1 + k by omega]

/-- Iteration from a state yields the remaining positions. -/
theorem iterFrom_eq (s : BitSetS) : ∀ (m fuel : Nat) (w : U64) (idx : Nat),
    (rest s.bits w idx).length + (s.bits.length - idx) ≤ m →
    (rest s.bits w idx).length < fuel → idx ≤ s.bits.length → (idx = 0 → w = 0) →
    iterFrom s fuel (w, idx) = (rest s.bits w idx).map (elemAt s.offset)
  | m, fuel, w, idx, hm, hf, hi, h0 => by
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
    by_cases hw : w = 0
    · subst hw
      by_cases he : idx = s.bits.length
      · have hr : rest s.bits 0 idx = [] := by
          unfold rest; rw [cpos_zero, he, Nat.sub_self]; simp
        simp only [iterFrom, iterate, iterStep_end s _ idx he, hr, List.map_nil]
      · have hn := rest_next s.bits idx (by omega)
        have hit : iterate s (0, idx) = iterate s (s.bits.getD idx 0, idx + 1) := by
          unfold iterate
          obtain ⟨L, hL⟩ : ∃ L, s.bits.length + 1 = L + 1 := ⟨_, rfl⟩
          rw [hL, iterStep_next s L idx (by omega)]
          exact iterStep_fuel s (s.bits.length - (idx + 1)) _ _ _ _ (Nat.le_refl _) (by omega)
            (by omega) (by omega)
        have hm1 : 1 ≤ m := by omega
        have ih := iterFrom_eq s (m - 1) (g + 1) (s.bits.getD idx 0) (idx + 1)
          (by rw [← hn]; omega) (by rw [← hn]; omega) (by omega) (by omega)
        rw [hn]
        rw [← ih]
        simp only [iterFrom, hit]
    · have hidx : 1 ≤ idx := by
        rcases Nat.eq_zero_or_pos idx with h | h
        · exact absurd (h0 h) hw
        · exact h
      have hr : rest s.bits w idx = (64 * (idx - 1) + trailingZeros w) :: rest s.bits (blsr w) idx := by
        unfold rest; rw [cpos_blsr w hw]; simp
      have hit : iterate s (w, idx) =
          some (elemAt s.offset (64 * (idx - 1) + trailingZeros w), blsr w, idx) := by
        unfold iterate; simp only; rw [iterStep_nz s _ w idx hw, elem_step _ _ _ hidx]
      rw [hr, List.map_cons]
      simp only [iterFrom, hit]
      congr 1
      rw [hr] at hm hf
      simp only [List.length_cons] at hm hf
      have hm1 : 1 ≤ m := by omega
      exact iterFrom_eq s (m - 1) g (blsr w) idx (by omega) (by omega) hi (fun h => absurd h (by omega))
termination_by m => m
decreasing_by all_goals omega

theorem length_flatMap_le (bits : List U64) (a n : Nat) :
    ((List.range n).flatMap (fun k => (cpos (bits.getD (a + k) 0)).map (64 * (a + k) + ·))).length ≤ 64 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp only [List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map]
    have := length_cpos (bits.getD (a + n) 0)
    omega

theorem elems_eq (s : BitSetS) : elems s = (pos s.bits).map (elemAt s.offset) := by
  have hr : rest s.bits 0 0 = pos s.bits := by
    unfold rest pos
    rw [cpos_zero, List.map_nil, List.nil_append, Nat.sub_zero, pos_eq]
    simp
  have hl : (rest s.bits 0 0).length ≤ 64 * s.bits.length := by
    unfold rest; rw [cpos_zero]; simpa using length_flatMap_le s.bits 0 s.bits.length
  unfold elems
  rw [iterFrom_eq s _ _ 0 0 (Nat.le_refl _) (by omega) (Nat.zero_le _) (fun _ => rfl), hr]

end BS

end JuliaLean.BitSetsCov
