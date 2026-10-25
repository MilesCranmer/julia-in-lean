import JuliaLean.ParsePrint.IntPrint

/-!
Properties of `string(n; base, pad)`, `digits` and `digits!` (`base/intfuncs.jl`).
-/

namespace JuliaLean.ParsePrint.IntPrint

open JuliaLean

/-- `string(n; base)` accepts every negative base `-62 ≤ base ≤ -2` for every
integer `n`: `_base` documents negative bases for negative `n`
(`base/intfuncs.jl:1048-1049`), and `digits` writes any `n` in them. -/
def StringNegativeBase : Prop := ∀ (t : IntTy) (n : JInt t) (b : Int),
  -62 ≤ b → b ≤ -2 → ∃ s, string n (JInt.lit .i64 b) = .ok s

set_option maxRecDepth 8192 in
theorem stringNegativeBase_refuted : ¬ StringNegativeBase := by
  intro h
  obtain ⟨s, hs⟩ := h .u8 (JInt.lit .u8 200) (-2) (by decide) (by decide)
  have : string (JInt.lit .u8 200) (JInt.lit .i64 (-2)) =
      .error (.inexactError IntTy.i8.name) := by decide
  rw [this] at hs
  cases hs

/-- `digits(n; base)` succeeds for every `Int` base with `base ≥ 2` or `base ≤ -2`,
the restriction its error message states (`base/intfuncs.jl:1250`). -/
def DigitsValidBase : Prop := ∀ (t : IntTy) (n : JInt t) (b : JInt .i64),
  (b.val ≤ -2 ∨ 2 ≤ b.val) → ∃ ds, digits n b = .ok ds

set_option maxRecDepth 8192 in
theorem digitsValidBase_refuted : ¬ DigitsValidBase := by
  intro h
  obtain ⟨ds, hds⟩ := h .i64 (JInt.lit .i64 5) (JInt.typemin .i64) (Or.inl (by decide))
  have : digits (JInt.lit .i64 5) (JInt.typemin .i64) =
      .error (.domainError "base must be ≥ 2 or ≤ -2") := by decide
  rw [this] at hds
  cases hds

/-- `sum(d[k] * base^(k-1))`, as in the `digits` docstring. -/
def horner (b : Int) : List Int → Int
  | [] => 0
  | d :: ds => d + b * horner b ds

theorem divremDigits_inv (b : Int) (hb : 0 < b) : ∀ (L : Nat) (n : Int),
    ∃ q, horner b (divremDigits b L n) + b ^ L * q = n ∧ (divremDigits b L n).length = L ∧
      ∀ d ∈ divremDigits b L n, d.natAbs < b.natAbs
  | 0, n => ⟨n, by simp [divremDigits, horner]⟩
  | L+1, n => by
    obtain ⟨q, hq, hl, hd⟩ := divremDigits_inv b hb L (n.tdiv b)
    refine ⟨q, ?_, by simp only [divremDigits, List.length_cons, hl], ?_⟩
    · have e := Int.tmod_add_mul_tdiv n b
      have : horner b (divremDigits b (L + 1) n) + b ^ (L + 1) * q
          = n.tmod b + b * (horner b (divremDigits b L (n.tdiv b)) + b ^ L * q) := by
        simp only [divremDigits, horner, Int.pow_succ]
        rw [Int.mul_add, Int.mul_comm (b ^ L) b, Int.mul_assoc, Int.add_assoc]
      rw [this, hq]
      exact e
    · intro d hdm
      simp only [divremDigits, List.mem_cons] at hdm
      rcases hdm with rfl | hdm
      · have h1 := Int.tmod_lt_of_pos n hb
        have h2 := Int.lt_tmod_of_pos n hb
        omega
      · exact hd d hdm

theorem negDigits_inv (b : Int) (hb : b < 0) : ∀ (L : Nat) (n : Int),
    ∃ q, horner b (negDigits b L n) + b ^ L * q = n ∧ (negDigits b L n).length = L ∧
      ∀ d ∈ negDigits b L n, 0 ≤ d ∧ d < -b
  | 0, n => ⟨n, by simp [negDigits, horner]⟩
  | L+1, n => by
    obtain ⟨q, hq, hl, hd⟩ := negDigits_inv b hb L (-(n / (-b)))
    refine ⟨q, ?_, by simp only [negDigits, List.length_cons, hl], ?_⟩
    · have e := Int.emod_add_mul_ediv n (-b)
      have : horner b (negDigits b (L + 1) n) + b ^ (L + 1) * q
          = n % -b + b * (horner b (negDigits b L (-(n / -b))) + b ^ L * q) := by
        simp only [negDigits, horner, Int.pow_succ]
        rw [Int.mul_add, Int.mul_comm (b ^ L) b, Int.mul_assoc, Int.add_assoc]
      rw [this, hq, Int.mul_neg, ← Int.neg_mul]
      exact e
    · intro d hdm
      simp only [negDigits, List.mem_cons] at hdm
      rcases hdm with rfl | hdm
      · exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
      · exact hd d hdm

theorem pow2Digits_eq (k : Nat) : ∀ (L : Nat) (n : Int), 0 ≤ n →
    pow2Digits n k L = divremDigits (2 ^ k) L n
  | 0, _, _ => by simp [pow2Digits, divremDigits]
  | L+1, n, hn => by
    have hpos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
    have tail := pow2Digits_eq k L (n / 2 ^ k) (Int.ediv_nonneg hn (Int.le_of_lt hpos))
    simp only [pow2Digits, divremDigits, List.range_succ_eq_map, List.map_cons, List.map_map]
    rw [Int.tmod_eq_emod_of_nonneg hn, Int.tdiv_eq_ediv_of_nonneg hn, ← tail]
    simp only [Nat.mul_zero, Int.pow_zero, Int.ediv_one, pow2Digits]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.mul_succ, Int.pow_add]
    rw [Int.ediv_ediv_of_nonneg (Int.le_of_lt hpos), Int.mul_comm]

/-- A positive value with one set bit is the power of two at its trailing-zero count. -/
theorem pow2_of_ispow2 (b : JInt .i64) (h : JuliaLean.IntArith.PowersDigits.ispow2 b = true) :
    b.val = 2 ^ JuliaLean.IntArith.PowersDigits.trailingZeros b := by
  simp only [JuliaLean.IntArith.PowersDigits.ispow2, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, JuliaLean.IntArith.PowersDigits.countOnes] at h
  obtain ⟨hpos, hone⟩ := h
  have hlo : (-9223372036854775808 : Int) ≤ b.val := b.property.1
  have hhi : b.val ≤ 9223372036854775807 := b.property.2
  have hx : (JInt.rem IntTy.i64.toUnsigned b).val = b.val % 18446744073709551616 := rfl
  have hx' : (JInt.rem IntTy.i64.toUnsigned b).val = b.val := by rw [hx]; omega
  obtain ⟨x, hxdef⟩ : ∃ x, x = (JInt.rem IntTy.i64.toUnsigned b).val.toNat := ⟨_, rfl⟩
  rw [← hxdef] at hone
  have hxb : (x : Int) = b.val := by rw [hxdef, hx']; omega
  have hxlt : x < 2 ^ 64 := by omega
  obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hone
  have hmem : ∀ j, (j < 64 ∧ x / 2 ^ j % 2 = 1) ↔ j = k := by
    intro j
    have := congrArg (j ∈ ·) hk
    simp only [List.mem_filter, List.mem_range, List.mem_singleton, IntTy.bits,
      decide_eq_true_eq, eq_iff_iff] at this
    exact this
  have hk64 := ((hmem k).mpr rfl).1
  have htz : JuliaLean.IntArith.PowersDigits.trailingZeros b = k := by
    unfold JuliaLean.IntArith.PowersDigits.trailingZeros
    rw [← hxdef]
    cases hf : (List.range IntTy.i64.bits).find? (fun j => decide (x / 2 ^ j % 2 = 1)) with
    | none =>
      have := List.find?_eq_none.mp hf k (by simp [IntTy.bits, hk64])
      simp [((hmem k).mpr rfl).2] at this
    | some j =>
      have hp := List.find?_some hf
      have hj := List.mem_of_find?_eq_some hf
      simp only [List.mem_range, IntTy.bits, decide_eq_true_eq] at hp hj
      simp only [Option.getD_some]
      exact (hmem j).mp ⟨hj, hp⟩
  rw [htz, ← hxb]
  have hpow : x = 2 ^ k := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_two_pow, Nat.testBit_eq_decide_div_mod_eq]
    by_cases hi : i < 64
    · by_cases hik : k = i
      · subst hik; simp [((hmem k).mpr rfl).2]
      · have : ¬ x / 2 ^ i % 2 = 1 := fun h => hik ((hmem i).mp ⟨hi, h⟩).symm
        simp [this, hik]
    · have hlt : x < 2 ^ i := Nat.lt_of_lt_of_le hxlt (Nat.pow_le_pow_right (by decide) (by omega))
      have : x / 2 ^ i = 0 := Nat.div_eq_of_lt hlt
      have hik : k ≠ i := by omega
      simp [this, hik]
  rw [hpow]
  simp

/-- `digits!(a, n; base)` fills `a` with the `length(a)` least significant digits of
`n` (`base/intfuncs.jl:1224-1228`): the digits are below `|base|` in magnitude
(nonnegative for a negative base), and their value `sum(a[k] * base^(k-1))` is
congruent to `n` modulo `base^length(a)`. -/
def DigitsFillLowOrder : Prop := ∀ (t : IntTy) (n : JInt t) (b : JInt .i64) (L : Nat) (ds : List Int),
  digitsFill L n b = .ok ds →
  ds.length = L ∧ (∃ q, horner b.val ds + b.val ^ L * q = n.val) ∧
    ∀ d ∈ ds, d.natAbs < b.val.natAbs ∧ (b.val < 0 → 0 ≤ d)

theorem digitsFillLowOrder : DigitsFillLowOrder := by
  intro t n b L ds h
  unfold digitsFill at h
  by_cases hab : ¬ 2 ≤ (if b.val < 0 then -b else b).val
  · simp only [hab] at h
    cases h
  simp only [hab, ite_false] at h
  by_cases hL : L = 0
  · subst hL
    simp only [ite_true] at h
    cases h
    exact ⟨rfl, ⟨n.val, by simp [horner]⟩, by simp⟩
  simp only [hL, ite_false] at h
  by_cases hpos : b.val > 0
  · simp only [hpos, ite_true] at h
    have hdiv : ds = divremDigits b.val L n.val := by
      by_cases hp : JuliaLean.IntArith.PowersDigits.ispow2 b = true ∧ n.val ≥ 0
      · simp only [hp, and_self, ite_true] at h
        cases h
        rw [pow2_of_ispow2 b hp.1]
        exact pow2Digits_eq _ L n.val hp.2
      · simp only [hp, ite_false] at h
        cases h; rfl
    subst hdiv
    obtain ⟨q, hq, hl, hd⟩ := divremDigits_inv b.val hpos L n.val
    exact ⟨hl, ⟨q, hq⟩, fun d hdm => ⟨hd d hdm, fun hneg => absurd hneg (by omega)⟩⟩
  · simp only [hpos, ite_false] at h
    cases h
    have hbneg : b.val < 0 := by
      by_cases h0 : b.val < 0
      · exact h0
      · simp only [h0, ite_false] at hab
        omega
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    obtain ⟨q, hq, hl, hd⟩ := negDigits_inv b.val hbneg (L' + 1) n.val
    simp only [negDigits, Nat.add_sub_cancel] at hq hl hd ⊢
    refine ⟨hl, ⟨q, hq⟩, fun d hdm => ?_⟩
    obtain ⟨h1, h2⟩ := hd d hdm
    exact ⟨by omega, fun _ => h1⟩

end JuliaLean.ParsePrint.IntPrint
