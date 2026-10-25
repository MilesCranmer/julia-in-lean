import JuliaLean.Promotion.Compare

/-!
Julia's `==`, `<` and `<=` between an `IEEEFloat` and a `BitInteger` of at most 32 bits compare
the exact mathematical values. Each such comparison converts the integer exactly into a format
at least as wide as the float, possibly after widening the float, and then compares two values of
one format.
-/

namespace JuliaLean.Promotion

open JuliaLean.Float

/-- Exact mathematical comparison of a float with an integer: `-1`, `0`, `1` for less, equal,
greater; NaN gives `none`. -/
def exactOrder {f : Fmt} (x : Fl f) (y : Int) : Option Int :=
  if x.isnan then none
  else if x.isinf then some (if x.signbit then -1 else 1)
  else
    let r := x.toRat
    some (if r.1 < y * r.2 then -1 else if r.1 = y * r.2 then 0 else 1)

/-- `==`, `<`, `<=` between every IEEE float type and every integer type of at most 32 bits
compare the mathematical values, in both argument orders; NaN compares false. -/
def MixedCompareSmall : Prop := ∀ (T : FTy) (t : IntTy) (x : FV T) (y : JInt t), t.bits ≤ 32 →
  cmpFI .eq x y = (exactOrder x y.val == some 0) ∧
  cmpFI .lt x y = (exactOrder x y.val == some (-1)) ∧
  cmpFI .le x y = (exactOrder x y.val == some (-1) || exactOrder x y.val == some 0) ∧
  cmpIF .lt y x = (exactOrder x y.val == some 1) ∧
  cmpIF .le y x = (exactOrder x y.val == some 1 || exactOrder x y.val == some 0)

/-- Shape facts shared by `half`, `single` and `double`. -/
structure Fmt.Good (f : Fmt) : Prop where
  emax_eq : f.emax = 2 * f.bias + 1
  emax_succ : f.emax + 1 = 2 ^ f.eb
  bias_pos : 1 ≤ f.bias
  sb_pos : 1 ≤ f.sb
  sb_le : f.sb ≤ f.bias

theorem good_half : half.Good := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem good_single : single.Good := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem good_double : double.Good := ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- `2^(bias+sb-1)`, the reciprocal of the smallest subnormal. -/
def Fmt.den (f : Fmt) : Nat := 2 ^ (f.bias + f.sb - 1)

theorem Fmt.den_pos (f : Fmt) : 0 < f.den := Nat.two_pow_pos _

theorem Fmt.width_pow (f : Fmt) : 2 ^ f.width = 2 * 2 ^ (f.eb + f.sb) := by
  rw [Fmt.width, show 1 + f.eb + f.sb = f.eb + f.sb + 1 by omega, Nat.pow_succ, Nat.mul_comm]

theorem pow_mul_eq (m a b c d : Nat) (h : a + b = c + d) : m * 2 ^ a * 2 ^ b = m * 2 ^ c * 2 ^ d := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, h]

/-! ### Magnitude keys -/

/-- The magnitude bits `M` as the integer `|value| * 2^(bias+sb-1)`. -/
def magKey (f : Fmt) (M : Nat) : Nat :=
  (M % 2 ^ f.sb + if M / 2 ^ f.sb = 0 then 0 else 2 ^ f.sb) * 2 ^ (M / 2 ^ f.sb - 1)

theorem magKey_zero (f : Fmt) : magKey f 0 = 0 := by simp [magKey]

theorem magKey_lt (f : Fmt) (M : Nat) : magKey f M < 2 ^ f.sb * 2 ^ (M / 2 ^ f.sb) := by
  have hr := Nat.mod_lt M (Nat.two_pow_pos f.sb)
  unfold magKey
  generalize M / 2 ^ f.sb = e
  generalize M % 2 ^ f.sb = r at hr
  generalize 2 ^ f.sb = P at *
  cases e with
  | zero => simpa using hr
  | succ e =>
    have hq := Nat.two_pow_pos e
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Nat.pow_succ]
    have h1 : (r + P) * 2 ^ e < (P + P) * 2 ^ e := (Nat.mul_lt_mul_right hq).2 (by omega)
    have h2 : (P + P) * 2 ^ e = P * (2 ^ e * 2) := by
      rw [← Nat.two_mul, Nat.mul_comm 2 P, Nat.mul_assoc, Nat.mul_comm 2]
    omega

theorem magKey_ge (f : Fmt) (M : Nat) (h : M / 2 ^ f.sb ≠ 0) :
    2 ^ f.sb * 2 ^ (M / 2 ^ f.sb - 1) ≤ magKey f M := by
  unfold magKey
  rw [if_neg h]
  exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

theorem magKey_strictMono (f : Fmt) {a b : Nat} (h : a < b) : magKey f a < magKey f b := by
  have hab : a / 2 ^ f.sb ≤ b / 2 ^ f.sb := Nat.div_le_div_right (Nat.le_of_lt h)
  rcases Nat.lt_or_eq_of_le hab with hlt | heq
  · have h1 := magKey_lt f a
    have h2 := magKey_ge f b (Nat.pos_iff_ne_zero.1 (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt))
    have h3 : 2 ^ (a / 2 ^ f.sb) ≤ 2 ^ (b / 2 ^ f.sb - 1) :=
      Nat.pow_le_pow_right (by decide) (Nat.le_sub_one_of_lt hlt)
    have h4 := Nat.mul_le_mul_left (2 ^ f.sb) h3
    exact Nat.lt_of_lt_of_le h1 (Nat.le_trans h4 h2)
  · have ha := Nat.div_add_mod a (2 ^ f.sb)
    have hb := Nat.div_add_mod b (2 ^ f.sb)
    rw [heq] at ha
    have hr : a % 2 ^ f.sb < b % 2 ^ f.sb := by omega
    unfold magKey
    rw [heq]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 (by omega)

theorem magKey_cases (f : Fmt) (a : Nat) :
    (a = 0 ∧ magKey f a = 0) ∨ (0 < a ∧ 0 < magKey f a) := by
  rcases Nat.eq_zero_or_pos a with h | h
  · exact Or.inl ⟨h, h ▸ magKey_zero f⟩
  · exact Or.inr ⟨h, magKey_zero f ▸ magKey_strictMono f h⟩

/-- Three-way comparison as in `exactOrder`. -/
def cmpInt (a b : Int) : Int :=
  if a < b then -1 else if a = b then 0 else 1

namespace Fl

variable {f g : Fmt}

/-! ### Bit-level structure -/

theorem toBits_ofBits (v : Nat) : (ofBits v : Fl f).toBits = v % 2 ^ f.width := rfl

theorem ofBits_toBits (x : Fl f) : ofBits x.toBits = x := by
  obtain ⟨⟨v, hv⟩⟩ := x
  simp only [ofBits, toBits, Nat.mod_eq_of_lt hv]

theorem bits_split (x : Fl f) :
    x.toBits = (if x.signbit then 2 ^ (f.eb + f.sb) else 0) + x.magnitude ∧
    x.magnitude < 2 ^ (f.eb + f.sb) := by
  have h : x.toBits < 2 * 2 ^ (f.eb + f.sb) := by
    have h1 := x.bits.isLt
    have h2 := Fmt.width_pow f
    have h3 : x.toBits = x.bits.val := rfl
    omega
  have hW := Nat.two_pow_pos (f.eb + f.sb)
  refine ⟨?_, Nat.mod_lt _ hW⟩
  unfold signbit magnitude
  by_cases hs : x.toBits ≥ 2 ^ (f.eb + f.sb)
  · rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega)]
    simp only [hs, decide_true, ↓reduceIte]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp [hs]

theorem expField_eq (x : Fl f) : x.expField = x.magnitude / 2 ^ f.sb := by
  unfold expField magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_div_self]

theorem frac_eq (x : Fl f) : x.frac = x.magnitude % 2 ^ f.sb := by
  unfold frac magnitude
  rw [Nat.add_comm f.eb f.sb, Nat.pow_add, Nat.mod_mul_right_mod]

/-- The value with sign `neg`, raw exponent `B` and stored fraction `r`. -/
def pack (neg : Bool) (B r : Nat) : Fl f :=
  ofBits ((if neg then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r))

theorem pack_parts (neg : Bool) (B r : Nat) (hB : B < 2 ^ f.eb) (hr : r < 2 ^ f.sb) :
    (pack neg B r : Fl f).signbit = neg ∧ (pack neg B r : Fl f).expField = B ∧
    (pack neg B r : Fl f).frac = r ∧ (pack neg B r : Fl f).magnitude = B * 2 ^ f.sb + r := by
  have hP := Nat.two_pow_pos f.sb
  have hM : B * 2 ^ f.sb + r < 2 ^ (f.eb + f.sb) := by
    rw [Nat.pow_add]
    have : (B + 1) * 2 ^ f.sb ≤ 2 ^ f.eb * 2 ^ f.sb := Nat.mul_le_mul_right _ hB
    rw [Nat.succ_mul] at this
    omega
  have hw := Fmt.width_pow f
  have ht : (pack neg B r : Fl f).toBits =
      (if neg then 2 ^ (f.eb + f.sb) else 0) + (B * 2 ^ f.sb + r) := by
    unfold pack
    rw [toBits_ofBits, Nat.mod_eq_of_lt]
    rw [hw]
    cases neg <;> simp <;> omega
  have hm : (pack neg B r : Fl f).magnitude = B * 2 ^ f.sb + r := by
    unfold magnitude
    rw [ht]
    cases neg <;> simp [Nat.mod_eq_of_lt hM]
  refine ⟨?_, ?_, ?_, hm⟩
  · unfold signbit
    rw [ht]
    cases neg <;> simp <;> omega
  · rw [expField_eq, hm, Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr,
      Nat.zero_add]
  · rw [frac_eq, hm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-! ### Order and keys -/

/-- The value times `2^(bias+sb-1)`, with infinities beyond every finite value. -/
def key (x : Fl f) : Int :=
  if x.signbit then -((magKey f x.magnitude : Nat) : Int) else ((magKey f x.magnitude : Nat) : Int)

theorem lt_key {x y : Fl f} (hx : x.isnan = false) (hy : y.isnan = false) :
    Fl.lt x y = decide (x.key < y.key) := by
  obtain ⟨bx, mx⟩ := bits_split x
  obtain ⟨by', my⟩ := bits_split y
  unfold Fl.lt key iszero
  rw [hx, hy, bx, by']
  generalize x.magnitude = a at *
  generalize y.magnitude = b at *
  generalize x.signbit = s
  generalize y.signbit = t
  have pa := magKey_cases f a
  have pb := magKey_cases f b
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := magKey_strictMono f h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega
  · subst h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega
  · have := magKey_strictMono f h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem eq_key {x y : Fl f} (hx : x.isnan = false) (hy : y.isnan = false) :
    Fl.eq x y = decide (x.key = y.key) := by
  obtain ⟨bx, mx⟩ := bits_split x
  obtain ⟨by', my⟩ := bits_split y
  unfold Fl.eq key iszero
  rw [hx, hy, bx, by']
  generalize x.magnitude = a at *
  generalize y.magnitude = b at *
  generalize x.signbit = s
  generalize y.signbit = t
  have pa := magKey_cases f a
  have pb := magKey_cases f b
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := magKey_strictMono f h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega
  · subst h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega
  · have := magKey_strictMono f h
    cases s <;> cases t <;> rw [Bool.eq_iff_iff] <;> simp <;> omega

theorem isnan_of_finite {x : Fl f} (h : x.isfinite = true) : x.isnan = false := by
  simp_all [isfinite, isnan]

theorem isinf_of_finite {x : Fl f} (h : x.isfinite = true) : x.isinf = false := by
  simp_all [isfinite, isinf]

/-- Every finite value is `±m * 2^i / 2^j` with `m` of at most `sb+1` bits, and its key is the
value times `2^(bias+sb-1)`. -/
theorem toRat_cases (hf : f.Good) (x : Fl f) (hx : x.isfinite = true) : ∃ m i j : Nat,
    x.toRat = ((if x.signbit then -((m * 2 ^ i : Nat) : Int) else ((m * 2 ^ i : Nat) : Int)),
      2 ^ j) ∧
    magKey f x.magnitude * 2 ^ j = m * 2 ^ i * f.den ∧ m < 2 ^ (f.sb + 1) ∧
    (m ≠ 0 → j + 1 ≤ m.log2 + i + f.bias + f.sb ∧ m.log2 + i ≤ j + f.bias) := by
  have hP := Nat.two_pow_pos f.sb
  have hb := hf.bias_pos
  have hs := hf.sb_pos
  have hE := hf.emax_eq
  have hS := hf.emax_succ
  have hM := (bits_split x).2
  have hfin : x.magnitude / 2 ^ f.sb ≠ f.emax := by
    have := hx
    simp only [isfinite, bne_iff_ne, ne_eq] at this
    rw [expField_eq] at this
    exact this
  have hdiv : x.magnitude / 2 ^ f.sb < 2 ^ f.eb := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, Nat.add_comm]
    exact hM
  have hr := Nat.mod_lt x.magnitude hP
  have hpow : 2 ^ (f.sb + 1) = 2 * 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold toRat magKey Fmt.den
  rw [expField_eq, frac_eq]
  simp only [hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  generalize x.signbit = s
  generalize x.magnitude / 2 ^ f.sb = e at *
  generalize x.magnitude % 2 ^ f.sb = r at *
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    refine ⟨r, 0, f.bias + f.sb - 1, ?_, ?_, by omega, ?_⟩
    · simp only [↓reduceIte, Nat.add_zero]
      split
      · exfalso; omega
      · refine Prod.ext ?_ ?_
        · cases s <;> simp
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
    · simp
    · intro hr0
      have : r.log2 < f.sb := (Nat.log2_lt hr0).2 hr
      omega
  · have he0 : e ≠ 0 := by omega
    have hne : r + 2 ^ f.sb ≠ 0 := by omega
    have hl1 : (r + 2 ^ f.sb).log2 < f.sb + 1 := (Nat.log2_lt hne).2 (by omega)
    have hl2 : f.sb ≤ (r + 2 ^ f.sb).log2 := (Nat.le_log2 hne).2 (by omega)
    simp only [he0, ↓reduceIte]
    split
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, e - f.bias - f.sb, 0, ?_, ?_, by omega, fun _ => by omega⟩
      · have ht : ((e : Int) - f.bias - f.sb).toNat = e - f.bias - f.sb := by omega
        rw [ht]
        refine Prod.ext ?_ rfl
        cases s <;> simp [Int.natCast_mul, Int.neg_mul]
      · rw [Nat.mul_one]
        conv => lhs; rw [← Nat.mul_one ((r + 2 ^ f.sb) * 2 ^ (e - 1))]
        rw [show (1 : Nat) = 2 ^ 0 from rfl]
        exact pow_mul_eq _ _ _ _ _ (by omega)
    · rename_i hp
      refine ⟨r + 2 ^ f.sb, 0, f.bias + f.sb - e, ?_, ?_, by omega, fun _ => by omega⟩
      · refine Prod.ext ?_ ?_
        · cases s <;> simp
        · show 2 ^ _ = 2 ^ _
          congr 1
          omega
      · exact pow_mul_eq _ _ _ _ _ (by omega)

theorem toRat_key (hf : f.Good) (x : Fl f) (hx : x.isfinite = true) :
    0 < x.toRat.2 ∧ x.toRat.1 * (f.den : Int) = x.key * (x.toRat.2 : Int) := by
  obtain ⟨m, i, j, hr, hk, -, -⟩ := toRat_cases hf x hx
  rw [hr]
  refine ⟨Nat.two_pow_pos j, ?_⟩
  unfold key
  dsimp only
  cases x.signbit <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Int.neg_mul, ← Int.natCast_mul, hk]

/-! ### Exact order through keys -/

theorem cmpInt_scale {a b c d : Int} (hc : 0 < c) (hd : 0 < d) (h : a * c = b * d) (y : Int) :
    cmpInt a (y * d) = cmpInt b (y * c) := by
  have h1 : a < y * d ↔ b < y * c := by
    rw [← Int.mul_lt_mul_right hc, h, Int.mul_right_comm y d c, Int.mul_lt_mul_right hd]
  have h2 : a = y * d ↔ b = y * c := by
    rw [← Int.mul_eq_mul_right_iff (by omega : c ≠ 0), h, Int.mul_right_comm y d c,
      Int.mul_eq_mul_right_iff (by omega : d ≠ 0)]
  unfold cmpInt
  simp only [h1, h2]

theorem exactOrder_finite (hf : f.Good) (x : Fl f) (hx : x.isfinite = true) (y : Int) :
    exactOrder x y = some (cmpInt x.key (y * f.den)) := by
  obtain ⟨h0, h1⟩ := toRat_key hf x hx
  unfold exactOrder
  simp only [isnan_of_finite hx, isinf_of_finite hx, Bool.false_eq_true, ↓reduceIte]
  rw [← cmpInt_scale (by exact_mod_cast f.den_pos) (by exact_mod_cast h0) h1 y]
  rfl

theorem exactOrder_key (hf : f.Good) (x : Fl f) (hx : x.isnan = false) (y : Int)
    (hy : y.natAbs < 2 ^ (f.bias + 1)) : exactOrder x y = some (cmpInt x.key (y * f.den)) := by
  cases hfin : x.isfinite
  · have he : x.expField = f.emax := by simpa [isfinite] using hfin
    have hr : x.frac = 0 := by simpa [isnan, he] using hx
    have hinf : x.isinf = true := by simp [isinf, he, hr]
    have hK : magKey f x.magnitude = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
      unfold magKey
      rw [← expField_eq, ← frac_eq, he, hr, if_neg (by have := hf.emax_eq; omega), Nat.zero_add]
    have hbound : y.natAbs * f.den < 2 ^ f.sb * 2 ^ (f.emax - 1) := by
      calc y.natAbs * f.den < 2 ^ (f.bias + 1) * f.den :=
            (Nat.mul_lt_mul_right f.den_pos).2 hy
        _ = 2 ^ f.sb * 2 ^ (f.emax - 1) := by
          unfold Fmt.den
          rw [← Nat.pow_add, ← Nat.pow_add]
          congr 1
          have := hf.emax_eq
          have := hf.sb_pos
          omega
    have hyD : (y * (f.den : Int)).natAbs < 2 ^ f.sb * 2 ^ (f.emax - 1) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      exact hbound
    unfold exactOrder key cmpInt
    rw [hK]
    simp only [hx, hinf, Bool.false_eq_true, ↓reduceIte]
    generalize y * (f.den : Int) = w at hyD
    generalize 2 ^ f.sb * 2 ^ (f.emax - 1) = K at hyD
    cases x.signbit <;> simp <;> omega
  · exact exactOrder_finite hf x hfin y

/-! ### Rounding of exactly representable values -/

theorem log2_mul_pow (c i : Nat) (hc : c ≠ 0) : (c * 2 ^ i).log2 = c.log2 + i := by
  have hne : c * 2 ^ i ≠ 0 := Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  apply Nat.le_antisymm
  · have : c * 2 ^ i < 2 ^ (c.log2 + i + 1) := by
      rw [show c.log2 + i + 1 = (c.log2 + 1) + i by omega, Nat.pow_add]
      exact (Nat.mul_lt_mul_right (Nat.two_pow_pos i)).2 Nat.lt_log2_self
    have := (Nat.log2_lt hne).2 this
    omega
  · apply (Nat.le_log2 hne).2
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le hc)

theorem floorLog2Rat_pow (a j : Nat) (ha : a ≠ 0) :
    floorLog2Rat a (2 ^ j) = (a.log2 : Int) - j := by
  have h1 := Nat.log2_self_le ha
  unfold floorLog2Rat
  simp only [Nat.log2_two_pow]
  split
  · rename_i hge
    have : 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat = 2 ^ a.log2 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hc : ¬ a < 2 ^ j * 2 ^ ((a.log2 : Int) - j).toNat := by omega
    split
    · contradiction
    · rfl
  · rename_i hlt
    have : 2 ^ a.log2 * 2 ^ (-((a.log2 : Int) - j)).toNat = 2 ^ j := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have := Nat.mul_le_mul_right (2 ^ (-((a.log2 : Int) - j)).toNat) h1
    have hc : ¬ a * 2 ^ (-((a.log2 : Int) - j)).toNat < 2 ^ j := by omega
    split
    · contradiction
    · rfl

theorem roundQuotient_exact (q d : Nat) (hd : 0 < d) : roundQuotient (q * d) d = q := by
  unfold roundQuotient
  rw [Nat.mul_div_cancel _ hd, Nat.mul_mod_left]
  dsimp only
  split
  · rename_i h
    simp at h <;> omega
  · rfl

theorem packRounded_normal (neg : Bool) (q : Nat) (k : Int) (h1 : 2 ^ f.sb ≤ q)
    (h2 : q < 2 ^ (f.sb + 1)) (hk2 : k + f.bias + f.sb < f.emax) :
    (packRounded neg q k : Fl f) = pack neg (k + f.bias + f.sb).toNat (q - 2 ^ f.sb) := by
  have hP := Nat.two_pow_pos f.sb
  have hq0 : (q == 0) = false := by simp; omega
  have hc : ¬ q ≥ 2 ^ (f.sb + 1) := by omega
  have he : ¬ k + f.bias + f.sb ≥ (f.emax : Int) := by omega
  have hm : ¬ q < 2 ^ f.sb := by omega
  unfold packRounded pack
  simp only [hq0, hc, he, hm, Bool.false_eq_true, ↓reduceIte]

theorem sig_bounds (c : Nat) (hc : c ≠ 0) (hc1 : c < 2 ^ (f.sb + 1)) :
    c.log2 ≤ f.sb ∧ 2 ^ f.sb ≤ c * 2 ^ (f.sb - c.log2) ∧
    c * 2 ^ (f.sb - c.log2) < 2 ^ (f.sb + 1) := by
  have hlc : c.log2 ≤ f.sb := by have := (Nat.log2_lt hc).2 hc1; omega
  refine ⟨hlc, ?_, ?_⟩
  · calc 2 ^ f.sb = 2 ^ c.log2 * 2 ^ (f.sb - c.log2) := by
          rw [← Nat.pow_add]
          congr 1
          omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.log2_self_le hc)
  · calc c * 2 ^ (f.sb - c.log2) < 2 ^ (c.log2 + 1) * 2 ^ (f.sb - c.log2) :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 Nat.lt_log2_self
      _ = 2 ^ (f.sb + 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega

theorem roundRat_normal (hf : f.Good) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f) =
      pack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := sig_bounds (f := f) c hc hc1
  have ha : n.natAbs ≠ 0 := by
    rw [hn]
    exact Nat.mul_ne_zero hc (by have := Nat.two_pow_pos i; omega)
  have hn0 : (n == 0) = false := by simp; omega
  have hd : (2 ^ j == 0) = false := by simp
  have hE : floorLog2Rat n.natAbs (2 ^ j) = ((c.log2 + i : Nat) : Int) - j := by
    rw [floorLog2Rat_pow _ _ ha, hn, log2_mul_pow c i hc]
  have hb := hf.bias_pos
  have hem := hf.emax_eq
  have hs := hf.sb_pos
  unfold roundRat
  simp only [hd, hn0, Bool.false_eq_true, ↓reduceIte]
  generalize floorLog2Rat n.natAbs (2 ^ j) = e at hE
  split
  · exfalso; omega
  split
  · exfalso; omega
  have hk : max (e - f.sb) (1 - (f.bias : Int) - f.sb) = e - f.sb := by omega
  rw [hk]
  have hpack : ∀ q : Nat, q = c * 2 ^ (f.sb - c.log2) →
      (packRounded (decide (n < 0)) q (e - f.sb) : Fl f) =
        pack (decide (n < 0)) (c.log2 + i + f.bias - j) (c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb) := by
    intro q hq
    subst hq
    rw [packRounded_normal _ _ _ hq1 hq2 (by omega)]
    congr 1
    omega
  apply hpack
  by_cases hk0 : e - (f.sb : Int) ≥ 0
  · rw [if_pos hk0]
    dsimp only
    have h1 : n.natAbs = c * 2 ^ (f.sb - c.log2) * (2 ^ j * 2 ^ (e - f.sb).toNat) := by
      rw [hn, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
      congr 2
      omega
    rw [h1, roundQuotient_exact _ _ (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))]
  · rw [if_neg hk0]
    dsimp only
    have h1 : n.natAbs * 2 ^ (-(e - f.sb)).toNat = c * 2 ^ (f.sb - c.log2) * 2 ^ j := by
      rw [hn]
      exact pow_mul_eq _ _ _ _ _ (by omega)
    rw [h1, roundQuotient_exact _ _ (Nat.two_pow_pos _)]

theorem pack_key (neg : Bool) (B r : Nat) (hB : B < 2 ^ f.eb) (hr : r < 2 ^ f.sb) :
    (pack neg B r : Fl f).key = if neg then
      -(((r + if B = 0 then 0 else 2 ^ f.sb) * 2 ^ (B - 1) : Nat) : Int)
      else (((r + if B = 0 then 0 else 2 ^ f.sb) * 2 ^ (B - 1) : Nat) : Int) := by
  obtain ⟨hs, he, hfr, -⟩ := pack_parts (f := f) neg B r hB hr
  unfold key magKey
  rw [← expField_eq, ← frac_eq, hs, he, hfr]

theorem roundRat_key (hf : f.Good) (n : Int) (c i j : Nat) (z : Bool)
    (hn : n.natAbs = c * 2 ^ i) (hc0 : 1 ≤ c) (hc1 : c < 2 ^ (f.sb + 1))
    (hlo : j + 1 ≤ c.log2 + i + f.bias) (hhi : c.log2 + i + f.bias < j + f.emax) :
    (roundRat n (2 ^ j) z : Fl f).isfinite = true ∧
    (roundRat n (2 ^ j) z : Fl f).key * ((2 ^ j : Nat) : Int) = n * (f.den : Int) := by
  have hc : c ≠ 0 := by omega
  obtain ⟨hlc, hq1, hq2⟩ := sig_bounds (f := f) c hc hc1
  have hem := hf.emax_eq
  have hS := hf.emax_succ
  have hpow : 2 ^ (f.sb + 1) = 2 * 2 ^ f.sb := by rw [Nat.pow_succ, Nat.mul_comm]
  have hB : c.log2 + i + f.bias - j < 2 ^ f.eb := by omega
  have hr : c * 2 ^ (f.sb - c.log2) - 2 ^ f.sb < 2 ^ f.sb := by
    generalize c * 2 ^ (f.sb - c.log2) = q at hq1 hq2 ⊢
    omega
  rw [roundRat_normal hf n c i j z hn hc0 hc1 hlo hhi]
  obtain ⟨-, he, -, -⟩ := pack_parts (f := f) (decide (n < 0)) _ _ hB hr
  refine ⟨by rw [isfinite, he, bne_iff_ne]; omega, ?_⟩
  rw [pack_key _ _ _ hB hr, if_neg (show ¬ (c.log2 + i + f.bias - j = 0) by omega),
    Nat.sub_add_cancel hq1]
  have hpow : c * 2 ^ (f.sb - c.log2) * 2 ^ (c.log2 + i + f.bias - j - 1) * 2 ^ j =
      c * 2 ^ i * f.den := by
    unfold Fmt.den
    simp only [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rcases Int.lt_or_le n 0 with hneg | hpos
  · have hn' : n = -((c * 2 ^ i : Nat) : Int) := by omega
    simp only [decide_eq_true hneg, ↓reduceIte]
    rw [hn', Int.neg_mul, Int.neg_mul, ← Int.natCast_mul, ← Int.natCast_mul, hpow]
  · have hn' : n = ((c * 2 ^ i : Nat) : Int) := by omega
    simp only [decide_eq_false (Int.not_lt.2 hpos), Bool.false_eq_true, ↓reduceIte]
    rw [hn', ← Int.natCast_mul, ← Int.natCast_mul, hpow]

theorem zero_spec (hf : f.Good) (s : Bool) :
    (zero s : Fl f).isfinite = true ∧ (zero s : Fl f).key = 0 := by
  have hz : (zero s : Fl f) = pack s 0 0 := by simp [zero, pack]
  have hS := hf.emax_succ
  have hE := hf.emax_eq
  obtain ⟨-, he, -, -⟩ := pack_parts (f := f) s 0 0 (by omega) (Nat.two_pow_pos _)
  rw [hz]
  refine ⟨by rw [isfinite, he, bne_iff_ne]; omega, ?_⟩
  rw [pack_key _ _ _ (by omega) (Nat.two_pow_pos _)]
  cases s <;> simp

theorem ofInt_key (hf : f.Good) (n : Int) (hn : n.natAbs < 2 ^ (f.sb + 1)) :
    (ofInt n : Fl f).isfinite = true ∧ (ofInt n : Fl f).key = n * (f.den : Int) := by
  by_cases h0 : n = 0
  · subst h0
    have : (ofInt 0 : Fl f) = zero false := by simp [ofInt, roundRat]
    rw [this]
    obtain ⟨h1, h2⟩ := zero_spec hf false
    exact ⟨h1, by rw [h2]; simp⟩
  · have hc : n.natAbs ≠ 0 := by omega
    have hlc := (sig_bounds (f := f) n.natAbs hc hn).1
    have := hf.sb_le
    have := hf.emax_eq
    have := hf.bias_pos
    obtain ⟨h1, h2⟩ := roundRat_key hf n n.natAbs 0 0 false (by simp) (by omega) hn
      (by omega) (by omega)
    refine ⟨h1, ?_⟩
    simpa [ofInt] using h2

/-! ### Widening conversion -/

theorem convert_exactOrder (hf : f.Good) (hg : g.Good) (hne : (g == f) = false)
    (hsb : f.sb ≤ g.sb) (hbias : f.bias + f.sb ≤ g.bias) (x : Fl f) (y : Int) :
    exactOrder (convert x : Fl g) y = exactOrder x y := by
  have hgS := hg.emax_succ
  have hgE := hg.emax_eq
  have hfE := hf.emax_eq
  have hPg := Nat.two_pow_pos g.sb
  unfold convert
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hn : x.isnan
  · cases hi : x.isinf
    · have hfin : x.isfinite = true := by
        simp_all [isnan, isinf, isfinite]
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨m, i, j, hr, hk, hm, hrange⟩ := toRat_cases hf x hfin
      have hkey := (toRat_key hf x hfin).2
      rw [exactOrder_finite hf x hfin]
      rw [hr]
      dsimp only
      rw [hr] at hkey
      dsimp only at hkey
      by_cases hm0 : m = 0
      · subst hm0
        have hz : (roundRat (if x.signbit then -((0 * 2 ^ i : Nat) : Int)
            else ((0 * 2 ^ i : Nat) : Int)) (2 ^ j) x.signbit : Fl g) = zero x.signbit := by
          cases x.signbit <;> simp [roundRat]
        rw [hz]
        obtain ⟨hz1, hz2⟩ := zero_spec hg x.signbit
        rw [exactOrder_finite hg _ hz1, hz2]
        have hkx : x.key = 0 := by
          have h2 : ((2 ^ j : Nat) : Int) ≠ 0 := by have := Nat.two_pow_pos j; omega
          have h3 : x.key * ((2 ^ j : Nat) : Int) = 0 := by
            rw [← hkey]
            cases x.signbit <;> simp
          exact (Int.mul_eq_zero.1 h3).resolve_right h2
        rw [hkx]
        congr 1
        unfold cmpInt
        have hDf : (0 : Int) < f.den := by exact_mod_cast f.den_pos
        have hDg : (0 : Int) < g.den := by exact_mod_cast g.den_pos
        rcases Int.lt_trichotomy y 0 with hy | hy | hy
        · have h1 : y * (g.den : Int) < 0 := Int.mul_neg_of_neg_of_pos hy hDg
          have h2 : y * (f.den : Int) < 0 := Int.mul_neg_of_neg_of_pos hy hDf
          simp only [show ¬ (0 : Int) < y * g.den by omega, show ¬ (0 : Int) < y * f.den by omega,
            show ¬ (0 : Int) = y * g.den by omega, show ¬ (0 : Int) = y * f.den by omega,
            ↓reduceIte]
        · subst hy
          simp
        · have h1 : 0 < y * (g.den : Int) := Int.mul_pos hy hDg
          have h2 : 0 < y * (f.den : Int) := Int.mul_pos hy hDf
          simp only [h1, h2, ↓reduceIte]
      · obtain ⟨hlo, hhi⟩ := hrange hm0
        have hn' : (if x.signbit then -((m * 2 ^ i : Nat) : Int)
            else ((m * 2 ^ i : Nat) : Int)).natAbs = m * 2 ^ i := by
          cases x.signbit <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg,
            Int.natAbs_natCast]
        have hm1 : m < 2 ^ (g.sb + 1) :=
          Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega))
        obtain ⟨h1, h2⟩ := roundRat_key (f := g) hg _ m i j x.signbit hn' (by omega) hm1
          (by omega) (by omega)
        rw [exactOrder_finite hg _ h1]
        congr 1
        have hj : (0 : Int) < ((2 ^ j : Nat) : Int) := by exact_mod_cast Nat.two_pow_pos j
        have hDf : (0 : Int) < f.den := by exact_mod_cast f.den_pos
        have hDg : (0 : Int) < g.den := by exact_mod_cast g.den_pos
        generalize (if x.signbit then -((m * 2 ^ i : Nat) : Int)
            else ((m * 2 ^ i : Nat) : Int)) = N at h2 hkey
        generalize (roundRat N (2 ^ j) x.signbit : Fl g).key = K at h2
        have hscale : K * f.den = x.key * g.den := by
          apply Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hj)
          calc K * f.den * ((2 ^ j : Nat) : Int) = K * ((2 ^ j : Nat) : Int) * f.den := by
                rw [Int.mul_right_comm]
            _ = N * g.den * f.den := by rw [h2]
            _ = N * f.den * g.den := by rw [Int.mul_right_comm]
            _ = x.key * ((2 ^ j : Nat) : Int) * g.den := by rw [hkey]
            _ = x.key * g.den * ((2 ^ j : Nat) : Int) := by rw [Int.mul_right_comm]
        exact cmpInt_scale hDf hDg hscale y
    · have hinf : (inf x.signbit : Fl g) = pack x.signbit g.emax 0 := by simp [inf, pack]
      obtain ⟨hs, he, hfr, -⟩ := pack_parts (f := g) x.signbit g.emax 0 (by omega) hPg
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hinf]
      unfold exactOrder
      have hpn : (pack x.signbit g.emax 0 : Fl g).isnan = false := by
        unfold isnan
        rw [he, hfr]
        simp
      have hpi : (pack x.signbit g.emax 0 : Fl g).isinf = true := by
        unfold isinf
        rw [he, hfr]
        simp
      simp only [hpn, hpi, hs, hn, hi, Bool.false_eq_true, ↓reduceIte]
  · have hfr : x.frac < 2 ^ f.sb := by rw [frac_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hpay : x.frac * 2 ^ (g.sb - f.sb) < 2 ^ g.sb := by
      calc x.frac * 2 ^ (g.sb - f.sb) < 2 ^ f.sb * 2 ^ (g.sb - f.sb) :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).2 hfr
        _ = 2 ^ g.sb := by rw [← Nat.pow_add]; congr 1; omega
    have hhalf : 2 ^ (g.sb - 1) < 2 ^ g.sb :=
      Nat.pow_lt_pow_right (by decide) (by have := hg.sb_pos; omega)
    have hL : Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1)) < 2 ^ g.sb :=
      Nat.or_lt_two_pow hpay hhalf
    have hpk : (ofBits ((if x.signbit then 2 ^ (g.eb + g.sb) else 0) + g.emax * 2 ^ g.sb +
        Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) : Fl g) =
        pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) := by
      unfold pack
      rw [Nat.add_assoc]
    obtain ⟨-, he, hfr', -⟩ := pack_parts (f := g) x.signbit g.emax _ (by omega) hL
    simp only [↓reduceIte, if_pos hsb]
    rw [hpk]
    unfold exactOrder
    have hpn : (pack x.signbit g.emax (Nat.lor (x.frac * 2 ^ (g.sb - f.sb)) (2 ^ (g.sb - 1))) :
        Fl g).isnan = true := by
      unfold isnan
      rw [he, hfr']
      simp
    simp only [hpn, hn, ↓reduceIte]

/-! ### Comparisons in one format -/

theorem compare_core (hg : g.Good) (a z : Fl g) (y : Int) (hz : z.isfinite = true)
    (hkz : z.key = y * (g.den : Int)) (hy : y.natAbs < 2 ^ (g.bias + 1)) :
    Fl.eq a z = (exactOrder a y == some 0) ∧ Fl.lt a z = (exactOrder a y == some (-1)) ∧
    Fl.le a z = (exactOrder a y == some (-1) || exactOrder a y == some 0) ∧
    Fl.lt z a = (exactOrder a y == some 1) ∧
    Fl.le z a = (exactOrder a y == some 1 || exactOrder a y == some 0) := by
  have hzn := isnan_of_finite hz
  cases ha : a.isnan
  · rw [exactOrder_key hg a ha y hy]
    simp only [Fl.le, lt_key ha hzn, lt_key hzn ha, eq_key ha hzn, eq_key hzn ha, hkz]
    unfold cmpInt
    generalize a.key = k
    generalize y * (g.den : Int) = w
    by_cases h1 : k < w <;> by_cases h2 : k = w <;> simp [h1, h2] <;> omega
  · have hnone : exactOrder a y = none := by simp [exactOrder, ha]
    simp [hnone, Fl.le, Fl.lt, Fl.eq, ha, hzn]

theorem cmp_promote (hg : g.Good) (x : Fl g) (y : Int) (h1 : y.natAbs < 2 ^ (g.sb + 1))
    (h2 : y.natAbs < 2 ^ (g.bias + 1)) :
    Fl.eq x (ofInt y) = (exactOrder x y == some 0) ∧
    Fl.lt x (ofInt y) = (exactOrder x y == some (-1)) ∧
    Fl.le x (ofInt y) = (exactOrder x y == some (-1) || exactOrder x y == some 0) ∧
    Fl.lt (ofInt y) x = (exactOrder x y == some 1) ∧
    Fl.le (ofInt y) x = (exactOrder x y == some 1 || exactOrder x y == some 0) := by
  obtain ⟨hz, hk⟩ := ofInt_key hg y h1
  exact compare_core hg x _ y hz hk h2

theorem cmp_via (hf : f.Good) (hg : g.Good) (hne : (g == f) = false) (hsb : f.sb ≤ g.sb)
    (hbias : f.bias + f.sb ≤ g.bias) (x : Fl f) (y : Int) (h1 : y.natAbs < 2 ^ (g.sb + 1))
    (h2 : y.natAbs < 2 ^ (g.bias + 1)) :
    Fl.eq (convert x : Fl g) (ofInt y) = (exactOrder x y == some 0) ∧
    Fl.lt (convert x : Fl g) (ofInt y) = (exactOrder x y == some (-1)) ∧
    Fl.le (convert x : Fl g) (ofInt y) = (exactOrder x y == some (-1) || exactOrder x y == some 0) ∧
    Fl.lt (ofInt y) (convert x : Fl g) = (exactOrder x y == some 1) ∧
    Fl.le (ofInt y) (convert x : Fl g) = (exactOrder x y == some 1 || exactOrder x y == some 0) := by
  rw [← convert_exactOrder hf hg hne hsb hbias x y]
  exact cmp_promote hg _ y h1 h2

end Fl

/-! ### The shared binary64 model -/

/-- `F64.packRounded` (`JuliaLean/Float/Basic.lean`), restated. -/
def f64Pack (negative : Bool) (q : Nat) (k : Int) : F64 :=
  if q == 0 then F64.zero negative
  else
    let carry := q ≥ 2^53
    let m := if carry then q / 2 else q
    let p := if carry then k + 1 else k
    let exponent := p + 1075
    if exponent ≥ 2047 then F64.inf negative
    else
      let magnitude :=
        if m < 2^52 then m
        else exponent.toNat * 2^52 + (m - 2^52)
      F64.ofBits ((if negative then 2^63 else 0) + magnitude)

theorem f64_roundRat_eq (n : Int) (d : Nat) (z : Bool) : F64.roundRat n d z =
    if d == 0 then if n == 0 then F64.nan else F64.inf (decide (n < 0))
    else if n == 0 then F64.zero z
    else
      let negative := decide (n < 0)
      let a := n.natAbs
      let e := Fl.floorLog2Rat a d
      if e ≥ 1024 then F64.inf negative
      else if e < -1075 then F64.zero negative
      else
        let k := max (e - 52) (-1074)
        let scaled :=
          if k ≥ 0 then (a, d * 2^k.toNat)
          else (a * 2^(-k).toNat, d)
        f64Pack negative (Fl.roundQuotient scaled.1 scaled.2) k := rfl

theorem f64_ofBits_mod (v : Nat) : F64.ofBits (v % 2 ^ double.width) = F64.ofBits v := by
  unfold F64.ofBits
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd v (by decide)

theorem f64Pack_eq (neg : Bool) (q : Nat) (k : Int) :
    f64Pack neg q k = F64.ofBits (Fl.packRounded (f := double) neg q k).toBits := by
  have c1 : ((double.bias : Nat) : Int) = 1023 := rfl
  have c2 : ((52 : Nat) : Int) = 52 := rfl
  have c3 : ((double.emax : Nat) : Int) = 2047 := rfl
  have c4 : double.sb = 52 := rfl
  have c5 : double.eb = 11 := rfl
  unfold f64Pack Fl.packRounded
  simp only [c1, c3, c4, c5, c2, Nat.reduceAdd, Int.add_assoc, Int.reduceAdd]
  repeat' (first | (exfalso; omega) | split)
  all_goals first
    | (cases neg <;> decide)
    | (rw [Fl.toBits_ofBits, f64_ofBits_mod])

theorem f64_roundRat_bridge (n : Int) (d : Nat) (z : Bool) (hd : d ≠ 0) (hn : n ≠ 0)
    (he : -1075 ≤ Fl.floorLog2Rat n.natAbs d) :
    F64.roundRat n d z = F64.ofBits (Fl.roundRat (f := double) n d z).toBits := by
  have c1 : ((double.emax : Nat) : Int) - (double.bias : Nat) = 1024 := by decide
  have c2 : -(((double.bias : Nat) : Int) + 52) - 1 = -1076 := by decide
  have c3 : (1 : Int) - (double.bias : Nat) - 52 = -1074 := by decide
  have c4 : ((double.sb : Nat) : Int) = 52 := rfl
  have hd' : (d == 0) = false := by simpa using hd
  have hn' : (n == 0) = false := by simpa using hn
  rw [f64_roundRat_eq]
  unfold Fl.roundRat
  simp only [hd', hn', Bool.false_eq_true, ↓reduceIte, c1, c2, c3, c4]
  generalize Fl.floorLog2Rat n.natAbs d = e at he ⊢
  generalize decide (n < 0) = neg
  by_cases h1 : e ≥ 1024
  · rw [if_pos h1, if_pos h1]
    cases neg <;> decide
  · rw [if_neg h1, if_neg h1, if_neg (show ¬ e < -1075 by omega),
      if_neg (show ¬ e < -1076 by omega)]
    exact f64Pack_eq _ _ _

theorem ofF64_ofInt (n : Int) : Fl.ofF64 (F64.ofInt n) = (Fl.ofInt n : Fl double) := by
  by_cases hn : n = 0
  · subst hn
    decide
  · have ha : n.natAbs ≠ 0 := by omega
    have he : Fl.floorLog2Rat n.natAbs 1 = (n.natAbs.log2 : Int) := by
      have := Fl.floorLog2Rat_pow n.natAbs 0 ha
      simpa using this
    unfold F64.ofInt Fl.ofInt Fl.ofF64
    rw [f64_roundRat_bridge n 1 false (by decide) hn (by rw [he]; omega)]
    unfold F64.toBits F64.ofBits
    rw [BitVec.toNat_ofNat, show (2 : Nat) ^ 64 = 2 ^ double.width from rfl,
      Nat.mod_eq_of_lt (show (Fl.roundRat n 1 false : Fl double).toBits < 2 ^ double.width from
        (Fl.roundRat n 1 false : Fl double).bits.isLt), Fl.ofBits_toBits]

theorem cmp_promote64 (x : Fl double) (y : Int) (h : y.natAbs < 2 ^ 53) :
    Fl.eq x (Fl.ofF64 (F64.ofInt y)) = (exactOrder x y == some 0) ∧
    Fl.lt x (Fl.ofF64 (F64.ofInt y)) = (exactOrder x y == some (-1)) ∧
    Fl.le x (Fl.ofF64 (F64.ofInt y)) = (exactOrder x y == some (-1) || exactOrder x y == some 0) ∧
    Fl.lt (Fl.ofF64 (F64.ofInt y)) x = (exactOrder x y == some 1) ∧
    Fl.le (Fl.ofF64 (F64.ofInt y)) x = (exactOrder x y == some 1 || exactOrder x y == some 0) := by
  rw [ofF64_ofInt]
  exact Fl.cmp_promote good_double x y h
    (Nat.lt_trans h (Nat.pow_lt_pow_right (by decide) (by decide)))

theorem cmp_via64 {f : Fmt} (hf : f.Good) (hne : (double == f) = false) (hsb : f.sb ≤ double.sb)
    (hbias : f.bias + f.sb ≤ double.bias) (x : Fl f) (y : Int) (h : y.natAbs < 2 ^ 53) :
    Fl.eq (Fl.convert x : Fl double) (Fl.ofF64 (F64.ofInt y)) = (exactOrder x y == some 0) ∧
    Fl.lt (Fl.convert x : Fl double) (Fl.ofF64 (F64.ofInt y)) = (exactOrder x y == some (-1)) ∧
    Fl.le (Fl.convert x : Fl double) (Fl.ofF64 (F64.ofInt y)) =
      (exactOrder x y == some (-1) || exactOrder x y == some 0) ∧
    Fl.lt (Fl.ofF64 (F64.ofInt y)) (Fl.convert x : Fl double) = (exactOrder x y == some 1) ∧
    Fl.le (Fl.ofF64 (F64.ofInt y)) (Fl.convert x : Fl double) =
      (exactOrder x y == some 1 || exactOrder x y == some 0) := by
  rw [ofF64_ofInt]
  exact Fl.cmp_via hf good_double hne hsb hbias x y h
    (Nat.lt_trans h (Nat.pow_lt_pow_right (by decide) (by decide)))

/-! ### All type pairs -/

theorem natAbs_le_bits {t : IntTy} (y : JInt t) : y.val.natAbs ≤ 2 ^ t.bits := by
  obtain ⟨v, h1, h2⟩ := y
  cases t <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h1 h2 ⊢ <;> omega

theorem natAbs_lt {t : IntTy} (y : JInt t) {k : Nat} (h : 2 ^ t.bits < 2 ^ k) :
    y.val.natAbs < 2 ^ k :=
  Nat.lt_of_le_of_lt (natAbs_le_bits y) h

theorem mixedCompareSmall_proven : MixedCompareSmall := by
  intro T t x y ht
  cases T <;> cases t
  · exact Fl.cmp_promote good_half x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_via good_half good_single (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact cmp_via64 good_half (by decide) (by decide) (by decide) x y.val (natAbs_lt y (by decide))
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact Fl.cmp_promote good_half x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_via good_half good_single (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact cmp_via64 good_half (by decide) (by decide) (by decide) x y.val (natAbs_lt y (by decide))
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact Fl.cmp_promote good_single x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_single x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact cmp_via64 good_single (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide))
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact Fl.cmp_promote good_single x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact Fl.cmp_promote good_single x y.val (natAbs_lt y (by decide)) (natAbs_lt y (by decide))
  · exact cmp_via64 good_single (by decide) (by decide) (by decide) x y.val
      (natAbs_lt y (by decide))
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact cmp_promote64 x y.val (natAbs_lt y (by decide))
  · exact cmp_promote64 x y.val (natAbs_lt y (by decide))
  · exact cmp_promote64 x y.val (natAbs_lt y (by decide))
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact cmp_promote64 x y.val (natAbs_lt y (by decide))
  · exact cmp_promote64 x y.val (natAbs_lt y (by decide))
  · exact cmp_promote64 x y.val (natAbs_lt y (by decide))
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

/-! ### `isless` totality -/

theorem Fl.exactOrder_cases {f : Fmt} (x : Fl f) (hx : x.isnan = false) (y : Int) :
    exactOrder x y = some (-1) ∨ exactOrder x y = some 0 ∨ exactOrder x y = some 1 := by
  unfold exactOrder
  simp only [hx, Bool.false_eq_true, ↓reduceIte]
  split
  · split <;> simp
  · split
    · simp
    · split <;> simp

/-- A float with its sign bit set is at most every nonnegative integer; one without it exceeds
every negative integer. -/
theorem Fl.exactOrder_sign {f : Fmt} (hf : f.Good) (x : Fl f) (hx : x.isnan = false) (y : Int) :
    (x.signbit = true → 0 ≤ y → exactOrder x y ≠ some 1) ∧
    (x.signbit = false → y < 0 → exactOrder x y = some 1) := by
  cases hfin : x.isfinite
  · have he : x.expField = f.emax := by simpa [Fl.isfinite] using hfin
    have hr : x.frac = 0 := by simpa [Fl.isnan, he] using hx
    have hinf : x.isinf = true := by simp [Fl.isinf, he, hr]
    unfold exactOrder
    simp only [hx, hinf, Bool.false_eq_true, ↓reduceIte]
    cases x.signbit <;> simp
  · obtain ⟨m, i, j, hr, -, -, -⟩ := Fl.toRat_cases hf x hfin
    have hP : (0 : Int) < ((2 ^ j : Nat) : Int) := by have := Nat.two_pow_pos j; omega
    unfold exactOrder
    simp only [Fl.isnan_of_finite hfin, Fl.isinf_of_finite hfin, Bool.false_eq_true,
      ↓reduceIte]
    rw [hr]
    dsimp only
    generalize ((2 ^ j : Nat) : Int) = P at hP ⊢
    generalize hA : ((m * 2 ^ i : Nat) : Int) = A
    have hA0 : 0 ≤ A := by omega
    constructor
    · intro hs hy
      have : 0 ≤ y * P := Int.mul_nonneg hy (Int.le_of_lt hP)
      rw [hs]
      simp only [↓reduceIte]
      split
      · simp
      · split
        · simp
        · exfalso; omega
    · intro hs hy
      have : y * P < 0 := Int.mul_neg_of_neg_of_pos hy hP
      rw [hs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · exfalso; omega
      · split
        · exfalso; omega
        · rfl

theorem FTy.good (T : FTy) : T.fmt.Good := by
  cases T
  · exact good_half
  · exact good_single
  · exact good_double

/-- `isless(x::AbstractFloat, y::Integer)`, `isless(y, x)` and `isequal(x, y)`: exactly one
holds, for every IEEE float type and every integer type of at most 32 bits. -/
def MixedIslessTotalSmall : Prop := ∀ (T : FTy) (t : IntTy) (x : FV T) (y : JInt t), t.bits ≤ 32 →
  ((islessFI x y && !islessIF y x && !isequalFI x y) ||
   (!islessFI x y && islessIF y x && !isequalFI x y) ||
   (!islessFI x y && !islessIF y x && isequalFI x y)) = true

theorem mixedIslessTotalSmall_proven : MixedIslessTotalSmall := by
  intro T t x y ht
  obtain ⟨heq, hlt, -, hgt, -⟩ := mixedCompareSmall_proven T t x y ht
  unfold islessFI islessIF isequalFI
  rw [heq, hlt, hgt]
  cases hn : x.isnan
  · have hs := Fl.exactOrder_sign (FTy.good T) x hn y.val
    rcases Fl.exactOrder_cases x hn y.val with h | h | h <;> rw [h] at hs ⊢ <;>
      cases hsb : x.signbit <;> by_cases hy : y.val < 0 <;> simp_all
  · have : exactOrder x y.val = none := by simp [exactOrder, hn]
    rw [this]
    simp

end JuliaLean.Promotion
