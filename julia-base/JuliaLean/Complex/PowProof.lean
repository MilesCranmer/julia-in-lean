import JuliaLean.Complex.Props

namespace JuliaLean.Complex

open JuliaLean JuliaLean.Float

/-! ### Exact Gaussian integers -/

theorem gmul_assoc (a b c : Int × Int) : gmul (gmul a b) c = gmul a (gmul b c) := by
  simp only [gmul, Prod.mk.injEq]
  constructor <;> grind

theorem gmul_comm (a b : Int × Int) : gmul a b = gmul b a := by
  simp only [gmul, Prod.mk.injEq]
  constructor <;> grind

theorem gmul_one (a : Int × Int) : gmul a (1, 0) = a := by
  simp only [gmul]
  ext <;> simp

theorem one_gmul (a : Int × Int) : gmul (1, 0) a = a := by
  rw [gmul_comm, gmul_one]

theorem gpow_one (a : Int × Int) : gpow a 1 = a := by
  simp [gpow, one_gmul]

theorem gpow_add (a : Int × Int) (m n : Nat) : gpow a (m + n) = gmul (gpow a m) (gpow a n) := by
  induction n with
  | zero => simp [gpow, gmul_one]
  | succ n ih => rw [← Nat.add_assoc, gpow, gpow, ih, gmul_assoc]

theorem gpow_mul (a : Int × Int) (m n : Nat) : gpow a (m * n) = gpow (gpow a m) n := by
  induction n with
  | zero => simp [gpow]
  | succ n ih => rw [Nat.mul_succ, gpow_add, ih, gpow]

theorem gpow_two (a : Int × Int) : gpow a 2 = gmul a a := by
  simp [gpow, one_gmul]

/-- Gaussian operations seen by `power_by_squaring`. -/
def gops : MulOps (Int × Int) := ⟨gmul, (1, 0), fun a => a == (1, 0), fun a => (-a.1, -a.2)⟩

theorem squareN_gpow (k : Nat) (x : Int × Int) : squareN gmul k x = gpow x (2 ^ k) := by
  induction k generalizing x with
  | zero => simp [squareN, gpow_one]
  | succ k ih =>
    rw [squareN, ih, ← gpow_two, ← gpow_mul, Nat.pow_succ, Nat.mul_comm]

/-! ### Trailing zeros -/

theorem trailingZeros_spec : ∀ (fuel n : Nat), 0 < n → n < 2 ^ fuel →
    n = 2 ^ trailingZeros fuel n * (2 * (n / 2 ^ (trailingZeros fuel n + 1)) + 1)
  | 0, n, h0, h1 => by simp at h1; omega
  | fuel + 1, n, h0, h1 => by
    by_cases hodd : n % 2 = 0
    · have hne : (n != 0 && n % 2 == 0) = true := by simp [hodd]; omega
      have hpos : 0 < n / 2 := by omega
      have hlt : n / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at h1; omega
      have ih := trailingZeros_spec fuel (n / 2) hpos hlt
      simp only [trailingZeros, hne, ↓reduceIte]
      generalize hs : trailingZeros fuel (n / 2) = s at ih
      have hdiv : n / 2 ^ (s + 1 + 1) = n / 2 / 2 ^ (s + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ 2 (s + 1), Nat.mul_comm]
      rw [hdiv]
      generalize n / 2 / 2 ^ (s + 1) = q at ih ⊢
      rw [Nat.pow_succ, Nat.mul_right_comm, ← ih]
      omega
    · have hne : (n != 0 && n % 2 == 0) = false := by simp [hodd]
      simp only [trailingZeros, hne, Bool.false_eq_true, ↓reduceIte, Nat.pow_zero, Nat.one_mul,
        Nat.zero_add, Nat.pow_one]
      omega

/-! ### The squaring loop on exact Gaussian integers -/

theorem pbsLoop_gpow : ∀ (fuel : Nat) (x y : Int × Int) (p : Nat),
    p < 2 ^ fuel → p < 2 ^ 64 → pbsLoop gmul fuel x y p = gmul y (gpow x (2 * p))
  | 0, x, y, p, h1, _ => by
    simp at h1; subst h1; simp [pbsLoop, gpow, gmul_one]
  | fuel + 1, x, y, p, h1, h2 => by
    by_cases hp : p = 0
    · subst hp; simp [pbsLoop, gpow, gmul_one]
    · simp only [pbsLoop, hp, ↓reduceIte]
      have hspec := trailingZeros_spec 64 p (by omega) h2
      generalize hs : trailingZeros 64 p = s at hspec
      have hshift : p >>> (s + 1) = p / 2 ^ (s + 1) := Nat.shiftRight_eq_div_pow p (s + 1)
      rw [hshift]
      generalize hq : p / 2 ^ (s + 1) = q at hspec
      have hqle : q ≤ p / 2 := by
        rw [← hq, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
        exact Nat.div_le_self _ _
      have hq1 : q < 2 ^ fuel := by rw [Nat.pow_succ] at h1; omega
      rw [pbsLoop_gpow fuel _ _ q hq1 (by omega), squareN_gpow, ← gpow_mul, gmul_assoc, ← gpow_add]
      congr 2
      rw [hspec, Nat.pow_succ]
      generalize 2 ^ s = t
      have e : t * 2 * (2 * q) = 2 * (t * (2 * q)) := by rw [Nat.mul_comm t 2, Nat.mul_assoc]
      rw [e, Nat.mul_add, Nat.mul_one, Nat.mul_add]
      omega

theorem pbs_gpow (x : Int × Int) (p : JInt .i64) (hp : 0 ≤ p.val) :
    powerBySquaring gops x p = .ok (gpow x p.val.toNat) := by
  have hb := p.property
  simp only [IntTy.max, IntTy.min, IntTy.signed, IntTy.bits] at hb
  unfold powerBySquaring
  by_cases h1 : p.val = 1
  · simp [h1, gpow_one]
  by_cases h0 : p.val = 0
  · simp [h0, gpow, gops]
  by_cases h2 : p.val = 2
  · simp [h2, gpow_two, gops]
  have hneg : ¬ p.val < 0 := by omega
  simp only [h1, h0, h2, hneg, ↓reduceIte]
  generalize hn : p.val.toNat = n
  have hn0 : 0 < n := by omega
  have hn64 : n < 2 ^ 64 := by omega
  have hspec := trailingZeros_spec 64 n hn0 hn64
  generalize hs : trailingZeros 64 n = s at hspec
  have hx2 : squareN gops.mul (s + 1 - 2) (if s + 1 - 1 > 0 then gops.mul x x else x)
      = gpow x (2 ^ s) := by
    simp only [gops]
    by_cases hs0 : s = 0
    · subst hs0; simp [squareN, gpow_one]
    · have hgt : s + 1 - 1 > 0 := by omega
      simp only [hgt, ↓reduceIte, squareN_gpow, ← gpow_two, ← gpow_mul]
      congr 1
      rw [← Nat.pow_succ']
      congr 1
      omega
  rw [hx2]
  have hshift : n >>> (s + 1) = n / 2 ^ (s + 1) := Nat.shiftRight_eq_div_pow n (s + 1)
  rw [hshift]
  generalize hq : n / 2 ^ (s + 1) = q at hspec
  have hq64 : q < 2 ^ 64 := by
    have : q ≤ n := by rw [← hq]; exact Nat.div_le_self _ _
    omega
  simp only [gops]
  rw [pbsLoop_gpow 64 _ _ q hq64 hq64, ← gpow_mul, ← gpow_add]
  congr 1
  conv => rhs; rw [hspec]
  rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-! ### Wrapping homomorphism -/

/-- Componentwise `x % Int` of an exact Gaussian integer. -/
def W (p : Int × Int) : CInt .i64 := ⟨JInt.wrap .i64 p.1, JInt.wrap .i64 p.2⟩

/-- Congruence modulo 2^64. -/
def Cg (a b : Int) : Prop := (18446744073709551616 : Int) ∣ a - b

theorem cg_wrap (x : Int) : Cg (wrapInt .i64 x) x := by
  simp only [Cg, wrapInt, IntTy.signed, IntTy.bits]
  simp
  omega

theorem wrap_cg {a b : Int} (h : Cg a b) : wrapInt .i64 a = wrapInt .i64 b := by
  simp only [Cg] at h
  simp only [wrapInt, IntTy.signed, IntTy.bits]
  simp
  omega

theorem cg_trans {a b c : Int} (h1 : Cg a b) (h2 : Cg b c) : Cg a c := by
  simp only [Cg] at *
  have : a - c = (a - b) + (b - c) := by omega
  rw [this]; exact Int.dvd_add h1 h2

theorem cg_mul {A B a b : Int} (h1 : Cg A a) (h2 : Cg B b) : Cg (A * B) (a * b) := by
  simp only [Cg] at *
  have e : A * B - a * b = (A - a) * B + a * (B - b) := by grind
  rw [e]
  exact Int.dvd_add (Int.dvd_trans h1 (Int.dvd_mul_right _ _)) (Int.dvd_trans h2 (Int.dvd_mul_left _ _))

theorem cg_add {A B a b : Int} (h1 : Cg A a) (h2 : Cg B b) : Cg (A + B) (a + b) := by
  simp only [Cg] at *
  have e : A + B - (a + b) = (A - a) + (B - b) := by omega
  rw [e]; exact Int.dvd_add h1 h2

theorem cg_sub {A B a b : Int} (h1 : Cg A a) (h2 : Cg B b) : Cg (A - B) (a - b) := by
  simp only [Cg] at *
  have e : A - B - (a - b) = (A - a) - (B - b) := by omega
  rw [e]; exact Int.dvd_sub h1 h2

theorem cg_wrapmul (A B a b : Int) (h1 : Cg A a) (h2 : Cg B b) :
    Cg (wrapInt .i64 (A * B)) (a * b) := cg_trans (cg_wrap _) (cg_mul h1 h2)

theorem W_mul (p q : Int × Int) : CInt.mul (W p) (W q) = W (gmul p q) := by
  have hp1 := cg_wrap p.1
  have hp2 := cg_wrap p.2
  have hq1 := cg_wrap q.1
  have hq2 := cg_wrap q.2
  simp only [CInt.mul, W, gmul, CInt.mk.injEq]
  constructor <;> apply Subtype.ext <;> apply wrap_cg
  · exact cg_sub (cg_wrapmul _ _ _ _ hp1 hq1) (cg_wrapmul _ _ _ _ hp2 hq2)
  · exact cg_add (cg_wrapmul _ _ _ _ hp1 hq2) (cg_wrapmul _ _ _ _ hp2 hq1)

theorem squareN_W (k : Nat) (x : Int × Int) : squareN CInt.mul k (W x) = W (squareN gmul k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp only [squareN, W_mul, ih]

theorem pbsLoop_W : ∀ (fuel : Nat) (x y : Int × Int) (p : Nat),
    pbsLoop CInt.mul fuel (W x) (W y) p = W (pbsLoop gmul fuel x y p)
  | 0, _, _, _ => rfl
  | fuel + 1, x, y, p => by
    simp only [pbsLoop]
    split
    · rfl
    · rw [squareN_W, W_mul, pbsLoop_W fuel]

theorem pbs_W (x : Int × Int) (p : JInt .i64) (hp : 0 ≤ p.val) :
    powerBySquaring CInt.ops (W x) p = (powerBySquaring gops x p).map W := by
  unfold powerBySquaring
  by_cases h1 : p.val = 1
  · simp [h1, Except.map]
  by_cases h0 : p.val = 0
  · simp [h0, Except.map, CInt.ops, gops, W, CInt.one, JInt.lit]
  by_cases h2 : p.val = 2
  · simp [h2, Except.map, CInt.ops, gops, W_mul]
  have hneg : ¬ p.val < 0 := by omega
  simp only [h1, h0, h2, hneg, ↓reduceIte, Except.map, CInt.ops, gops]
  congr 1
  rw [← pbsLoop_W]
  congr 2 <;> (split <;> simp only [W_mul, squareN_W])

theorem W_self (z : CInt .i64) : W (z.re.val, z.im.val) = z := by
  cases z with
  | mk a b =>
    simp only [W, CInt.mk.injEq]
    constructor
    · exact Subtype.ext (wrapInt_of_inRange .i64 a.val a.property)
    · exact Subtype.ext (wrapInt_of_inRange .i64 b.val b.property)

theorem intPowWraps_proven : IntPowWraps := by
  intro z n hn
  have h := pbs_W (z.re.val, z.im.val) n hn
  rw [pbs_gpow _ n hn, W_self] at h
  unfold CInt.powInt
  rw [h]
  rfl

end JuliaLean.Complex
