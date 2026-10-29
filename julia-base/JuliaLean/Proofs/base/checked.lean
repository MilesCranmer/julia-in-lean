import JuliaLean.base.checked
import JuliaLean.Proofs.base.int
import JuliaLean.Registry.Types

/-!
# Properties of `base/checked.jl`

Arithmetic specifications use the exact mathematical result and the target type's representable
range, independently of the model's intrinsic calls and manual multiplication thresholds.
-/
namespace JuliaLean.Proofs.base.checked

open JuliaLean JuliaLean.C JuliaLean.base.checked JuliaLean.base.int JuliaLean.base.bool JuliaLean.Proofs.base.int
private instance {α : Type} [DecidableEq α] : DecidableEq (Jl α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/- A checked operation reports an overflow error, with a source-specific message. -/
def Overflowed {t : IntTy} : Jl (JInt t) → Prop
  | .error (.overflowError _) => True
  | _ => False

/-- A checked result is exact inside the target range and throws `OverflowError` outside it. -/
def ExactOrOverflow {t : IntTy} (r : Jl (JInt t)) (n : Int) : Prop :=
  if t.min ≤ n ∧ n ≤ t.max then ∃ z, r = .ok z ∧ z.val = n else Overflowed r

private theorem exact_ok_iff {t : IntTy} (z : JInt t) (n : Int) :
    ExactOrOverflow (.ok z) n ↔ z.val = n := by
  by_cases h : t.min ≤ n ∧ n ≤ t.max
  · simp [ExactOrOverflow, h]
  · constructor
    · intro he
      simp [ExactOrOverflow, Overflowed, h] at he
    · intro he
      exact False.elim (h (he ▸ z.property))

private theorem negValue {t : IntTy} (x : JInt t) : (-x).val = wrapInt t (-x.val) := rfl
/-- The bit-integer intrinsic result used by checked add, subtract, and multiply. -/
def intrinsicResult (t : IntTy) (n : Int) : JInt t × Bool :=
  (JInt.wrap t n, decide (¬ (t.min ≤ n ∧ n ≤ t.max)))
-- The intrinsic result either fits exactly or sets its overflow flag.
-- The next theorem proves the intrinsic's range flag.
/-- A wrapped intrinsic result is the exact result or sets its overflow flag. -/
theorem exact_intrinsic {t : IntTy} (n : Int) (msg : String) :
    ExactOrOverflow
      (if (intrinsicResult t n).2 then .error (.overflowError msg)
       else .ok (intrinsicResult t n).1) n := by
  unfold ExactOrOverflow
  by_cases h : t.min ≤ n ∧ n ≤ t.max
  · simp only [if_pos h]
    refine ⟨JInt.wrap t n, ?_, ?_⟩
    · simp [intrinsicResult, h]
    · change wrapInt t n = n
      exact wrapInt_of_inRange t n h
  · simp only [if_neg h]
    simp [intrinsicResult, Overflowed, h]
private theorem signedFlagFormula {t : IntTy} (hs : t.signed = true) (n : Int) :
    (n < -(2 ^ (t.bits - 1) : Nat) || n ≥ (2 ^ (t.bits - 1) : Nat)) =
      decide (¬ (t.min ≤ n ∧ n ≤ t.max)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

private theorem unsignedFlagFormula {t : IntTy} (hu : t.signed = false) (n : Int) :
    (n < 0 || n ≥ (2 ^ t.bits : Nat)) =
      decide (¬ (t.min ≤ n ∧ n ≤ t.max)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  cases t <;> simp_all [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] <;> omega

private theorem signedIntrinsicPair {t : IntTy} (hs : t.signed = true)
    (x y : JInt t) (op : Int → Int → Int) :
    (toJInt t (JuliaLean.C.checkedInteger true op (fromJInt x) (fromJInt y)).1,
      (JuliaLean.C.checkedInteger true op (fromJInt x) (fromJInt y)).2) =
      intrinsicResult t (op x.val y.val) := by
  have hf := signedFlagFormula hs (op x.val y.val)
  simp only [JuliaLean.C.checkedInteger, hs, ↓reduceIte,
    fromJInt_toInt x hs, fromJInt_toInt y hs]
  apply Prod.ext
  · apply Subtype.ext
    simp [intrinsicResult, JInt.wrap, toJInt_ofInt_val]
  · simpa [intrinsicResult] using hf

private theorem unsignedIntrinsicPair {t : IntTy} (hu : t.signed = false)
    (x y : JInt t) (op : Int → Int → Int) :
    (toJInt t (JuliaLean.C.checkedInteger false op (fromJInt x) (fromJInt y)).1,
      (JuliaLean.C.checkedInteger false op (fromJInt x) (fromJInt y)).2) =
      intrinsicResult t (op x.val y.val) := by
  have hf := unsignedFlagFormula hu (op x.val y.val)
  simp only [JuliaLean.C.checkedInteger, hu, ↓reduceIte,
    fromJInt_toNat_unsigned x hu, fromJInt_toNat_unsigned y hu]
  apply Prod.ext
  · apply Subtype.ext
    simp [intrinsicResult, JInt.wrap, toJInt_ofInt_val]
  · simpa [intrinsicResult] using hf
theorem addWithOverflowSignedExact {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    addWithOverflowSigned h x y = intrinsicResult t (x.val + y.val) := by
  simpa [addWithOverflowSigned, JuliaLean.C.jlCheckedSaddInt] using
    (signedIntrinsicPair h x y (· + ·))

theorem addWithOverflowUnsignedExact {t : IntTy} (h : t.signed = false) (x y : JInt t) :
    addWithOverflowUnsigned h x y = intrinsicResult t (x.val + y.val) := by
  simpa [addWithOverflowUnsigned, JuliaLean.C.jlCheckedUaddInt] using
    (unsignedIntrinsicPair h x y (· + ·))

theorem subWithOverflowSignedExact {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    subWithOverflowSigned h x y = intrinsicResult t (x.val - y.val) := by
  simpa [subWithOverflowSigned, JuliaLean.C.jlCheckedSsubInt] using
    (signedIntrinsicPair h x y (· - ·))

theorem subWithOverflowUnsignedExact {t : IntTy} (h : t.signed = false) (x y : JInt t) :
    subWithOverflowUnsigned h x y = intrinsicResult t (x.val - y.val) := by
  simpa [subWithOverflowUnsigned, JuliaLean.C.jlCheckedUsubInt] using
    (unsignedIntrinsicPair h x y (· - ·))
theorem mulWithOverflowSignedExact {t : IntTy} (h : t.signed = true) (x y : JInt t) :
    mulWithOverflowSigned h x y = intrinsicResult t (x.val * y.val) := by
  simpa [mulWithOverflowSigned, JuliaLean.C.jlCheckedSmulInt] using
    (signedIntrinsicPair h x y (· * ·))

theorem mulWithOverflowUnsignedExact {t : IntTy} (h : t.signed = false) (x y : JInt t) :
    mulWithOverflowUnsigned h x y = intrinsicResult t (x.val * y.val) := by
  simpa [mulWithOverflowUnsigned, JuliaLean.C.jlCheckedUmulInt] using
    (unsignedIntrinsicPair h x y (· * ·))

def OverflowReportsExact : Prop :=
  (∀ (t : IntTy) (h : t.signed = true) (x y : JInt t),
    addWithOverflowSigned h x y = intrinsicResult t (x.val + y.val)) ∧
  (∀ (t : IntTy) (h : t.signed = false) (x y : JInt t),
    addWithOverflowUnsigned h x y = intrinsicResult t (x.val + y.val)) ∧
  (∀ (t : IntTy) (h : t.signed = true) (x y : JInt t),
    subWithOverflowSigned h x y = intrinsicResult t (x.val - y.val)) ∧
  (∀ (t : IntTy) (h : t.signed = false) (x y : JInt t),
    subWithOverflowUnsigned h x y = intrinsicResult t (x.val - y.val)) ∧
  (∀ (t : IntTy) (h : t.signed = true) (x y : JInt t),
    mulWithOverflowSigned h x y = intrinsicResult t (x.val * y.val)) ∧
  (∀ (t : IntTy) (h : t.signed = false) (x y : JInt t),
    mulWithOverflowUnsigned h x y = intrinsicResult t (x.val * y.val)) ∧
  (∀ (x y : JInt .i128),
    mulWithOverflowInt128 JInt.fld JInt.cld x y =
      .ok (intrinsicResult .i128 (x.val * y.val))) ∧
  (∀ (x y : JInt .u128),
    mulWithOverflowUInt128 JInt.fld x y =
      .ok (intrinsicResult .u128 (x.val * y.val)))



/-- Addition at every `BitInteger` width is exact or reports overflow. -/
def AddExact : Prop := ∀ (t : IntTy) (x y : JInt t),
  ExactOrOverflow (checkedAddBits x y) (x.val + y.val)

theorem addExact : AddExact := by
  intro t x y
  by_cases hs : t.signed = true
  · simpa [checkedAddBits, checkedAddSame, hs, addWithOverflowSignedExact hs x y,
      throwOverflowBinary, Overflowed, ExactOrOverflow] using
      exact_intrinsic (t := t) (x.val + y.val)
        (checkedBinaryLazyString x " " "+" " " y " overflowed for type " t.name)
  · have hu : t.signed = false := by cases t <;> simp_all [IntTy.signed]
    simpa [checkedAddBits, checkedAddSame, hs, hu, addWithOverflowUnsignedExact hu x y,
      throwOverflowBinary, Overflowed, ExactOrOverflow] using
      exact_intrinsic (t := t) (x.val + y.val)
        (checkedBinaryLazyString x " " "+" " " y " overflowed for type " t.name)
/-- Subtraction at every `BitInteger` width is exact or reports overflow. -/
def SubExact : Prop := ∀ (t : IntTy) (x y : JInt t),
  ExactOrOverflow (checkedSubBits x y) (x.val - y.val)

theorem subExact : SubExact := by
  intro t x y
  by_cases hs : t.signed = true
  · simpa [checkedSubBits, checkedSubSame, hs, subWithOverflowSignedExact hs x y,
      throwOverflowBinary, Overflowed, ExactOrOverflow] using
      exact_intrinsic (t := t) (x.val - y.val)
        (checkedBinaryLazyString x " " "-" " " y " overflowed for type " t.name)
  · have hu : t.signed = false := by cases t <;> simp_all [IntTy.signed]
    simpa [checkedSubBits, checkedSubSame, hs, hu, subWithOverflowUnsignedExact hu x y,
      throwOverflowBinary, Overflowed, ExactOrOverflow] using
      exact_intrinsic (t := t) (x.val - y.val)
        (checkedBinaryLazyString x " " "-" " " y " overflowed for type " t.name)

/-- Same-type checked addition and subtraction satisfy their mathematical contracts. -/
def AddAllExact : Prop :=
  AddExact ∧
  ∀ (lazyString : Bool → String → String → String → Bool → String → String → String)
    (typeOf : Bool → String) (x y : Bool),
    checkedAddSame addWithOverflowBool (throwOverflowBinary lazyString typeOf "+") x y =
      checkedAddBits (ofBool .i64 x) (ofBool .i64 y) ∧
    ExactOrOverflow
      (checkedAddSame addWithOverflowBool (throwOverflowBinary lazyString typeOf "+") x y)
      ((if x then 1 else 0) + (if y then 1 else 0))

theorem addAllExact : AddAllExact := by
  refine ⟨addExact, ?_⟩
  intro lazyString typeOf x y
  simp only [checkedAddSame, addWithOverflowBool, Bool.false_eq_true, ↓reduceIte, exact_ok_iff]
  cases x <;> cases y <;> decide

def SubAllExact : Prop :=
  SubExact ∧
  ∀ (lazyString : Bool → String → String → String → Bool → String → String → String)
    (typeOf : Bool → String) (x y : Bool),
    checkedSubSame subWithOverflowBool (throwOverflowBinary lazyString typeOf "-") x y =
      checkedSubBits (ofBool .i64 x) (ofBool .i64 y) ∧
    ExactOrOverflow
      (checkedSubSame subWithOverflowBool (throwOverflowBinary lazyString typeOf "-") x y)
      ((if x then 1 else 0) - (if y then 1 else 0))

theorem subAllExact : SubAllExact := by
  refine ⟨subExact, ?_⟩
  intro lazyString typeOf x y
  simp only [checkedSubSame, subWithOverflowBool, Bool.false_eq_true, ↓reduceIte, exact_ok_iff]
  cases x <;> cases y <;> decide

def AddSubExact : Prop := AddAllExact ∧ SubAllExact

theorem addSubExact : AddSubExact := ⟨addAllExact, subAllExact⟩

/-- Negation returns its exact mathematical value or reports overflow at every width. -/
def NegExact : Prop := ∀ (t : IntTy) (x : JInt t),
  ExactOrOverflow (checkedNegBits x) (-x.val)

theorem negExact : NegExact := by
  intro t x
  have hz : (JInt.lit t 0).val = 0 := by cases t <;> decide
  simpa [checkedNegBits, checkedNeg, hz] using
    (subExact t (JInt.lit t 0) x)

def NegAllExact : Prop :=
  NegExact ∧
  ∀ (convert : Int → Bool)
    (lazyString : Bool → String → String → String → Bool → String → String → String)
    (typeOf : Bool → String) (x : Bool),
    convert 0 = false →
    checkedNeg convert
      (checkedSubSame subWithOverflowBool (throwOverflowBinary lazyString typeOf "-")) x =
      checkedNegBits (ofBool .i64 x) ∧
    ExactOrOverflow
      (checkedNeg convert
        (checkedSubSame subWithOverflowBool (throwOverflowBinary lazyString typeOf "-")) x)
      (-(if x then 1 else 0))

theorem negAllExact : NegAllExact := by
  refine ⟨negExact, ?_⟩
  intro convert lazyString typeOf x h0
  simp only [checkedNeg, h0, checkedSubSame, subWithOverflowBool, Bool.false_eq_true, ↓reduceIte, exact_ok_iff]
  cases x <;> decide

/-- Absolute value returns its exact mathematical value or reports overflow. -/
def AbsExact : Prop := ∀ (t : IntTy) (x : JInt t),
  ExactOrOverflow (checkedAbsBits x) (if x.val < 0 then -x.val else x.val)

private theorem signedAbsExact {t : IntTy} (hs : t.signed = true) (x : JInt t) :
    ExactOrOverflow (checkedAbsBits x) (if x.val < 0 then -x.val else x.val) := by
  have hx := x.property
  by_cases hn : x.val < 0
  · by_cases hmin : x.val = t.min
    · have hminneg : t.min < 0 := by omega
      have hneg : (-x).val = t.min := by
        rw [negValue, hmin]
        cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.bits, wrapInt] <;> omega
      have hno : ¬ (t.min ≤ -x.val ∧ -x.val ≤ t.max) := by
        cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
      have hOverflow : Overflowed (checkedAbsBits x) := by
        simp [checkedAbsBits, checkedAbsSigned, hs, hn, hneg, hminneg, Overflowed]
      simpa [ExactOrOverflow, hn, hno] using hOverflow
    · have hfit : t.min ≤ -x.val ∧ -x.val ≤ t.max := by
        cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] <;> omega
      have hneg : (-x).val = -x.val := by
        rw [negValue]
        exact wrapInt_of_inRange t (-x.val) hfit
      have hnonpos : ¬ (0 < x.val) := by omega
      simpa [checkedAbsBits, checkedAbsSigned, hs, hn, hneg, hnonpos] using
        (exact_ok_iff (z := -x) (-x.val)).2 hneg
  · simpa [checkedAbsBits, checkedAbsSigned, hs, hn] using
      (exact_ok_iff (z := x) x.val).2 rfl

theorem absExact : AbsExact := by
  intro t x
  by_cases hs : t.signed = true
  · exact signedAbsExact hs x
  · have hu : t.signed = false := by cases t <;> simp_all [IntTy.signed]
    have hn : ¬ x.val < 0 := by
      have hx := x.property
      cases t <;> simp_all [IntTy.signed, IntTy.min] <;> omega
    simpa [checkedAbsBits, hs, hu, checkedAbsUnsigned, hn] using
      (exact_ok_iff (z := x) x.val).2 rfl

def NegAbsExact : Prop := NegAllExact ∧ AbsExact

theorem negAbsExact : NegAbsExact := ⟨negAllExact, absExact⟩

/-- Checked multiplication's product is exact or reports overflow at every width. -/
def MulExact : Prop := ∀ (t : IntTy) (x y : JInt t),
  ExactOrOverflow (checkedMulBits x y) (x.val * y.val)

private theorem wrapInt_sub_wrap (t : IntTy) (x y : Int) :
    wrapInt t (x - wrapInt t y) = wrapInt t (x - y) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

private theorem wrapInt_add_wrap (t : IntTy) (x y : Int) :
    wrapInt t (x + wrapInt t y) = wrapInt t (x + y) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

private theorem ty_range (t : IntTy) :
    (t.min = -(t.max + 1) ∧ 127 ≤ t.max) ∨ (t.min = 0 ∧ 255 ≤ t.max) := by
  cases t <;> simp [IntTy.signed, IntTy.min, IntTy.max, IntTy.bits]

private theorem signed_of_min_neg (t : IntTy) (h : t.min < 0) : t.signed = true := by
  cases t <;> simp_all [IntTy.signed, IntTy.min]

private theorem unsigned_nonneg {t : IntTy} (x : JInt t) (h : t.signed = false) :
    0 ≤ x.val := by
  have hx := x.property.1
  cases t <;> simp_all [IntTy.signed, IntTy.min]

private theorem fdiv_fmod_tdiv (a b : Int) (hb : b ≠ 0) :
    a.fdiv b = (if ((a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0)) ∧ a.tmod b ≠ 0
      then a.tdiv b - 1 else a.tdiv b) ∧
    a.fmod b = (if ((a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0)) ∧ a.tmod b ≠ 0
      then a.tmod b + b else a.tmod b) := by
  have h0 := Int.emod_nonneg a hb
  have h1 := Int.emod_lt a hb
  have h4 : a = 0 → a % b = 0 := by intro h; subst h; simp
  have htm0 : (a.tmod b = 0) = (a % b = 0) := by
    rw [Int.tmod_eq_emod]
    simp only [Int.dvd_iff_emod_eq_zero]
    apply propext
    split <;> omega
  simp only [ne_eq, htm0]
  rw [Int.fdiv_eq_ediv, Int.fmod_eq_emod, Int.tdiv_eq_ediv, Int.tmod_eq_emod]
  simp only [Int.dvd_iff_emod_eq_zero]
  generalize a / b = e
  generalize a % b = m at h0 h1 h4 ⊢
  rcases Int.lt_or_gt_of_ne hb with hs | hs
  · rw [Int.sign_eq_neg_one_of_neg hs]
    constructor <;> (repeat' split) <;> omega
  · rw [Int.sign_eq_one_of_pos hs]
    constructor <;> (repeat' split) <;> omega

private theorem cdiv_tdiv (a b : Int) (hb : b ≠ 0) :
    -((-a).fdiv b) = (if ((0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)) ∧ a.tmod b ≠ 0
      then a.tdiv b + 1 else a.tdiv b) := by
  rw [(fdiv_fmod_tdiv (-a) b hb).1, Int.neg_tdiv, Int.neg_tmod]
  split <;> split <;> omega

private theorem fdiv_mul_add_fmod (a b : Int) (hb : b ≠ 0) :
    a.fdiv b * b + a.fmod b = a := by
  obtain ⟨hfd, hfm⟩ := fdiv_fmod_tdiv a b hb
  have := Int.tdiv_mul_add_tmod a b
  rw [hfd, hfm]
  split
  · rw [Int.sub_mul, Int.one_mul]
    omega
  · omega

private theorem fmod_neg_one (a : Int) : a.fmod (-1) = 0 := by
  rw [(fdiv_fmod_tdiv a (-1) (by decide)).2, Int.tmod_neg, Int.tmod_one]
  simp

private theorem quot_facts (a b : Int) (hb : b ≠ 0) :
    a.tdiv b * b + a.tmod b = a ∧
    (0 ≤ a → 0 ≤ a.tmod b ∧ a.tmod b ≤ a) ∧ (a < 0 → a ≤ a.tmod b ∧ a.tmod b ≤ 0) ∧
    (0 < b → -b < a.tmod b ∧ a.tmod b < b) ∧ (b < 0 → b < a.tmod b ∧ a.tmod b < -b) ∧
    (0 ≤ a → (2 ≤ b ∨ b ≤ -2) → -a ≤ 2 * a.tdiv b ∧ 2 * a.tdiv b ≤ a) ∧
    (a < 0 → (2 ≤ b ∨ b ≤ -2) → a ≤ 2 * a.tdiv b ∧ 2 * a.tdiv b ≤ -a) ∧
    (b = 1 → a.tdiv b = a) ∧ (b = -1 → a.tdiv b = -a) ∧
    (0 ≤ a → 0 < b → 0 ≤ a.tdiv b) := by
  have hra : (a.tmod b).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_tmod]; exact Nat.mod_le _ _
  have hq2 : 2 ≤ b.natAbs → 2 * (a.tdiv b).natAbs ≤ a.natAbs := by
    intro h2
    rw [Int.natAbs_tdiv]
    have := @Nat.div_le_div_left 2 b.natAbs a.natAbs h2 (by omega)
    show 2 * (a.natAbs / b.natAbs) ≤ a.natAbs
    omega
  refine ⟨Int.tdiv_mul_add_tmod a b, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h h2 => ?_, fun h h2 => ?_, fun h => by subst h; exact Int.tdiv_one a,
    fun h => by subst h; rw [Int.tdiv_neg, Int.tdiv_one], fun ha hb' => ?_⟩
  · have := Int.tmod_nonneg b h
    omega
  · have := Int.tmod_nonneg b (show 0 ≤ -a by omega)
    rw [Int.neg_tmod] at this
    omega
  · exact ⟨Int.lt_tmod_of_pos a h, Int.tmod_lt_of_pos a h⟩
  · have h1 := Int.lt_tmod_of_pos a (show 0 < -b by omega)
    have h2 := Int.tmod_lt_of_pos a (show 0 < -b by omega)
    rw [Int.tmod_neg] at h1 h2
    omega
  · have := hq2 (by omega)
    omega
  · have := hq2 (by omega)
    omega
  · rw [Int.tdiv_eq_ediv_of_nonneg ha]; exact Int.ediv_nonneg ha (by omega)

private theorem ranges_int (x y q r lo hi : Int) (hy : y ≠ 0)
    (hx : lo ≤ x ∧ x ≤ hi) (hyr : lo ≤ y ∧ y ≤ hi)
    (hty : (lo = -(hi + 1) ∧ 127 ≤ hi) ∨ (lo = 0 ∧ 255 ≤ hi))
    (hqr : q * y + r = x)
    (hra0 : 0 ≤ x → 0 ≤ r ∧ r ≤ x) (hra1 : x < 0 → x ≤ r ∧ r ≤ 0)
    (hrb0 : 0 < y → -y < r ∧ r < y) (hrb1 : y < 0 → y < r ∧ r < -y)
    (hq20 : 0 ≤ x → (2 ≤ y ∨ y ≤ -2) → -x ≤ 2 * q ∧ 2 * q ≤ x)
    (hq21 : x < 0 → (2 ≤ y ∨ y ≤ -2) → x ≤ 2 * q ∧ 2 * q ≤ -x)
    (hq1 : y = 1 → q = x) (hqm1 : y = -1 → q = -x) (hqpos : 0 ≤ x → 0 < y → 0 ≤ q) :
    (lo ≤ r ∧ r ≤ hi) ∧
    (lo ≤ (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then r + y else r) ∧
      (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then r + y else r) ≤ hi) ∧
    (lo ≤ q * y ∧ q * y ≤ hi) ∧
    (¬(lo < 0 ∧ x = lo ∧ y = -1) →
      (lo ≤ q ∧ q ≤ hi) ∧
      (lo ≤ (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then q - 1 else q) ∧
        (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then q - 1 else q) ≤ hi) ∧
      (lo ≤ (if ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∧ r ≠ 0 then q + 1 else q) ∧
        (if ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∧ r ≠ 0 then q + 1 else q) ≤ hi)) := by
  rcases hty with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩ <;>
  by_cases hx0 : 0 ≤ x <;>
  rcases Int.lt_or_gt_of_ne hy with hy0 | hy0 <;>
  refine ⟨by omega, by split <;> omega, by omega,
    fun hn => ⟨by omega, by split <;> omega, by split <;> omega⟩⟩

private theorem div_ranges {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0) :
    (t.min ≤ a.val.tmod b.val ∧ a.val.tmod b.val ≤ t.max) ∧
    (t.min ≤ a.val.fmod b.val ∧ a.val.fmod b.val ≤ t.max) ∧
    (t.min ≤ a.val.tdiv b.val * b.val ∧ a.val.tdiv b.val * b.val ≤ t.max) ∧
    (¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1) →
      (t.min ≤ a.val.tdiv b.val ∧ a.val.tdiv b.val ≤ t.max) ∧
      (t.min ≤ a.val.fdiv b.val ∧ a.val.fdiv b.val ≤ t.max) ∧
      (t.min ≤ -((-a.val).fdiv b.val) ∧ -((-a.val).fdiv b.val) ≤ t.max)) := by
  obtain ⟨hqr, hr0, hr1, hrb, hra, hqa, hq2, hq1, hqm1, hqpos⟩ := quot_facts a.val b.val hb0
  obtain ⟨hfd, hfm⟩ := fdiv_fmod_tdiv a.val b.val hb0
  have key := ranges_int a.val b.val _ _ t.min t.max hb0 a.property b.property (ty_range t)
    hqr hr0 hr1 hrb hra hqa hq2 hq1 hqm1 hqpos
  rw [hfd, hfm, cdiv_tdiv a.val b.val hb0]
  exact ⟨key.1, key.2.1, key.2.2.1,
    fun hn => key.2.2.2 fun h => hn ⟨signed_of_min_neg t h.1, h.2⟩⟩

private theorem div_mach {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0)
    (hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    JInt.div a b = .ok (JInt.wrap t (a.val.tdiv b.val)) := by
  unfold JInt.div
  rw [ite_eq_right_iff.mpr (fun h => False.elim (hb0 h)),
    ite_eq_right_iff.mpr (fun h => False.elim (hn h))]

private theorem mul_wrap_val {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0)
    (hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    (JInt.wrap t (a.val.tdiv b.val) * b).val = a.val.tdiv b.val * b.val := by
  obtain ⟨-, -, hqbR, hrng⟩ := div_ranges a b hb0
  show wrapInt t (wrapInt t _ * b.val) = _
  rw [wrapInt_of_inRange t _ (hrng hn).1, wrapInt_of_inRange t _ hqbR]

private theorem pos_of_unsigned {t : IntTy} (x : JInt t) (h : t.signed = false)
    (hx : x.val ≠ 0) : 0 < x.val := by
  have := unsigned_nonneg x h
  omega

private theorem sub_of_add (p m x : Int) (h : p + m = x) : x - p = m := by
  omega

private theorem fld_cond (x y q r : Int) (hy : y ≠ 0) (hqr : q * y + r = x)
    (hr0 : 0 ≤ x → 0 ≤ r ∧ r ≤ x) (hr1 : x < 0 → x ≤ r ∧ r ≤ 0) :
    q - (if ((x < 0 ∧ 0 ≤ y) ∨ (0 ≤ x ∧ y < 0)) ∧ q * y ≠ x then 1 else 0) =
      (if ((x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0)) ∧ r ≠ 0 then q - 1 else q) := by
  split <;> split <;> omega

private theorem cld_cond (s : Bool) (x y q r : Int) (hy : y ≠ 0) (hqr : q * y + r = x)
    (hr0 : 0 ≤ x → 0 ≤ r ∧ r ≤ x) (hr1 : x < 0 → x ≤ r ∧ r ≤ 0)
    (hs : s = false → 0 ≤ x ∧ 0 < y) :
    q + (if (¬ s = true ∨ (x > 0 ↔ y > 0)) ∧ q * y ≠ x then 1 else 0) =
      (if ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) ∧ r ≠ 0 then q + 1 else q) := by
  cases s
  · have := hs rfl
    simp only [Bool.false_eq_true, not_false_eq_true, true_or, true_and]
    split <;> split <;> omega
  · simp only [not_true_eq_false, false_or]
    split <;> split <;> omega

private theorem fld_mach {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0)
    (hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    JInt.fld a b = .ok (JInt.wrap t (a.val.fdiv b.val)) := by
  obtain ⟨hqr, hr0, hr1, -⟩ := quot_facts a.val b.val hb0
  obtain ⟨-, -, -, hrng⟩ := div_ranges a b hb0
  obtain ⟨hfd, -⟩ := fdiv_fmod_tdiv a.val b.val hb0
  unfold JInt.fld
  rw [div_mach a b hb0 hn]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [mul_wrap_val a b hb0 hn]
  cases hs : t.signed
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have ha0 := unsigned_nonneg a hs
    have hb1 := pos_of_unsigned b hs hb0
    rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hb1), Int.tdiv_eq_ediv_of_nonneg ha0]
  · simp only [↓reduceIte]
    congr 1
    apply Subtype.ext
    show wrapInt t (wrapInt t (a.val.tdiv b.val) - wrapInt t _) = wrapInt t (a.val.fdiv b.val)
    rw [wrapInt_of_inRange t (a.val.tdiv b.val) (hrng hn).1, wrapInt_sub_wrap, hfd,
      fld_cond a.val b.val _ _ hb0 hqr hr0 hr1]

private theorem cld_mach {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0)
    (hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    JInt.cld a b = .ok (JInt.wrap t (-((-a.val).fdiv b.val))) := by
  obtain ⟨hqr, hr0, hr1, -⟩ := quot_facts a.val b.val hb0
  obtain ⟨-, -, -, hrng⟩ := div_ranges a b hb0
  have hsu : t.signed = false → 0 ≤ a.val ∧ 0 < b.val := fun hs =>
    ⟨unsigned_nonneg a hs, pos_of_unsigned b hs hb0⟩
  unfold JInt.cld
  rw [div_mach a b hb0 hn]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [mul_wrap_val a b hb0 hn]
  congr 1
  apply Subtype.ext
  show wrapInt t (wrapInt t (a.val.tdiv b.val) + wrapInt t _) =
    wrapInt t (-((-a.val).fdiv b.val))
  rw [wrapInt_of_inRange t (a.val.tdiv b.val) (hrng hn).1, wrapInt_add_wrap,
    cdiv_tdiv a.val b.val hb0, cld_cond t.signed a.val b.val _ _ hb0 hqr hr0 hr1 hsu]

private theorem mod_mach {t : IntTy} (a b : JInt t) (hb0 : b.val ≠ 0) :
    JInt.mod a b = .ok (JInt.wrap t (a.val.fmod b.val)) := by
  obtain ⟨-, -, -, hrng⟩ := div_ranges a b hb0
  unfold JInt.mod
  cases hs : t.signed
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have ha0 := unsigned_nonneg a hs
    have hb1 := pos_of_unsigned b hs hb0
    unfold JInt.remInt
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hb0 h)),
      Int.fmod_eq_emod_of_nonneg _ (Int.le_of_lt hb1),
      Int.tmod_eq_emod_of_nonneg ha0]
  · simp only [↓reduceIte]
    by_cases hbm : b.val = -1
    · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hbm)), hbm, fmod_neg_one]
      rfl
    · have hn : ¬(t.signed = true ∧ a.val = t.min ∧ b.val = -1) := fun h => hbm h.2.2
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hbm h)), fld_mach a b hb0 hn]
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      congr 1
      apply Subtype.ext
      show wrapInt t (a.val - wrapInt t (wrapInt t (a.val.fdiv b.val) * b.val)) =
        wrapInt t (a.val.fmod b.val)
      rw [wrapInt_of_inRange t (a.val.fdiv b.val) (hrng hn).2.1, wrapInt_sub_wrap]
      rw [sub_of_add _ _ _ (fdiv_mul_add_fmod a.val b.val hb0)]

private theorem ok_map_val {t : IntTy} (x : Int) (h : t.min ≤ x ∧ x ≤ t.max) :
    (Except.ok (JInt.wrap t x) : Jl (JInt t)).map Subtype.val = .ok x := by
  show Except.ok (wrapInt t x) = Except.ok x
  rw [wrapInt_of_inRange t x h]

private theorem fldResultValue {t : IntTy} (x y : JInt t)
    (hno : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1))
    (hy : y.val ≠ 0) :
    ∃ z, JInt.fld x y = .ok z ∧ z.val = x.val.fdiv y.val := by
  obtain ⟨-, -, -, hrng⟩ := div_ranges x y hy
  refine ⟨JInt.wrap t (x.val.fdiv y.val), fld_mach x y hy hno, ?_⟩
  exact wrapInt_of_inRange t (x.val.fdiv y.val) (hrng hno).2.1

private theorem cldResultValue {t : IntTy} (x y : JInt t)
    (hno : ¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1))
    (hy : y.val ≠ 0) :
    ∃ z, JInt.cld x y = .ok z ∧ z.val = -((-x.val).fdiv y.val) := by
  obtain ⟨-, -, -, hrng⟩ := div_ranges x y hy
  refine ⟨JInt.wrap t (-((-x.val).fdiv y.val)), cld_mach x y hy hno, ?_⟩
  exact wrapInt_of_inRange t (-((-x.val).fdiv y.val)) (hrng hno).2.2

private theorem floorDivBounds (a b : Int) (hb : b ≠ 0) :
    (0 < b → a.fdiv b * b ≤ a ∧ a < (a.fdiv b + 1) * b) ∧
    (b < 0 → a ≤ a.fdiv b * b ∧ (a.fdiv b + 1) * b < a) := by
  have hqr : b * (a / b) + a % b = a := Int.mul_ediv_add_emod a b
  have hr0 := Int.emod_nonneg a hb
  constructor
  · intro hp
    have hq : a.fdiv b = a / b :=
      Int.fdiv_eq_ediv_of_nonneg a (Int.le_of_lt hp)
    rw [hq]
    have hrlt := Int.emod_lt_of_pos a hp
    constructor
    · have hmul : (a / b) * b = b * (a / b) := Int.mul_comm _ _
      rw [hmul]
      omega
    · have hmul : (a / b + 1) * b = b * (a / b) + b := by
        rw [Int.add_mul, Int.one_mul, Int.mul_comm (a / b) b]
      calc
        a = b * (a / b) + a % b := hqr.symm
        _ < b * (a / b) + b := by omega
        _ = (a / b + 1) * b := hmul.symm
  · intro hn
    have hrlt := Int.emod_lt a hb
    have hbabs : (b.natAbs : Int) = -b := Int.ofNat_natAbs_of_nonpos (by omega)
    rw [hbabs] at hrlt
    by_cases hd : b ∣ a
    · have hrz := Int.dvd_iff_emod_eq_zero.mp hd
      have hq : a.fdiv b = a / b := by
        simp [Int.fdiv_eq_ediv, hn, hd]
      rw [hq]
      rw [hrz] at hqr
      constructor
      · rw [Int.mul_comm (a / b) b]
        omega
      · have hmul : (a / b + 1) * b = b * (a / b) + b := by
          rw [Int.add_mul, Int.one_mul, Int.mul_comm (a / b) b]
        rw [hmul]
        omega
    · have hrpos : 0 < a % b := by
        have hrne : a % b ≠ 0 := fun hz => hd (Int.dvd_iff_emod_eq_zero.mpr hz)
        omega
      have hq : a.fdiv b = a / b - 1 := by
        simp [Int.fdiv_eq_ediv, hn, hd]
      rw [hq]
      constructor
      · have hmul : (a / b - 1) * b = b * (a / b) - b := by
          rw [Int.sub_mul, Int.one_mul, Int.mul_comm (a / b) b]
        rw [hmul]
        omega
      · have hmul : (a / b - 1 + 1) * b = b * (a / b) := by
          rw [show a / b - 1 + 1 = a / b by omega,
            Int.mul_comm (a / b) b]
        rw [hmul]
        omega
private theorem typeminValue (t : IntTy) : (JInt.typemin t).val = t.min := by
  change wrapInt t t.min = t.min
  exact wrapInt_of_inRange t t.min
    ⟨by simp, by cases t <;> simp [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed] <;> omega⟩

private theorem typemaxValue (t : IntTy) : (JInt.typemax t).val = t.max := by
  change wrapInt t t.max = t.max
  exact wrapInt_of_inRange t t.max
    ⟨by cases t <;> simp [IntTy.min, IntTy.max, IntTy.bits, IntTy.signed] <;> omega, by simp⟩

private theorem unsignedMulThreshold (m x y q : Int) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hlo : q * y ≤ m) (hhi : m < (q + 1) * y) :
    decide (x > q) = decide (¬ (0 ≤ x * y ∧ x * y ≤ m)) := by
  by_cases h : x > q
  · have hmul : (q + 1) * y ≤ x * y :=
      Int.mul_le_mul_of_nonneg_right (by omega) hy
    have hbad : ¬ (0 ≤ x * y ∧ x * y ≤ m) := by
      intro hfit
      omega
    simp [h, hbad]
  · have hmul : x * y ≤ q * y :=
      Int.mul_le_mul_of_nonneg_right (by omega) hy
    have hfit : 0 ≤ x * y ∧ x * y ≤ m := by
      exact ⟨Int.mul_nonneg hx hy, by omega⟩
    simp [h, hfit]

private theorem signedMulThresholdPos (m M x y hi lo : Int)
    (hy : 0 < y) (hhi : hi * y ≤ M) (hhi' : M < (hi + 1) * y)
    (hlo : m ≤ lo * y) (hlo' : (lo - 1) * y < m) :
    (if x > hi then true else decide (x < lo)) =
      decide (¬ (m ≤ x * y ∧ x * y ≤ M)) := by
  by_cases hhigh : x > hi
  · have hmul : (hi + 1) * y ≤ x * y :=
      Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hy)
    have hbad : ¬ (m ≤ x * y ∧ x * y ≤ M) := by
      intro hfit
      omega
    simp [hhigh, hbad]
  · by_cases hlow : x < lo
    · have hmul : x * y ≤ (lo - 1) * y :=
        Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hy)
      have hbad : ¬ (m ≤ x * y ∧ x * y ≤ M) := by
        intro hfit
        omega
      simp [hhigh, hlow, hbad]
    · have hupper : x * y ≤ hi * y :=
        Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hy)
      have hlower : lo * y ≤ x * y :=
        Int.mul_le_mul_of_nonneg_right (by omega) (Int.le_of_lt hy)
      have hfit : m ≤ x * y ∧ x * y ≤ M := by omega
      simp [hhigh, hlow, hfit]

private theorem signedMulThresholdNeg (m M x y hi lo : Int)
    (hy : y < 0) (hhi : hi * y ≤ M) (hhi' : M < (hi - 1) * y)
    (hlo : m ≤ lo * y) (hlo' : (lo + 1) * y < m) (hne : y ≠ -1) :
    (if x < hi then true else if y != -1 then decide (x > lo) else false) =
      decide (¬ (m ≤ x * y ∧ x * y ≤ M)) := by
  have hneBool : (y != -1) = true := by simp [hne]
  by_cases hhigh : x < hi
  · have hmul : (hi - 1) * y ≤ x * y :=
      Int.mul_le_mul_of_nonpos_right (by omega) (Int.le_of_lt hy)
    have hbad : ¬ (m ≤ x * y ∧ x * y ≤ M) := by
      intro hfit
      omega
    simp [hhigh, hneBool, hbad]
  · by_cases hlow : x > lo
    · have hmul : x * y ≤ (lo + 1) * y :=
        Int.mul_le_mul_of_nonpos_right (by omega) (Int.le_of_lt hy)
      have hbad : ¬ (m ≤ x * y ∧ x * y ≤ M) := by
        intro hfit
        omega
      simp [hhigh, hlow, hneBool, hbad]
    · have hupper : x * y ≤ hi * y :=
        Int.mul_le_mul_of_nonpos_right (by omega) (Int.le_of_lt hy)
      have hlower : lo * y ≤ x * y :=
        Int.mul_le_mul_of_nonpos_right (by omega) (Int.le_of_lt hy)
      have hfit : m ≤ x * y ∧ x * y ≤ M := by omega
      simp [hhigh, hlow, hneBool, hfit]

private theorem signedMulNegOneThreshold (m M x : Int)
    (hm : m = -(M + 1)) (hx : m ≤ x ∧ x ≤ M) :
    x < -M ↔ ¬ (m ≤ x * -1 ∧ x * -1 ≤ M) := by
  by_cases h : x < -M
  · have hx' : x = m := by omega
    have hprod : x * -1 = M + 1 := by rw [hx', hm]; simp
    have hbad : ¬ (m ≤ x * -1 ∧ x * -1 ≤ M) := by
      intro hfit
      rw [hprod] at hfit
      omega
    constructor
    · intro _
      exact hbad
    · intro _
      exact h
  · have hfit : m ≤ x * -1 ∧ x * -1 ≤ M := by omega
    constructor
    · intro hxlt
      exact False.elim (h hxlt)
    · intro hbad
      exact False.elim (hbad hfit)
private theorem mulWithOverflowInt128Exact (x y : JInt .i128) :
    mulWithOverflowInt128 JInt.fld JInt.cld x y =
      .ok (intrinsicResult .i128 (x.val * y.val)) := by
  let m : Int := IntTy.i128.min
  let M : Int := IntTy.i128.max
  have hmM : m = -(M + 1) := by
    dsimp [m, M, IntTy.min, IntTy.max, IntTy.bits, IntTy.signed]
  have htmin : (JInt.typemin .i128).val = m := by
    simpa [m] using typeminValue .i128
  have htmax : (JInt.typemax .i128).val = M := by
    simpa [M] using typemaxValue .i128
  have hxrange : m ≤ x.val ∧ x.val ≤ M := by
    simpa [m, M] using x.property
  have hmul : x * y = JInt.wrap .i128 (x.val * y.val) := rfl
  by_cases hy0 : y.val = 0
  · simp [mulWithOverflowInt128, hy0, hmul, intrinsicResult, m, M,
      IntTy.min, IntTy.max, IntTy.bits, IntTy.signed,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · by_cases hypos : y.val > 0
    · have hnoHigh : ¬ (IntTy.i128.signed = true ∧
          (JInt.typemax .i128).val = IntTy.i128.min ∧ y.val = -1) := by
        intro h
        omega
      have hnoLow : ¬ (IntTy.i128.signed = true ∧
          (JInt.typemin .i128).val = IntTy.i128.min ∧ y.val = -1) := by
        intro h
        omega
      obtain ⟨high, hhigh, hhighVal⟩ :=
        fldResultValue (JInt.typemax .i128) y hnoHigh hy0
      obtain ⟨low, hlow, hlowVal⟩ :=
        cldResultValue (JInt.typemin .i128) y hnoLow hy0
      have hhval : high.val = M.fdiv y.val := by
        simpa [htmax] using hhighVal
      have hlval : low.val = -((-m).fdiv y.val) := by
        simpa [htmin] using hlowVal
      have hfloorHigh := (floorDivBounds M y.val hy0).1 hypos
      have hhighBounds : high.val * y.val ≤ M ∧ M < (high.val + 1) * y.val := by
        simpa [hhval] using hfloorHigh
      let k : Int := (-m).fdiv y.val
      have hlval' : low.val = -k := by simpa [k] using hlval
      have hfloorLow := (floorDivBounds (-m) y.val hy0).1 hypos
      have hfloorLow' : k * y.val ≤ -m ∧ -m < (k + 1) * y.val := by
        simpa [k] using hfloorLow
      have hlowLower : m ≤ low.val * y.val := by
        rw [hlval', Int.neg_mul]
        omega
      have hlowUpper : (low.val - 1) * y.val < m := by
        calc
          (low.val - 1) * y.val = -((k + 1) * y.val) := by
            rw [hlval', show -k - 1 = -(k + 1) by omega, Int.neg_mul]
          _ < m := by omega
      have hlowBounds : m ≤ low.val * y.val ∧ (low.val - 1) * y.val < m :=
        ⟨hlowLower, hlowUpper⟩
      have hflag := signedMulThresholdPos m M x.val y.val high.val low.val
        (by omega) hhighBounds.1 hhighBounds.2 hlowBounds.1 hlowBounds.2
      simp only [mulWithOverflowInt128, if_pos hypos, hhigh, hlow,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      by_cases hhighBranch : x.val > high.val
      · simp only [hhighBranch]
        apply congrArg (Except.ok : JInt .i128 × Bool → Jl (JInt .i128 × Bool))
        apply Prod.ext
        · exact hmul
        · simpa [intrinsicResult, m, M, IntTy.min, IntTy.max, IntTy.bits,
            IntTy.signed, hhighBranch] using hflag
      · simp only [hhighBranch]
        apply congrArg (Except.ok : JInt .i128 × Bool → Jl (JInt .i128 × Bool))
        apply Prod.ext
        · exact hmul
        · simpa [intrinsicResult, m, M, IntTy.min, IntTy.max, IntTy.bits,
            IntTy.signed, hhighBranch] using hflag
    · have hyneg : y.val < 0 := by omega
      by_cases hyone : y.val = -1
      · have hnoHigh : ¬ (IntTy.i128.signed = true ∧
            (JInt.typemax .i128).val = IntTy.i128.min ∧ y.val = -1) := by
          intro h
          have hval : M = m := by simpa [htmax, htmin] using h.2.1
          omega
        obtain ⟨high, hhigh, hhighVal⟩ :=
          cldResultValue (JInt.typemax .i128) y hnoHigh hy0
        have hhighFormula : high.val = -((-M).fdiv (-1)) := by
          simpa only [htmax, hyone] using hhighVal
        have hfloor := (floorDivBounds (-M) (-1) (by decide)).2 (by decide)
        have hquot : (-M).fdiv (-1) = M := by
          simp only [Int.mul_neg_one] at hfloor
          omega
        have hhighValue : high.val = -M := by
          rw [hhighFormula, hquot]
        have hflag := signedMulNegOneThreshold m M x.val hmM hxrange
        have hyoneBool : (y.val != -1) = false := by simp [hyone]
        simp only [mulWithOverflowInt128,
          if_neg (by omega : ¬ y.val > 0), if_pos hyneg, hhigh, hyoneBool,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        by_cases hhighBranch : x.val < high.val
        · simp only [hhighBranch]
          have hbad : ¬ (m ≤ x.val * y.val ∧ x.val * y.val ≤ M) := by
            have hlt : x.val < -M := by simpa [hhighValue] using hhighBranch
            have h := hflag.mp hlt
            simpa [hyone, Int.mul_neg_one] using h
          have hbad'' : ¬ (IntTy.i128.min ≤ x.val * y.val ∧
              x.val * y.val ≤ IntTy.i128.max) := by
            simpa [m, M] using hbad
          apply congrArg (Except.ok : JInt .i128 × Bool → Jl (JInt .i128 × Bool))
          apply Prod.ext
          · exact hmul
          · change true = decide (¬ (IntTy.i128.min ≤ x.val * y.val ∧
              x.val * y.val ≤ IntTy.i128.max))
            simp [hbad'']
        · simp only [hhighBranch]
          have hnot : ¬ x.val < -M := by simpa [hhighValue] using hhighBranch
          have hprod : x.val * y.val = -x.val := by rw [hyone]; simp
          have hfit : m ≤ x.val * y.val ∧ x.val * y.val ≤ M := by
            rw [hprod]
            omega
          have hfit' : IntTy.i128.min ≤ x.val * y.val ∧
              x.val * y.val ≤ IntTy.i128.max := by simpa [m, M] using hfit
          apply congrArg (Except.ok : JInt .i128 × Bool → Jl (JInt .i128 × Bool))
          apply Prod.ext
          · exact hmul
          · change false = decide (¬ (IntTy.i128.min ≤ x.val * y.val ∧
              x.val * y.val ≤ IntTy.i128.max))
            simp [hfit']
      · have hnoHigh : ¬ (IntTy.i128.signed = true ∧
            (JInt.typemax .i128).val = IntTy.i128.min ∧ y.val = -1) := by
          intro h
          exact hyone h.2.2
        have hnoLow : ¬ (IntTy.i128.signed = true ∧
            (JInt.typemin .i128).val = IntTy.i128.min ∧ y.val = -1) := by
          intro h
          exact hyone h.2.2
        obtain ⟨high, hhigh, hhighVal⟩ :=
          cldResultValue (JInt.typemax .i128) y hnoHigh hy0
        obtain ⟨low, hlow, hlowVal⟩ :=
          fldResultValue (JInt.typemin .i128) y hnoLow hy0
        have hhval : high.val = -((-M).fdiv y.val) := by
          simpa [htmax] using hhighVal
        have hlval : low.val = m.fdiv y.val := by
          simpa [htmin] using hlowVal
        let k : Int := (-M).fdiv y.val
        have hhval' : high.val = -k := by simpa [k] using hhval
        have hfloorHigh := (floorDivBounds (-M) y.val hy0).2 hyneg
        have hfloorHigh' : -M ≤ k * y.val ∧
            (k + 1) * y.val < -M := by simpa [k] using hfloorHigh
        have hhighUpper : high.val * y.val ≤ M := by
          rw [hhval', Int.neg_mul]
          omega
        have hhighLower : M < (high.val - 1) * y.val := by
          calc
            M < -((k + 1) * y.val) := by omega
            _ = (high.val - 1) * y.val := by
              rw [hhval', show -k - 1 = -(k + 1) by omega, Int.neg_mul]
        have hfloorLow := (floorDivBounds m y.val hy0).2 hyneg
        have hlowBounds : m ≤ low.val * y.val ∧
            (low.val + 1) * y.val < m := by simpa [hlval] using hfloorLow
        have hhighBounds : high.val * y.val ≤ M ∧
            M < (high.val - 1) * y.val := ⟨hhighUpper, hhighLower⟩
        have hflag := signedMulThresholdNeg m M x.val y.val high.val low.val
          hyneg hhighBounds.1 hhighBounds.2 hlowBounds.1 hlowBounds.2 hyone
        have hyneBool : (y.val != -1) = true := by simp [hyone]
        simp only [mulWithOverflowInt128, if_neg (by omega : ¬ y.val > 0),
          if_pos hyneg, hhigh, hlow, hyneBool,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        by_cases hhighBranch : x.val < high.val
        · simp only [hhighBranch]
          apply congrArg (Except.ok : JInt .i128 × Bool → Jl (JInt .i128 × Bool))
          apply Prod.ext
          · exact hmul
          · simpa [intrinsicResult, m, M, IntTy.min, IntTy.max, IntTy.bits,
              IntTy.signed, hhighBranch, hyneBool] using hflag
        · simp only [hhighBranch]
          apply congrArg (Except.ok : JInt .i128 × Bool → Jl (JInt .i128 × Bool))
          apply Prod.ext
          · exact hmul
          · simpa [intrinsicResult, m, M, IntTy.min, IntTy.max, IntTy.bits,
              IntTy.signed, hhighBranch, hyneBool] using hflag

private theorem mulWithOverflowUInt128Exact (x y : JInt .u128) :
    mulWithOverflowUInt128 JInt.fld x y =
      .ok (intrinsicResult .u128 (x.val * y.val)) := by
  let M : Int := IntTy.u128.max
  have htmax : (JInt.typemax .u128).val = M := by
    simpa [M] using typemaxValue .u128
  have hx0 : 0 ≤ x.val := by
    simpa [IntTy.min, IntTy.signed] using x.property.1
  have hmul : x * y = JInt.wrap .u128 (x.val * y.val) := rfl
  by_cases hy0 : y.val = 0
  · simp [mulWithOverflowUInt128, hy0, hmul, intrinsicResult, M,
      IntTy.min, IntTy.max, IntTy.bits, IntTy.signed,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have hyNonneg : 0 ≤ y.val := by
      simpa [IntTy.min, IntTy.signed] using y.property.1
    have hypos : 0 < y.val := by omega
    have hno : ¬ (IntTy.u128.signed = true ∧
        (JInt.typemax .u128).val = IntTy.u128.min ∧ y.val = -1) := by
      simp [IntTy.signed]
    obtain ⟨high, hhigh, hhighVal⟩ :=
      fldResultValue (JInt.typemax .u128) y hno hy0
    have hhval : high.val = M.fdiv y.val := by
      simpa [htmax] using hhighVal
    have hfloor := (floorDivBounds M y.val hy0).1 hypos
    have hhighBounds : high.val * y.val ≤ M ∧
        M < (high.val + 1) * y.val := by simpa [hhval] using hfloor
    have hflag := unsignedMulThreshold M x.val y.val high.val hx0
      (Int.le_of_lt hypos) hhighBounds.1 hhighBounds.2
    simp only [mulWithOverflowUInt128, if_pos hypos, hhigh,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    apply congrArg (Except.ok : JInt .u128 × Bool → Jl (JInt .u128 × Bool))
    apply Prod.ext
    · exact hmul
    · simpa [intrinsicResult, M, IntTy.min, IntTy.max, IntTy.bits,
        IntTy.signed] using hflag

theorem mulWithOverflowBitsExact {t : IntTy} (x y : JInt t) :
    mulWithOverflowBits x y = .ok (intrinsicResult t (x.val * y.val)) := by
  cases t with
  | i8 =>
    simpa [mulWithOverflowBits] using congrArg (Except.ok : JInt .i8 × Bool → Jl (JInt .i8 × Bool))
      (mulWithOverflowSignedExact (t := .i8) rfl x y)
  | i16 =>
    simpa [mulWithOverflowBits] using congrArg (Except.ok : JInt .i16 × Bool → Jl (JInt .i16 × Bool))
      (mulWithOverflowSignedExact (t := .i16) rfl x y)
  | i32 =>
    simpa [mulWithOverflowBits] using congrArg (Except.ok : JInt .i32 × Bool → Jl (JInt .i32 × Bool))
      (mulWithOverflowSignedExact (t := .i32) rfl x y)
  | i64 =>
    simpa [mulWithOverflowBits] using congrArg (Except.ok : JInt .i64 × Bool → Jl (JInt .i64 × Bool))
      (mulWithOverflowSignedExact (t := .i64) rfl x y)
  | i128 => simpa [mulWithOverflowBits] using mulWithOverflowInt128Exact x y
  | u8 =>
    simpa [mulWithOverflowBits] using congrArg (Except.ok : JInt .u8 × Bool → Jl (JInt .u8 × Bool))
      (mulWithOverflowUnsignedExact (t := .u8) rfl x y)
  | u16 =>
    simpa [mulWithOverflowBits] using congrArg (Except.ok : JInt .u16 × Bool → Jl (JInt .u16 × Bool))
      (mulWithOverflowUnsignedExact (t := .u16) rfl x y)
  | u32 =>
    simpa [mulWithOverflowBits] using congrArg (Except.ok : JInt .u32 × Bool → Jl (JInt .u32 × Bool))
      (mulWithOverflowUnsignedExact (t := .u32) rfl x y)
  | u64 =>
    simpa [mulWithOverflowBits] using congrArg (Except.ok : JInt .u64 × Bool → Jl (JInt .u64 × Bool))
      (mulWithOverflowUnsignedExact (t := .u64) rfl x y)
  | u128 => simpa [mulWithOverflowBits] using mulWithOverflowUInt128Exact x y

theorem overflowReportsExact : OverflowReportsExact := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t h x y
    exact addWithOverflowSignedExact h x y
  · intro t h x y
    exact addWithOverflowUnsignedExact h x y
  · intro t h x y
    exact subWithOverflowSignedExact h x y
  · intro t h x y
    exact subWithOverflowUnsignedExact h x y
  · intro t h x y
    exact mulWithOverflowSignedExact h x y
  · intro t h x y
    exact mulWithOverflowUnsignedExact h x y
  · exact mulWithOverflowInt128Exact
  · exact mulWithOverflowUInt128Exact

set_option maxHeartbeats 800000 in
theorem mulExact : MulExact := by
  intro t x y
  have hp := mulWithOverflowBitsExact x y
  simpa [checkedMulBits, checkedMulSame, throwOverflowBinary, checkedBinaryLazyString,
    Bind.bind, Except.bind, Pure.pure, Overflowed, ExactOrOverflow, hp] using
    exact_intrinsic (t := t) (x.val * y.val)
      (checkedBinaryLazyString x " " "*" " " y " overflowed for type " t.name)

def MulAllExact : Prop :=
  MulExact ∧
  ∀ (lazyString : Bool → String → String → String → Bool → String → String → String)
    (typeOf : Bool → String) (x y : Bool),
    (∀ z : Bool,
      checkedMulSame (fun a b => .ok (mulWithOverflowBool a b))
        (throwOverflowBinary lazyString typeOf "*") x y = .ok z ↔
      (if z then (1 : Int) else 0) = (if x then 1 else 0) * (if y then 1 else 0)) ∧
    (∀ t : IntTy,
      (checkedMulSame (fun a b => .ok (mulWithOverflowBool a b))
        (throwOverflowBinary lazyString typeOf "*") x y).map (ofBool t) =
        checkedMulBits (ofBool t x) (ofBool t y))

theorem mulAllExact : MulAllExact := by
  refine ⟨mulExact, ?_⟩
  intro lazyString typeOf x y
  constructor
  · intro z
    simp only [checkedMulSame, mulWithOverflowBool, Bind.bind, Except.bind,
      Bool.false_eq_true, ↓reduceIte]
    cases x <;> cases y <;> cases z <;> decide
  · intro t
    simp only [checkedMulSame, mulWithOverflowBool, Bind.bind, Except.bind,
      Bool.false_eq_true, ↓reduceIte]
    cases t <;> cases x <;> cases y <;> decide

/-- The 128-bit small-factor contract follows from the all-input property. -/
def ManualSmallFactorsExact : Prop := ∀ (t : IntTy) (x : JInt t) (k : Int),
  (t = .i128 ∨ t = .u128) →
  (k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2) →
  ExactOrOverflow (checkedMulBits x (JInt.lit t k))
    (x.val * (JInt.lit t k).val)

theorem manualSmallFactorsExact : ManualSmallFactorsExact := by
  intro t x k _ _
  exact mulExact t x (JInt.lit t k)

/-- All widths detect the documented upper and lower checked-arithmetic boundaries. -/
def BoundaryArithmetic : Prop := ∀ t : IntTy,
  ExactOrOverflow (checkedAddBits (JInt.typemax t) (JInt.lit t 1))
    ((JInt.typemax t).val + (JInt.lit t 1).val) ∧
  ExactOrOverflow (checkedSubBits (JInt.typemin t) (JInt.lit t 1))
    ((JInt.typemin t).val - (JInt.lit t 1).val) ∧
  ExactOrOverflow (checkedMulBits (JInt.typemax t) (JInt.lit t 2))
    ((JInt.typemax t).val * (JInt.lit t 2).val) ∧
  ExactOrOverflow (checkedMulBits (JInt.typemin t) (JInt.lit t (-1)))
    ((JInt.typemin t).val * (JInt.lit t (-1)).val) ∧
  ExactOrOverflow (checkedNegBits (JInt.typemin t)) (-(JInt.typemin t).val) ∧
  ExactOrOverflow (checkedAbsBits (JInt.typemin t))
    (if (JInt.typemin t).val < 0 then -(JInt.typemin t).val else (JInt.typemin t).val)

theorem boundaryArithmetic : BoundaryArithmetic := by
  intro t
  exact ⟨addExact t (JInt.typemax t) (JInt.lit t 1),
    subExact t (JInt.typemin t) (JInt.lit t 1),
    mulExact t (JInt.typemax t) (JInt.lit t 2),
    mulExact t (JInt.typemin t) (JInt.lit t (-1)),
    negExact t (JInt.typemin t),
    absExact t (JInt.typemin t)⟩

/-! ## Checked division -/

/-- Zero division and signed `typemin / -1` throw `DivideError`; remainders are zero. -/
def DivisionBoundaries : Prop := ∀ t : IntTy,
  checkedDiv JInt.div (JInt.lit t 0) (JInt.lit t 0) = .error .divideError ∧
  (t.signed = true →
    checkedDiv JInt.div (JInt.typemin t) (JInt.lit t (-1)) = .error .divideError ∧
    checkedFld JInt.fld (JInt.typemin t) (JInt.lit t (-1)) = .error .divideError ∧
    checkedCld JInt.cld (JInt.typemin t) (JInt.lit t (-1)) = .error .divideError ∧
    checkedRem JInt.remInt (JInt.typemin t) (JInt.lit t (-1)) = .ok (JInt.lit t 0) ∧
    checkedMod JInt.mod (JInt.typemin t) (JInt.lit t (-1)) = .ok (JInt.lit t 0))

theorem divisionBoundaries : DivisionBoundaries := by
  intro t
  cases t <;> decide

/- The checked integer division methods agree with unbounded integer arithmetic (`Int.tdiv`,
   `Int.tmod`, `Int.fdiv`, `Int.fmod`, and ceiling division `-((-x).fdiv y)`), except that
   signed `typemin / -1` cannot produce a machine-width quotient. -/
def DivisionExact : Prop := ∀ (t : IntTy) (x y : JInt t),
  (y.val = 0 →
    checkedRem JInt.remInt x y = .error .divideError ∧
    checkedMod JInt.mod x y = .error .divideError ∧
    checkedDiv JInt.div x y = .error .divideError ∧
    checkedFld JInt.fld x y = .error .divideError ∧
    checkedCld JInt.cld x y = .error .divideError) ∧
  (y.val ≠ 0 →
    (checkedRem JInt.remInt x y).map Subtype.val = .ok (x.val.tmod y.val) ∧
    (checkedMod JInt.mod x y).map Subtype.val = .ok (x.val.fmod y.val) ∧
    (¬ (t.signed = true ∧ x.val = t.min ∧ y.val = -1) →
      (checkedDiv JInt.div x y).map Subtype.val = .ok (x.val.tdiv y.val) ∧
      (checkedFld JInt.fld x y).map Subtype.val = .ok (x.val.fdiv y.val) ∧
      (checkedCld JInt.cld x y).map Subtype.val = .ok (-((-x.val).fdiv y.val))))

theorem divisionExact : DivisionExact := by
  intro t x y
  constructor
  · intro hy0
    have hd : JInt.div x y = .error .divideError := by simp [JInt.div, hy0]
    have hf : JInt.fld x y = .error .divideError := by
      simp only [JInt.fld, hd, Bind.bind, Except.bind]
    have hc : JInt.cld x y = .error .divideError := by
      simp only [JInt.cld, hd, Bind.bind, Except.bind]
    have hm : JInt.mod x y = .error .divideError := by
      simp [JInt.mod, JInt.remInt, hf, hy0, Bind.bind, Except.bind]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [checkedRem, checkedMod, checkedDiv, checkedFld, checkedCld,
        JInt.remInt, hm, hd, hf, hc, hy0]
  · intro hy0
    obtain ⟨hrR, hfmR, -, hrng⟩ := div_ranges x y hy0
    have hrem : JInt.remInt x y = .ok (JInt.wrap t (x.val.tmod y.val)) := by
      unfold JInt.remInt
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hy0 h))]
    refine ⟨?_, ?_, fun hn => ?_⟩
    · simpa [checkedRem, hrem] using ok_map_val (x.val.tmod y.val) hrR
    · simpa [checkedMod, mod_mach x y hy0] using ok_map_val (x.val.fmod y.val) hfmR
    · obtain ⟨hqR, hfR, hcR⟩ := hrng hn
      refine ⟨?_, ?_, ?_⟩
      · simpa [checkedDiv, div_mach x y hy0 hn] using ok_map_val (x.val.tdiv y.val) hqR
      · simpa [checkedFld, fld_mach x y hy0 hn] using ok_map_val (x.val.fdiv y.val) hfR
      · simpa [checkedCld, cld_mach x y hy0 hn] using ok_map_val (-((-x.val).fdiv y.val)) hcR

/-! ## Promotion before checked operations -/
private theorem ofBool_val (t : IntTy) (b : Bool) :
    (ofBool t b).val = if b then 1 else 0 := by
  cases t <;> cases b <;> decide

private theorem not_ofBool_min {t : IntTy} (b : Bool) (y : JInt t) :
    ¬ (t.signed = true ∧ (ofBool t b).val = t.min ∧ y.val = -1) := by
  intro h
  have hmin : t.signed = true ∧ (ofBool t b).val = t.min := ⟨h.1, h.2.1⟩
  revert hmin
  cases t <;> cases b <;> decide

private theorem not_ofBool_neg_one {t : IntTy} (x : JInt t) (b : Bool) :
    ¬ (t.signed = true ∧ x.val = t.min ∧ (ofBool t b).val = -1) := by
  intro h
  have hm1 : (ofBool t b).val = -1 := h.2.2
  revert hm1
  cases t <;> cases b <;> decide

/-- For every mixed fixed-width integer pair and every mixed `Bool`/fixed-width integer pair in
both argument orders, inexact promotion to the target type fails with `InexactError` before the
operation (including before divide-by-zero), and successful promotion converts both arguments to
the promoted width and equals the corresponding same-type checked result (producing the exact
sum, difference, product, or division/remainder on the integer values). -/
def PromotionBeforeOperation : Prop :=
  (∀ (t s : IntTy)
    (promote : JInt t → JInt s → Jl (JInt (t.promote s) × JInt (t.promote s))),
    (∀ a b, promote a b = do
      let pa ← JInt.convert (t.promote s) a.val
      let pb ← JInt.convert (t.promote s) b.val
      pure (pa, pb)) →
    ∀ (x : JInt t) (y : JInt s),
      if h : ((t.promote s).min ≤ x.val ∧ x.val ≤ (t.promote s).max) ∧
             ((t.promote s).min ≤ y.val ∧ y.val ≤ (t.promote s).max) then
        let pa : JInt (t.promote s) := ⟨x.val, h.1⟩
        let pb : JInt (t.promote s) := ⟨y.val, h.2⟩
        checkedAddPromoted promote checkedAddBits x y = checkedAddBits pa pb ∧
        checkedSubPromoted promote checkedSubBits x y = checkedSubBits pa pb ∧
        checkedMulPromoted promote checkedMulBits x y = checkedMulBits pa pb ∧
        checkedDivPromoted promote (checkedDiv JInt.div) x y = checkedDiv JInt.div pa pb ∧
        checkedRemPromoted promote (checkedRem JInt.remInt) x y = checkedRem JInt.remInt pa pb ∧
        checkedFldPromoted promote (checkedFld JInt.fld) x y = checkedFld JInt.fld pa pb ∧
        checkedModPromoted promote (checkedMod JInt.mod) x y = checkedMod JInt.mod pa pb ∧
        checkedCldPromoted promote (checkedCld JInt.cld) x y = checkedCld JInt.cld pa pb ∧
        ExactOrOverflow (checkedAddPromoted promote checkedAddBits x y) (x.val + y.val) ∧
        ExactOrOverflow (checkedSubPromoted promote checkedSubBits x y) (x.val - y.val) ∧
        ExactOrOverflow (checkedMulPromoted promote checkedMulBits x y) (x.val * y.val) ∧
        (y.val = 0 →
          checkedRemPromoted promote (checkedRem JInt.remInt) x y = .error .divideError ∧
          checkedModPromoted promote (checkedMod JInt.mod) x y = .error .divideError ∧
          checkedDivPromoted promote (checkedDiv JInt.div) x y = .error .divideError ∧
          checkedFldPromoted promote (checkedFld JInt.fld) x y = .error .divideError ∧
          checkedCldPromoted promote (checkedCld JInt.cld) x y = .error .divideError) ∧
        (y.val ≠ 0 →
          (checkedRemPromoted promote (checkedRem JInt.remInt) x y).map Subtype.val =
            .ok (x.val.tmod y.val) ∧
          (checkedModPromoted promote (checkedMod JInt.mod) x y).map Subtype.val =
            .ok (x.val.fmod y.val) ∧
          (¬ ((t.promote s).signed = true ∧ x.val = (t.promote s).min ∧ y.val = -1) →
            (checkedDivPromoted promote (checkedDiv JInt.div) x y).map Subtype.val =
              .ok (x.val.tdiv y.val) ∧
            (checkedFldPromoted promote (checkedFld JInt.fld) x y).map Subtype.val =
              .ok (x.val.fdiv y.val) ∧
            (checkedCldPromoted promote (checkedCld JInt.cld) x y).map Subtype.val =
              .ok (-((-x.val).fdiv y.val))))
      else
        checkedAddPromoted promote checkedAddBits x y =
          .error (.inexactError (t.promote s).name) ∧
        checkedSubPromoted promote checkedSubBits x y =
          .error (.inexactError (t.promote s).name) ∧
        checkedMulPromoted promote checkedMulBits x y =
          .error (.inexactError (t.promote s).name) ∧
        checkedDivPromoted promote (checkedDiv JInt.div) x y =
          .error (.inexactError (t.promote s).name) ∧
        checkedRemPromoted promote (checkedRem JInt.remInt) x y =
          .error (.inexactError (t.promote s).name) ∧
        checkedFldPromoted promote (checkedFld JInt.fld) x y =
          .error (.inexactError (t.promote s).name) ∧
        checkedModPromoted promote (checkedMod JInt.mod) x y =
          .error (.inexactError (t.promote s).name) ∧
        checkedCldPromoted promote (checkedCld JInt.cld) x y =
          .error (.inexactError (t.promote s).name)) ∧
  (∀ (t : IntTy) (promote : Bool → JInt t → Jl (JInt t × JInt t)),
    (∀ a b, promote a b = .ok (ofBool t a, b)) →
    ∀ (x : Bool) (y : JInt t),
      let px : JInt t := ofBool t x
      let xv : Int := if x then 1 else 0
      checkedAddPromoted promote checkedAddBits x y = checkedAddBits px y ∧
      checkedSubPromoted promote checkedSubBits x y = checkedSubBits px y ∧
      checkedMulPromoted promote checkedMulBits x y = checkedMulBits px y ∧
      checkedDivPromoted promote (checkedDiv JInt.div) x y = checkedDiv JInt.div px y ∧
      checkedRemPromoted promote (checkedRem JInt.remInt) x y = checkedRem JInt.remInt px y ∧
      checkedFldPromoted promote (checkedFld JInt.fld) x y = checkedFld JInt.fld px y ∧
      checkedModPromoted promote (checkedMod JInt.mod) x y = checkedMod JInt.mod px y ∧
      checkedCldPromoted promote (checkedCld JInt.cld) x y = checkedCld JInt.cld px y ∧
      ExactOrOverflow (checkedAddPromoted promote checkedAddBits x y) (xv + y.val) ∧
      ExactOrOverflow (checkedSubPromoted promote checkedSubBits x y) (xv - y.val) ∧
      ExactOrOverflow (checkedMulPromoted promote checkedMulBits x y) (xv * y.val) ∧
      (y.val = 0 →
        checkedRemPromoted promote (checkedRem JInt.remInt) x y = .error .divideError ∧
        checkedModPromoted promote (checkedMod JInt.mod) x y = .error .divideError ∧
        checkedDivPromoted promote (checkedDiv JInt.div) x y = .error .divideError ∧
        checkedFldPromoted promote (checkedFld JInt.fld) x y = .error .divideError ∧
        checkedCldPromoted promote (checkedCld JInt.cld) x y = .error .divideError) ∧
      (y.val ≠ 0 →
        (checkedRemPromoted promote (checkedRem JInt.remInt) x y).map Subtype.val =
          .ok (xv.tmod y.val) ∧
        (checkedModPromoted promote (checkedMod JInt.mod) x y).map Subtype.val =
          .ok (xv.fmod y.val) ∧
        (checkedDivPromoted promote (checkedDiv JInt.div) x y).map Subtype.val =
          .ok (xv.tdiv y.val) ∧
        (checkedFldPromoted promote (checkedFld JInt.fld) x y).map Subtype.val =
          .ok (xv.fdiv y.val) ∧
        (checkedCldPromoted promote (checkedCld JInt.cld) x y).map Subtype.val =
          .ok (-((-xv).fdiv y.val)))) ∧
  (∀ (t : IntTy) (promote : JInt t → Bool → Jl (JInt t × JInt t)),
    (∀ a b, promote a b = .ok (a, ofBool t b)) →
    ∀ (x : JInt t) (y : Bool),
      let py : JInt t := ofBool t y
      let yv : Int := if y then 1 else 0
      checkedAddPromoted promote checkedAddBits x y = checkedAddBits x py ∧
      checkedSubPromoted promote checkedSubBits x y = checkedSubBits x py ∧
      checkedMulPromoted promote checkedMulBits x y = checkedMulBits x py ∧
      checkedDivPromoted promote (checkedDiv JInt.div) x y = checkedDiv JInt.div x py ∧
      checkedRemPromoted promote (checkedRem JInt.remInt) x y = checkedRem JInt.remInt x py ∧
      checkedFldPromoted promote (checkedFld JInt.fld) x y = checkedFld JInt.fld x py ∧
      checkedModPromoted promote (checkedMod JInt.mod) x y = checkedMod JInt.mod x py ∧
      checkedCldPromoted promote (checkedCld JInt.cld) x y = checkedCld JInt.cld x py ∧
      ExactOrOverflow (checkedAddPromoted promote checkedAddBits x y) (x.val + yv) ∧
      ExactOrOverflow (checkedSubPromoted promote checkedSubBits x y) (x.val - yv) ∧
      ExactOrOverflow (checkedMulPromoted promote checkedMulBits x y) (x.val * yv) ∧
      (yv = 0 →
        checkedRemPromoted promote (checkedRem JInt.remInt) x y = .error .divideError ∧
        checkedModPromoted promote (checkedMod JInt.mod) x y = .error .divideError ∧
        checkedDivPromoted promote (checkedDiv JInt.div) x y = .error .divideError ∧
        checkedFldPromoted promote (checkedFld JInt.fld) x y = .error .divideError ∧
        checkedCldPromoted promote (checkedCld JInt.cld) x y = .error .divideError) ∧
      (yv ≠ 0 →
        (checkedRemPromoted promote (checkedRem JInt.remInt) x y).map Subtype.val =
          .ok (x.val.tmod yv) ∧
        (checkedModPromoted promote (checkedMod JInt.mod) x y).map Subtype.val =
          .ok (x.val.fmod yv) ∧
        (checkedDivPromoted promote (checkedDiv JInt.div) x y).map Subtype.val =
          .ok (x.val.tdiv yv) ∧
        (checkedFldPromoted promote (checkedFld JInt.fld) x y).map Subtype.val =
          .ok (x.val.fdiv yv) ∧
        (checkedCldPromoted promote (checkedCld JInt.cld) x y).map Subtype.val =
          .ok (-((-x.val).fdiv yv))))

theorem promotionBeforeOperation : PromotionBeforeOperation := by
  refine ⟨?_, ?_, ?_⟩
  · intro t s promote hprom x y
    by_cases hx : (t.promote s).min ≤ x.val ∧ x.val ≤ (t.promote s).max
    · by_cases hy : (t.promote s).min ≤ y.val ∧ y.val ≤ (t.promote s).max
      · have hboth : ((t.promote s).min ≤ x.val ∧ x.val ≤ (t.promote s).max) ∧
            ((t.promote s).min ≤ y.val ∧ y.val ≤ (t.promote s).max) := ⟨hx, hy⟩
        have hp : promote x y = .ok (⟨x.val, hx⟩, ⟨y.val, hy⟩) := by
          simp [hprom, JInt.convert, hx, hy, Bind.bind, Except.bind, Pure.pure, Except.pure]
        have hdiv := divisionExact (t.promote s) ⟨x.val, hx⟩ ⟨y.val, hy⟩
        simp only [dif_pos hboth, checkedAddPromoted, checkedSubPromoted, checkedMulPromoted,
          checkedDivPromoted, checkedRemPromoted, checkedFldPromoted, checkedModPromoted,
          checkedCldPromoted, hp, Bind.bind, Except.bind]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
          addExact (t.promote s) ⟨x.val, hx⟩ ⟨y.val, hy⟩,
          subExact (t.promote s) ⟨x.val, hx⟩ ⟨y.val, hy⟩,
          mulExact (t.promote s) ⟨x.val, hx⟩ ⟨y.val, hy⟩,
          hdiv.1, hdiv.2⟩
      · have hnot : ¬ (((t.promote s).min ≤ x.val ∧ x.val ≤ (t.promote s).max) ∧
            ((t.promote s).min ≤ y.val ∧ y.val ≤ (t.promote s).max)) := fun h => hy h.2
        have hp : promote x y = .error (.inexactError (t.promote s).name) := by
          simp [hprom, JInt.convert, hx, hy, Bind.bind, Except.bind]
        simp [hnot, checkedAddPromoted, checkedSubPromoted, checkedMulPromoted,
          checkedDivPromoted, checkedRemPromoted, checkedFldPromoted, checkedModPromoted,
          checkedCldPromoted, hp, Bind.bind, Except.bind]
    · have hnot : ¬ (((t.promote s).min ≤ x.val ∧ x.val ≤ (t.promote s).max) ∧
          ((t.promote s).min ≤ y.val ∧ y.val ≤ (t.promote s).max)) := fun h => hx h.1
      have hp : promote x y = .error (.inexactError (t.promote s).name) := by
        simp [hprom, JInt.convert, hx, Bind.bind, Except.bind]
      simp [hnot, checkedAddPromoted, checkedSubPromoted, checkedMulPromoted,
        checkedDivPromoted, checkedRemPromoted, checkedFldPromoted, checkedModPromoted,
        checkedCldPromoted, hp, Bind.bind, Except.bind]
  · intro t promote hprom x y
    have hdiv := divisionExact t (ofBool t x) y
    have hval := ofBool_val t x
    have hno := not_ofBool_min x y
    simp only [checkedAddPromoted, checkedSubPromoted, checkedMulPromoted,
      checkedDivPromoted, checkedRemPromoted, checkedFldPromoted, checkedModPromoted,
      checkedCldPromoted, hprom, Bind.bind, Except.bind]
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      hval ▸ addExact t (ofBool t x) y,
      hval ▸ subExact t (ofBool t x) y,
      hval ▸ mulExact t (ofBool t x) y,
      hdiv.1, ?_⟩
    intro hy0
    have hnz := hdiv.2 hy0
    have hq := hnz.2.2 hno
    exact ⟨hval ▸ hnz.1, hval ▸ hnz.2.1, hval ▸ hq.1, hval ▸ hq.2.1, hval ▸ hq.2.2⟩
  · intro t promote hprom x y
    have hdiv := divisionExact t x (ofBool t y)
    have hval := ofBool_val t y
    have hno := not_ofBool_neg_one x y
    simp only [checkedAddPromoted, checkedSubPromoted, checkedMulPromoted,
      checkedDivPromoted, checkedRemPromoted, checkedFldPromoted, checkedModPromoted,
      checkedCldPromoted, hprom, Bind.bind, Except.bind]
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      hval ▸ addExact t x (ofBool t y),
      hval ▸ subExact t x (ofBool t y),
      hval ▸ mulExact t x (ofBool t y),
      fun hy0 => hdiv.1 (hval.trans hy0), ?_⟩
    intro hy0
    have hnz := hdiv.2 (fun h => hy0 (hval.symm.trans h))
    have hq := hnz.2.2 hno
    exact ⟨hval ▸ hnz.1, hval ▸ hnz.2.1, hval ▸ hq.1, hval ▸ hq.2.1, hval ▸ hq.2.2⟩
/-! ## Checked powers -/

/-- Successful integer powers of negative exponent must have base `1` or `-1`. -/
def NegativePowerUnits : Prop :=
  ∀ (t s : IntTy) (x : JInt t) (p : JInt s),
    p.val < 0 →
    ((∃ z, checkedPow (checkedPowerBySquaring powerBySquaringBits checkedMulBits) x p = .ok z) ∨
     (∃ z, checkedPowerBySquaring powerBySquaringBits checkedMulBits x p = .ok z)) →
    x.val = 1 ∨ x.val = -1

theorem negativePowerUnits_refuted : ¬ NegativePowerUnits := by
  intro h
  have bad := h .u8 .i8 (JInt.lit .u8 255) (JInt.lit .i8 (-1))
  have hp : (JInt.lit .i8 (-1)).val < 0 := by decide
  have hz : (∃ z, checkedPow (checkedPowerBySquaring powerBySquaringBits checkedMulBits)
        (JInt.lit .u8 255) (JInt.lit .i8 (-1)) = .ok z) ∨
      (∃ z, checkedPowerBySquaring powerBySquaringBits checkedMulBits
        (JInt.lit .u8 255) (JInt.lit .i8 (-1)) = .ok z) := by
    exact Or.inl ⟨JInt.lit .u8 255, by decide⟩
  have hf := bad hp hz
  have hn : ¬ ((JInt.lit .u8 255).val = 1 ∨ (JInt.lit .u8 255).val = -1) := by decide
  exact hn hf

/- The power-by-squaring callee is defined in `base/intfuncs.jl`. Its contract for a
   nonnegative exponent is exact power or checked overflow. -/
def CheckedPowerExact : Prop :=
  ∀ {t s : IntTy}
    (powerBySquaring : JInt t → JInt s →
      (JInt t → JInt t → Jl (JInt t)) → Jl (JInt t)),
    (∀ x p, 0 ≤ p.val →
      ExactOrOverflow (powerBySquaring x p checkedMulBits) (x.val ^ p.val.toNat)) →
    ∀ (x : JInt t) (p : JInt s), 0 ≤ p.val →
      ExactOrOverflow
        (checkedPowerBySquaring powerBySquaring checkedMulBits x p)
        (x.val ^ p.val.toNat) ∧
      ExactOrOverflow
        (checkedPow (checkedPowerBySquaring powerBySquaring checkedMulBits) x p)
        (x.val ^ p.val.toNat)

theorem checkedPowerExact : CheckedPowerExact := by
  intro t s powerBySquaring hpower x p hp
  exact ⟨by simpa [checkedPowerBySquaring] using hpower x p hp,
    by simpa [checkedPow, checkedPowerBySquaring] using hpower x p hp⟩

def BoolArithmeticExact : Prop :=
  (∀ (t : IntTy) (x : Bool),
    checkedAbsBits (ofBool t x) = .ok (ofBool t (checkedAbsBool x)) ∧
    ExactOrOverflow (.ok (ofBool t (checkedAbsBool x))) ↑((ofBool t x).val.natAbs)) ∧
  (∀ x : Bool,
    checkedAddBits (JInt.lit .i64 0) (ofBool .i64 x) = .ok (checkedAddBool x) ∧
    ExactOrOverflow (.ok (checkedAddBool x)) (if x then 1 else 0)) ∧
  (∀ (convert : Int → Bool)
     (lazyString : Bool → String → String → String → Bool → String → String → String)
     (typeOf : Bool → String) (x : Bool),
    convert 0 = false →
    checkedNeg convert
      (checkedSubSame subWithOverflowBool (throwOverflowBinary lazyString typeOf "-")) x =
      checkedNegBits (ofBool .i64 x) ∧
    ExactOrOverflow
      (checkedNeg convert
        (checkedSubSame subWithOverflowBool (throwOverflowBinary lazyString typeOf "-")) x)
      (-(if x then 1 else 0))) ∧
  (∀ (lazyString : Bool → String → String → String → Bool → String → String → String)
     (typeOf : Bool → String) (x y : Bool),
    checkedAddSame addWithOverflowBool (throwOverflowBinary lazyString typeOf "+") x y =
      checkedAddBits (ofBool .i64 x) (ofBool .i64 y) ∧
    ExactOrOverflow
      (checkedAddSame addWithOverflowBool (throwOverflowBinary lazyString typeOf "+") x y)
      ((if x then 1 else 0) + (if y then 1 else 0)) ∧
    checkedSubSame subWithOverflowBool (throwOverflowBinary lazyString typeOf "-") x y =
      checkedSubBits (ofBool .i64 x) (ofBool .i64 y) ∧
    ExactOrOverflow
      (checkedSubSame subWithOverflowBool (throwOverflowBinary lazyString typeOf "-") x y)
      ((if x then 1 else 0) - (if y then 1 else 0)) ∧
    (∀ z : Bool,
      checkedMulSame (fun a b => .ok (mulWithOverflowBool a b))
        (throwOverflowBinary lazyString typeOf "*") x y = .ok z ↔
      (if z then (1 : Int) else 0) = (if x then 1 else 0) * (if y then 1 else 0)) ∧
    (∀ t : IntTy,
      (checkedMulSame (fun a b => .ok (mulWithOverflowBool a b))
        (throwOverflowBinary lazyString typeOf "*") x y).map (ofBool t) =
        checkedMulBits (ofBool t x) (ofBool t y))) ∧
  (∀ x y : Bool,
    addWithOverflowBool x y =
      intrinsicResult .i64 ((if x then 1 else 0) + (if y then 1 else 0)) ∧
    addWithOverflowBool x y =
      addWithOverflowSigned (t := .i64) rfl (ofBool .i64 x) (ofBool .i64 y)) ∧
  (∀ x y : Bool,
    subWithOverflowBool x y =
      intrinsicResult .i64 ((if x then 1 else 0) - (if y then 1 else 0)) ∧
    subWithOverflowBool x y =
      subWithOverflowSigned (t := .i64) rfl (ofBool .i64 x) (ofBool .i64 y)) ∧
  (∀ x y : Bool,
    (ofBool .i64 (mulWithOverflowBool x y).1, (mulWithOverflowBool x y).2) =
      intrinsicResult .i64 ((if x then 1 else 0) * (if y then 1 else 0)) ∧
    (if (mulWithOverflowBool x y).1 then (1 : Int) else 0) =
      ((if x then (1 : Int) else 0) * (if y then (1 : Int) else 0)) % 2 ∧
    (mulWithOverflowBool x y).2 =
      decide (¬ ((if typeminBool then (1 : Int) else 0) ≤
          (if x then (1 : Int) else 0) * (if y then (1 : Int) else 0) ∧
        (if x then (1 : Int) else 0) * (if y then (1 : Int) else 0) ≤
          (if typemaxBool then (1 : Int) else 0))))

theorem boolArithmeticExact : BoolArithmeticExact := by
  unfold BoolArithmeticExact
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x
    simp only [exact_ok_iff]
    cases t <;> cases x <;> decide
  · intro x
    simp only [exact_ok_iff]
    cases x <;> decide
  · exact negAllExact.2
  · intro lazyString typeOf x y
    refine ⟨(addAllExact.2 lazyString typeOf x y).1,
      (addAllExact.2 lazyString typeOf x y).2,
      (subAllExact.2 lazyString typeOf x y).1,
      (subAllExact.2 lazyString typeOf x y).2, ?_, ?_⟩
    · intro z
      simp only [checkedMulSame, mulWithOverflowBool, Bind.bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
      cases x <;> cases y <;> cases z <;> decide
    · intro t
      simp only [checkedMulSame, mulWithOverflowBool, Bind.bind, Except.bind, Bool.false_eq_true, ↓reduceIte]
      cases t <;> cases x <;> cases y <;> decide
  · intro x y
    cases x <;> cases y <;> decide
  · intro x y
    cases x <;> cases y <;> decide
  · intro x y
    cases x <;> cases y <;> decide
/-!
## Julia method to property map

| Julia method | Property |
| --- | --- |
| `checked_add(::Integer,::Integer)@26` | `intarith-checked-promotion-order` |
| `checked_sub(::Integer,::Integer)@27` | `intarith-checked-promotion-order` |
| `checked_mul(::Integer,::Integer)@28` | `intarith-checked-promotion-order` |
| `checked_div(::Integer,::Integer)@29` | `intarith-checked-promotion-order` |
| `checked_rem(::Integer,::Integer)@30` | `intarith-checked-promotion-order` |
| `checked_fld(::Integer,::Integer)@31` | `intarith-checked-promotion-order` |
| `checked_mod(::Integer,::Integer)@32` | `intarith-checked-promotion-order` |
| `checked_cld(::Integer,::Integer)@33` | `intarith-checked-promotion-order` |
| `checked_abs fallback@37` | Nothing to promise |
| `checked_neg(::T<:Integer)@89` | `intarith-checked-neg-abs-exact`, `intarith-checked-bool-arithmetic`, `floatintcov-checked-l89` |
| `throw_overflowerr_negation@92` | Nothing to promise |
| `checked_neg(::BrokenSignedInt)@95` | Nothing to promise |
| `checked_neg(::BrokenUnsignedInt)@102` | Nothing to promise |
| `checked_abs(::SignedInt)@121` | `intarith-checked-neg-abs-exact`, `floatintcov-checked-l121` |
| `checked_abs(::UnsignedInt)@127` | `intarith-checked-neg-abs-exact` |
| `checked_abs(::Bool)@128` | `intarith-checked-bool-arithmetic` |
| `add_with_overflow(::SignedInt)@136` | `intarith-checked-overflow-reports-exact` |
| `add_with_overflow(::UnsignedInt)@137` | `intarith-checked-overflow-reports-exact` |
| `add_with_overflow(::Bool,::Bool)@138` | `intarith-checked-bool-arithmetic` |
| `add_with_overflow(::BrokenSignedInt)@141` | Nothing to promise |
| `add_with_overflow(::BrokenUnsignedInt)@149` | Nothing to promise |
| `throw_overflowerr_binaryop@156` | Nothing to promise |
| `checked_add same type@166` | `intarith-checked-add-sub-exact`, `intarith-checked-bool-arithmetic`, `floatintcov-checked-l166` |
| `checked_add unary@178` | Nothing to promise |
| `checked_add(::Bool)@179` | `intarith-checked-bool-arithmetic` |
| `checked_add arity 3@181` | Nothing to promise |
| `checked_add arity 4@183` | Nothing to promise |
| `checked_add arity 5@185` | Nothing to promise |
| `checked_add arity 6@187` | Nothing to promise |
| `checked_add arity 7@189` | Nothing to promise |
| `checked_add arity 8@191` | Nothing to promise |
| `sub_with_overflow(::SignedInt)@200` | `intarith-checked-overflow-reports-exact` |
| `sub_with_overflow(::UnsignedInt)@201` | `intarith-checked-overflow-reports-exact` |
| `sub_with_overflow(::Bool,::Bool)@202` | `intarith-checked-bool-arithmetic` |
| `sub_with_overflow(::BrokenSignedInt)@205` | Nothing to promise |
| `sub_with_overflow(::BrokenUnsignedInt)@213` | Nothing to promise |
| `checked_sub same type@226` | `intarith-checked-add-sub-exact`, `intarith-checked-bool-arithmetic`, `floatintcov-checked-l226` |
| `mul_with_overflow(::SignedInt)@239` | `intarith-checked-overflow-reports-exact` |
| `mul_with_overflow(::UnsignedInt)@240` | `intarith-checked-overflow-reports-exact` |
| `mul_with_overflow(::Bool,::Bool)@241` | `intarith-checked-bool-arithmetic` |
| `mul_with_overflow(::BrokenSignedIntMul)@244` | Nothing to promise |
| `mul_with_overflow(::BrokenUnsignedIntMul)@251` | Nothing to promise |
| `mul_with_overflow(::Int128)@259` | `intarith-checked-overflow-reports-exact` |
| `mul_with_overflow(::UInt128)@277` | `intarith-checked-overflow-reports-exact` |
| `checked_mul same type@290` | `intarith-checked-mul-intrinsic-exact`, `intarith-checked-bool-arithmetic` |
| `checked_mul unary@298` | Nothing to promise |
| `checked_mul arity 3@299` | Nothing to promise |
| `checked_mul arity 4@301` | Nothing to promise |
| `checked_mul arity 5@303` | Nothing to promise |
| `checked_mul arity 6@305` | Nothing to promise |
| `checked_mul arity 7@307` | Nothing to promise |
| `checked_mul arity 8@309` | Nothing to promise |
| `checked_div same type@319` | `intarith-checked-division-errors`, `intarith-checked-division-exact` |
| `checked_rem same type@328` | `intarith-checked-division-errors`, `intarith-checked-division-exact` |
| `checked_fld same type@337` | `intarith-checked-division-errors`, `intarith-checked-division-exact` |
| `checked_mod same type@346` | `intarith-checked-division-errors`, `intarith-checked-division-exact` |
| `checked_cld same type@355` | `intarith-checked-division-errors`, `intarith-checked-division-exact` |
| `checked_pow@364` | `intarith-checked-negative-pow`, `intarith-checked-power-exact` |
| `checked_power_by_squaring@366` | `intarith-checked-negative-pow`, `intarith-checked-power-exact` |
| `checked_power_by_squaring(::Bool)@368` | Nothing to promise |
| `checked_length@376` | Nothing to promise |

## Nothing to promise

Nothing to promise: `checked_abs fallback@37`; it delegates unsupported integer types to `Base.no_op_err`.
Nothing to promise: `throw_overflowerr_negation@92`; this helper constructs the error already covered by checked negation's property.
Nothing to promise: `checked_neg(::BrokenSignedInt)@95` and `checked_neg(::BrokenUnsignedInt)@102`; both dispatch unions are empty for the modeled target.
Nothing to promise: `throw_overflowerr_binaryop@156`; this helper constructs the error already covered by checked addition, subtraction, and multiplication.
Nothing to promise: `add_with_overflow(::BrokenSignedInt)@141` and `add_with_overflow(::BrokenUnsignedInt)@149`; both dispatch unions are empty for the modeled target.
Nothing to promise: `checked_add unary@178`; this is only the identity base case of the multi-argument fold.
Nothing to promise: `checked_add arity 3@181`, `checked_add arity 4@183`, `checked_add arity 5@185`, `checked_add arity 6@187`, `checked_add arity 7@189`, and `checked_add arity 8@191`; they only nest the checked binary method.
Nothing to promise: `sub_with_overflow(::BrokenSignedInt)@205` and `sub_with_overflow(::BrokenUnsignedInt)@213`; both dispatch unions are empty for the modeled target.
Nothing to promise: `mul_with_overflow(::BrokenSignedIntMul)@244` and `mul_with_overflow(::BrokenUnsignedIntMul)@251`; the generic fallback conditions exclude Int128 and UInt128 on the modeled target.
Nothing to promise: `checked_mul unary@298`; this is only the identity base case of the multi-argument fold.
Nothing to promise: `checked_mul arity 3@299`, `checked_mul arity 4@301`, `checked_mul arity 5@303`, `checked_mul arity 6@305`, `checked_mul arity 7@307`, and `checked_mul arity 8@309`; they only nest the checked binary method.
Nothing to promise: `checked_power_by_squaring(::Bool)@368`; it forwards to the ordinary Boolean power routine without checked multiplication.
Nothing to promise: `checked_length@376`; the generic fallback returns `length(r)`, while overflow-aware range lengths are supplied by methods in other Base files.
-/

/-! ## Registry -/
def entries : List JuliaLean.Registry.Entry := [
  { id := "intarith-checked-add-sub-exact", juliaFile := "base/checked.jl",
    juliaFns := ["checked_add", "checked_sub", "add_with_overflow", "sub_with_overflow"],
    statement := "All same-type inputs at every BitInteger width and Bool return the exact mathematical sum/difference or OverflowError precisely when out of range.",
    source := "base/checked.jl:130-137,159-175,194-201,219-231", status := .proven,
    prop := ``AddSubExact, thm := some ``addSubExact },
  { id := "intarith-checked-neg-abs-exact", juliaFile := "base/checked.jl",
    juliaFns := ["checked_neg", "checked_abs"],
    statement := "For arbitrary input at every width and Bool, negation and absolute value return the exact mathematical result or OverflowError precisely when out of range.",
    source := "base/checked.jl:80-128", status := .proven,
    prop := ``NegAbsExact, thm := some ``negAbsExact },
  { id := "intarith-checked-manual-mul-factors", juliaFile := "base/checked.jl",
    juliaFns := ["checked_mul", "mul_with_overflow"],
    statement := "For every Int128/UInt128 input, multiplication by converted -2,-1,0,1,2 returns the exact product or OverflowError precisely when out of range.",
    source := "base/checked.jl:257-280", status := .proven,
    prop := ``ManualSmallFactorsExact, thm := some ``manualSmallFactorsExact },
  { id := "intarith-checked-mul-intrinsic-exact", juliaFile := "base/checked.jl",
    juliaFns := ["checked_mul", "mul_with_overflow"],
    statement := "All inputs at every BitInteger width and Bool return the exact product or OverflowError precisely when out of range.",
    source := "base/checked.jl:233-241,257-295", status := .proven,
    prop := ``MulAllExact, thm := some ``mulAllExact },
  { id := "intarith-checked-boundaries", juliaFile := "base/checked.jl",
    juliaFns := ["checked_add", "checked_sub", "checked_mul", "checked_neg", "checked_abs"],
    statement := "Every width detects upper addition/product overflow and lower subtraction/negation/abs overflow; unsigned zero remains zero.",
    source := "base/checked.jl:89-128,166-175,226-280,290-295", status := .proven,
    prop := ``BoundaryArithmetic, thm := some ``boundaryArithmetic },
  { id := "intarith-checked-division-errors", juliaFile := "base/checked.jl",
    juliaFns := ["checked_div", "checked_rem", "checked_fld", "checked_mod", "checked_cld"],
    statement := "Zero division and signed typemin/-1 division throw DivideError, whereas typemin rem/mod -1 equals zero.",
    source := "base/checked.jl:312-355; base/int.jl division primitives", status := .proven,
    prop := ``DivisionBoundaries, thm := some ``divisionBoundaries },
  { id := "intarith-checked-promotion-order", juliaFile := "base/checked.jl",
    juliaFns := ["checked_add(::Integer,::Integer)", "checked_sub(::Integer,::Integer)",
      "checked_mul(::Integer,::Integer)", "checked_div(::Integer,::Integer)",
      "checked_rem(::Integer,::Integer)", "checked_fld(::Integer,::Integer)",
      "checked_mod(::Integer,::Integer)", "checked_cld(::Integer,::Integer)"],
    statement := "For every mixed fixed-width integer pair and mixed Bool/fixed-width integer pair in either order, inexact promotion returns InexactError before the operation, and successful promotion equals the same-type checked operation and produces the exact mathematical result.",
    source := "base/checked.jl:25-33", status := .proven,
    prop := ``PromotionBeforeOperation, thm := some ``promotionBeforeOperation },
  { id := "intarith-checked-negative-pow", juliaFile := "base/checked.jl",
    juliaFns := ["checked_pow", "checked_power_by_squaring"],
    statement := "A successful checked integer power with negative exponent has base +1 or -1.",
    source := "base/checked.jl:364-366; base/intfuncs.jl:388-392,418-421", status := .refuted,
    prop := ``NegativePowerUnits, thm := some ``negativePowerUnits_refuted,
    issue := "none found (issues: checked_pow unsigned negative; unsigned negative exponent; power_by_squaring typemax. PRs: power_by_squaring unsigned; checked_pow negative; negative exponent UInt)" },
  { id := "intarith-checked-overflow-reports-exact", juliaFile := "base/checked.jl",
    juliaFns := ["add_with_overflow", "sub_with_overflow", "mul_with_overflow"],
    statement := "At every BitInteger width, each overflow helper returns the wrapped exact result and sets its flag precisely when the mathematical result is out of range.",
    source := "base/checked.jl:136-154,200-217,239-281", status := .proven,
    prop := ``OverflowReportsExact, thm := some ``overflowReportsExact },
  { id := "intarith-checked-division-exact", juliaFile := "base/checked.jl",
    juliaFns := ["checked_div", "checked_rem", "checked_fld", "checked_mod", "checked_cld"],
    statement := "For every fixed-width integer pair, checked rem and mod agree with unbounded integer arithmetic, and checked div/fld/cld agree wherever their quotient fits.",
    source := "base/checked.jl:312-355; base/int.jl division primitives", status := .proven,
    prop := ``DivisionExact, thm := some ``divisionExact },
  { id := "intarith-checked-power-exact", juliaFile := "base/checked.jl",
    juliaFns := ["checked_pow", "checked_power_by_squaring"],
    statement := "For nonnegative exponents, checked power returns the exact mathematical power or OverflowError when it does not fit, assuming Base.power_by_squaring honors its checked-multiplication contract.",
    source := "base/checked.jl:357-368; base/intfuncs.jl power-by-squaring contract", status := .proven,
    prop := ``CheckedPowerExact, thm := some ``checkedPowerExact },
  { id := "intarith-checked-bool-arithmetic", juliaFile := "base/checked.jl",
    juliaFns := ["checked_neg", "checked_abs(::Bool)", "checked_add same type",
      "checked_add(::Bool)", "checked_sub same type", "checked_mul same type",
      "add_with_overflow(::Bool,::Bool)", "sub_with_overflow(::Bool,::Bool)",
      "mul_with_overflow(::Bool,::Bool)"],
    statement := "Boolean checked negation, absolute value, unary and binary checked addition, subtraction, multiplication, and overflow helpers return their exact integer or Boolean results and never report overflow.",
    source := "base/checked.jl:89,128,138,166,179,202,226,241,290", status := .proven,
    prop := ``BoolArithmeticExact, thm := some ``boolArithmeticExact },
  { id := "floatintcov-checked-l89", juliaFile := "base/checked.jl",
    juliaFns := ["checked_neg"],
    statement := "Negation returns the exact mathematical result or OverflowError at every BitInteger width and for Bool.",
    source := "base/checked.jl:89", status := .proven,
    prop := ``NegAllExact, thm := some ``negAllExact },
  { id := "floatintcov-checked-l121", juliaFile := "base/checked.jl",
    juliaFns := ["checked_abs(::SignedInt)"],
    statement := "Signed absolute value returns the exact magnitude or OverflowError when the magnitude is out of range.",
    source := "base/checked.jl:121-126", status := .proven,
    prop := ``AbsExact, thm := some ``absExact },
  { id := "floatintcov-checked-l166", juliaFile := "base/checked.jl",
    juliaFns := ["checked_add same type"],
    statement := "Same-type checked addition returns the mathematical sum or OverflowError when it is out of range, including Bool.",
    source := "base/checked.jl:166-175", status := .proven,
    prop := ``AddAllExact, thm := some ``addAllExact },
  { id := "floatintcov-checked-l226", juliaFile := "base/checked.jl",
    juliaFns := ["checked_sub same type"],
    statement := "Same-type checked subtraction returns the mathematical difference or OverflowError when it is out of range, including Bool.",
    source := "base/checked.jl:226-231", status := .proven,
    prop := ``SubAllExact, thm := some ``subAllExact }
]

end JuliaLean.Proofs.base.checked
