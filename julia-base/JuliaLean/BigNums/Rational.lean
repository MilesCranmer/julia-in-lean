import JuliaLean.Promotion.IEEE
import JuliaLean.BigNums.Int
import JuliaLean.BigNums.Proofs.Convert

/-!
`Rational{BigInt}` comparison and float conversion at master
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`
(`base/gmp.jl:958-1125`, `base/mpfr.jl:565-571`).

Finite operands are compared by GMP and the result is reduced to its sign.
Infinite operands are handled before calling GMP. The model of GMP 6.3's
`mpq_cmp_numden` retains `none` for its undefined zero-denominator path.
-/

namespace JuliaLean.BigNums

open JuliaLean JuliaLean.Promotion

/-- A `Rational{BigInt}` as Julia stores it: `den ≥ 0`, coprime components, and `±1//0` for the
infinities. -/
structure QBig where
  num : Int
  den : Nat
  deriving DecidableEq, Repr

/-- `count_leading_zeros` of a nonzero 64-bit limb. -/
def clz (w : Nat) : Nat := 64 - (w.log2 + 1)

/-- The most significant limb of `abs(x)` (`PTR(x)[size - 1]`), for `x ≠ 0`. -/
def topLimb (x : Int) : Nat := limb x (nlimbs x - 1)

/-- `mpq_cmp(op1, op2)` as implemented in GMP 6.3 `mpq/cmp.c` (`mpq_cmp_numden`). -/
def mpqCmp (a b : QBig) : Option Int :=
  let n1 := size a.num
  let n2 := size b.num
  let d1 := nlimbs a.den
  let d2 := nlimbs b.den
  if n1 = 0 then some (-n2)
  else if n2 = 0 then some n1
  else if decide (n1 < 0) != decide (n2 < 0) then some n1
  else if d1 = 0 ∨ d2 = 0 then none
  else
    let sign1 := n1
    let a1 := n1.natAbs
    let d1h := topLimb a.den
    let d2h := topLimb b.den
    let op2Int := d2 = 1 ∧ d2h = 1
    let op1Int := d1 = 1 ∧ d1h = 1
    if op2Int ∧ op1Int then
      if sign1 ≠ n2 then some (if sign1 > n2 then 1 else -1)
      else
        let c : Int := if a.num.natAbs < b.num.natAbs then -1
          else if a.num.natAbs = b.num.natAbs then 0 else 1
        some (if sign1 > 0 then c else -c)
    else
      let a2 := n2.natAbs
      let oi : Nat := if op2Int then 1 else 0
      let t1 := a1 + d2
      let t2 := a2 + d1
      if t1 > t2 + 1 then some sign1
      else if t2 + oi > t1 + 1 then some (-sign1)
      else
        let bits1 := t1 * 64 - clz (topLimb a.num) - clz d2h
        let bits2 := t2 * 64 - clz (topLimb b.num) - clz d1h
        if bits1 > bits2 + 1 then some sign1
        else if bits2 + oi > bits1 + 1 then some (-sign1)
        else
          -- step 3: exact cross products; `cc` is their limb-count difference or `mpn_cmp`
          let p1 := a.num.natAbs * b.den
          let p2 := b.num.natAbs * a.den
          let s1 : Int := nlimbs p1
          let s2 : Int := nlimbs p2
          let cc : Int := if s1 ≠ s2 then s1 - s2
            else if p1 < p2 then -1 else if p1 = p2 then 0 else 1
          some (if sign1 < 0 then -cc else cc)

/-- `cmp(x::Rational{BigInt}, y::Rational{BigInt})`, `base/gmp.jl:1116-1124`. -/
def cmpQ (a b : QBig) : Option Int :=
  if a.den = 0 then
    if b.den = 0 then
      some (if b.num < 0 then (if a.num < 0 then 0 else 1)
            else if a.num < 0 then -1 else 0)
    else some (if a.num < 0 then -1 else 1)
  else if b.den = 0 then some (if b.num < 0 then 1 else -1)
  else (mpqCmp a b).map Int.sign

/-- The order of `Rational` values, with `±1//0` the infinities (`base/rational.jl`). -/
def qOrder (a b : QBig) : Int :=
  let l := a.num * b.den
  let r := b.num * a.den
  if a.den = 0 ∧ b.den = 0 then (if a.num < b.num then -1 else if a.num = b.num then 0 else 1)
  else if l < r then -1 else if l = r then 0 else 1

/-- Valid states constructed by Julia's rational constructors (`base/rational.jl:20-44`,
`base/gmp.jl:1004-1011`). `unsafe_rational` bypasses those checks; arbitrary
unchecked states are outside this contract. -/
def QBig.normalized (q : QBig) : Prop :=
  (0 < q.den ∧ Nat.gcd q.num.natAbs q.den = 1) ∨ (q.den = 0 ∧ (q.num = 1 ∨ q.num = -1))

/-- `cmp` on valid `Rational{BigInt}` values returns `-1`, `0` or `1`
(`base/operators.jl:508-511`), including infinite values. -/
def RationalCmpUnit : Prop :=
  ∀ a b : QBig, a.normalized → b.normalized →
    ∃ c, cmpQ a b = some c ∧ (c = -1 ∨ c = 0 ∨ c = 1)

private theorem isSome_ite (p : Prop) [Decidable p] (a b : Option Int) :
    (if p then a else b).isSome = (if p then a.isSome else b.isSome) := by
  split <;> rfl

private theorem isSome_some (x : Int) : (some x).isSome = true := rfl

theorem mpqCmp_finite_defined (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den) :
    ∃ c, mpqCmp a b = some c := by
  have da : nlimbs (a.den : Int) ≠ 0 := by
    simp [nlimbs, show a.den ≠ 0 by omega]
  have db : nlimbs (b.den : Int) ≠ 0 := by
    simp [nlimbs, show b.den ≠ 0 by omega]
  have present : (mpqCmp a b).isSome = true := by
    simp only [mpqCmp, da, db, or_self, if_false, isSome_ite, isSome_some, ite_self]
  cases h : mpqCmp a b with
  | some c => exact ⟨c, rfl⟩
  | none => simp [h] at present

theorem rationalCmpUnit_proven : RationalCmpUnit := by
  intro a b _ _
  by_cases ha : a.den = 0
  · by_cases hb : b.den = 0
    · simp only [cmpQ, ha, hb, if_true]
      split <;> split <;> simp
    · simp only [cmpQ, ha, hb, if_true, if_false]
      split <;> simp
  · by_cases hb : b.den = 0
    · simp only [cmpQ, ha, hb, if_true, if_false]
      split <;> simp
    · obtain ⟨c, hc⟩ := mpqCmp_finite_defined a b (by omega) (by omega)
      refine ⟨c.sign, ?_, ?_⟩
      · simp [cmpQ, ha, hb, hc]
      · cases c with
        | ofNat n => cases n <;> simp [Int.sign]
        | negSucc n => simp [Int.sign]

/-- The prior source returned GMP's comparison result without normalization. -/
def LegacyRationalCmpUnit : Prop :=
  ∀ a b : QBig, 0 < a.den → 0 < b.den → a.normalized → b.normalized →
    ∃ c, mpqCmp a b = some c ∧ (c = -1 ∨ c = 0 ∨ c = 1)

theorem rationalCmpUnit_refuted : ¬ LegacyRationalCmpUnit := by
  intro h
  obtain ⟨c, hc, h1⟩ := h ⟨0, 1⟩ ⟨2 ^ 200, 1⟩ (by decide) (by decide)
    (Or.inl ⟨by decide, by decide⟩) (Or.inl ⟨by decide, by decide⟩)
  have : mpqCmp ⟨0, 1⟩ ⟨2 ^ 200, 1⟩ = some (-4) := by decide +kernel
  rw [this] at hc
  cases hc
  omega


/-- Limb counts preserve the order of nonnegative magnitudes. -/
theorem nlimbs_nat_mono {a b : Nat} (h : a ≤ b) :
    nlimbs (a : Int) ≤ nlimbs (b : Int) := by
  apply (ConvProofs.nlimbs_le_iff (a : Int) (nlimbs (b : Int))).2
  have hb := (ConvProofs.nlimbs_le_iff (b : Int) (nlimbs (b : Int))).1 (Nat.le_refl _)
  change b < 2 ^ (64 * nlimbs (b : Int)) at hb
  change a < 2 ^ (64 * nlimbs (b : Int))
  omega
/-- A strict difference in limb counts implies the same strict magnitude order. -/
theorem lt_of_nlimbs_lt {a b : Nat}
    (h : nlimbs (a : Int) < nlimbs (b : Int)) : a < b := by
  have hm := nlimbs_nat_mono (a := b) (b := a)
  omega

/-- Every nonzero magnitude lies between the powers of two surrounding its limb count. -/
theorem nlimbs_bounds (a : Nat) (ha : a ≠ 0) :
    2 ^ (64 * (nlimbs (a : Int) - 1)) ≤ a ∧
      a < 2 ^ (64 * nlimbs (a : Int)) := by
  have hp : 0 < nlimbs (a : Int) := ConvProofs.nlimbs_pos _ (by omega)
  have hu := (ConvProofs.nlimbs_le_iff (a : Int) (nlimbs (a : Int))).1 (Nat.le_refl _)
  have hl : ¬ nlimbs (a : Int) ≤ nlimbs (a : Int) - 1 := by omega
  have hl' := mt (ConvProofs.nlimbs_le_iff (a : Int) (nlimbs (a : Int) - 1)).2 hl
  change a < 2 ^ (64 * nlimbs (a : Int)) at hu
  change ¬ a < 2 ^ (64 * (nlimbs (a : Int) - 1)) at hl'
  omega

/-- The most significant limb of a nonzero magnitude is a nonzero 64-bit word. -/
theorem topLimb_bounds (a : Nat) (ha : a ≠ 0) :
    0 < topLimb (a : Int) ∧ topLimb (a : Int) < 2 ^ 64 := by
  obtain ⟨hl, hu⟩ := nlimbs_bounds a ha
  have hn := ConvProofs.nlimbs_pos (a : Int) (by omega)
  let k := 64 * (nlimbs (a : Int) - 1)
  have hk : 0 < 2 ^ k := Nat.two_pow_pos _
  have hexp : 64 * nlimbs (a : Int) = 64 + k := by dsimp [k]; omega
  rw [hexp, Nat.pow_add] at hu
  have hdiv : a / 2 ^ k < 2 ^ 64 := (Nat.div_lt_iff_lt_mul hk).2 hu
  have hpos : 0 < a / 2 ^ k := Nat.div_pos hl hk
  change 0 < (a / 2 ^ k % 2 ^ 64) ∧ a / 2 ^ k % 2 ^ 64 < 2 ^ 64
  rw [Nat.mod_eq_of_lt hdiv]
  exact ⟨hpos, hdiv⟩

/-- The top limb contains exactly the high bits of a nonzero magnitude. -/
theorem topLimb_log2 (a : Nat) (ha : a ≠ 0) :
    a.log2 = 64 * (nlimbs (a : Int) - 1) + (topLimb (a : Int)).log2 := by
  obtain ⟨hl, hu⟩ := nlimbs_bounds a ha
  have hn := ConvProofs.nlimbs_pos (a : Int) (by omega)
  let k := 64 * (nlimbs (a : Int) - 1)
  have hk : 0 < 2 ^ k := Nat.two_pow_pos _
  have hexp : 64 * nlimbs (a : Int) = 64 + k := by dsimp [k]; omega
  rw [hexp, Nat.pow_add] at hu
  have hdiv : a / 2 ^ k < 2 ^ 64 := (Nat.div_lt_iff_lt_mul hk).2 hu
  have hpos : 0 < a / 2 ^ k := Nat.div_pos hl hk
  have htop : topLimb (a : Int) = a / 2 ^ k := by
    change a / 2 ^ k % 2 ^ 64 = a / 2 ^ k
    exact Nat.mod_eq_of_lt hdiv
  rw [htop]
  apply (Nat.log2_eq_iff ha).2
  have hlow := (Nat.le_div_iff_mul_le hk).1 (Nat.log2_self_le (by omega : a / 2 ^ k ≠ 0))
  have hhigh := (Nat.div_lt_iff_lt_mul hk).1
    ((Nat.log2_lt (by omega : a / 2 ^ k ≠ 0)).1
      (show (a / 2 ^ k).log2 < (a / 2 ^ k).log2 + 1 by omega))
  constructor
  · rw [Nat.pow_add, Nat.mul_comm]; exact hlow
  · have he : k + (a / 2 ^ k).log2 + 1 = ((a / 2 ^ k).log2 + 1) + k := by omega
    rw [he, Nat.pow_add]
    exact hhigh

/-- GMP's top-limb estimate is the sum of the operands' exact bit lengths. -/
theorem limb_bit_sum (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
    (nlimbs (a : Int) + nlimbs (b : Int)) * 64 -
        clz (topLimb (a : Int)) - clz (topLimb (b : Int)) =
      (a.log2 + 1) + (b.log2 + 1) := by
  obtain ⟨ap, ab⟩ := topLimb_bounds a ha
  obtain ⟨bp, bb⟩ := topLimb_bounds b hb
  have an := ConvProofs.nlimbs_pos (a : Int) (by omega)
  have bn := ConvProofs.nlimbs_pos (b : Int) (by omega)
  have al := (Nat.log2_lt (by omega : topLimb (a : Int) ≠ 0)).2 ab
  have bl := (Nat.log2_lt (by omega : topLimb (b : Int) ≠ 0)).2 bb
  have ae := topLimb_log2 a ha
  have be := topLimb_log2 b hb
  unfold clz
  omega

/-- GMP's one-limb integer test identifies denominator one. -/
theorem one_limb_top_one (a : Nat)
    (hsize : nlimbs (a : Int) = 1) (htop : topLimb (a : Int) = 1) : a = 1 := by
  have hb := (ConvProofs.nlimbs_le_iff (a : Int) 1).1 (by omega)
  change a < 2 ^ (64 * 1) at hb
  simp only [Nat.mul_one] at hb
  change a / 2 ^ (64 * (nlimbs (a : Int) - 1)) % 2 ^ 64 = 1 at htop
  simp [hsize, Nat.mod_eq_of_lt hb] at htop
  exact htop

/-- GMP's limb-count early exit orders the full products when the counts are separated. -/
theorem product_lt_of_limb_gap (a b c d : Nat) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : nlimbs (a : Int) + nlimbs (b : Int) >
      nlimbs (c : Int) + nlimbs (d : Int) + 1) : c * d < a * b := by
  obtain ⟨al, _⟩ := nlimbs_bounds a ha
  obtain ⟨bl, _⟩ := nlimbs_bounds b hb
  have ap := ConvProofs.nlimbs_pos (a : Int) (by omega)
  have bp := ConvProofs.nlimbs_pos (b : Int) (by omega)
  have cu := (ConvProofs.nlimbs_le_iff (c : Int) (nlimbs (c : Int))).1 (Nat.le_refl _)
  have du := (ConvProofs.nlimbs_le_iff (d : Int) (nlimbs (d : Int))).1 (Nat.le_refl _)
  change c < 2 ^ (64 * nlimbs (c : Int)) at cu
  change d < 2 ^ (64 * nlimbs (d : Int)) at du
  have hm := Nat.mul_lt_mul_of_lt_of_lt cu du
  have hn := Nat.mul_le_mul al bl
  have he : 64 * nlimbs (c : Int) + 64 * nlimbs (d : Int) ≤
      64 * (nlimbs (a : Int) - 1) + 64 * (nlimbs (b : Int) - 1) := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) he
  simp only [Nat.pow_add] at hp
  omega

/-- A denominator of one saves a limb in GMP's second limb-count test. -/
theorem lt_product_of_limb_gap_one (a b c : Nat) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : nlimbs (b : Int) + nlimbs (c : Int) > nlimbs (a : Int) + 1) :
    a < b * c := by
  obtain ⟨bl, _⟩ := nlimbs_bounds b hb
  obtain ⟨cl, _⟩ := nlimbs_bounds c hc
  have bp := ConvProofs.nlimbs_pos (b : Int) (by omega)
  have cp := ConvProofs.nlimbs_pos (c : Int) (by omega)
  have au := (ConvProofs.nlimbs_le_iff (a : Int) (nlimbs (a : Int))).1 (Nat.le_refl _)
  change a < 2 ^ (64 * nlimbs (a : Int)) at au
  have hn := Nat.mul_le_mul bl cl
  have he : 64 * nlimbs (a : Int) ≤
      64 * (nlimbs (b : Int) - 1) + 64 * (nlimbs (c : Int) - 1) := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) he
  rw [Nat.pow_add] at hp
  omega

/-- A two-bit gap between sums of operand bit lengths orders the exact products. -/
theorem product_lt_of_log2_gap (a b c d : Nat) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (h : a.log2 + b.log2 > c.log2 + d.log2 + 1) : c * d < a * b := by
  have al := Nat.log2_self_le ha
  have bl := Nat.log2_self_le hb
  have cu := (Nat.log2_lt hc).1 (show c.log2 < c.log2 + 1 by omega)
  have du := (Nat.log2_lt hd).1 (show d.log2 < d.log2 + 1 by omega)
  have hm := Nat.mul_lt_mul_of_lt_of_lt cu du
  have hn := Nat.mul_le_mul al bl
  have he : (c.log2 + 1) + (d.log2 + 1) ≤ a.log2 + b.log2 := by omega
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) he
  have hm' : c * d < 2 ^ ((c.log2 + 1) + (d.log2 + 1)) := by
    simpa only [Nat.pow_add] using hm
  have hn' : 2 ^ (a.log2 + b.log2) ≤ a * b := by
    simpa only [Nat.pow_add] using hn
  omega

/-- With a unit denominator, a one-bit gap already orders the products. -/
theorem lt_product_of_log2_gap_one (a b c : Nat) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (h : b.log2 + c.log2 > a.log2) : a < b * c := by
  have al := (Nat.log2_lt ha).1 (show a.log2 < a.log2 + 1 by omega)
  have bl := Nat.log2_self_le hb
  have cl := Nat.log2_self_le hc
  have hp := Nat.pow_le_pow_right (n := 2) (by decide)
    (show a.log2 + 1 ≤ b.log2 + c.log2 by omega)
  have hm : 2 ^ (b.log2 + c.log2) ≤ b * c := by
    simpa only [Nat.pow_add] using Nat.mul_le_mul bl cl
  omega

/-- The sign of the GMP size field is the sign of the integer. -/
theorem size_sign (x : Int) : (size x).sign = x.sign := by
  by_cases hx : x = 0
  · subst x; rfl
  · have hp := ConvProofs.nlimbs_pos x hx
    rcases Int.lt_or_gt_of_ne hx with hn | hn
    · have hs : size x < 0 := by simp [size, hn]; omega
      rw [Int.sign_eq_neg_one_of_neg hs, Int.sign_eq_neg_one_of_neg hn]
    · have hs : 0 < size x := by simp [size, show ¬ x < 0 by omega]; omega
      rw [Int.sign_eq_one_of_pos hs, Int.sign_eq_one_of_pos hn]

/-- The early limb-count tests order the cross-products, including the unit-denominator case. -/
theorem cross_products_limb_thresholds (a b d e : Nat)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    (nlimbs (a : Int) + nlimbs (e : Int) >
      nlimbs (b : Int) + nlimbs (d : Int) + 1 → b * d < a * e) ∧
    (nlimbs (b : Int) + nlimbs (d : Int) +
      (if nlimbs (e : Int) = 1 ∧ topLimb (e : Int) = 1 then 1 else 0) >
      nlimbs (a : Int) + nlimbs (e : Int) + 1 → a * e < b * d) := by
  constructor
  · exact product_lt_of_limb_gap a e b d ha he
  · intro h
    split at h
    · rename_i hunit
      have heq : e = 1 := one_limb_top_one e hunit.1 hunit.2
      subst e
      simpa using lt_product_of_limb_gap_one a b d hb hd (by omega)
    · exact product_lt_of_limb_gap b d a e hb hd (by omega)

/-- The early top-limb bit tests order the same cross-products. -/
theorem cross_products_bit_thresholds (a b d e : Nat)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    let bits1 := (nlimbs (a : Int) + nlimbs (e : Int)) * 64 -
      clz (topLimb (a : Int)) - clz (topLimb (e : Int))
    let bits2 := (nlimbs (b : Int) + nlimbs (d : Int)) * 64 -
      clz (topLimb (b : Int)) - clz (topLimb (d : Int))
    (bits1 > bits2 + 1 → b * d < a * e) ∧
    (bits2 + (if nlimbs (e : Int) = 1 ∧ topLimb (e : Int) = 1 then 1 else 0) >
      bits1 + 1 → a * e < b * d) := by
  dsimp only
  rw [limb_bit_sum a e ha he, limb_bit_sum b d hb hd]
  constructor
  · intro h
    exact product_lt_of_log2_gap a e b d ha he hb hd (by omega)
  · intro h
    split at h
    · rename_i hunit
      have heq : e = 1 := one_limb_top_one e hunit.1 hunit.2
      subst e
      have hlog : Nat.log2 1 = 0 := by decide
      rw [hlog] at h
      simpa using lt_product_of_log2_gap_one a b d ha hb hd (by omega)
    · exact product_lt_of_log2_gap b d a e hb hd ha he (by omega)

theorem size_nat (a : Nat) : size (a : Int) = (nlimbs (a : Int) : Int) := by
  simp [size, show ¬ (a : Int) < 0 by omega]

theorem size_nat_abs (a : Int) : (size a).natAbs = nlimbs a := by
  unfold size
  split <;> simp

theorem nlimbs_natAbs (a : Int) : nlimbs (a.natAbs : Int) = nlimbs a := by
  unfold nlimbs
  by_cases h : a = 0
  · simp [h]
  · have hn : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr h
    simp [h, hn]

theorem topLimb_natAbs (a : Int) : topLimb (a.natAbs : Int) = topLimb a := by
  simp [topLimb, limb, nlimbs_natAbs]

/-- A finite rational order is the sign of the difference of cross-products. -/
theorem qOrder_finite_sign (a b : QBig) (ha : a.den ≠ 0) (hb : b.den ≠ 0) :
    qOrder a b = (a.num * b.den - b.num * a.den).sign := by
  unfold qOrder
  simp only [ha, hb, false_and, ite_false]
  by_cases hlt : a.num * b.den < b.num * a.den
  · simp [hlt, Int.sign_eq_neg_one_of_neg (show a.num * b.den - b.num * a.den < 0 by omega)]
  · by_cases heq : a.num * b.den = b.num * a.den
    · simp [heq]
    · simp [hlt, heq, Int.sign_eq_one_of_pos
        (show 0 < a.num * b.den - b.num * a.den by omega)]

/-- Equal numerator signs factor out of the signed cross-product difference. -/
theorem qOrder_same_sign (a b : QBig) (ha : a.den ≠ 0) (hb : b.den ≠ 0)
    (hs : a.num.sign = b.num.sign) :
    qOrder a b = a.num.sign *
      (((a.num.natAbs * b.den : Nat) : Int) - ((b.num.natAbs * a.den : Nat) : Int)).sign := by
  rw [qOrder_finite_sign a b ha hb]
  have ae := Int.sign_mul_natAbs a.num
  have be := Int.sign_mul_natAbs b.num
  rw [← hs] at be
  have he : a.num * b.den - b.num * a.den =
      a.num.sign * (((a.num.natAbs * b.den : Nat) : Int) -
        ((b.num.natAbs * a.den : Nat) : Int)) := by
    calc
      _ = (a.num.sign * a.num.natAbs) * b.den -
          (a.num.sign * b.num.natAbs) * a.den := by rw [ae, be]
      _ = _ := by simp [Int.natCast_mul, Int.mul_sub, Int.mul_assoc]
  rw [he, Int.sign_mul, Int.sign_sign]

/-- The zero-numerator branch agrees with finite cross-product order. -/
theorem rationalCmp_zero_left (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den)
    (hz : a.num = 0) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  have hda : a.den ≠ 0 := by omega
  have hdb : b.den ≠ 0 := by omega
  have hs : (a.den : Int).sign = 1 := Int.sign_eq_one_of_pos (by omega)
  refine ⟨(-size b.num).sign, ?_, ?_⟩
  · simp [cmpQ, hda, hdb, mpqCmp, hz, size, nlimbs]
  · rw [qOrder_finite_sign a b hda hdb]
    simp [hz, size_sign, hs]

/-- The second zero-numerator branch agrees with finite cross-product order. -/
theorem rationalCmp_zero_right (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den)
    (haz : a.num ≠ 0) (hbz : b.num = 0) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  have hda : a.den ≠ 0 := by omega
  have hdb : b.den ≠ 0 := by omega
  have hs : (b.den : Int).sign = 1 := Int.sign_eq_one_of_pos (by omega)
  have hn : size a.num ≠ 0 := by
    have hp := ConvProofs.nlimbs_pos a.num haz
    unfold size
    split <;> omega
  refine ⟨(size a.num).sign, ?_, ?_⟩
  · simp [cmpQ, hda, hdb, mpqCmp, hbz, hn, show size 0 = 0 by rfl]
  · rw [qOrder_finite_sign a b hda hdb]
    simp [hbz, size_sign, hs]

/-- Opposite-sign finite numerators are ordered before GMP multiplies. -/
theorem rationalCmp_opposite_sign (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den)
    (hop : (a.num < 0 ∧ 0 < b.num) ∨ (0 < a.num ∧ b.num < 0)) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  have hda : a.den ≠ 0 := by omega
  have hdb : b.den ≠ 0 := by omega
  have hpa : 0 < (a.den : Int) := by omega
  have hpb : 0 < (b.den : Int) := by omega
  have hsz : ∀ x : Int, x ≠ 0 → size x ≠ 0 := by
    intro x hx
    have hp := ConvProofs.nlimbs_pos x hx
    unfold size
    split <;> omega
  rcases hop with ⟨han, hbp⟩ | ⟨hap, hbn⟩
  · have hsa : size a.num < 0 := by
      have hp := ConvProofs.nlimbs_pos a.num (by omega)
      simp [size, han]; omega
    have hsb : 0 < size b.num := by
      have hp := ConvProofs.nlimbs_pos b.num (by omega)
      simp [size, show ¬ b.num < 0 by omega]; omega
    have hl : a.num * b.den < 0 := Int.mul_neg_of_neg_of_pos han hpb
    have hr : 0 < b.num * a.den := Int.mul_pos hbp hpa
    refine ⟨(size a.num).sign, ?_, ?_⟩
    · simp [cmpQ, hda, hdb, mpqCmp, hsz a.num (by omega), hsz b.num (by omega),
        show size a.num < 0 by omega, show ¬ size b.num < 0 by omega]
    · rw [qOrder_finite_sign a b hda hdb]
      simp [Int.sign_eq_neg_one_of_neg hsa,
        Int.sign_eq_neg_one_of_neg (show a.num * b.den - b.num * a.den < 0 by omega)]
  · have hsa : 0 < size a.num := by
      have hp := ConvProofs.nlimbs_pos a.num (by omega)
      simp [size, show ¬ a.num < 0 by omega]; omega
    have hsb : size b.num < 0 := by
      have hp := ConvProofs.nlimbs_pos b.num (by omega)
      simp [size, hbn]; omega
    have hl : 0 < a.num * b.den := Int.mul_pos hap hpb
    have hr : b.num * a.den < 0 := Int.mul_neg_of_neg_of_pos hbn hpa
    refine ⟨(size a.num).sign, ?_, ?_⟩
    · simp [cmpQ, hda, hdb, mpqCmp, hsz a.num (by omega), hsz b.num (by omega),
        show ¬ size a.num < 0 by omega, show size b.num < 0 by omega]
    · rw [qOrder_finite_sign a b hda hdb]
      simp [Int.sign_eq_one_of_pos hsa,
        Int.sign_eq_one_of_pos (show 0 < a.num * b.den - b.num * a.den by omega)]


/-- GMP's exact-product limb-count shortcut has the same sign as comparing the products. -/
theorem product_limb_compare_sign (a b : Nat) :
    (if (nlimbs (a : Int) : Int) ≠ (nlimbs (b : Int) : Int) then
      (nlimbs (a : Int) : Int) - (nlimbs (b : Int) : Int)
    else if a < b then -1 else if a = b then 0 else 1).sign =
      (if a < b then (-1 : Int) else if a = b then 0 else 1) := by
  have hab : a ≤ b → nlimbs (a : Int) ≤ nlimbs (b : Int) := nlimbs_nat_mono
  have hba : b ≤ a → nlimbs (b : Int) ≤ nlimbs (a : Int) := nlimbs_nat_mono
  by_cases hl : (nlimbs (a : Int) : Int) ≠ (nlimbs (b : Int) : Int)
  · by_cases hlt : a < b
    · have hn := hab (by omega)
      have hs : (nlimbs (a : Int) : Int) - (nlimbs (b : Int) : Int) < 0 := by omega
      simp [hl, hlt, Int.sign_eq_neg_one_of_neg hs]
    · have hn := hba (by omega)
      have hs : 0 < (nlimbs (a : Int) : Int) - (nlimbs (b : Int) : Int) := by omega
      have hne : a ≠ b := by intro h; subst b; exact hl rfl
      simp [hl, hlt, hne, Int.sign_eq_one_of_pos hs]
  · by_cases hlt : a < b <;> by_cases heq : a = b <;>
      simp [hl, hlt, heq, Int.sign] <;> decide

theorem product_limb_compare_difference_sign (a b : Nat) :
    (if (nlimbs (a : Int) : Int) ≠ (nlimbs (b : Int) : Int) then
      (nlimbs (a : Int) : Int) - (nlimbs (b : Int) : Int)
    else if a < b then -1 else if a = b then 0 else 1).sign =
      ((a : Int) - (b : Int)).sign := by
  rw [product_limb_compare_sign]
  by_cases hl : a < b
  · simp [hl, Int.sign_eq_neg_one_of_neg (show (a : Int) - b < 0 by omega)]
  · by_cases he : a = b
    · simp [he]
    · simp [hl, he, Int.sign_eq_one_of_pos (show 0 < (a : Int) - b by omega)]

/-- GMP applies the numerator sign to an unsigned comparison result. -/
theorem sign_conditional_neg (s x : Int) (hs : s ≠ 0) :
    (if s < 0 then -x else x).sign = s.sign * x.sign := by
  rcases Int.lt_or_gt_of_ne hs with hn | hp
  · simp [hn, Int.sign_eq_neg_one_of_neg hn]
  · simp [show ¬ s < 0 by omega, Int.sign_eq_one_of_pos hp]

/-- Comparing integer operands by limb count, then magnitude, gives their difference sign. -/
theorem integer_limb_compare_sign (a b : Nat) :
    (if nlimbs (a : Int) ≠ nlimbs (b : Int) then
      (if nlimbs (a : Int) > nlimbs (b : Int) then (1 : Int) else -1)
    else if a < b then -1 else if a = b then 0 else 1) =
      ((a : Int) - (b : Int)).sign := by
  have hab : a ≤ b → nlimbs (a : Int) ≤ nlimbs (b : Int) := nlimbs_nat_mono
  have hba : b ≤ a → nlimbs (b : Int) ≤ nlimbs (a : Int) := nlimbs_nat_mono
  by_cases hn : nlimbs (a : Int) ≠ nlimbs (b : Int)
  · by_cases hg : nlimbs (a : Int) > nlimbs (b : Int)
    · have hp : 0 < (a : Int) - b := by
        have hm := hba
        omega
      simp [hn, hg, Int.sign_eq_one_of_pos hp]
    · have hp : (a : Int) - b < 0 := by
        have hm := hab
        omega
      simp [hn, hg, Int.sign_eq_neg_one_of_neg hp]
  · by_cases hl : a < b
    · simp [hn, hl, Int.sign_eq_neg_one_of_neg (show (a : Int) - b < 0 by omega)]
    · by_cases he : a = b
      · simp [he]
      · simp [hn, hl, he, Int.sign_eq_one_of_pos (show 0 < (a : Int) - b by omega)]

/-- GMP's final exact-product branch agrees with rational order. -/
theorem rationalCmp_exact_products (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den)
    (hna : size a.num ≠ 0) (hnb : size b.num ≠ 0)
    (hs : a.num.sign = b.num.sign)
    (hsgn : (decide (size a.num < 0) != decide (size b.num < 0)) = false)
    (hint : ¬ ((nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1) ∧
      (nlimbs (a.den : Int) = 1 ∧ topLimb (a.den : Int) = 1)))
    (hg1 : ¬ ((size a.num).natAbs + nlimbs (b.den : Int) >
      (size b.num).natAbs + nlimbs (a.den : Int) + 1))
    (hg2 : ¬ ((size b.num).natAbs + nlimbs (a.den : Int) +
      (if nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1 then 1 else 0) >
      (size a.num).natAbs + nlimbs (b.den : Int) + 1))
    (hb1 : ¬ (((size a.num).natAbs + nlimbs (b.den : Int)) * 64 -
      clz (topLimb a.num) - clz (topLimb (b.den : Int)) >
      ((size b.num).natAbs + nlimbs (a.den : Int)) * 64 -
      clz (topLimb b.num) - clz (topLimb (a.den : Int)) + 1))
    (hb2 : ¬ (((size b.num).natAbs + nlimbs (a.den : Int)) * 64 -
      clz (topLimb b.num) - clz (topLimb (a.den : Int)) +
      (if nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1 then 1 else 0) >
      ((size a.num).natAbs + nlimbs (b.den : Int)) * 64 -
      clz (topLimb a.num) - clz (topLimb (b.den : Int)) + 1)) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  have hda : a.den ≠ 0 := by omega
  have hdb : b.den ≠ 0 := by omega
  have hla : nlimbs (a.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (a.den : Int) (by omega)
    omega
  have hlb : nlimbs (b.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (b.den : Int) (by omega)
    omega
  let x := a.num.natAbs * b.den
  let y := b.num.natAbs * a.den
  let cc : Int := if (nlimbs (x : Int) : Int) ≠ (nlimbs (y : Int) : Int) then
    (nlimbs (x : Int) : Int) - (nlimbs (y : Int) : Int)
    else if x < y then -1 else if x = y then 0 else 1
  refine ⟨(if size a.num < 0 then -cc else cc).sign, ?_, ?_⟩
  · simp [cmpQ, hda, hdb, mpqCmp, hna, hnb, hsgn, hla, hlb, hint,
      hg1, hg2, hb1, hb2, x, y, cc]
  · rw [Int.sign_sign, sign_conditional_neg _ _ hna, size_sign,
      qOrder_same_sign a b hda hdb hs]
    congr 1
    exact product_limb_compare_difference_sign x y

/-- The first GMP limb-count shortcut agrees with rational order. -/
theorem rationalCmp_first_limb_gap (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den)
    (hna : size a.num ≠ 0) (hnb : size b.num ≠ 0)
    (hs : a.num.sign = b.num.sign)
    (hsgn : (decide (size a.num < 0) != decide (size b.num < 0)) = false)
    (hint : ¬ ((nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1) ∧
      (nlimbs (a.den : Int) = 1 ∧ topLimb (a.den : Int) = 1)))
    (hg : (size a.num).natAbs + nlimbs (b.den : Int) >
      (size b.num).natAbs + nlimbs (a.den : Int) + 1) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  have hda : a.den ≠ 0 := by omega
  have hdb : b.den ≠ 0 := by omega
  have hla : nlimbs (a.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (a.den : Int) (by omega)
    omega
  have hlb : nlimbs (b.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (b.den : Int) (by omega)
    omega
  have haz : a.num ≠ 0 := by intro h; apply hna; rw [h]; rfl
  have hbz : b.num ≠ 0 := by intro h; apply hnb; rw [h]; rfl
  have hg' : nlimbs (a.num.natAbs : Int) + nlimbs (b.den : Int) >
      nlimbs (b.num.natAbs : Int) + nlimbs (a.den : Int) + 1 := by
    simpa [size_nat_abs, nlimbs_natAbs] using hg
  have hp := (cross_products_limb_thresholds a.num.natAbs b.num.natAbs a.den b.den
    (Int.natAbs_ne_zero.mpr haz) (Int.natAbs_ne_zero.mpr hbz) hda hdb).1 hg'
  have hdiff : 0 < ((a.num.natAbs * b.den : Nat) : Int) -
      ((b.num.natAbs * a.den : Nat) : Int) := by omega
  refine ⟨(size a.num).sign, ?_, ?_⟩
  · simp [cmpQ, hda, hdb, mpqCmp, hna, hnb, hsgn, hla, hlb, hint, hg]
  · rw [Int.sign_sign, size_sign, qOrder_same_sign a b hda hdb hs,
      Int.sign_eq_one_of_pos hdiff, Int.mul_one]

/-- The second GMP limb-count shortcut agrees with rational order. -/
theorem rationalCmp_second_limb_gap (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den)
    (hna : size a.num ≠ 0) (hnb : size b.num ≠ 0)
    (hs : a.num.sign = b.num.sign)
    (hsgn : (decide (size a.num < 0) != decide (size b.num < 0)) = false)
    (hint : ¬ ((nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1) ∧
      (nlimbs (a.den : Int) = 1 ∧ topLimb (a.den : Int) = 1)))
    (hg1 : ¬ ((size a.num).natAbs + nlimbs (b.den : Int) >
      (size b.num).natAbs + nlimbs (a.den : Int) + 1))
    (hg2 : (size b.num).natAbs + nlimbs (a.den : Int) +
      (if nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1 then 1 else 0) >
      (size a.num).natAbs + nlimbs (b.den : Int) + 1) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  have hda : a.den ≠ 0 := by omega
  have hdb : b.den ≠ 0 := by omega
  have hla : nlimbs (a.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (a.den : Int) (by omega)
    omega
  have hlb : nlimbs (b.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (b.den : Int) (by omega)
    omega
  have haz : a.num ≠ 0 := by intro h; apply hna; rw [h]; rfl
  have hbz : b.num ≠ 0 := by intro h; apply hnb; rw [h]; rfl
  have hg' : nlimbs (b.num.natAbs : Int) + nlimbs (a.den : Int) +
      (if nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1 then 1 else 0) >
      nlimbs (a.num.natAbs : Int) + nlimbs (b.den : Int) + 1 := by
    simpa [size_nat_abs, nlimbs_natAbs] using hg2
  have hp := (cross_products_limb_thresholds a.num.natAbs b.num.natAbs a.den b.den
    (Int.natAbs_ne_zero.mpr haz) (Int.natAbs_ne_zero.mpr hbz) hda hdb).2 hg'
  have hdiff : ((a.num.natAbs * b.den : Nat) : Int) -
      ((b.num.natAbs * a.den : Nat) : Int) < 0 := by omega
  refine ⟨(-size a.num).sign, ?_, ?_⟩
  · simp [cmpQ, hda, hdb, mpqCmp, hna, hnb, hsgn, hla, hlb, hint, hg1, hg2]
  · rw [Int.sign_sign, Int.sign_neg, size_sign, qOrder_same_sign a b hda hdb hs,
      Int.sign_eq_neg_one_of_neg hdiff]
    simp

/-- The first GMP top-limb bit shortcut agrees with rational order. -/
theorem rationalCmp_first_bit_gap (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den)
    (hna : size a.num ≠ 0) (hnb : size b.num ≠ 0)
    (hs : a.num.sign = b.num.sign)
    (hsgn : (decide (size a.num < 0) != decide (size b.num < 0)) = false)
    (hint : ¬ ((nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1) ∧
      (nlimbs (a.den : Int) = 1 ∧ topLimb (a.den : Int) = 1)))
    (hg1 : ¬ ((size a.num).natAbs + nlimbs (b.den : Int) >
      (size b.num).natAbs + nlimbs (a.den : Int) + 1))
    (hg2 : ¬ ((size b.num).natAbs + nlimbs (a.den : Int) +
      (if nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1 then 1 else 0) >
      (size a.num).natAbs + nlimbs (b.den : Int) + 1))
    (hbit : ((size a.num).natAbs + nlimbs (b.den : Int)) * 64 -
      clz (topLimb a.num) - clz (topLimb (b.den : Int)) >
      ((size b.num).natAbs + nlimbs (a.den : Int)) * 64 -
      clz (topLimb b.num) - clz (topLimb (a.den : Int)) + 1) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  have hda : a.den ≠ 0 := by omega
  have hdb : b.den ≠ 0 := by omega
  have hla : nlimbs (a.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (a.den : Int) (by omega)
    omega
  have hlb : nlimbs (b.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (b.den : Int) (by omega)
    omega
  have haz : a.num ≠ 0 := by intro h; apply hna; rw [h]; rfl
  have hbz : b.num ≠ 0 := by intro h; apply hnb; rw [h]; rfl
  have hg := cross_products_bit_thresholds a.num.natAbs b.num.natAbs a.den b.den
    (Int.natAbs_ne_zero.mpr haz) (Int.natAbs_ne_zero.mpr hbz) hda hdb
  simp only [nlimbs_natAbs, topLimb_natAbs] at hg
  have hp := hg.1 (by simpa only [size_nat_abs] using hbit)
  have hdiff : 0 < ((a.num.natAbs * b.den : Nat) : Int) -
      ((b.num.natAbs * a.den : Nat) : Int) := by omega
  refine ⟨(size a.num).sign, ?_, ?_⟩
  · simp [cmpQ, hda, hdb, mpqCmp, hna, hnb, hsgn, hla, hlb, hint, hg1, hg2, hbit]
  · rw [Int.sign_sign, size_sign, qOrder_same_sign a b hda hdb hs,
      Int.sign_eq_one_of_pos hdiff, Int.mul_one]

/-- The second GMP top-limb bit shortcut agrees with rational order. -/
theorem rationalCmp_second_bit_gap (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den)
    (hna : size a.num ≠ 0) (hnb : size b.num ≠ 0)
    (hs : a.num.sign = b.num.sign)
    (hsgn : (decide (size a.num < 0) != decide (size b.num < 0)) = false)
    (hint : ¬ ((nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1) ∧
      (nlimbs (a.den : Int) = 1 ∧ topLimb (a.den : Int) = 1)))
    (hg1 : ¬ ((size a.num).natAbs + nlimbs (b.den : Int) >
      (size b.num).natAbs + nlimbs (a.den : Int) + 1))
    (hg2 : ¬ ((size b.num).natAbs + nlimbs (a.den : Int) +
      (if nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1 then 1 else 0) >
      (size a.num).natAbs + nlimbs (b.den : Int) + 1))
    (hb1 : ¬ (((size a.num).natAbs + nlimbs (b.den : Int)) * 64 -
      clz (topLimb a.num) - clz (topLimb (b.den : Int)) >
      ((size b.num).natAbs + nlimbs (a.den : Int)) * 64 -
      clz (topLimb b.num) - clz (topLimb (a.den : Int)) + 1))
    (hbit : ((size b.num).natAbs + nlimbs (a.den : Int)) * 64 -
      clz (topLimb b.num) - clz (topLimb (a.den : Int)) +
      (if nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1 then 1 else 0) >
      ((size a.num).natAbs + nlimbs (b.den : Int)) * 64 -
      clz (topLimb a.num) - clz (topLimb (b.den : Int)) + 1) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  have hda : a.den ≠ 0 := by omega
  have hdb : b.den ≠ 0 := by omega
  have hla : nlimbs (a.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (a.den : Int) (by omega)
    omega
  have hlb : nlimbs (b.den : Int) ≠ 0 := by
    have h := ConvProofs.nlimbs_pos (b.den : Int) (by omega)
    omega
  have haz : a.num ≠ 0 := by intro h; apply hna; rw [h]; rfl
  have hbz : b.num ≠ 0 := by intro h; apply hnb; rw [h]; rfl
  have hg := cross_products_bit_thresholds a.num.natAbs b.num.natAbs a.den b.den
    (Int.natAbs_ne_zero.mpr haz) (Int.natAbs_ne_zero.mpr hbz) hda hdb
  simp only [nlimbs_natAbs, topLimb_natAbs] at hg
  have hp := hg.2 (by simpa only [size_nat_abs] using hbit)
  have hdiff : ((a.num.natAbs * b.den : Nat) : Int) -
      ((b.num.natAbs * a.den : Nat) : Int) < 0 := by omega
  refine ⟨(-size a.num).sign, ?_, ?_⟩
  · simp [cmpQ, hda, hdb, mpqCmp, hna, hnb, hsgn, hla, hlb, hint, hg1, hg2, hb1, hbit]
  · rw [Int.sign_sign, Int.sign_neg, size_sign, qOrder_same_sign a b hda hdb hs,
      Int.sign_eq_neg_one_of_neg hdiff]
    simp

/-- GMP's integer-only path preserves the signed magnitude comparison. -/
theorem signed_integer_limb_compare (x y : Int) (hx : x ≠ 0) (hy : y ≠ 0)
    (hs : x.sign = y.sign) :
    (if size x ≠ size y then (if size x > size y then (1 : Int) else -1)
      else
        let c : Int := if x.natAbs < y.natAbs then -1
          else if x.natAbs = y.natAbs then 0 else 1
        if size x > 0 then c else -c).sign =
      x.sign * ((x.natAbs : Int) - (y.natAbs : Int)).sign := by
  have px := ConvProofs.nlimbs_pos x hx
  have py := ConvProofs.nlimbs_pos y hy
  have hc := integer_limb_compare_sign x.natAbs y.natAbs
  simp only [nlimbs_natAbs] at hc
  by_cases hn : x < 0
  · have hny : y < 0 := by
      have h := Int.sign_eq_neg_one_of_neg hn
      have : y.sign = -1 := by rw [← hs]; exact h
      exact Int.neg_of_sign_eq_neg_one this
    have hxs : x.sign = -1 := Int.sign_eq_neg_one_of_neg hn
    by_cases hne : nlimbs x ≠ nlimbs y
    · have hne' : (nlimbs x : Int) ≠ (nlimbs y : Int) := by omega
      by_cases hlt : nlimbs x < nlimbs y
      · have hz : -(nlimbs x : Int) > -(nlimbs y : Int) := by omega
        have hc' : ((x.natAbs : Int) - y.natAbs).sign = -1 := by
          simpa [hne, show ¬ nlimbs x > nlimbs y by omega] using hc.symm
        simp [size, hn, hny, hxs, hne', hz, hc']
      · have hz : ¬ -(nlimbs x : Int) > -(nlimbs y : Int) := by omega
        have hc' : ((x.natAbs : Int) - y.natAbs).sign = 1 := by
          simpa [hne, show nlimbs x > nlimbs y by omega] using hc.symm
        simp [size, hn, hny, hxs, hne', hz, hc']
    · have hz : ¬ 0 < -(nlimbs x : Int) := by omega
      have he : (nlimbs x : Int) = (nlimbs y : Int) := by omega
      have hc' : ((x.natAbs : Int) - y.natAbs).sign =
          (if x.natAbs < y.natAbs then -1 else if x.natAbs = y.natAbs then 0 else 1) := by
        simpa [hne] using hc.symm
      by_cases hl : x.natAbs < y.natAbs <;> by_cases heq : x.natAbs = y.natAbs <;>
        simp [size, hn, hny, hxs, he, hc', hl, heq,
          show ¬ (nlimbs y : Int) < 0 by omega]
  · have hxpos : 0 < x := by omega
    have hys : y.sign = 1 := by rw [← hs]; exact Int.sign_eq_one_of_pos hxpos
    have hypos : 0 < y := Int.pos_of_sign_eq_one hys
    have hxs : x.sign = 1 := Int.sign_eq_one_of_pos hxpos
    have hny : ¬ y < 0 := by omega
    by_cases hne : nlimbs x ≠ nlimbs y
    · have hne' : (nlimbs x : Int) ≠ (nlimbs y : Int) := by omega
      by_cases hlt : nlimbs x < nlimbs y
      · have hz : ¬ (nlimbs x : Int) > (nlimbs y : Int) := by omega
        have hc' : ((x.natAbs : Int) - y.natAbs).sign = -1 := by
          simpa [hne, show ¬ nlimbs x > nlimbs y by omega] using hc.symm
        simp [size, hn, hny, hxs, hne', hz, hc']
      · have hz : (nlimbs x : Int) > (nlimbs y : Int) := by omega
        have hc' : ((x.natAbs : Int) - y.natAbs).sign = 1 := by
          simpa [hne, show nlimbs x > nlimbs y by omega] using hc.symm
        simp [size, hn, hny, hxs, hne', hz, hc']
    · have hz : 0 < (nlimbs x : Int) := by omega
      have he : (nlimbs x : Int) = (nlimbs y : Int) := by omega
      have hc' : ((x.natAbs : Int) - y.natAbs).sign =
          (if x.natAbs < y.natAbs then -1 else if x.natAbs = y.natAbs then 0 else 1) := by
        simpa [hne] using hc.symm
      by_cases hl : x.natAbs < y.natAbs <;> by_cases heq : x.natAbs = y.natAbs <;>
        simp [size, hn, hny, hxs, he, hc', hl, heq, py]

/-- GMP's integer-only branch agrees with finite rational order. -/
theorem rationalCmp_integer_denominators (a b : QBig) (_ha : 0 < a.den) (_hb : 0 < b.den)
    (hna : size a.num ≠ 0) (hnb : size b.num ≠ 0)
    (hs : a.num.sign = b.num.sign)
    (hsgn : (decide (size a.num < 0) != decide (size b.num < 0)) = false)
    (hint : (nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1) ∧
      (nlimbs (a.den : Int) = 1 ∧ topLimb (a.den : Int) = 1)) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  have hda : a.den = 1 := one_limb_top_one a.den hint.2.1 hint.2.2
  have hdb : b.den = 1 := one_limb_top_one b.den hint.1.1 hint.1.2
  have haz : a.num ≠ 0 := by intro h; apply hna; rw [h]; rfl
  have hbz : b.num ≠ 0 := by intro h; apply hnb; rw [h]; rfl
  let c : Int := if size a.num ≠ size b.num then
      (if size a.num > size b.num then 1 else -1)
    else
      let t : Int := if a.num.natAbs < b.num.natAbs then -1
        else if a.num.natAbs = b.num.natAbs then 0 else 1
      if size a.num > 0 then t else -t
  refine ⟨c.sign, ?_, ?_⟩
  · simp [cmpQ, hda, hdb, mpqCmp, hna, hnb, hsgn, c,
      show nlimbs 1 = 1 by decide, show topLimb 1 = 1 by decide]
    split <;> simp
  · rw [Int.sign_sign, qOrder_same_sign a b (by omega) (by omega) hs]
    simpa [hda, hdb, c] using signed_integer_limb_compare a.num b.num haz hbz hs

private theorem rationalCmp_same_sign_dispatch (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den)
    (hna : size a.num ≠ 0) (hnb : size b.num ≠ 0)
    (hs : a.num.sign = b.num.sign)
    (hsgn : (decide (size a.num < 0) != decide (size b.num < 0)) = false) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  by_cases hint : (nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1) ∧
      (nlimbs (a.den : Int) = 1 ∧ topLimb (a.den : Int) = 1)
  · exact rationalCmp_integer_denominators a b ha hb hna hnb hs hsgn hint
  by_cases hg1 : (size a.num).natAbs + nlimbs (b.den : Int) >
      (size b.num).natAbs + nlimbs (a.den : Int) + 1
  · exact rationalCmp_first_limb_gap a b ha hb hna hnb hs hsgn hint hg1
  by_cases hg2 : (size b.num).natAbs + nlimbs (a.den : Int) +
      (if nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1 then 1 else 0) >
      (size a.num).natAbs + nlimbs (b.den : Int) + 1
  · exact rationalCmp_second_limb_gap a b ha hb hna hnb hs hsgn hint hg1 hg2
  by_cases hb1 : ((size a.num).natAbs + nlimbs (b.den : Int)) * 64 -
      clz (topLimb a.num) - clz (topLimb (b.den : Int)) >
      ((size b.num).natAbs + nlimbs (a.den : Int)) * 64 -
      clz (topLimb b.num) - clz (topLimb (a.den : Int)) + 1
  · exact rationalCmp_first_bit_gap a b ha hb hna hnb hs hsgn hint hg1 hg2 hb1
  by_cases hb2 : ((size b.num).natAbs + nlimbs (a.den : Int)) * 64 -
      clz (topLimb b.num) - clz (topLimb (a.den : Int)) +
      (if nlimbs (b.den : Int) = 1 ∧ topLimb (b.den : Int) = 1 then 1 else 0) >
      ((size a.num).natAbs + nlimbs (b.den : Int)) * 64 -
      clz (topLimb a.num) - clz (topLimb (b.den : Int)) + 1
  · exact rationalCmp_second_bit_gap a b ha hb hna hnb hs hsgn hint hg1 hg2 hb1 hb2
  exact rationalCmp_exact_products a b ha hb hna hnb hs hsgn hint hg1 hg2 hb1 hb2

/-- GMP comparison agrees with cross-product order for all finite rationals. -/
theorem rationalCmpIsless_finite (a b : QBig) (ha : 0 < a.den) (hb : 0 < b.den) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  by_cases haz : a.num = 0
  · exact rationalCmp_zero_left a b ha hb haz
  by_cases hbz : b.num = 0
  · exact rationalCmp_zero_right a b ha hb haz hbz
  have hna : size a.num ≠ 0 := by
    have hp := ConvProofs.nlimbs_pos a.num haz
    unfold size; split <;> omega
  have hnb : size b.num ≠ 0 := by
    have hp := ConvProofs.nlimbs_pos b.num hbz
    unfold size; split <;> omega
  have hsa : size a.num < 0 ↔ a.num < 0 := by
    have hp := ConvProofs.nlimbs_pos a.num haz
    unfold size; split <;> omega
  have hsb : size b.num < 0 ↔ b.num < 0 := by
    have hp := ConvProofs.nlimbs_pos b.num hbz
    unfold size; split <;> omega
  by_cases han : a.num < 0
  · by_cases hbn : b.num < 0
    · have hs : a.num.sign = b.num.sign := by
        rw [Int.sign_eq_neg_one_of_neg han, Int.sign_eq_neg_one_of_neg hbn]
      have hsgn : (decide (size a.num < 0) != decide (size b.num < 0)) = false := by
        simp [hsa.mpr han, hsb.mpr hbn]
      apply rationalCmp_same_sign_dispatch a b ha hb hna hnb hs hsgn
    · exact rationalCmp_opposite_sign a b ha hb (.inl ⟨han, by omega⟩)
  · by_cases hbn : b.num < 0
    · exact rationalCmp_opposite_sign a b ha hb (.inr ⟨by omega, hbn⟩)
    · have hs : a.num.sign = b.num.sign := by
        rw [Int.sign_eq_one_of_pos (by omega), Int.sign_eq_one_of_pos (by omega)]
      have hsgn : (decide (size a.num < 0) != decide (size b.num < 0)) = false := by
        simp [show ¬ size a.num < 0 by simpa [hsa] using han,
          show ¬ size b.num < 0 by simpa [hsb] using hbn]
      apply rationalCmp_same_sign_dispatch a b ha hb hna hnb hs hsgn

/-- `cmp` on `Rational{BigInt}` values, infinite ones included, is a defined call whose sign is
the order of the values (`isless`, `base/operators.jl:508-511`). -/
def RationalCmpIsless : Prop :=
  ∀ a b : QBig, a.normalized → b.normalized → ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b

/-- For normalized rationals, the infinity branches of `cmp` agree with the value order. -/
theorem rationalCmpIsless_infinite (a b : QBig) (ha : a.normalized) (hb : b.normalized)
    (hinf : a.den = 0 ∨ b.den = 0) :
    ∃ c, cmpQ a b = some c ∧ c.sign = qOrder a b := by
  rcases ha with ⟨ha, _⟩ | ⟨ha, haNum⟩
  · rcases hb with ⟨hb, _⟩ | ⟨hb, hbNum⟩
    · omega
    · rcases hbNum with hbNum | hbNum <;>
        simp [cmpQ, qOrder, hb, hbNum, show a.den ≠ 0 by omega] <;> omega
  · rcases haNum with haNum | haNum
    all_goals
      rcases hb with ⟨hb, _⟩ | ⟨hb, hbNum⟩
      · simp [cmpQ, qOrder, ha, haNum, show b.den ≠ 0 by omega] <;> omega
      · rcases hbNum with hbNum | hbNum <;>
          simp [cmpQ, qOrder, ha, hb, haNum, hbNum] <;> omega

theorem rationalCmpIsless_proven : RationalCmpIsless := by
  intro a b ha hb
  by_cases hinf : a.den = 0 ∨ b.den = 0
  · exact rationalCmpIsless_infinite a b ha hb hinf
  · have hda : 0 < a.den := by omega
    have hdb : 0 < b.den := by omega
    exact rationalCmpIsless_finite a b hda hdb

/-- The prior source passed all rationals directly to GMP. -/
def LegacyRationalCmpIsless : Prop :=
  ∀ a b : QBig, a.normalized → b.normalized → ∃ c, mpqCmp a b = some c ∧ c.sign = qOrder a b

theorem rationalCmpIsless_refuted : ¬ LegacyRationalCmpIsless := by
  intro h
  obtain ⟨c, hc, _⟩ := h ⟨1, 0⟩ ⟨1, 2⟩ (Or.inr ⟨rfl, Or.inl rfl⟩) (Or.inl ⟨by decide, by decide⟩)
  have : mpqCmp ⟨1, 0⟩ ⟨1, 2⟩ = none := by decide +kernel
  rw [this] at hc
  cases hc


/-- `Rational{BigInt}(x::AbstractFloat)` for `x = Float64`, `base/mpfr.jl:565-571`. NaN builds
`zero(BigInt)//zero(BigInt)`, which `Rational{BigInt}(num, den)` rejects with
`ArgumentError` (`base/gmp.jl:1004-1006`). -/
def rationalBigOfF64 (x : Fl double) : Jl QBig :=
  if x.isnan then .error (.argumentError "invalid rational: zero(BigInt)//zero(BigInt)")
  else if x.isinf then .ok ⟨if x.signbit then -1 else 1, 0⟩
  else if x.iszero then .ok ⟨0, 1⟩
  else
    let (n, d) := x.toRat
    let g := Nat.gcd n.natAbs d
    .ok ⟨n / g, d / g⟩

/-- Converting NaN to `Rational{BigInt}` throws `InexactError`, as for every other `Rational{T}`
and every lossy conversion (`convert` docstring, `base/essentials.jl`). -/
def RationalOfNaNInexact : Prop :=
  ∀ x : Fl double, x.isnan = true → ∃ fn, rationalBigOfF64 x = .error (.inexactError fn)

theorem rationalOfNaNInexact_refuted : ¬ RationalOfNaNInexact := by
  intro h
  obtain ⟨fn, hfn⟩ := h Fl.nan (by decide)
  simp [rationalBigOfF64, (by decide : (Fl.nan : Fl double).isnan = true)] at hfn

end JuliaLean.BigNums
