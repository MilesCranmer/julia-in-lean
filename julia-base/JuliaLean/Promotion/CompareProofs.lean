import JuliaLean.Promotion.Compare
import JuliaLean.Proofs.base.float

/-!
Magnitude keys and the bridge from the generic binary64 rounding model `Fl.roundRat` to
`F64.roundRat`, used by `JuliaLean.FloatFuncs.ProofRound`. The generic `Fmt`/`Fl` format
lemmas are in `JuliaLean.Proofs.base.float`.
-/

namespace JuliaLean.Promotion

open JuliaLean.Float

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

end JuliaLean.Promotion
