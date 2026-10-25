import JuliaLean.BigNums.Int

/-!
Proofs of the `powermod` and `invmod` properties of `JuliaLean/BigNums/Int.lean`.
-/

namespace JuliaLean.BigNums

open JuliaLean JuliaLean.IntArith.NumberTheory

/-- Exact-integer `workMod` with a positive modulus is Euclidean `%`. -/
private theorem workMod_none_pos (a b : Int) (hb : 0 < b) : workMod none a b = .ok (a % b) := by
  have hr0 := Int.emod_nonneg a (show b ≠ 0 by omega)
  have hr1 := Int.emod_lt_of_pos a hb
  have hnat : ((b.natAbs : Nat) : Int) = b := Int.natAbs_of_nonneg (by omega)
  have ht := @Int.tmod_eq_emod a b
  simp only [workMod]
  rw [if_neg (by omega)]
  congr 1
  generalize a % b = r at *
  by_cases hc : 0 ≤ a ∨ b ∣ a
  · rw [if_pos hc] at ht
    split <;> rename_i h <;> omega
  · rw [if_neg hc, hnat] at ht
    split <;> rename_i h <;> omega

private theorem emod_mul_left' (a b m : Int) : a % m * b % m = a * b % m := by
  rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

private theorem emod_mul_right' (a b m : Int) : a * (b % m) % m = a * b % m := by
  rw [Int.mul_comm a, emod_mul_left', Int.mul_comm]

private theorem emod_pow' (a m : Int) (n : Nat) : (a % m) ^ n % m = a ^ n % m := by
  induction n with
  | zero => rw [Int.pow_zero, Int.pow_zero]
  | succ n ih => rw [Int.pow_succ, Int.pow_succ, Int.mul_emod, ih, Int.emod_emod, ← Int.mul_emod]

private theorem pow_two_mul (b : Int) (k : Nat) : b ^ (2 * k) = (b * b) ^ k := by
  rw [Int.pow_mul, Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

/-- The exact-integer square-and-multiply loop computes `rr * bb ^ q mod mm`. -/
private theorem loop_spec (mm : Int) (hm : 0 < mm) (q : Nat) (rr bb : Int) (hq : 0 < q) :
    powermodLoop none none q mm rr bb = .ok (rr * bb ^ q % mm) := by
  rw [powermodLoop]
  simp only [mul, workMod_none_pos _ _ hm]
  by_cases hodd : q % 2 ≠ 0
  · rw [if_pos hodd]
    by_cases hk : q / 2 = 0
    · have hq1 : q = 1 := by omega
      subst hq1
      simp [Except.map, norm, bind, Except.bind, pure, Except.pure, Int.pow_succ, Int.pow_zero]
    · have ih := loop_spec mm hm (q / 2) (rr * bb % mm) (bb * bb % mm) (by omega)
      simp only [Except.map, norm, bind, Except.bind, pure, Except.pure, hk, if_false, ih]
      congr 1
      obtain ⟨k, hkq⟩ : ∃ k, q / 2 = k := ⟨_, rfl⟩
      have hq2 : q = 2 * k + 1 := by omega
      rw [hkq, emod_mul_left', ← emod_mul_right' (rr * bb) ((bb * bb % mm) ^ k), emod_pow',
        emod_mul_right', hq2,
        Int.pow_succ, pow_two_mul, Int.mul_assoc, Int.mul_comm bb ((bb * bb) ^ k)]
  · have hk : q / 2 ≠ 0 := by omega
    have ih := loop_spec mm hm (q / 2) rr (bb * bb % mm) (by omega)
    rw [if_neg hodd]
    simp only [Except.map, norm, bind, Except.bind, pure, Except.pure, hk, if_false, ih]
    congr 1
    obtain ⟨k, hkq⟩ : ∃ k, q / 2 = k := ⟨_, rfl⟩
    have hq2 : q = 2 * k := by omega
    rw [hkq, ← emod_mul_right' rr ((bb * bb % mm) ^ k), emod_pow', emod_mul_right', hq2,
      pow_two_mul]
termination_by q
decreasing_by all_goals omega

private theorem gmpPowm_nonneg (x p m : Int) (hp : 0 ≤ p) (hm : m ≠ 0) :
    gmpPowm x p m = .ok (x ^ p.toNat % (m.natAbs : Int)) := by
  have hmm : 0 < (m.natAbs : Int) := by omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  rw [gmpPowm, if_neg hm]
  by_cases hn : n = 0
  · subst hn
    simp [pure, Except.pure]
  · have hp0 : ¬ ((n : Int) = 0) := by omega
    have hpn : ¬ ((n : Int) < 0) := by omega
    simp only [hp0, hpn, if_false, bind, Except.bind, pure, Except.pure]
    rw [loop_spec _ hmm _ _ _ (by omega)]
    simp only [Int.one_mul, emod_pow']
    rfl

/-- Julia's sign normalization of `x mod abs(m)` is the floored remainder. -/
private theorem normalize_fmod (a m : Int) (hm : m ≠ 0) :
    (if m < 0 ∧ a % (m.natAbs : Int) > 0 then a % (m.natAbs : Int) + m
      else a % (m.natAbs : Int)) = a.fmod m := by
  rw [Int.fmod_eq_emod]
  by_cases hneg : m < 0
  · have habs : (m.natAbs : Int) = -m := by omega
    rw [habs, Int.emod_neg]
    have hr0 := Int.emod_nonneg a hm
    by_cases hd : m ∣ a
    · have h0 : a % m = 0 := Int.dvd_iff_emod_eq_zero.mp hd
      simp only [hd, or_true, if_true]
      split <;> omega
    · have h0 : a % m ≠ 0 := fun h => hd (Int.dvd_iff_emod_eq_zero.mpr h)
      simp only [hd, or_false, show ¬ (0 ≤ m) by omega, if_false]
      split <;> omega
  · have habs : (m.natAbs : Int) = m := by omega
    rw [habs]
    simp only [hneg, false_and, if_false, show 0 ≤ m by omega, true_or, if_true, Int.add_zero]

theorem powermodFlooredMod_proven : PowermodFlooredMod := by
  intro x p m hp hm
  simp only [powermod, gmpPowermod, gmpPowm_nonneg x p m hp hm, bind, Except.bind, pure,
    Except.pure]
  rw [normalize_fmod _ _ hm]

private theorem fmod_congr (a b y : Int) (h : y ∣ a - b) : a.fmod y = b.fmod y := by
  rw [Int.fmod_eq_emod, Int.fmod_eq_emod]
  have e : a % y = b % y :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp h)
  have hiff : y ∣ a ↔ y ∣ b := by
    rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, e]
  simp only [e, hiff]

theorem invmodPostcondition_proven : InvmodPostcondition := by
  intro x y z h
  simp only [invmod] at h
  by_cases h1 : (y.natAbs : Int) = 1
  · rw [if_pos h1] at h
    injection h with h
    subst h
    have : y = 1 ∨ y = -1 := by omega
    rcases this with rfl | rfl <;> simp only [Int.zero_mul] <;> decide
  · rw [if_neg h1] at h
    by_cases hy : y = 0
    · rw [if_pos hy] at h
      cases h
    rw [if_neg hy] at h
    cases hz : mpzInvert x (y.natAbs : Int) with
    | none => rw [hz] at h; cases h
    | some z0 =>
      rw [hz] at h
      injection h with h
      subst h
      simp only [mpzInvert] at hz
      cases hf : (List.range (y.natAbs : Int).natAbs).find?
          (fun (z : Nat) => ((z : Int) * x - 1) % (((y.natAbs : Int).natAbs : Nat) : Int) = 0) with
      | none => rw [hf] at hz; cases hz
      | some n =>
        rw [hf] at hz
        injection hz with hz
        simp only at hz
        subst hz
        have hp := List.find?_some hf
        have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hf)
        have e : ((y.natAbs : Int)).natAbs = y.natAbs := rfl
        simp only [e, decide_eq_true_eq] at hp hmem
        have hdvd : y ∣ (n : Int) * x - 1 :=
          Int.natAbs_dvd.mp (Int.dvd_iff_emod_eq_zero.mpr hp)
        have hn1 : 1 ≤ n := by
          by_cases hn : n = 0
          · subst hn
            have h' : y ∣ -1 := by simpa using hdvd
            have h'' : y.natAbs ∣ 1 := by
              have := Int.natAbs_dvd_natAbs.mpr h'
              simpa using this
            have := Nat.dvd_one.mp h''
            omega
          · omega
        constructor
        · apply fmod_congr
          split
          · have e : ((n : Int) + y) * x - 1 = ((n : Int) * x - 1) + y * x := by
              rw [Int.add_mul]; omega
            rw [e]
            exact Int.dvd_add hdvd (Int.dvd_mul_right y x)
          · exact hdvd
        · split
          · rw [← Int.neg_tdiv_neg]
            apply Int.tdiv_eq_zero_of_lt <;> omega
          · apply Int.tdiv_eq_zero_of_lt <;> omega
