import JuliaLean.RandomSampling.Model

/-! Counting lemmas for `countBelow` and the arithmetic of Lemire's acceptance region. -/

namespace JuliaLean.RandomSampling

theorem countBelow_congr {p q : Nat → Bool} : ∀ {n : Nat}, (∀ x, x < n → p x = q x) →
    countBelow p n = countBelow q n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [countBelow]
    rw [countBelow_congr (fun x hx => h x (by omega)), h n (by omega)]

theorem countBelow_interval (lo hi : Nat) : ∀ n,
    countBelow (fun x => decide (lo ≤ x ∧ x < hi)) n = min hi n - min lo n
  | 0 => by simp [countBelow]
  | n + 1 => by
    simp only [countBelow]
    rw [countBelow_interval lo hi n]
    by_cases h : lo ≤ n ∧ n < hi
    · simp only [h, and_self, decide_true, ↓reduceIte]; omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

theorem countBelow_add (p : Nat → Bool) (a : Nat) : ∀ b,
    countBelow p (a + b) = countBelow p a + countBelow (fun x => p (a + x)) b
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc]
    simp only [countBelow]
    rw [countBelow_add p a b]
    omega

/-- Exactly `c` numbers below `c * M` are congruent to `r < M`. -/
theorem countBelow_mod (M r : Nat) (hr : r < M) : ∀ c,
    countBelow (fun w => decide (w % M = r)) (c * M) = c
  | 0 => by simp [countBelow]
  | c + 1 => by
    rw [Nat.succ_mul, countBelow_add, countBelow_mod M r hr c]
    have h1 : countBelow (fun x => decide ((c * M + x) % M = r)) M = 1 := by
      rw [countBelow_congr (q := fun x => decide (r ≤ x ∧ x < r + 1))]
      · rw [countBelow_interval]; omega
      · intro x hx
        have hx' : (c * M + x) % M = x := by
          rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hx
        rw [hx']
        by_cases hxr : x = r
        · subst hxr; simp
        · have : ¬ (r ≤ x ∧ x < r + 1) := by omega
          simp [hxr, this]
    omega

/-- Lemire's acceptance region: for `0 < s ≤ N` and `k < s`, the words `x < N` with
`x*s mod N ≥ (N - s) mod s` and `x*s ÷ N = k` are exactly an interval of `N ÷ s` words. -/
theorem lemire_interval (N s k : Nat) (hs : 0 < s) (hsN : s ≤ N) (hk : k < s) :
    ∃ lo, lo + N / s ≤ N ∧ ∀ x, (¬ (x * s % N < (N - s) % s) ∧ x * s / N = k) ↔
      (lo ≤ x ∧ x < lo + N / s) := by
  have hN : 0 < N := by omega
  have htmod : (N - s) % s = N % s := by
    conv => rhs; rw [show N = N - s + s by omega]
    rw [Nat.add_mod_right]
  rw [htmod]
  have hdm := Nat.div_add_mod N s
  generalize hq : N / s = q at hdm ⊢
  generalize ht : N % s = t at hdm ⊢
  have htlt : t < s := by rw [← ht]; exact Nat.mod_lt _ hs
  have hq1 : 1 ≤ q := by
    rw [← hq]; exact (Nat.le_div_iff_mul_le hs).2 (by omega)
  -- the region is k*N + t ≤ x*s < (k+1)*N = k*N + t + q*s
  have hregion : ∀ x, (¬ (x * s % N < t) ∧ x * s / N = k) ↔
      (k * N + t ≤ x * s ∧ x * s < k * N + t + q * s) := by
    intro x
    have hxd := Nat.div_add_mod (x * s) N
    have hxm := Nat.mod_lt (x * s) hN
    constructor
    · rintro ⟨h1, h2⟩
      rw [h2] at hxd
      have : N * k = k * N := Nat.mul_comm _ _
      have : s * q = q * s := Nat.mul_comm _ _
      constructor <;> omega
    · rintro ⟨h1, h2⟩
      have hdiv : x * s / N = k := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm k N] at h1 ⊢; omega
        · rw [Nat.succ_mul]; have : s * q = q * s := Nat.mul_comm _ _; omega
      refine ⟨?_, hdiv⟩
      rw [hdiv] at hxd
      have : N * k = k * N := Nat.mul_comm _ _
      omega
  -- A ≤ x*s ↔ lo ≤ x for lo = ⌈A/s⌉
  have hceil : ∀ A y, A ≤ y * s ↔ (A + s - 1) / s ≤ y := by
    intro A y
    have h := Nat.div_lt_iff_lt_mul hs (x := A + s - 1) (y := y + 1)
    rw [Nat.succ_mul] at h
    constructor
    · intro h1; have := h.2 (by omega); omega
    · intro h1; have := h.1 (by omega); omega
  have hL := Nat.div_mul_le_self (k * N + t + s - 1) s
  have hceil' : ∀ y, k * N + t ≤ y * s ↔ (k * N + t + s - 1) / s ≤ y := hceil _
  generalize (k * N + t + s - 1) / s = L at hL hceil'
  refine ⟨L, ?_, ?_⟩
  · -- the last word of the interval is below N
    apply Classical.byContradiction; intro hcon
    have hge : N ≤ L + q - 1 := by omega
    have h1 : N * s ≤ (L + q - 1) * s := Nat.mul_le_mul_right _ hge
    have h2 : (L + q - 1) * s + s = L * s + q * s := by
      rw [← Nat.succ_mul, show (L + q - 1).succ = L + q by omega, Nat.add_mul]
    have hks : k * N + N ≤ s * N := by
      have := Nat.mul_le_mul_right N (show k + 1 ≤ s by omega)
      rw [Nat.succ_mul] at this; exact this
    have : s * q = q * s := Nat.mul_comm _ _
    have : N * s = s * N := Nat.mul_comm _ _
    omega
  · intro x
    rw [hregion]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(hceil' x).1 h1, ?_⟩
      apply Classical.byContradiction; intro hcon
      have hy := (hceil' (x - q)).2 (by omega)
      have : (x - q) * s + q * s = x * s := by rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨(hceil' x).2 h1, ?_⟩
      by_cases hxq : x < q
      · have : x * s < q * s := Nat.mul_lt_mul_of_pos_right hxq hs
        omega
      · have hy : ¬ (k * N + t ≤ (x - q) * s) := fun h => by
          have := (hceil' _).1 h; omega
        have : (x - q) * s + q * s = x * s := by rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        omega

end JuliaLean.RandomSampling
