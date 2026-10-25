import JuliaLean.Dicts.Table

/-!
# Slot arithmetic of the `Dict` table

After the first `rehash!` a table has `2^p` slots with `p ≥ 4`. On such a size
the masked index arithmetic of `base/dict.jl` is cyclic arithmetic on
`1:sz`; this file gives each step in closed form, for `omega`.
-/

namespace JuliaLean.Dicts

/-- Table sizes after the first `rehash!`: powers of two, at least 16. -/
def IsPow (sz : Nat) : Prop := ∃ p, 4 ≤ p ∧ sz = 2 ^ p

theorem IsPow.ge {sz : Nat} (h : IsPow sz) : 16 ≤ sz := by
  obtain ⟨p, hp, rfl⟩ := h
  calc 16 = 2 ^ 4 := rfl
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp

theorem IsPow.land {sz : Nat} (h : IsPow sz) (x : Nat) : Nat.land x (sz - 1) = x % sz := by
  obtain ⟨p, -, rfl⟩ := h
  exact Nat.and_two_pow_sub_one_eq_mod x p

theorem IsPow.dvd64 {sz : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) : ∃ q, 2 ^ 64 = sz * q := by
  obtain ⟨p, -, rfl⟩ := h
  have hp : p ≤ 64 := by
    apply Nat.le_of_not_lt
    intro hc
    have : 2 ^ 65 ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hc
    omega
  exact ⟨2 ^ (64 - p), by rw [← Nat.pow_add]; congr 1; omega⟩

theorem IsPow.double {sz : Nat} (h : IsPow sz) : IsPow (sz * 2) := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p + 1, by omega, (Nat.pow_succ 2 p).symm⟩

theorem IsPow.quad {sz : Nat} (h : IsPow sz) : IsPow (sz * 4) := by
  obtain ⟨p, hp, rfl⟩ := h
  refine ⟨p + 2, by omega, ?_⟩
  rw [Nat.pow_add]

theorem sub_mod_pow {sz d : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (hd : 0 < d) (hd' : d ≤ sz) :
    (2 ^ 64 - d) % sz = sz - d := by
  obtain ⟨q, hq⟩ := h.dvd64 hs
  cases q with
  | zero => rw [Nat.mul_zero] at hq; exact absurd hq (by decide)
  | succ q =>
    have hle : sz ≤ sz * (q + 1) := Nat.le_mul_of_pos_right sz (by omega)
    have e : 2 ^ 64 - d = sz * q + (sz - d) := by
      have : sz * (q + 1) = sz * q + sz := Nat.mul_succ sz q
      omega
    rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-! ## The index steps -/

theorem nextIdx_spec {sz i : Nat} (h : IsPow sz) (h1 : 1 ≤ i) (h2 : i ≤ sz) :
    (i < sz ∧ nextIdx sz i = i + 1) ∨ (i = sz ∧ nextIdx sz i = 1) := by
  unfold nextIdx
  rw [h.land]
  by_cases hi : i < sz
  · left; exact ⟨hi, by rw [Nat.mod_eq_of_lt hi]⟩
  · right
    have e : i = sz := by omega
    refine ⟨e, ?_⟩
    rw [e, Nat.mod_self]

theorem bits64_of_nonneg {x : Int} (h0 : 0 ≤ x) (h1 : x < 2 ^ 64) : bits64 x = x.toNat := by
  unfold bits64
  omega

theorem bits64_of_neg {x : Int} (h0 : -2 ^ 64 ≤ x) (h1 : x < 0) :
    bits64 x = (x + 2 ^ 64).toNat := by
  unfold bits64
  omega

theorem prevIdx_spec {sz i : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i) (h2 : i ≤ sz) :
    (i = 1 ∧ prevIdx sz i = sz) ∨ (1 < i ∧ prevIdx sz i = i - 1) := by
  have h16 := h.ge
  unfold prevIdx
  rw [h.land]
  by_cases hi : i = 1
  · left
    refine ⟨hi, ?_⟩
    have hb : bits64 ((i : Int) - 2) = 2 ^ 64 - 1 := by
      rw [bits64_of_neg (by omega) (by omega)]
      omega
    rw [hb, sub_mod_pow h hs (by omega) (by omega)]
    omega
  · right
    refine ⟨by omega, ?_⟩
    have hb : bits64 ((i : Int) - 2) = i - 2 := by
      rw [bits64_of_nonneg (by omega) (by omega)]
      omega
    rw [hb, Nat.mod_eq_of_lt (by omega)]
    omega

theorem probeDist_spec {sz i j : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64)
    (h1 : 1 ≤ i) (h2 : i ≤ sz) (h3 : 1 ≤ j) (h4 : j ≤ sz) :
    (j ≤ i ∧ probeDist sz i j = i - j) ∨ (i < j ∧ probeDist sz i j = i + sz - j) := by
  unfold probeDist
  rw [h.land]
  by_cases hij : j ≤ i
  · left
    refine ⟨hij, ?_⟩
    have hb : bits64 ((i : Int) - j) = i - j := by
      rw [bits64_of_nonneg (by omega) (by omega)]
      omega
    rw [hb, Nat.mod_eq_of_lt (by omega)]
  · right
    refine ⟨by omega, ?_⟩
    have hb : bits64 ((i : Int) - j) = 2 ^ 64 - (j - i) := by
      rw [bits64_of_neg (by omega) (by omega)]
      omega
    rw [hb, sub_mod_pow h hs (by omega) (by omega)]
    omega

/-- The home slot `hashindex(key, sz)[1]` of a hash. -/
theorem hashindex_fst {sz : Nat} (h : IsPow sz) (hsh : JInt .u64) :
    (hashindex hsh sz).1 = hsh.val.toNat % sz + 1 := by
  show Nat.land hsh.val.toNat (sz - 1) + 1 = _
  rw [h.land]

theorem hashindex_range {sz : Nat} (h : IsPow sz) (hsh : JInt .u64) :
    1 ≤ (hashindex hsh sz).1 ∧ (hashindex hsh sz).1 ≤ sz := by
  rw [hashindex_fst h]
  have := Nat.mod_lt hsh.val.toNat (show sz > 0 by have := h.ge; omega)
  omega

/-! ## Probe sequences -/

/-- The slot at probe distance `d` from `home`: `d` steps `(index & (sz-1)) + 1`. -/
def pr (sz home : Nat) : Nat → Nat
  | 0 => home
  | d + 1 => nextIdx sz (pr sz home d)

theorem pr_succ (sz home d : Nat) : pr sz home (d + 1) = nextIdx sz (pr sz home d) := rfl

theorem pr_spec {sz home : Nat} (h : IsPow sz) (h1 : 1 ≤ home) (h2 : home ≤ sz) :
    ∀ d, d < sz →
      (home + d ≤ sz ∧ pr sz home d = home + d) ∨ (sz < home + d ∧ pr sz home d = home + d - sz)
  | 0, _ => Or.inl ⟨by omega, rfl⟩
  | d + 1, hd => by
    have ih := pr_spec h h1 h2 d (by omega)
    have hr : 1 ≤ pr sz home d ∧ pr sz home d ≤ sz := by omega
    have hn := nextIdx_spec h hr.1 hr.2
    rw [pr_succ]
    omega

theorem pr_range {sz home d : Nat} (h : IsPow sz) (h1 : 1 ≤ home) (h2 : home ≤ sz) (hd : d < sz) :
    1 ≤ pr sz home d ∧ pr sz home d ≤ sz := by
  have := pr_spec h h1 h2 d hd
  omega

theorem pr_inj {sz home d d' : Nat} (h : IsPow sz) (h1 : 1 ≤ home) (h2 : home ≤ sz)
    (hd : d < sz) (hd' : d' < sz) (e : pr sz home d = pr sz home d') : d = d' := by
  have := pr_spec h h1 h2 d hd
  have := pr_spec h h1 h2 d' hd'
  omega

theorem pr_surj {sz home j : Nat} (h : IsPow sz) (h1 : 1 ≤ home) (h2 : home ≤ sz)
    (hj1 : 1 ≤ j) (hj2 : j ≤ sz) : ∃ d, d < sz ∧ pr sz home d = j := by
  by_cases hc : home ≤ j
  · refine ⟨j - home, by omega, ?_⟩
    have := pr_spec h h1 h2 (j - home) (by omega)
    omega
  · refine ⟨j + sz - home, by omega, ?_⟩
    have := pr_spec h h1 h2 (j + sz - home) (by omega)
    omega

theorem probeDist_pr {sz home d : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ home)
    (h2 : home ≤ sz) (hd : d < sz) : probeDist sz (pr sz home d) home = d := by
  have := pr_spec h h1 h2 d hd
  have hr := pr_range h h1 h2 hd
  have := probeDist_spec h hs hr.1 hr.2 h1 h2
  omega

/-- The slot before `pr home (d+1)` is `pr home d`. -/
theorem prevIdx_pr_succ {sz home d : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ home)
    (h2 : home ≤ sz) (hd : d + 1 < sz) : prevIdx sz (pr sz home (d + 1)) = pr sz home d := by
  have := pr_spec h h1 h2 d (by omega)
  have := pr_spec h h1 h2 (d + 1) hd
  have hr := pr_range h h1 h2 hd
  have := prevIdx_spec h hs hr.1 hr.2
  omega

theorem nextIdx_prevIdx {sz i : Nat} (h : IsPow sz) (hs : sz ≤ 2 ^ 64) (h1 : 1 ≤ i) (h2 : i ≤ sz) :
    nextIdx sz (prevIdx sz i) = i ∧ 1 ≤ prevIdx sz i ∧ prevIdx sz i ≤ sz := by
  have hp := prevIdx_spec h hs h1 h2
  have h16 := h.ge
  have hr : 1 ≤ prevIdx sz i ∧ prevIdx sz i ≤ sz := by omega
  have := nextIdx_spec h hr.1 hr.2
  omega

theorem nextIdx_range {sz i : Nat} (h : IsPow sz) (h1 : 1 ≤ i) (h2 : i ≤ sz) :
    1 ≤ nextIdx sz i ∧ nextIdx sz i ≤ sz := by
  have := nextIdx_spec h h1 h2
  have := h.ge
  omega

/-! ## Slot bytes -/

theorem lor128_facts : ∀ y, y < 256 →
    isFilledB (Nat.lor y 128) = true ∧ Nat.lor y 128 ≠ 0 ∧ Nat.lor y 128 ≠ 127 := by
  decide +kernel

theorem shorthash7_facts (h : JInt .u64) :
    isFilledB (shorthash7 h) = true ∧ shorthash7 h ≠ 0 ∧ shorthash7 h ≠ 127 :=
  lor128_facts _ (Nat.mod_lt _ (by decide))

theorem shorthash7_filled (h : JInt .u64) : isFilledB (shorthash7 h) = true :=
  (shorthash7_facts h).1

theorem shorthash7_ne0 (h : JInt .u64) : shorthash7 h ≠ 0 := (shorthash7_facts h).2.1

theorem shorthash7_ne127 (h : JInt .u64) : shorthash7 h ≠ 127 := (shorthash7_facts h).2.2

theorem isFilledB_zero : isFilledB 0 = false := by decide

theorem isFilledB_127 : isFilledB 127 = false := by decide

/-! ## `_tablesz` -/

theorem tableszNat_pow (x : Nat) : IsPow (tableszNat x) := by
  unfold tableszNat
  split
  · exact ⟨4, by omega, rfl⟩
  · refine ⟨Nat.log2 (x - 1) + 1, ?_, rfl⟩
    have : 2 ^ 3 ≤ x - 1 := by
      have : (8 : Nat) = 2 ^ 3 := rfl
      omega
    have := (Nat.le_log2 (show x - 1 ≠ 0 by omega)).2 this
    omega

theorem tableszNat_ge (x : Nat) : x ≤ tableszNat x := by
  unfold tableszNat
  split
  · omega
  · have := @Nat.lt_log2_self (x - 1)
    omega

theorem tableszNat_le (x : Nat) : tableszNat x ≤ 16 + 2 * x := by
  unfold tableszNat
  split
  · omega
  · have h := Nat.log2_self_le (show x - 1 ≠ 0 by omega)
    rw [Nat.pow_succ]
    omega

theorem tableszNat_of_pow {x : Nat} (h : IsPow x) : tableszNat x = x := by
  obtain ⟨p, hp, rfl⟩ := h
  have h16 : 16 ≤ 2 ^ p := IsPow.ge ⟨p, hp, rfl⟩
  unfold tableszNat
  split
  · omega
  have hlog : Nat.log2 (2 ^ p - 1) = p - 1 := by
    rw [Nat.log2_eq_iff (by omega)]
    have e : 2 ^ p = 2 ^ (p - 1) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    constructor
    · omega
    · rw [show p - 1 + 1 = p by omega]; omega
  rw [hlog, show p - 1 + 1 = p by omega]

end JuliaLean.Dicts
