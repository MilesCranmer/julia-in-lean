import JuliaLean.RandomSampling.Props
import JuliaLean.RandomSampling.Count

/-! Proofs for `rand(rng, a:b)` on `BitInteger` types of at most 64 bits (`SamplerRangeNDL`). -/

set_option maxHeartbeats 4000000

namespace JuliaLean.RandomSampling

open JuliaLean

theorem val_add' {t : IntTy} (a b : JInt t) : (a + b).val = wrapInt t (a.val + b.val) := rfl
theorem val_sub' {t : IntTy} (a b : JInt t) : (a - b).val = wrapInt t (a.val - b.val) := rfl
theorem val_neg' {t : IntTy} (a : JInt t) : (-a).val = wrapInt t (-a.val) := rfl
theorem val_wrap' (t : IntTy) (x : Int) : (JInt.wrap t x).val = wrapInt t x := rfl
theorem val_rem' {t : IntTy} (t' : IntTy) (a : JInt t) : (JInt.rem t' a).val = wrapInt t' a.val := rfl
theorem val_lit' (t : IntTy) (x : Int) : (JInt.lit t x).val = wrapInt t x := rfl

theorem uintSup_unsigned (t : IntTy) : (uintSup t).signed = false := by cases t <;> rfl

theorem unsigned_bounds {u : IntTy} (hu : u.signed = false) (x : JInt u) :
    0 ≤ x.val ∧ x.val < 2 ^ u.bits := by
  have h := x.property
  simp only [IntTy.min, IntTy.max, hu, Bool.false_eq_true, ↓reduceIte] at h
  omega

theorem wrapInt_unsigned {u : IntTy} (hu : u.signed = false) {z : Int} (h0 : 0 ≤ z)
    (h1 : z < 2 ^ u.bits) : wrapInt u z = z :=
  wrapInt_of_inRange u z (by
    simp only [IntTy.min, IntTy.max, hu, Bool.false_eq_true, ↓reduceIte]; omega)

theorem two_pow_int (n : Nat) : (2 : Int) ^ n = ((2 ^ n : Nat) : Int) := by norm_cast

theorem IntTy.max_sub_min (t : IntTy) : t.max - t.min + 1 = 2 ^ t.bits := by
  cases t <;> decide

theorem wrapInt_wrap_add (t : IntTy) (x y : Int) :
    wrapInt t (wrapInt t x + y) = wrapInt t (x + y) := by
  unfold wrapInt
  split
  · rw [show (x + 2 ^ (t.bits - 1)) % 2 ^ t.bits - 2 ^ (t.bits - 1) + y + 2 ^ (t.bits - 1) =
      (x + 2 ^ (t.bits - 1)) % 2 ^ t.bits + y by omega, Int.emod_add_emod,
      show x + 2 ^ (t.bits - 1) + y = x + y + 2 ^ (t.bits - 1) by omega]
  · rw [Int.emod_add_emod]

/-- `wrap(k) + a` is `a + k` when `a + k` stays below a value of the type. -/
theorem wrap_add_val {t : IntTy} (k : Int) (a b : JInt t) (hk : 0 ≤ k) (hb : a.val + k ≤ b.val) :
    (JInt.wrap t k + a).val = a.val + k := by
  rw [val_add', val_wrap', wrapInt_wrap_add]
  have ha := a.property
  have hbb := b.property
  rw [wrapInt_of_inRange t _ (by omega)]
  omega

theorem toNat_lt_of_unsigned {u : IntTy} (hu : u.signed = false) (x : JInt u) :
    x.val.toNat < 2 ^ u.bits := by
  have h := unsigned_bounds hu x
  have : x.val < ((2 ^ u.bits : Nat) : Int) := by exact_mod_cast h.2
  omega

theorem wrap_toNat_unsigned {u : IntTy} (hu : u.signed = false) {x : Nat} (hx : x < 2 ^ u.bits) :
    (JInt.wrap u x).val.toNat = x := by
  rw [val_wrap', wrapInt_unsigned hu (by omega) (by exact_mod_cast hx)]
  simp

/-- What `ndlSampler` stores: the first element and the length, or zero for a full range. -/
theorem ndlSampler_spec {t : IntTy} (ht : t.bits ≤ 64) {a b : JInt t} {sp : NDL t}
    (h : ndlSampler a b = .ok sp) :
    sp.a = a ∧ a.val ≤ b.val ∧
    ((sp.s.val = b.val - a.val + 1 ∧ b.val - a.val + 1 < 2 ^ (uintSup t).bits) ∨
     (sp.s.val = 0 ∧ a.val = t.min ∧ b.val = t.max ∧ t.bits = (uintSup t).bits)) := by
  unfold ndlSampler at h
  split at h
  · cases h
  · injection h with h
    subst h
    refine ⟨rfl, by omega, ?_⟩
    simp only [val_add', val_rem', val_sub', val_lit']
    have ha := a.property
    have hb := b.property
    cases t <;> simp [IntTy.bits] at ht <;>
      simp [wrapInt, uintSup, IntTy.toUnsigned, IntTy.signed, IntTy.bits, IntTy.min,
        IntTy.max] at ha hb ⊢ <;> omega

/-- The rejection threshold `mod(-s, s)` of `rand_unlikely`. -/
theorem ndl_thr {u : IntTy} (hu : u.signed = false) (s : JInt u) (hs : 0 < s.val) :
    ∃ thr : JInt u, JInt.mod (-s) s = .ok thr ∧
      thr.val.toNat = (2 ^ u.bits - s.val.toNat) % s.val.toNat := by
  have hb := unsigned_bounds hu s
  have hneg : (-s).val = 2 ^ u.bits - s.val := by
    rw [val_neg']
    unfold wrapInt
    simp only [hu, Bool.false_eq_true, ↓reduceIte]
    have : -s.val = (2 ^ u.bits - s.val) + 2 ^ u.bits * (-1) := by omega
    rw [this, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  refine ⟨JInt.wrap u ((-s).val.tmod s.val), ?_, ?_⟩
  · unfold JInt.mod JInt.remInt
    simp only [hu, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hc; exact absurd hc (by omega)
    · rfl
  · rw [hneg, Int.tmod_eq_emod_of_nonneg (by omega)]
    have hlt : (2 ^ u.bits - s.val) % s.val < s.val := Int.emod_lt_of_pos _ hs
    have hge : 0 ≤ (2 ^ u.bits - s.val) % s.val := Int.emod_nonneg _ (by omega)
    rw [val_wrap', wrapInt_unsigned hu hge (by omega)]
    have e1 : s.val = (s.val.toNat : Int) := (Int.toNat_of_nonneg (by omega)).symm
    have e2 : (2 : Int) ^ u.bits = ((2 ^ u.bits : Nat) : Int) := by norm_cast
    rw [e1, e2, ← Int.natCast_sub (by have := toNat_lt_of_unsigned hu s; omega),
      ← Int.natCast_emod]
    simp only [Int.toNat_natCast]

theorem stateAfter_succ' {σ : Type} (g : Rng σ) (q : Req) (st : σ) :
    ∀ i, g.stateAfter q st (i + 1) = g.stateAfter q (g.next st q).2 i
  | 0 => rfl
  | i + 1 => by
    show (g.next (g.stateAfter q st (i + 1)) q).2 = (g.next (g.stateAfter q (g.next st q).2 i) q).2
    rw [stateAfter_succ' g q st i]

theorem wordAt_succ' {σ : Type} (g : Rng σ) (q : Req) (st : σ) (i : Nat) :
    g.wordAt q st (i + 1) = g.wordAt q (g.next st q).2 i := by
  unfold Rng.wordAt; rw [stateAfter_succ']

/-- Natural-number value of the `i`-th `U` word. -/
def wordNat {σ : Type} (g : Rng σ) (u : IntTy) (st : σ) (i : Nat) : Nat :=
  (g.wordAt (.int u) st i : JInt u).val.toNat

theorem ndlUnlikelyLoop_spec {σ : Type} (g : Rng σ) (u : IntTy) (s thr : Nat) :
    ∀ fuel st m q st', ndlUnlikelyLoop g u s thr fuel st m = some (q, st') →
    (thr ≤ m % 2 ^ u.bits ∧ q = m / 2 ^ u.bits ∧ st' = st) ∨
    (m % 2 ^ u.bits < thr ∧ ∃ n, (∀ i < n, wordNat g u st i * s % 2 ^ u.bits < thr) ∧
      thr ≤ wordNat g u st n * s % 2 ^ u.bits ∧ q = wordNat g u st n * s / 2 ^ u.bits ∧
      st' = g.stateAfter (.int u) st (n + 1))
  | 0, st, m, q, st', h => by
    unfold ndlUnlikelyLoop at h
    split at h
    · cases h
    · injection h with h; injection h with h1 h2
      exact .inl ⟨by omega, h1.symm, h2.symm⟩
  | f + 1, st, m, q, st', h => by
    unfold ndlUnlikelyLoop at h
    split at h
    · rename_i hlt
      right
      refine ⟨hlt, ?_⟩
      rcases ndlUnlikelyLoop_spec g u s thr f _ _ q st' h with ⟨h1, h2, h3⟩ | ⟨h1, n, h2, h3, h4, h5⟩
      · refine ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), ?_, ?_, ?_⟩
        · exact h1
        · exact h2
        · exact h3
      · refine ⟨n + 1, ?_, ?_, ?_, ?_⟩
        · intro i hi
          cases i with
          | zero => exact h1
          | succ i =>
            have := h2 i (by omega)
            unfold wordNat at this ⊢
            rw [wordAt_succ']; exact this
        · unfold wordNat at h3 ⊢; rw [wordAt_succ']; exact h3
        · unfold wordNat at h4 ⊢; rw [wordAt_succ']; exact h4
        · rw [stateAfter_succ']; exact h5
    · injection h with h; injection h with h1 h2
      exact .inl ⟨by omega, h1.symm, h2.symm⟩

theorem ndlStep_zero {t : IntTy} (sp : NDL t) (x : JInt (uintSup t)) (hs : sp.s.val.toNat = 0) :
    ndlStep sp x = some (JInt.rem t x + sp.a) := by
  unfold ndlStep; simp [hs]

theorem ndlStep_reject {t : IntTy} (sp : NDL t) (x : JInt (uintSup t)) (hs : sp.s.val.toNat ≠ 0)
    (h : x.val.toNat * sp.s.val.toNat % 2 ^ (uintSup t).bits <
      (2 ^ (uintSup t).bits - sp.s.val.toNat) % sp.s.val.toNat) :
    ndlStep sp x = none := by
  unfold ndlStep; simp only [hs, ↓reduceIte, h]

theorem ndlStep_accept {t : IntTy} (sp : NDL t) (x : JInt (uintSup t)) (hs : sp.s.val.toNat ≠ 0)
    (h : ¬ x.val.toNat * sp.s.val.toNat % 2 ^ (uintSup t).bits <
      (2 ^ (uintSup t).bits - sp.s.val.toNat) % sp.s.val.toNat) :
    ndlStep sp x = some (JInt.wrap t ((x.val.toNat * sp.s.val.toNat / 2 ^ (uintSup t).bits : Nat) :
      Int) + sp.a) := by
  unfold ndlStep; simp only [hs, ↓reduceIte, h]

theorem ndlStep_range {t : IntTy} (ht : t.bits ≤ 64) {a b : JInt t} {sp : NDL t}
    (hsp : ndlSampler a b = .ok sp) (x : JInt (uintSup t)) (v : JInt t)
    (h : ndlStep sp x = some v) : a.val ≤ v.val ∧ v.val ≤ b.val := by
  obtain ⟨hspa, hab, hs⟩ := ndlSampler_spec ht hsp
  have hu := uintSup_unsigned t
  have hx := toNat_lt_of_unsigned hu x
  rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hamin, hbmax, _⟩
  · have e : ((sp.s.val.toNat : Nat) : Int) = sp.s.val := Int.toNat_of_nonneg (by omega)
    have hsN : sp.s.val.toNat ≠ 0 := by omega
    by_cases hrej : x.val.toNat * sp.s.val.toNat % 2 ^ (uintSup t).bits <
        (2 ^ (uintSup t).bits - sp.s.val.toNat) % sp.s.val.toNat
    · rw [ndlStep_reject sp x hsN hrej] at h; cases h
    · rw [ndlStep_accept sp x hsN hrej] at h
      injection h with h
      subst h
      have hk : x.val.toNat * sp.s.val.toNat / 2 ^ (uintSup t).bits < sp.s.val.toNat := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm]
        exact Nat.mul_lt_mul_of_pos_left hx (by omega)
      rw [hspa]
      generalize x.val.toNat * sp.s.val.toNat / 2 ^ (uintSup t).bits = K at hk ⊢
      rw [wrap_add_val _ a b (by omega) (by omega)]
      omega
  · have hs0 : sp.s.val.toNat = 0 := by omega
    rw [ndlStep_zero sp x hs0] at h
    injection h with h
    subst h
    have := (JInt.rem t x + sp.a).property
    omega

theorem ndlRand_spec {σ : Type} {t : IntTy} (ht : t.bits ≤ 64) {a b : JInt t} {sp : NDL t}
    (hsp : ndlSampler a b = .ok sp) (g : Rng σ) (fuel : Nat) (st : σ) (res : Jl (JInt t × σ))
    (h : ndlRand g sp fuel st = some res) :
    ∃ v st' n, res = .ok (v, st') ∧
      (∀ i < n, ndlStep sp (g.wordAt (.int (uintSup t)) st i) = none) ∧
      ndlStep sp (g.wordAt (.int (uintSup t)) st n) = some v ∧
      st' = g.stateAfter (.int (uintSup t)) st (n + 1) := by
  have hu := uintSup_unsigned t
  obtain ⟨hspa, hab, hs⟩ := ndlSampler_spec ht hsp
  have hsnn : 0 ≤ sp.s.val := (unsigned_bounds hu sp.s).1
  simp only [ndlRand] at h
  by_cases hlt : ((g.next st (.int (uintSup t))).1 : JInt (uintSup t)).val.toNat *
      sp.s.val.toNat % 2 ^ (uintSup t).bits < sp.s.val.toNat
  · have hspos : 0 < sp.s.val := by omega
    have hsN : sp.s.val.toNat ≠ 0 := by omega
    obtain ⟨thr, hmod, hthr⟩ := ndl_thr hu sp.s hspos
    simp only [hlt, ↓reduceIte, hmod] at h
    cases hl : ndlUnlikelyLoop g (uintSup t) sp.s.val.toNat thr.val.toNat fuel
        (g.next st (.int (uintSup t))).2
        (((g.next st (.int (uintSup t))).1 : JInt (uintSup t)).val.toNat *
          sp.s.val.toNat) with
    | none => simp [hl] at h
    | some qq =>
      simp [hl] at h
      subst h
      rw [hthr] at hl
      rcases ndlUnlikelyLoop_spec g _ _ _ fuel _ _ qq.1 qq.2 hl with
        ⟨h1, h2, h3⟩ | ⟨h1, n, h2, h3, h4, h5⟩
      · refine ⟨_, _, 0, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), ?_, h3⟩
        change ndlStep sp (g.next st (.int (uintSup t))).1 = _
        rw [ndlStep_accept sp _ hsN (Nat.not_lt.2 h1)]
        congr 1
        have hq : qq.1 < 2 ^ (uintSup t).bits := by
          have : qq.1 < sp.s.val.toNat := by
            rw [h2, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm]
            exact Nat.mul_lt_mul_of_pos_left (toNat_lt_of_unsigned hu _) (by omega)
          have := toNat_lt_of_unsigned hu sp.s
          omega
        apply Subtype.ext
        simp only [val_add', val_rem', val_wrap']
        rw [wrapInt_unsigned hu (z := (qq.1 : Int)) (by omega) (by exact_mod_cast hq), h2]
      · refine ⟨_, _, n + 1, rfl, ?_, ?_, ?_⟩
        · intro i hi
          cases i with
          | zero => exact ndlStep_reject sp _ hsN h1
          | succ i =>
            rw [wordAt_succ']
            exact ndlStep_reject sp _ hsN (h2 i (by omega))
        · rw [wordAt_succ', ndlStep_accept sp _ hsN (Nat.not_lt.2 h3)]
          congr 1
          have hq : qq.1 < 2 ^ (uintSup t).bits := by
            have : qq.1 < sp.s.val.toNat := by
              rw [h4, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm]
              exact Nat.mul_lt_mul_of_pos_left (toNat_lt_of_unsigned hu _) (by omega)
            have := toNat_lt_of_unsigned hu sp.s
            omega
          apply Subtype.ext
          simp only [val_add', val_rem', val_wrap']
          rw [wrapInt_unsigned hu (z := (qq.1 : Int)) (by omega) (by exact_mod_cast hq), h4]
          rfl
        · rw [stateAfter_succ']; exact h5
  · simp only [hlt, ↓reduceIte] at h
    by_cases hs0 : sp.s.val.toNat = 0
    · simp only [hs0, ↓reduceIte] at h
      injection h with h
      subst h
      exact ⟨_, _, 0, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), ndlStep_zero sp _ hs0, rfl⟩
    · simp only [hs0, ↓reduceIte] at h
      injection h with h
      subst h
      refine ⟨_, _, 0, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), ?_, rfl⟩
      have hthr := Nat.mod_lt (2 ^ (uintSup t).bits - sp.s.val.toNat) (Nat.pos_of_ne_zero hs0)
      exact ndlStep_accept sp (g.next st (.int (uintSup t))).1 hs0 (by omega)

/-- Each value of `a:b` is yielded by the same positive number of words. -/
theorem ndl_count {t : IntTy} (ht : t.bits ≤ 64) {a b : JInt t} {sp : NDL t}
    (hsp : ndlSampler a b = .ok sp) :
    ∃ q, 0 < q ∧ ∀ v : JInt t, a.val ≤ v.val → v.val ≤ b.val →
      countBelow (fun x => decide (ndlStep sp (JInt.wrap (uintSup t) x) = some v))
        (2 ^ (uintSup t).bits) = q := by
  have hu := uintSup_unsigned t
  obtain ⟨hspa, hab, hs⟩ := ndlSampler_spec ht hsp
  rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hamin, hbmax, hbits⟩
  · have e : ((sp.s.val.toNat : Nat) : Int) = sp.s.val := Int.toNat_of_nonneg (by omega)
    have hsN : sp.s.val.toNat ≠ 0 := by omega
    have hsle : sp.s.val.toNat ≤ 2 ^ (uintSup t).bits := by
      have : sp.s.val < ((2 ^ (uintSup t).bits : Nat) : Int) := by rw [hs1]; exact_mod_cast hs2
      omega
    refine ⟨2 ^ (uintSup t).bits / sp.s.val.toNat, Nat.div_pos hsle (by omega), ?_⟩
    intro v hav hvb
    obtain ⟨lo, hlo, hiff⟩ := lemire_interval (2 ^ (uintSup t).bits) sp.s.val.toNat
      (v.val - a.val).toNat (by omega) hsle (by omega)
    rw [countBelow_congr (q := fun x => decide (lo ≤ x ∧ x < lo + 2 ^ (uintSup t).bits /
      sp.s.val.toNat)), countBelow_interval]
    · generalize 2 ^ (uintSup t).bits / sp.s.val.toNat = q at hlo ⊢
      omega
    · intro x hx
      have hxw : (JInt.wrap (uintSup t) x).val.toNat = x := wrap_toNat_unsigned hu hx
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_iff]
      rw [← hiff x]
      by_cases hrej : x * sp.s.val.toNat % 2 ^ (uintSup t).bits <
          (2 ^ (uintSup t).bits - sp.s.val.toNat) % sp.s.val.toNat
      · rw [ndlStep_reject sp _ hsN (by rw [hxw]; exact hrej)]
        simp [hrej]
      · rw [ndlStep_accept sp _ hsN (by rw [hxw]; exact hrej), hxw]
        have hk : x * sp.s.val.toNat / 2 ^ (uintSup t).bits < sp.s.val.toNat := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm]
          exact Nat.mul_lt_mul_of_pos_left hx (by omega)
        simp only [hrej, not_false_eq_true, true_and, Option.some.injEq]
        rw [hspa]
        generalize x * sp.s.val.toNat / 2 ^ (uintSup t).bits = K at hk ⊢
        rw [Subtype.ext_iff, wrap_add_val _ a b (by omega) (by omega)]
        omega
  · refine ⟨1, by omega, ?_⟩
    intro v hav hvb
    have hs0 : sp.s.val.toNat = 0 := by omega
    have hspan := IntTy.max_sub_min t
    have hN : (2 : Int) ^ t.bits = ((2 ^ (uintSup t).bits : Nat) : Int) := by
      rw [hbits]; norm_cast
    rw [countBelow_congr (q := fun x => decide ((v.val - a.val).toNat ≤ x ∧
      x < (v.val - a.val).toNat + 1)), countBelow_interval]
    · omega
    · intro x hx
      rw [ndlStep_zero sp _ hs0, hspa]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_iff, Option.some.injEq]
      rw [Subtype.ext_iff, val_add', val_rem', wrapInt_wrap_add, val_wrap',
        wrapInt_unsigned hu (by omega) (by rw [two_pow_int]; exact_mod_cast hx),
        wrapInt_of_inRange t _ (by omega)]
      omega

theorem ndlInRange_proven : NdlInRange := by
  intro t ht a b sp hsp σ g fuel st res h
  obtain ⟨v, st', n, hres, -, hv, -⟩ := ndlRand_spec ht hsp g fuel st res h
  exact ⟨v, st', hres, ndlStep_range ht hsp _ v hv⟩

theorem ndlUniform_proven : NdlUniform := by
  intro t ht a b sp hsp
  refine ⟨?_, fun x v h => ndlStep_range ht hsp x v h, ndl_count ht hsp⟩
  intro σ g fuel st v st' h
  obtain ⟨v', st'', n, hres, h1, h2, h3⟩ := ndlRand_spec ht hsp g fuel st _ h
  injection hres with hres
  injection hres with hv hst
  subst hv; subst hst
  exact ⟨n, h1, h2, h3⟩

end JuliaLean.RandomSampling
