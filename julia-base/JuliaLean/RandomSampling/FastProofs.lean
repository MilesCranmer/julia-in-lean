import JuliaLean.RandomSampling.NdlProofs

/-! Proofs for `rand(rng, a:b)` on `Int128`/`UInt128` (`SamplerRangeFast`). -/

set_option maxHeartbeats 4000000

namespace JuliaLean.RandomSampling

open JuliaLean

theorem topSetBit_spec (d : Nat) (hd : d < 2 ^ 128) : d < 2 ^ topSetBit d ∧ topSetBit d ≤ 128 := by
  unfold topSetBit
  split
  · rename_i h; subst h; exact ⟨by decide, by decide⟩
  · rename_i h; exact ⟨Nat.lt_log2_self, by have := (Nat.log2_lt h).2 hd; omega⟩

theorem fastWord_unsigned (bw : Nat) : (fastWord bw).signed = false := by
  unfold fastWord; split <;> rfl

theorem fastWord_bits (bw : Nat) (h : bw ≤ 128) : bw ≤ (fastWord bw).bits ∧ (fastWord bw).bits ≤ 128 := by
  unfold fastWord; split <;> simp [IntTy.bits] <;> omega

theorem mask_val (bw : Nat) (h : bw ≤ 128) :
    (JInt.wrap .u128 (2 ^ bw) - JInt.lit .u128 1).val = 2 ^ bw - 1 := by
  rw [val_sub', val_wrap', val_lit']
  have h1 : wrapInt .u128 1 = 1 := by decide
  rw [h1]
  rcases Nat.lt_or_ge bw 128 with hlt | hge
  · have hp : 2 ^ bw < 2 ^ 128 := Nat.pow_lt_pow_right (by decide) hlt
    have hp1 : 1 ≤ 2 ^ bw := Nat.one_le_two_pow
    rw [two_pow_int, wrapInt_unsigned (u := .u128) (z := ((2 ^ bw : Nat) : Int)) rfl (by omega) (by
        rw [show IntTy.u128.bits = 128 from rfl, two_pow_int]; exact_mod_cast hp)]
    rw [wrapInt_unsigned (u := .u128) (z := ((2 ^ bw : Nat) : Int) - 1) rfl (by omega) (by
        rw [show IntTy.u128.bits = 128 from rfl, two_pow_int]; omega)]
  · have : bw = 128 := by omega
    subst this
    decide

theorem mask_toNat (bw : Nat) (m : Int) (hm : m = 2 ^ bw - 1) : m.toNat = 2 ^ bw - 1 := by
  rw [hm, two_pow_int, show ((2 ^ bw : Nat) : Int) - 1 = ((2 ^ bw - 1 : Nat) : Int) by
    rw [Int.natCast_sub Nat.one_le_two_pow]; rfl, Int.toNat_natCast]

theorem band_val {u : IntTy} (hu : u.signed = false) (w mask : JInt u) (bw : Nat)
    (hm : mask.val = 2 ^ bw - 1) (hbw : bw ≤ u.bits) :
    (band w mask).val = ((w.val.toNat % 2 ^ bw : Nat) : Int) := by
  unfold band
  rw [val_wrap', mask_toNat bw _ hm, Nat.and_two_pow_sub_one_eq_mod]
  have : w.val.toNat % 2 ^ bw < 2 ^ u.bits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) hbw)
  exact wrapInt_unsigned hu (by omega) (by rw [two_pow_int]; exact_mod_cast this)

/-- What `fastSampler` stores. -/
theorem fastSampler_spec {t : IntTy} (ht : t.bits = 128) {a b : JInt t} {sp : Fast t}
    (h : fastSampler a b = .ok sp) :
    sp.a = a ∧ a.val ≤ b.val ∧ sp.m.val = b.val - a.val ∧ b.val - a.val < 2 ^ 128 ∧
    sp.bw = topSetBit (b.val - a.val).toNat ∧ sp.mask.val = 2 ^ sp.bw - 1 := by
  unfold fastSampler at h
  split at h
  · cases h
  · injection h with h
    subst h
    have ha := a.property
    have hb := b.property
    have hm : (JInt.rem .u128 (JInt.rem t.toUnsigned (b - a))).val = b.val - a.val := by
      simp only [val_rem', val_sub']
      cases t <;> simp [IntTy.bits] at ht <;>
        simp [wrapInt, IntTy.toUnsigned, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at ha hb ⊢ <;>
        omega
    have hd : b.val - a.val < 2 ^ 128 := by
      cases t <;> simp [IntTy.bits] at ht <;> simp [IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at ha hb ⊢ <;> omega
    dsimp only
    rw [hm]
    refine ⟨rfl, by omega, rfl, hd, rfl, ?_⟩
    apply mask_val
    have hd' : (b.val - a.val).toNat < 2 ^ 128 := by
      have : ((2 ^ 128 : Nat) : Int) = 2 ^ 128 := by norm_cast
      omega
    exact (topSetBit_spec _ hd').2

theorem lessThanMasked_spec {σ : Type} (g : Rng σ) (u : IntTy) (sup mask : JInt u) :
    ∀ fuel st x st', lessThanMasked g u sup mask fuel st = some (x, st') →
    ∃ n, (∀ i < n, sup.val < (band (g.wordAt (.int u) st i) mask).val) ∧
      x = band (g.wordAt (.int u) st n) mask ∧ x.val ≤ sup.val ∧
      st' = g.stateAfter (.int u) st (n + 1)
  | fuel, st, x, st', h => by
    unfold lessThanMasked at h
    dsimp only at h
    by_cases hle : (band ((g.next st (.int u)).1 : JInt u) mask).val ≤ sup.val
    · have hh : some (band ((g.next st (.int u)).1 : JInt u) mask, (g.next st (.int u)).2) =
          some (x, st') := by
        cases fuel <;> simpa [hle] using h
      injection hh with hh
      injection hh with h1 h2
      exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), h1.symm, h1 ▸ hle, h2.symm⟩
    · cases fuel with
      | zero => simp [hle] at h
      | succ f =>
        simp only [hle, ↓reduceIte] at h
        obtain ⟨n, h1, h2, h3, h4⟩ := lessThanMasked_spec g u sup mask f _ x st' h
        refine ⟨n + 1, ?_, ?_, h3, ?_⟩
        · intro i hi
          cases i with
          | zero => exact Int.lt_of_not_ge hle
          | succ i => rw [wordAt_succ']; exact h1 i (by omega)
        · rw [wordAt_succ']; exact h2
        · rw [stateAfter_succ']; exact h4

theorem fastStep_eq {t : IntTy} (sp : Fast t) (w : JInt (fastWord sp.bw)) :
    fastStep sp w = if w.val.toNat % 2 ^ sp.bw ≤ sp.m.val.toNat then
      some (JInt.wrap t ((w.val.toNat % 2 ^ sp.bw : Nat) : Int) + sp.a) else none := rfl

theorem fastUniform_proven : FastUniform := by
  intro t ht a b sp hsp
  obtain ⟨hspa, hab, hm, hd, hbw, hmask⟩ := fastSampler_spec ht hsp
  obtain ⟨hlt, hbw128⟩ := topSetBit_spec (b.val - a.val).toNat (by
    have : ((2 ^ 128 : Nat) : Int) = 2 ^ 128 := by norm_cast
    omega)
  rw [← hbw] at hlt hbw128
  have hu := fastWord_unsigned sp.bw
  obtain ⟨hwb, hw128⟩ := fastWord_bits sp.bw hbw128
  have hdN : (b.val - a.val).toNat < 2 ^ sp.bw := hlt
  have hsup : (JInt.rem (fastWord sp.bw) sp.m).val = b.val - a.val := by
    rw [val_rem', hm]
    apply wrapInt_unsigned hu (by omega)
    have := Nat.lt_of_lt_of_le hdN (Nat.pow_le_pow_right (by decide) hwb)
    rw [two_pow_int]; omega
  have hmk : (JInt.rem (fastWord sp.bw) sp.mask).val = 2 ^ sp.bw - 1 := by
    rw [val_rem', hmask, two_pow_int]
    have h1 : 1 ≤ 2 ^ sp.bw := Nat.one_le_two_pow
    have h2 := Nat.pow_le_pow_right (n := 2) (by decide) hwb
    apply wrapInt_unsigned hu (by omega)
    rw [two_pow_int]; omega
  -- the accepted value of a word
  have hval : ∀ w : JInt (fastWord sp.bw), w.val.toNat % 2 ^ sp.bw ≤ (b.val - a.val).toNat →
      (JInt.wrap t ((w.val.toNat % 2 ^ sp.bw : Nat) : Int) + sp.a).val =
        a.val + ((w.val.toNat % 2 ^ sp.bw : Nat) : Int) := by
    intro w hw
    rw [hspa]
    generalize w.val.toNat % 2 ^ sp.bw = k at hw ⊢
    exact wrap_add_val _ a b (by omega) (by omega)
  have hmtn : sp.m.val.toNat = (b.val - a.val).toNat := by rw [hm]
  refine ⟨?_, ?_⟩
  · intro σ g fuel st res h
    simp only [fastRand] at h
    cases hl : lessThanMasked g (fastWord sp.bw) (JInt.rem (fastWord sp.bw) sp.m)
        (JInt.rem (fastWord sp.bw) sp.mask) fuel st with
    | none => simp [hl] at h
    | some q =>
      obtain ⟨x, st'⟩ := q
      simp only [hl, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨n, h1, h2, h3, h4⟩ := lessThanMasked_spec g _ _ _ fuel st x st' hl
      have hbv : ∀ i, (band (g.wordAt (.int (fastWord sp.bw)) st i)
          (JInt.rem (fastWord sp.bw) sp.mask)).val =
          (((g.wordAt (.int (fastWord sp.bw)) st i : JInt (fastWord sp.bw)).val.toNat % 2 ^ sp.bw :
            Nat) : Int) := fun i => band_val hu _ _ sp.bw hmk hwb
      have hacc := h3
      rw [h2, hbv, hsup] at hacc
      have hx : x.val = (((g.wordAt (.int (fastWord sp.bw)) st n : JInt (fastWord sp.bw)).val.toNat %
          2 ^ sp.bw : Nat) : Int) := by rw [h2, hbv]
      have hacc' : (g.wordAt (.int (fastWord sp.bw)) st n : JInt (fastWord sp.bw)).val.toNat %
          2 ^ sp.bw ≤ (b.val - a.val).toNat := by omega
      have hvalue : JInt.rem t (JInt.rem .u128 x) + sp.a =
          JInt.wrap t (((g.wordAt (.int (fastWord sp.bw)) st n : JInt (fastWord sp.bw)).val.toNat %
            2 ^ sp.bw : Nat) : Int) + sp.a := by
        congr 1
        apply Subtype.ext
        rw [val_rem', val_rem', val_wrap', wrapInt_unsigned (u := .u128) (z := x.val) rfl (by omega) (by
          have := Nat.lt_of_lt_of_le (Nat.mod_lt
            (g.wordAt (.int (fastWord sp.bw)) st n : JInt (fastWord sp.bw)).val.toNat
            (Nat.two_pow_pos sp.bw)) (Nat.pow_le_pow_right (by decide) hbw128)
          rw [show IntTy.u128.bits = 128 from rfl, two_pow_int]; omega), hx]
      refine ⟨_, _, n, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · have := hval _ hacc'; rw [hvalue, this]; omega
      · have := hval _ hacc'; rw [hvalue, this]; omega
      · intro i hi
        have := h1 i hi
        rw [hbv, hsup] at this
        rw [fastStep_eq sp (g.wordAt (.int (fastWord sp.bw)) st i), hmtn, if_neg (by omega)]
      · rw [fastStep_eq sp (g.wordAt (.int (fastWord sp.bw)) st n), hmtn, if_pos hacc', hvalue]
      · exact h4
  · refine ⟨2 ^ ((fastWord sp.bw).bits - sp.bw), Nat.two_pow_pos _, ?_⟩
    intro v hav hvb
    have hc : (v.val - a.val).toNat < 2 ^ sp.bw := by omega
    rw [countBelow_congr (q := fun w => decide (w % 2 ^ sp.bw = (v.val - a.val).toNat)),
      show 2 ^ (fastWord sp.bw).bits = 2 ^ ((fastWord sp.bw).bits - sp.bw) * 2 ^ sp.bw by
        rw [← Nat.pow_add, Nat.sub_add_cancel hwb]]
    · exact countBelow_mod _ _ hc _
    · intro w hw
      have hww : (JInt.wrap (fastWord sp.bw) w).val.toNat = w := wrap_toNat_unsigned hu hw
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_iff]
      rw [fastStep_eq sp (JInt.wrap (fastWord sp.bw) w), hmtn, hww]
      by_cases hacc : w % 2 ^ sp.bw ≤ (b.val - a.val).toNat
      · rw [if_pos hacc, Option.some.injEq, Subtype.ext_iff]
        have := hval (JInt.wrap (fastWord sp.bw) w) (by rw [hww]; exact hacc)
        rw [hww] at this
        rw [this]
        omega
      · rw [if_neg hacc]
        simp only [reduceCtorEq, false_iff]
        omega

end JuliaLean.RandomSampling
