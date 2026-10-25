import JuliaLean.RegexUnicode.CoreWrappers

/-!
# Lemmas about the regex wrappers

Bridges from `exec`, `match` and `SubString` construction to the integer-level
index theory of the String model.
-/

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

theorem liftS_ok {α : Type} {x : SJl α} {a : α} (h : liftS x = .ok a) : x = .ok a := by
  cases x with
  | error e => simp [liftS, Except.mapError] at h
  | ok b => simp [liftS, Except.mapError] at h; rw [h]

theorem convert_ok {t : IntTy} {x : Int} (h : t.min ≤ x ∧ x ≤ t.max) :
    JInt.convert t x = .ok ⟨x, h⟩ := by
  unfold JInt.convert; rw [dif_pos h]

theorem convert_err {t : IntTy} {x : Int} (h : ¬ (t.min ≤ x ∧ x ≤ t.max)) :
    JInt.convert t x = .error (.inexactError t.name) := by
  unfold JInt.convert; rw [dif_neg h]

theorem u64_min : IntTy.u64.min = 0 := by decide

theorem exec_ok {P : Pcre} {s : JStr} {offset : JInt64} {opts : UInt32} {x : Option Ovec}
    (h : exec P s offset opts = .ok x) :
    0 ≤ offset.val ∧ offset.val ≤ s.bytes.length ∧ P.run s offset.val.toNat opts = x := by
  unfold exec at h
  by_cases hc : IntTy.u64.min ≤ offset.val ∧ offset.val ≤ IntTy.u64.max
  · rw [convert_ok hc] at h
    dsimp only at h
    by_cases hl : offset.val > (s.bytes.length : Int)
    · rw [if_pos hl] at h; cases h
    · rw [if_neg hl] at h
      cases h
      rw [u64_min] at hc
      exact ⟨hc.1, by omega, rfl⟩
  · rw [convert_err hc] at h; cases h

theorem sub1_val (x : JInt64) (h0 : 0 ≤ (x - ix 1).val) (h1 : (x - ix 1).val < 2 ^ 62) :
    (x - ix 1).val = x.val - 1 := by
  have hx := x.2
  have e : (x - ix 1).val = wrapInt .i64 (x.val - (ix 1).val) := rfl
  rw [ix1] at e
  simp only [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max, if_true] at e hx
  omega

theorem substring_ok (s : JStr) (i j : JInt64) (ss : JSub) (h : substring s i j = .ok ss) :
    (j.val < i.val ∧ ss.ncu.val = 0) ∨
    (i.val ≤ j.val ∧ 1 ≤ i.val ∧ j.val ≤ s.bytes.length ∧ validZ s j.val ∧
      ∃ j', nextind s j = .ok j' ∧ ss.ncu = j' - i) := by
  unfold substring at h
  by_cases hij : i.val ≤ j.val
  · right
    by_cases c1 : 1 ≤ i.val ∧ j.val ≤ (ncodeunits s).val
    · by_cases c2 : isvalidAt s i = true
      · by_cases c3 : isvalidAt s j = true
        · simp only [hij, c1, c2, c3, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
            Bool.and_self] at h
          split at h
          · cases h
          · rename_i j' hj'
            cases h
            rw [ncu_val] at c1
            exact ⟨hij, c1.1, c1.2, (isvalidAt_iff s j).1 c3, j', hj', rfl⟩
        · simp [hij, c1, c2, c3] at h
      · simp [hij, c1, c2] at h
    · simp only [hij, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at h
      have c1' : (decide (1 ≤ i.val) && decide (j.val ≤ (ncodeunits s).val)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp [c1'] at h
  · left
    simp only [hij, decide_false, Bool.not_false, ite_true] at h
    cases h
    exact ⟨by omega, rfl⟩

theorem capSub_sub (s : JStr) (a b : Int) (ss : JSub) (j0 : JInt64)
    (hp : prevind s (ix (b + 1)) = .ok j0) (h : capSub s a b = .ok ss) :
    substring s (ix (a + 1)) j0 = .ok ss := by
  unfold capSub at h
  rw [hp] at h
  exact liftS_ok h

theorem capSub_ok (s : JStr) (a b : Int) (ss : JSub) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ s.bytes.length) (h : capSub s a b = .ok ss) :
    (ss.ncu.val = 0 ∨
      (1 ≤ ss.ncu.val ∧ a + 1 + ss.ncu.val ≤ s.bytes.length + 1 ∧ a + 1 ≤ s.bytes.length)) ∧
    (a < b → validZ s (a + 1) → ss.ncu.val ≠ 0) := by
  have hs := ncu_small s
  have ea : (ix (a + 1)).val = a + 1 := ix_val _ (by omega) (by omega)
  have eb : (ix (b + 1)).val = b + 1 := ix_val _ (by omega) (by omega)
  obtain ⟨j0, hj0, hj0'⟩ := previndN_one s (ix (b + 1)) (by omega) (by omega)
  have hp : prevind s (ix (b + 1)) = .ok j0 := hj0
  have hsub := capSub_sub s a b ss j0 hp h
  have main : (j0.val < a + 1 ∧ ss.ncu.val = 0) ∨
      (a + 1 ≤ j0.val ∧ 1 ≤ ss.ncu.val ∧ a + 1 + ss.ncu.val ≤ s.bytes.length + 1 ∧
        a + 1 ≤ s.bytes.length) := by
    rcases substring_ok s _ _ ss hsub with ⟨hlt, h0⟩ | ⟨hij, h1, h2, hv, j', hj', hn⟩
    · rw [ea] at hlt; exact Or.inl ⟨hlt, h0⟩
    · right
      rw [ea] at hij h1
      obtain ⟨j'', hj'', hv''⟩ := nextind_mid s j0 (by omega) h2
      rw [hj'] at hj''
      simp only [Except.ok.injEq] at hj''
      subst hj''
      obtain ⟨n1, n2, _, _⟩ := nextZ_spec s j0.val (by omega) h2
      have e : ss.ncu.val = j'.val - (a + 1) := by
        rw [hn, sub_val _ _ (by omega) (by omega), ea]
      refine ⟨hij, by omega, by omega, by omega⟩
  refine ⟨?_, fun hlt hv => ?_⟩
  · rcases main with ⟨_, h0⟩ | ⟨_, h1, h2, h3⟩
    · exact Or.inl h0
    · exact Or.inr ⟨h1, h2, h3⟩
  · rcases hj0' with ⟨h1, _⟩ | ⟨_, hpv⟩
    · omega
    · rw [eb] at hpv
      have hge : a + 1 ≤ j0.val := by
        rcases Int.lt_or_le j0.val (a + 1) with hc | hc
        · exact absurd hv (hpv.2.2.2 (a + 1) hc (by omega))
        · exact hc
      rcases main with ⟨hlt', _⟩ | ⟨_, h1, _, _⟩
      · omega
      · omega

theorem regexMatch_raw {re : Regex} {s : JStr} {idx : JInt64} {opts : UInt32} {m : RegexMatch}
    (h : regexMatch re s idx opts = .ok (some m)) :
    ∃ v, exec re.pcre s (idx - ix 1) (re.matchOptions ||| opts) = .ok (some v) ∧
      capSub s v.start v.stop = .ok m.mat ∧ m.offset = ix (v.start + 1) := by
  unfold regexMatch at h
  split at h
  · cases h
  · cases h
  rename_i v hex
  generalize hc : capSub s v.start v.stop = C at h
  cases C with
  | error e => cases h
  | ok mat =>
    dsimp only at h
    split at h
    · cases h
    simp only [Except.ok.injEq, Option.some.injEq] at h
    refine ⟨v, hex, ?_, ?_⟩
    · rw [← h]; exact hc
    · rw [← h]

/-- What a successful `match` returned. -/
theorem regexMatch_some {re : Regex} {s : JStr} {idx : JInt64} {opts : UInt32} {m : RegexMatch}
    (h : regexMatch re s idx opts = .ok (some m)) :
    ∃ v, 1 ≤ idx.val ∧ idx.val ≤ s.bytes.length + 1 ∧
      re.pcre.run s (idx.val - 1).toNat (re.matchOptions ||| opts) = some v ∧
      0 ≤ v.start ∧ v.start ≤ v.stop ∧ v.stop ≤ s.bytes.length ∧ idx.val ≤ v.start + 1 ∧
      m.offset.val = v.start + 1 ∧ capSub s v.start v.stop = .ok m.mat := by
  have hs := ncu_small s
  obtain ⟨v, hex, hc, hmo⟩ := regexMatch_raw h
  obtain ⟨h0, h1, hr⟩ := exec_ok hex
  have e1 := sub1_val idx h0 (by omega)
  have ho : (idx - ix 1).val.toNat ≤ s.bytes.length := by omega
  have hge := re.pcre.start_ge _ _ _ _ ho hr
  have hle := re.pcre.start_le_stop _ _ _ _ ho hr
  have hst := re.pcre.stop_le _ _ _ _ ho hr
  have hoff : (ix (v.start + 1)).val = v.start + 1 := ix_val _ (by omega) (by omega)
  rw [e1] at hr
  refine ⟨v, by omega, by omega, hr, by omega, hle, hst, by omega, ?_, hc⟩
  rw [hmo]; exact hoff

theorem regexMatch_bounds {re : Regex} {s : JStr} {idx : JInt64} {opts : UInt32}
    {x : Option RegexMatch} (h : regexMatch re s idx opts = .ok x) :
    1 ≤ idx.val ∧ idx.val ≤ s.bytes.length + 1 := by
  have hs := ncu_small s
  cases hex : exec re.pcre s (idx - ix 1) (re.matchOptions ||| opts) with
  | error e => unfold regexMatch at h; rw [hex] at h; cases h
  | ok y =>
    obtain ⟨h0, h1, _⟩ := exec_ok hex
    have e1 := sub1_val idx h0 (by omega)
    omega

end JuliaLean.RegexUnicode.Core
