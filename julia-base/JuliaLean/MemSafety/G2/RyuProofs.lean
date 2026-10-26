import JuliaLean.MemSafety.G2.Model

namespace JuliaLean.MemSafety.G2

open JuliaLean JuliaLean.Float JuliaLean.ParsePrint JuliaLean.ParsePrint.Ryu

set_option maxHeartbeats 200000
set_option maxRecDepth 256

private def slowStep (s : St) : St :=
  let cd := udivLit s.c 10
  let ad := udivLit s.a 10
  let am := mod10 s.a ad
  let bd := udivLit s.b 10
  let bm := mod10 s.b bd
  ⟨ad, bd, cd, s.e10 + 1, s.aAll && (am.val == 0),
    s.bAll && (s.bLast.val == 0), JInt.rem .u8 bm, s.roundup⟩

private def aZeroStep (s : St) : St :=
  let cd := udivLit s.c 10
  let bd := udivLit s.b 10
  let bm := mod10 s.b bd
  ⟨udivLit s.a 10, bd, cd, s.e10 + 1, s.aAll,
    s.bAll && (s.bLast.val == 0), JInt.rem .u8 bm, s.roundup⟩

private def fastStep (s : St) : St :=
  let cd := udivLit s.c 10
  let ad := udivLit s.a 10
  let bd := udivLit s.b 10
  let bm := mod10 s.b bd
  ⟨ad, bd, cd, s.e10 + 1, s.aAll, s.bAll, s.bLast, decide (bm.val ≥ 5)⟩

private def maxStep (s : St) : St :=
  let bd := udivLit s.b 10
  let bm := mod10 s.b bd
  ⟨s.a, bd, s.c, s.e10 + 1, s.aAll, s.bAll && (bm.val == 0), s.bLast,
    if s.bAll && (bd.val % 2 == 0) then decide (bm.val > 5) else decide (bm.val ≥ 5)⟩

private theorem slowLoop_e10 (n : Nat) (s : St) :
    s.e10 ≤ (slowLoop n s).e10 ∧ (slowLoop n s).e10 ≤ s.e10 + n := by
  induction n generalizing s with
  | zero => simp [slowLoop]
  | succ n ih =>
      simp only [slowLoop]
      split
      · omega
      · change s.e10 ≤ (slowLoop n (slowStep s)).e10 ∧
          (slowLoop n (slowStep s)).e10 ≤ s.e10 + ↑(n + 1)
        have h := ih (slowStep s)
        dsimp [slowStep] at h ⊢
        omega

private theorem aZeroLoop_e10 (m : Option Int) (n : Nat) (s : St) :
    s.e10 ≤ (aZeroLoop m n s).e10 ∧ (aZeroLoop m n s).e10 ≤ s.e10 + n := by
  cases m with
  | none =>
    induction n generalizing s with
    | zero => simp [aZeroLoop]
    | succ n ih =>
      simp only [aZeroLoop]
      split
      · omega
      · change s.e10 ≤ (aZeroLoop none n (aZeroStep s)).e10 ∧
          (aZeroLoop none n (aZeroStep s)).e10 ≤ s.e10 + ↑(n + 1)
        have h := ih (aZeroStep s)
        dsimp [aZeroStep] at h ⊢
        omega
  | some m =>
    induction n generalizing s with
    | zero => simp [aZeroLoop]
    | succ n ih =>
      simp only [aZeroLoop]
      split
      · omega
      · change s.e10 ≤ (aZeroLoop (some m) n (aZeroStep s)).e10 ∧
          (aZeroLoop (some m) n (aZeroStep s)).e10 ≤ s.e10 + ↑(n + 1)
        have h := ih (aZeroStep s)
        dsimp [aZeroStep] at h ⊢
        omega

private theorem fastLoop_e10 (n : Nat) (s : St) :
    s.e10 ≤ (fastLoop n s).e10 ∧ (fastLoop n s).e10 ≤ s.e10 + n := by
  induction n generalizing s with
  | zero => simp [fastLoop]
  | succ n ih =>
      simp only [fastLoop]
      split
      · omega
      · change s.e10 ≤ (fastLoop n (fastStep s)).e10 ∧
          (fastLoop n (fastStep s)).e10 ≤ s.e10 + ↑(n + 1)
        have h := ih (fastStep s)
        dsimp [fastStep] at h ⊢
        omega

private theorem maxLoop_e10 (m : Int) (n : Nat) (s : St) :
    s.e10 ≤ (maxLoop m n s).e10 ∧ (maxLoop m n s).e10 ≤ s.e10 + n := by
  induction n generalizing s with
  | zero => simp [maxLoop]
  | succ n ih =>
      simp only [maxLoop]
      split
      · omega
      · change s.e10 ≤ (maxLoop m n (maxStep s)).e10 ∧
          (maxLoop m n (maxStep s)).e10 ≤ s.e10 + ↑(n + 1)
        have h := ih (maxStep s)
        dsimp [maxStep] at h ⊢
        omega

private theorem zeroLoop_e10 (n : Nat) (b : RyuU64) (e : Int) :
    e ≤ (zeroLoop n (b, e)).2 ∧ (zeroLoop n (b, e)).2 ≤ e + n := by
  induction n generalizing b e with
  | zero => simp [zeroLoop]
  | succ n ih =>
      simp only [zeroLoop]
      split
      · omega
      · have h := ih (udivLit b 10) (e + 1)
        omega

private theorem log10pow2_range (e : Int) (h0 : 0 ≤ e) (h1 : e ≤ 969) :
    -1 ≤ log10pow2 e - (if e > 3 then 1 else 0) ∧
      log10pow2 e - (if e > 3 then 1 else 0) ≤ 292 := by
  unfold log10pow2
  split <;> omega

private theorem log10pow5_range (n : Int) (h0 : 1 ≤ n) (h1 : n ≤ 1076) :
    -400 ≤ log10pow5 n - (if n > 1 then 1 else 0) - n ∧
      log10pow5 n - (if n > 1 then 1 else 0) - n ≤ 0 := by
  unfold log10pow5
  split <;> omega

private theorem ryuInitialState_e10 (e2 : Int) (mfIsEven uShiftHalf : Bool)
    (u v w : RyuU64) (hlo : -1076 ≤ e2) (hhi : e2 ≤ 969) :
    -400 ≤ (ryuInitialState e2 mfIsEven uShiftHalf u v w).e10 ∧
      (ryuInitialState e2 mfIsEven uShiftHalf u v w).e10 ≤ 300 := by
  change -400 ≤ ryuInitialE10 e2 ∧ ryuInitialE10 e2 ≤ 300
  unfold ryuInitialE10
  split
  · have hq := log10pow2_range e2 (by omega) hhi
    omega
  · have hq := log10pow5_range (-e2) (by omega) (by omega)
    omega

private theorem ryuRoundState_e10 (mfIsEven : Bool) (m : Option Int) (s0 : St) :
    s0.e10 ≤ (ryuRoundState mfIsEven m s0).e10 ∧
      (ryuRoundState mfIsEven m s0).e10 ≤ s0.e10 + 48 := by
  unfold ryuRoundState
  split
  · generalize hs1 : slowLoop fuel s0 = s1
    have hslow := slowLoop_e10 fuel s0
    rw [hs1] at hslow
    dsimp only
    split
    · generalize hs2 : aZeroLoop m fuel s1 = s2
      have hzero := aZeroLoop_e10 m fuel s1
      rw [hs2] at hzero
      split
      all_goals simp only [fuel] at hslow hzero ⊢; omega
    · split
      all_goals simp only [fuel] at hslow ⊢; omega
  · dsimp only
    split
    · have hfast := fastLoop_e10 fuel
        (⟨udivLit s0.a 100, udivLit s0.b 100, udivLit s0.c 100, s0.e10 + 2,
          s0.aAll, s0.bAll, s0.bLast,
          decide ((mod100 s0.b (udivLit s0.b 100)).val ≥ 50)⟩ : St)
      simp only [fuel] at hfast ⊢
      omega
    · have hfast := fastLoop_e10 fuel { s0 with roundup := decide (s0.bLast.val ≥ 5) }
      simp only [fuel] at hfast ⊢
      omega

private theorem ryuFinish_e10 (mfIsEven : Bool) (m : Option Int) (s0 : St)
    (hlo : -400 ≤ s0.e10) (hhi : s0.e10 ≤ 300) :
    -400 ≤ (ryuFinish mfIsEven m s0).2 ∧ (ryuFinish mfIsEven m s0).2 ≤ 400 := by
  have hr := ryuRoundState_e10 mfIsEven m s0
  simp only [ryuFinish]
  generalize hs : ryuRoundState mfIsEven m s0 = s
  rw [hs] at hr
  cases m with
  | none => simp only; omega
  | some M =>
    simp only
    split
    · have hm := maxLoop_e10 M fuel s
      have hz := zeroLoop_e10 fuel
        ((maxLoop M fuel s).b + ofBool .u64 (maxLoop M fuel s).roundup)
        (maxLoop M fuel s).e10
      simp only [fuel] at hm hz ⊢
      omega
    · omega

private theorem ryuCore_e10 (rawM : RyuU64) (rawE ef : Int) (mf : RyuU64)
    (maxsignif : Option Int) (hlo : -1074 ≤ ef) (hhi : ef ≤ 971) :
    -400 ≤ (ryuCore rawM rawE ef mf maxsignif).2 ∧
      (ryuCore rawM rawE ef mf maxsignif).2 ≤ 400 := by
  unfold ryuCore
  let even := mf.val % 2 == 0
  let v : RyuU64 := JInt.lit .u64 4 * mf
  let w : RyuU64 := v + JInt.lit .u64 2
  let half := rawM.val == 0 && decide (rawE > 1)
  let u : RyuU64 := v - JInt.lit .u64 2 + ofBool .u64 half
  have hi := ryuInitialState_e10 (ef - 2) even half u v w (by omega) (by omega)
  exact ryuFinish_e10 even maxsignif (ryuInitialState (ef - 2) even half u v w) hi.1 hi.2

private theorem ryuFixupE_bounds (rawE ef : Int)
    (he0 : 0 ≤ rawE) (he1 : rawE ≤ 2046) (hef : ef = rawE - 1023 - 52) :
    -1074 ≤ ryuFixupE rawE ef ∧ ryuFixupE rawE ef ≤ 971 := by
  unfold ryuFixupE
  by_cases hz : rawE = 0
  · have hbeq : (rawE == 0) = true := by simp [hz]
    rw [if_pos hbeq]
    omega
  · have hbeq : ¬(rawE == 0) = true := by simp [hz]
    rw [if_neg hbeq]
    constructor
    · rw [hef]
      omega
    · rw [hef]
      omega

set_option maxHeartbeats 2000000 in
private theorem ryuReduceFromParts_e10 (rawM : RyuU64) (rawE ef : Int) (mf : RyuU64)
    (m : Option Int) (he0 : 0 ≤ rawE) (he1 : rawE ≤ 2046)
    (hef : ef = rawE - 1023 - 52) :
    -400 ≤ (ryuReduceFromParts rawM rawE ef mf m).2 ∧
      (ryuReduceFromParts rawM rawE ef mf m).2 ≤ 400 := by
  unfold ryuReduceFromParts
  by_cases hlong : ryuLongPath mf ef = true
  · rw [if_pos hlong]
    have hf := ryuFixupE_bounds rawE ef he0 he1 hef
    exact ryuCore_e10 rawM rawE (ryuFixupE rawE ef)
      (ryuFixupM rawM rawE mf) m hf.1 hf.2
  · rw [if_neg hlong]
    cases m with
    | none =>
      simp only
      have hz := zeroLoop_e10 fuel (shrI mf (-ef)) 0
      simp only [fuel] at hz ⊢
      omega
    | some M =>
      simp only
      split
      · let b := shrI mf (-ef)
        let s0 : St := ⟨b, b, b, 0, false, true, JInt.lit .u8 0, false⟩
        have hm := maxLoop_e10 M fuel s0
        have hz := zeroLoop_e10 fuel
          ((maxLoop M fuel s0).b + ofBool .u64 (maxLoop M fuel s0).roundup)
          (maxLoop M fuel s0).e10
        dsimp [b, s0] at hm hz ⊢
        simp only [fuel] at hm hz ⊢
        omega
      · have hz := zeroLoop_e10 fuel (shrI mf (-ef)) 0
        simp only [fuel] at hz ⊢
        omega

private theorem ryuReduceModel_e10 (x : F64) (m : Option Int)
    (hfinite : F64.isfinite x = true) :
    let r := ryuReduceModel x m; -400 ≤ r.2 ∧ r.2 ≤ 400 := by
  unfold ryuReduceModel
  apply ryuReduceFromParts_e10
  · omega
  · have heq : F64.exponentField x = F64.toBits x / 2^52 % 2048 := rfl
    have hm := Nat.mod_lt (F64.toBits x / 2^52) (by omega : 0 < 2048)
    have hne : F64.exponentField x ≠ 2047 := by
      simpa [F64.isfinite] using hfinite
    rw [heq] at hne ⊢
    omega
  · rfl

private theorem ryuSmallInitialState_e10 (x : RyuSmall) (e2 : Int)
    (mfIsEven uShiftHalf : Bool) (u v w : Nat)
    (hlo : -151 ≤ e2) (hhi : e2 ≤ 103) :
    -400 ≤ (ryuSmallInitialState x e2 mfIsEven uShiftHalf u v w).e10 ∧
      (ryuSmallInitialState x e2 mfIsEven uShiftHalf u v w).e10 ≤ 300 := by
  change -400 ≤ ryuSmallInitialE10 e2 ∧ ryuSmallInitialE10 e2 ≤ 300
  unfold ryuSmallInitialE10 log10pow2 log10pow5
  split <;> simp_all <;> omega

private theorem ryuSmallCore_e10 (x : RyuSmall) (rawM : Nat) (rawE ef : Int)
    (mf : Nat) (m : Option Int) (hlo : -149 ≤ ef) (hhi : ef ≤ 105) :
    -400 ≤ (ryuSmallCore x rawM rawE ef mf m).2 ∧
      (ryuSmallCore x rawM rawE ef mf m).2 ≤ 400 := by
  unfold ryuSmallCore
  let even := mf % 2 == 0
  let v := x.wrap (4 * mf)
  let w := x.wrap (v + 2)
  let half := rawM == 0 && decide (rawE > 1)
  let u := x.wrap (x.sub v 2 + if half then 1 else 0)
  have hi := ryuSmallInitialState_e10 x (ef - 2) even half u v w (by omega) (by omega)
  exact ryuFinish_e10 even m (ryuSmallInitialState x (ef - 2) even half u v w)
    hi.1 hi.2

private theorem ryuSmallEf_bounds (x : RyuSmall) :
    -149 ≤ ryuSmallFixedEf x ∧ ryuSmallFixedEf x ≤ 105 := by
  cases x with
  | f16 bits =>
      have hr := Nat.mod_lt (bits.val / 2^10) (by decide : 0 < 2^5)
      unfold ryuSmallFixedEf ryuSmallEf RyuSmall.rawE
      simp only [RyuSmall.exponentBits, RyuSmall.exponentBias, RyuSmall.significandBits]
      let e : Int := Int.ofNat (bits.val / 2^10 % 2^5)
      have he : e < 2^5 := by exact Int.ofNat_lt.mpr hr
      have he0 : 0 ≤ e := Int.ofNat_nonneg _
      change -149 ≤ (if e = 0 then 1 - 15 - 10 else e - 15 - 10) ∧
        (if e = 0 then 1 - 15 - 10 else e - 15 - 10) ≤ 105
      by_cases hz : e = 0 <;> simp [hz] <;> omega
  | f32 bits =>
      have hr := Nat.mod_lt (bits.val / 2^23) (by decide : 0 < 2^8)
      unfold ryuSmallFixedEf ryuSmallEf RyuSmall.rawE
      simp only [RyuSmall.exponentBits, RyuSmall.exponentBias, RyuSmall.significandBits]
      let e : Int := Int.ofNat (bits.val / 2^23 % 2^8)
      have he : e < 2^8 := by exact Int.ofNat_lt.mpr hr
      have he0 : 0 ≤ e := Int.ofNat_nonneg _
      change -149 ≤ (if e = 0 then 1 - 127 - 23 else e - 127 - 23) ∧
        (if e = 0 then 1 - 127 - 23 else e - 127 - 23) ≤ 105
      by_cases hz : e = 0 <;> simp [hz] <;> omega

private theorem ryuSmallReduce_e10 (x : RyuSmall) (m : Option Int) :
    -400 ≤ (ryuSmallReduce x m).2 ∧ (ryuSmallReduce x m).2 ≤ 400 := by
  have hef := ryuSmallEf_bounds x
  unfold ryuSmallReduce
  dsimp only
  split
  · exact ryuSmallCore_e10 x x.rawM x.rawE
      (ryuSmallFixedEf x)
      (if x.rawE = 0 then x.rawM
       else x.wrap (2 ^ x.significandBits + x.rawM)) m hef.1 hef.2
  · cases m with
    | none =>
      simp only
      have hz := zeroLoop_e10 fuel
        (JInt.lit .u64
          (x.wrap (x.wrap (2 ^ x.significandBits + x.rawM) /
            2 ^ (-ryuSmallEf x).toNat))) 0
      simp only [fuel] at hz ⊢
      omega
    | some M =>
      simp only
      split
      · let b := JInt.lit .u64
          (x.wrap (x.wrap (2 ^ x.significandBits + x.rawM) /
            2 ^ (-ryuSmallEf x).toNat))
        let s0 : St := ⟨b, b, b, 0, false, true, JInt.lit .u8 0, false⟩
        have hm := maxLoop_e10 M fuel s0
        have hz := zeroLoop_e10 fuel
          ((maxLoop M fuel s0).b + ofBool .u64 (maxLoop M fuel s0).roundup)
          (maxLoop M fuel s0).e10
        dsimp [b, s0] at hm hz ⊢
        simp only [fuel] at hm hz ⊢
        omega
      · have hz := zeroLoop_e10 fuel
          (JInt.lit .u64
            (x.wrap (x.wrap (2 ^ x.significandBits + x.rawM) /
              2 ^ (-ryuSmallEf x).toNat))) 0
        simp only [fuel] at hz ⊢
        omega

set_option maxRecDepth 2048 in
theorem ryuExponentTableInBounds : RyuExponentTableInBounds := by
  constructor
  · intro x compact access ha
    simp only [ryuExponentAccesses] at ha
    split at ha
    · simp at ha
    ·
      have hfinite : F64.isfinite x = true := by simp_all
      generalize hr : ryuReduceModel x (if compact then some 999999 else none) = result at ha
      obtain ⟨output, nexp⟩ := result
      simp only [Prod.fst, Prod.snd] at ha
      have hb := ryuReduceModel_e10 x (if compact then some 999999 else none) hfinite
      rw [hr] at hb
      dsimp only at hb
      have hd : (ryuDecimalLength output).val ≤ 17 := by
        have := (ryuDecimalLength output).isLt
        omega
      split at ha
      · split at ha
        · simp at ha
          subst access
          simp only [Access.inBounds]
          omega
        · split at ha
          · simp at ha
            subst access
            simp only [Access.inBounds]
            omega
          · simp at ha
      · split at ha
        · simp at ha
          subst access
          simp only [Access.inBounds]
          omega
        · split at ha
          · simp at ha
            subst access
            simp only [Access.inBounds]
            omega
          · simp at ha
  · intro x compact access ha
    simp only [ryuSmallExponentAccesses] at ha
    split at ha
    · simp at ha
    ·
      generalize hr : ryuSmallReduce x (if compact then some 999999 else none) = result at ha
      obtain ⟨output, nexp⟩ := result
      simp only [Prod.fst, Prod.snd] at ha
      have hb := ryuSmallReduce_e10 x (if compact then some 999999 else none)
      rw [hr] at hb
      dsimp only at hb
      have hd : (ryuDecimalLength output).val ≤ 17 := by
        have := (ryuDecimalLength output).isLt
        omega
      split at ha
      · split at ha
        · simp at ha
          subst access
          simp only [Access.inBounds]
          omega
        · split at ha
          · simp at ha
            subst access
            simp only [Access.inBounds]
            omega
          · simp at ha
      · split at ha
        · simp at ha
          subst access
          simp only [Access.inBounds]
          omega
        · split at ha
          · simp at ha
            subst access
            simp only [Access.inBounds]
            omega
          · simp at ha

end JuliaLean.MemSafety.G2
