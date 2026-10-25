import JuliaLean.Dates.Props

namespace JuliaLean.Dates
open JuliaLean
set_option maxHeartbeats 1000000

private theorem wrap_small (x : Int) (h : -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807) :
    (JInt.wrap .i64 x).val = x :=
  wrapInt_of_inRange .i64 x h

private theorem add_val (a b : I) : (a+b).val = wrapInt .i64 (a.val+b.val) := rfl

private theorem mod_small (d : I) (n : Int) (hn : 0 < n) (hb : n ≤ 9223372036854775807) :
    (qmod d n).val = d.val % n := by
  apply wrap_small
  have h0 := Int.emod_nonneg d.val (by omega : n ≠ 0)
  have h1 := Int.emod_lt_of_pos d.val hn
  omega

theorem weekdayAgreement_proven : WeekdayAgreement := by
  intro d
  have h0 := Int.emod_nonneg d.val (by decide : (7 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos d.val (by decide : (0 : Int) < 7)
  have hm := mod_small d 7 (by decide) (by decide)
  dsimp only [dayofweek,mod1]
  simp only [hm]
  by_cases h : d.val % 7 = 0
  · simp [h,i,JInt.lit,JInt.wrap,wrapInt,IntTy.signed,IntTy.bits]
  · simp only [h,ite_false,hm]
    exact ⟨True.intro,by omega,by omega⟩

theorem timeNormalized_proven : TimeNormalized := by
  intro n
  have hm := mod_small n 86400000000000 (by decide) (by decide)
  change 0 ≤ (qmod n 86400000000000).val ∧ (qmod n 86400000000000).val < 86400000000000
  rw [hm]
  exact ⟨Int.emod_nonneg _ (by decide),Int.emod_lt_of_pos _ (by decide)⟩

theorem monthLengths_proven : MonthLengths := by
  intro y m ld h
  unfold daysinmonth at h
  split at h
  · contradiction
  · rename_i hm
    have bounds : 1 ≤ m.val ∧ m.val ≤ 12 := by omega
    have cases : m.val = 1 ∨ m.val = 2 ∨ m.val = 3 ∨ m.val = 4 ∨ m.val = 5 ∨
        m.val = 6 ∨ m.val = 7 ∨ m.val = 8 ∨ m.val = 9 ∨ m.val = 10 ∨
        m.val = 11 ∨ m.val = 12 := by omega
    rcases cases with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
      simp only [h1] at h <;> split at h <;>
      simp_all [i,JInt.lit,JInt.wrap,wrapInt,IntTy.signed,IntTy.bits] <;>
      cases h <;> decide

private theorem clamp (c : Civil) (y m : I) (r : Civil)
    (hd : 0 < c.d.val)
    (h : (do
      let ld ← daysinmonth y m
      pure (⟨y,m,if c.d ≤ ld then c.d else ld⟩ : Civil)) = .ok r) :
    r.d.val ≤ c.d.val ∧ 1 ≤ r.d.val ∧ r.d.val ≤ 31 ∧
      (c.d.val ≤ 28 → r.d = c.d) := by
  generalize he : daysinmonth y m = result at h
  cases result with
  | error e => change Except.error e = Except.ok r at h; contradiction
  | ok ld =>
    have hb := monthLengths_proven y m ld he
    change Except.ok (⟨y,m,if c.d ≤ ld then c.d else ld⟩ : Civil) = Except.ok r at h
    by_cases hc : c.d ≤ ld
    · simp only [hc,ite_true,Except.ok.injEq] at h
      subst r
      dsimp only
      change c.d.val ≤ ld.val at hc
      exact ⟨by omega,by omega,by omega,by intro _; rfl⟩
    · simp only [hc,ite_false,Except.ok.injEq] at h
      subst r
      dsimp only
      change ¬ c.d.val ≤ ld.val at hc
      exact ⟨by omega,by omega,by omega,by intro hsmall; omega⟩

theorem calendarClamp_proven : CalendarClamp := by
  intro c n r hd h
  rcases h with hm | hy
  · exact clamp c (yearwrap c.y c.m n) (monthwrap c.m n) r hd hm
  · exact clamp c (c.y+n) c.m r hd hy

theorem fixedPeriodCancellation_proven : FixedPeriodCancellation := by
  intro d n
  have hd := d.property
  have hn := n.property
  constructor <;> apply Subtype.ext
  all_goals
    change wrapInt .i64 (wrapInt .i64 (d.val+n.val) + wrapInt .i64 (-n.val)) = d.val
    simp [wrapInt,IntTy.signed,IntTy.bits,IntTy.min,IntTy.max] at hd hn ⊢
    omega

theorem roundTiesUp_proven : RoundTiesUp := by
  intro d p f c r hf hc hr
  unfold ceilDay at hc
  unfold roundDay at hr
  simp only [hf] at hc hr
  change Except.ok (if d = f then f else f+p) = Except.ok c at hc
  change Except.ok (if d-f < (if d = f then f else f+p)-d then f else
    (if d = f then f else f+p)) = Except.ok r at hr
  have hc' : (if d = f then f else f+p) = c := Except.ok.inj hc
  rw [hc'] at hr
  have hr' : (if d-f < c-d then f else c) = r := Except.ok.inj hr
  by_cases h : d-f < c-d
  · simp only [h,ite_true] at hr'
    exact ⟨Or.inl hr'.symm,by intro he; change (d-f).val < (c-d).val at h; omega⟩
  · simp only [h,ite_false] at hr'
    exact ⟨Or.inr hr'.symm,by intro _; exact hr'.symm⟩

theorem firstMonday_proven : FirstMonday := by
  intro d hd
  have hw := weekdayAgreement_proven d
  have hb := d.property
  have hf : (firstdayofweek d).val = d.val - (dayofweek d).val + 1 := by
    unfold firstdayofweek
    change wrapInt .i64 (wrapInt .i64 (d.val - (dayofweek d).val) + (i 1).val) = _
    have hinner : wrapInt .i64 (d.val-(dayofweek d).val) = d.val-(dayofweek d).val := by
      apply wrapInt_of_inRange
      simp [IntTy.min,IntTy.max,IntTy.signed,IntTy.bits] at hb ⊢
      omega
    rw [hinner]
    change wrapInt .i64 (d.val - (dayofweek d).val + 1) = _
    apply wrapInt_of_inRange
    simp [IntTy.min,IntTy.max,IntTy.signed,IntTy.bits] at hb ⊢
    omega
  have hfw := weekdayAgreement_proven (firstdayofweek d)
  dsimp only
  constructor
  · rw [hf] at hfw
    rcases hw with ⟨hw,_,_⟩
    by_cases hz : d.val % 7 = 0
    · simp only [hz,ite_true] at hw
      rw [hw] at hfw
      omega
    · simp only [hz,ite_false] at hw
      rw [hw] at hfw
      omega
  · change (firstdayofweek d).val ≤ d.val ∧ d.val-(firstdayofweek d).val ≤ 6
    rw [hf]
    omega

private theorem adjust_spec (f : I → Bool) (step : I) (limit : Nat) :
    ∀ d r : I, adjust f step limit d = .ok r → ∃ k < limit,
      stepIter step k d = r ∧ f r = true ∧ ∀ j < k, f (stepIter step j d) = false := by
  induction limit with
  | zero => intro d r h; simp [adjust] at h
  | succ n ih =>
    intro d r h
    unfold adjust at h
    by_cases hfd : f d = true
    · simp only [hfd,ite_true,Except.ok.injEq] at h
      subst r
      exact ⟨0,by omega,rfl,hfd,by intro j hj; omega⟩
    · have hfalse : f d = false := by cases h : f d <;> simp_all
      simp only [hfalse,Bool.false_eq_true,ite_false] at h
      obtain ⟨k,hk,he,hr,hprev⟩ := ih (d+step) r h
      refine ⟨k+1,by omega,he,hr,?_⟩
      intro j hj
      cases j with
      | zero => exact hfalse
      | succ j => exact hprev j (by omega)

theorem adjustFirstMatch_proven : AdjustFirstMatch := adjust_spec

private theorem rem_zero (a : Int) (k : Int) (hk : k = 4 ∨ k = 100 ∨ k = 400) :
    a.tmod k = 0 ↔ a % k = 0 := by
  rcases hk with rfl | rfl | rfl <;>
    rw [Int.tmod_eq_emod] <;>
    split <;> simp_all [Int.dvd_iff_emod_eq_zero] <;> omega

theorem leapCycle_proven : LeapCycle := by
  intro y z h
  have h4y := Int.emod_emod_of_dvd y.val (show (4 : Int) ∣ 400 by decide)
  have h4z := Int.emod_emod_of_dvd z.val (show (4 : Int) ∣ 400 by decide)
  have h100y := Int.emod_emod_of_dvd y.val (show (100 : Int) ∣ 400 by decide)
  have h100z := Int.emod_emod_of_dvd z.val (show (100 : Int) ∣ 400 by decide)
  have h4 : y.val % 4 = z.val % 4 := by omega
  have h100 : y.val % 100 = z.val % 100 := by omega
  have eqzero : ∀ k : Int, k = 4 ∨ k = 100 ∨ k = 400 →
      (y.val.tmod k = 0 ↔ z.val.tmod k = 0) := by
    intro k hk
    rw [rem_zero y.val k hk,rem_zero z.val k hk]
    rcases hk with rfl | rfl | rfl <;> simp_all
  apply Bool.eq_iff_iff.mpr
  simp only [isleapyear,bne_iff_ne,beq_iff_eq,Bool.and_eq_true,Bool.or_eq_true]
  exact and_congr (eqzero 4 (Or.inl rfl))
    (or_congr (not_congr (eqzero 100 (Or.inr (Or.inl rfl))))
      (eqzero 400 (Or.inr (Or.inr rfl))))

theorem dayOfYearBounds_proven : DayOfYearBounds := by
  intro c n hv hdoy
  have hm : 0 < c.m.val ∧ c.m.val < 13 := by
    unfold validDate at hv
    split at hv
    · contradiction
    · omega
  have hdim : ∃ ld : I, daysinmonth c.y c.m = .ok ld ∧
      0 < c.d.val ∧ c.d.val ≤ ld.val := by
    unfold validDate at hv
    simp only [hm] at hv
    generalize he : daysinmonth c.y c.m = result at hv
    cases result with
    | error e => change Except.error e = Except.ok () at hv; contradiction
    | ok ld =>
      change (if ¬ (0 < c.d.val ∧ c.d.val < (ld+i 1).val) then
        Except.error (JlError.argumentError "day") else Except.ok ()) = Except.ok () at hv
      have hb := monthLengths_proven c.y c.m ld he
      have hsum : (ld+i 1).val = ld.val+1 := by
        change wrapInt .i64 (ld.val+1) = _
        apply wrapInt_of_inRange
        simp [IntTy.min,IntTy.max,IntTy.signed,IntTy.bits]
        omega
      split at hv
      · contradiction
      · rename_i hg
        rw [hsum] at hg
        exact ⟨ld,rfl,by omega,by omega⟩
  obtain ⟨ld,hld,hd,hdd⟩ := hdim
  have hc : c.m.val = 1 ∨ c.m.val = 2 ∨ c.m.val = 3 ∨ c.m.val = 4 ∨
      c.m.val = 5 ∨ c.m.val = 6 ∨ c.m.val = 7 ∨ c.m.val = 8 ∨ c.m.val = 9 ∨
      c.m.val = 10 ∨ c.m.val = 11 ∨ c.m.val = 12 := by omega
  unfold dayofyear at hdoy
  simp only [show ¬ (c.m.val < 1 ∨ c.m.val > 12) by omega,ite_false] at hdoy
  rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    cases hl : isleapyear c.y <;>
    simp [daysinmonth,hc,hl,i,JInt.lit,JInt.wrap,wrapInt,IntTy.signed,IntTy.bits] at hld hdoy ⊢ <;>
    cases hld <;> cases hdoy <;>
    simp [add_val,wrapInt,IntTy.signed,IntTy.bits] at hdd ⊢ <;> omega

private theorem tail_length (r : DateRange) (n : Nat) : ∀ index xs,
    collectTail r n index = .ok xs → xs.length = n := by
  induction n with
  | zero => intro index xs h; change Except.ok [] = Except.ok xs at h; cases h; rfl
  | succ n ih =>
    intro index xs h
    unfold collectTail at h
    cases he : rangeElement r (i index) with
    | error e => rw [he] at h; change Except.error e = Except.ok xs at h; contradiction
    | ok v =>
      rw [he] at h
      cases ht : collectTail r n (index+1) with
      | error e =>
        rw [ht] at h
        change Except.error e = Except.ok xs at h
        contradiction
      | ok vs =>
        rw [ht] at h
        change Except.ok (v::vs) = Except.ok xs at h
        cases h
        simpa only [List.length_cons] using congrArg (·+1) (ih (index+1) vs ht)

theorem rangeIterationCount_proven : RangeIterationCount := by
  intro r fuel length xs hn _ h
  unfold collectRange at h
  by_cases hz : length.val ≤ 0
  · simp only [hz,ite_true,Except.ok.injEq] at h
    subst xs
    simp only [List.length_nil]
    omega
  · simp only [hz,ite_false] at h
    cases ht : collectTail r (length.val.toNat-1) 1 with
    | error e =>
      rw [ht] at h
      change Except.error e = Except.ok xs at h
      contradiction
    | ok vs =>
      rw [ht] at h
      change Except.ok (r.start::vs) = Except.ok xs at h
      cases h
      have hlen := tail_length r (length.val.toNat-1) 1 vs ht
      simp only [List.length_cons]
      omega

/-- The manual's January 31 -> February 28 -> January 28 example. This is a
consequence of clamping, not a claim that Month addition is invertible. -/
theorem documentedMonthNoninverse :
    (addMonth (i 735264) (i 1) >>= fun d => subMonth d (i 1)) = .ok (i 735261) := by
  decide +kernel

end JuliaLean.Dates
