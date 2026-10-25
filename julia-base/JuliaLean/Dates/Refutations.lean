import JuliaLean.Dates.Props

namespace JuliaLean.Dates
open JuliaLean
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

/-- Public Date(252527349277666,1,1), verified on both Julia versions. -/
def badCalendarDay : I := i 92233720368547560

theorem dayNumberRoundtrip_refuted : ¬ DayNumberRoundtrip := by
  intro h
  have bad := (h badCalendarDay).1
  have ne : date (yearmonthday badCalendarDay) ≠ .ok badCalendarDay := by decide +kernel
  exact ne bad

/-- The independent printed-form conjunct fails at the same Date. -/
theorem printedDateCounterexample :
    (stringDate badCalendarDay >>= fun s => parseDate s minimumFormat) ≠ .ok badCalendarDay := by
  decide +kernel

theorem weekISO_refuted : ¬ WeekISO := by
  intro h
  have bad := h (i 0) (i 1) (by decide +kernel)
  have ne : isoWeek (i 0) ≠ .ok (i 1).val := by decide +kernel
  exact ne bad

def midnight : Clock := ⟨i 0,i 0,i 0,i 0,i 0,i 0,.twentyfour⟩

theorem dateTimeParts_refuted : ¬ DateTimeParts := by
  intro h
  have bad := h ⟨i 300000000,i 1,i 1⟩ midnight (i (-8979658505245551616))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ne : yearmonthday (qfld (i (-8979658505245551616)) 86400000) ≠
      (⟨i 300000000,i 1,i 1⟩ : Civil) := by decide +kernel
  exact ne bad

def badRange : DateRange := ⟨i 737090,i 1,i 737149,false⟩

theorem monthRangeBound_refuted : ¬ MonthRangeBound := by
  intro h
  have bad := (h (i 737090) (i 737147) (i 1) 20 badRange (i 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  have ne : ¬ (badRange.stop ≤ i 737147) := by decide +kernel
  exact ne bad

theorem timeAdditionClock_refuted : ¬ TimeAdditionClock := by
  intro h
  have bad := h (i 3600000000000) (i 9223372036854775807)
    (by decide +kernel) (by decide +kernel)
  have ne : (addNanosecond (i 3600000000000) (i 9223372036854775807)).val ≠
      ((i 3600000000000).val+(i 9223372036854775807).val) % 86400000000000 := by decide +kernel
  exact ne bad

theorem canonicalizeMonths_refuted : ¬ CanonicalizeMonths := by
  intro h
  have bad := h ⟨i 9223372036854775807,i 12⟩
  have ne : calendarMonths (canonicalCalendar ⟨i 9223372036854775807,i 12⟩) ≠
      calendarMonths ⟨i 9223372036854775807,i 12⟩ := by decide +kernel
  exact ne bad

theorem roundingBrackets_refuted : ¬ RoundingBrackets := by
  intro h
  have bad := (h (i (-730)) (i 9223372036854775807)
    (i 9223372036854775444) (i (-365))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  have ne : ¬ (i 9223372036854775444 ≤ i (-730)) := by decide +kernel
  exact ne bad

theorem formatRoundtrip_refuted : ¬ FormatRoundtrip := by
  intro h
  have bad := h (i (-730)) isoFormat (bytes "0001-01-01")
    (by decide +kernel) (by decide +kernel)
  have ne : parseDate (bytes "0001-01-01") isoFormat ≠ .ok (i (-730)) := by decide +kernel
  exact ne bad

def inconsistentRange : DateRange := ⟨i (-92233720368548560),i 1,i (-92229932536089924),false⟩

theorem rangeLastIteration_refuted : ¬ RangeLastIteration := by
  intro h
  have bad := h (i (-92233720368548560)) (i (-92233720368548559)) (i 1)
    20 inconsistentRange (i 124448796357)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ne : rangeElement inconsistentRange (i 124448796357-i 1) ≠
      .ok inconsistentRange.stop := by decide +kernel
  exact ne bad

end JuliaLean.Dates
