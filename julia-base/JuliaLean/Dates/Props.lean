import JuliaLean.Dates.Format
import JuliaLean.Dates.Ranges
import JuliaLean.Dates.Periods

namespace JuliaLean.Dates
open JuliaLean

/-- Every stored Date, including values reachable by the public parts constructor,
reconstructs from its calendar fields and from its ordinary printed form. -/
def DayNumberRoundtrip : Prop := ∀ d : I,
  date (yearmonthday d) = .ok d ∧
  (stringDate d >>= fun s => parseDate s minimumFormat) = .ok d

def WeekdayAgreement : Prop := ∀ d : I,
  (dayofweek d).val = (if d.val % 7 = 0 then 7 else d.val % 7) ∧
  1 ≤ (dayofweek d).val ∧ (dayofweek d).val ≤ 7

/-- Thursday determines the ISO week-year, including in year zero and BCE years. -/
def WeekISO : Prop := ∀ (d n : I), week d = .ok n → isoWeek d = .ok n.val

def MonthLengths : Prop := ∀ (y m ld : I), daysinmonth y m = .ok ld →
  28 ≤ ld.val ∧ ld.val ≤ 31

/-- A leap year repeats every 400 Gregorian years, including negative years. -/
def LeapCycle : Prop := ∀ y z : I, y.val % 400 = z.val % 400 →
  isleapyear y = isleapyear z

/-- Valid calendar dates have a day-of-year in the documented year length. -/
def DayOfYearBounds : Prop := ∀ (c : Civil) (n : I),
  validDate c = .ok () → dayofyear c = .ok n →
  1 ≤ n.val ∧ n.val ≤ (if isleapyear c.y then 366 else 365)

/-- Parts constructors must preserve the supplied date, or reject it. The
24:00 normalization is excluded here because it intentionally changes the date. -/
def DateTimeParts : Prop := ∀ (c : Civil) (t : Clock) (dt : I),
  validDateTime c t = .ok () → t.h.val < 24 → datetime c t = .ok dt →
  yearmonthday (qfld dt 86400000) = c

/-- Successful Month/Year field transformations preserve the day when the target
month can hold it, otherwise choose the last day. The result is a valid day. -/
def CalendarClamp : Prop := ∀ (c : Civil) (n : I) (r : Civil), 0 < c.d.val →
  (monthParts c n = .ok r ∨ yearParts c n = .ok r) →
  r.d.val ≤ c.d.val ∧ 1 ≤ r.d.val ∧ r.d.val ≤ 31 ∧
  (c.d.val ≤ 28 → r.d = c.d)

/-- Day and Millisecond addition/subtraction keep the documented fixed-width
wrapping algebra even when the exact intermediate sum does not fit. -/
def FixedPeriodCancellation : Prop := ∀ d n : I,
  addDay (addDay d n) (-n) = d ∧ addMillisecond (addMillisecond d n) (-n) = d

/-- A positive calendar range must not emit a value beyond its requested stop;
its stored last value must agree with the final iterated element. -/
def MonthRangeBound : Prop := ∀ (a b step : I) (fuel : Nat) (r : DateRange) (length : I),
  0 < step.val → a ≤ b → calendarRange a step b false fuel = some (.ok r) →
  rangeLength r fuel = some (.ok length) →
  r.stop ≤ b ∧ rangeElement r (length-i 1) = .ok r.stop

/-- Successful complete iteration yields the cached nonnegative length.
Iteration uses start+step*i, rather than repeatedly clamping a prior element. -/
def RangeIterationCount : Prop := ∀ (r : DateRange) (fuel : Nat) (length : I) (xs : List I),
  0 ≤ length.val → rangeLength r fuel = some (.ok length) →
  collectRange r length = .ok xs → xs.length = length.val.toNat

/-- The last stored endpoint of a nonempty calendar range is also the value
at its final cached iteration index. This is independent of requested-stop bounds. -/
def RangeLastIteration : Prop := ∀ (a b step : I) (fuel : Nat) (r : DateRange) (length : I),
  calendarRange a step b false fuel = some (.ok r) →
  rangeLength r fuel = some (.ok length) → 0 < length.val →
  rangeElement r (length-i 1) = .ok r.stop

/-- Time arithmetic is addition on the 24-hour clock. -/
def TimeAdditionClock : Prop := ∀ t n : I, 0 ≤ t.val → t.val < 86400000000000 →
  (addNanosecond t n).val = (t.val+n.val) % 86400000000000

/-- canonicalize changes the representation of a duration, not its value. -/
def CanonicalizeMonths : Prop := ∀ p : CalendarPeriod,
  calendarMonths (canonicalCalendar p) = calendarMonths p

/-- The documented floor/ceil inequalities and alignment to 0000-01-01. -/
def RoundingBrackets : Prop := ∀ d p f c : I, 0 < p.val →
  floorDay d p = .ok f → ceilDay d p = .ok c →
  f ≤ d ∧ d ≤ c ∧ (f.val-dateEpoch.val) % p.val = 0

/-- Round chooses one of floor and ceil and breaks equal-distance ties upward. -/
def RoundTiesUp : Prop := ∀ d p f c r : I,
  floorDay d p = .ok f → ceilDay d p = .ok c → roundDay d p = .ok r →
  (r = f ∨ r = c) ∧ ((d-f).val = (c-d).val → r = c)

/-- A representable Monday needs up to six days of headroom before its input. -/
def FirstMonday : Prop := ∀ d : I, -9223372036854775802 ≤ d.val →
  let f := firstdayofweek d
  (dayofweek f).val = 1 ∧ f ≤ d ∧ d.val-f.val ≤ 6

/-- The source loop's candidate sequence, including the initial candidate. -/
def stepIter (step : I) : Nat → I → I
  | 0, d => d
  | n+1, d => stepIter step n (d+step)

def AdjustFirstMatch : Prop := ∀ (f : I → Bool) (step : I) (limit : Nat) (d r : I),
  adjust f step limit d = .ok r → ∃ k < limit,
    stepIter step k d = r ∧ f r = true ∧ ∀ j < k, f (stepIter step j d) = false

/-- The inner Time constructor always produces a valid point within its day. -/
def TimeNormalized : Prop := ∀ n : I,
  0 ≤ (timeOfNs n).val ∧ (timeOfNs n).val < 86400000000000

def containsFields (tokens : List Token) : Bool :=
  tokens.any (fun t => match t with | .year .. => true | _ => false) &&
  tokens.any (fun t => match t with | .month .. | .monthName .. => true | _ => false) &&
  tokens.any (fun t => match t with | .day .. => true | _ => false)

/-- Merely containing year/month/day does not guarantee lossless formatting. -/
def FormatRoundtrip : Prop := ∀ (d : I) (tokens : List Token) (text : Bytes),
  containsFields tokens = true → formatDate d tokens = .ok text →
  parseDate text tokens = .ok d

end JuliaLean.Dates
