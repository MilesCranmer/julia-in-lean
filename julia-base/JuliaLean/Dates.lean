import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Dates.Model
import JuliaLean.Dates.Format
import JuliaLean.Dates.Ranges
import JuliaLean.Dates.Periods
import JuliaLean.Dates.Props
import JuliaLean.Dates.Refutations
import JuliaLean.Dates.Proofs
import JuliaLean.Dates.Validation

namespace JuliaLean.Dates
open JuliaLean.Registry

/-- Proleptic Gregorian dates, constructors, calendar arithmetic, ranges,
rounding, adjusters and date-format round-trips at master bbfa0ce4150. -/
def entries : List Entry := [
  { id := "dates-daynumber-roundtrip", juliaFile := "stdlib/Dates/src/accessors.jl"
    juliaFns := ["yearmonthday", "totaldays", "Date", "print(::IO, ::Date)"]
    statement := "Every stored Date reconstructs from yearmonthday and from its ordinary printed form."
    source := "accessors.jl:234-245 (calendar parts); io.jl:846-850 (parsable output)"
    status := .refuted, prop := ``DayNumberRoundtrip, thm := some ``dayNumberRoundtrip_refuted
    issue := "duplicate PR #63714 (open); related #50981"
    notes := "Date(252527349277666,1,1) stores 92233720368547560 days; its fields rebuild 92229932536088893. Outside the advertised typemax(Date), but publicly constructible without error. Both Julia versions agree." },
  { id := "dates-dayofweek-mod7", juliaFile := "stdlib/Dates/src/query.jl"
    juliaFns := ["dayofweek", "mod1"]
    statement := "dayofweek is the nonzero residue of the Rata Die day modulo 7, always in 1 through 7, including negative days."
    source := "query.jl:85-86, 109-121; base/operators.jl:914"
    status := .proven, prop := ``WeekdayAgreement, thm := some ``weekdayAgreement_proven },
  { id := "dates-week-negative", juliaFile := "stdlib/Dates/src/accessors.jl"
    juliaFns := ["week(::Date)", "week(days)"]
    statement := "week agrees with the ISO rule that the Thursday in a date's week determines its week-year."
    source := "accessors.jl:182-189 (ISO week definition)"
    status := .refuted, prop := ``WeekISO, thm := some ``weekISO_refuted
    issue := "duplicate PR #62425 (open); queries: Dates week negative year; week negative; week in:title,body"
    notes := "0000-12-31 is a Sunday in ISO week 52, but week returns 1. abs(days-1) reflects all nonpositive days." },
  { id := "dates-month-lengths", juliaFile := "stdlib/Dates/src/types.jl"
    juliaFns := ["daysinmonth"]
    statement := "Every successful daysinmonth call returns a count between 28 and 31."
    source := "types.jl:339-341; Gregorian month lengths"
    status := .proven, prop := ``MonthLengths, thm := some ``monthLengths_proven },
  { id := "dates-leap-cycle", juliaFile := "stdlib/Dates/src/types.jl"
    juliaFns := ["isleapyear"]
    statement := "Years with the same residue modulo 400 have the same leap-year status, including BCE years and year zero."
    source := "types.jl:336-337 (Gregorian leap-year rule)"
    status := .proven, prop := ``LeapCycle, thm := some ``leapCycle_proven },
  { id := "dates-dayofyear-bounds", juliaFile := "stdlib/Dates/src/query.jl"
    juliaFns := ["dayofyear", "validargs(::Type{Date})"]
    statement := "A valid date has dayofyear between 1 and the length of its leap or common year."
    source := "query.jl:103-107; types.jl:412-415"
    status := .proven, prop := ``DayOfYearBounds, thm := some ``dayOfYearBounds_proven },
  { id := "dates-constructor-overflow", juliaFile := "stdlib/Dates/src/types.jl"
    juliaFns := ["DateTime", "validargs(::Type{DateTime})"]
    statement := "A successful DateTime parts constructor retains the supplied calendar date, apart from 24:00 normalization."
    source := "types.jl:369-380 (construct by parts)"
    status := .refuted, prop := ``DateTimeParts, thm := some ``dateTimeParts_refuted
    issue := "duplicate #50981 (open); related #50930 and PR #63714"
    notes := "DateTime(300000000,1,1) passes validargs and returns -284554050-09-30T09:34:08.384. DateTime's type docstring warns about fixed-point overflow." },
  { id := "dates-calendar-clamp", juliaFile := "stdlib/Dates/src/arithmetic.jl"
    juliaFns := ["+(::Date,::Month)", "+(::Date,::Year)", "-(::Date,::Month)"]
    statement := "Month and Year field arithmetic clamps a positive day to the target month end; days 1 through 28 remain unchanged."
    source := "Dates/docs/src/index.md:408-436 (slot-based arithmetic); arithmetic.jl:25-74"
    status := .proven, prop := ``CalendarClamp, thm := some ``calendarClamp_proven
    notes := "This is the field-transform invariant; complete Date reconstruction also needs the calendar accessors to remain valid. The separately checked documentedMonthNoninverse theorem gives Jan 31 + Month(1) - Month(1) = Jan 28 in 2014." },
  { id := "dates-fixed-period-cancellation", juliaFile := "stdlib/Dates/src/arithmetic.jl"
    juliaFns := ["+(::Date,::Day)", "-(::Date,::Day)", "+(::DateTime,::Millisecond)", "-(::DateTime,::Millisecond)"]
    statement := "Adding and subtracting the same Day or Millisecond restores the stored count, even across Int64 overflow."
    source := "arithmetic.jl:81-84; types.jl:788 (ArithmeticWraps)"
    status := .proven, prop := ``FixedPeriodCancellation, thm := some ``fixedPeriodCancellation_proven },
  { id := "dates-range-month-stop", juliaFile := "stdlib/Dates/src/ranges.jl"
    juliaFns := ["len", "Base.steprange_last", "length", "iterate", "in"]
    statement := "A positive Month range ends no later than its requested stop and its stored last equals the final indexed element."
    source := "range endpoint invariant; ranges.jl:19-31, 40-72"
    status := .refuted, prop := ``MonthRangeBound, thm := some ``monthRangeBound_refuted
    issue := "none found for exact case (queries: Dates range Month last; StepRange Month; Month range); related PR #63714"
    notes := "Jan 31:Month(1):Mar 29 in 2019 has length 3 and last Mar 31. The correction loop repeatedly clamps; iteration indexes from the original start. Membership includes the overshooting date." },
  { id := "dates-range-last-iteration", juliaFile := "stdlib/Dates/src/ranges.jl"
    juliaFns := ["Base.steprange_last", "length", "iterate", "getindex", "in"]
    statement := "A nonempty Month range's stored last equals its final indexed and iterated element."
    source := "range invariant last(r)==r[end]; ranges.jl:66-72"
    status := .refuted, prop := ``RangeLastIteration, thm := some ``rangeLastIteration_refuted
    issue := "related PR #63714 and #50981; exact case not found (queries: Dates last length; Month range); final additional PR search rate-limited"
    notes := "A one-day range from raw day -92233720368548560 reports length 124448796357. Stored last is -92229932536089924, indexed last is -92226144703631306, and last(r) is not in r. Outside advertised typemin(Date), but constructible through public Day arithmetic." },
  { id := "dates-range-iteration-count", juliaFile := "stdlib/Dates/src/ranges.jl"
    juliaFns := ["length(::StepRange{<:TimeType})", "iterate"]
    statement := "A successful complete Date-range traversal yields exactly its cached nonnegative length."
    source := "ranges.jl:71-72 (cached-length iterator)"
    status := .proven, prop := ``RangeIterationCount, thm := some ``rangeIterationCount_proven
    notes := "This remains true for the month-end overshoot: iteration itself uses length to decide when to stop. It does not establish that all yielded dates respect the requested bound." },
  { id := "dates-time-add-overflow", juliaFile := "stdlib/Dates/src/arithmetic.jl"
    juliaFns := ["+(::Time,::Nanosecond)", "Time(::Nanosecond)"]
    statement := "Time addition equals the exact nanosecond sum modulo one 24-hour day."
    source := "types.jl:184-191 (24-hour clock and day modulus); clock arithmetic invariant"
    status := .refuted, prop := ``TimeAdditionClock, thm := some ``timeAdditionClock_refuted
    issue := "none found (queries: Time typemax; Time overflow nanosecond); related #50930"
    notes := "Time(1)+Nanosecond(typemax(Int64)) gives 4363145224191 ns; exact modulo-day addition gives 2836854775807 ns." },
  { id := "dates-canonicalize-overflow", juliaFile := "stdlib/Dates/src/periods.jl"
    juliaFns := ["canonicalize(::CompoundPeriod)"]
    statement := "Canonicalizing Year/Month CompoundPeriods preserves their exact number of calendar months."
    source := "periods.jl:208-215 (representation reduction into coarser periods)"
    status := .refuted, prop := ``CanonicalizeMonths, thm := some ``canonicalizeMonths_refuted
    issue := "none found (issue and PR queries: canonicalize overflow)"
    notes := "Year(typemax(Int64))+Month(12) canonicalizes to Year(typemin(Int64)); the coarser carry wraps." },
  { id := "dates-rounding-overflow", juliaFile := "stdlib/Dates/src/rounding.jl"
    juliaFns := ["floor(::Date,::Day)", "ceil", "epochdays2date"]
    statement := "For positive Day precision, floor and ceil bracket the input and floor is aligned to the 0000-01-01 epoch."
    source := "rounding.jl:3-5, 187-193, 216-221"
    status := .refuted, prop := ``RoundingBrackets, thm := some ``roundingBrackets_refuted
    issue := "none found (queries: Dates rounding overflow; rounding); related #50930"
    notes := "floor(Date(-1),Day(typemax(Int64))) has a huge positive day count, after the input. Its exact lower bound is outside Int64." },
  { id := "dates-round-ties-up", juliaFile := "stdlib/Dates/src/rounding.jl"
    juliaFns := ["round(::Date,::Day)", "ceil", "floorceil"]
    statement := "round chooses its computed floor or ceil and sends equal stored-distance ties to ceil."
    source := "rounding.jl:289-315 (RoundNearestTiesUp)"
    status := .proven, prop := ``RoundTiesUp, thm := some ``roundTiesUp_proven
    notes := "Distances are wrapping Day values, matching the source. Bracketing and mathematically nearest bounds are a separate refuted property." },
  { id := "dates-firstdayofweek", juliaFile := "stdlib/Dates/src/adjusters.jl"
    juliaFns := ["firstdayofweek"]
    statement := "With six days of lower-bound headroom, firstdayofweek is Monday, no later than its input and at most six days earlier."
    source := "adjusters.jl:40-55 (Monday of the week)"
    status := .proven, prop := ``FirstMonday, thm := some ``firstMonday_proven },
  { id := "dates-adjuster-first-match", juliaFile := "stdlib/Dates/src/adjusters.jl"
    juliaFns := ["adjust", "tonext(::Function,...)", "toprev(::Function,...)"]
    statement := "A successful pure-predicate, Day-stepped Date adjuster returns the first matching candidate among its limit tested candidates."
    source := "adjusters.jl:201-207, 435-457 (search, same and step)"
    status := .proven, prop := ``AdjustFirstMatch, thm := some ``adjustFirstMatch_proven
    notes := "tonext/toprev select the initial candidate according to same, then call this loop. DateFunction's discarded type-check call is harmless for pure predicates; effectful predicates are outside the property." },
  { id := "dates-time-normalized", juliaFile := "stdlib/Dates/src/types.jl"
    juliaFns := ["Time(::Nanosecond)", "Time", "validargs(::Type{Time})"]
    statement := "The Time inner constructor returns a nanosecond count in the half-open interval from midnight to one day."
    source := "types.jl:184-191 (24-hour Time), 430-451 (validated parts)"
    status := .proven, prop := ``TimeNormalized, thm := some ``timeNormalized_proven
    notes := "The model also mirrors master's expanded ns field and combined subsecond validation. Release 1.13.2 instead requires ns<1000; both branches were differentially checked." },
  { id := "dates-format-year-loss", juliaFile := "stdlib/Dates/src/io.jl"
    juliaFns := ["format", "parse(Date,...)", "ISODateFormat"]
    statement := "Every date format containing year, month and day can format and parse a Date without loss."
    source := "io.jl:551-562 (ISODateFormat), 782-807 (fixed-width y versus minimum-width Y)"
    status := .refuted, prop := ``FormatRoundtrip, thm := some ``formatRoundtrip_refuted
    issue := "none found for sign loss (queries: Dates format negative year; format BCE); related #42790 and PR #54535"
    notes := "P3 documentation concern: yyyy-mm-dd drops the sign of year -1. Fixed-width y truncation is explicitly documented, so merely including all fields is insufficient; YYYY preserves the year. Numeric adjacent fields, two-digit years and English month names are modelled." }
]

end JuliaLean.Dates
