import JuliaLean.Dates.Format
import JuliaLean.Dates.Ranges
import JuliaLean.Dates.Periods

namespace JuliaLean.Dates.Validation
open JuliaLean

private def showI (x : I) : String := toString x.val
private def showCivil (c : Civil) : String := s!"{c.y.val},{c.m.val},{c.d.val}"
private def showBytes (s : Bytes) : String := String.ofList (s.map Char.ofNat)
private def showJl {α : Type} (f : α → String) : Jl α → String
  | .ok a => f a
  | .error (.argumentError _) => "argument"
  | .error (.inexactError _) => "inexact"
  | .error .boundsError => "bounds"
  | .error (.overflowError _) => "overflow"
  | .error (.domainError _) => "domain"
  | .error e => s!"unexpected:{repr e}"
private def showOpt {α : Type} (f : α → String) : Option (Jl α) → String
  | none => "unfinished"
  | some x => showJl f x

def years : List Int := [-400,-100,-4,-1,0,1,4,100,400,1900,2000,2019,2020,
  9999,10000,300000000,252522163911149,252527349277666,1000000000000000,
  -9223372036854775808,9223372036854775807]
def rawDays : List Int := [0,1,-1,-365,-730,737090,737148,737152,
  -92231826452318568,92231826452317838,92233720368547560,
  -9223372036854775808,9223372036854775807]
def shifts : List Int := [-13,-1,0,1,2,13,9223372036854775807,-9223372036854775808]
def periodInputs : List Int := [-9223372036854775808,-9223372036854775807,-25,-12,-1,0,1,12,25,9223372036854775807]

/-- Deterministic differential inputs.
Rows exercise real source operations, including invalid fields and wrapped counts. -/
def differential (release : Bool := false) : IO Unit := do
  for y in years do
    for m in [1,2,12] do
      let c : Civil := ⟨i y,i m,i 1⟩
      IO.println s!"date {y} {m} {showJl showI (date c)}"
      IO.println s!"dim {y} {m} {showJl showI (daysinmonth c.y c.m)}"
      IO.println s!"doy {y} {m} {showJl showI (dayofyear c)}"
      IO.println s!"dt {y} {m} {showJl showI (datetime c ⟨i 0,i 0,i 0,i 0,i 0,i 0,.twentyfour⟩)}"
  for n in rawDays do
    let d := i n
    IO.println s!"ymd {n} {showCivil (yearmonthday d)}"
    IO.println s!"dow {n} {showI (dayofweek d)}"
    IO.println s!"week {n} {showJl showI (week d)}"
    IO.println s!"first {n} {showI (firstdayofweek d)}"
    IO.println s!"rebuild {n} {showJl showI (date (yearmonthday d))}"
    for p in [1,7,31,9223372036854775807] do
      IO.println s!"floor {n} {p} {showJl showI (floorDay d (i p))}"
      IO.println s!"ceil {n} {p} {showJl showI (ceilDay d (i p))}"
      IO.println s!"round {n} {p} {showJl showI (roundDay d (i p))}"
    if n.natAbs < 1000000 then
      for shift in shifts do
        IO.println s!"month {n} {shift} {showJl showI (addMonth d (i shift))}"
        IO.println s!"year {n} {shift} {showJl showI (addYear d (i shift))}"
  for y in [-1,0,1,2020,9999,10000,12345,252527349277666] do
    let d := (date ⟨i y,i 1,i 1⟩).toOption.getD (i 0)
    for (label,df) in [("iso",isoFormat),("minimum",minimumFormat),("fixed",fixedFormat),("named",namedFormat)] do
      let s := formatDate d df
      IO.println s!"fmt {y} {label} {showJl showBytes s}"
      IO.println s!"parse {y} {label} {showJl showI (s >>= fun s => parseDate s df)}"
    IO.println s!"string {y} {showJl showBytes (stringDate d)}"
  for h in [-1,0,12,23,24] do
    for ns in [0,999,1000,999999999,1000000000] do
      let t : Clock := ⟨i h,i 0,i 0,i 0,i 0,i ns,.twentyfour⟩
      IO.println s!"time {h} {ns} {showJl showI (time t release)}"
  for y in periodInputs do
    for m in periodInputs do
      let p := canonicalCalendar ⟨i y,i m⟩
      IO.println s!"canonical {y} {m} {p.years.val},{p.months.val}"
  for ns in [0,1,3600000000000,86399999999999] do
    for shift in shifts do
      IO.println s!"timeadd {ns} {shift} {showI (addNanosecond (i ns) (i shift))}"
  for (a,b,step,yrs) in [(737090,737147,1,false),(737149,737089,-1,false),
      (737484,738944,1,true),(0,700,1,false),(1,3650,2,false)] do
    let r := calendarRange (i a) (i step) (i b) yrs 100
    IO.println s!"range {a} {b} {step} {yrs} {showOpt (fun r => showI r.stop) r}"
    match r with
    | some (.ok r) =>
      IO.println s!"len {a} {b} {step} {yrs} {showOpt showI (rangeLength r 100)}"
    | _ => pure ()
  for d in [-730,0,737090] do
    for p in [0,1,2,13] do
      IO.println s!"floormonth {d} {p} {showJl showI (floorMonth (i d) (i p))}"
      IO.println s!"flooryear {d} {p} {showJl showI (floorYear (i d) (i p))}"
  for limit in [0,1,2,7] do
    for same in [false,true] do
      IO.println s!"next {limit} {same} {showJl showI (tonext (fun d => dayofweek d == i 7) (i 1) (i 1) limit same)}"
      IO.println s!"prev {limit} {same} {showJl showI (toprev (fun d => dayofweek d == i 7) (i 1) (i (-1)) limit same)}"

/-- Additional validation branches and complete range traversals. -/
def supplemental (release : Bool := false) : IO Unit := do
  for y in [-400,0,1900,2000] do
    for m in [0,1,2,3,12,13] do
      for d in [0,1,28,29,31,32] do
        let c : Civil := ⟨i y,i m,i d⟩
        IO.println s!"valid {y} {m} {d} {showJl (fun _ => "ok") (validDate c)} {showJl showI (date c)} {showJl showI (dayofyear c)}"
  for (label,ampm) in [("am",AMPM.am),("pm",AMPM.pm),("24",AMPM.twentyfour)] do
    for h in [0,1,12,13,23,24] do
      for mi in [-1,0,59,60] do
        for ms in [0,1,999,1000] do
          let t : Clock := ⟨i h,i mi,i 0,i ms,i 0,i 0,ampm⟩
          let c : Civil := ⟨i 2000,i 2,i 29⟩
          IO.println s!"clock {label} {h} {mi} {ms} {showJl (fun _ => "ok") (validDateTime c t)} {showJl showI (datetime c t)} {showJl showI (time t release)}"
  for (a,b,step,yrs) in [(737090,737147,1,false),(737149,737089,-1,false),
      (737484,738944,1,true),(0,700,1,false),(1,3650,2,false),
      (737149,737090,1,false),(737090,737149,-1,false),(737090,737149,0,false)] do
    match calendarRange (i a) (i step) (i b) yrs 100 with
    | some (.ok r) =>
      match rangeLength r 100 with
      | some (.ok n) =>
        IO.println s!"collect {a} {b} {step} {yrs} {showJl (fun xs => "[" ++ String.intercalate "," (xs.map showI) ++ "]") (collectRange r n)}"
        for x in [a,b,r.stop.val] do
          IO.println s!"in {a} {b} {step} {yrs} {x} {showOpt toString (rangeContains r (i x) 100)}"
      | result => IO.println s!"collect {a} {b} {step} {yrs} {showOpt showI result}"
    | result => IO.println s!"collect {a} {b} {step} {yrs} {showOpt (fun r => showI r.stop) result}"
  for y in [-1,0,20,2020] do
    let df := [.year 2 false false,.delim [45],.month 2 false,.delim [45],.day 2 false]
    let d := (date ⟨i y,i 1,i 1⟩).toOption.getD (i 0)
    let text := formatDate d df
    IO.println s!"twodigit {y} {showJl showBytes text} {showJl showI (text >>= fun s => parseDate s df)}"
  match calendarRange (i (-92233720368548560)) (i 1) (i (-92233720368548559)) false 20 with
  | some (.ok r) =>
    match rangeLength r 20 with
    | some (.ok n) =>
      IO.println s!"edge-range {r.stop.val} {n.val} {showJl showI (rangeElement r (n-i 1))} {showOpt toString (rangeContains r r.stop 20)}"
    | result => IO.println s!"edge-range {showOpt showI result}"
  | result => IO.println s!"edge-range {showOpt (fun r => showI r.stop) result}"

end JuliaLean.Dates.Validation
