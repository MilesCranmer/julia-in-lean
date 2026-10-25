import JuliaLean.Dates.Model

namespace JuliaLean.Dates
open JuliaLean JuliaLean.Float

/-- stdlib/Dates/src/periods.jl:474-475: Float64 average month/year lengths.
The decimal literals are rounded once, then multiplied in binary64. -/
def calendarDays (n : I) (years : Bool) : F64 :=
  F64.mul (if years then F64.roundRat 146097 400 false else F64.roundRat 48699 1600 false)
    (F64.ofInt n.val)

/-- stdlib/Dates/src/ranges.jl:17; mixed div converts the day difference to
Float64 before truncating division. The shared IEEE model preserves rounding. -/
def calendarGuess (a b step : I) (years : Bool) : Jl I :=
  F64.int .i64 (F64.divInteger (F64.ofInt (b-a).val) (calendarDays step years))

def calendarAdd (years : Bool) (d n : I) : Jl I :=
  if years then addYear d n else addMonth d n

/-- stdlib/Dates/src/ranges.jl:24-30. none means the execution budget was
insufficient to observe termination, not a Julia result or an exception.
Every some result follows exactly a finite execution of the source while loop. -/
def lenLoop (years : Bool) (hi step : I) : Nat → I → I → I → Option (Jl I)
  | 0, _, _, _ => none
  | fuel+1, v, prev, n =>
    if v ≤ hi ∧ prev ≤ v then
      match calendarAdd years v step with
      | .error e => some (.error e)
      | .ok next => lenLoop years hi step fuel next v (n+i 1)
    else some (.ok (n-i 1))

/-- stdlib/Dates/src/ranges.jl:19-30. The observation budget only limits how
many source steps can be inspected; unfinished runs are never reported as values. -/
def calendarLen (a b step : I) (years : Bool) (fuel : Nat) : Option (Jl I) :=
  let lo := if a ≤ b then a else b
  let hi := if a ≤ b then b else a
  let st := qabs step
  match calendarGuess a b step years with
  | .error e => some (.error e)
  | .ok n =>
    match calendarAdd years lo (st*n) with
    | .error e => some (.error e)
    | .ok v => lenLoop years hi st fuel v v n

structure DateRange where
  start : I
  step : I
  stop : I
  years : Bool
  deriving DecidableEq, Repr

/-- stdlib/Dates/src/ranges.jl:40-63; base/range.jl:401 retains the requested
stop for an empty non-integer range. Otherwise the endpoint is normalized. -/
def calendarRange (a step b : I) (years : Bool) (fuel : Nat) : Option (Jl DateRange) :=
  if step.val = 0 then some (.error (.argumentError "step"))
  else if a = b then some (.ok ⟨a,step,b,years⟩)
  else if (step.val > 0) ≠ (b > a) then some (.ok ⟨a,step,b,years⟩)
  else if ((b-a).val > 0) ≠ (b > a) then some (.error (.overflowError "difference"))
  else do
    match ← calendarLen a b step years fuel with
    | .error e => pure (.error e)
    | .ok n =>
      match calendarAdd years a (step*n) with
      | .error e => pure (.error e)
      | .ok endpoint => pure (.ok ⟨a,step,b-(b-endpoint),years⟩)

/-- stdlib/Dates/src/ranges.jl:31: empty ranges have zero length; nonempty
ranges recompute len against the stored normalized stop. -/
def rangeLength (r : DateRange) (fuel : Nat) : Option (Jl I) :=
  if (r.step.val > 0 ∧ r.stop < r.start) ∨ (r.step.val < 0 ∧ r.start < r.stop) then
    some (.ok (i 0))
  else do
    match ← calendarLen r.start r.stop r.step r.years fuel with
    | .ok n => pure (.ok (n+i 1))
    | .error e => pure (.error e)

/-- stdlib/Dates/src/ranges.jl:71-72: zero-based emitted value. -/
def rangeElement (r : DateRange) (n : I) : Jl I := calendarAdd r.years r.start (r.step*n)

/-- stdlib/Dates/src/ranges.jl:72: the repeated iterate calls after the
initial element. An exception terminates the traversal, as in Julia. -/
def collectTail (r : DateRange) : Nat → Nat → Jl (List I)
  | 0, _ => .ok []
  | count+1, index => do
    let v ← rangeElement r (i index)
    let vs ← collectTail r count (index+1)
    pure (v::vs)

/-- stdlib/Dates/src/ranges.jl:71-72: the first call caches length and emits
the stored start, then the second method indexes from the original start. -/
def collectRange (r : DateRange) (length : I) : Jl (List I) :=
  if length.val ≤ 0 then .ok []
  else do
    let tail ← collectTail r (length.val.toNat-1) 1
    pure (r.start::tail)

/-- stdlib/Dates/src/ranges.jl:66-69. -/
def rangeContains (r : DateRange) (x : I) (fuel : Nat) : Option (Jl Bool) := do
  match ← calendarLen r.start x r.step r.years fuel with
  | .error e => pure (.error e)
  | .ok k =>
    match ← rangeLength r fuel with
    | .error e => pure (.error e)
    | .ok length =>
      let n := k+i 1
      if n.val ≥ 1 ∧ n ≤ length then
        match rangeElement r (n-i 1) with
        | .error e => pure (.error e)
        | .ok value => pure (.ok (value == x))
      else pure (.ok false)

end JuliaLean.Dates
