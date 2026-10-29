import JuliaLean.Ranges.Ordinal
import JuliaLean.Ranges.Keywords
import JuliaLean.IntArith.NumberTheory

set_option maxRecDepth 4096

namespace JuliaLean.Ranges

/-- `base/range.jl:881-884`: ordinal minimum checks emptiness before reading endpoints. -/
def minimum (r : Rng) : Jl Num :=
  if isEmpty r then .error (.argumentError "range must be non-empty")
  else .ok (if r.kind = .step then Num.min (first r) (last r) else first r)

/-- `base/range.jl:881-884`: ordinal maximum checks emptiness before reading endpoints. -/
def maximum (r : Rng) : Jl Num :=
  if isEmpty r then .error (.argumentError "range must be non-empty")
  else .ok (if r.kind = .step then Num.max (first r) (last r) else last r)

/-- `base/range.jl:920`: extrema evaluates minimum before maximum. -/
def extrema (r : Rng) : Jl (Num × Num) := do
  let lo ← minimum r
  let hi ← maximum r
  pure (lo, hi)

/-- `base/range.jl:1479-1484`: integer membership uses independent moduli to avoid subtract overflow. -/
def contains (x : Num) (r : Rng) : Jl Bool := do
  if r.kind ≠ .step then
    pure (decide ((first r).val ≤ x.val ∧ x.val ≤ (last r).val))
  else if isEmpty r then pure false
  else if (step r).val = 0 then pure (Num.eq x (first r))
  else
    let lo ← minimum r
    let hi ← maximum r
    if x.val < lo.val ∨ hi.val < x.val then pure false
    else
      let x ← Num.cast (first r).ty x
      let a ← Num.mod x (step r)
      let b ← Num.mod (first r) (step r)
      pure (decide ((Num.sub a b).val = 0))

/-- `base/range.jl:1435`: reversing ordinal ranges reconstructs with `negate(step)`. -/
def reverse (r : Rng) : Jl Rng := do
  let st ← Num.negate (step r)
  colon3 (last r) st (first r)

/-- `base/range.jl:1312`: ordinal unary minus uses the length constructor. -/
def negateRange (r : Rng) : Jl ResultRng := do
  let st ← Num.negate (step r)
  let len ← length r
  rangeStartStepLength (Num.neg (first r)) st len

/-- `base/range.jl:1458-1464`: sum divides the even length factor before multiplying. -/
def sum (r : Rng) : Jl Num := do
  let l ← length r
  let lm := Num.sub l (Num.lit (.bit .i64) 1)
  let tail := if l.val % 2 = 0 then
      Num.mul (Num.mul (step r) lm) (Num.lit l.ty (l.val / 2))
    else Num.mul (Num.mul (step r) l) (Num.lit lm.ty (lm.val / 2))
  pure (Num.add (Num.mul l (first r)) tail)

/-- `base/range.jl:1134-1151`: specialized OneTo/unit equality precedes ordinal equality. -/
def rangeEq (r s : Rng) : Bool :=
  if r.kind = .oneTo ∧ s.kind = .oneTo then Num.eq (last r) (last s)
  else if r.kind ≠ .step ∧ s.kind ≠ .step then
    (isEmpty r && isEmpty s) || (Num.eq (first r) (first s) && Num.eq (last r) (last s))
  else if isEmpty r then isEmpty s
  else if Num.eq (first r) (last r) then
    Num.eq (first s) (last s) && Num.eq (first r) (first s)
  else Num.eq (first r) (first s) && Num.eq (step r) (step s) && Num.eq (last r) (last s)

/-- `base/abstractarray.jl:756-757`, `base/multidimensional.jl:910-917`: logical indices compare axes. -/
def checkRangeIndex (r s : Rng) : Jl Bool := do
  let n ← length r
  if (first s).ty = .bool then
    let m ← length s
    pure (Num.eq n m)
  else pure (isEmpty s || decide (1 ≤ (first s).val ∧ (first s).val ≤ n.val ∧
    1 ≤ (last s).val ∧ (last s).val ≤ n.val))

/-- `base/range.jl:1002-1012`: find a representable endpoint on the empty side. -/
def emptyStop (start st : Num) : Jl Num := do
  let stop := if st.val > 0 then Num.sub start (Num.one st.ty)
    else Num.add start (Num.one st.ty)
  if (if st.val > 0 then stop.val < start.val else stop.val > start.val) then
    pure stop
  else
    throw (.overflowError s!"cannot represent an empty range starting at {start.val}")

/-- A successfully represented empty endpoint lies opposite to the step direction. -/
def emptyStopDirection : Prop :=
  ∀ start st stop, emptyStop start st = .ok stop →
    (0 < st.val → stop.val < start.val) ∧
    (st.val ≤ 0 → start.val < stop.val)

theorem emptyStopDirection_proven : emptyStopDirection := by
  intro start st stop h
  by_cases hs : 0 < st.val
  · simp only [emptyStop, hs, ↓reduceIte] at h
    split at h
    · rename_i hlt
      cases h
      exact ⟨fun _ => hlt, fun hn => False.elim (by omega)⟩
    · contradiction
  · simp only [emptyStop, hs, ↓reduceIte] at h
    split at h
    · rename_i hlt
      cases h
      exact ⟨fun hp => False.elim (hs hp), fun _ => hlt⟩
    · contradiction

/-- `base/range.jl:1002-1067`: all ordinal range-indexing dispatches, including logical ranges. -/
def getindexRange (r s : Rng) : Jl ResultRng := do
  if !(← checkRangeIndex r s) then throw .boundsError
  if r.kind = .oneTo ∧ s.kind = .oneTo then
    let stop ← Num.cast (first r).ty (last s)
    return .ordinal (← oneTo stop)
  if (first s).ty = .bool then
    if r.kind ≠ .step then
      let start := if (first s).val ≠ 0 then first r else last r
      return ← if s.kind ≠ .step then rangeStartLength start (last s)
        else rangeStartStepLength start (Num.one (first r).ty) (Num.lit (.bit .i64) (last s).val)
    else
      let nonempty := if (step s).val > 0 then decide ((last s).val ≠ 0) else decide ((first s).val ≠ 0)
      let useLast := (decide ((first s).val ≠ 0) != nonempty) != isEmpty r
      rangeStartStepLength (if useLast then last r else first r) (step r)
        (Num.lit (.bit .i64) (if nonempty then 1 else 0))
  else if r.kind ≠ .step ∧ s.kind ≠ .step then
    let f := first r
    let start ← Num.cast f.ty (Num.sub (Num.add f (first s)) (Num.lit (.bit .i64) 1))
    let len ← length s
    let stop ← Num.cast f.ty (← if isEmpty s then emptyStop start (step r)
      else pure (Num.add start (Num.sub len (Num.one len.ty))))
    return .ordinal (← colon2 start stop)
  else
    let f := first r
    let start ← if r.kind = .step then
        Num.cast f.ty (Num.add f (Num.mul (Num.sub (first s) (Num.lit (.bit .i64) 1)) (step r)))
      else Num.cast f.ty (Num.sub (Num.add f (first s)) (Num.lit (.bit .i64) 1))
    let st := if r.kind = .step then Num.mul (step r) (step s) else step s
    let len ← length s
    let stop ← Num.cast f.ty (← if isEmpty s then emptyStop start st
      else pure (Num.add start (Num.mul (Num.sub len (Num.one len.ty)) st)))
    return .ordinal (← colon3 start st stop)

/-- `base/range.jl:1219-1225`: negative step is negated with wrapping unary minus. -/
def firstStepLastAscending (r : Rng) : Num × Num × Num :=
  if (step r).val < 0 then (last r, Num.neg (step r), first r)
  else (first r, Num.pos (step r), last r)

/-- `base/range.jl:1205-1217`: unit/step intersection keeps the first argument ascending. -/
def intersectUnitStep (r s : Rng) : Jl Rng := do
  let t := Num.promote (first r).ty (first s).ty
  if isEmpty s then
    let a ← Num.cast t (first r)
    let b ← Num.cast t (Num.sub (first r) (step s))
    stepRange a (Num.pos (step s)) b
  else
    let (sta, ste, sto) := firstStepLastAscending s
    let lo := first r
    let hi := last r
    let m ← Num.mod (Num.sub sta lo) ste
    let n ← Num.mod (Num.sub hi sta) ste
    let a ← Num.cast t (Num.max sta (Num.add lo m))
    let b ← Num.cast t (Num.min sto (Num.sub hi n))
    stepRange a ste b

/-- `base/array.jl:2474-2485`: mixed-element-type step searches use indexed findnext. -/
def findfirstScan (x : Num) (r : Rng) : Nat → Num → Jl (Option Num)
  | 0, _ => .ok none
  | n + 1, i => do
      let a ← getindex r i
      if Num.eq x a then return some i
      findfirstScan x r n (Num.add i (Num.lit (.bit .i64) 1))

/-- `base/array.jl:2534-2552`: equality/isequal findfirst specializations on integer ranges. -/
def findfirstEq (x : Num) (r : Rng) : Jl (Option Num) := do
  if r.kind = .oneTo then
    if 1 ≤ x.val ∧ x.val ≤ (last r).val then
      return some (← Num.cast (.bit .i64) x)
    else return none
  else if r.kind ≠ .step then
    if (first r).val ≤ x.val ∧ x.val ≤ (last r).val then
      let n ← length r
      let _ ← Num.cast (.bit .i64) n
      let d ← Num.cast (.bit .i64) (Num.sub x (first r))
      return some (Num.add (Num.lit (.bit .i64) 1) d)
    else return none
  else if x.ty ≠ (first r).ty then
    let n ← length r
    let n ← Num.cast (.bit .i64) n
    findfirstScan x r n.val.toNat (Num.lit (.bit .i64) 1)
  else
    if isEmpty r then return none
    let lo ← minimum r
    let hi ← maximum r
    if x.val < lo.val ∨ hi.val < x.val then return none
    let d := Num.sub x (first r)
    let rem ← Num.rem d (step r)
    if rem.val ≠ 0 then return none
    let q ← Num.div d (step r)
    return some (← Num.cast (.bit .i64) (Num.add q (Num.lit (.bit .i64) 1)))

/-- `base/array.jl:2537-2538,2554-2555`: iszero delegates except for OneTo. -/
def findfirstZero (r : Rng) : Jl (Option Num) :=
  if r.kind = .oneTo then .ok none else findfirstEq (Num.zero (first r).ty) r

/-- `base/array.jl:2538,2555`: isone delegates except for OneTo. -/
def findfirstOne (r : Rng) : Jl (Option Num) :=
  if r.kind = .oneTo then .ok (if isEmpty r then none else some (Num.lit (.bit .i64) 1))
  else findfirstEq (Num.one (first r).ty) r


/-- `base/abstractset.jl:348-351`: range fallback short-circuits on the first missing element.
The natural counter is the finite ordinal cardinality, rather than a machine length. -/
def subsetScan (r s : Rng) : Nat → Num → Jl Bool
  | 0, _ => .ok true
  | n + 1, x => do
      if !(← contains x s) then return false
      if n = 0 then return true
      let next ← Num.cast (first r).ty (Num.add x (step r))
      subsetScan r s n next

/-- `base/range.jl:1305-1308`, `base/abstractset.jl:335-351`: ranges have fast membership. -/
def issubset (r s : Rng) : Jl Bool :=
  if r.kind = .oneTo ∧ s.kind = .oneTo then
    .ok (decide ((last r).val ≤ (last s).val))
  else if r.kind ≠ .step ∧ s.kind ≠ .step then
    .ok (isEmpty r || decide ((first s).val ≤ (first r).val ∧ (last r).val ≤ (last s).val))
  else subsetScan r s (trueCount r).toNat (first r)

/-- `base/div.jl:387-407,422-433`: ceiling quotient adds one exactly when the nonzero remainder
has the divisor's sign; mixed-sign quotient type is retained. -/
def operationCld (a b : Num) : Jl Num := do
  let q ← Num.div a b
  if a.ty = .bool ∧ b.ty = .bool then return q
  let r ← Num.rem a b
  pure (Num.add q (Num.lit .bool (if r.val ≠ 0 ∧ decide (a.val < 0) = decide (b.val < 0) then 1 else 0)))

/-- `base/range.jl:1286-1303`, `base/array.jl:2966`: specialized `findall(in(span), r)`. -/
def findallInUnit (r span : Rng) : Jl Rng := do
  let fr := first r
  let lr := last r
  let sr := step r
  let fs := first span
  let ls := last span
  let one := Num.lit (.bit .i64) 1
  let (a, b) ← if sr.val > 0 then do
      let a ← if fr.val ≥ fs.val then pure one
        else do pure (Num.add (← operationCld (Num.sub fs fr) sr) one)
      let b ← if lr.val ≤ ls.val then length r
        else do pure (Num.sub (← length r) (← operationCld (Num.sub lr ls) sr))
      pure (a, b)
    else if sr.val < 0 then do
      let a ← if fr.val ≤ ls.val then pure one
        else do pure (Num.add (← operationCld (Num.sub ls fr) sr) one)
      let b ← if lr.val ≥ fs.val then length r
        else do pure (Num.sub (← length r) (← operationCld (Num.sub lr fs) sr))
      pure (a, b)
    else do
      let a ← if fr.val ≥ fs.val then pure one else do pure (Num.add (← length r) one)
      let b ← if fr.val ≤ ls.val then length r else pure (Num.lit (.bit .i64) 0)
      pure (a, b)
  if r.kind = .step then colon3 a one b else colon2 a b

/-- `base/array.jl:2843-2853`: collect predicate matches in increasing Int index order. -/
def findallScan (predicate : Num → Jl Bool) (r : Rng) : Nat → Num → Num → Jl (List Num)
  | 0, _, _ => .ok []
  | n + 1, i, x => do
      let yes ← predicate x
      let tail ← if n = 0 then pure []
        else do
          let next ← Num.cast (first r).ty (Num.add x (step r))
          findallScan predicate r n (Num.add i (Num.lit (.bit .i64) 1)) next
      pure (if yes then i :: tail else tail)

/-- `base/array.jl:2796,2843-2853`: equality broadcast followed by Boolean findall. -/
def findallEq (x : Num) (r : Rng) : Jl (List Num) := do
  let len ← length r
  let _ ← Num.cast (.bit .i64) len
  findallScan (fun y => .ok (Num.eq y x)) r (trueCount r).toNat
    (Num.lit (.bit .i64) 1) (first r)

/-- `base/array.jl:2966`, `base/range.jl:1286`: stepped spans use generic membership;
unit spans use the range-valued specialization. -/
def findallIn (r span : Rng) : Jl (Rng ⊕ List Num) := do
  if span.kind ≠ .step then return .inl (← findallInUnit r span)
  let len ← length r
  let _ ← Num.cast (.bit .i64) len
  return .inr (← findallScan (fun x => contains x span) r (trueCount r).toNat
    (Num.lit (.bit .i64) 1) (first r))

/-- `base/intfuncs.jl:149-165`: mixed-sign lcm uses its signed/unsigned promotion methods. -/
def operationLcm (a b : Num) : Jl Num := do
  match a, b with
  | ⟨.bit _, x⟩, ⟨.bit _, y⟩ =>
      let z ← JuliaLean.IntArith.NumberTheory.mixedLcm x y
      pure ⟨.bit _, z⟩
  | ⟨.bool, x⟩, ⟨.bool, y⟩ => pure (Num.lit .bool (if x && y then 1 else 0))
  | ⟨.bool, _⟩, ⟨.bit t, y⟩ =>
      let x ← JInt.convert t a.val
      let z ← JuliaLean.IntArith.NumberTheory.lcm x y
      pure ⟨.bit t, z⟩
  | ⟨.bit t, x⟩, ⟨.bool, _⟩ =>
      let y ← JInt.convert t b.val
      let z ← JuliaLean.IntArith.NumberTheory.lcm x y
      pure ⟨.bit t, z⟩

/-- `base/intfuncs.jl:242-288`: mixed gcdx returns Bézout coefficients in its promoted type. -/
def operationGcdx (a b : Num) : Jl (Num × Num × Num) := do
  match a, b with
  | ⟨.bit _, x⟩, ⟨.bit _, y⟩ =>
      let (g, x, y) ← JuliaLean.IntArith.NumberTheory.mixedGcdx x y
      pure (⟨.bit _, g⟩, ⟨.bit _, x⟩, ⟨.bit _, y⟩)
  | ⟨.bool, x⟩, ⟨.bool, y⟩ =>
      if (show Bool from y) = true then pure (Num.one .bool, Num.zero .bool, Num.one .bool)
      else if (show Bool from x) = true then pure (Num.one .bool, Num.one .bool, Num.zero .bool)
      else pure (Num.zero .bool, Num.zero .bool, Num.zero .bool)
  | ⟨.bool, _⟩, ⟨.bit t, y⟩ =>
      let x ← JInt.convert t a.val
      let (g, x, y) ← JuliaLean.IntArith.NumberTheory.gcdx x y
      pure (⟨.bit t, g⟩, ⟨.bit t, x⟩, ⟨.bit t, y⟩)
  | ⟨.bit t, x⟩, ⟨.bool, _⟩ =>
      let y ← JInt.convert t b.val
      let (g, x, y) ← JuliaLean.IntArith.NumberTheory.gcdx x y
      pure (⟨.bit t, g⟩, ⟨.bit t, x⟩, ⟨.bit t, y⟩)

/-- `base/range.jl:1235-1265`: step/step intersection retains wrapping intermediates. -/
def intersectSteps (r s : Rng) : Jl Rng := do
  let t := Num.promote (first r).ty (first s).ty
  let u := Num.promote (step r).ty (step s).ty
  let build := fun a st b => do
    let a ← Num.cast t a
    let st ← Num.cast u st
    let b ← Num.cast t b
    stepRange a st b
  if isEmpty r || isEmpty s then
    return ← build (first r) (step r) (Num.sub (first r) (step r))
  let (start1, step1, stop1) := firstStepLastAscending r
  let (start2, step2, stop2) := firstStepLastAscending s
  let a ← operationLcm step1 step2
  let (g, x, _) ← operationGcdx step1 step2
  let diff := Num.sub start1 start2
  let rem ← Num.rem diff g
  if rem.val ≠ 0 then
    if (step r).val < 0 then build stop1 (Num.neg a) (Num.add stop1 a)
    else build start1 a (Num.sub start1 a)
  else
    let z ← Num.div diff g
    let b := Num.sub start1 (Num.mul (Num.mul x z) step1)
    let m1 ← Num.mod (Num.sub b start1) a
    let m2 ← Num.mod (Num.sub b start2) a
    let n1 ← Num.mod (Num.sub stop1 b) a
    let n2 ← Num.mod (Num.sub stop2 b) a
    let m := Num.max (Num.add start1 m1) (Num.add start2 m2)
    let n := Num.min (Num.sub stop1 n1) (Num.sub stop2 n2)
    if (step r).val < 0 then build n (Num.neg a) m else build m a n

/-- `base/range.jl:1196-1265`: all nine OneTo/UnitRange/StepRange pairings,
with first-input order retained by reversing descending first inputs. -/
def intersect (r s : Rng) : Jl Rng := do
  if r.kind = .oneTo ∧ s.kind = .oneTo then oneTo (Num.min (last r) (last s))
  else if r.kind ≠ .step ∧ s.kind ≠ .step then
    colon2 (Num.max (first r) (first s)) (Num.min (last r) (last s))
  else if r.kind ≠ .step then intersectUnitStep r s
  else if s.kind ≠ .step then
    if (step r).val < 0 then
      let rr ← reverse r
      let result ← intersectUnitStep s rr
      reverse result
    else intersectUnitStep s r
  else intersectSteps r s

/-- Every integer in the endpoint interval belongs to a unit range, independent of integer type. -/
def unitMembershipProp : Prop :=
  ∀ (r : Rng) (x : Num), r.kind ≠ .step →
    contains x r = .ok (decide ((first r).val ≤ x.val ∧ x.val ≤ (last r).val))

theorem unitMembershipThm : unitMembershipProp := by
  intro r x h
  simp [contains, h]
  rfl

/-- Empty ranges have no minimum or maximum, including empty unsigned/Bool ranges. -/
def emptyExtremaProp : Prop :=
  ∀ r : Rng, isEmpty r = true →
    minimum r = .error (.argumentError "range must be non-empty") ∧
    maximum r = .error (.argumentError "range must be non-empty")

theorem emptyExtremaThm : emptyExtremaProp := by
  intro r h
  simp [minimum, maximum, h]

/-- The empty unit range `one(T):zero(T)` sums to integer zero for Bool and all ten integer types. -/
def emptySumProp : Prop :=
  ∀ ty : NType, ((unit (Num.one ty) (Num.zero ty)).bind sum).map Num.val = .ok 0

theorem emptySumThm : emptySumProp := by
  intro ty
  cases ty with
  | bool => decide
  | bit t => cases t <;> decide

/-- A unit range whose endpoints lie inside another unit range is a subset. -/
def unitSubsetProp : Prop :=
  ∀ r s : Rng, r.kind ≠ .step → s.kind ≠ .step →
    (first s).val ≤ (first r).val → (last r).val ≤ (last s).val →
    issubset r s = .ok true

theorem unitSubsetThm : unitSubsetProp := by
  intro r s hr hs hlo hhi
  by_cases h : r.kind = .oneTo ∧ s.kind = .oneTo
  · simp [issubset, h, hhi]
  · simp [issubset, h, hr, hs, hlo, hhi]

/-- Successful equality searches return a positive array index for any matching range element. -/
def findfirstPositiveProp : Prop :=
  ∀ (a st b : Num) (r : Rng) (x : Num),
    stepRange a st b = .ok r → contains x r = .ok true →
    match findfirstEq x r with
    | .ok (some i) => 1 ≤ i.val
    | _ => False

theorem findfirstPositiveRefuted : ¬ findfirstPositiveProp := by
  intro h
  let a := Num.lit (.bit .i8) (-100)
  let st := Num.lit (.bit .i8) 2
  let b := Num.lit (.bit .i8) 120
  let r : Rng := ⟨.step, a, st, b⟩
  have hs : stepRange a st b = .ok r := by decide
  have hm : contains (Num.lit (.bit .i8) 100) r = .ok true := by decide
  have hp := h a st b r (Num.lit (.bit .i8) 100) hs hm
  have hn : ¬ (match findfirstEq (Num.lit (.bit .i8) 100) r with
      | .ok (some i) => 1 ≤ i.val | _ => False) := by
    change ¬ (1 ≤ (-27 : Int))
    decide
  exact hn hp

/-- Unit/step intersection contains every element shared by both inputs. -/
def unitIntersectCompleteProp : Prop :=
  ∀ (a b c st d : Num) (r s : Rng) (x : Num),
    unit a b = .ok r → stepRange c st d = .ok s →
    contains x r = .ok true → contains x s = .ok true →
    match intersect r s with
    | .ok out => contains x out = .ok true
    | .error _ => False

theorem unitIntersectCompleteRefuted : ¬ unitIntersectCompleteProp := by
  intro h
  let a := Num.lit (.bit .i8) (-100)
  let b := Num.lit (.bit .i8) 100
  let c := Num.lit (.bit .i8) (-120)
  let st := Num.lit (.bit .i8) 7
  let d := Num.lit (.bit .i8) 125
  let r : Rng := ⟨.unit, a, Num.one (.bit .i8), b⟩
  let s : Rng := ⟨.step, c, st, d⟩
  let x := Num.lit (.bit .i8) 97
  have hr : unit a b = .ok r := by decide
  have hs : stepRange c st d = .ok s := by decide
  have hxr : contains x r = .ok true := by decide
  have hxs : contains x s = .ok true := by decide
  have hp := h a b c st d r s x hr hs hxr hxs
  have hn : ¬ (match intersect r s with
      | .ok out => contains x out = .ok true | .error _ => False) := by
    change ¬ ((.ok false : Jl Bool) = .ok true)
    decide
  exact hn hp

/-- Step/step intersection contains every element shared by both inputs. -/
def stepIntersectCompleteProp : Prop :=
  ∀ (a st b c su d : Num) (r s : Rng) (x : Num),
    stepRange a st b = .ok r → stepRange c su d = .ok s →
    contains x r = .ok true → contains x s = .ok true →
    match intersect r s with
    | .ok out => contains x out = .ok true
    | .error _ => False

theorem stepIntersectCompleteRefuted : ¬ stepIntersectCompleteProp := by
  intro h
  let a := Num.lit (.bit .i8) (-100)
  let b := Num.lit (.bit .i8) 120
  let st := Num.lit (.bit .i8) 2
  let su := Num.lit (.bit .i8) 3
  let r : Rng := ⟨.step, a, st, b⟩
  let s : Rng := ⟨.step, a, su, Num.lit (.bit .i8) 119⟩
  let x := Num.lit (.bit .i8) 116
  have hr : stepRange a st b = .ok r := by decide
  have hs : stepRange a su b = .ok s := by decide
  have hxr : contains x r = .ok true := by decide
  have hxs : contains x s = .ok true := by decide
  have hp := h a st b a su b r s x hr hs hxr hxs
  let out : Rng := ⟨.step, a, Num.lit (.bit .i8) 6, Num.lit (.bit .i8) 110⟩
  have hout : intersect r s = .ok out := by decide +kernel
  rw [hout] at hp
  exact (by decide : contains x out ≠ .ok true) hp

/-- Reversing a successfully constructed ordinal range preserves its mathematical cardinality. -/
def reverseCardinalityProp : Prop :=
  ∀ (a st b : Num) (r : Rng), stepRange a st b = .ok r →
    match reverse r with
    | .ok out => trueCount out = trueCount r
    | .error _ => False

theorem reverseCardinalityRefuted : ¬ reverseCardinalityProp := by
  intro h
  let a := Num.lit (.bit .i8) 0
  let st := Num.lit (.bit .i8) (-128)
  let r : Rng := ⟨.step, a, st, st⟩
  have hr : stepRange a st st = .ok r := by decide
  have hp := h a st st r hr
  have hn : ¬ (match reverse r with
      | .ok out => trueCount out = trueCount r | .error _ => False) := by
    change ¬ ((0 : Int) = 2)
    decide
  exact hn hp

/-- Negating an ordinal range negates every corresponding element with Julia scalar arithmetic. -/
def negatePointwiseProp : Prop :=
  ∀ (a st b : Num) (r : Rng) (i x : Num), stepRange a st b = .ok r →
    getindex r i = .ok x →
    match negateRange r with
    | .ok out => (resultGetindex out i).map Num.val = .ok (Num.neg x).val
    | .error _ => False

theorem negatePointwiseRefuted : ¬ negatePointwiseProp := by
  intro h
  let a := Num.lit (.bit .i8) (-128)
  let st := Num.lit (.bit .i8) 1
  let b := Num.lit (.bit .i8) (-126)
  let r : Rng := ⟨.step, a, st, b⟩
  let i := Num.lit (.bit .i64) 2
  let x := Num.lit (.bit .i8) (-127)
  have hr : stepRange a st b = .ok r := by decide
  have hx : getindex r i = .ok x := by decide
  have hp := h a st b r i x hr hx
  have hn : ¬ (match negateRange r with
      | .ok out => (resultGetindex out i).map Num.val = .ok (Num.neg x).val
      | .error _ => False) := by
    change ¬ ((.ok (-129) : Jl Int) = .ok 127)
    decide
  exact hn hp

/-- Valid integer range slicing agrees with scalar indexing at every selected position. -/
def sliceAgreementProp : Prop :=
  ∀ (a b c d : Num) (r s : Rng) (i j x : Num),
    unit a b = .ok r → unit c d = .ok s → (first s).ty ≠ .bool →
    checkRangeIndex r s = .ok true → getindex s i = .ok j → getindex r j = .ok x →
    match getindexRange r s with
    | .ok out => (resultLength out).map Num.val = (length s).map Num.val ∧
        (resultGetindex out i).map Num.val = .ok x.val
    | .error _ => False

theorem sliceAgreementRefuted : ¬ sliceAgreementProp := by
  intro h
  let a := Num.lit (.bit .i8) 120
  let b := Num.lit (.bit .i8) 127
  let c := Num.lit (.bit .i8) 8
  let r : Rng := ⟨.unit, a, Num.one (.bit .i8), b⟩
  let s : Rng := ⟨.unit, c, Num.one (.bit .i8), c⟩
  let i := Num.lit (.bit .i64) 1
  let x := Num.lit (.bit .i8) 127
  have hr : unit a b = .ok r := by decide
  have hs : unit c c = .ok s := by decide
  have ht : (first s).ty ≠ .bool := by decide
  have hb : checkRangeIndex r s = .ok true := by decide
  have hi : getindex s i = .ok c := by decide
  have hx : getindex r c = .ok x := by decide
  have hp := h a b c c r s i c x hr hs ht hb hi hx
  have hn : ¬ (match getindexRange r s with
      | .ok out => (resultLength out).map Num.val = (length s).map Num.val ∧
          (resultGetindex out i).map Num.val = .ok x.val
      | .error _ => False) := by
    change ¬ False
    simp
  exact hn hp

/-- Empty integer selectors can fail when the source starts at unsigned zero. -/
theorem emptyUnsignedUnitSliceError :
    (do
      let r ← unit (Num.lit (.bit .u8) 0) (Num.lit (.bit .u8) 3)
      let s ← unit (Num.lit (.bit .i64) 1) (Num.lit (.bit .i64) 0)
      getindexRange r s) = .error (.overflowError "cannot represent an empty range starting at 0") := by
  decide

theorem emptyUnsignedStepSliceError :
    (do
      let r ← unit (Num.lit (.bit .u8) 0) (Num.lit (.bit .u8) 3)
      let s ← stepRange (Num.lit (.bit .i64) 1) (Num.lit (.bit .i64) 2)
        (Num.lit (.bit .i64) 0)
      getindexRange r s) = .error (.inexactError "UInt8") := by
  decide

/-- A valid empty selector produces an empty slice, including at unsigned zero. -/
def emptyUnitSlicePromise : Prop :=
  ∀ r s, (∃ a b, unit a b = .ok r) → (∃ c d, unit c d = .ok s) →
    isEmpty s = true → checkRangeIndex r s = .ok true →
    ∃ out, getindexRange r s = .ok out ∧ (resultLength out).map Num.val = .ok 0

theorem emptyUnitSlicePromiseRefuted : ¬ emptyUnitSlicePromise := by
  intro h
  let a := Num.lit (.bit .u8) 0
  let b := Num.lit (.bit .u8) 3
  let c := Num.lit (.bit .i64) 1
  let d := Num.lit (.bit .i64) 0
  let r : Rng := ⟨.unit, a, Num.one (.bit .u8), b⟩
  let s : Rng := ⟨.unit, c, Num.one (.bit .i64), d⟩
  have hr : unit a b = .ok r := by decide
  have hs : unit c d = .ok s := by decide
  have he : isEmpty s = true := by decide
  have hb : checkRangeIndex r s = .ok true := by decide
  obtain ⟨out, hout, _⟩ := h r s ⟨a, b, hr⟩ ⟨c, d, hs⟩ he hb
  have herr : getindexRange r s = .error (.overflowError "cannot represent an empty range starting at 0") := by decide
  rw [herr] at hout
  contradiction

/-- A valid empty stepped selector produces an empty slice. -/
def emptyUnitStepSlicePromise : Prop :=
  ∀ r s, (∃ a b, unit a b = .ok r) →
    (∃ c st d, stepRange c st d = .ok s) →
    isEmpty s = true → checkRangeIndex r s = .ok true →
    ∃ out, getindexRange r s = .ok out ∧ (resultLength out).map Num.val = .ok 0

theorem emptyUnitStepSlicePromiseRefuted : ¬ emptyUnitStepSlicePromise := by
  intro h
  let a := Num.lit (.bit .u8) 0
  let b := Num.lit (.bit .u8) 3
  let c := Num.lit (.bit .i64) 1
  let st := Num.lit (.bit .i64) 2
  let d := Num.lit (.bit .i64) 0
  let r : Rng := ⟨.unit, a, Num.one (.bit .u8), b⟩
  let s : Rng := ⟨.step, c, st, Num.lit (.bit .i64) 0⟩
  have hr : unit a b = .ok r := by decide
  have hs : stepRange c st d = .ok s := by decide
  have he : isEmpty s = true := by decide
  have hb : checkRangeIndex r s = .ok true := by decide
  obtain ⟨out, hout, _⟩ := h r s ⟨a, b, hr⟩ ⟨c, st, d, hs⟩ he hb
  have herr : getindexRange r s = .error (.inexactError "UInt8") := by decide
  rw [herr] at hout
  contradiction

/-- Property observation of `base/range.jl:1458-1463` against repeated iteration. -/
def pairSumCheck (r : Rng) : Bool :=
  match iterateAt r 0, iterateAt r 1, sum r with
  | .ok (some a), .ok (some b), .ok z =>
      decide (z.val = (Num.lit z.ty (a.val + b.val)).val)
  | _, _, _ => false

/-- For every machine integer width/sign, two-element ranges beside each extremum
sum to the sum of their iterated elements reduced in the actual result type. -/
def edgeSumProp : Prop :=
  ∀ (t : IntTy) (descending : Bool), pairSumCheck (extremalPair t descending) = true

theorem edgeSumThm : edgeSumProp := by
  intro t descending
  cases t <;> cases descending <;> decide

/-- Property observation of `base/range.jl:881-884,920` against repeated iteration. -/
def pairExtremaCheck (r : Rng) : Bool :=
  match iterateAt r 0, iterateAt r 1, extrema r with
  | .ok (some a), .ok (some b), .ok (lo, hi) =>
      decide (lo.val = min a.val b.val ∧ hi.val = max a.val b.val)
  | _, _, _ => false

/-- For every machine integer width/sign, extrema of nonempty edge pairs equal
the mathematical extrema of the values returned by repeated Julia iteration. -/
def edgeExtremaProp : Prop :=
  ∀ (t : IntTy) (descending : Bool), pairExtremaCheck (extremalPair t descending) = true

theorem edgeExtremaThm : edgeExtremaProp := by
  intro t descending
  cases t <;> cases descending <;> decide

/-- Membership near each type's endpoints agrees with iteration, including UInt8
queries and Int64 queries mathematically outside a narrow range's element type. -/
def edgeMembershipProp : Prop :=
  ∀ (t : IntTy) (descending unsignedQuery : Bool) (probe : Fin 3),
    let r := extremalPair t descending
    let queryTy : NType := .bit (if unsignedQuery then .u8 else .i64)
    let query := Num.lit queryTy (if probe.val = 0 then (first r).val
      else if probe.val = 1 then (last r).val
      else (first r).val + (if descending then 1 else -1))
    contains query r = .ok true ↔
      ∃ i : Fin 2, (iterateAt r i.val).map (Option.map Num.val) = .ok (some query.val)

theorem edgeMembershipThm : edgeMembershipProp := by
  intro t descending unsignedQuery probe
  cases t <;> cases descending <;> cases unsignedQuery
  all_goals
    rcases probe with ⟨p, hp⟩
    have h : p = 0 ∨ p = 1 ∨ p = 2 := by omega
    rcases h with rfl | rfl | rfl <;> decide +revert

/-- Intersecting a constructed step range with an empty constructed unit range returns empty. -/
def intersectEmptyProp : Prop :=
  ∀ (a st b c d : Num) (r s : Rng),
    stepRange a st b = .ok r → unit c d = .ok s → isEmpty s = true →
    (intersect r s).map isEmpty = .ok true

theorem intersectEmptyRefuted : ¬ intersectEmptyProp := by
  intro h
  let a := Num.lit (.bit .i8) (-128)
  let st := Num.lit (.bit .i8) 127
  let b := Num.lit (.bit .i8) 126
  let c := Num.lit (.bit .i8) 5
  let d := Num.lit (.bit .i8) 4
  let r : Rng := ⟨.step, a, st, b⟩
  let s : Rng := ⟨.unit, c, Num.one (.bit .i8), d⟩
  have hr : stepRange a st b = .ok r := by decide
  have hs : unit c d = .ok s := by decide
  have he : isEmpty s = true := by decide
  have hp := h a st b c d r s hr hs he
  exact (by decide : (intersect r s).map isEmpty ≠ .ok true) hp

/-- A unit/step intersection cannot contain a value absent from either input. -/
def intersectMixedSoundProp : Prop :=
  ∀ (a b c st d : Num) (r s out : Rng) (x : Num),
    unit a b = .ok r → stepRange c st d = .ok s →
    intersect r s = .ok out → contains x out = .ok true →
    contains x r = .ok true ∧ contains x s = .ok true

theorem intersectMixedSoundRefuted : ¬ intersectMixedSoundProp := by
  intro h
  let a := Num.lit (.bit .u8) 0
  let b := Num.lit (.bit .u8) 255
  let c := Num.lit (.bit .i8) (-100)
  let st := Num.lit (.bit .i8) 7
  let d := Num.lit (.bit .i8) 117
  let r : Rng := ⟨.unit, a, Num.one (.bit .u8), b⟩
  let s : Rng := ⟨.step, c, st, d⟩
  let x := Num.lit (.bit .u8) 2
  let out : Rng := ⟨.step, x, st, Num.lit (.bit .u8) 114⟩
  have hr : unit a b = .ok r := by decide
  have hs : stepRange c st d = .ok s := by decide
  have ho : intersect r s = .ok out := by decide
  have hx : contains x out = .ok true := by decide
  have hp := h a b c st d r s out x hr hs ho hx
  exact (by decide : contains x s ≠ .ok true) hp.2

/-- Constructed stepped range slicing preserves its selected length and scalar elements. -/
def stepSliceAgreementProp : Prop :=
  ∀ (a st b c su d : Num) (r s : Rng) (i j x : Num),
    stepRange a st b = .ok r → stepRange c su d = .ok s → (first s).ty ≠ .bool →
    checkRangeIndex r s = .ok true → getindex s i = .ok j → getindex r j = .ok x →
    match getindexRange r s with
    | .ok out => (resultLength out).map Num.val = (length s).map Num.val ∧
        (resultGetindex out i).map Num.val = .ok x.val
    | .error _ => False

theorem stepSliceAgreementRefuted : ¬ stepSliceAgreementProp := by
  intro h
  let a := Num.lit (.bit .u64) 1
  let b := Num.lit (.bit .u64) 4
  let c := Num.lit (.bit .i64) 4
  let su := Num.lit (.bit .i64) (-1)
  let d := Num.lit (.bit .i64) 1
  let r : Rng := ⟨.step, a, a, b⟩
  let s : Rng := ⟨.step, c, su, d⟩
  let out : Rng := ⟨.step, b, Num.lit (.bit .u64) (-1), Num.lit (.bit .u64) 3⟩
  have hr : stepRange a a b = .ok r := by decide
  have hs : stepRange c su d = .ok s := by decide
  have ht : (first s).ty ≠ .bool := by decide
  have hb : checkRangeIndex r s = .ok true := by decide
  have hi : getindex s d = .ok c := by decide
  have hx : getindex r c = .ok b := by decide
  have hp := h a a b c su d r s d c b hr hs ht hb hi hx
  have ho : getindexRange r s = .ok (.ordinal out) := by decide
  rw [ho] at hp
  exact (by decide : (resultLength (.ordinal out)).map Num.val ≠ (length s).map Num.val) hp.1

/-- Additional concrete unit-search symptom of `base/array.jl:2540-2544`. -/
theorem findfirstUnitOverflow :
    (do
      let r ← unit (Num.lit (.bit .i8) (-128)) (Num.lit (.bit .i8) 127)
      let out ← findfirstEq (Num.lit (.bit .i8) 0) r
      pure (out.map Num.val)) = .ok (some (-127 : Int)) := by decide

/-- Additional Int64 empty-result symptom of `base/range.jl:1312`. -/
theorem negateInt64Empty :
    (do
      let a := Num.lit (.bit .i64) (IntTy.min .i64)
      let r ← colon3 a (Num.lit (.bit .i64) 3) (Num.lit (.bit .i64) (IntTy.min .i64 + 20))
      let out ← negateRange r
      let n ← resultLength out
      pure n.val) = .ok (0 : Int) := by decide

/-- `base/range.jl:1435,1453`: sort calls this reverse on the descending typemin-step input. -/
theorem reverseSortEmpty :
    (do
      let r ← colon3 (Num.lit (.bit .i8) 127) (Num.lit (.bit .i8) (-128))
        (Num.lit (.bit .i8) (-1))
      let out ← reverse r
      pure (isEmpty out)) = .ok true := by decide

/-- Self-intersection drops the last element, `base/range.jl:1235-1265`. -/
theorem intersectSelfDropsLast :
    (do
      let r ← colon3 (Num.lit (.bit .i8) (-128)) (Num.lit (.bit .i8) 127)
        (Num.lit (.bit .i8) 126)
      let out ← intersect r r
      pure (trueCount out)) = .ok (2 : Int) := by decide +kernel

/-- Descending intersection emits values absent from its first input, `base/range.jl:1262-1264`. -/
theorem intersectDescendingWrongFirst :
    (do
      let r ← colon3 (Num.lit (.bit .i8) 120) (Num.lit (.bit .i8) (-3))
        (Num.lit (.bit .i8) (-128))
      let s ← colon3 (Num.lit (.bit .i8) (-100)) (Num.lit (.bit .i8) 7)
        (Num.lit (.bit .i8) 120)
      let out ← intersect r s
      pure (first out).val) = .ok (104 : Int) := by decide +kernel

open JuliaLean.Registry in
def operationsEntries : List Entry := []

end JuliaLean.Ranges
