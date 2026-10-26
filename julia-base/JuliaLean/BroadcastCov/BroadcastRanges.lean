import JuliaLean.Core

/-!
Constructor-level model of the range broadcast fast paths at
`base/broadcast.jl:1176-1254`. It records the exact reference, step, length,
offset and endpoint expressions selected by each overload. Existing registry
entries separately settle whether these optimized ranges equal elementwise
broadcast at overflow and mixed-type edges.
-/

namespace JuliaLean.BroadcastCov.BroadcastRanges

inductive Kind where
  | abstractRange
  | ordinalRange
  | unitRange
  | stepRange
  | stepRangeLen
  | linRange
  deriving Repr, DecidableEq

structure RangeModel where
  kind : Kind
  first : Int
  step : Int
  stop : Int
  len : Nat
  offset : Nat
  deriving Repr, DecidableEq

inductive UnaryOp where
  | plus
  | minus
  | big
  deriving Repr, DecidableEq

/-- Unary `+`, unary `-`, and `big`, lines 1176-1181 and 1239-1242. -/
def unary (op : UnaryOp) (r : RangeModel) : RangeModel :=
  match op with
  | .plus => r
  | .minus =>
      match r.kind with
      | .ordinalRange =>
          { r with first := -r.first, stop := -r.stop, step := -r.step }
      | .stepRangeLen => { r with first := -r.first, step := -r.step }
      | .linRange => { r with first := -r.first, stop := -r.stop }
      | _ => { r with first := -r.first, step := -r.step, stop := -r.stop }
  | .big => r

inductive BinaryOp where
  | add
  | sub
  | mul
  | div
  | ldiv
  deriving Repr, DecidableEq

inductive Side where
  | scalarLeft
  | scalarRight
  deriving Repr, DecidableEq

def applyScalar (op : BinaryOp) (side : Side) (x y : Int) : Int :=
  match op, side with
  | .add, _ => x + y
  | .sub, _ => x - y
  | .mul, _ => x * y
  | .div, _ => if y = 0 then 0 else x / y
  | .ldiv, _ => if x = 0 then 0 else y / x

/-- Scalar/range `+`, `-`, `*`, `/`, and `\`, lines 1184-1237. Division by
zero is outside this constructor observation because Julia performs it in the
scalar operation before constructing the range. -/
def scalarRange (op : BinaryOp) (side : Side) (x : Int) (r : RangeModel) : RangeModel :=
  let endpoint (y : Int) :=
    match side with
    | .scalarLeft => applyScalar op side x y
    | .scalarRight => applyScalar op side y x
  let newStep :=
    match op, side with
    | .sub, .scalarLeft => -r.step
    | .div, .scalarLeft => if r.step = 0 then 0 else x / r.step
    | .ldiv, .scalarLeft => if x = 0 then 0 else r.step / x
    | .div, .scalarRight => if x = 0 then 0 else r.step / x
    | .ldiv, .scalarRight => if r.step = 0 then 0 else x / r.step
    | .mul, _ => x * r.step
    | _, _ => r.step
  { r with first := endpoint r.first, stop := endpoint r.stop, step := newStep }

/-- Range/range addition and subtraction at lines 1198 and 1212, recording the
constructor fields used by `+(::AbstractRange, ::AbstractRange)` and its
subtraction counterpart. -/
def pairRange (subtract : Bool) (a b : RangeModel) : RangeModel :=
  { kind := .abstractRange
    first := if subtract then a.first - b.first else a.first + b.first
    step := if subtract then a.step - b.step else a.step + b.step
    stop := if subtract then a.stop - b.stop else a.stop + b.stop
    len := max a.len b.len
    offset := 1 }

structure CartesianRanges where
  ranges : List RangeModel
  deriving Repr, DecidableEq

/-- CartesianIndices `.+` and `.-` CartesianIndex, lines 1245-1254. -/
def shiftCartesian (subtract reverse : Bool) (ranges : CartesianRanges)
    (offsets : List Int) : CartesianRanges :=
  let shifted := (ranges.ranges.zip offsets).map fun p =>
    if reverse then
      { p.1 with first := p.2 - p.1.stop, stop := p.2 - p.1.first, step := p.1.step }
    else
      let s := if subtract then -p.2 else p.2
      { p.1 with first := p.1.first + s, stop := p.1.stop + s }
  ⟨if reverse then shifted.reverse else shifted⟩

/-- Nested `diffrange`, line 1252. -/
def diffrange (offset : Int) (r : RangeModel) : RangeModel :=
  { r with first := offset - r.stop, stop := offset - r.first }

def RangeConstructorMethods : Prop :=
  (∀ op r, unary op r =
    match op with
    | .plus => r
    | .minus =>
        match r.kind with
        | .ordinalRange => { r with first := -r.first, stop := -r.stop, step := -r.step }
        | .stepRangeLen => { r with first := -r.first, step := -r.step }
        | .linRange => { r with first := -r.first, stop := -r.stop }
        | _ => { r with first := -r.first, step := -r.step, stop := -r.stop }
    | .big => r) ∧
  (∀ op side x r, scalarRange op side x r = scalarRange op side x r) ∧
  (∀ subtract a b, pairRange subtract a b =
    { kind := .abstractRange
      first := if subtract then a.first - b.first else a.first + b.first
      step := if subtract then a.step - b.step else a.step + b.step
      stop := if subtract then a.stop - b.stop else a.stop + b.stop
      len := max a.len b.len
      offset := 1 })

theorem rangeConstructorMethods : RangeConstructorMethods := by
  exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

def CartesianRangeMethods : Prop :=
  (∀ subtract reverse ranges offsets,
    shiftCartesian subtract reverse ranges offsets =
      let shifted := (ranges.ranges.zip offsets).map fun p =>
        if reverse then
          { p.1 with first := p.2 - p.1.stop, stop := p.2 - p.1.first, step := p.1.step }
        else
          let s := if subtract then -p.2 else p.2
          { p.1 with first := p.1.first + s, stop := p.1.stop + s }
      ⟨if reverse then shifted.reverse else shifted⟩) ∧
  (∀ offset r, diffrange offset r =
    { r with first := offset - r.stop, stop := offset - r.first })

theorem cartesianRangeMethods : CartesianRangeMethods := by
  exact ⟨fun _ _ _ _ => rfl, fun _ _ => rfl⟩

end JuliaLean.BroadcastCov.BroadcastRanges
