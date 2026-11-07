import JuliaLean.base.broadcast

namespace JuliaLean.BroadcastCov.BroadcastRanges

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
