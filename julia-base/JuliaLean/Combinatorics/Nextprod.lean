import JuliaLean.Core

/-! `nextprod`, `base/combinatorics.jl:337-373`. The source calls `nextpow`
for each factor and then enumerates exponent counters. The executable loop is
used for differential checks; the empty-input branch is kernel-reducible for
the refutation theorem. -/

namespace JuliaLean.Combinatorics

open JuliaLean

private def nextPowerLoop (a x p : Nat) : Nat → Nat
  | 0 => p
  | fuel + 1 => if x ≤ p then p else nextPowerLoop a x (p * a) fuel

def nextPower (a x : Nat) : Jl Nat :=
  if x = 0 then .error (.domainError "x must be positive")
  else if a ≤ 1 then .error (.domainError "a must exceed one")
  else .ok (nextPowerLoop a x 1 128)

private partial def carry (a mx : List Nat) (p : Nat) (v : List Nat) (icarry : Nat) :
    Jl (Nat × List Nat × Nat) := do
  let vi := v.getD icarry 0
  if vi = 0 then .error .divideError else
  let p := p / vi
  let v := v.set icarry 1
  let icarry := icarry + 1
  let factor := a.getD icarry 0
  let p := p * factor
  let v := v.set icarry (v.getD icarry 0 * factor)
  if v.getD icarry 0 > mx.getD icarry 0 ∧ icarry + 1 < a.length then
    carry a mx p v icarry
  else .ok (p, v, icarry)

private partial def nextprodLoop (a mx : List Nat) (x p best icarry : Nat) (v : List Nat) : Nat :=
  if v.getLastD 0 < mx.getLastD 0 then
    if x ≤ p then
      let best := min p best
      match carry a mx p v icarry with
      | .error _ => best
      | .ok (p, v, icarry) =>
          nextprodLoop a mx x p best (if p < x then 0 else icarry) v
    else
      nextprodLoop a mx x (p * a.getD 0 0) best icarry
        (v.set 0 (v.getD 0 0 * a.getD 0 0))
  else min (mx.getLastD 0) best

/-- Source control flow for positive machine-`Int` inputs. Empty factors reach
the same first-element `BoundsError` as lines 344-345. -/
def nextprod (a : List Nat) (x : Nat) : Jl Nat := do
  let mx ← a.mapM (fun factor => nextPower factor x)
  match a, mx with
  | [], _ => .error .boundsError
  | _, [] => .error .boundsError
  | _, first :: _ =>
      let v := (List.replicate a.length 1).set 0 first
      .ok (nextprodLoop a mx x first first 0 v)

def IsFactorProduct (a : List Nat) (y : Nat) : Prop :=
  ∃ powers : List Nat, powers.length = a.length ∧
    y = ((a.zip powers).map fun q => q.1 ^ q.2).foldl (· * ·) 1

def NextprodLeast : Prop := ∀ (a : List Nat) (x : Nat),
  0 < x → (∀ factor ∈ a, 2 ≤ factor) →
  ∃ y, nextprod a x = .ok y ∧ IsFactorProduct a y ∧ x ≤ y ∧
    ∀ z, IsFactorProduct a z → x ≤ z → y ≤ z

theorem nextprodLeast_refuted : ¬ NextprodLeast := by
  intro h
  obtain ⟨y, hy, _⟩ := h [] 1 (by omega) (by simp)
  simp [nextprod] at hy

end JuliaLean.Combinatorics
