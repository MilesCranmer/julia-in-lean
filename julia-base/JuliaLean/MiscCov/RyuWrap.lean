import JuliaLean.MiscCov.RyuUtils

/-! Wrapper methods from `base/ryu/Ryu.jl` (master `bbfa0ce4150`). -/

namespace JuliaLean.MiscCov.RyuWrap

open JuliaLean.MiscCov
open JuliaLean.MiscCov.RyuUtils

/-- `neededdigits`, `base/ryu/Ryu.jl:16-18`. -/
def neededdigits : FT → Nat | .f64 => 309 + 17 | .f32 => 39 + 9 + 2 | .f16 => 9 + 5 + 9

/-- `neededfloatdigits`, `base/ryu/Ryu.jl:25-27`. -/
def neededfloatdigits : FT → Nat | .f64 => 24 | .f32 => 17 | .f16 => 20

structure ShortOpts where
  plus : Bool := false
  space : Bool := false
  hash : Bool := true
  expchar : Nat := 0x65
  padexp : Bool := false
  decchar : Nat := 0x2e
  typed : Bool := false
  compact : Bool := false
  deriving DecidableEq, Repr

structure FixedOpts where
  plus : Bool := false
  space : Bool := false
  hash : Bool := false
  expchar : Nat := 0x65
  decchar : Nat := 0x2e
  trim : Bool := false
  deriving DecidableEq, Repr

/-- A lower-level Ryu writer. It receives the allocated buffer size and returns
the buffer and Julia's one-past-the-end position. -/
abbrev Writer (X O : Type) := Nat → X → Int → O → List Nat × Nat

private def finish (r : List Nat × Nat) : List Nat := r.1.take (r.2 - 1)

/-- `writeshortest(x, ...)`, `base/ryu/Ryu.jl:48-64`. -/
def writeshortest {X : Type} (write : Writer X ShortOpts) (ft : FT) (x : X)
    (precision : Int) (opts : ShortOpts := {}) : M (List Nat) :=
  if precision < -1 then .error (.argumentError "precision must be at least -1")
  else
    let size := if precision < 0 then neededdigits ft else precision.toNat + neededdigits ft
    .ok (finish (write size x precision opts))

/-- `writefixed(x, ...)`, `base/ryu/Ryu.jl:82-94`. -/
def writefixed {X : Type} (write : Writer X FixedOpts) (ft : FT) (x : X)
    (precision : Int) (opts : FixedOpts := {}) : M (List Nat) :=
  if precision < 0 then .error (.argumentError "precision must be non-negative")
  else .ok (finish (write (precision.toNat + neededdigits ft) x precision opts))

/-- `writeexp(x, ...)`, `base/ryu/Ryu.jl:113-126`. -/
def writeexp {X : Type} (write : Writer X FixedOpts) (ft : FT) (x : X)
    (precision : Int) (opts : FixedOpts := {}) : M (List Nat) :=
  if precision < 0 then .error (.argumentError "precision must be non-negative")
  else .ok (finish (write (precision.toNat + neededdigits ft) x precision opts))

/-- `Base.show(io, x, forceuntyped, fromprint)`, `base/ryu/Ryu.jl:128-136`.
The result is the bytes written to `io`. -/
def showFloat {X : Type} (write : Writer X ShortOpts) (ft : FT) (x : X)
    (compact forceuntyped fromprint typeinfoSame isF32 : Bool) : List Nat :=
  let typed := !forceuntyped && !compact && !typeinfoSame
  let expchar := if isF32 && !fromprint then 0x66 else 0x65
  finish (write (neededfloatdigits ft) x (-1)
    { hash := true, expchar := expchar, typed := typed, compact := compact })

/-- `Base.string(x)`, `base/ryu/Ryu.jl:138-143`. -/
def stringFloat {X : Type} (write : Writer X ShortOpts) (ft : FT) (x : X) : List Nat :=
  finish (write (neededfloatdigits ft) x (-1) {})

/-- `Base.print(io, x::Union{Float16,Float32})`, `base/ryu/Ryu.jl:145`. -/
def printFloat {X : Type} (write : Writer X ShortOpts) (ft : FT) (x : X)
    (compact typeinfoSame isF32 : Bool) : List Nat :=
  showFloat write ft x compact true true typeinfoSame isF32

def DigitCounts : Prop := ∀ ft : FT,
  neededdigits ft = (match ft with | .f64 => 326 | .f32 => 50 | .f16 => 23) ∧
  neededfloatdigits ft = (match ft with | .f64 => 24 | .f32 => 17 | .f16 => 20)

theorem digitCounts_proven : DigitCounts := by
  intro ft
  cases ft <;> decide

def WrapperContract : Prop :=
  (∀ (X : Type) (write : Writer X ShortOpts) ft x opts,
    writeshortest write ft x (-2) opts = .error (.argumentError "precision must be at least -1")) ∧
  (∀ (X : Type) (write : Writer X ShortOpts) ft x opts p, ¬ p < -1 →
    writeshortest write ft x p opts = .ok (finish (write
      (if p < 0 then neededdigits ft else p.toNat + neededdigits ft) x p opts))) ∧
  (∀ (X : Type) (write : Writer X FixedOpts) ft x opts p, p < 0 →
    writefixed write ft x p opts = .error (.argumentError "precision must be non-negative")) ∧
  (∀ (X : Type) (write : Writer X FixedOpts) ft x opts p, ¬ p < 0 →
    writefixed write ft x p opts = .ok (finish (write (p.toNat + neededdigits ft) x p opts))) ∧
  (∀ (X : Type) (write : Writer X FixedOpts) ft x opts p, p < 0 →
    writeexp write ft x p opts = .error (.argumentError "precision must be non-negative")) ∧
  (∀ (X : Type) (write : Writer X FixedOpts) ft x opts p, ¬ p < 0 →
    writeexp write ft x p opts = .ok (finish (write (p.toNat + neededdigits ft) x p opts))) ∧
  (∀ (X : Type) (write : Writer X ShortOpts) ft x compact force fromprint same isF32,
    showFloat write ft x compact force fromprint same isF32 =
      finish (write (neededfloatdigits ft) x (-1)
        { hash := true, expchar := if isF32 && !fromprint then 0x66 else 0x65,
          typed := !force && !compact && !same, compact := compact })) ∧
  (∀ (X : Type) (write : Writer X ShortOpts) ft x,
    stringFloat write ft x = finish (write (neededfloatdigits ft) x (-1) {})) ∧
  (∀ (X : Type) (write : Writer X ShortOpts) ft x compact same isF32,
    printFloat write ft x compact same isF32 = showFloat write ft x compact true true same isF32)

theorem wrapperContract_proven : WrapperContract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ _ _ _ _ => rfl⟩
  · intro X write ft x opts
    rfl
  · intro X write ft x opts p hp
    simp [writeshortest, hp]
  · intro X write ft x opts p hp
    simp [writefixed, hp]
  · intro X write ft x opts p hp
    simp [writefixed, hp]
  · intro X write ft x opts p hp
    simp [writeexp, hp]
  · intro X write ft x opts p hp
    simp [writeexp, hp]
  · intro X write ft x compact force fromprint same isF32
    rfl
  · intro X write ft x
    rfl

end JuliaLean.MiscCov.RyuWrap
