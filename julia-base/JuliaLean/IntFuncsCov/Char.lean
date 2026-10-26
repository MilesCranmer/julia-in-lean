import JuliaLean.MissingChar.Char
import JuliaLean.MissingChar.CharProofs
import JuliaLean.HashOps.Model

/-!
Coverage models for `base/char.jl` at master `bbfa0ce4150`. A Julia `Char` is
represented by its `UInt32` storage bits, matching `JuliaLean.MissingChar`.
-/

namespace JuliaLean.IntFuncsCov.Char

open JuliaLean
open JuliaLean.MissingChar
open JuliaLean.Strings

def sgetD {ε α : Type} (x : Except ε α) (d : α) : α :=
  match x with
  | .ok a => a
  | .error _ => d

/-! ## Construction, decoding, and conversion, lines 54-239 -/

def int8OfChar (signed : Bool) (c : UInt32) : Jl Int :=
  let i := c.toInt32
  if 0 ≤ i then
    let byte := (c >>> 24).toUInt8.toNat
    if signed then .ok (UInt8.ofNat byte).toInt8.toInt else .ok byte
  else match Strings.codepoint c with
    | .error _ => .error (.argumentError "invalid character")
    | .ok u =>
      if signed then JInt.convert .i8 u.toNat |>.map Subtype.val
      else JInt.convert .u8 u.toNat |>.map Subtype.val

def CharEncodingBehavior : Prop :=
  MissingChar.CharCodepointRoundTrip ∧ MissingChar.CodepointWellFormed ∧
  (∀ c : UInt32, MissingChar.unsafeCodepoint c =
    if c < 0x80000000 then c >>> 24
    else
      let l1 := Strings.clo32 c
      let t0 := Strings.land56 (Strings.ctz32 c)
      let u := c &&& Strings.ushr32 0xffffffff l1
      let u := Strings.ushr32 u t0
      ((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
        ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6)) ∧
  (∀ c : UInt32, Strings.ismalformed c = false → ∃ u, Strings.codepoint c = .ok u)

theorem charEncodingBehavior : CharEncodingBehavior := by
  refine ⟨MissingChar.charCodepointRoundTrip_proven, MissingChar.codepointWellFormed_proven,
    fun _ => rfl, ?_⟩
  exact MissingChar.codepointWellFormed_proven

/-! ## Scalar collection interface and comparisons, lines 241-300 -/

def charSizeDim (d : Int) : Jl Nat := if d < 1 then .error .boundsError else .ok 1

def charGet (c : UInt32) (indices : List Int) : Jl UInt32 :=
  if indices.all (· = 1) then .ok c else .error .boundsError

def charIter (c : UInt32) (done : Bool) : Option (UInt32 × Bool) :=
  if done then none else some (c, true)

def charSub (x y : UInt32) : Strings.SJl Int := do
  let a ← Strings.codepoint x
  let b ← Strings.codepoint y
  pure ((a.toNat : Int) - b.toNat)

def CharScalarBehavior : Prop :=
  (∀ (c : UInt32) (d : Int), charSizeDim d = if d < 1 then .error .boundsError else .ok 1) ∧
  (∀ (c : UInt32) (is : List Int), charGet c is =
    if is.all (· = 1) then .ok c else .error .boundsError) ∧
  (∀ (c : UInt32) (done : Bool), charIter c done = if done then none else some (c, true)) ∧
  (∀ (x y : UInt32), decide (x = y) = decide (x.toNat = y.toNat)) ∧
  (∀ (x y : UInt32), decide (x < y) = decide (x.toNat < y.toNat)) ∧
  MissingChar.CharAddCodepoint

theorem charScalarBehavior : CharScalarBehavior := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_,
    MissingChar.charAddCodepoint_proven⟩
  · intro x y
    simp only [decide_eq_decide, UInt32.toNat_inj]
  · intro x y
    simp only [decide_eq_decide, UInt32.lt_iff_toNat_lt]

/-! ## Printing, lines 305-392 -/

structure PlainDisplay where
  literal : List UInt8
  malformed : Bool
  overlong : Bool
  codepoint : Option UInt32
  compact : Bool
  deriving DecidableEq

def plainDisplay (literal : List UInt8) (c : UInt32) (compact : Bool) : PlainDisplay :=
  { literal := literal
    malformed := Strings.ismalformed c
    overlong := Strings.isoverlong c
    codepoint := if Strings.ismalformed c then none else (Strings.codepoint c).toOption
    compact := compact }

def CharDisplayBehavior : Prop :=
  MissingChar.NcodeunitsWrite ∧
  (∀ c : UInt32, MissingChar.showInvalid c =
    [0x27] ++ MissingChar.showInvalidLoop 4 c ++ [0x27]) ∧
  (∀ (literal : List UInt8) (c : UInt32) (compact : Bool),
    plainDisplay literal c compact =
      { literal := literal
        malformed := Strings.ismalformed c
        overlong := Strings.isoverlong c
        codepoint := if Strings.ismalformed c then none else (Strings.codepoint c).toOption
        compact := compact })

set_option maxRecDepth 100000 in
theorem charDisplayBehavior : CharDisplayBehavior := by
  refine ⟨MissingChar.ncodeunitsWrite_proven, fun _ => rfl, ?_⟩
  intro literal c compact
  rfl

end JuliaLean.IntFuncsCov.Char
