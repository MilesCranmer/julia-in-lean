import JuliaLean.base.char
import JuliaLean.Proofs.base.char.contracts
import JuliaLean.Proofs.base.char.encoding
import JuliaLean.base.hashing
/-!
Coverage models for `base/char.jl` at master `bbfa0ce4150`. A Julia `Char` is
represented by its `UInt32` storage bits, matching `JuliaLean.MissingChar`.
-/

namespace JuliaLean.IntFuncsCov.Char

open JuliaLean
open JuliaLean.MissingChar
open JuliaLean.Strings

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
