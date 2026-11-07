import JuliaLean.base.parse
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.parse.complex_imaginary_minimum

open JuliaLean JuliaLean.ParsePrint.IntParse
open JuliaLean.DocsSyntaxCov.Parse

/-- The fixed Int8 operations used by Complex{Int8}; the component parser is the
installed Base integer parser, rather than an assumed parser callback. -/
def int8Ops : JuliaLean.DocsSyntaxCov.Parse.FloatOps (JInt .i8) :=
  ⟨JInt.wrap .i8 0, JuliaLean.base.int.neg⟩

def parseComponent (s : Bytes) (raise : Bool) : Jl (Option (JInt .i8)) :=
  tryparseInternalInt10 .i8 s 1 (lastindex s) raise

def parseComplex (s : Bytes) : Jl (Option (JInt .i8 × JInt .i8)) :=
  tryparseComplexStr int8Ops (tryparseInternalInt10 .i8) s false

/-- Nonempty decimal digits, with no whitespace, radix prefix, or additional sign. -/
def DecimalMagnitude (s : Bytes) : Prop :=
  s ≠ [] ∧ ∀ b ∈ s, 48 ≤ b.val ∧ b.val ≤ 57

/-- parse's docstring, base/parse.jl:10-12: decimal R-Iim denotes Complex(R,-I).
If both signed components fit Int8, adding the real component must not cause
an otherwise representable negative imaginary component to be rejected. -/
def DecimalComponentsAccepted : Prop :=
  ∀ (real magnitude : Bytes) (re im : JInt .i8),
    DecimalMagnitude real → DecimalMagnitude magnitude →
    parseComponent real false = .ok (some re) →
    parseComponent (byte 45 :: magnitude) false = .ok (some im) →
    parseComplex (real ++ [byte 45] ++ magnitude ++ [byte 105, byte 109]) =
      .ok (some (re, im))

def zeroText : Bytes := [byte 48]
def minimumMagnitude : Bytes := [byte 49, byte 50, byte 56]

theorem scalar_minimum_accepted :
    parseComponent (byte 45 :: minimumMagnitude) false =
      .ok (some (JInt.wrap .i8 (-128))) := by decide +kernel

theorem pure_imaginary_minimum_accepted :
    parseComplex ((byte 45 :: minimumMagnitude) ++ [byte 105, byte 109]) =
      .ok (some (JInt.wrap .i8 0, JInt.wrap .i8 (-128))) := by decide +kernel

theorem complex_minimum_rejected :
    parseComplex (zeroText ++ [byte 45] ++ minimumMagnitude ++ [byte 105, byte 109]) =
      .ok none := by decide +kernel

theorem decimalComponentsAccepted_refuted : ¬ DecimalComponentsAccepted := by
  intro h
  have hz : DecimalMagnitude zeroText := by
    constructor
    · decide +kernel
    · intro b hb
      simp only [zeroText, List.mem_singleton] at hb
      subst b
      decide +kernel
  have hm : DecimalMagnitude minimumMagnitude := by
    constructor
    · decide +kernel
    · intro b hb
      simp [minimumMagnitude] at hb
      rcases hb with rfl | rfl | rfl <;> decide +kernel
  have hp : parseComponent zeroText false = .ok (some (JInt.wrap .i8 0)) := by decide +kernel
  have bad := h zeroText minimumMagnitude (JInt.wrap .i8 0) (JInt.wrap .i8 (-128))
    hz hm hp scalar_minimum_accepted
  rw [complex_minimum_rejected] at bad
  cases bad

def entries : List JuliaLean.Registry.Entry := [
  { id := "parse-complex-imaginary-typemin"
    juliaFile := "base/parse.jl"
    juliaFns := ["parse(::Type{Complex{T}}, ::AbstractString)", "tryparse(::Type{Complex{T}}, ::AbstractString)"]
    statement := "Decimal complex strings are accepted when their real and signed imaginary components are representable."
    source := "base/parse.jl:10-12,284-339,370-374"
    status := .refuted
    prop := ``DecimalComponentsAccepted
    thm := some ``decimalComponentsAccepted_refuted
    issue := "none found; searches: parse Complex Int8 typemin imaginary; parse Complex -128"
    notes := "0-128im is rejected for Complex{Int8}, although -128 parses as Int8 and -128im parses as Complex{Int8}." }
]

end JuliaLean.Proofs.base.parse.complex_imaginary_minimum
