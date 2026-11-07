import JuliaLean.base.complex
import JuliaLean.base.special.exp
import JuliaLean.base.special.trig
import JuliaLean.Registry.Types

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 5000

namespace JuliaLean.Proofs.base.complex.CisImaginaryAxis

open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion (Fl)

/-- Bind the source `cis_Complex` body to its native Float64 callees.
The exponential and trigonometric pair are computed in source order, then
their actual results are supplied to the pure body for its two products.
Source: base/complex.jl:592-596; base/special/trig.jl:174-200;
base/special/exp.jl:207-231,325-332. -/
def nativeCis (z : JuliaLean.base.complex.Complex (FV .f64)) :
    Jl (JuliaLean.base.complex.Complex (FV .f64)) := do
  let scale := JuliaLean.base.special.exp.exp (T := .f64) (neg_float z.im)
  let pair ← JuliaLean.base.special.trig.sincos .f64 z.re
  return JuliaLean.base.complex.cis_Complex neg_float
    (fun _ => scale) (fun _ => pair) mul_float z

/-- On the finite imaginary axis, exp(i*z) is positive real. Its imaginary
coordinate is exactly zero even when its real coordinate overflows.
Independent promise: cis is the efficient exp(im*z) method,
base/complex.jl:573-576. -/
def ImaginaryAxisIsReal : Prop :=
  ∀ y : FV .f64, y.isfinite = true →
    ∃ w, nativeCis ⟨Fl.zero false, y⟩ = .ok w ∧ w.im.iszero = true

def input : FV .f64 := Fl.ofBits 0xc08f400000000000

theorem nativeCis_imaginary_nan :
    (nativeCis ⟨Fl.zero false, input⟩).map
      (fun w => w.im.isnan) = .ok true := by
  decide

theorem nativeCis_imaginary_not_zero :
    (nativeCis ⟨Fl.zero false, input⟩).map
      (fun w => w.im.iszero) = .ok false := by
  decide

theorem imaginaryAxisIsReal_refuted : ¬ ImaginaryAxisIsReal := by
  intro h
  obtain ⟨w, hw, hz⟩ := h input (by decide)
  have hn := nativeCis_imaginary_not_zero
  rw [hw] at hn
  have hn' : w.im.iszero = false := Except.ok.inj hn
  rw [hz] at hn'
  cases hn'

def entries : List JuliaLean.Registry.Entry :=
  [{ id := "complex-cis-spurious-nan"
     juliaFile := "base/complex.jl"
     juliaFns := ["cis(::Complex)"]
     statement := "For every finite imaginary-axis input, cis returns a zero imaginary coordinate, including when its real coordinate overflows."
     source := "base/complex.jl:573-576,592-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027"
     status := .refuted
     prop := ``ImaginaryAxisIsReal
     thm := some ``imaginaryAxisIsReal_refuted
     issue := "none found (queries: cis NaN overflow; cis overflow; cis NaN)" }]
