import JuliaLean.Registry.Types
import JuliaLean.base.special.cbrt
import JuliaLean.base.floatfuncs

/-!
Unproved candidates over the source-mirrored cbrt entry points. No generic
AbstractFloat callback is instantiated or assumed correct. The accompanying TSV
records the complete numerical contracts still blocked by missing source bindings.
-/

namespace JuliaLean.Proofs.base.special.cbrt

open JuliaLean JuliaLean.Promotion

/-- Format-tag adapter to the existing source `isnan` model. -/
def sourceIsNaN : (T : FTy) → FV T → Bool
  | .f16, x => JuliaLean.base.float.isnan_IEEEFloat (T := .f16) x
  | .f32, x => JuliaLean.base.float.isnan_IEEEFloat (T := .f32) x
  | .f64, x => JuliaLean.base.float.isnan_IEEEFloat (T := .f64) x

/-- Format-tag adapter to the existing source `isinf` model. -/
def sourceIsInf : (T : FTy) → FV T → Bool
  | .f16, x => JuliaLean.base.float.isinf_IEEEFloat (T := .f16) x
  | .f32, x => JuliaLean.base.float.isinf_IEEEFloat (T := .f32) x
  | .f64, x => JuliaLean.base.float.isinf_IEEEFloat (T := .f64) x

/-- Format-tag adapter to the existing source `isfinite` model. -/
def sourceIsFinite : (T : FTy) → FV T → Bool
  | .f16, x => JuliaLean.base.float.isfinite_IEEEFloat (T := .f16) x
  | .f32, x => JuliaLean.base.float.isfinite_IEEEFloat (T := .f32) x
  | .f64, x => JuliaLean.base.float.isfinite_IEEEFloat (T := .f64) x

/-- Bound source float equality with zero, not a supplied classifier. -/
def sourceIsZero : (T : FTy) → FV T → Bool
  | .f16, x => JuliaLean.base.float.iszero_float (T := .f16) x
  | .f32, x => JuliaLean.base.float.iszero_float (T := .f32) x
  | .f64, x => JuliaLean.base.float.iszero_float (T := .f64) x

/-- Format-tag adapter to source signbit, including signed zeros. -/
def sourceSignbit : (T : FTy) → FV T → Bool
  | .f16, x => JuliaLean.base.floatfuncs.signbit_Float16 x
  | .f32, x => JuliaLean.base.floatfuncs.signbit_Float32 x
  | .f64, x => JuliaLean.base.floatfuncs.signbit_Float64 x

/-- Independent real-root class/sign postcondition, not a Julia function copy. -/
def RootClassAndSign (T : FTy) (x y : FV T) : Prop :=
  if sourceIsNaN T x then sourceIsNaN T y = true
  else if sourceIsInf T x then y = x
  else if sourceIsZero T x then y = x
  else sourceIsFinite T y = true ∧ sourceIsZero T y = false ∧
    sourceSignbit T y = sourceSignbit T x

end JuliaLean.Proofs.base.special.cbrt

namespace JuliaLean.Proofs.base.special.cbrtArchive20261101

open JuliaLean.Proofs.base.special.cbrt
open JuliaLean JuliaLean.Promotion

/-- Cbrt returns a finite nonzero root of the input's sign on every finite nonzero IEEE input, preserves both signed zeros and infinities, and returns NaN on every NaN.
Julia source: base/special/cbrt.jl:144-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/special/cbrt.jl:17-24 (real cube root and negative-root acceptance); doc/src/base/math.md:252-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CbrtIEEEClassAndSign : Prop :=
  (∀ x : FV .f32,
    match JuliaLean.base.special.cbrt.cbrt (.f32 x) with
    | .f32 y => RootClassAndSign .f32 x y
    | .f64 _ => False) ∧
  (∀ x : FV .f64,
    match JuliaLean.base.special.cbrt.cbrt (.f64 x) with
    | .f64 y => RootClassAndSign .f64 x y
    | .f32 _ => False) ∧
  (∀ x : FV .f16,
    RootClassAndSign .f16 x (JuliaLean.base.special.cbrt.cbrt16 x))

end JuliaLean.Proofs.base.special.cbrtArchive20261101

namespace JuliaLean.Proofs.base.special.cbrt

open JuliaLean.Registry

def entries : List Entry := [
  { id := "mathfuncs-cbrt-special-v2", juliaFile := "base/special/cbrt.jl",
    juliaFns := ["cbrt"],
    statement := "For every Float16, Float32, and Float64 input, cbrt preserves the format, returns a finite nonzero result of the input sign on finite nonzero inputs, preserves signed zeros and infinities, and propagates NaN.",
    source := "base/special/cbrt.jl:17-24,144-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.special.cbrtArchive20261101.CbrtIEEEClassAndSign, thm := none,
    notes := "No complete exact target proof was returned. Exceptional classes and initial normal approximations do not prove finite nonzero class/sign preservation through every cbrt32/cbrt64 numerical branch or the finite cbrt16 conversion." }
]

end JuliaLean.Proofs.base.special.cbrt

namespace JuliaLean.ChatGPT.Batch4.Group23
open JuliaLean JuliaLean.Promotion JuliaLean.MathCov
open JuliaLean.Proofs.base.special.cbrt

/-- The source NaN predicate agrees with the raw IEEE classification in all three formats. -/
theorem cbrt_sourceIsNaN_eq (T : FTy) (x : FV T) :
    sourceIsNaN T x = x.isnan := by
  cases T <;>
    simp [sourceIsNaN, JuliaLean.base.float.isnan_IEEEFloat,
      JuliaLean.base.float.isnan_AbstractFloat, JuliaLean.base.float.eq_IEEEFloat,
      JuliaLean.base.float.eq_float, JuliaLean.C.jlEqFloat,
      Fl.eq] <;> rfl

/-- Every NaN takes the early return, independent of its payload or sign. -/
theorem cbrt_nan_not_finite {f : Fmt} (x : Fl f) (h : x.isnan = true) :
    x.isfinite = false := by
  simp only [Fl.isnan, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  simp only [Fl.isfinite, h.1, bne_self_eq_false]

/-- Format preservation for every binary32 input, including the numerical branch. -/
theorem cbrt_format32 (x : FV .f32) :
    ∃ y, JuliaLean.base.special.cbrt.cbrt (.f32 x) = .f32 y := by
  simp only [JuliaLean.base.special.cbrt.cbrt]
  split <;> exact ⟨_, rfl⟩

/-- Format preservation for every binary64 input, including the numerical branch. -/
theorem cbrt_format64 (x : FV .f64) :
    ∃ y, JuliaLean.base.special.cbrt.cbrt (.f64 x) = .f64 y := by
  simp only [JuliaLean.base.special.cbrt.cbrt]
  split <;> exact ⟨_, rfl⟩

theorem cbrt_nonfinite32 (x : FV .f32) (h : x.isfinite = false) :
    JuliaLean.base.special.cbrt.cbrt (.f32 x) = .f32 x := by
  simp only [JuliaLean.base.special.cbrt.cbrt, FP.isfinite, h,
    Bool.not_false, Bool.true_or, ite_true]

theorem cbrt_nonfinite64 (x : FV .f64) (h : x.isfinite = false) :
    JuliaLean.base.special.cbrt.cbrt (.f64 x) = .f64 x := by
  simp only [JuliaLean.base.special.cbrt.cbrt, FP.isfinite, h,
    Bool.not_false, Bool.true_or, ite_true]

theorem cbrt_nonfinite16 (x : FV .f16) (h : x.isfinite = false) :
    JuliaLean.base.special.cbrt.cbrt16 x = x := by
  simp only [JuliaLean.base.special.cbrt.cbrt16, FP.isfinite, h,
    Bool.not_false, Bool.true_or, ite_true]

/-- The full frozen class/sign postcondition holds for every binary32 NaN. -/
theorem cbrt_nan32 (x : FV .f32) (h : sourceIsNaN .f32 x = true) :
    match JuliaLean.base.special.cbrt.cbrt (.f32 x) with
    | .f32 y => RootClassAndSign .f32 x y
    | .f64 _ => False := by
  have hn : x.isnan = true := (cbrt_sourceIsNaN_eq .f32 x).symm.trans h
  rw [cbrt_nonfinite32 x (cbrt_nan_not_finite x hn)]
  simp only [RootClassAndSign, h, ite_true]

/-- The full frozen class/sign postcondition holds for every binary64 NaN. -/
theorem cbrt_nan64 (x : FV .f64) (h : sourceIsNaN .f64 x = true) :
    match JuliaLean.base.special.cbrt.cbrt (.f64 x) with
    | .f64 y => RootClassAndSign .f64 x y
    | .f32 _ => False := by
  have hn : x.isnan = true := (cbrt_sourceIsNaN_eq .f64 x).symm.trans h
  rw [cbrt_nonfinite64 x (cbrt_nan_not_finite x hn)]
  simp only [RootClassAndSign, h, ite_true]

/-- The full frozen class/sign postcondition holds for every binary16 NaN. -/
theorem cbrt_nan16 (x : FV .f16) (h : sourceIsNaN .f16 x = true) :
    RootClassAndSign .f16 x (JuliaLean.base.special.cbrt.cbrt16 x) := by
  have hn : x.isnan = true := (cbrt_sourceIsNaN_eq .f16 x).symm.trans h
  rw [cbrt_nonfinite16 x (cbrt_nan_not_finite x hn)]
  simp only [RootClassAndSign, h, ite_true]

/-- Both signed zeros satisfy the frozen contract in binary32. -/
theorem cbrt_signedZero32 (s : Bool) :
    match JuliaLean.base.special.cbrt.cbrt (.f32 (Fl.zero s)) with
    | .f32 y => RootClassAndSign .f32 (Fl.zero s) y
    | .f64 _ => False := by
  cases s <;> rfl

/-- Both signed zeros satisfy the frozen contract in binary64. -/
theorem cbrt_signedZero64 (s : Bool) :
    match JuliaLean.base.special.cbrt.cbrt (.f64 (Fl.zero s)) with
    | .f64 y => RootClassAndSign .f64 (Fl.zero s) y
    | .f32 _ => False := by
  cases s <;> rfl

/-- Both signed zeros satisfy the frozen contract in binary16. -/
theorem cbrt_signedZero16 (s : Bool) :
    RootClassAndSign .f16 (Fl.zero s) (JuliaLean.base.special.cbrt.cbrt16 (Fl.zero s)) := by
  cases s <;> rfl

/-- Both signed infinities satisfy the frozen contract in binary32. -/
theorem cbrt_signedInf32 (s : Bool) :
    match JuliaLean.base.special.cbrt.cbrt (.f32 (Fl.inf s)) with
    | .f32 y => RootClassAndSign .f32 (Fl.inf s) y
    | .f64 _ => False := by
  cases s <;> rfl

/-- Both signed infinities satisfy the frozen contract in binary64. -/
theorem cbrt_signedInf64 (s : Bool) :
    match JuliaLean.base.special.cbrt.cbrt (.f64 (Fl.inf s)) with
    | .f64 y => RootClassAndSign .f64 (Fl.inf s) y
    | .f32 _ => False := by
  cases s <;> rfl

/-- Both signed infinities satisfy the frozen contract in binary16. -/
theorem cbrt_signedInf16 (s : Bool) :
    RootClassAndSign .f16 (Fl.inf s) (JuliaLean.base.special.cbrt.cbrt16 (Fl.inf s)) := by
  cases s <;> rfl

end JuliaLean.ChatGPT.Batch4.Group23
