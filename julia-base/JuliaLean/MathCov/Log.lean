import JuliaLean.MathCov.Exp
import JuliaLean.MathFuncs.Log

/-!
`base/special/log.jl` at Julia master `bbfa0ce4150` for `Float32` (`log`, `log2`,
`log10`, `log1p`, the two procedures, the `logb` constants). The `Float64` methods are
`JuliaLean.MathFuncs.Log`; this file adds the `Float64` constant methods' table view.
-/

namespace JuliaLean.MathCov.Log

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathFuncs (LogBase)

/-- `logb(Float32, base)` (Float64 values); `base/special/log.jl:141-143`. -/
def logb32 : LogBase → FV .f64 | .two => logb32Two | .e => logb32E | .ten => logb32Ten

/-- `t_log_Float32[jp]` with Julia's one-based `jp`; out-of-range indices (which
`@inbounds` would not check) read `NaN`. -/
def tLog32 (jp : Int) : FV .f64 :=
  if 1 ≤ jp then (tLogFloat32[(jp - 1).toNat]?).getD (nan .f64) else nan .f64

/-- `log_proc1(y::Float32, mf, F, f, base)`; `base/special/log.jl:210-230`. -/
def logProc1 (y mf bigF f : FV .f32) (b : LogBase) : FV .f32 :=
  let jp := (unsafeTrunc .i64 (mul (lit .f32 0x43000000) bigF)).val - 127
  let hi := tLog32 jp
  let l := add (mul (conv mf : FV .f64) ln2For32) hi
  let u := div (mul (ofInt .f32 2) f) (add y bigF)
  let v := mul u u
  let q := mul (mul u v) logProc1Q32
  conv (mul (logb32 b) (add l (conv (add u q) : FV .f64)))

/-- `log_proc2(f::Float32, base)`; `base/special/log.jl:233-249`. -/
def logProc2 (f : FV .f32) (b : LogBase) : FV .f32 :=
  let u64 : FV .f64 := div (conv (mul (ofInt .f32 2) f)) (add (ofInt .f64 2) (conv f))
  let u : FV .f32 := conv u64
  let v := mul u u
  let q := mul (mul u v) (Exp.horner v logProc2Q32)
  conv (mul (logb32 b) (add u64 (conv q)))

/-- `_log(x::Float32, base, func)`; `base/special/log.jl:294-327`. -/
def log32 (x : FV .f32) (b : LogBase) : Jl (FV .f32) :=
  if lt (zero .f32) x then
    if eq x (inf .f32) then .ok x
    else if lt logLo32 x && lt x logHi32 then .ok (logProc2 (sub x (one .f32)) b)
    else
      let xu : Nat := x.toBits
      let m0 : Nat := xu / 2 ^ 23 % 256
      let (xu, m) : Nat × Int :=
        if m0 == 0 then
          let x' := mul x log2p25
          (x'.toBits, ((x'.toBits / 2 ^ 23 % 256 : Nat) : Int) - 25)
        else (xu, (m0 : Int))
      let m := m - 127
      let y : FV .f32 := Fl.ofBits (xu % 2 ^ 23 + 0x3f800000)
      let mf : FV .f32 := ofInt .f32 m
      let bigF := sub (add y logShift32) logShift32
      let f := sub y bigF
      .ok (logProc1 y mf bigF f b)
  else if eq x (zero .f32) then .ok (inf .f32 true)
  else if x.isnan then .ok (nan .f32)
  else .error (.domainError (LogBase.funcName b))

/-- `log2`, `log`, `log10` of `Float32`; `base/special/log.jl:251-253`. -/
def log2F32 (x : FV .f32) := log32 x .two
def logF32 (x : FV .f32) := log32 x .e
def log10F32 (x : FV .f32) := log32 x .ten

/-- `log1p(x::Float32)`; `base/special/log.jl:364-394`. -/
def log1pF32 (x : FV .f32) : Jl (FV .f32) :=
  if lt (neg (one .f32)) x then
    if eq x (inf .f32) then .ok x
    else if lt (neg log1pTiny32) x && lt x log1pTiny32 then .ok x
    else if lt log1pLo32 x && lt x log1pHi32 then .ok (logProc2 x .e)
    else
      let z := add (one .f32) x
      let zu := z.toBits
      let s : FV .f32 := Fl.ofBits (wrapInt .u32 (0x7f000000 - ((zu / 2 ^ 23 % 512) * 2 ^ 23 : Nat))).toNat
      let m : Int := ((zu / 2 ^ 23 % 256 : Nat) : Int) - 127
      let c := if m > 0 then sub (one .f32) (sub z x) else sub x (sub z (one .f32))
      let y : FV .f32 := Fl.ofBits (zu % 2 ^ 23 + 0x3f800000)
      let mf : FV .f32 := ofInt .f32 m
      let bigF := sub (add y logShift32) logShift32
      let f := add (sub y bigF) (mul s c)
      .ok (logProc1 y mf bigF f .e)
  else if eq x (neg (one .f32)) then .ok (inf .f32 true)
  else if x.isnan then .ok (nan .f32)
  else .error (.domainError "log1p")

end JuliaLean.MathCov.Log
