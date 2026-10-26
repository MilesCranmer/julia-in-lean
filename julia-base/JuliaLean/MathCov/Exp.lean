import JuliaLean.MathCov.Consts
import JuliaLean.MathFuncs.Exp

/-!
`base/special/exp.jl` at Julia master `bbfa0ce4150` for `Float32` and `Float16`, plus
the per-type constant methods; the `Float64` methods are `JuliaLean.MathFuncs.Exp`.
Also `exthorner`/`_exthorner` (`base/math.jl:196-210`) for both types.
-/

namespace JuliaLean.MathCov.Exp

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathFuncs (ExpBase)

/-- `evalpoly(x, p)` for a coefficient tuple: Horner with `muladd`; `base/math.jl:75-86`. -/
def horner {T : FTy} (x : FV T) : List (FV T) → FV T
  | [] => zero T
  | [c] => c
  | c :: cs => muladd x (horner x cs) c

/-- `MAX_EXP(base, Float32)`; `base/special/exp.jl:11-16`. -/
def maxExp32 : ExpBase → FV .f32 | .two => maxExp32Two | .e => maxExp32E | .ten => maxExp32Ten
/-- `MIN_EXP(base, Float32)`; `base/special/exp.jl:19-24`. -/
def minExp32 : ExpBase → FV .f32 | .two => minExp32Two | .e => minExp32E | .ten => minExp32Ten
/-- `SUBNORM_EXP(base, Float32)`; `base/special/exp.jl:28-33`. -/
def subnormExp32 : ExpBase → FV .f32
  | .two => subnormExp32Two | .e => subnormExp32E | .ten => subnormExp32Ten
/-- `LogBINV(base, Float32)`; `base/special/exp.jl:52-54`. -/
def logBInv32 : ExpBase → FV .f32 | .two => logBInv32Two | .e => logBInv32E | .ten => logBInv32Ten
/-- `LogBU(base, Float32)`; `base/special/exp.jl:60-62`. -/
def logBU32 : ExpBase → FV .f32 | .two => logBU32Two | .e => logBU32E | .ten => logBU32Ten
/-- `LogBL(base, Float32)`; `base/special/exp.jl:63-65`. -/
def logBL32 : ExpBase → FV .f32 | .two => logBL32Two | .e => logBL32E | .ten => logBL32Ten
/-- `LogB(base, Float16)` (Float32 values); `base/special/exp.jl:68-70`. -/
def logB16 : ExpBase → FV .f32 | .two => logB16Two | .e => logB16E | .ten => logB16Ten

/-- `expb_kernel(base, x::Float32)`; `base/special/exp.jl:86-100`. -/
def expbKernel : ExpBase → FV .f32 → FV .f32
  | .two, x => horner x expbKernel32Two
  | .e, x => horner x expbKernel32E
  | .ten, x => horner x expbKernel32Ten

/-- `reinterpret(Float32, p << Int32(23))` for an `Int32` `p` (the shift wraps in Int32). -/
def pow2Bits32 (p : Int) : FV .f32 := Fl.ofBits (wrapInt .u32 (wrapInt .i32 (p * 2 ^ 23))).toNat

/-- `exp_impl(x::Float32, base)`; `base/special/exp.jl:276-295`. -/
def expImpl32 (x : FV .f32) (b : ExpBase) : FV .f32 :=
  let nFloat := roundI (mul x (logBInv32 b))
  let n := (unsafeTrunc .i32 nFloat).val
  let r := muladd nFloat (logBU32 b) x
  let r := muladd nFloat (logBL32 b) r
  let smallPart := expbKernel b r
  let power := wrapInt .i32 (n + 127)
  if lt (maxExp32 b) x then inf .f32
  else if lt x (minExp32 b) then zero .f32
  else
    let (power, smallPart) :=
      if le x (neg (subnormExp32 b)) then (wrapInt .i32 (power + 24), mul smallPart (lit .f32 0x33800000))
      else (power, smallPart)
    let (power, smallPart) :=
      if n == 128 then (wrapInt .i32 (power - 1), mul smallPart (ofInt .f32 2)) else (power, smallPart)
    mul smallPart (pow2Bits32 power)

/-- `exp_impl_fast(x::Float32, base)`; `base/special/exp.jl:297-308`. -/
def expImplFast32 (x : FV .f32) (b : ExpBase) : FV .f32 :=
  if le (maxExp32 b) x then inf .f32
  else if le x (neg (subnormExp32 b)) then zero .f32
  else
    let nFloat := roundI (mul x (logBInv32 b))
    let n := (unsafeTrunc .i32 nFloat).val
    let r := muladd nFloat (logBU32 b) x
    let r := muladd nFloat (logBL32 b) r
    let smallPart := expbKernel b r
    mul (pow2Bits32 (wrapInt .i32 (n + 127))) smallPart

/-- `exp_impl(a::Float16, base)`; `base/special/exp.jl:310-323`. -/
def expImpl16 (a : FV .f16) (b : ExpBase) : FV .f16 :=
  let x : FV .f32 := conv a
  let nFloat := roundI (mul x (logBInv32 b))
  let n := (unsafeTrunc .i32 nFloat).val
  let r := muladd nFloat (logB16 b) x
  let smallPart := expbKernel b r
  let early : Option (FV .f16) :=
    if !(le (abs x) (ofInt .f32 25)) then
      if lt (ofInt .f32 16) x then some (inf .f16)
      else if lt x (ofInt .f32 25) then some (zero .f16)
      else none
    else none
  match early with
  | some v => v
  | none => conv (mul (pow2Bits32 (wrapInt .i32 (n + 127))) smallPart)

/-- `exp2`, `exp`, `exp10` of `Float16`, `Float32`, `Float64` call `exp_impl(x, base)`;
`base/special/exp.jl:325-332`. -/
def expFn (b : ExpBase) : (T : FTy) → FV T → FV T
  | .f16, x => expImpl16 x b
  | .f32, x => expImpl32 x b
  | .f64, x => Fl.ofF64 (MathFuncs.expImpl (Fl.toF64 x) b)

/-- `exp2_fast` and friends for `Float32`; the `Float64` method is `exp_impl_fast(x::Float64)`
(`base/special/exp.jl:260-274`). -/
def expImplFast64 (x : F64) (b : ExpBase) : F64 :=
  if F64.le (MathFuncs.maxExp b) x then F64.inf
  else if F64.le x (F64.neg (MathFuncs.subnormExp b)) then F64.zero
  else
    let (n, r) := MathFuncs.expReduce x b
    let k := n.fdiv 256
    let (jU, _) := MathFuncs.tableUnpack n
    let smallPart := F64.muladd jU (MathFuncs.expm1bKernel b r) jU
    MathFuncs.ofInt64 (k * 2^52 + MathFuncs.toInt64 smallPart)

/-- `two_mul(x, y)` with hardware fma for `Float32`/`Float16`; `base/floatfuncs.jl:390-394`. -/
def twoMulG {T : FTy} (x y : FV T) : FV T × FV T :=
  let xy := mul x y
  (xy, fma x y (neg xy))

/-- `_exthorner(i, x, p, hi, lo)` with `pi = p[i]`, after the index check
`i == 2 || i == 1 || error(...)`; `base/math.jl:203-210`. -/
def exthornerStep {T : FTy} (i : Nat) (x : FV T) (p : FV T × FV T × FV T) (hi lo : FV T) :
    Jl (FV T × FV T) :=
  if !(i == 2 || i == 1) then .error (.argumentError "unexpected index")
  else
    let pi := if i == 1 then p.1 else p.2.1
    let (prod, err) := twoMulG hi x
    let hi' := add pi prod
    .ok (hi', fma lo x (add (sub prod (sub hi' pi)) err))

/-- `exthorner(x, p::Tuple{T,T,T})`; `base/math.jl:196-201`. -/
def exthorner {T : FTy} (x : FV T) (p : FV T × FV T × FV T) : Jl (FV T × FV T) := do
  let (hi, lo) ← exthornerStep 2 x p p.2.2 (zero T)
  exthornerStep 1 x p hi lo

/-- `expm1_small(x::Float32)`; `base/special/exp.jl:426-431`. -/
def expm1Small32 (x : FV .f32) : FV .f32 :=
  let p := horner x expm1SmallP32
  match exthorner x (one .f32, lit .f32 0x3f000000, p) with
  | .ok (h, l) => fma x h (mul x l)
  | .error _ => nan .f32

/-- `expm1(x::Float32)`; `base/special/exp.jl:459-474`. -/
def expm1F32 (x : FV .f32) : FV .f32 :=
  if lt expm1Max32 x then inf .f32
  else if lt x expm1Min32 then neg (one .f32)
  else if le expm1Lo32 x && le x expm1Hi32 then expm1Small32 x
  else
    let xd : FV .f64 := conv x
    let nFloat := roundI (mul xd ln2Inv64)
    let n := (unsafeTrunc .i64 nFloat).val
    let r := muladd nFloat ln2Neg64 xd
    let hi := horner r expm1Poly64For32
    let smallPart := mul r hi
    let twopk : FV .f64 := Fl.ofBits (wrapInt .u64 (wrapInt .i64 ((n + 1023) * 2 ^ 52))).toNat
    conv (muladd twopk smallPart (sub twopk (one .f64)))

/-- `expm1(x::Float16)`; `base/special/exp.jl:476-490`. -/
def expm1F16 (a : FV .f16) : FV .f16 :=
  if lt expm1Max16 a then inf .f16
  else if lt a expm1Min16 then neg (one .f16)
  else
    let x : FV .f32 := conv a
    if le expm1Lo32 x && le x expm1Hi32 then conv (mul x (horner x expm1SmallPoly16))
    else
      let nFloat := roundI (mul x ln2Inv32)
      let n := (unsafeTrunc .i32 nFloat).val
      let r := muladd nFloat ln2Neg32 x
      let hi := horner r expm1Poly16
      let smallPart := mul r hi
      let twopk := pow2Bits32 (wrapInt .i32 (n + 127))
      conv (muladd twopk smallPart (sub twopk (one .f32)))

end JuliaLean.MathCov.Exp
