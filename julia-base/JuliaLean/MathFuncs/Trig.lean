import JuliaLean.MathFuncs.Prelude

/-!
`sinpi`, `cospi`, `sincospi`, `tanpi` for `Float64` and `Int64` from `base/special/trig.jl`,
Julia master `bbfa0ce4150`, and the Float64 kernels of Julia 1.13.2 (tag `v1.13.2`).
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `maxintfloat(::Type{Float64}) = 9007199254740992.`; `base/floatfuncs.jl:34`. -/
def maxintfloat : F64 := lit 0x4340000000000000

/-- `_sinpi_kernel_polynomial_f64.c₁`; `base/special/trig.jl:907-908`. -/
def sinpiC1 : F64 × F64 := (lit 0x400921fb54442d18, lit 0x3ca1adc7bbf1b141)

/-- `_sinpi_kernel_polynomial_f64.rest`; `base/special/trig.jl:909-918`. -/
def sinpiRest : List F64 :=
  [lit 0xc014abbce625be53, lit 0x400466bc6775ab4d, lit 0xbfe32d2cce634924,
   lit 0x3fb50783492dcb22, lit 0xbf7e3075d7cb71a7, lit 0x3f3e8fb7e22504ca,
   lit 0xbef6fdb69126ffe7]

/-- `_cospi_kernel_polynomial_f64.c₀`; `base/special/trig.jl:896`. -/
def cospiC0 : F64 := lit 0x3ff0000000000000

/-- `_cospi_kernel_polynomial_f64.c₂`; `base/special/trig.jl:897`. -/
def cospiC2 : F64 × F64 := (lit 0xc013bd3cc9be45de, lit 0xbcb30f699892a25e)

/-- `_cospi_kernel_polynomial_f64.rest`; `base/special/trig.jl:898-905`. -/
def cospiRest : List F64 :=
  [lit 0x40103c1f081b5aae, lit 0xbff55d3c7e3c9254, lit 0x3fce1f5068363dd1,
   lit 0xbf9a6d1ec7b4d288, lit 0x3f5f9cc3eb9ab614, lit 0xbf1b26337cdaa924]

/-- `_sinpi_kernel(x, sch)` with `sch.c₁ = (c1, c1lo)` and `sch.rest = c3 :: rest`;
`base/special/trig.jl:785-796`. -/
def sinpiKernelWith (c1 c1lo c3 : F64) (rest : List F64) (x : F64) : F64 :=
  let x2 := F64.mul x x
  let r := if rest.isEmpty then F64.zero else horner x2 rest
  F64.muladd c1 x (F64.mul x (F64.muladd c3 x2 (F64.muladd (F64.mul x2 x2) r c1lo)))

/-- `_cospi_kernel(x, sch)` after the negations `c₂ = -c₂`, `c₂_lo = -c₂_lo`, so `c2`, `c2lo`
are the negated stored coefficients; `base/special/trig.jl:771-783`. The compiled code
(x86-64, `code_llvm`/`code_native` of `Base.Math._cospi_kernel` on master) merges the
multiplication inside `muladd(c₂, x², -a_x²)` with `a_x² = c₂ * x²`, so that `muladd` is not
fused and evaluates `a_x² - a_x²`; the other `muladd`s are fused. -/
def cospiKernelWith (c0 c2 c2lo : F64) (rest : List F64) (x : F64) : F64 :=
  let x2 := F64.mul x x
  let r := F64.mul (horner x2 rest) x2
  let ax2 := F64.mul c2 x2
  let ax2lo := F64.muladd c2lo x2 (F64.sub ax2 ax2)
  let w := F64.sub c0 ax2
  F64.add w (F64.muladd x2 r (F64.sub (F64.sub (F64.sub c0 w) ax2) ax2lo))

/-- `sinpi_kernel(x::Float64) = _sinpi_kernel_f64(x)`, also `sinpi_kernel_wide`;
`base/special/trig.jl:725-730,923`. -/
def sinpiKernel (x : F64) : F64 :=
  sinpiKernelWith sinpiC1.1 sinpiC1.2 (sinpiRest.headD F64.zero) sinpiRest.tail x

/-- `cospi_kernel(x::Float64) = _cospi_kernel_f64(x)`, also `cospi_kernel_wide`;
`base/special/trig.jl:749-754,921`. -/
def cospiKernel (x : F64) : F64 :=
  cospiKernelWith cospiC0 (F64.neg cospiC2.1) (F64.neg cospiC2.2) cospiRest x

/-- `sinpi_kernel_wide(x::Float64)` of Julia 1.13.2; `base/special/trig.jl:732-739` at `v1.13.2`. -/
def sinpiKernelRelease (x : F64) : F64 :=
  sinpiKernelWith (lit 0x400921fb54442d18) (lit 0x3ca1a5f14401a51a) (lit 0xc014abbce625be53)
    [lit 0x400466bc6775aad9, lit 0xbfe32d2cce62ac24, lit 0x3fb50783485cc005,
     lit 0xbf7e3074b502de17, lit 0x3f3e8eed159ae666, lit 0xbef6c5b93983c183] x

/-- `cospi_kernel_wide(x::Float64)` of Julia 1.13.2, with the same unfused
`muladd(4.934802200544679, x², -a_x²)` as `cospiKernelWith`; `base/special/trig.jl:761-770` at
`v1.13.2`. -/
def cospiKernelRelease (x : F64) : F64 :=
  cospiKernelWith (lit 0x3ff0000000000000) (lit 0x4013bd3cc9be45de) (lit 0x3cb6685bec517345)
    [lit 0x40103c1f081b5ac0, lit 0xbff55d3c7e3cb0f5, lit 0x3fce1f506865cf50,
     lit 0xbf9a6d1eeca77196, lit 0x3f5f9cdff3b5e8c1, lit 0xbf1b2e7995b6bda9] x

/-- Integer value of an integral finite float, as `Int64(n)` for `|n| < 2^63`;
`base/special/trig.jl:946`. -/
private def intValue (n : F64) : Int :=
  let q := F64.toRat n
  q.1 / (q.2 : Int)

/-- Shared reduction `n = round(2*x)`, `rx = muladd(-0.5, n, x)`, `n = Int64(n) & 3`;
`base/special/trig.jl:944-946`. -/
def piReduce (x : F64) : F64 × Int :=
  let n := F64.round (F64.mul (F64.ofInt 2) x) .RoundNearest
  let rx := F64.muladd (lit 0xbfe0000000000000) n x
  (rx, intValue n % 4)

/-- `sinpi(_x::Float64)` with kernels `sk`, `ck`; `base/special/trig.jl:934-956`. -/
def sinpiWith (sk ck : F64 → F64) (x0 : F64) : Jl F64 :=
  let x := F64.abs x0
  if !F64.isfinite x then
    if F64.isnan x then .ok x else .error (.domainError "sinpi")
  else if F64.le maxintfloat x then .ok (copysign F64.zero x0)
  else
    let p := piReduce x
    let rx := p.1
    let n := p.2
    let res :=
      if n == 0 then sk rx
      else if n == 1 then ck rx
      else if n == 2 then F64.sub F64.zero (sk rx)
      else F64.sub F64.zero (ck rx)
    .ok (if F64.signbit x0 then F64.neg res else res)

/-- `cospi(x::Float64)` with kernels `sk`, `ck`; `base/special/trig.jl:968-990`. -/
def cospiWith (sk ck : F64 → F64) (x0 : F64) : Jl F64 :=
  let x := F64.abs x0
  if !F64.isfinite x then
    if F64.isnan x then .ok x else .error (.domainError "cospi")
  else if F64.le maxintfloat x then .ok F64.one
  else
    let p := piReduce x
    let rx := p.1
    let n := p.2
    if n == 0 then .ok (ck rx)
    else if n == 1 then .ok (F64.sub F64.zero (sk rx))
    else if n == 2 then .ok (F64.sub F64.zero (ck rx))
    else .ok (sk rx)

/-- The quadrant selection of `sincospi`/`tanpi`; `base/special/trig.jl:1018-1029`. -/
private def sincosQuadrant (sk ck : F64 → F64) (x0 x : F64) : F64 × F64 :=
  let p := piReduce x
  let rx := p.1
  let n := p.2
  let si := sk rx
  let co := ck rx
  let q :=
    if n == 0 then (si, co)
    else if n == 1 then (co, F64.sub F64.zero si)
    else if n == 2 then (F64.sub F64.zero si, F64.sub F64.zero co)
    else (F64.sub F64.zero co, si)
  (if F64.signbit x0 then F64.neg q.1 else q.1, q.2)

/-- `sincospi(_x::Float64)` with kernels `sk`, `ck`; `base/special/trig.jl:1005-1030`. -/
def sincospiWith (sk ck : F64 → F64) (x0 : F64) : Jl (F64 × F64) :=
  let x := F64.abs x0
  if !F64.isfinite x then
    if F64.isnan x then .ok (x, x) else .error (.domainError "sincospi")
  else if F64.le maxintfloat x then .ok (copysign F64.zero x0, F64.one)
  else .ok (sincosQuadrant sk ck x0 x)

/-- `tanpi(_x::Float64)` with kernels `sk`, `ck`; `base/special/trig.jl:1044-1071`. -/
def tanpiWith (sk ck : F64 → F64) (x0 : F64) : Jl F64 :=
  let x := F64.abs x0
  if !F64.isfinite x then
    if F64.isnan x then .ok x else .error (.domainError "tanpi")
  else if F64.le maxintfloat x then .ok (copysign F64.zero x0)
  else
    let q := sincosQuadrant sk ck x0 x
    .ok (F64.div q.1 q.2)

/-- `sinpi(::Float64)`; `base/special/trig.jl:934-956`. -/
def sinpi (x : F64) : Jl F64 := sinpiWith sinpiKernel cospiKernel x

/-- `cospi(::Float64)`; `base/special/trig.jl:968-990`. -/
def cospi (x : F64) : Jl F64 := cospiWith sinpiKernel cospiKernel x

/-- `sincospi(::Float64)`; `base/special/trig.jl:1005-1030`. -/
def sincospi (x : F64) : Jl (F64 × F64) := sincospiWith sinpiKernel cospiKernel x

/-- `tanpi(::Float64)`; `base/special/trig.jl:1044-1071`. -/
def tanpi (x : F64) : Jl F64 := tanpiWith sinpiKernel cospiKernel x

/-- `sinpi(::Float64)` of Julia 1.13.2; `base/special/trig.jl:796-817` at `v1.13.2`. -/
def sinpiRelease (x : F64) : Jl F64 := sinpiWith sinpiKernelRelease cospiKernelRelease x

/-- `cospi(::Float64)` of Julia 1.13.2; `base/special/trig.jl:829-850` at `v1.13.2`. -/
def cospiRelease (x : F64) : Jl F64 := cospiWith sinpiKernelRelease cospiKernelRelease x

/-- `sincospi(::Float64)` of Julia 1.13.2; `base/special/trig.jl:865-889` at `v1.13.2`. -/
def sincospiRelease (x : F64) : Jl (F64 × F64) :=
  sincospiWith sinpiKernelRelease cospiKernelRelease x

/-- `tanpi(::Float64)` of Julia 1.13.2; `base/special/trig.jl:904-931` at `v1.13.2`. -/
def tanpiRelease (x : F64) : Jl F64 := tanpiWith sinpiKernelRelease cospiKernelRelease x

/-- `sinpi(x::Integer)` for `Int64`; `base/special/trig.jl:1074`. -/
def sinpiInt (n : Int) : F64 := if n ≥ 0 then F64.zero else F64.neg F64.zero

/-- `cospi(x::Integer)` for `Int64`; `base/special/trig.jl:1075`. -/
def cospiInt (n : Int) : F64 := if n % 2 != 0 then F64.neg F64.one else F64.one

/-- `tanpi(x::Integer)` for `Int64`; `base/special/trig.jl:1076-1077`. -/
def tanpiInt (n : Int) : F64 :=
  if n ≥ 0 then (if n % 2 != 0 then F64.neg F64.zero else F64.zero)
  else (if n % 2 != 0 then F64.zero else F64.neg F64.zero)

end JuliaLean.MathFuncs
