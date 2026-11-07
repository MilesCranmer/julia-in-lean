import JuliaLean.base.float
import JuliaLean.base.floatfuncs
import JuliaLean.base.int
import JuliaLean.base.twiceprecision
import JuliaLean.base.math

/-!
Model of the Float64 methods of `base/special/exp.jl` (exp, exp2, exp10, expm1, the
integer `exp2`) and `exthorner` from `base/math.jl`, Julia master `bbfa0ce4150`.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- The base selectors `Val(2)`, `Val(:ℯ)`, `Val(10)`; `base/special/exp.jl:325-327`. -/
inductive ExpBase
  | two
  | e
  | ten
  deriving DecidableEq, Repr

/-- `MAGIC_ROUND_CONST(Float64)`; `base/special/exp.jl:6`. -/
def magicRoundConst : F64 := lit 0x4338000000000000

/-- `MAX_EXP(base, Float64)`; `base/special/exp.jl:12-16`. -/
def maxExp : ExpBase → F64
  | .two => lit 0x4090000000000000
  | .e => lit 0x40862e42fefa39f0
  | .ten => lit 0x40734413509f79ff

/-- `MIN_EXP(base, Float64)`; `base/special/exp.jl:20-24`. -/
def minExp : ExpBase → F64
  | .two => lit 0xc090cc0000000000
  | .e => lit 0xc0874910d52d3052
  | .ten => lit 0xc07439b746e36b52

/-- `SUBNORM_EXP(base, Float64)`; `base/special/exp.jl:29-33`. -/
def subnormExp : ExpBase → F64
  | .two => lit 0x408ff00000000000
  | .e => lit 0x4086232bdd7abcd2
  | .ten => lit 0x40733a7146f72a41

/-- `LogBo256INV(base, Float64)`; `base/special/exp.jl:36-38`. -/
def logBo256Inv : ExpBase → F64
  | .two => lit 0x4070000000000000
  | .e => lit 0x40771547652b82fe
  | .ten => lit 0x408a934f0979a371

/-- `LogBo256U(base, Float64)`; `base/special/exp.jl:44-46`. -/
def logBo256U : ExpBase → F64
  | .two => lit 0xbf70000000000000
  | .e => lit 0xbf662e42fef80000
  | .ten => lit 0xbf53441350980000

/-- `LogBo256L(base, Float64)`; `base/special/exp.jl:47-49`. -/
def logBo256L : ExpBase → F64
  | .two => lit 0x0000000000000000
  | .e => lit 0xbd31cf79abc9e3b4
  | .ten => lit 0xbd3de7fbcc47c4ad

/-- `expm1b_kernel(base, x::Float64)`; `base/special/exp.jl:73-84`. -/
def expm1bKernel : ExpBase → F64 → F64
  | .two, x => F64.mul x (horner x [lit 0x3fe62e42fefa39b9, lit 0x3fcebfbdff82c58a,
      lit 0x3fac6b090da323ac, lit 0x3f83b2ab7edf14f2])
  | .e, x => F64.mul x (horner x [lit 0x3fefffffffffffb1, lit 0x3fdffffffffffffb,
      lit 0x3fc555557e55efed, lit 0x3fa5555565bbf98f])
  | .ten, x => F64.mul x (horner x [lit 0x40026bb1bbb554e8, lit 0x40053524c73cea65,
      lit 0x40004705b127214d, lit 0x3ff2bd761865db6c])

/-- `J_TABLE`, 256 UInt64 words; `base/special/exp.jl:125-175`. -/
def jTable : List Nat := [
  0x0000000000000000,0xaac00b1afa5abcbe,0x9b60163da9fb3335,0xab502168143b0280,0xadc02c9a3e778060,
  0x656037d42e11bbcc,0xa7a04315e86e7f84,0x84c04e5f72f654b1,0x8d7059b0d3158574,0xa510650a0e3c1f88,
  0xa8d0706b29ddf6dd,0x83207bd42b72a836,0x6180874518759bc8,0xa4b092bdf66607df,0x91409e3ecac6f383,
  0x85d0a9c79b1f3919,0x98a0b5586cf9890f,0x94f0c0f145e46c85,0x9010cc922b7247f7,0xa210d83b23395deb,
  0x4030e3ec32d3d1a2,0xa5b0efa55fdfa9c4,0xae40fb66affed31a,0x8d41073028d7233e,0xa4911301d0125b50,
  0xa1a11edbab5e2ab5,0xaf712abdc06c31cb,0xae8136a814f204aa,0xa661429aaea92ddf,0xa9114e95934f312d,
  0x82415a98c8a58e51,0x58f166a45471c3c2,0xab9172b83c7d517a,0x70917ed48695bbc0,0xa7718af9388c8de9,
  0x94a1972658375d2f,0x8e51a35beb6fcb75,0x97b1af99f8138a1c,0xa351bbe084045cd3,0x9001c82f95281c6b,
  0x9e01d4873168b9aa,0xa481e0e75eb44026,0xa711ed5022fcd91c,0xa201f9c18438ce4c,0x8dc2063b88628cd6,
  0x935212be3578a819,0x82a21f49917ddc96,0x8d322bdda27912d1,0x99b2387a6e756238,0x8ac2451ffb82140a,
  0x8ac251ce4fb2a63f,0x93e25e85711ece75,0x82b26b4565e27cdd,0x9e02780e341ddf29,0xa2d284dfe1f56380,
  0xab4291ba7591bb6f,0x86129e9df51fdee1,0xa352ab8a66d10f12,0xafb2b87fd0dad98f,0xa572c57e39771b2e,
  0x9002d285a6e4030b,0x9d12df961f641589,0x71c2ecafa93e2f56,0xaea2f9d24abd886a,0x86f306fe0a31b715,
  0x89531432edeeb2fd,0x8a932170fc4cd831,0xa1d32eb83ba8ea31,0x93233c08b26416ff,0xab23496266e3fa2c,
  0xa92356c55f929ff0,0xa8f36431a2de883a,0xa4e371a7373aa9ca,0xa3037f26231e7549,0xa0b38cae6d05d865,
  0xa3239a401b7140ee,0xad43a7db34e59ff6,0x9543b57fbfec6cf4,0xa083c32dc313a8e4,0x7fe3d0e544ede173,
  0x8ad3dea64c123422,0xa943ec70df1c5174,0xa413fa4504ac801b,0x8bd40822c367a024,0xaf04160a21f72e29,
  0xa3d423fb27094689,0xab8431f5d950a896,0x88843ffa3f84b9d4,0x48944e086061892d,0xae745c2042a7d231,
  0x9c946a41ed1d0057,0xa1e4786d668b3236,0x73c486a2b5c13cd0,0xab1494e1e192aed1,0x99c4a32af0d7d3de,
  0xabb4b17dea6db7d6,0x7d44bfdad5362a27,0x9054ce41b817c114,0x98e4dcb299fddd0d,0xa564eb2d81d8abfe,
  0xa5a4f9b2769d2ca6,0x7a2508417f4531ee,0xa82516daa2cf6641,0xac65257de83f4eee,0xabe5342b569d4f81,
  0x879542e2f4f6ad27,0xa8a551a4ca5d920e,0xa7856070dde910d1,0x99b56f4736b527da,0xa7a57e27dbe2c4ce,
  0x82958d12d497c7fd,0xa4059c0827ff07cb,0x9635ab07dd485429,0xa245ba11fba87a02,0x3c45c9268a5946b7,
  0xa195d84590998b92,0x9ba5e76f15ad2148,0xa985f6a320dceb70,0xa60605e1b976dc08,0x9e46152ae6cdf6f4,
  0xa636247eb03a5584,0x984633dd1d1929fd,0xa8e6434634ccc31f,0xa28652b9febc8fb6,0xa226623882552224,
  0xa85671c1c70833f5,0x60368155d44ca973,0x880690f4b19e9538,0xa216a09e667f3bcc,0x7a36b052fa75173e,
  0xada6c012750bdabe,0x9c76cfdcddd47645,0xae46dfb23c651a2e,0xa7a6ef9298593ae4,0xa9f6ff7df9519483,
  0x59d70f7466f42e87,0xaba71f75e8ec5f73,0xa6f72f8286ead089,0xa7a73f9a48a58173,0x90474fbd35d7cbfd,
  0xa7e75feb564267c8,0x9b777024b1ab6e09,0x986780694fde5d3f,0x934790b938ac1cf6,0xaaf7a11473eb0186,
  0xa207b17b0976cfda,0x9f17c1ed0130c132,0x91b7d26a62ff86f0,0x7057e2f336cf4e62,0xabe7f3878491c490,
  0xa6c80427543e1a11,0x946814d2add106d9,0xa1582589994cce12,0x9998364c1eb941f7,0xa9c8471a4623c7ac,
  0xaf2857f4179f5b20,0xa01868d99b4492ec,0x85d879cad931a436,0x99988ac7d98a6699,0x9d589bd0a478580f,
  0x96e8ace5422aa0db,0x9ec8be05bad61778,0xade8cf3216b5448b,0xa478e06a5e0866d8,0x85c8f1ae99157736,
  0x959902fed0282c8a,0xa119145b0b91ffc5,0xab2925c353aa2fe1,0xae893737b0cdc5e4,0xa88948b82b5f98e4,
  0xad395a44cbc8520e,0xaf296bdd9a7670b2,0xa1797d829fde4e4f,0x7ca98f33e47a22a2,0xa749a0f170ca07b9,
  0xa119b2bb4d53fe0c,0x7c79c49182a3f090,0xa579d674194bb8d4,0x7829e86319e32323,0xaad9fa5e8d07f29d,
  0xa65a0c667b5de564,0x9c6a1e7aed8eb8bb,0x963a309bec4a2d33,0xa2aa42c980460ad7,0xa16a5503b23e255c,
  0x650a674a8af46052,0x9bca799e1330b358,0xa58a8bfe53c12e58,0x90fa9e6b5579fdbf,0x889ab0e521356eba,
  0xa81ac36bbfd3f379,0x97ead5ff3a3c2774,0x97aae89f995ad3ad,0xa5aafb4ce622f2fe,0xa21b0e07298db665,
  0x94db20ce6c9a8952,0xaedb33a2b84f15fa,0xac1b468415b749b0,0xa1cb59728de55939,0x92ab6c6e29f1c52a,
  0xad5b7f76f2fb5e46,0xa24b928cf22749e3,0xa08ba5b030a10649,0xafcbb8e0b79a6f1e,0x823bcc1e904bc1d2,
  0xafcbdf69c3f3a206,0xa08bf2c25bd71e08,0xa89c06286141b33c,0x811c199bdd85529c,0xa48c2d1cd9fa652b,
  0x9b4c40ab5fffd07a,0x912c544778fafb22,0x928c67f12e57d14b,0xa86c7ba88988c932,0x71ac8f6d9406e7b5,
  0xaa0ca3405751c4da,0x750cb720dcef9069,0xac5ccb0f2e6d1674,0xa88cdf0b555dc3f9,0xa2fcf3155b5bab73,
  0xa1ad072d4a07897b,0x955d1b532b08c968,0xa15d2f87080d89f1,0x93dd43c8eacaa1d6,0x82ed5818dcfba487,
  0x5fed6c76e862e6d3,0xa77d80e316c98397,0x9a0d955d71ff6075,0x9c2da9e603db3285,0xa24dbe7cd63a8314,
  0x92ddd321f301b460,0xa1ade7d5641c0657,0xa72dfc97337b9b5e,0xadae11676b197d16,0xa42e264614f5a128,
  0xa30e3b333b16ee11,0x839e502ee78b3ff6,0xaa7e653924676d75,0x92de7a51fbc74c83,0xa77e8f7977cdb73f,
  0xa0bea4afa2a490d9,0x948eb9f4867cca6e,0xa1becf482d8e67f0,0x91cee4aaa2188510,0x9dcefa1bee615a27,
  0xa66f0f9c1cb64129,0x93af252b376bba97,0xacdf3ac948dd7273,0x99df50765b6e4540,0x9faf6632798844f8,
  0xa12f7bfdad9cbe13,0xaeef91d802243c88,0x874fa7c1819e90d8,0xacdfbdba3692d513,0x62efd3c22b8f71f1,
  0x74afe9d96b2a23d9]

/-- `JU_MASK = typemax(UInt64)>>12`; `base/special/exp.jl:106`. -/
def juMask : Nat := 2^52 - 1

/-- `JU_CONST`; `base/special/exp.jl:108`. -/
def juConst : Nat := 0x3FF0000000000000

/-- `JL_CONST`; `base/special/exp.jl:109`. -/
def jlConst : Nat := 0x3C00000000000000

/-- `table_unpack(ind::Int32)` with `ind` an Int32 value; `base/special/exp.jl:178-184`. -/
def tableUnpack (ind : Int) : F64 × F64 :=
  let j := jTable.getD (ind % 256).toNat 0
  (ofBitsU (Nat.lor juConst (Nat.land j juMask)), ofBitsU (Nat.lor jlConst (j >>> 8)))

/-- `reinterpret(UInt64, x) % Int32`: the low 32 bits as a signed value;
`base/special/exp.jl:210`. -/
def int32OfBits (u : Nat) : Int :=
  let v : Nat := u % 2^32
  if v ≥ 2^31 then (v : Int) - 2^32 else (v : Int)

/-- Shared argument reduction returning `(N, r)`; `base/special/exp.jl:209-213`
(identical at `:235-239` and `:443-447`). -/
def expReduce (x : F64) (b : ExpBase) : Int × F64 :=
  let nf := F64.muladd x (logBo256Inv b) magicRoundConst
  let n := int32OfBits (bitsOf nf)
  let nf := F64.sub nf magicRoundConst
  let r := F64.muladd nf (logBo256U b) x
  (n, F64.muladd nf (logBo256L b) r)

/-- Subnormal-result scaling `reinterpret(T, ((k % UInt64) +% 53) << 52 +% small) * 0x1p-53`;
`base/special/exp.jl:224-225`. -/
def expSubnormalScale (k : Int) (smallPart : F64) : F64 :=
  let twopk := ((k + 53) % 2^64).toNat * 2^52 % 2^64
  F64.mul (ofBitsU (twopk + bitsOf smallPart)) (lit 0x3ca0000000000000)

/-- `exp_impl(x::Float64, base)`; `base/special/exp.jl:207-231`. -/
def expImpl (x : F64) (b : ExpBase) : F64 :=
  let (n, r) := expReduce x b
  let k := n.fdiv 256
  let (jU, jL) := tableUnpack n
  let smallPart := F64.add (F64.muladd jU (expm1bKernel b r) jL) jU
  let scaled := ofInt64 (k * 2^52 + toInt64 smallPart)
  if !(F64.le (F64.abs x) (subnormExp b)) then
    if F64.isnan x then x
    else if F64.le (maxExp b) x then F64.inf
    else if F64.le x (minExp b) then F64.zero
    else if k ≤ -53 then expSubnormalScale k smallPart
    else scaled
  else scaled

/-- `exp_impl(x::Float64, xlo::Float64, base)`, computing `base^(x+xlo)`;
`base/special/exp.jl:233-259`. -/
def expImplLo (x xlo : F64) (b : ExpBase) : F64 :=
  let (n, r) := expReduce x b
  let k := n.fdiv 256
  let (jU, jL) := tableUnpack n
  let kern := expm1bKernel b r
  let verySmall := F64.muladd kern (F64.mul jU xlo) jL
  let (hi, lo) := canonicalize2 F64.one kern
  let smallPart := F64.fma jU hi (F64.muladd jU (F64.add lo xlo) verySmall)
  let scaled := ofInt64 (k * 2^52 + toInt64 smallPart)
  if !(F64.le (F64.abs x) (subnormExp b)) then
    if F64.isnan x then x
    else if F64.le (maxExp b) x then F64.inf
    else if F64.le x (minExp b) then F64.zero
    else if k ≤ -53 then expSubnormalScale k smallPart
    else if k == 1024 then
      F64.mul (F64.mul smallPart (lit 0x4000000000000000)) (lit 0x7fe0000000000000)
    else scaled
  else scaled

/-- `exp(x::Float64) = exp_impl(x, Val(:ℯ))`; `base/special/exp.jl:325-329`. -/
def exp (x : F64) : F64 := expImpl x .e

/-- `exp2(x::Float64) = exp_impl(x, Val(2))`; `base/special/exp.jl:325-329`. -/
def exp2 (x : F64) : F64 := expImpl x .two

/-- `exp10(x::Float64) = exp_impl(x, Val(10))`; `base/special/exp.jl:325-329`. -/
def exp10 (x : F64) : F64 := expImpl x .ten

/-- `exp2(x::Base.BitInteger)`; `base/special/exp.jl:391-403`. `x + 1074` is computed in
`promote_type(T, Int64)`, then reduced `% UInt`; the UInt64 shift `1 << s` is zero for
`s ≥ 64`. -/
def exp2Int {t : IntTy} (x : JInt t) : F64 :=
  if x.val > 1023 then F64.inf
  else if x.val < -1074 then F64.zero
  else if x.val ≤ -1023 then
    let s := (JInt.wrap .u64 (JInt.wrap (IntTy.promote t .i64) (x.val + 1074)).val).val.toNat
    ofBitsU (if s < 64 then 2^s else 0)
  else
    let e := JInt.wrap .i64 (1023 + (JInt.wrap .i64 x.val).val)
    ofInt64 (JInt.wrap .i64 (e.val * 2^52)).val

/-- The previous pinned implementation, retained for the release-era counterexample. -/
def exp2IntLegacy {t : IntTy} (x : JInt t) : F64 :=
  if x.val > 1023 then F64.inf
  else if x.val ≤ -1023 then
    let s := (JInt.wrap .u64 (JInt.wrap (IntTy.promote t .i64) (x.val + 1074)).val).val.toNat
    ofBitsU (if s < 64 then 2^s else 0)
  else
    let e := JInt.wrap .i64 (1023 + (JInt.wrap .i64 x.val).val)
    ofInt64 (JInt.wrap .i64 (e.val * 2^52)).val

/-- `MAX_EXP(Float64)` for `expm1`; `base/special/exp.jl:406`. -/
def expm1MaxExp : F64 := lit 0x40862e42fefa39f4

/-- `MIN_EXP(Float64)` for `expm1`; `base/special/exp.jl:407`. -/
def expm1MinExp : F64 := lit 0xc042b708872320e2


/-- `expm1_small(x::Float64)`; `base/special/exp.jl:419-425`. -/
def expm1Small (x : F64) : F64 :=
  let p := horner x [lit 0x3fc5555555555549, lit 0x3fa55555555554b6, lit 0x3f8111111111a9f3,
    lit 0x3f56c16c16ce14c6, lit 0x3f2a01a01159dd2d, lit 0x3efa019f635825c4,
    lit 0x3ec71e14bfe3db59, lit 0x3e928295484734ee, lit 0x3e5a2836aa646b96]
  let p2 := exthorner twoMul x (F64.one, lit 0x3fe0000000000000, p)
  F64.fma x p2.1 (F64.mul x p2.2)

/-- Table path of `expm1(x::Float64)` after the range checks; `base/special/exp.jl:443-456`. -/
def expm1Table (x : F64) : F64 :=
  let (n, r) := expReduce x .e
  let k := n.fdiv 256
  let (jU, jL) := tableUnpack n
  let p := expm1bKernel .e r
  let twopk := ofInt64 ((1023 + k) * 2^52)
  let twopnk := ofInt64 ((1023 - k) * 2^52)
  if k ≥ 106 then
    F64.mul (F64.mul (ofInt64 ((1022 + k) * 2^52)) (F64.add jU (F64.muladd jU p jL)))
      (lit 0x4000000000000000)
  else if k ≥ 53 then F64.mul twopk (F64.add jU (F64.muladd jU p (F64.sub jL twopnk)))
  else if k ≤ -2 then F64.sub (F64.mul twopk (F64.add jU (F64.muladd jU p jL))) F64.one
  else F64.mul twopk (F64.add (F64.sub jU twopnk) (F64.fma jU p jL))

/-- `expm1(x::Float64)`; `base/special/exp.jl:433-457`. -/
def expm1 (x : F64) : F64 :=
  if F64.le (lit 0xbfd269621134db92) x && F64.le x (lit 0x3fcc8ff7c79a9a22) then expm1Small x
  else if !(F64.le (F64.abs x) expm1MinExp) then
    if F64.isnan x then x
    else if F64.lt expm1MaxExp x then F64.inf
    else if F64.lt x expm1MinExp then lit 0xbff0000000000000
    else expm1Table x
  else expm1Table x

end JuliaLean.MathFuncs

/-!
`base/special/exp.jl` at Julia master `bbfa0ce4150` for `Float32` and `Float16`, plus
the per-type constant methods; the `Float64` methods are `JuliaLean.MathFuncs.Exp`.
Also `exthorner`/`_exthorner` (`base/math.jl:196-210`) for both types.
-/

namespace JuliaLean.MathCov.Exp

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathFuncs (ExpBase)


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

/-- `expm1_small(x::Float32)`; `base/special/exp.jl:426-431`. -/
def expm1Small32 (x : FV .f32) : FV .f32 :=
  let p := horner x expm1SmallP32
  match exthorner twoMulG x (one .f32, lit .f32 0x3f000000, p) with
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

/-!
# Model of `base/special/exp.jl`

The Float16, Float32 and Float64 methods use typed IEEE values and the shared
integer and float models. `J_TABLE` stays visible in its source form below; its
exact Float64 words are reused from `JuliaLean.MathFuncs.Exp.jTable`.
-/

namespace JuliaLean.base.special.exp

open JuliaLean JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.MathCov
open JuliaLean.MathFuncs (ExpBase)

abbrev F32 := FV .f32
abbrev F64 := FV .f64

private def lit32 (bits : Nat) : F32 := FP.lit .f32 bits
private def lit64 (bits : Nat) : F64 := FP.lit .f64 bits

/--
Julia source: base/special/exp.jl:6-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
MAGIC_ROUND_CONST(::Type{Float64}) = 6.755399441055744e15
MAGIC_ROUND_CONST(::Type{Float32}) = 1.048576f7
```
-/
def magicRoundConst64 : F64 := lit64 0x4338000000000000
def magicRoundConst32 : F32 := lit32 0x4b200000

/--
Julia source: base/special/exp.jl:11-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
MAX_EXP(n::Val{2}, ::Type{Float32}) = 128.0f0
MAX_EXP(n::Val{2}, ::Type{Float64}) = 1024.0
MAX_EXP(n::Val{:ℯ}, ::Type{Float32}) = 88.72284f0
MAX_EXP(n::Val{:ℯ}, ::Type{Float64}) = 709.7827128933841
MAX_EXP(n::Val{10}, ::Type{Float32}) = 38.53184f0
MAX_EXP(n::Val{10}, ::Type{Float64}) = 308.25471555991675
```
-/
def maxExp32 : ExpBase → F32
  | .two => lit32 0x43000000
  | .e => lit32 0x42b17218
  | .ten => lit32 0x421a209b

def maxExp64 : ExpBase → F64
  | .two => lit64 0x4090000000000000
  | .e => lit64 0x40862e42fefa39f0
  | .ten => lit64 0x40734413509f79ff

/--
Julia source: base/special/exp.jl:19-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
MIN_EXP(n::Val{2}, ::Type{Float32}) = -150.0f0
MIN_EXP(n::Val{2}, ::Type{Float64}) = -1075.0
MIN_EXP(n::Val{:ℯ}, ::Type{Float32}) = -103.97208f0
MIN_EXP(n::Val{:ℯ}, ::Type{Float64}) = -745.1332191019412
MIN_EXP(n::Val{10}, ::Type{Float32}) = -45.1545f0
MIN_EXP(n::Val{10}, ::Type{Float64}) = -323.60724533877976
```
-/
def minExp32 : ExpBase → F32
  | .two => lit32 0xc3160000
  | .e => lit32 0xc2cff1b4
  | .ten => lit32 0xc2349e35

def minExp64 : ExpBase → F64
  | .two => lit64 0xc090cc0000000000
  | .e => lit64 0xc0874910d52d3052
  | .ten => lit64 0xc07439b746e36b52

/--
Julia source: base/special/exp.jl:28-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SUBNORM_EXP(n::Val{2}, ::Type{Float32}) = 126.00001f0
SUBNORM_EXP(n::Val{2}, ::Type{Float64}) = 1022.0
SUBNORM_EXP(n::Val{:ℯ}, ::Type{Float32}) = 87.33655f0
SUBNORM_EXP(n::Val{:ℯ}, ::Type{Float64}) = 708.3964185322641
SUBNORM_EXP(n::Val{10}, ::Type{Float32}) = 37.92978f0
SUBNORM_EXP(n::Val{10}, ::Type{Float64}) = 307.6526555685887
```
-/
def subnormExp32 : ExpBase → F32
  | .two => lit32 0x42fc0001
  | .e => lit32 0x42aeac50
  | .ten => lit32 0x4217b818

def subnormExp64 : ExpBase → F64
  | .two => lit64 0x408ff00000000000
  | .e => lit64 0x4086232bdd7abcd2
  | .ten => lit64 0x40733a7146f72a41

/--
Julia source: base/special/exp.jl:36-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogBo256INV(::Val{2}, ::Type{Float64}) = 256.0
LogBo256INV(::Val{:ℯ}, ::Type{Float64}) = 369.3299304675746
LogBo256INV(::Val{10}, ::Type{Float64}) = 850.4135922911647
```
-/
def logBo256Inv : ExpBase → F64
  | .two => lit64 0x4070000000000000
  | .e => lit64 0x40771547652b82fe
  | .ten => lit64 0x408a934f0979a371

/--
Julia source: base/special/exp.jl:44-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogBo256U(::Val{2}, ::Type{Float64}) = -0.00390625
LogBo256U(::Val{:ℯ}, ::Type{Float64}) = -0.002707606173999011
LogBo256U(::Val{10}, ::Type{Float64}) = -0.0011758984204561784
```
-/
def logBo256U : ExpBase → F64
  | .two => lit64 0xbf70000000000000
  | .e => lit64 0xbf662e42fef80000
  | .ten => lit64 0xbf53441350980000

/--
Julia source: base/special/exp.jl:47-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogBo256L(::Val{2}, ::Type{Float64}) = 0.0
LogBo256L(::Val{:ℯ}, ::Type{Float64}) = -6.327543041662719e-14
LogBo256L(::Val{10}, ::Type{Float64}) = -1.0624811566412999e-13
```
-/
def logBo256L : ExpBase → F64
  | .two => lit64 0x0000000000000000
  | .e => lit64 0xbd31cf79abc9e3b4
  | .ten => lit64 0xbd3de7fbcc47c4ad

/--
Julia source: base/special/exp.jl:52-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogBINV(::Val{2}, ::Type{Float32}) = 1.0f0
LogBINV(::Val{:ℯ}, ::Type{Float32}) = 1.442695f0
LogBINV(::Val{10}, ::Type{Float32}) = 3.321928f0
```
-/
def logBInv32 : ExpBase → F32
  | .two => lit32 0x3f800000
  | .e => lit32 0x3fb8aa3b
  | .ten => lit32 0x40549a78

/--
Julia source: base/special/exp.jl:60-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogBU(::Val{2}, ::Type{Float32}) = -1.0f0
LogBU(::Val{:ℯ}, ::Type{Float32}) = -0.69314575f0
LogBU(::Val{10}, ::Type{Float32}) = -0.3010254f0
```
-/
def logBU32 : ExpBase → F32
  | .two => lit32 0xbf800000
  | .e => lit32 0xbf317200
  | .ten => lit32 0xbe9a2000

/--
Julia source: base/special/exp.jl:63-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogBL(::Val{2}, ::Type{Float32}) = 0.0f0
LogBL(::Val{:ℯ}, ::Type{Float32}) = -1.4286068f-6
LogBL(::Val{10}, ::Type{Float32}) = -4.605039f-6
```
-/
def logBL32 : ExpBase → F32
  | .two => lit32 0x00000000
  | .e => lit32 0xb5bfbe8e
  | .ten => lit32 0xb69a84fc

/--
Julia source: base/special/exp.jl:68-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogB(::Val{2}, ::Type{Float16}) = -1.0f0
LogB(::Val{:ℯ}, ::Type{Float16}) = -0.6931472f0
LogB(::Val{10}, ::Type{Float16}) = -0.30103f0
```
-/
def logB16 : ExpBase → FV .f32
  | .two => lit32 0xbf800000
  | .e => lit32 0xbf317218
  | .ten => lit32 0xbe9a209b

private def horner64 (x : F64) : List F64 → F64
  | [] => FP.zero .f64
  | [c] => c
  | c :: cs => FP.muladd x (horner64 x cs) c

/--
Julia source: base/special/exp.jl:73-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function expm1b_kernel(::Val{2}, x::Float64)
    return x * evalpoly(x, (0.6931471805599393, 0.24022650695910058,
                            0.05550411502333161, 0.009618129548366803))
end
function expm1b_kernel(::Val{:ℯ}, x::Float64)
    return x * evalpoly(x, (0.9999999999999912, 0.4999999999999997,
                            0.1666666857598779, 0.04166666857598777))
end
function expm1b_kernel(::Val{10}, x::Float64)
    return x * evalpoly(x, (2.3025850929940255, 2.6509490552391974,
                            2.034678825384765, 1.1712552025835192))
end
```
-/
def expm1bKernel (b : ExpBase) (x : F64) : F64 :=
  let cs := match b with
    | .two => [lit64 0x3fe62e42fefa39b9, lit64 0x3fcebfbdff82c58a, lit64 0x3fac6b090da323ac, lit64 0x3f83b2ab7edf14f2]
    | .e => [lit64 0x3fefffffffffffb1, lit64 0x3fdffffffffffffb, lit64 0x3fc555557e55efed, lit64 0x3fa5555565bbf98f]
    | .ten => [lit64 0x40026bb1bbb554e8, lit64 0x40053524c73cea65, lit64 0x40004705b127214d, lit64 0x3ff2bd761865db6c]
  FP.mul x (horner64 x cs)

/--
Julia source: base/special/exp.jl:86-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function expb_kernel(::Val{2}, x::Float32)
    return evalpoly(x, (1.0f0, 0.6931472f0, 0.2402265f0,
                        0.05550411f0, 0.009618025f0,
                        0.0013333423f0, 0.00015469732f0, 1.5316464f-5))
end
function expb_kernel(::Val{:ℯ}, x::Float32)
    return evalpoly(x, (1.0f0, 1.0f0, 0.5f0, 0.16666667f0,
                        0.041666217f0, 0.008333249f0,
                        0.001394858f0, 0.00019924171f0))
end
function expb_kernel(::Val{10}, x::Float32)
    return evalpoly(x, (1.0f0, 2.3025851f0, 2.650949f0,
                        2.0346787f0, 1.1712426f0, 0.53937745f0,
                        0.20788547f0, 0.06837386f0))
end
```
-/
def expbKernel32 (b : ExpBase) (x : F32) : F32 :=
  let cs := match b with
    | .two => JuliaLean.MathCov.C.expbKernel32Two
    | .e => JuliaLean.MathCov.C.expbKernel32E
    | .ten => JuliaLean.MathCov.C.expbKernel32Ten
  JuliaLean.MathCov.Exp.horner x cs

/-- The mantissa table words are read from the exact typed table model below. -/
def jTable : List Nat := JuliaLean.MathFuncs.jTable

/--
Julia source: base/special/exp.jl:106-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const JU_MASK = typemax(UInt64)>>12
const JL_MASK = typemax(UInt64)>>8
const JU_CONST = 0x3FF0000000000000
const JL_CONST = 0x3C00000000000000
```
-/
def tableMasks : Nat × Nat × Nat × Nat :=
  (2^52 - 1, 2^56 - 1, 0x3FF0000000000000, 0x3C00000000000000)
-- UNTRANSLATED
-- Source: base/special/exp.jl:125-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const J_TABLE = (0x0000000000000000, 0xaac00b1afa5abcbe, 0x9b60163da9fb3335, 0xab502168143b0280, 0xadc02c9a3e778060,
--                  0x656037d42e11bbcc, 0xa7a04315e86e7f84, 0x84c04e5f72f654b1, 0x8d7059b0d3158574, 0xa510650a0e3c1f88,
--                  0xa8d0706b29ddf6dd, 0x83207bd42b72a836, 0x6180874518759bc8, 0xa4b092bdf66607df, 0x91409e3ecac6f383,
--                  0x85d0a9c79b1f3919, 0x98a0b5586cf9890f, 0x94f0c0f145e46c85, 0x9010cc922b7247f7, 0xa210d83b23395deb,
--                  0x4030e3ec32d3d1a2, 0xa5b0efa55fdfa9c4, 0xae40fb66affed31a, 0x8d41073028d7233e, 0xa4911301d0125b50,
--                  0xa1a11edbab5e2ab5, 0xaf712abdc06c31cb, 0xae8136a814f204aa, 0xa661429aaea92ddf, 0xa9114e95934f312d,
--                  0x82415a98c8a58e51, 0x58f166a45471c3c2, 0xab9172b83c7d517a, 0x70917ed48695bbc0, 0xa7718af9388c8de9,
--                  0x94a1972658375d2f, 0x8e51a35beb6fcb75, 0x97b1af99f8138a1c, 0xa351bbe084045cd3, 0x9001c82f95281c6b,
--                  0x9e01d4873168b9aa, 0xa481e0e75eb44026, 0xa711ed5022fcd91c, 0xa201f9c18438ce4c, 0x8dc2063b88628cd6,
--                  0x935212be3578a819, 0x82a21f49917ddc96, 0x8d322bdda27912d1, 0x99b2387a6e756238, 0x8ac2451ffb82140a,
--                  0x8ac251ce4fb2a63f, 0x93e25e85711ece75, 0x82b26b4565e27cdd, 0x9e02780e341ddf29, 0xa2d284dfe1f56380,
--                  0xab4291ba7591bb6f, 0x86129e9df51fdee1, 0xa352ab8a66d10f12, 0xafb2b87fd0dad98f, 0xa572c57e39771b2e,
--                  0x9002d285a6e4030b, 0x9d12df961f641589, 0x71c2ecafa93e2f56, 0xaea2f9d24abd886a, 0x86f306fe0a31b715,
--                  0x89531432edeeb2fd, 0x8a932170fc4cd831, 0xa1d32eb83ba8ea31, 0x93233c08b26416ff, 0xab23496266e3fa2c,
--                  0xa92356c55f929ff0, 0xa8f36431a2de883a, 0xa4e371a7373aa9ca, 0xa3037f26231e7549, 0xa0b38cae6d05d865,
--                  0xa3239a401b7140ee, 0xad43a7db34e59ff6, 0x9543b57fbfec6cf4, 0xa083c32dc313a8e4, 0x7fe3d0e544ede173,
--                  0x8ad3dea64c123422, 0xa943ec70df1c5174, 0xa413fa4504ac801b, 0x8bd40822c367a024, 0xaf04160a21f72e29,
--                  0xa3d423fb27094689, 0xab8431f5d950a896, 0x88843ffa3f84b9d4, 0x48944e086061892d, 0xae745c2042a7d231,
--                  0x9c946a41ed1d0057, 0xa1e4786d668b3236, 0x73c486a2b5c13cd0, 0xab1494e1e192aed1, 0x99c4a32af0d7d3de,
--                  0xabb4b17dea6db7d6, 0x7d44bfdad5362a27, 0x9054ce41b817c114, 0x98e4dcb299fddd0d, 0xa564eb2d81d8abfe,
--                  0xa5a4f9b2769d2ca6, 0x7a2508417f4531ee, 0xa82516daa2cf6641, 0xac65257de83f4eee, 0xabe5342b569d4f81,
--                  0x879542e2f4f6ad27, 0xa8a551a4ca5d920e, 0xa7856070dde910d1, 0x99b56f4736b527da, 0xa7a57e27dbe2c4ce,
--                  0x82958d12d497c7fd, 0xa4059c0827ff07cb, 0x9635ab07dd485429, 0xa245ba11fba87a02, 0x3c45c9268a5946b7,
--                  0xa195d84590998b92, 0x9ba5e76f15ad2148, 0xa985f6a320dceb70, 0xa60605e1b976dc08, 0x9e46152ae6cdf6f4,
--                  0xa636247eb03a5584, 0x984633dd1d1929fd, 0xa8e6434634ccc31f, 0xa28652b9febc8fb6, 0xa226623882552224,
--                  0xa85671c1c70833f5, 0x60368155d44ca973, 0x880690f4b19e9538, 0xa216a09e667f3bcc, 0x7a36b052fa75173e,
--                  0xada6c012750bdabe, 0x9c76cfdcddd47645, 0xae46dfb23c651a2e, 0xa7a6ef9298593ae4, 0xa9f6ff7df9519483,
--                  0x59d70f7466f42e87, 0xaba71f75e8ec5f73, 0xa6f72f8286ead089, 0xa7a73f9a48a58173, 0x90474fbd35d7cbfd,
--                  0xa7e75feb564267c8, 0x9b777024b1ab6e09, 0x986780694fde5d3f, 0x934790b938ac1cf6, 0xaaf7a11473eb0186,
--                  0xa207b17b0976cfda, 0x9f17c1ed0130c132, 0x91b7d26a62ff86f0, 0x7057e2f336cf4e62, 0xabe7f3878491c490,
--                  0xa6c80427543e1a11, 0x946814d2add106d9, 0xa1582589994cce12, 0x9998364c1eb941f7, 0xa9c8471a4623c7ac,
--                  0xaf2857f4179f5b20, 0xa01868d99b4492ec, 0x85d879cad931a436, 0x99988ac7d98a6699, 0x9d589bd0a478580f,
--                  0x96e8ace5422aa0db, 0x9ec8be05bad61778, 0xade8cf3216b5448b, 0xa478e06a5e0866d8, 0x85c8f1ae99157736,
--                  0x959902fed0282c8a, 0xa119145b0b91ffc5, 0xab2925c353aa2fe1, 0xae893737b0cdc5e4, 0xa88948b82b5f98e4,
--                  0xad395a44cbc8520e, 0xaf296bdd9a7670b2, 0xa1797d829fde4e4f, 0x7ca98f33e47a22a2, 0xa749a0f170ca07b9,
--                  0xa119b2bb4d53fe0c, 0x7c79c49182a3f090, 0xa579d674194bb8d4, 0x7829e86319e32323, 0xaad9fa5e8d07f29d,
--                  0xa65a0c667b5de564, 0x9c6a1e7aed8eb8bb, 0x963a309bec4a2d33, 0xa2aa42c980460ad7, 0xa16a5503b23e255c,
--                  0x650a674a8af46052, 0x9bca799e1330b358, 0xa58a8bfe53c12e58, 0x90fa9e6b5579fdbf, 0x889ab0e521356eba,
--                  0xa81ac36bbfd3f379, 0x97ead5ff3a3c2774, 0x97aae89f995ad3ad, 0xa5aafb4ce622f2fe, 0xa21b0e07298db665,
--                  0x94db20ce6c9a8952, 0xaedb33a2b84f15fa, 0xac1b468415b749b0, 0xa1cb59728de55939, 0x92ab6c6e29f1c52a,
--                  0xad5b7f76f2fb5e46, 0xa24b928cf22749e3, 0xa08ba5b030a10649, 0xafcbb8e0b79a6f1e, 0x823bcc1e904bc1d2,
--                  0xafcbdf69c3f3a206, 0xa08bf2c25bd71e08, 0xa89c06286141b33c, 0x811c199bdd85529c, 0xa48c2d1cd9fa652b,
--                  0x9b4c40ab5fffd07a, 0x912c544778fafb22, 0x928c67f12e57d14b, 0xa86c7ba88988c932, 0x71ac8f6d9406e7b5,
--                  0xaa0ca3405751c4da, 0x750cb720dcef9069, 0xac5ccb0f2e6d1674, 0xa88cdf0b555dc3f9, 0xa2fcf3155b5bab73,
--                  0xa1ad072d4a07897b, 0x955d1b532b08c968, 0xa15d2f87080d89f1, 0x93dd43c8eacaa1d6, 0x82ed5818dcfba487,
--                  0x5fed6c76e862e6d3, 0xa77d80e316c98397, 0x9a0d955d71ff6075, 0x9c2da9e603db3285, 0xa24dbe7cd63a8314,
--                  0x92ddd321f301b460, 0xa1ade7d5641c0657, 0xa72dfc97337b9b5e, 0xadae11676b197d16, 0xa42e264614f5a128,
--                  0xa30e3b333b16ee11, 0x839e502ee78b3ff6, 0xaa7e653924676d75, 0x92de7a51fbc74c83, 0xa77e8f7977cdb73f,
--                  0xa0bea4afa2a490d9, 0x948eb9f4867cca6e, 0xa1becf482d8e67f0, 0x91cee4aaa2188510, 0x9dcefa1bee615a27,
--                  0xa66f0f9c1cb64129, 0x93af252b376bba97, 0xacdf3ac948dd7273, 0x99df50765b6e4540, 0x9faf6632798844f8,
--                  0xa12f7bfdad9cbe13, 0xaeef91d802243c88, 0x874fa7c1819e90d8, 0xacdfbdba3692d513, 0x62efd3c22b8f71f1, 0x74afe9d96b2a23d9)
-- /Source
-- The table data is reused from the exact Float64 word list in `MathFuncs.Exp.jTable`.

/--
Julia source: base/special/exp.jl:178-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@assume_effects :nothrow function table_unpack(ind::Int32)
    ind = ind & 255 + 1 # 255 == length(J_TABLE) - 1
    j = getfield(J_TABLE, ind) # use getfield so the compiler can prove consistent
    jU = reinterpret(Float64, JU_CONST | (j&JU_MASK))
    jL = reinterpret(Float64, JL_CONST | (j>>8))
    return jU, jL
end
```
-/
def tableUnpack (ind : JInt .i32) : F64 × F64 :=
  let idx := (ind.val % 256).toNat
  let j := JuliaLean.MathFuncs.jTable.getD idx 0
  let (juMask, _, juConst, jlConst) := tableMasks
  (lit64 (Nat.lor juConst (Nat.land j juMask)),
   lit64 (Nat.lor jlConst (j / 256)))

private def expReduce64 (x : F64) (b : ExpBase) : JInt .i32 × F64 :=
  let nFloat := FP.muladd x (logBo256Inv b) magicRoundConst64
  let n := JInt.wrap .i32 (JuliaLean.base.float.reinterpret_Unsigned_Float64 nFloat).val
  let nFloat := FP.sub nFloat magicRoundConst64
  let r := FP.muladd nFloat (logBo256U b) x
  (n, FP.muladd nFloat (logBo256L b) r)

private def ofInt64Bits (bits : Int) : F64 :=
  Fl.ofBits (JInt.wrap .u64 bits).val.toNat

private def scaled64 (k : Int) (smallPart : F64) : F64 :=
  let bits := JInt.wrap .i64 (k * 2^52 + (JuliaLean.base.float.reinterpret_Signed_Float64 smallPart).val)
  JuliaLean.base.float.bitcast_to_float .f64 bits

private def subnormalScale64 (k : Int) (smallPart : F64) : F64 :=
  let twopk := JInt.wrap .u64 ((JInt.wrap .u64 (k + 53)).val * 2^52)
  let mantissa := (JuliaLean.base.float.reinterpret_Unsigned_Float64 smallPart).val
  let combined := JInt.wrap .u64 (twopk.val + mantissa)
  FP.mul (JuliaLean.base.float.bitcast_to_float .f64 combined) (lit64 0x3ca0000000000000)

/--
Julia source: base/special/exp.jl:207-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function exp_impl(x::Float64, base)
    T = Float64
    N_float = muladd(x, LogBo256INV(base, T), MAGIC_ROUND_CONST(T))
    N = reinterpret(UInt64, N_float) % Int32
    N_float -=  MAGIC_ROUND_CONST(T) #N_float now equals round(x*LogBo256INV(base, T))
    r = muladd(N_float, LogBo256U(base, T), x)
    r = muladd(N_float, LogBo256L(base, T), r)
    k = N >> 8
    jU, jL = table_unpack(N)
    small_part =  muladd(jU, expm1b_kernel(base, r), jL) + jU

    if !(abs(x) <= SUBNORM_EXP(base, T))
        isnan(x) && return x
        x >= MAX_EXP(base, T) && return Inf
        x <= MIN_EXP(base, T) && return 0.0
        if k <= -53
            # The UInt64 forces promotion. (Only matters for 32 bit systems.)
            twopk = ((k % UInt64) +% UInt64(53)) << 52
            return reinterpret(T, twopk +% reinterpret(UInt64, small_part))*0x1p-53
        end
        #k == 1024 && return (small_part * 2.0) * 0x1p1023
    end
    twopk = Int64(k) << 52
    return reinterpret(T, twopk + reinterpret(Int64, small_part))
end
```
-/
def expImpl64 (x : F64) (b : ExpBase) : F64 :=
  let (n, r) := expReduce64 x b
  let k := n.val.fdiv 256
  let (jU, jL) := tableUnpack n
  let smallPart := FP.add (FP.muladd jU (expm1bKernel b r) jL) jU
  if !(FP.le (FP.abs x) (subnormExp64 b)) then
    if FP.isnan x then x
    else if FP.le (maxExp64 b) x then FP.inf .f64
    else if FP.le x (minExp64 b) then FP.zero .f64
    else if k <= -53 then subnormalScale64 k smallPart
    else scaled64 k smallPart
  else scaled64 k smallPart

/--
Julia source: base/special/exp.jl:233-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function exp_impl(x::Float64, xlo::Float64, base)
    T = Float64
    N_float = muladd(x, LogBo256INV(base, T), MAGIC_ROUND_CONST(T))
    N = reinterpret(UInt64, N_float) % Int32
    N_float -=  MAGIC_ROUND_CONST(T) #N_float now equals round(x*LogBo256INV(base, T))
    r = muladd(N_float, LogBo256U(base, T), x)
    r = muladd(N_float, LogBo256L(base, T), r)
    k = N >> 8
    jU, jL = table_unpack(N)
    kern = expm1b_kernel(base, r)
    very_small = muladd(kern, jU*xlo, jL)
    hi, lo = Base.canonicalize2(1.0, kern)
    small_part = fma(jU, hi, muladd(jU, (lo+xlo), very_small))
    if !(abs(x) <= SUBNORM_EXP(base, T))
        isnan(x) && return x
        x >= MAX_EXP(base, T) && return Inf
        x <= MIN_EXP(base, T) && return 0.0
        if k <= -53
            # The UInt64 forces promotion. (Only matters for 32 bit systems.)
            twopk = ((k % UInt64) +% UInt64(53)) << 52
            return reinterpret(T, twopk +% reinterpret(UInt64, small_part))*0x1p-53
        end
        k == 1024 && return (small_part * 2.0) * 0x1p1023
    end
    twopk = Int64(k) << 52
    return reinterpret(T, twopk + reinterpret(Int64, small_part))
end
```
-/
def expImpl64Lo (x xlo : F64) (b : ExpBase) : F64 :=
  let (n, r) := expReduce64 x b
  let k := n.val.fdiv 256
  let (jU, jL) := tableUnpack n
  let kern := expm1bKernel b r
  let verySmall := FP.muladd kern (FP.mul jU xlo) jL
  let one := FP.ofInt .f64 1
  let (hi, lo) := JuliaLean.base.twiceprecision.canonicalize2 FP.add FP.sub one kern
  let smallPart := FP.fma jU hi (FP.muladd jU (FP.add lo xlo) verySmall)
  if !(FP.le (FP.abs x) (subnormExp64 b)) then
    if FP.isnan x then x
    else if FP.le (maxExp64 b) x then FP.inf .f64
    else if FP.le x (minExp64 b) then FP.zero .f64
    else if k <= -53 then subnormalScale64 k smallPart
    else if k == 1024 then FP.mul (FP.mul smallPart (lit64 0x4000000000000000)) (lit64 0x7fe0000000000000)
    else scaled64 k smallPart
  else scaled64 k smallPart

/--
Julia source: base/special/exp.jl:260-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function exp_impl_fast(x::Float64, base)
    T = Float64
    x >= MAX_EXP(base, T) && return Inf
    x <= -SUBNORM_EXP(base, T) && return 0.0
    N_float = muladd(x, LogBo256INV(base, T), MAGIC_ROUND_CONST(T))
    N = reinterpret(UInt64, N_float) % Int32
    N_float -=  MAGIC_ROUND_CONST(T) #N_float now equals round(x*LogBo256INV(base, T))
    r = muladd(N_float, LogBo256U(base, T), x)
    r = muladd(N_float, LogBo256L(base, T), r)
    k = N >> 8
    jU, _ = table_unpack(N)
    small_part =  muladd(jU, expm1b_kernel(base, r), jU)
    twopk = Int64(k) << 52
    return reinterpret(T, twopk + reinterpret(Int64, small_part))
end
```
-/
def expImplFast64 (x : F64) (b : ExpBase) : F64 :=
  if FP.le (maxExp64 b) x then FP.inf .f64
  else if FP.le x (FP.neg (subnormExp64 b)) then FP.zero .f64
  else
    let (n, r) := expReduce64 x b
    let k := n.val.fdiv 256
    let (jU, _) := tableUnpack n
    let smallPart := FP.muladd jU (expm1bKernel b r) jU
    scaled64 k smallPart

private def pow2Bits32 (p : Int) : F32 :=
  let p := JInt.wrap .i32 p
  let bits := JInt.wrap .u32 (p.val * 2^23)
  JuliaLean.base.float.bitcast_to_float .f32 bits

/--
Julia source: base/special/exp.jl:276-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function exp_impl(x::Float32, base)
    T = Float32
    N_float = round(x*LogBINV(base, T))
    N = unsafe_trunc(Int32, N_float)
    r = muladd(N_float, LogBU(base, T), x)
    r = muladd(N_float, LogBL(base, T), r)
    small_part = expb_kernel(base, r)
    power = (N+Int32(127))
    x > MAX_EXP(base, T) && return Inf32
    x < MIN_EXP(base, T) && return 0.0f0
    if x <= -SUBNORM_EXP(base, T)
        power += Int32(24)
        small_part *= Float32(0x1p-24)
    end
    if N == 128
        power -= Int32(1)
        small_part *= 2f0
    end
    return small_part * reinterpret(T, power << Int32(23))
end
```
-/
def expImpl32 (x : F32) (b : ExpBase) : F32 :=
  let nFloat := FP.roundI (FP.mul x (logBInv32 b))
  let n := FP.unsafeTrunc .i32 nFloat
  let r := FP.muladd nFloat (logBU32 b) x
  let r := FP.muladd nFloat (logBL32 b) r
  let smallPart := expbKernel32 b r
  let power := JInt.wrap .i32 (n.val + 127)
  if FP.lt (maxExp32 b) x then FP.inf .f32
  else if FP.lt x (minExp32 b) then FP.zero .f32
  else
    let (power, smallPart) :=
      if FP.le x (FP.neg (subnormExp32 b)) then
        (JInt.wrap .i32 (power.val + 24), FP.mul smallPart (lit32 0x33800000))
      else (power, smallPart)
    let (power, smallPart) :=
      if n.val == 128 then (JInt.wrap .i32 (power.val - 1), FP.mul smallPart (FP.ofInt .f32 2))
      else (power, smallPart)
    FP.mul smallPart (pow2Bits32 power.val)

/--
Julia source: base/special/exp.jl:297-308 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function exp_impl_fast(x::Float32, base)
    T = Float32
    x >= MAX_EXP(base, T) && return Inf32
    x <= -SUBNORM_EXP(base, T) && return 0f0
    N_float = round(x*LogBINV(base, T))
    N = unsafe_trunc(Int32, N_float)
    r = muladd(N_float, LogBU(base, T), x)
    r = muladd(N_float, LogBL(base, T), r)
    small_part = expb_kernel(base, r)
    twopk = reinterpret(T, (N+Int32(127)) << Int32(23))
    return twopk*small_part
end
```
-/
def expImplFast32 (x : F32) (b : ExpBase) : F32 :=
  if FP.le (maxExp32 b) x then FP.inf .f32
  else if FP.le x (FP.neg (subnormExp32 b)) then FP.zero .f32
  else
    let nFloat := FP.roundI (FP.mul x (logBInv32 b))
    let n := FP.unsafeTrunc .i32 nFloat
    let r := FP.muladd nFloat (logBU32 b) x
    let r := FP.muladd nFloat (logBL32 b) r
    let smallPart := expbKernel32 b r
    FP.mul (pow2Bits32 (n.val + 127)) smallPart

/--
Julia source: base/special/exp.jl:310-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function exp_impl(a::Float16, base)
    T = Float32
    x = T(a)
    N_float = round(x*LogBINV(base, T))
    N = unsafe_trunc(Int32, N_float)
    r = muladd(N_float, LogB(base, Float16), x)
    small_part = expb_kernel(base, r)
    if !(abs(x) <= 25)
        x > 16 && return Inf16
        x < 25 && return zero(Float16)
    end
    twopk = reinterpret(T, (N+Int32(127)) << Int32(23))
    return Float16(twopk*small_part)
end
```
-/
def expImpl16 (a : FV .f16) (b : ExpBase) : FV .f16 :=
  let x : F32 := FP.conv a
  let nFloat := FP.roundI (FP.mul x (logBInv32 b))
  let n := FP.unsafeTrunc .i32 nFloat
  let r := FP.muladd nFloat (logB16 b) x
  let smallPart := expbKernel32 b r
  if !(FP.le (FP.abs x) (FP.ofInt .f32 25)) then
    if FP.lt (FP.ofInt .f32 16) x then FP.inf .f16
    else if FP.lt x (FP.ofInt .f32 25) then FP.zero .f16
    else FP.conv (FP.mul (pow2Bits32 (n.val + 127)) smallPart)
  else FP.conv (FP.mul (pow2Bits32 (n.val + 127)) smallPart)

/-- The `exp_impl` overloads for Float16/32/64. -/
def expImpl (b : ExpBase) : (T : FTy) → FV T → FV T
  | .f16, x => expImpl16 x b
  | .f32, x => expImpl32 x b
  | .f64, x => expImpl64 x b

/--
Julia source: base/special/exp.jl:325-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
for (func, fast_func, base) in ((:exp2,  :exp2_fast,  Val(2)),
                                (:exp,   :exp_fast,   Val(:ℯ)),
                                (:exp10, :exp10_fast, Val(10)))
    @eval begin
        @noinline $func(x::Union{Float16,Float32,Float64}) = exp_impl(x, $base)
        @noinline $fast_func(x::Union{Float32,Float64}) = exp_impl_fast(x, $base)
    end
end
```
-/
def exp2 {T : FTy} (x : FV T) : FV T := expImpl .two T x
def exp {T : FTy} (x : FV T) : FV T := expImpl .e T x
def exp10 {T : FTy} (x : FV T) : FV T := expImpl .ten T x

def exp2Fast32 (x : F32) : F32 := expImplFast32 x .two
def expFast32 (x : F32) : F32 := expImplFast32 x .e
def exp10Fast32 (x : F32) : F32 := expImplFast32 x .ten
def exp2Fast64 (x : F64) : F64 := expImplFast64 x .two
def expFast64 (x : F64) : F64 := expImplFast64 x .e
def exp10Fast64 (x : F64) : F64 := expImplFast64 x .ten

/--
Julia source: base/special/exp.jl:391-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function exp2(x::Base.BitInteger)
    if x > 1023
        Inf64
    elseif x < -1074
        0.0
    elseif x <= -1023
        # if -1073 < x <= -1023 then Result will be a subnormal number
        # Hex literal with padding must be used to work on 32bit machine
        reinterpret(Float64, 0x0000_0000_0000_0001 << ((x + 1074) % UInt))
    else
        # We will cast everything to Int64 to avoid errors in case of Int128
        # If x is an Int128, and is outside the range of Int64, then it is not -1023<x<=1023
        reinterpret(Float64, (exponent_bias(Float64) + (x % Int64)) << (significand_bits(Float64) % UInt))
    end
end
```
-/
def exp2Int {t : IntTy} (x : JInt t) : F64 :=
  if x.val > 1023 then FP.inf .f64
  else if x.val < -1074 then FP.zero .f64
  else if x.val <= -1023 then
    let shift := (JInt.wrap .u64 (JInt.wrap (IntTy.promote t .i64) (x.val + 1074)).val).val.toNat
    Fl.ofBits (2 ^ shift)
  else
    let x64 := JInt.wrap .i64 x.val
    let exponent := JInt.wrap .i64 (1023 + x64.val)
    let bits := (JInt.wrap .u64 (JInt.wrap .i64 (exponent.val * 2^52)).val).val.toNat
    Fl.ofBits bits

structure Expm1Limits where
  max64 : F64
  min64 : F64
  max32 : F32
  min32 : F32
  max16 : FV .f16
  min16 : FV .f16

/--
Julia source: base/special/exp.jl:408-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
MAX_EXP(::Type{Float64}) =  709.7827128933845   # log 2^1023*(2-2^-52)
MIN_EXP(::Type{Float64}) = -37.42994775023705   # log 2^-54
MAX_EXP(::Type{Float32}) =  88.72284f0          # log 2^127 *(2-2^-23)
MIN_EXP(::Type{Float32}) = -17.32868f0          # log 2^-25
MAX_EXP(::Type{Float16}) =  Float16(11.09)      # log 2^15 *(2-2^-10)
MIN_EXP(::Type{Float16}) = -Float16(8.32)       # log 2^-12
```
-/
def expm1Limits : Expm1Limits :=
  { max64 := lit64 0x40862e42fefa39f4, min64 := lit64 0xc042b708872320e2
    max32 := lit32 0x42b17218, min32 := lit32 0xc18aa123
    max16 := FP.lit .f16 0x498c, min16 := FP.lit .f16 0xc829 }

structure Ln2Values where
  inv64 : F64
  neg64 : F64
  inv32 : F32
  neg32 : F32

/--
Julia source: base/special/exp.jl:415-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Ln2INV(::Type{Float64}) = 1.4426950408889634
Ln2(::Type{Float64}) = -0.6931471805599453
Ln2INV(::Type{Float32}) = 1.442695f0
Ln2(::Type{Float32}) = -0.6931472f0
```
-/
def ln2Values : Ln2Values :=
  { inv64 := lit64 0x3ff71547652b82fe, neg64 := lit64 0xbfe62e42fefa39ef
    inv32 := lit32 0x3fb8aa3b, neg32 := lit32 0xbf317218 }

private def twoMulFloatWith (haveFma : FTy → Bool) :
    {T : FTy} → FV T → FV T → FV T × FV T
  | .f64, x, y => JuliaLean.base.floatfuncs.twoMulFloat64Source (haveFma .f64)
      (fun x nb => JuliaLean.base.twiceprecision.truncbitsF64 x (JInt.wrap .i64 nb))
      JuliaLean.base.float.add_IEEEFloat JuliaLean.base.float.sub_IEEEFloat
      JuliaLean.base.float.mul_IEEEFloat JuliaLean.base.float.neg_IEEEFloat x y
  | .f32, x, y => JuliaLean.base.floatfuncs.two_mul_Small (Or.inr rfl)
      { haveFma := haveFma .f32, widen := JuliaLean.base.float.convertFloat .f64,
        narrow := JuliaLean.base.float.convertFloat .f32 }
      (fun a b c => FP.fma (T := .f32) a b c) x y
  | .f16, x, y => JuliaLean.base.floatfuncs.two_mul_Small (Or.inl rfl)
      { haveFma := haveFma .f16, widen := JuliaLean.base.float.convertFloat .f32,
        narrow := JuliaLean.base.float.convertFloat .f16 }
      (fun a b c => FP.fma (T := .f16) a b c) x y

private def exthornerStep {T : FTy} (haveFma : FTy → Bool) (p x hi lo : FV T) : FV T × FV T :=
  let (prod, err) := twoMulFloatWith haveFma hi x
  let hi' := FP.add p prod
  (hi', FP.fma lo x (FP.add (FP.sub prod (FP.sub hi' p)) err))

private def exthorner {T : FTy} (haveFma : FTy → Bool) (x p1 p2 p3 : FV T) : FV T × FV T :=
  let (hi, lo) := exthornerStep haveFma p2 x p3 (FP.zero T)
  exthornerStep haveFma p1 x hi lo

/--
Julia source: base/special/exp.jl:421-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function expm1_small(x::Float64)
    p = evalpoly(x, (0.16666666666666632, 0.04166666666666556, 0.008333333333401227,
                     0.001388888889068783, 0.00019841269447671544, 2.480157691845342e-5,
                     2.7558212415361945e-6, 2.758218402815439e-7, 2.4360682937111612e-8))
    p2 = exthorner(x, (1.0, .5, p))
    return fma(x, p2[1], x*p2[2])
end
```
-/
def expm1Small64With (haveFma : FTy → Bool) (x : F64) : F64 :=
  let p := horner64 x [lit64 0x3fc5555555555549, lit64 0x3fa55555555554b6,
    lit64 0x3f8111111111a9f3, lit64 0x3f56c16c16ce14c6, lit64 0x3f2a01a01159dd2d,
    lit64 0x3efa019f635825c4, lit64 0x3ec71e14bfe3db59, lit64 0x3e928295484734ee,
    lit64 0x3e5a2836aa646b96]
  let (hi, lo) := exthorner haveFma x (FP.ofInt .f64 1) (lit64 0x3fe0000000000000) p
  FP.fma x hi (FP.mul x lo)

def expm1Small64 (x : F64) : F64 := expm1Small64With (fun _ => true) x

/--
Julia source: base/special/exp.jl:428-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function expm1_small(x::Float32)
    p = evalpoly(x, (0.16666666f0, 0.041666627f0, 0.008333682f0,
                     0.0013908712f0, 0.0001933096f0))
    p2 = exthorner(x, (1f0, .5f0, p))
    return fma(x, p2[1], x*p2[2])
end
```
-/
def expm1Small32With (haveFma : FTy → Bool) (x : F32) : F32 :=
  let p := JuliaLean.MathCov.Exp.horner x JuliaLean.MathCov.C.expm1SmallP32
  let (hi, lo) := exthorner haveFma x (FP.ofInt .f32 1) (lit32 0x3f000000) p
  FP.fma x hi (FP.mul x lo)

def expm1Small32 (x : F32) : F32 := expm1Small32With (fun _ => true) x

/--
Julia source: base/special/exp.jl:435-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function expm1(x::Float64)
    T = Float64
    if -0.2876820724517809 <= x <= 0.22314355131420976
        return expm1_small(x)
    elseif !(abs(x)<=MIN_EXP(Float64))
        isnan(x) && return x
        x > MAX_EXP(Float64) && return Inf
        x < MIN_EXP(Float64) && return -1.0
    end

    N_float = muladd(x, LogBo256INV(Val(:ℯ), T), MAGIC_ROUND_CONST(T))
    N = reinterpret(UInt64, N_float) % Int32
    N_float -=  MAGIC_ROUND_CONST(T) #N_float now equals round(x*LogBo256INV(Val(:ℯ), T))
    r = muladd(N_float, LogBo256U(Val(:ℯ), T), x)
    r = muladd(N_float, LogBo256L(Val(:ℯ), T), r)
    k = Int64(N >> 8)
    jU, jL = table_unpack(N)
    p = expm1b_kernel(Val(:ℯ), r)
    twopk  = reinterpret(Float64, (1023+k) << 52)
    twopnk = reinterpret(Float64, (1023-k) << 52)
    k>=106 && return reinterpret(Float64, (1022+k) << 52)*(jU + muladd(jU, p, jL))*2
    k>=53 && return twopk*(jU + muladd(jU, p, (jL-twopnk)))
    k<=-2 && return twopk*(jU + muladd(jU, p, jL))-1
    return twopk*((jU-twopnk) + fma(jU, p, jL))
end
```
-/
def expm164With (haveFma : FTy → Bool) (x : F64) : F64 :=
  if FP.le (lit64 0xbfd269621134db92) x && FP.le x (lit64 0x3fcc8ff7c79a9a22) then expm1Small64With haveFma x
  else if !(FP.le (FP.abs x) expm1Limits.min64) then
    if FP.isnan x then x
    else if FP.lt expm1Limits.max64 x then FP.inf .f64
    else if FP.lt x expm1Limits.min64 then lit64 0xbff0000000000000
    else expm1Table64 x
  else expm1Table64 x
where
  expm1Table64 (x : F64) : F64 :=
    let (n, r) := expReduce64 x .e
    let k := n.val.fdiv 256
    let (jU, jL) := tableUnpack n
    let p := expm1bKernel .e r
    let twopk := ofInt64Bits ((1023 + k) * 2^52)
    let twopnk := ofInt64Bits ((1023 - k) * 2^52)
    if k >= 106 then
      FP.mul (FP.mul (ofInt64Bits ((1022 + k) * 2^52))
        (FP.add jU (FP.muladd jU p jL))) (FP.ofInt .f64 2)
    else if k >= 53 then FP.mul twopk (FP.add jU (FP.muladd jU p (FP.sub jL twopnk)))
    else if k <= -2 then FP.sub (FP.mul twopk (FP.add jU (FP.muladd jU p jL))) (FP.ofInt .f64 1)
    else FP.mul twopk (FP.add (FP.sub jU twopnk) (FP.fma jU p jL))

def expm164 (x : F64) : F64 := expm164With (fun _ => true) x

/--
Julia source: base/special/exp.jl:461-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function expm1(x::Float32)
    x > MAX_EXP(Float32) && return Inf32
    x < MIN_EXP(Float32) && return -1f0
    if -0.2876821f0 <=x <= 0.22314355f0
        return expm1_small(x)
    end
    x = Float64(x)
    N_float = round(x*Ln2INV(Float64))
    N = unsafe_trunc(Int64, N_float)
    r = muladd(N_float, Ln2(Float64), x)
    hi = evalpoly(r, (1.0, .5, 0.16666667546642386, 0.041666183019487026,
                      0.008332997481506921, 0.0013966479175977883, 0.0002004037059220124))
    small_part = r*hi
    twopk = reinterpret(Float64, (N+1023) << 52)
    return Float32(muladd(twopk, small_part, twopk-1.0))
end
```
-/
def expm1_32With (haveFma : FTy → Bool) (x : F32) : F32 :=
  if FP.lt expm1Limits.max32 x then FP.inf .f32
  else if FP.lt x expm1Limits.min32 then lit32 0xbf800000
  else if FP.le (lit32 0xbe934b11) x && FP.le x (lit32 0x3e647fbe) then expm1Small32With haveFma x
  else
    let xd : F64 := FP.conv x
    let nFloat := FP.roundI (FP.mul xd ln2Values.inv64)
    let n := FP.unsafeTrunc .i64 nFloat
    let r := FP.muladd nFloat ln2Values.neg64 xd
    let hi := JuliaLean.MathCov.Exp.horner r JuliaLean.MathCov.C.expm1Poly64For32
    let smallPart := FP.mul r hi
    let twopk := ofInt64Bits ((n.val + 1023) * 2^52)
    FP.conv (FP.muladd twopk smallPart (FP.sub twopk (FP.ofInt .f64 1)))

def expm1_32 (x : F32) : F32 := expm1_32With (fun _ => true) x

/--
Julia source: base/special/exp.jl:478-492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function expm1(x::Float16)
    x > MAX_EXP(Float16) && return Inf16
    x < MIN_EXP(Float16) && return Float16(-1.0)
    x = Float32(x)
    if -0.2876821f0 <=x <= 0.22314355f0
        return Float16(x*evalpoly(x, (1f0, .5f0, 0.16666628f0, 0.04166785f0, 0.008351848f0, 0.0013675707f0)))
    end
    N_float = round(x*Ln2INV(Float32))
    N = unsafe_trunc(Int32, N_float)
    r = muladd(N_float, Ln2(Float32), x)
    hi = evalpoly(r, (1f0, .5f0, 0.16666667f0, 0.041665863f0, 0.008333111f0, 0.0013981499f0, 0.00019983904f0))
    small_part = r*hi
    twopk = reinterpret(Float32, (N+Int32(127)) << Int32(23))
    return Float16(muladd(twopk, small_part, twopk-1f0))
end
```
-/
def expm1_16 (x : FV .f16) : FV .f16 :=
  if FP.lt expm1Limits.max16 x then FP.inf .f16
  else if FP.lt x expm1Limits.min16 then FP.ofInt .f16 (-1)
  else
    let x32 : F32 := FP.conv x
    if FP.le (lit32 0xbe934b11) x32 && FP.le x32 (lit32 0x3e647fbe) then
      let p := JuliaLean.MathCov.Exp.horner x32 JuliaLean.MathCov.C.expm1SmallPoly16
      FP.conv (FP.mul x32 p)
    else
      let nFloat := FP.roundI (FP.mul x32 ln2Values.inv32)
      let n := FP.unsafeTrunc .i32 nFloat
      let r := FP.muladd nFloat ln2Values.neg32 x32
      let hi := JuliaLean.MathCov.Exp.horner r JuliaLean.MathCov.C.expm1Poly16
      let smallPart := FP.mul r hi
      let twopk := pow2Bits32 (n.val + 127)
      FP.conv (FP.muladd twopk smallPart (FP.sub twopk (FP.ofInt .f32 1)))
end JuliaLean.base.special.exp

namespace JuliaLean.base.twiceprecision
open JuliaLean.MathFuncs (ExpBase)

-- Source: base/twiceprecision.jl:795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- placed here to break an import cycle with twiceprecision
def expAllowingTwice64Bound (x : TwicePrecision F64) : F64 :=
  expAllowingTwice64 (fun hi lo (_ : Unit) => JuliaLean.base.special.exp.expImpl64Lo hi lo .e) () x

end JuliaLean.base.twiceprecision

