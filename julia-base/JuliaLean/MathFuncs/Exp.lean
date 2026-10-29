import JuliaLean.MathFuncs.Prelude

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

/-- `_exthorner(i, x, p, hi, lo)` with `pi = p[i]`; `base/math.jl:203-210`. -/
def exthornerStep (p x hi lo : F64) : F64 × F64 :=
  let (prod, err) := twoMul hi x
  let hi' := F64.add p prod
  (hi', F64.fma lo x (F64.add (F64.sub prod (F64.sub hi' p)) err))

/-- `exthorner(x, (p1, p2, p3))`; `base/math.jl:196-201`. -/
def exthorner (x : F64) (p : F64 × F64 × F64) : F64 × F64 :=
  let (hi, lo) := exthornerStep p.2.1 x p.2.2 F64.zero
  exthornerStep p.1 x hi lo

/-- `expm1_small(x::Float64)`; `base/special/exp.jl:419-425`. -/
def expm1Small (x : F64) : F64 :=
  let p := horner x [lit 0x3fc5555555555549, lit 0x3fa55555555554b6, lit 0x3f8111111111a9f3,
    lit 0x3f56c16c16ce14c6, lit 0x3f2a01a01159dd2d, lit 0x3efa019f635825c4,
    lit 0x3ec71e14bfe3db59, lit 0x3e928295484734ee, lit 0x3e5a2836aa646b96]
  let p2 := exthorner x (F64.one, lit 0x3fe0000000000000, p)
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
