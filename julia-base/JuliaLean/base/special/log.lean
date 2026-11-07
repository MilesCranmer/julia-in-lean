import JuliaLean.Core
import JuliaLean.base.special.exp
import JuliaLean.base.float

/-!
Model of the Float64 logarithms of `base/special/log.jl`, Julia master `bbfa0ce4150`:
`log`, `log2`, `log10`, `log1p` (Tang's table-driven algorithm) and `_log_ext`, the
double-word logarithm used by `^`. Table entries are Float64 bit patterns.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- The `base` argument of `_log`: `Val(:ℯ)`, `Val(2)`, `Val(10)`; `base/special/log.jl:254-256`. -/
inductive LogBase
  | e
  | two
  | ten
  deriving DecidableEq, Repr

/-- `t_log_Float64`: pairs `(l_hi, l_lo)` with `l_hi + l_lo ≈ log(1 + j/128)`, `j = 0:128`;
`base/special/log.jl:29-74`. -/
def tLogFloat64 : List (Nat × Nat) :=
  [(0x0000000000000000, 0x0000000000000000),
   (0x3f7fe02a6b200000, 0xbd6f30ee07912df9),
   (0x3f8fc0a8b1000000, 0xbd5fe0e183092c59),
   (0x3f97b91b07d80000, 0xbd62772ab6c0559c),
   (0x3f9f829b0e780000, 0x3d2980267c7e09e4),
   (0x3fa39e87ba000000, 0xbd642a056fea4dfd),
   (0x3fa77458f6340000, 0xbd62303b9cb0d5e1),
   (0x3fab42dd71180000, 0x3d671bec28d14c7e),
   (0x3faf0a30c0100000, 0x3d662a6617cc9717),
   (0x3fb16536eea40000, 0xbd60a3e2f3b47d18),
   (0x3fb341d7961c0000, 0xbd4717b6b33e44f8),
   (0x3fb51b073f060000, 0x3d383f69278e686a),
   (0x3fb6f0d28ae60000, 0xbd62968c836cc8c2),
   (0x3fb8c345d6320000, 0xbd5937c294d2f567),
   (0x3fba926d3a4a0000, 0x3d6aac6ca17a4554),
   (0x3fbc5e548f5c0000, 0xbd4c5e7514f4083f),
   (0x3fbe27076e2a0000, 0x3d6e5cbd3d50fffc),
   (0x3fbfec9131dc0000, 0xbd354555d1ae6607),
   (0x3fc0d77e7cd10000, 0xbd6c69a65a23a170),
   (0x3fc1b72ad52f0000, 0x3d69e80a41811a39),
   (0x3fc29552f8200000, 0xbd35b967f4471dfc),
   (0x3fc371fc201f0000, 0xbd6c22f10c9a4ea8),
   (0x3fc44d2b6ccb0000, 0x3d6f4799f4f6543e),
   (0x3fc526e5e3a20000, 0xbd62f21746ff8a47),
   (0x3fc5ff3070a80000, 0xbd6b0b0de3077d7e),
   (0x3fc6d60fe71a0000, 0xbd56f1b955c4d1da),
   (0x3fc7ab8902110000, 0xbd537b720e4a694b),
   (0x3fc87fa065210000, 0xbd5b77b7effb7f41),
   (0x3fc9525a9cf40000, 0x3d65ad1d904c1d4e),
   (0x3fca23bc1fe30000, 0xbd62a739b23b93e1),
   (0x3fcaf3c94e810000, 0xbd600349cc67f9b2),
   (0x3fcbc286742e0000, 0xbd6cca75818c5dbc),
   (0x3fcc8ff7c79b0000, 0xbd697794f689f843),
   (0x3fcd5c216b500000, 0xbd611ba91bbca682),
   (0x3fce27076e2b0000, 0xbd3a342c2af0003c),
   (0x3fcef0adcbdc0000, 0x3d664d948637950e),
   (0x3fcfb9186d5e0000, 0x3d5f1546aaa3361c),
   (0x3fd0402594b50000, 0xbd67df928ec217a5),
   (0x3fd0a324e2738000, 0x3d50e35f73f7a018),
   (0x3fd1058bf9ae8000, 0xbd6a9573b02faa5a),
   (0x3fd1675cabab8000, 0x3d630701ce63eab9),
   (0x3fd1c898c1698000, 0x3d59fafbc68e7540),
   (0x3fd22941fbcf8000, 0xbd3a6976f5eb0963),
   (0x3fd2895a13de8000, 0x3d3a8d7ad24c13f0),
   (0x3fd2e8e2bae10000, 0x3d5d309c2cc91a85),
   (0x3fd347dd9a988000, 0xbd25594dd4c58092),
   (0x3fd3a64c55698000, 0xbd6d0b1c68651946),
   (0x3fd4043086868000, 0x3d63f1de86093efa),
   (0x3fd4618bc21c8000, 0xbd609ec17a426426),
   (0x3fd4be5f95778000, 0xbd3d7c92cd9ad824),
   (0x3fd51aad872e0000, 0xbd3f4bd8db0a7cc1),
   (0x3fd5767717458000, 0xbd62c9d5b2a49af9),
   (0x3fd5d1bdbf580000, 0x3d4394a11b1c1ee4),
   (0x3fd62c82f2ba0000, 0xbd6c356848506ead),
   (0x3fd686c81e9b0000, 0x3d54aec442be1015),
   (0x3fd6e08eaa2b8000, 0x3d60f1c609c98c6c),
   (0x3fd739d7f6bc0000, 0xbd67fcb18ed9d603),
   (0x3fd792a55fdd8000, 0xbd6c2ec1f512dc03),
   (0x3fd7eaf83b828000, 0x3d67e1b259d2f3da),
   (0x3fd842d1da1e8000, 0x3d462e927628cbc2),
   (0x3fd89a3386c18000, 0xbd6ed2a52c73bf78),
   (0x3fd8f11e87368000, 0xbd5d3881e8962a96),
   (0x3fd947941c210000, 0x3d56faba4cdd147d),
   (0x3fd99d9581180000, 0xbd5f753456d113b8),
   (0x3fd9f323ecbf8000, 0x3d584bf2b68d766f),
   (0x3fda484090e58000, 0x3d6d8515fe535b87),
   (0x3fda9cec9a9a0000, 0x3d40931a909fea5e),
   (0x3fdaf12932478000, 0xbd3e53bb31eed7a9),
   (0x3fdb44f77bcc8000, 0x3d4ec5197ddb55d3),
   (0x3fdb985896930000, 0x3d50fb598fb14f89),
   (0x3fdbeb4d9da70000, 0x3d5b7bf7861d37ac),
   (0x3fdc3dd7a7cd8000, 0x3d66a6b9d9e0a5bd),
   (0x3fdc8ff7c79a8000, 0x3d5a21ac25d81ef3),
   (0x3fdce1af0b860000, 0xbd48290905a86aa6),
   (0x3fdd32fe7e010000, 0xbd542a9e21373414),
   (0x3fdd83e7258a0000, 0x3d679f2828add176),
   (0x3fddd46a04c20000, 0xbd6dafa08cecadb1),
   (0x3fde24881a7c8000, 0xbd53d9e34270ba6b),
   (0x3fde744261d68000, 0x3d3e1f8df68dbcf3),
   (0x3fdec399d2468000, 0x3d49802eb9dca7e7),
   (0x3fdf128f5faf0000, 0x3d3bb2cd720ec44c),
   (0x3fdf6123fa700000, 0x3d645630a2b61e5b),
   (0x3fdfaf588f790000, 0xbd49c24ca098362b),
   (0x3fdffd2e08580000, 0xbd46cf54d05f9367),
   (0x3fe02552a5a5c000, 0x3d60fec69c695d7f),
   (0x3fe04bdf9da94000, 0xbd692d9a033eff75),
   (0x3fe0723e5c1cc000, 0x3d6f404e57963891),
   (0x3fe0986f4f574000, 0xbd55be8dc04ad601),
   (0x3fe0be72e4254000, 0xbd657d49676844cc),
   (0x3fe0e44985d1c000, 0x3d5917edd5cbbd2d),
   (0x3fe109f39e2d4000, 0x3d592dfbc7d93617),
   (0x3fe12f7195940000, 0xbd6043acfedce638),
   (0x3fe154c3d2f4c000, 0x3d65e9a98f33a396),
   (0x3fe179eabbd88000, 0x3d69a0bfc60e6fa0),
   (0x3fe19ee6b467c000, 0x3d52dd98b97baef0),
   (0x3fe1c3b81f714000, 0xbd3eda1b58389902),
   (0x3fe1e85f5e704000, 0x3d1a07bd8b34be7c),
   (0x3fe20cdcd192c000, 0xbd64926cafc2f08a),
   (0x3fe23130d7bec000, 0xbd17afa4392f1ba7),
   (0x3fe2555bce990000, 0xbd506987f78a4a5e),
   (0x3fe2795e1289c000, 0xbd5dca290f81848d),
   (0x3fe29d37fec2c000, 0xbd5eea6f465268b4),
   (0x3fe2c0e9ed448000, 0x3d5d1772f5386374),
   (0x3fe2e47436e40000, 0x3d334202a10c3491),
   (0x3fe307d7334f0000, 0x3d60be1fb590a1f5),
   (0x3fe32b1339120000, 0x3d6d71320556b67b),
   (0x3fe34e289d9d0000, 0xbd6e2ce9146d277a),
   (0x3fe37117b5474000, 0x3d4ed71774092113),
   (0x3fe393e0d3564000, 0xbd65e6563bbd9fc9),
   (0x3fe3b6844a000000, 0xbd3eea838909f3d3),
   (0x3fe3d9026a714000, 0x3d66faa404263d0b),
   (0x3fe3fb5b84d18000, 0xbd60bda4b162afa3),
   (0x3fe41d8fe8468000, 0xbd5aa33736867a17),
   (0x3fe43f9fe2f9c000, 0x3d5ccef4e4f736c2),
   (0x3fe4618bc21c4000, 0x3d6ec27d0b7b37b3),
   (0x3fe48353d1ea8000, 0x3d51bee7abd17660),
   (0x3fe4a4f85db04000, 0xbd244fdd840b8591),
   (0x3fe4c679afcd0000, 0xbd61c64e971322ce),
   (0x3fe4e7d811b74000, 0x3d6bb09cb0985646),
   (0x3fe50913cc018000, 0xbd6794b434c5a4f5),
   (0x3fe52a2d265bc000, 0x3d46abb9df22bc57),
   (0x3fe54b2467998000, 0x3d6497a915428b44),
   (0x3fe56bf9d5b40000, 0xbd58cd7dc73bd194),
   (0x3fe58cadb5cd8000, 0xbd49db3db43689b4),
   (0x3fe5ad404c358000, 0x3d6f2cfb29aaa5f0),
   (0x3fe5cdb1dc6c0000, 0x3d67648cf6e3c5d7),
   (0x3fe5ee02a9240000, 0x3d667570d6095fd2),
   (0x3fe60e32f4478000, 0x3d51b194f912b417),
   (0x3fe62e42fefa4000, 0xbd48432a1b0e2634)]

/-- `logbU(Float64, base)`; `base/special/log.jl:144-148`. -/
def logbU : LogBase → F64
  | .two => lit 0x3ff71547652b82fe
  | .e => lit 0x3ff0000000000000
  | .ten => lit 0x3fdbcb7b1526e50e

/-- `logbL(Float64, base)`; `base/special/log.jl:145-149`. -/
def logbL : LogBase → F64
  | .two => lit 0x3c7777d0ffda0d24
  | .e => lit 0x0000000000000000
  | .ten => lit 0x3c695355baaafad3

/-- `unsafe_trunc(Int, x)` for a finite `x` whose truncation fits in an `Int`. -/
private def truncToInt (x : F64) : Int :=
  let (n, d) := F64.toRat x
  n.tdiv d

/-- `log_proc1(y, mf, F, f, base)` for Float64; `base/special/log.jl:152-181`. -/
def logProc1 (y mf F f : F64) (b : LogBase) : F64 :=
  let jp := truncToInt (F64.mul (lit 0x4060000000000000) F) - 127
  let (hiB, loB) := tLogFloat64.getD (jp - 1).toNat (0, 0)
  let lHi := F64.add (F64.mul mf (lit 0x3fe62e42fefa4000)) (lit hiB)
  let lLo := F64.add (F64.mul mf (lit 0xbd48432a1b0e2634)) (lit loB)
  let u := F64.div (F64.mul (lit 0x4000000000000000) f) (F64.add y F)
  let v := F64.mul u u
  let q := F64.mul (F64.mul u v) (horner v [lit 0x3fb5555555550286, lit 0x3f8999a0bc712416])
  let mHi := logbU b
  let mLo := logbL b
  F64.fma mHi lHi (F64.fma mHi (F64.add u (F64.add q lLo)) (F64.mul mLo lHi))

/-- `log_proc2(f, base)` for Float64; `base/special/log.jl:184-207`. -/
def logProc2 (f : F64) (b : LogBase) : F64 :=
  let g := F64.div F64.one (F64.add (lit 0x4000000000000000) f)
  let u := F64.mul (F64.mul (lit 0x4000000000000000) f) g
  let v := F64.mul u u
  let q := F64.mul (F64.mul u v)
    (horner v [lit 0x3fb55555555554e6, lit 0x3f89999999bac6d4,
               lit 0x3f62492307f1519f, lit 0x3f3c8034c85dfff0])
  let mHi := logbU b
  let mLo := logbL b
  let w := F64.fma (F64.fma (F64.neg u) f (F64.mul (lit 0x4000000000000000) (F64.sub f u))) g q
  F64.fma mHi u (F64.fma mLo u (F64.mul mHi w))

/-- The `func` symbol passed to `_log` by `log`, `log2`, `log10`; `base/special/log.jl:254-256`. -/
def LogBase.funcName : LogBase → String
  | .e => "log"
  | .two => "log2"
  | .ten => "log10"

/-- `_log(x::Float64, base, func)`; a negative `x` throws `DomainError` through
`throw_complex_domainerror`; `base/special/log.jl:258-292`. -/
def logImpl (x : F64) (b : LogBase) : Jl F64 :=
  if F64.lt F64.zero x then
    if F64.eq x (F64.inf) then .ok x
    else if F64.lt (lit 0x3fee0fabfbc702a3) x && F64.lt x (lit 0x3ff1082b577d34ee) then
      .ok (logProc2 (F64.sub x F64.one) b)
    else
      let xu0 := bitsOf x
      let m0 : Int := (xu0 / 2^52 % 2048 : Nat)
      let (xu, m) : Nat × Int :=
        if m0 = 0 then
          let xs := F64.mul x (lit 0x4350000000000000)
          let xus := bitsOf xs
          (xus, ((xus / 2^52 % 2048 : Nat) : Int) - 54)
        else (xu0, m0)
      let m := m - 1023
      let y := ofBitsU (xu % 2^52 + 0x3ff0000000000000)
      let mf := F64.ofInt m
      let F := F64.sub (F64.add y (lit 0x42c0000000000000)) (lit 0x42c0000000000000)
      let f := F64.sub y F
      .ok (logProc1 y mf F f b)
  else if F64.eq x F64.zero then .ok (F64.inf true)
  else if F64.isnan x then .ok F64.nan
  else .error (.domainError b.funcName)

/-- `log(x::Float64)`; `base/special/log.jl:255`. -/
def log (x : F64) : Jl F64 := logImpl x .e

/-- `log2(x::Float64)`; `base/special/log.jl:254`. -/
def log2 (x : F64) : Jl F64 := logImpl x .two

/-- `log10(x::Float64)`; `base/special/log.jl:256`. -/
def log10 (x : F64) : Jl F64 := logImpl x .ten

/-- `log1p(x::Float64)`; `x < -1` throws `DomainError` through
`throw_complex_domainerror_neg1`; `base/special/log.jl:330-362`. -/
def log1p (x : F64) : Jl F64 :=
  if F64.lt (lit 0xbff0000000000000) x then
    if F64.eq x (F64.inf) then .ok x
    else if F64.lt (lit 0xbca0000000000000) x && F64.lt x (lit 0x3ca0000000000000) then .ok x
    else if F64.lt (lit 0xbfaf0540438fd5c4) x && F64.lt x (lit 0x3fb082b577d34ed8) then
      .ok (logProc2 x .e)
    else
      let z := F64.add F64.one x
      let zu := bitsOf z
      let s := ofBitsU (0x7fe0000000000000 + 2^64 - (zu - zu % 2^52))
      let m : Int := ((zu / 2^52 % 2048 : Nat) : Int) - 1023
      let c := if 0 < m then F64.sub F64.one (F64.sub z x) else F64.sub x (F64.sub z F64.one)
      let y := ofBitsU (zu % 2^52 + 0x3ff0000000000000)
      let mf := F64.ofInt m
      let F := F64.sub (F64.add y (lit 0x42c0000000000000)) (lit 0x42c0000000000000)
      let f := F64.add (F64.sub y F) (F64.mul c s)
      .ok (logProc1 y mf F f .e)
  else if F64.eq x (lit 0xbff0000000000000) then .ok (F64.inf true)
  else if F64.isnan x then .ok F64.nan
  else .error (.domainError "log1p")

/-- `t_log_table_compact`: pairs `(t, logctail)` where `t` packs `logc` with the bits of
`invc` in its low byte; `base/special/log.jl:412-540`. -/
def tLogTableCompact : List (Nat × Nat) :=
  [(0xbfd62c82f2b9c8b5, 0x3cfab42428375680),
   (0xbfd5d1bdbf5808b4, 0xbd1ca508d8e0f720),
   (0xbfd57677174558b3, 0xbd2362a4d5b6506d),
   (0xbfd51aad872df8b2, 0xbce684e49eb067d5),
   (0xbfd4be5f957778b1, 0xbd041b6993293ee0),
   (0xbfd4618bc21c60b0, 0x3d13d82f484c84cc),
   (0xbfd404308686a8af, 0x3cdc42f3ed820b3a),
   (0xbfd3a64c556948ae, 0x3d20b1c686519460),
   (0xbfd347dd9a9880ad, 0x3d25594dd4c58092),
   (0xbfd2e8e2bae120ac, 0x3d267b1e99b72bd8),
   (0xbfd2895a13de88ab, 0x3d15ca14b6cfb03f),
   (0xbfd2895a13de88ab, 0x3d15ca14b6cfb03f),
   (0xbfd22941fbcf78aa, 0xbd165a242853da76),
   (0xbfd1c898c16998a9, 0xbd1fafbc68e75404),
   (0xbfd1675cababa8a8, 0x3d1f1fc63382a8f0),
   (0xbfd1058bf9ae48a7, 0xbd26a8c4fd055a66),
   (0xbfd0a324e27390a6, 0xbd0c6bee7ef4030e),
   (0xbfd0402594b4d0a5, 0xbcf036b89ef42d7f),
   (0xbfd0402594b4d0a5, 0xbcf036b89ef42d7f),
   (0xbfcfb9186d5e40a4, 0x3d0d572aab993c87),
   (0xbfcef0adcbdc60a3, 0x3d2b26b79c86af24),
   (0xbfce27076e2af0a2, 0xbd172f4f543fff10),
   (0xbfcd5c216b4fc0a1, 0x3d21ba91bbca681b),
   (0xbfcc8ff7c79aa0a0, 0x3d27794f689f8434),
   (0xbfcc8ff7c79aa0a0, 0x3d27794f689f8434),
   (0xbfcbc286742d909f, 0x3d194eb0318bb78f),
   (0xbfcaf3c94e80c09e, 0x3cba4e633fcd9066),
   (0xbfca23bc1fe2b09d, 0xbd258c64dc46c1ea),
   (0xbfca23bc1fe2b09d, 0xbd258c64dc46c1ea),
   (0xbfc9525a9cf4509c, 0xbd2ad1d904c1d4e3),
   (0xbfc87fa06520d09b, 0x3d2bbdbf7fdbfa09),
   (0xbfc7ab890210e09a, 0x3d2bdb9072534a58),
   (0xbfc7ab890210e09a, 0x3d2bdb9072534a58),
   (0xbfc6d60fe719d099, 0xbd10e46aa3b2e266),
   (0xbfc5ff3070a79098, 0xbd1e9e439f105039),
   (0xbfc5ff3070a79098, 0xbd1e9e439f105039),
   (0xbfc526e5e3a1b097, 0xbd20de8b90075b8f),
   (0xbfc44d2b6ccb8096, 0x3d170cc16135783c),
   (0xbfc44d2b6ccb8096, 0x3d170cc16135783c),
   (0xbfc371fc201e9095, 0x3cf178864d27543a),
   (0xbfc29552f81ff094, 0xbd248d301771c408),
   (0xbfc1b72ad52f6093, 0xbd2e80a41811a396),
   (0xbfc1b72ad52f6093, 0xbd2e80a41811a396),
   (0xbfc0d77e7cd09092, 0x3d0a699688e85bf4),
   (0xbfc0d77e7cd09092, 0x3d0a699688e85bf4),
   (0xbfbfec9131dbe091, 0xbd2575545ca333f2),
   (0xbfbe27076e2b0090, 0x3d2a342c2af0003c),
   (0xbfbe27076e2b0090, 0x3d2a342c2af0003c),
   (0xbfbc5e548f5bc08f, 0xbd1d0c57585fbe06),
   (0xbfba926d3a4ae08e, 0x3d253935e85baac8),
   (0xbfba926d3a4ae08e, 0x3d253935e85baac8),
   (0xbfb8c345d631a08d, 0x3d137c294d2f5668),
   (0xbfb8c345d631a08d, 0x3d137c294d2f5668),
   (0xbfb6f0d28ae5608c, 0xbd269737c93373da),
   (0xbfb51b073f06208b, 0x3d1f025b61c65e57),
   (0xbfb51b073f06208b, 0x3d1f025b61c65e57),
   (0xbfb341d7961be08a, 0x3d2c5edaccf913df),
   (0xbfb341d7961be08a, 0x3d2c5edaccf913df),
   (0xbfb16536eea38089, 0x3d147c5e768fa309),
   (0xbfaf0a30c0118088, 0x3d2d599e83368e91),
   (0xbfaf0a30c0118088, 0x3d2d599e83368e91),
   (0xbfab42dd71198087, 0x3d1c827ae5d6704c),
   (0xbfab42dd71198087, 0x3d1c827ae5d6704c),
   (0xbfa77458f632c086, 0xbd2cfc4634f2a1ee),
   (0xbfa77458f632c086, 0xbd2cfc4634f2a1ee),
   (0xbfa39e87b9fec085, 0x3cf502b7f526feaa),
   (0xbfa39e87b9fec085, 0x3cf502b7f526feaa),
   (0xbf9f829b0e780084, 0xbd2980267c7e09e4),
   (0xbf9f829b0e780084, 0xbd2980267c7e09e4),
   (0xbf97b91b07d58083, 0xbd288d5493faa639),
   (0xbf8fc0a8b0fc0082, 0xbcdf1e7cf6d3a69c),
   (0xbf8fc0a8b0fc0082, 0xbcdf1e7cf6d3a69c),
   (0xbf7fe02a6b100081, 0xbd19e23f0dda40e4),
   (0xbf7fe02a6b100081, 0xbd19e23f0dda40e4),
   (0x0000000000000080, 0x0000000000000000),
   (0x0000000000000080, 0x0000000000000000),
   (0x3f8010157589007e, 0xbd10c76b999d2be8),
   (0x3f9020565893807c, 0xbd23dc5b06e2f7d2),
   (0x3f98492528c9007a, 0xbd2aa0ba325a0c34),
   (0x3fa0415d89e74078, 0x3d0111c05cf1d753),
   (0x3fa466aed42e0076, 0xbd2c167375bdfd28),
   (0x3fa894aa149fc074, 0xbd197995d05a267d),
   (0x3faccb73cdddc072, 0xbd1a68f247d82807),
   (0x3faeea31c006c071, 0xbd0e113e4fc93b7b),
   (0x3fb1973bd146606f, 0xbd25325d560d9e9b),
   (0x3fb3bdf5a7d1e06d, 0x3d2cc85ea5db4ed7),
   (0x3fb5e95a4d97a06b, 0xbd2c69063c5d1d1e),
   (0x3fb700d30aeac06a, 0x3cec1e8da99ded32),
   (0x3fb9335e5d594068, 0x3d23115c3abd47da),
   (0x3fbb6ac88dad6066, 0xbd1390802bf768e5),
   (0x3fbc885801bc4065, 0x3d2646d1c65aacd3),
   (0x3fbec739830a2063, 0xbd2dc068afe645e0),
   (0x3fbfe89139dbe062, 0xbd2534d64fa10afd),
   (0x3fc1178e8227e060, 0x3d21ef78ce2d07f2),
   (0x3fc1aa2b7e23f05f, 0x3d2ca78e44389934),
   (0x3fc2d1610c86805d, 0x3d039d6ccb81b4a1),
   (0x3fc365fcb015905c, 0x3cc62fa8234b7289),
   (0x3fc4913d8333b05a, 0x3d25837954fdb678),
   (0x3fc527e5e4a1b059, 0x3d2633e8e5697dc7),
   (0x3fc6574ebe8c1057, 0x3d19cf8b2c3c2e78),
   (0x3fc6f0128b757056, 0xbd25118de59c21e1),
   (0x3fc7898d85445055, 0xbd1c661070914305),
   (0x3fc8beafeb390053, 0xbd073d54aae92cd1),
   (0x3fc95a5adcf70052, 0x3d07f22858a0ff6f),
   (0x3fca93ed3c8ae050, 0xbd28724350562169),
   (0x3fcb31d8575bd04f, 0xbd0c358d4eace1aa),
   (0x3fcbd087383be04e, 0xbd2d4bc4595412b6),
   (0x3fcc6ffbc6f0104d, 0xbcf1ec72c5962bd2),
   (0x3fcdb13db0d4904b, 0xbd2aff2af715b035),
   (0x3fce530effe7104a, 0x3cc212276041f430),
   (0x3fcef5ade4dd0049, 0xbcca211565bb8e11),
   (0x3fcf991c6cb3b048, 0x3d1bcbecca0cdf30),
   (0x3fd07138604d5846, 0x3cf89cdb16ed4e91),
   (0x3fd0c42d67616045, 0x3d27188b163ceae9),
   (0x3fd1178e8227e844, 0xbd2c210e63a5f01c),
   (0x3fd16b5ccbacf843, 0x3d2b9acdf7a51681),
   (0x3fd1bf99635a6842, 0x3d2ca6ed5147bdb7),
   (0x3fd214456d0eb841, 0x3d0a87deba46baea),
   (0x3fd2bef07cdc903f, 0x3d2a9cfa4a5004f4),
   (0x3fd314f1e1d3603e, 0xbd28e27ad3213cb8),
   (0x3fd36b6776be103d, 0x3d116ecdb0f177c8),
   (0x3fd3c2527733303c, 0x3d183b54b606bd5c),
   (0x3fd419b423d5e83b, 0x3d08e436ec90e09d),
   (0x3fd4718dc271c83a, 0xbd2f27ce0967d675),
   (0x3fd4c9e09e173039, 0xbd2e20891b0ad8a4),
   (0x3fd522ae0738a038, 0x3d2ebe708164c759),
   (0x3fd57bf753c8d037, 0x3d1fadedee5d40ef),
   (0x3fd5d5bddf596036, 0xbd0a0b2a08a465dc)]

/-- `log_tab_unpack(t::UInt64)`, returning `(invc, logc)`; `base/special/log.jl:542-546`. -/
def logTabUnpack (t : Nat) : F64 × F64 :=
  (ofBitsU ((t % 256 + 0x1ff00) * 2^45), ofBitsU (t - t % 256))

/-- `_log_ext(xu::UInt64)` returning `(hi, lo)`; `base/special/log.jl:555-583`. -/
def logExt (xu : Nat) : F64 × F64 :=
  let xu : Nat := xu % 2^64
  let tmpU : Nat := (xu + 2^64 - 0x3fe6955500000000) % 2^64
  let tmp : Int := if tmpU ≥ 2^63 then (tmpU : Int) - 2^64 else (tmpU : Int)
  let z := ofBitsU (xu + 2^64 - (tmpU - tmpU % 2^52))
  let k := F64.ofInt (tmp.fdiv (2^52))
  let idx := ((tmp.fdiv (2^45)).emod 128).toNat + 1
  let (t, logctailB) := tLogTableCompact.getD (idx - 1) (0, 0)
  let logctail := lit logctailB
  let (invc, logc) := logTabUnpack t
  let r := F64.fma z invc (lit 0xbff0000000000000)
  let t1 := F64.muladd k (lit 0x3fe62e42fefa3800) logc
  let t2 := F64.add t1 r
  let lo1 := F64.muladd k (lit 0x3d2ef35793c76730) logctail
  let lo2 := F64.add (F64.sub t1 t2) r
  let ar := F64.mul (lit 0xbfe0000000000000) r
  let (ar2, lo3) := twoMul r ar
  let hi := F64.add t2 ar2
  let lo4 := F64.add (F64.sub t2 hi) ar2
  let p := horner r [lit 0xbfe5555555555560, lit 0x3fe0000000000006, lit 0xbfd999999959554e,
                     lit 0x3fd555555529a47a, lit 0xbfd2495b9b4845e9, lit 0x3fd0002b8b263fc3]
  let lo := F64.add (F64.add (F64.add lo1 lo2) lo3) (F64.muladd (F64.mul r ar2) p lo4)
  (hi, lo)

end JuliaLean.MathFuncs

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

/-!
# Model of `base/special/log.jl`

The Float32 and Float64 methods use typed IEEE values. Lookup tables remain visible
in their original Julia form below; exact words from the existing float models feed
the translated methods.
-/

namespace JuliaLean.base.special.log

open JuliaLean JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov
open JuliaLean.MathFuncs (LogBase)

abbrev F32 := FV .f32
abbrev F64 := FV .f64

private def lit32 (bits : Nat) : F32 := FP.lit .f32 bits
private def lit64 (bits : Nat) : F64 := FP.lit .f64 bits

private def horner64 (x : F64) : List F64 → F64
  | [] => FP.zero .f64
  | [c] => c
  | c :: cs => FP.muladd x (horner64 x cs) c

private def tLog64 : List (Nat × Nat) := JuliaLean.MathFuncs.tLogFloat64
private def tLog32 : List F64 := JuliaLean.MathCov.C.tLogFloat32
private def tLogCompact : List (Nat × Nat) := JuliaLean.MathFuncs.tLogTableCompact

/--
Julia source: base/special/log.jl:141-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
logb(::Type{Float32},::Val{2})  = 1.4426950408889634
logb(::Type{Float32},::Val{:ℯ}) = 1.0
logb(::Type{Float32},::Val{10}) = 0.4342944819032518
```
-/
def logb32 : LogBase → F64
  | .two => lit64 0x3ff71547652b82fe
  | .e => lit64 0x3ff0000000000000
  | .ten => lit64 0x3fdbcb7b1526e50e

/--
Julia source: base/special/log.jl:144-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
logbU(::Type{Float64},::Val{2})  = 1.4426950408889634
logbL(::Type{Float64},::Val{2})  = 2.0355273740931033e-17
logbU(::Type{Float64},::Val{:ℯ}) = 1.0
```
-/
def logbU64 : LogBase → F64
  | .two => lit64 0x3ff71547652b82fe
  | .e => lit64 0x3ff0000000000000
  | .ten => lit64 0x3fdbcb7b1526e50e

/--
Julia source: base/special/log.jl:147-149 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
logbL(::Type{Float64},::Val{:ℯ}) = 0.0
logbU(::Type{Float64},::Val{10}) = 0.4342944819032518
logbL(::Type{Float64},::Val{10}) = 1.098319650216765e-17
```
-/
def logbL64 : LogBase → F64
  | .two => lit64 0x3c7777d0ffda0d24
  | .e => lit64 0x0000000000000000
  | .ten => lit64 0x3c695355baaafad3

private def ln2Hi64 : F64 := lit64 0x3fe62e42fefa4000
private def ln2Lo64 : F64 := lit64 0xbd48432a1b0e2634
private def ln2For32 : F64 := lit64 0x3fe62e42fefa39ef

/--
Julia source: base/special/log.jl:152-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function log_proc1(y::Float64,mf::Float64,F::Float64,f::Float64,base=Val(:ℯ))
    jp = unsafe_trunc(Int,128.0*F)-127

    ## Steps 1 and 2
    Base.@assume_effects :nothrow :noub @inbounds hi,lo = t_log_Float64[jp]
    l_hi = mf* 0.6931471805601177 + hi
    l_lo = mf*-1.7239444525614835e-13 + lo

    ## Step 3
    # @inbounds u = f*c_invF[jp]
    # u = f/F
    # q = u*u*@horner(u,
    #                 -0x1.0_0000_0000_0001p-1,
    #                 +0x1.5_5555_5550_9ba5p-2,
    #                 -0x1.f_ffff_ffeb_6526p-3,
    #                 +0x1.9_99b4_dfed_6fe4p-3,
    #                 -0x1.5_5576_6647_2e04p-3)

    ## Step 3' (alternative)
    u = (2.0f)/(y+F)
    v = u*u
    q = u*v*@horner(v,
                    0.08333333333303913,
                    0.012500053168098584)

    ## Step 4
    m_hi = logbU(Float64, base)
    m_lo = logbL(Float64, base)
    return fma(m_hi, l_hi, fma(m_hi, (u + (q + l_lo)), m_lo*l_hi))
end
```
-/
def logProc1_64 (y mf bigF f : F64) (b : LogBase) : F64 :=
  let jp := (FP.unsafeTrunc .i64 (FP.mul (lit64 0x4060000000000000) bigF)).val - 127
  let (hiBits, loBits) := tLog64.getD (jp - 1).toNat (0, 0)
  let hi := lit64 hiBits
  let lo := lit64 loBits
  let lHi := FP.add (FP.mul mf ln2Hi64) hi
  let lLo := FP.add (FP.mul mf ln2Lo64) lo
  let two := FP.ofInt .f64 2
  let u := FP.div (FP.mul two f) (FP.add y bigF)
  let v := FP.mul u u
  let q := FP.mul (FP.mul u v) (horner64 v [lit64 0x3fb5555555550286, lit64 0x3f8999a0bc712416])
  FP.fma (logbU64 b) lHi
    (FP.fma (logbU64 b) (FP.add u (FP.add q lLo)) (FP.mul (logbL64 b) lHi))

/--
Julia source: base/special/log.jl:184-207 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function log_proc2(f::Float64,base=Val(:ℯ))
    ## Step 1
    g = 1.0/(2.0+f)
    u = 2.0*f*g
    v = u*u

    ## Step 2
    q = u*v*@horner(v,
                    0.08333333333333179,
                    0.012500000003771751,
                    0.0022321399879194482,
                    0.0004348877777076146)

    ## Step 3
    # based on:
    #   2(f-u) = 2(f(2+f)-2f)/(2+f) = 2f^2/(2+f) = fu
    #   2(f-u1-u2) - f*(u1+u2) = 0
    #   2(f-u1) - f*u1 = (2+f)u2
    #   u2 = (2(f-u1) - f*u1)/(2+f)

    m_hi = logbU(Float64, base)
    m_lo = logbL(Float64, base)
    return fma(m_hi, u, fma(m_lo, u, m_hi*fma(fma(-u,f,2(f-u)), g, q)))
end
```
-/
def logProc2_64 (f : F64) (b : LogBase) : F64 :=
  let one := FP.ofInt .f64 1
  let two := FP.ofInt .f64 2
  let g := FP.div one (FP.add two f)
  let u := FP.mul (FP.mul two f) g
  let v := FP.mul u u
  let q := FP.mul (FP.mul u v)
    (horner64 v [lit64 0x3fb55555555554e6, lit64 0x3f89999999bac6d4,
      lit64 0x3f62492307f1519f, lit64 0x3f3c8034c85dfff0])
  let w := FP.fma (FP.fma (FP.neg u) f (FP.mul two (FP.sub f u))) g q
  FP.fma (logbU64 b) u (FP.fma (logbL64 b) u (FP.mul (logbU64 b) w))

/--
Julia source: base/special/log.jl:210-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function log_proc1(y::Float32,mf::Float32,F::Float32,f::Float32,base=Val(:ℯ))
    jp = unsafe_trunc(Int,128.0f0*F)-127

    ## Steps 1 and 2
    Base.@assume_effects :nothrow :noub @inbounds hi = t_log_Float32[jp]
    l = mf*0.6931471805599453 + hi

    ## Step 3
    # @inbounds u = f*c_invF[jp]
    # q = u*u*@horner(u,
    #                 Float32(-0x1.00006p-1),
    #                 Float32(0x1.55546cp-2))

    ## Step 3' (alternative)
    u = (2f0f)/(y+F)
    v = u*u
    q = u*v*0.08333351f0

    ## Step 4
    Float32(logb(Float32, base)*(l + (u + q)))
end
```
-/
def logProc1_32 (y mf bigF f : F32) (b : LogBase) : F32 :=
  let jp := (FP.unsafeTrunc .i64 (FP.mul (lit32 0x43000000) bigF)).val - 127
  let hi := tLog32.getD (jp - 1).toNat (lit64 0x7ff8000000000000)
  let l := FP.add (FP.mul (FP.conv mf : F64) ln2For32) hi
  let two := FP.ofInt .f32 2
  let u := FP.div (FP.mul two f) (FP.add y bigF)
  let v := FP.mul u u
  let q := FP.mul (FP.mul u v) (lit32 0x3daaaac2)
  FP.conv (FP.mul (logb32 b) (FP.add l (FP.conv (FP.add u q) : F64)))

/--
Julia source: base/special/log.jl:233-249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function log_proc2(f::Float32,base=Val(:ℯ))
    ## Step 1
    # compute in higher precision
    u64 = Float64(2f0*f)/(2.0+f)
    u = Float32(u64)
    v = u*u

    ## Step 2
    q = u*v*@horner(v,
                    0.08333332f0,
                    0.012512346f0)

    ## Step 3: not required

    ## Step 4
    Float32(logb(Float32, base)*(u64 + q))
end
```
-/
def logProc2_32 (f : F32) (b : LogBase) : F32 :=
  let two32 := FP.ofInt .f32 2
  let two64 := FP.ofInt .f64 2
  let u64 : F64 := FP.div (FP.conv (FP.mul two32 f)) (FP.add two64 (FP.conv f))
  let u : F32 := FP.conv u64
  let v := FP.mul u u
  let q := FP.mul (FP.mul u v) (JuliaLean.MathCov.Exp.horner v [lit32 0x3daaaaa9, lit32 0x3c4d0095])
  FP.conv (FP.mul (logb32 b) (FP.add u64 (FP.conv q)))


/--
Julia source: base/special/log.jl:258-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _log(x::Float64, base, func::Symbol)
    if x > 0.0
        x == Inf && return x

        # Step 2
        if 0.9394130628134757 < x < 1.0644944589178595
            f = x-1.0
            return log_proc2(f, base)
        end

        # Step 3
        xu = reinterpret(UInt64,x)
        # `% Int` rather than `Int(...)` to preserve `:nothrow` (the shifted value fits in 11 bits)
        m = ((xu >> 52) % Int) & 0x07ff
        if m == 0 # x is subnormal
            x *= 1.8014398509481984e16 # 0x1p54, normalise significand
            xu = reinterpret(UInt64,x)
            m = ((xu >> 52) % Int) & 0x07ff - 54
        end
        m -= 1023
        y = reinterpret(Float64,(xu & 0x000f_ffff_ffff_ffff) | 0x3ff0_0000_0000_0000)

        mf = Float64(m)
        F = (y + 3.5184372088832e13) - 3.5184372088832e13 # 0x1p-7*round(0x1p7*y)
        f = y-F

        return log_proc1(y,mf,F,f,base)
    elseif x == 0.0
        return -Inf
    elseif isnan(x)
        return NaN
    else
        throw_complex_domainerror(func, x)
    end
end
```
-/
def logImpl64 (x : F64) (b : LogBase) : Jl F64 :=
  if FP.lt (FP.zero .f64) x then
    if FP.eq x (FP.inf .f64) then .ok x
    else if FP.lt (lit64 0x3fee0fabfbc702a3) x && FP.lt x (lit64 0x3ff1082b577d34ee) then
      .ok (logProc2_64 (FP.sub x (FP.ofInt .f64 1)) b)
    else
      let xu := x.toBits
      let m0 := xu / 2^52 % 2048
      let (xu, m) :=
        if m0 == 0 then
          let xScaled := FP.mul x (lit64 0x4350000000000000)
          let xBits := xScaled.toBits
          (xBits, (xBits / 2^52 % 2048 : Nat) - 54)
        else (xu, m0)
      let m : Int := (m : Int) - 1023
      let y := lit64 (xu % 2^52 + 0x3ff0000000000000)
      let mf := FP.ofInt .f64 m
      let shift := lit64 0x42c0000000000000
      let bigF := FP.sub (FP.add y shift) shift
      let f := FP.sub y bigF
      .ok (logProc1_64 y mf bigF f b)
  else if FP.eq x (FP.zero .f64) then .ok (FP.inf .f64 true)
  else if FP.isnan x then .ok (FP.nan .f64)
  else .error (.domainError (JuliaLean.MathFuncs.LogBase.funcName b))

/--
Julia source: base/special/log.jl:294-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _log(x::Float32, base, func::Symbol)
    if x > 0f0
        x == Inf32 && return x

        # Step 2
        if 0.939413f0 < x < 1.0644945f0
            f = x-1f0
            return log_proc2(f, base)
        end

        # Step 3
        xu = reinterpret(UInt32,x)
        m = Int(xu >> 23) & 0x00ff
        if m == 0 # x is subnormal
            x *= 3.3554432f7 # 0x1p25, normalise significand
            xu = reinterpret(UInt32,x)
            m = Int(xu >> 23) & 0x00ff - 25
        end
        m -= 127
        y = reinterpret(Float32,(xu & 0x007f_ffff) | 0x3f80_0000)

        mf = Float32(m)
        F = (y + 65536.0f0) - 65536.0f0 # 0x1p-7*round(0x1p7*y)
        f = y-F

        return log_proc1(y,mf,F,f,base)
    elseif x == 0f0
        return -Inf32
    elseif isnan(x)
        return NaN32
    else
        throw_complex_domainerror(func, x)
    end
end
```
-/
def logImpl32 (x : F32) (b : LogBase) : Jl F32 :=
  if FP.lt (FP.zero .f32) x then
    if FP.eq x (FP.inf .f32) then .ok x
    else if FP.lt (lit32 0x3f707d5f) x && FP.lt x (lit32 0x3f88415b) then
      .ok (logProc2_32 (FP.sub x (FP.ofInt .f32 1)) b)
    else
      let xu := x.toBits
      let m0 := xu / 2^23 % 256
      let (xu, m) :=
        if m0 == 0 then
          let xScaled := FP.mul x (lit32 0x4c000000)
          let xBits := xScaled.toBits
          (xBits, (xBits / 2^23 % 256 : Nat) - 25)
        else (xu, m0)
      let m : Int := (m : Int) - 127
      let y := lit32 (xu % 2^23 + 0x3f800000)
      let mf := FP.ofInt .f32 m
      let shift := lit32 0x47800000
      let bigF := FP.sub (FP.add y shift) shift
      let f := FP.sub y bigF
      .ok (logProc1_32 y mf bigF f b)
  else if FP.eq x (FP.zero .f32) then .ok (FP.inf .f32 true)
  else if FP.isnan x then .ok (FP.nan .f32)
  else .error (.domainError (JuliaLean.MathFuncs.LogBase.funcName b))

/--
Julia source: base/special/log.jl:251-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline log2(x::Float32)  = _log(x, Val(2),  :log2)
@noinline log(x::Float32)   = _log(x, Val(:ℯ), :log)
@noinline log10(x::Float32) = _log(x, Val(10), :log10)
@noinline log2(x::Float64)  = _log(x, Val(2),  :log2)
@noinline log(x::Float64)   = _log(x, Val(:ℯ), :log)
@noinline log10(x::Float64) = _log(x, Val(10), :log10)
```
-/
def log2_64 (x : F64) : Jl F64 := logImpl64 x .two
def log_64 (x : F64) : Jl F64 := logImpl64 x .e
def log10_64 (x : F64) : Jl F64 := logImpl64 x .ten
def log2_32 (x : F32) : Jl F32 := logImpl32 x .two
def log_32 (x : F32) : Jl F32 := logImpl32 x .e
def log10_32 (x : F32) : Jl F32 := logImpl32 x .ten
/--
Julia source: base/special/log.jl:330-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function log1p(x::Float64)
    if x > -1.0
        x == Inf && return x
        if -1.1102230246251565e-16 < x < 1.1102230246251565e-16
            return x # Inexact

        # Step 2
        elseif -0.06058693718652422 < x < 0.06449445891785943
            return log_proc2(x)
        end

        # Step 3
        z = 1.0 + x
        zu = reinterpret(UInt64,z)
        s = reinterpret(Float64,0x7fe0_0000_0000_0000 - (zu & 0xfff0_0000_0000_0000)) # 2^-m
        # `% Int` rather than `Int(...)` to preserve `:nothrow` (the shifted value fits in 11 bits)
        m = ((zu >> 52) % Int) & 0x07ff - 1023 # z cannot be subnormal
        c = m > 0 ? 1.0-(z-x) : x-(z-1.0) # 1+x = z+c exactly
        y = reinterpret(Float64,(zu & 0x000f_ffff_ffff_ffff) | 0x3ff0_0000_0000_0000)

        mf = Float64(m)
        F = (y + 3.5184372088832e13) - 3.5184372088832e13 # 0x1p-7*round(0x1p7*y)
        f = (y - F) + c*s #2^m(F+f) = 1+x = z+c

        log_proc1(y,mf,F,f)
    elseif x == -1.0
        -Inf
    elseif isnan(x)
        NaN
    else
        throw_complex_domainerror_neg1(:log1p, x)
    end
end
```
-/
def log1p64 (x : F64) : Jl F64 :=
  if FP.lt (lit64 0xbff0000000000000) x then
    if FP.eq x (FP.inf .f64) then .ok x
    else if FP.lt (lit64 0xbca0000000000000) x && FP.lt x (lit64 0x3ca0000000000000) then .ok x
    else if FP.lt (lit64 0xbfaf0540438fd5c4) x && FP.lt x (lit64 0x3fb082b577d34ed8) then
      .ok (logProc2_64 x .e)
    else
      let z := FP.add (FP.ofInt .f64 1) x
      let zu := z.toBits
      let mask := Nat.land zu 0xfff0000000000000
      let sbits := (0x7fe0000000000000 + 2^64 - mask) % 2^64
      let s := lit64 sbits
      let m := ((zu / 2^52 % 2048 : Nat) : Int) - 1023
      let c := if m > 0 then FP.sub (FP.ofInt .f64 1) (FP.sub z x)
        else FP.sub x (FP.sub z (FP.ofInt .f64 1))
      let y := lit64 (zu % 2^52 + 0x3ff0000000000000)
      let mf := FP.ofInt .f64 m
      let shift := lit64 0x42c0000000000000
      let bigF := FP.sub (FP.add y shift) shift
      let f := FP.add (FP.sub y bigF) (FP.mul c s)
      .ok (logProc1_64 y mf bigF f .e)
  else if FP.eq x (lit64 0xbff0000000000000) then .ok (FP.inf .f64 true)
  else if FP.isnan x then .ok (FP.nan .f64)
  else .error (.domainError "log1p")

/--
Julia source: base/special/log.jl:364-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function log1p(x::Float32)
    if x > -1f0
        x == Inf32 && return x
        if -5.9604645f-8 < x < 5.9604645f-8
            return x # Inexact
        # Step 2
        elseif -0.06058694f0 < x < 0.06449446f0
            return log_proc2(x)
        end

        # Step 3
        z = 1f0 + x
        zu = reinterpret(UInt32,z)
        s = reinterpret(Float32,0x7f000000 - (zu & 0xff80_0000)) # 2^-m
        m = Int(zu >> 23) & 0x00ff - 127 # z cannot be subnormal
        c = m > 0 ? 1f0-(z-x) : x-(z-1f0) # 1+x = z+c
        y = reinterpret(Float32,(zu & 0x007f_ffff) | 0x3f80_0000)

        mf = Float32(m)
        F = (y + 65536.0f0) - 65536.0f0 # 0x1p-7*round(0x1p7*y)
        f = (y - F) + s*c #2^m(F+f) = 1+x = z+c

        log_proc1(y,mf,F,f)
    elseif x == -1f0
        -Inf32
    elseif isnan(x)
        NaN32
    else
        throw_complex_domainerror_neg1(:log1p, x)
    end
end
```
-/
def log1p32 (x : F32) : Jl F32 :=
  if FP.lt (lit32 0xbf800000) x then
    if FP.eq x (FP.inf .f32) then .ok x
    else if FP.lt (lit32 0x33800000 |> FP.neg) x && FP.lt x (lit32 0x33800000) then .ok x
    else if FP.lt (lit32 0xbd782a03) x && FP.lt x (lit32 0x3d8415ac) then
      .ok (logProc2_32 x .e)
    else
      let z := FP.add (FP.ofInt .f32 1) x
      let zu := z.toBits
      let mask := Nat.land zu 0xff800000
      let sbits := (0x7f000000 + 2^32 - mask) % 2^32
      let s := lit32 sbits
      let m := ((zu / 2^23 % 256 : Nat) : Int) - 127
      let c := if m > 0 then FP.sub (FP.ofInt .f32 1) (FP.sub z x)
        else FP.sub x (FP.sub z (FP.ofInt .f32 1))
      let y := lit32 (zu % 2^23 + 0x3f800000)
      let mf := FP.ofInt .f32 m
      let shift := lit32 0x47800000
      let bigF := FP.sub (FP.add y shift) shift
      let f := FP.add (FP.sub y bigF) (FP.mul s c)
      .ok (logProc1_32 y mf bigF f .e)
  else if FP.eq x (lit32 0xbf800000) then .ok (FP.inf .f32 true)
  else if FP.isnan x then .ok (FP.nan .f32)
  else .error (.domainError "log1p")

-- Source: base/special/log.jl:29-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const t_log_Float64 = ((0.0,0.0),(0.007782140442941454,-8.865052917267247e-13),
--     (0.015504186536418274,-4.530198941364935e-13),(0.0231670592820592,-5.248209479295644e-13),
--     (0.03077165866670839,4.529814257790929e-14),(0.0383188643027097,-5.730994833076631e-13),
--     (0.04580953603181115,-5.16945692881222e-13),(0.053244514518155484,6.567993368985218e-13),
--     (0.06062462181580486,6.299848199383311e-13),(0.06795066190898069,-4.729424109166329e-13),
--     (0.07522342123775161,-1.6408301585598662e-13),(0.08244366921098845,8.614512936087814e-14),
--     (0.08961215869021544,-5.283050530808144e-13),(0.09672962645890948,-3.5836667430094137e-13),
--     (0.10379679368088546,7.581073923016376e-13),(0.11081436634049169,-2.0157368416016215e-13),
--     (0.11778303565552051,8.629474042969438e-13),(0.1247034785010328,-7.556920687451337e-14),
--     (0.1315763577895268,-8.075373495358435e-13),(0.13840232285838283,7.363043577087051e-13),
--     (0.14518200984457508,-7.718001336828099e-14),(0.15191604202664166,-7.996871607743758e-13),
--     (0.15860503017574956,8.890223439724663e-13),(0.16524957289584563,-5.384682618788232e-13),
--     (0.17185025692742784,-7.686134224018169e-13),(0.17840765747314435,-3.2605717931058157e-13),
--     (0.18492233849428885,-2.7685884310448306e-13),(0.1913948530000198,-3.903387893794952e-13),
--     (0.1978257433293038,6.160755775588723e-13),(0.20421554142922105,-5.30156516006026e-13),
--     (0.21056476910780475,-4.55112422774782e-13),(0.21687393830143264,-8.182853292737783e-13),
--     (0.22314355131493357,-7.238189921749681e-13),(0.22937410106533207,-4.86240001538379e-13),
--     (0.23556607131286,-9.30945949519689e-14),(0.24171993688651128,6.338907368997553e-13),
--     (0.24783616390413954,4.4171755371315547e-13),(0.25391520998164196,-6.785208495970588e-13),
--     (0.25995752443668607,2.3999540484211735e-13),(0.2659635484978935,-7.555569400283742e-13),
--     (0.27193371548310097,5.407904186145515e-13),(0.2778684510030871,3.692037508208009e-13),
--     (0.28376817313073843,-9.3834172236637e-14),(0.28963329258294834,9.43339818951269e-14),
--     (0.29546421289342106,4.148131870425857e-13),(0.3012613305781997,-3.7923164802093147e-14),
--     (0.3070250352957373,-8.25463138725004e-13),(0.31275571000333,5.668653582900739e-13),
--     (0.318453731119007,-4.723727821986367e-13),(0.32411946865431673,-1.0475750058776541e-13),
--     (0.32975328637257917,-1.1118671389559323e-13),(0.33535554192167183,-5.339989292003297e-13),
--     (0.3409265869704541,1.3912841212197566e-13),(0.3464667673470103,-8.017372713972018e-13),
--     (0.35197642315688427,2.9391859187648e-13),(0.3574558889213222,4.815896111723205e-13),
--     (0.3629054936900502,-6.817539406325327e-13),(0.36832556115950865,-8.009990055432491e-13),
--     (0.3737164097929053,6.787566823158706e-13),(0.37907835293481185,1.5761203773969435e-13),
--     (0.3844116989112081,-8.760375990774874e-13),(0.38971675114044046,-4.152515806343612e-13),
--     (0.3949938082405424,3.2655698896907146e-13),(0.40024316412745975,-4.4704265010452445e-13),
--     (0.4054651081078191,3.452764795203977e-13),(0.4106599249844294,8.390050778518307e-13),
--     (0.4158278951435932,1.1776978751369214e-13),(0.4209692946442374,-1.0774341461609579e-13),
--     (0.42608439531068143,2.186334329321591e-13),(0.43117346481813,2.413263949133313e-13),
--     (0.4362367667745275,3.90574622098307e-13),(0.44127456080423144,6.437879097373207e-13),
--     (0.44628710262804816,3.713514191959202e-13),(0.45127464413963025,-1.7166921336082432e-13),
--     (0.4562374334818742,-2.8658285157914353e-13),(0.4611757151214988,6.713692791384601e-13),
--     (0.46608972992544295,-8.437281040871276e-13),(0.4709797152190731,-2.821014384618127e-13),
--     (0.4758459048698569,1.0701931762114255e-13),(0.4806885293455707,1.8119346366441111e-13),
--     (0.4855078157816024,9.840465278232627e-14),(0.49030398804461583,5.780031989454028e-13),
--     (0.49507726679803454,-1.8302857356041668e-13),(0.4998278695566114,-1.620740015674495e-13),
--     (0.5045560107519123,4.83033149495532e-13),(0.5092619017905236,-7.156055317238212e-13),
--     (0.5139457511013461,8.882123951857185e-13),(0.5186077642083546,-3.0900580513238243e-13),
--     (0.5232481437651586,-6.10765519728515e-13),(0.5278670896204858,3.565996966334783e-13),
--     (0.532464798869114,3.5782396591276384e-13),(0.5370414658973459,-4.622608700154458e-13),
--     (0.5415972824321216,6.227976291722515e-13),(0.5461324375974073,7.283894727206574e-13),
--     (0.5506471179523942,2.680964661521167e-13),(0.5551415075406112,-1.0960825046059278e-13),
--     (0.5596157879353996,2.3119493838005378e-14),(0.5640701382853877,-5.846905800529924e-13),
--     (0.5685047353526897,-2.1037482511444942e-14),(0.5729197535620187,-2.332318294558741e-13),
--     (0.5773153650352469,-4.2333694288141915e-13),(0.5816917396350618,-4.3933937969737843e-13),
--     (0.5860490450031648,4.1341647073835564e-13),(0.590387446602108,6.841763641591467e-14),
--     (0.5947071077462169,4.758553400443064e-13),(0.5990081896452466,8.367967867475769e-13),
--     (0.6032908514389419,-8.576373464665864e-13),(0.6075552502243227,2.1913281229340092e-13),
--     (0.6118015411066153,-6.224284253643115e-13),(0.6160298772156239,-1.098359432543843e-13),
--     (0.6202404097512044,6.531043137763365e-13),(0.6244332880123693,-4.758019902171077e-13),
--     (0.6286086594227527,-3.785425126545704e-13),(0.6327666695706284,4.0939233218678666e-13),
--     (0.636907462236195,8.742438391485829e-13),(0.6410311794206791,2.521818845684288e-13),
--     (0.6451379613736208,-3.6081313604225574e-14),(0.649227946625615,-5.05185559242809e-13),
--     (0.6533012720119586,7.869940332335532e-13),(0.6573580727090302,-6.702087696194906e-13),
--     (0.6613984822452039,1.6108575753932459e-13),(0.6654226325445052,5.852718843625151e-13),
--     (0.6694306539429817,-3.5246757297904794e-13),(0.6734226752123504,-1.8372084495629058e-13),
--     (0.6773988235909201,8.860668981349492e-13),(0.6813592248072382,6.64862680714687e-13),
--     (0.6853040030982811,6.383161517064652e-13),(0.6892332812385575,2.5144230728376075e-13),
--     (0.6931471805601177,-1.7239444525614835e-13))
-- /Source
-- The exact Float64 table words are reused from `MathFuncs.tLogFloat64`.
-- Source: base/special/log.jl:107-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const t_log_Float32 = (0.0,0.007782140442054949,0.015504186535965254,0.02316705928153438,
--     0.030771658666753687,0.0383188643021366,0.0458095360312942,0.053244514518812285,
--     0.06062462181643484,0.06795066190850775,0.07522342123758753,0.08244366921107459,
--     0.08961215868968714,0.09672962645855111,0.10379679368164356,0.11081436634029011,
--     0.11778303565638346,0.12470347850095724,0.13157635778871926,0.13840232285911913,
--     0.1451820098444979,0.15191604202584197,0.15860503017663857,0.16524957289530717,
--     0.17185025692665923,0.1784076574728183,0.184922338494012,0.19139485299962947,
--     0.19782574332991987,0.2042155414286909,0.21056476910734964,0.21687393830061436,
--     0.22314355131420976,0.22937410106484582,0.2355660713127669,0.24171993688714516,
--     0.24783616390458127,0.25391520998096345,0.25995752443692605,0.26596354849713794,
--     0.27193371548364176,0.2778684510034563,0.2837681731306446,0.28963329258304266,
--     0.2954642128938359,0.3012613305781618,0.3070250352949119,0.3127557100038969,
--     0.3184537311185346,0.324119468654212,0.329753286372468,0.3353555419211378,
--     0.3409265869705932,0.34646676734620857,0.3519764231571782,0.3574558889218038,
--     0.3629054936893685,0.3683255611587076,0.37371640979358406,0.37907835293496944,
--     0.38441169891033206,0.3897167511400252,0.394993808240869,0.4002431641270127,
--     0.4054651081081644,0.4106599249852684,0.415827895143711,0.42096929464412963,
--     0.4260843953109001,0.4311734648183713,0.43623676677491807,0.4412745608048752,
--     0.44628710262841953,0.45127464413945856,0.4562374334815876,0.46117571512217015,
--     0.46608972992459924,0.470979715218791,0.4758459048699639,0.4806885293457519,
--     0.4855078157817008,0.4903039880451938,0.4950772667978515,0.4998278695564493,
--     0.5045560107523953,0.5092619017898079,0.5139457511022343,0.5186077642080457,
--     0.5232481437645479,0.5278670896208424,0.5324647988694718,0.5370414658968836,
--     0.5415972824327444,0.5461324375981357,0.5506471179526623,0.5551415075405016,
--     0.5596157879354227,0.564070138284803,0.5685047353526688,0.5729197535617855,
--     0.5773153650348236,0.5816917396346225,0.5860490450035782,0.5903874466021763,
--     0.5947071077466928,0.5990081896460834,0.6032908514380843,0.6075552502245418,
--     0.6118015411059929,0.616029877215514,0.6202404097518576,0.6244332880118935,
--     0.6286086594223741,0.6327666695710378,0.6369074622370692,0.6410311794209312,
--     0.6451379613735847,0.6492279466251099,0.6533012720127457,0.65735807270836,
--     0.661398482245365,0.6654226325450905,0.6694306539426292,0.6734226752121667,
--     0.6773988235918061,0.6813592248079031,0.6853040030989194,0.689233281238809,
--     0.6931471805599453)
-- /Source
-- The Float32 table values are reused from `MathCov.C.tLogFloat32`.
-- Source: base/special/log.jl:412-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const t_log_table_compact = (
--     (0xbfd62c82f2b9c8b5, 5.929407345889625e-15),
--     (0xbfd5d1bdbf5808b4, -2.544157440035963e-14),
--     (0xbfd57677174558b3, -3.443525940775045e-14),
--     (0xbfd51aad872df8b2, -2.500123826022799e-15),
--     (0xbfd4be5f957778b1, -8.929337133850617e-15),
--     (0xbfd4618bc21c60b0, 1.7625431312172662e-14),
--     (0xbfd404308686a8af, 1.5688303180062087e-15),
--     (0xbfd3a64c556948ae, 2.9655274673691784e-14),
--     (0xbfd347dd9a9880ad, 3.7923164802093147e-14),
--     (0xbfd2e8e2bae120ac, 3.993416384387844e-14),
--     (0xbfd2895a13de88ab, 1.9352855826489123e-14),
--     (0xbfd2895a13de88ab, 1.9352855826489123e-14),
--     (0xbfd22941fbcf78aa, -1.9852665484979036e-14),
--     (0xbfd1c898c16998a9, -2.814323765595281e-14),
--     (0xbfd1675cababa8a8, 2.7643769993528702e-14),
--     (0xbfd1058bf9ae48a7, -4.025092402293806e-14),
--     (0xbfd0a324e27390a6, -1.2621729398885316e-14),
--     (0xbfd0402594b4d0a5, -3.600176732637335e-15),
--     (0xbfd0402594b4d0a5, -3.600176732637335e-15),
--     (0xbfcfb9186d5e40a4, 1.3029797173308663e-14),
--     (0xbfcef0adcbdc60a3, 4.8230289429940886e-14),
--     (0xbfce27076e2af0a2, -2.0592242769647135e-14),
--     (0xbfcd5c216b4fc0a1, 3.149265065191484e-14),
--     (0xbfcc8ff7c79aa0a0, 4.169796584527195e-14),
--     (0xbfcc8ff7c79aa0a0, 4.169796584527195e-14),
--     (0xbfcbc286742d909f, 2.2477465222466186e-14),
--     (0xbfcaf3c94e80c09e, 3.6507188831790577e-16),
--     (0xbfca23bc1fe2b09d, -3.827767260205414e-14),
--     (0xbfca23bc1fe2b09d, -3.827767260205414e-14),
--     (0xbfc9525a9cf4509c, -4.7641388950792196e-14),
--     (0xbfc87fa06520d09b, 4.9278276214647115e-14),
--     (0xbfc7ab890210e09a, 4.9485167661250996e-14),
--     (0xbfc7ab890210e09a, 4.9485167661250996e-14),
--     (0xbfc6d60fe719d099, -1.5003333854266542e-14),
--     (0xbfc5ff3070a79098, -2.7194441649495324e-14),
--     (0xbfc5ff3070a79098, -2.7194441649495324e-14),
--     (0xbfc526e5e3a1b097, -2.99659267292569e-14),
--     (0xbfc44d2b6ccb8096, 2.0472357800461955e-14),
--     (0xbfc44d2b6ccb8096, 2.0472357800461955e-14),
--     (0xbfc371fc201e9095, 3.879296723063646e-15),
--     (0xbfc29552f81ff094, -3.6506824353335045e-14),
--     (0xbfc1b72ad52f6093, -5.4183331379008994e-14),
--     (0xbfc1b72ad52f6093, -5.4183331379008994e-14),
--     (0xbfc0d77e7cd09092, 1.1729485484531301e-14),
--     (0xbfc0d77e7cd09092, 1.1729485484531301e-14),
--     (0xbfbfec9131dbe091, -3.811763084710266e-14),
--     (0xbfbe27076e2b0090, 4.654729747598445e-14),
--     (0xbfbe27076e2b0090, 4.654729747598445e-14),
--     (0xbfbc5e548f5bc08f, -2.5799991283069902e-14),
--     (0xbfba926d3a4ae08e, 3.7700471749674615e-14),
--     (0xbfba926d3a4ae08e, 3.7700471749674615e-14),
--     (0xbfb8c345d631a08d, 1.7306161136093256e-14),
--     (0xbfb8c345d631a08d, 1.7306161136093256e-14),
--     (0xbfb6f0d28ae5608c, -4.012913552726574e-14),
--     (0xbfb51b073f06208b, 2.7541708360737882e-14),
--     (0xbfb51b073f06208b, 2.7541708360737882e-14),
--     (0xbfb341d7961be08a, 5.0396178134370583e-14),
--     (0xbfb341d7961be08a, 5.0396178134370583e-14),
--     (0xbfb16536eea38089, 1.8195060030168815e-14),
--     (0xbfaf0a30c0118088, 5.213620639136504e-14),
--     (0xbfaf0a30c0118088, 5.213620639136504e-14),
--     (0xbfab42dd71198087, 2.532168943117445e-14),
--     (0xbfab42dd71198087, 2.532168943117445e-14),
--     (0xbfa77458f632c086, -5.148849572685811e-14),
--     (0xbfa77458f632c086, -5.148849572685811e-14),
--     (0xbfa39e87b9fec085, 4.6652946995830086e-15),
--     (0xbfa39e87b9fec085, 4.6652946995830086e-15),
--     (0xbf9f829b0e780084, -4.529814257790929e-14),
--     (0xbf9f829b0e780084, -4.529814257790929e-14),
--     (0xbf97b91b07d58083, -4.361324067851568e-14),
--     (0xbf8fc0a8b0fc0082, -1.7274567499706107e-15),
--     (0xbf8fc0a8b0fc0082, -1.7274567499706107e-15),
--     (0xbf7fe02a6b100081, -2.298941004620351e-14),
--     (0xbf7fe02a6b100081, -2.298941004620351e-14),
--     (0x0000000000000080, 0.0),
--     (0x0000000000000080, 0.0),
--     (0x3f8010157589007e, -1.4902732911301337e-14),
--     (0x3f9020565893807c, -3.527980389655325e-14),
--     (0x3f98492528c9007a, -4.730054772033249e-14),
--     (0x3fa0415d89e74078, 7.580310369375161e-15),
--     (0x3fa466aed42e0076, -4.9893776716773285e-14),
--     (0x3fa894aa149fc074, -2.262629393030674e-14),
--     (0x3faccb73cdddc072, -2.345674491018699e-14),
--     (0x3faeea31c006c071, -1.3352588834854848e-14),
--     (0x3fb1973bd146606f, -3.765296820388875e-14),
--     (0x3fb3bdf5a7d1e06d, 5.1128335719851986e-14),
--     (0x3fb5e95a4d97a06b, -5.046674438470119e-14),
--     (0x3fb700d30aeac06a, 3.1218748807418837e-15),
--     (0x3fb9335e5d594068, 3.3871241029241416e-14),
--     (0x3fbb6ac88dad6066, -1.7376727386423858e-14),
--     (0x3fbc885801bc4065, 3.957125899799804e-14),
--     (0x3fbec739830a2063, -5.2849453521890294e-14),
--     (0x3fbfe89139dbe062, -3.767012502308738e-14),
--     (0x3fc1178e8227e060, 3.1859736349078334e-14),
--     (0x3fc1aa2b7e23f05f, 5.0900642926060466e-14),
--     (0x3fc2d1610c86805d, 8.710783796122478e-15),
--     (0x3fc365fcb015905c, 6.157896229122976e-16),
--     (0x3fc4913d8333b05a, 3.821577743916796e-14),
--     (0x3fc527e5e4a1b059, 3.9440046718453496e-14),
--     (0x3fc6574ebe8c1057, 2.2924522154618074e-14),
--     (0x3fc6f0128b757056, -3.742530094732263e-14),
--     (0x3fc7898d85445055, -2.5223102140407338e-14),
--     (0x3fc8beafeb390053, -1.0320443688698849e-14),
--     (0x3fc95a5adcf70052, 1.0634128304268335e-14),
--     (0x3fca93ed3c8ae050, -4.3425422595242564e-14),
--     (0x3fcb31d8575bd04f, -1.2527395755711364e-14),
--     (0x3fcbd087383be04e, -5.204008743405884e-14),
--     (0x3fcc6ffbc6f0104d, -3.979844515951702e-15),
--     (0x3fcdb13db0d4904b, -4.7955860343296286e-14),
--     (0x3fce530effe7104a, 5.015686013791602e-16),
--     (0x3fcef5ade4dd0049, -7.252318953240293e-16),
--     (0x3fcf991c6cb3b048, 2.4688324156011588e-14),
--     (0x3fd07138604d5846, 5.465121253624792e-15),
--     (0x3fd0c42d67616045, 4.102651071698446e-14),
--     (0x3fd1178e8227e844, -4.996736502345936e-14),
--     (0x3fd16b5ccbacf843, 4.903580708156347e-14),
--     (0x3fd1bf99635a6842, 5.089628039500759e-14),
--     (0x3fd214456d0eb841, 1.1782016386565151e-14),
--     (0x3fd2bef07cdc903f, 4.727452940514406e-14),
--     (0x3fd314f1e1d3603e, -4.4204083338755686e-14),
--     (0x3fd36b6776be103d, 1.548345993498083e-14),
--     (0x3fd3c2527733303c, 2.1522127491642888e-14),
--     (0x3fd419b423d5e83b, 1.1054030169005386e-14),
--     (0x3fd4718dc271c83a, -5.534326352070679e-14),
--     (0x3fd4c9e09e173039, -5.351646604259541e-14),
--     (0x3fd522ae0738a038, 5.4612144489920215e-14),
--     (0x3fd57bf753c8d037, 2.8136969901227338e-14),
--     (0x3fd5d5bddf596036, -1.156568624616423e-14))
-- /Source
-- The compact-table words are reused from `MathFuncs.Log.tLogTableCompact`.

/--
Julia source: base/special/log.jl:542-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
 @inline function log_tab_unpack(t::UInt64)
    invc = UInt64(t&UInt64(0xff)|0x1ff00)<<45
    logc = t&(~UInt64(0xff))
    return (reinterpret(Float64, invc), reinterpret(Float64, logc))
end
```
-/
def logTabUnpack (t : JInt .u64) : F64 × F64 :=
  let bits := t.val.toNat
  (lit64 ((Nat.lor (bits % 256) 0x1ff00) * 2^45),
   lit64 (bits - bits % 256))

/--
Julia source: base/special/log.jl:547-583 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Log implementation that returns 2 numbers which sum to give true value with about 68 bits of precision
# Since `log` only makes sense for positive exponents, we speed up the implementation by stealing the sign bit
# of the input for an extra bit of the exponent which is used to normalize subnormal inputs.
# Does not normalize results.
# Adapted and modified from https://github.com/ARM-software/optimized-routines/blob/master/math/pow.c
# Copyright (c) 2018-2020, Arm Limited. (which is also MIT licensed)
# note that this isn't an exact translation as this version compacts the table to reduce cache pressure.
function _log_ext(xu::UInt64)
    # x = 2^k z; where z is in range [0x1.69555p-1,0x1.69555p-0) and exact.
    # The range is split into N subintervals.
    # The ith subinterval contains z and c is near the center of the interval.
    tmp = reinterpret(Int64, xu -% 0x3fe6955500000000) #0x1.69555p-1
    z = reinterpret(Float64, xu -% (tmp & 0xfff0000000000000))
    k = Float64(tmp >> 52)
    # log(x) = k*Ln2 + log(c) + log1p(z/c-1).
    # N.B. :nothrow and :noub since `idx` is known to be `1 ≤ idx ≤ length(t_log_table_compact)`
    idx = (tmp >> 45) & (length(t_log_table_compact)-1) + 1
    t, logctail = Base.@assume_effects :nothrow :noub @inbounds t_log_table_compact[idx]
    invc, logc = log_tab_unpack(t)
    # Note: invc is j/N or j/N/2 where j is an integer in [N,2N) and
    # |z/c - 1| < 1/N, so r = z/c - 1 is exactly representable.
    r = fma(z, invc, -1.0)
    # k*Ln2 + log(c) + r.
    t1 = muladd(k, 0.6931471805598903, logc) #ln(2) hi part
    t2 = t1 + r
    lo1 = muladd(k, 5.497923018708371e-14, logctail) #ln(2) lo part
    lo2 = t1 - t2 + r
    ar = -0.5 * r
    ar2, lo3 = two_mul(r, ar)
    # k*Ln2 + log(c) + r + .5*r*r.
    hi = t2 + ar2
    lo4 = t2 - hi + ar2
    p = evalpoly(r, (-0x1.555555555556p-1, 0x1.0000000000006p-1, -0x1.999999959554ep-2, 0x1.555555529a47ap-2, -0x1.2495b9b4845e9p-2, 0x1.0002b8b263fc3p-2))
    lo = lo1 + lo2 + lo3 + muladd(r*ar2, p, lo4)
    return hi, lo
end
```
-/
def logExt (xu : JInt .u64) : F64 × F64 :=
  let xuBits := xu.val.toNat
  let two64 : Nat := 2^64
  let tmpU : Nat := (xuBits + two64 - 0x3fe6955500000000) % two64
  let tmp := if tmpU ≥ 2^63 then (tmpU : Int) - (two64 : Int) else (tmpU : Int)
  let zBits : Nat := (xuBits + two64 - (tmpU - tmpU % (2^52))) % two64
  let z := lit64 zBits
  let k := FP.ofInt .f64 (tmp.fdiv (2^52))
  let idx := ((tmp.fdiv (2^45)).emod 128).toNat
  let (t, logctailBits) := tLogCompact.getD idx (0, 0)
  let logctail := lit64 logctailBits
  let (invc, logc) := logTabUnpack (JInt.wrap .u64 (t : Int))
  let r := FP.fma z invc (lit64 0xbff0000000000000)
  let t1 := FP.muladd k (lit64 0x3fe62e42fefa3800) logc
  let t2 := FP.add t1 r
  let lo1 := FP.muladd k (lit64 0x3d2ef35793c76730) logctail
  let lo2 := FP.add (FP.sub t1 t2) r
  let ar := FP.mul (lit64 0xbfe0000000000000) r
  let ar2 := FP.mul r ar
  let lo3 := FP.fma r ar (FP.neg ar2)
  let hi := FP.add t2 ar2
  let lo4 := FP.add (FP.sub t2 hi) ar2
  let p := horner64 r [lit64 0xbfe5555555555560, lit64 0x3fe0000000000006,
    lit64 0xbfd999999959554e, lit64 0x3fd555555529a47a,
    lit64 0xbfd2495b9b4845e9, lit64 0x3fd0002b8b263fc3]
  let lo := FP.add (FP.add (FP.add lo1 lo2) lo3)
    (FP.muladd (FP.mul r ar2) p lo4)
  (hi, lo)

end JuliaLean.base.special.log

namespace JuliaLean.MathCov.FloatFuncs

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP

variable {T : FTy}

/-- `log10` and `log` of the format (`Float16` via `Float32`). -/
def log10T (x : FV T) : Jl (FV T) :=
  match T, x with
  | .f64, x => do return of64 (← MathFuncs.log10 (to64 x))
  | .f32, x => Log.log10F32 x
  | .f16, x => do return conv (← Log.log10F32 (conv x))

end JuliaLean.MathCov.FloatFuncs
