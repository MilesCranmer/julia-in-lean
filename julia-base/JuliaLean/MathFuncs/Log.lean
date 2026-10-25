import JuliaLean.MathFuncs.Prelude

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
