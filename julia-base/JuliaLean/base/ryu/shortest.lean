import JuliaLean.Core
import JuliaLean.base.rounding
import JuliaLean.Runtime.Float
import JuliaLean.base.ryu.utils

/-!
# Model of `base/ryu/shortest.jl`

Float64 formatting reuses `ParsePrint.Ryu`; Float16 and Float32 reduction reuses
the exact bit-pattern model in `JuliaLean.MemSafety.G2`.
-/
namespace JuliaLean.ParsePrint.Ryu

open JuliaLean JuliaLean.Float JuliaLean.ParsePrint
/-- `(x % UInt32) -% UInt32(10) *% (xdiv % UInt32)`, the last decimal digit. -/
def mod10 (x xdiv : U64) : U32 :=
  JInt.rem .u32 x - JInt.lit .u32 10 * JInt.rem .u32 xdiv

/-- `(x % UInt32) -% UInt32(100) *% (xdiv % UInt32)`. -/
def mod100 (x xdiv : U64) : U32 :=
  JInt.rem .u32 x - JInt.lit .u32 100 * JInt.rem .u32 xdiv

/-- The mutable locals of step 4 and of the `maxsignif` reduction. -/
structure St where
  a : U64
  b : U64
  c : U64
  e10 : Int
  aAll : Bool
  bAll : Bool
  bLast : JInt .u8
  roundup : Bool

/-- `base/ryu/shortest.jl:96-112`: the slow reduction loop. -/
def slowLoop : Nat → St → St
  | 0, s => s
  | n+1, s =>
    let cd := udivLit s.c 10
    let ad := udivLit s.a 10
    if cd.val ≤ ad.val then s else
      let am := mod10 s.a ad
      let bd := udivLit s.b 10
      let bm := mod10 s.b bd
      slowLoop n { s with
        aAll := s.aAll && am.val == 0, bAll := s.bAll && s.bLast.val == 0,
        bLast := JInt.rem .u8 bm, b := bd, c := cd, a := ad, e10 := s.e10 + 1 }

/-- `base/ryu/shortest.jl:114-129`: remove digits while `a` ends in zero, or while
`b` is not below `maxsignif`. -/
def aZeroLoop (maxsignif : Option Int) : Nat → St → St
  | 0, s => s
  | n+1, s =>
    let ad := udivLit s.a 10
    let am := mod10 s.a ad
    if am.val ≠ 0 && (match maxsignif with | none => true | some M => decide (s.b.val < M)) then s else
      let cd := udivLit s.c 10
      let bd := udivLit s.b 10
      let bm := mod10 s.b bd
      aZeroLoop maxsignif n { s with
        bAll := s.bAll && s.bLast.val == 0,
        bLast := JInt.rem .u8 bm, b := bd, c := cd, a := ad, e10 := s.e10 + 1 }

/-- `base/ryu/shortest.jl:149-162`: the common-case reduction loop. -/
def fastLoop : Nat → St → St
  | 0, s => s
  | n+1, s =>
    let cd := udivLit s.c 10
    let ad := udivLit s.a 10
    if cd.val ≤ ad.val then s else
      let bd := udivLit s.b 10
      let bm := mod10 s.b bd
      fastLoop n { s with
        roundup := decide (bm.val ≥ 5), b := bd, c := cd, a := ad, e10 := s.e10 + 1 }

/-- `base/ryu/shortest.jl:167-177` and `202-212`: reduce to `maxsignif` digits,
remembering whether the removed digits were all zero. -/
def maxLoop (M : Int) : Nat → St → St
  | 0, s => s
  | n+1, s =>
    let bd := udivLit s.b 10
    let bm := mod10 s.b bd
    if s.b.val ≤ M then s else
      maxLoop M n { s with
        b := bd,
        roundup := if s.bAll && bd.val % 2 == 0 then decide (bm.val > 5) else decide (bm.val ≥ 5),
        bAll := s.bAll && bm.val == 0, e10 := s.e10 + 1 }

/-- `base/ryu/shortest.jl:181-189` and `215-223`: remove trailing zeros. -/
def zeroLoop : Nat → U64 × Int → U64 × Int
  | 0, s => s
  | n+1, (b, e10) =>
    let bd := udivLit b 10
    let bm := mod10 b bd
    if bm.val ≠ 0 then (b, e10) else zeroLoop n (bd, e10 + 1)

/-- The fuel for every reduction loop (see the module docstring). -/
def fuel : Nat := 24

/-- `base/ryu/shortest.jl:7-226`: `reduce_shortest(f::Float64, maxsignif)`. -/
def reduceShortest (f : F64) (maxsignif : Option Int) : U64 × Int :=
  let uf : U64 := JInt.wrap .u64 (F64.toBits f)
  let m : U64 := band uf (JInt.lit .u64 0x000fffffffffffff)
  let e : Int := (shr (band uf (JInt.lit .u64 0x7ff0000000000000)) 52).val
  -- Step 1
  let mf : U64 := bor (shl (JInt.lit .u64 1) 52) m
  let ef : Int := e - 1023 - 52
  let fIsInteger := (band mf (shlI (JInt.lit .u64 1) (-ef) - JInt.lit .u64 1)).val == 0
  if ef > 0 ∨ ef < -52 ∨ !fIsInteger then
    -- fixup subnormals
    let (ef, mf) := if e == 0 then ((1 : Int) - 1023 - 52, m) else (ef, mf)
    -- Step 2
    let e2 := ef - 2
    let mfIsEven := mf.val % 2 == 0
    let v : U64 := JInt.lit .u64 4 * mf
    let w : U64 := v + JInt.lit .u64 2
    let uShiftHalf := m.val == 0 && e > 1
    let u : U64 := v - JInt.lit .u64 2 + ofBool .u64 uShiftHalf
    -- Step 3
    let (a, b, c, e10, aAll, bAll) :=
      if e2 ≥ 0 then
        let q := log10pow2 e2 - (if e2 > 3 then 1 else 0)
        let k := 122 + pow5bits q - 1
        let i := -e2 + q + k
        let mul := pow5invsplit q
        let a := mulshift u mul i
        let b := mulshift v mul i
        let c := mulshift w mul i
        if q ≤ 21 then
          -- `(v % UInt32) -% 5 *% div(v, 5)`: `div(v, 5)` stays a UInt64, so the
          -- difference is taken modulo 2^64 (`base/ryu/shortest.jl:59`).
          let vmod5 : U64 := JInt.rem .u64 (JInt.rem .u32 v) -
            JInt.lit .u64 5 * udivLit v 5
          if vmod5.val == 0 then (a, b, c, q, false, pow5 v q)
          else if mfIsEven then (a, b, c, q, pow5 u q, false)
          else (a, b, c - ofBool .u64 (pow5 w q), q, false, false)
        else (a, b, c, q, false, false)
      else
        let q := log10pow5 (-e2) - (if -e2 > 1 then 1 else 0)
        let e10 := q + e2
        let i := -e2 - q
        let k := pow5bits i - 121
        let j := q - k
        let mul := pow5split i
        let a := mulshift u mul j
        let b := mulshift v mul j
        let c := mulshift w mul j
        if q ≤ 1 then
          if mfIsEven then (a, b, c, e10, !uShiftHalf, true)
          else (a, b, c - JInt.lit .u64 1, e10, false, true)
        else if q < 63 then (a, b, c, e10, false, pow2 v q)
        else (a, b, c, e10, false, false)
    let s0 : St := ⟨a, b, c, e10, aAll, bAll, JInt.lit .u8 0, false⟩
    -- Step 4
    let s :=
      if s0.aAll || s0.bAll then
        let s := slowLoop fuel s0
        let s := if s.aAll then aZeroLoop maxsignif fuel s else s
        let s := if s.bAll && s.bLast.val == 5 && s.b.val % 2 == 0 then
          { s with bLast := JInt.lit .u8 4 } else s
        { s with roundup := (s.b.val == s.a.val && (!mfIsEven || !s.aAll)) || decide (s.bLast.val ≥ 5) }
      else
        let s := { s0 with roundup := decide (s0.bLast.val ≥ 5) }
        let cd := udivLit s.c 100
        let ad := udivLit s.a 100
        let s := if cd.val > ad.val then
            let bd := udivLit s.b 100
            let bm := mod100 s.b bd
            { s with roundup := decide (bm.val ≥ 50), b := bd, c := cd, a := ad, e10 := s.e10 + 2 }
          else s
        let s := fastLoop fuel s
        { s with roundup := s.b.val == s.a.val || s.roundup }
    match maxsignif with
    | some M =>
      if s.b.val > M then
        let s := maxLoop M fuel s
        zeroLoop fuel (s.b + ofBool .u64 s.roundup, s.e10)
      else (s.b + ofBool .u64 s.roundup, s.e10)
    | none => (s.b + ofBool .u64 s.roundup, s.e10)
  else
    -- c) an integer < 2^53
    let b := shrI mf (-ef)
    let (b, e10) : U64 × Int := match maxsignif with
      | some M =>
        if b.val > M then
          let s := maxLoop M fuel ⟨b, b, b, 0, false, true, JInt.lit .u8 0, false⟩
          (s.b + ofBool .u64 s.roundup, s.e10)
        else (b, 0)
      | none => (b, 0)
    zeroLoop fuel (b, e10)


/-- The Float64 literal `0.05`. -/
def c005 : F64 := F64.ofBits 0x3FA999999999999A

/-- `base/ryu/shortest.jl:228-464` for `x::Float64` (`typed` has no effect). -/
def writeshortest (x : F64) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (compact : Bool) : List Nat :=
  if F64.iszero x then
    let pre := appendSign x plus space ++ [chZero] ++ (if hash then [decchar] else [])
    if precision == -1 then pre ++ (if hash then [chZero] else [])
    else pre ++ (if hash then zeros (precision - 1).toNat else [])
  else if F64.isnan x then appendSign x plus space ++ [78, 97, 78]
  else if !F64.isfinite x then appendSign x plus space ++ [73, 110, 102]
  else
    let (output, nexp) := reduceShortest x (if compact then some (999999 : Int) else none)
    let sign := appendSign x plus space
    let olength := decimallength output
    let digits := cDigits olength output.val.toNat
    let pt : Int := nexp + olength
    let fixedForm :=
      -4 < pt ∧ pt ≤ (if precision == -1 then 6 else precision) ∧
      ¬ (pt ≥ olength ∧
        F64.lt c005 (F64.abs (F64.sub
          (F64.mod (F64.add x c005) (F64.ofInt (JInt.wrap .i64 (10 ^ (pt - olength).toNat)).val))
          c005)))
    if fixedForm then
      if pt ≤ 0 then
        let precision := precision - olength
        sign ++ [chZero, decchar] ++ zeros pt.natAbs ++ digits ++
          (if hash then zeros precision.toNat else [])
      else if pt ≥ olength then
        let precision := precision - olength - nexp
        sign ++ digits ++ zeros nexp.toNat ++
          (if hash then [decchar] ++ (if precision < 0 then [chZero] else []) ++ zeros precision.toNat
           else [])
      else
        let pointoff := olength - nexp.natAbs
        let precision := precision - olength
        sign ++ digits.take pointoff ++ [decchar] ++ digits.drop pointoff ++
          (if hash then zeros precision.toNat else [])
    else
      let (mant, precision) :=
        if olength > 1 || hash then (digits.take 1 ++ [decchar] ++ digits.drop 1, precision - olength)
        else (digits.take 1, precision)
      let mant := mant ++
        (if hash then (if olength == 1 then [chZero] else []) ++ zeros precision.toNat else [])
      let exp2 : Int := nexp + olength - 1
      let (esign, exp2) :=
        if exp2 < 0 then ([chMinus], -exp2) else if padexp then ([chPlus], exp2) else ([], exp2)
      let e := exp2.toNat
      let edigits :=
        if exp2 ≥ 100 then d100 (e / 10) ++ [chZero + e % 10]
        else if exp2 ≥ 10 then d100 e
        else (if padexp then [chZero] else []) ++ [chZero + e]
      sign ++ mant ++ [expchar] ++ esign ++ edigits

end JuliaLean.ParsePrint.Ryu
namespace JuliaLean.MemSafety.G2

open JuliaLean
/-! ## `base/ryu/shortest.jl:319-447` -/

open JuliaLean.ParsePrint JuliaLean.ParsePrint.Ryu

abbrev RyuU64 := JuliaLean.ParsePrint.Ryu.U64

def ryuInitialE10 (e2 : Int) : Int :=
  if e2 ≥ 0 then log10pow2 e2 - (if e2 > 3 then 1 else 0)
  else log10pow5 (-e2) - (if -e2 > 1 then 1 else 0) + e2

def ryuInitialState (e2 : Int) (mfIsEven uShiftHalf : Bool)
    (u v w : RyuU64) : St :=
  let (a, b, c, e10, aAll, bAll) :=
    if e2 ≥ 0 then
      let q := log10pow2 e2 - (if e2 > 3 then 1 else 0)
      let k := 122 + pow5bits q - 1
      let i := -e2 + q + k
      let mul := pow5invsplit q
      let a := mulshift u mul i
      let b := mulshift v mul i
      let c := mulshift w mul i
      if q ≤ 21 then
        let vmod5 : RyuU64 := JInt.rem .u64 (JInt.rem .u32 v) - JInt.lit .u64 5 * udivLit v 5
        if vmod5.val == 0 then (a, b, c, q, false, pow5 v q)
        else if mfIsEven then (a, b, c, q, pow5 u q, false)
        else (a, b, c - ofBool .u64 (pow5 w q), q, false, false)
      else (a, b, c, q, false, false)
    else
      let q := log10pow5 (-e2) - (if -e2 > 1 then 1 else 0)
      let e10 := q + e2
      let i := -e2 - q
      let k := pow5bits i - 121
      let j := q - k
      let mul := pow5split i
      let a := mulshift u mul j
      let b := mulshift v mul j
      let c := mulshift w mul j
      if q ≤ 1 then
        if mfIsEven then (a, b, c, e10, !uShiftHalf, true)
        else (a, b, c - JInt.lit .u64 1, e10, false, true)
      else if q < 63 then (a, b, c, e10, false, pow2 v q)
      else (a, b, c, e10, false, false)
  let s : St := ⟨a, b, c, e10, aAll, bAll, JInt.lit .u8 0, false⟩
  { s with e10 := ryuInitialE10 e2 }

def ryuRoundState (mfIsEven : Bool) (m : Option Int) (s0 : St) : St :=
  if s0.aAll || s0.bAll then
    let s := slowLoop fuel s0
    let s := if s.aAll then aZeroLoop m fuel s else s
    let s := if s.bAll && s.bLast.val == 5 && s.b.val % 2 == 0 then
      { s with bLast := JInt.lit .u8 4 } else s
    { s with roundup := (s.b.val == s.a.val && (!mfIsEven || !s.aAll)) || decide (s.bLast.val ≥ 5) }
  else
    let s := { s0 with roundup := decide (s0.bLast.val ≥ 5) }
    let cd := udivLit s.c 100
    let ad := udivLit s.a 100
    let s := if cd.val > ad.val then
        let bd := udivLit s.b 100
        let bm := mod100 s.b bd
        { s with roundup := decide (bm.val ≥ 50), b := bd, c := cd, a := ad, e10 := s.e10 + 2 }
      else s
    let s := fastLoop fuel s
    { s with roundup := s.b.val == s.a.val || s.roundup }

def ryuFinish (mfIsEven : Bool) (m : Option Int) (s0 : St) : RyuU64 × Int :=
  let s := ryuRoundState mfIsEven m s0
  match m with
  | some M =>
    if s.b.val > M then
      let s := maxLoop M fuel s
      zeroLoop fuel (s.b + ofBool .u64 s.roundup, s.e10)
    else (s.b + ofBool .u64 s.roundup, s.e10)
  | none => (s.b + ofBool .u64 s.roundup, s.e10)

def ryuCore (rawM : RyuU64) (rawE ef : Int) (mf : RyuU64)
    (maxsignif : Option Int) : RyuU64 × Int :=
  let e2 := ef - 2
  let mfIsEven := mf.val % 2 == 0
  let v : RyuU64 := JInt.lit .u64 4 * mf
  let w : RyuU64 := v + JInt.lit .u64 2
  let uShiftHalf := rawM.val == 0 && decide (rawE > 1)
  let u : RyuU64 := v - JInt.lit .u64 2 + ofBool .u64 uShiftHalf
  ryuFinish mfIsEven maxsignif (ryuInitialState e2 mfIsEven uShiftHalf u v w)

def ryuLongPath (mf : RyuU64) (ef : Int) : Bool :=
  let fIsInteger := (band mf (shlI (JInt.lit .u64 1) (-ef) - JInt.lit .u64 1)).val == 0
  ef > 0 || ef < -52 || !fIsInteger

def ryuFixup (rawM : RyuU64) (rawE ef : Int) (mf : RyuU64) : Int × RyuU64 :=
  if rawE == 0 then ((1 : Int) - 1023 - 52, rawM) else (ef, mf)

def ryuFixupE (rawE ef : Int) : Int :=
  if rawE == 0 then (1 : Int) - 1023 - 52 else ef

def ryuFixupM (rawM : RyuU64) (rawE : Int) (mf : RyuU64) : RyuU64 :=
  if rawE == 0 then rawM else mf

def ryuReduceFromParts (rawM : RyuU64) (rawE ef : Int) (mf : RyuU64)
    (maxsignif : Option Int) : RyuU64 × Int :=
  if ryuLongPath mf ef then
    ryuCore rawM rawE (ryuFixupE rawE ef) (ryuFixupM rawM rawE mf) maxsignif
  else
    let b := shrI mf (-ef)
    let (b, e10) := match maxsignif with
      | some M =>
        if b.val > M then
          let s := maxLoop M fuel ⟨b, b, b, 0, false, true, JInt.lit .u8 0, false⟩
          (s.b + ofBool .u64 s.roundup, s.e10)
        else (b, 0)
      | none => (b, 0)
    zeroLoop fuel (b, e10)

def ryuReduceModel (x : JuliaLean.Float.F64) (maxsignif : Option Int) : RyuU64 × Int :=
  let uf : RyuU64 := JInt.wrap .u64 (JuliaLean.Float.F64.toBits x)
  let rawM := band uf (JInt.lit .u64 0x000fffffffffffff)
  let rawE : Int := JuliaLean.Float.F64.exponentField x
  let mf : RyuU64 := bor (shl (JInt.lit .u64 1) 52) rawM
  let ef : Int := rawE - 1023 - 52
  ryuReduceFromParts rawM rawE ef mf maxsignif

def ryuDecimalLength (x : RyuU64) : Fin 18 :=
  let v := x.val
  if v ≥ 10000000000000000 then ⟨17, by decide⟩
  else if v ≥ 1000000000000000 then ⟨16, by decide⟩
  else if v ≥ 100000000000000 then ⟨15, by decide⟩
  else if v ≥ 10000000000000 then ⟨14, by decide⟩
  else if v ≥ 1000000000000 then ⟨13, by decide⟩
  else if v ≥ 100000000000 then ⟨12, by decide⟩
  else if v ≥ 10000000000 then ⟨11, by decide⟩
  else if v ≥ 1000000000 then ⟨10, by decide⟩
  else if v ≥ 100000000 then ⟨9, by decide⟩
  else if v ≥ 10000000 then ⟨8, by decide⟩
  else if v ≥ 1000000 then ⟨7, by decide⟩
  else if v ≥ 100000 then ⟨6, by decide⟩
  else if v ≥ 10000 then ⟨5, by decide⟩
  else if v ≥ 1000 then ⟨4, by decide⟩
  else if v ≥ 100 then ⟨3, by decide⟩
  else if v ≥ 10 then ⟨2, by decide⟩
  else ⟨1, by decide⟩



inductive RyuSmall where
  | f16 (bits : Fin (2^16))
  | f32 (bits : Fin (2^32))
  deriving DecidableEq, Repr

def RyuSmall.bits : RyuSmall → Nat
  | .f16 x | .f32 x => x.val

def RyuSmall.width : RyuSmall → Nat
  | .f16 _ => 16
  | .f32 _ => 32

def RyuSmall.significandBits : RyuSmall → Nat
  | .f16 _ => 10
  | .f32 _ => 23

def RyuSmall.exponentBits : RyuSmall → Nat
  | .f16 _ => 5
  | .f32 _ => 8

def RyuSmall.exponentBias : RyuSmall → Int
  | .f16 _ => 15
  | .f32 _ => 127

def RyuSmall.pow5InvBitcount : RyuSmall → Nat
  | .f16 _ => 30
  | .f32 _ => 59

def RyuSmall.pow5Bitcount : RyuSmall → Nat
  | .f16 _ => 30
  | .f32 _ => 61

def RyuSmall.qinvbound : RyuSmall → Int
  | .f16 _ => 4
  | .f32 _ => 9

def RyuSmall.qbound : RyuSmall → Int
  | .f16 _ => 15
  | .f32 _ => 31

def RyuSmall.modulus (x : RyuSmall) : Nat := 2^x.width

def RyuSmall.wrap (x : RyuSmall) (n : Nat) : Nat := n % x.modulus

def RyuSmall.sub (x : RyuSmall) (a b : Nat) : Nat :=
  (a + x.modulus - b % x.modulus) % x.modulus

def RyuSmall.rawM (x : RyuSmall) : Nat := x.bits % 2^x.significandBits

def RyuSmall.rawE (x : RyuSmall) : Int :=
  (x.bits / 2^x.significandBits % 2^x.exponentBits : Nat)

def RyuSmall.finite (x : RyuSmall) : Bool :=
  x.rawE != (2^x.exponentBits : Nat) - 1

def RyuSmall.zero (x : RyuSmall) : Bool :=
  x.bits % 2^(x.width - 1) == 0

def ryuSmallPow5InvSplit (x : RyuSmall) (q : Int) : Nat :=
  let pow := 5 ^ q.toNat
  2 ^ (nbits pow - 1 + x.pow5InvBitcount) / pow + 1

def ryuSmallPow5Split (x : RyuSmall) (i : Int) : Nat :=
  let pow := 5 ^ i.toNat
  let shift : Int := (nbits pow : Int) - x.pow5Bitcount
  if shift ≥ 0 then pow / 2^shift.toNat else pow * 2^(-shift).toNat

def ryuSmallMulshift (x : RyuSmall) (m mul : Nat) (j : Int) : RyuU64 :=
  let shifted := if j ≥ 0 then m * mul / 2^j.toNat else m * mul * 2^(-j).toNat
  JInt.lit .u64 (x.wrap shifted)

def ryuSmallPow5 (x : RyuSmall) (m : Nat) (q : Int) : Bool :=
  m % x.wrap (5^q.toNat) == 0

def ryuSmallPow2 (m : Nat) (q : Int) : Bool := m % 2^q.toNat == 0

def ryuSmallInitialE10 (e2 : Int) : Int :=
  if e2 ≥ 0 then log10pow2 e2 else log10pow5 (-e2) + e2

def ryuSmallInitialState (x : RyuSmall) (e2 : Int) (mfIsEven uShiftHalf : Bool)
    (u v w : Nat) : St :=
  let (a, b, c, e10, aAll, bAll, bLast) :=
    if e2 ≥ 0 then
      let q := log10pow2 e2
      let k := (x.pow5InvBitcount : Int) + pow5bits q - 1
      let i := -e2 + q + k
      let mul := ryuSmallPow5InvSplit x q
      let a := ryuSmallMulshift x u mul i
      let b := ryuSmallMulshift x v mul i
      let c := ryuSmallMulshift x w mul i
      let bLast := if q != 0 && x.sub c.val.toNat 1 / 10 ≤ a.val / 10 then
          JInt.lit .u8 ((ryuSmallMulshift x v (ryuSmallPow5InvSplit x (q - 1))
            (-e2 + q - 1 + ((x.pow5InvBitcount : Int) + pow5bits (q - 1) - 1))).val % 10)
        else JInt.lit .u8 0
      if q ≤ x.qinvbound then
        let vmod5 := v - 5 * (v / 5)
        if vmod5 == 0 then (a, b, c, q, false, ryuSmallPow5 x v q, bLast)
        else if mfIsEven then (a, b, c, q, ryuSmallPow5 x u q, false, bLast)
        else (a, b, JInt.lit .u64 (x.sub c.val.toNat (if ryuSmallPow5 x w q then 1 else 0)),
          q, false, false, bLast)
      else (a, b, c, q, false, false, bLast)
    else
      let q := log10pow5 (-e2)
      let e10 := q + e2
      let i := -e2 - q
      let k := pow5bits i - x.pow5Bitcount
      let j := q - k
      let mul := ryuSmallPow5Split x i
      let a := ryuSmallMulshift x u mul j
      let b := ryuSmallMulshift x v mul j
      let c := ryuSmallMulshift x w mul j
      let bLast := if q != 0 && x.sub c.val.toNat 1 / 10 ≤ a.val / 10 then
          let j' := q - 1 - (pow5bits (i + 1) - x.pow5Bitcount)
          JInt.lit .u8 ((ryuSmallMulshift x v (ryuSmallPow5Split x (i + 1)) j').val % 10)
        else JInt.lit .u8 0
      if q ≤ 1 then
        if mfIsEven then (a, b, c, e10, !uShiftHalf, true, bLast)
        else (a, b, JInt.lit .u64 (x.sub c.val.toNat 1), e10, false, true, bLast)
      else if q < x.qbound then
        (a, b, c, e10, false, ryuSmallPow2 v (q - 1), bLast)
      else (a, b, c, e10, false, false, bLast)
  { a := a, b := b, c := c, e10 := ryuSmallInitialE10 e2,
    aAll := aAll, bAll := bAll, bLast := bLast, roundup := false }

def ryuSmallLongPath (x : RyuSmall) (mf : Nat) (ef : Int) : Bool :=
  let mask := x.wrap (2^(-ef).toNat - 1)
  ef > 0 || ef < -(x.significandBits : Int) || ((x.wrap mf &&& mask) != 0)

def ryuSmallCore (x : RyuSmall) (rawM : Nat) (rawE ef : Int) (mf : Nat)
    (maxsignif : Option Int) : RyuU64 × Int :=
  let e2 := ef - 2
  let mfIsEven := mf % 2 == 0
  let v := x.wrap (4 * mf)
  let w := x.wrap (v + 2)
  let uShiftHalf := rawM == 0 && decide (rawE > 1)
  let u := x.wrap (x.sub v 2 + if uShiftHalf then 1 else 0)
  ryuFinish mfIsEven maxsignif (ryuSmallInitialState x e2 mfIsEven uShiftHalf u v w)

def ryuSmallEf (x : RyuSmall) : Int :=
  x.rawE - x.exponentBias - x.significandBits

def ryuSmallFixedEf (x : RyuSmall) : Int :=
  if x.rawE = 0 then 1 - x.exponentBias - x.significandBits else ryuSmallEf x

def ryuSmallReduce (x : RyuSmall) (maxsignif : Option Int) : RyuU64 × Int :=
  let rawM := x.rawM
  let rawE := x.rawE
  let mf := x.wrap (2^x.significandBits + rawM)
  let ef := ryuSmallEf x
  if ryuSmallLongPath x mf ef then
    let ef := ryuSmallFixedEf x
    let mf := if rawE = 0 then rawM else mf
    ryuSmallCore x rawM rawE ef mf maxsignif
  else
    let b := JInt.lit .u64 (x.wrap (mf / 2^(-ef).toNat))
    let (b, e10) := match maxsignif with
      | some M =>
        if b.val > M then
          let s := maxLoop M fuel ⟨b, b, b, 0, false, true, JInt.lit .u8 0, false⟩
          (s.b + ofBool .u64 s.roundup, s.e10)
        else (b, 0)
      | none => (b, 0)
    zeroLoop fuel (b, e10)

end JuliaLean.MemSafety.G2

namespace JuliaLean.base.ryu.Ryu

open JuliaLean JuliaLean.Float JuliaLean.Promotion

def smallFloat16 (x : Fl half) : JuliaLean.MemSafety.G2.RyuSmall :=
  .f16 x.bits

def smallFloat32 (x : Fl single) : JuliaLean.MemSafety.G2.RyuSmall :=
  .f32 x.bits

def writeReducedShortest (x : F64) (reduced : ParsePrint.Ryu.U64 × Int)
    (plus space hash : Bool) (precision : Int) (expchar : Nat)
    (padexp : Bool) (decchar : Nat) (defaultDigits : Int) :
    List Nat :=
  let (output, nexp) := reduced
  let sign := ParsePrint.Ryu.appendSign x plus space
  let olength := ParsePrint.Ryu.decimallength output
  let digits := ParsePrint.Ryu.cDigits olength output.val.toNat
  let pt : Int := nexp + olength
  let fixedForm :=
    -4 < pt ∧ pt ≤ (if precision == -1 then defaultDigits else precision) ∧
      ¬ (pt ≥ olength ∧
        F64.lt ParsePrint.Ryu.c005 (F64.abs (F64.sub
          (F64.mod (F64.add x ParsePrint.Ryu.c005)
            (F64.ofInt (JInt.wrap .i64 (10 ^ (pt - olength).toNat)).val))
          ParsePrint.Ryu.c005)))
  if fixedForm then
    if pt ≤ 0 then
      let pad := precision - olength
      sign ++ [48, decchar] ++ ParsePrint.Ryu.zeros pt.natAbs ++ digits ++
        (if hash then ParsePrint.Ryu.zeros pad.toNat else [])
    else if pt ≥ olength then
      let pad := precision - olength - nexp
      sign ++ digits ++ ParsePrint.Ryu.zeros nexp.toNat ++
        (if hash then [decchar] ++ (if pad < 0 then [48] else []) ++
          ParsePrint.Ryu.zeros pad.toNat else [])
    else
      let pointoff := olength - nexp.natAbs
      let pad := precision - olength
      sign ++ digits.take pointoff ++ [decchar] ++ digits.drop pointoff ++
        (if hash then ParsePrint.Ryu.zeros pad.toNat else [])
  else
    let (mant, pad) :=
      if olength > 1 || hash then
        (digits.take 1 ++ [decchar] ++ digits.drop 1, precision - olength)
      else (digits.take 1, precision)
    let mant := mant ++
      (if hash then (if olength == 1 then [48] else []) ++
        ParsePrint.Ryu.zeros pad.toNat else [])
    let exp2 : Int := nexp + olength - 1
    let (esign, exp2) :=
      if exp2 < 0 then ([45], -exp2) else if padexp then ([43], exp2) else ([], exp2)
    let e := exp2.toNat
    let edigits :=
      if exp2 ≥ 100 then ParsePrint.Ryu.d100 (e / 10) ++ [48 + e % 10]
      else if exp2 ≥ 10 then ParsePrint.Ryu.d100 e
      else (if padexp then [48] else []) ++ [48 + e]
    sign ++ mant ++ [expchar] ++ esign ++ edigits

def writeShortestSmall (x : F64) (reduced : ParsePrint.Ryu.U64 × Int)
    (plus space hash : Bool) (precision : Int) (expchar : Nat)
    (padexp : Bool) (decchar : Nat) (typed : Bool)
    (isFloat16 : Bool) : List Nat :=
  if F64.iszero x then
    let pre := if typed && isFloat16 then [70, 108, 111, 97, 116, 49, 54, 40] else []
    let sign := ParsePrint.Ryu.appendSign x plus space
    let body := [48] ++ (if hash then [decchar] else [])
    if precision == -1 then
      pre ++ sign ++ body ++ (if hash then [48] else []) ++
        (if typed && !isFloat16 then [102, 48] else []) ++
        (if typed && isFloat16 then [41] else [])
    else
      pre ++ sign ++ body ++
        (if hash && precision > 1 then ParsePrint.Ryu.zeros (precision - 1).toNat else []) ++
        (if typed && !isFloat16 then [102, 48] else []) ++
        (if typed && isFloat16 then [41] else [])
  else if F64.isnan x then
    ParsePrint.Ryu.appendSign x plus space ++ [78, 97, 78] ++
      (if typed then (if isFloat16 then [49, 54] else [51, 50]) else [])
  else if !F64.isfinite x then
    ParsePrint.Ryu.appendSign x plus space ++ [73, 110, 102] ++
      (if typed then (if isFloat16 then [49, 54] else [51, 50]) else [])
  else
    let pre := if typed && isFloat16 then [70, 108, 111, 97, 116, 49, 54, 40] else []
    let body := writeReducedShortest x reduced plus space hash precision expchar padexp decchar
      (if isFloat16 then 3 else 6)
    pre ++ body ++
      (if typed && isFloat16 then [41] else if typed then [102, 48] else [])

def writeshortest16 (x : Fl half) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (typed compact : Bool) :
    JuliaLean.Jl (List Nat) :=
  if precision < -1 then .error (.argumentError "precision must be at least -1")
  else
    let reduced := JuliaLean.MemSafety.G2.ryuSmallReduce (smallFloat16 x)
      (if compact then some (999999 : Int) else none)
    .ok (writeShortestSmall (Fl.toF64 (Fl.convert x)) reduced plus space hash precision
      expchar padexp decchar typed true)

def writeshortest32 (x : Fl single) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (typed compact : Bool) :
    JuliaLean.Jl (List Nat) :=
  if precision < -1 then .error (.argumentError "precision must be at least -1")
  else
    let reduced := JuliaLean.MemSafety.G2.ryuSmallReduce (smallFloat32 x)
      (if compact then some (999999 : Int) else none)
    .ok (writeShortestSmall (Fl.toF64 (Fl.convert x)) reduced plus space hash precision
      expchar padexp decchar typed false)

def writeshortest64 (x : F64) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (compact : Bool) :
    JuliaLean.Jl (List Nat) :=
  if precision < -1 then .error (.argumentError "precision must be at least -1")
  else .ok (ParsePrint.Ryu.writeshortest x plus space hash precision expchar padexp decchar compact)

inductive RyuShortestFloat where
  | float16 (value : Fl half)
  | float32 (value : Fl single)
  | float64 (value : F64)

/-!
Julia source: base/ryu/shortest.jl:1-226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    b, e10 = reduce_shortest(f[, maxsignif])

Reduce to shortest decimal representation where `abs(f) == b * 10^e10` and `b` is an
integer. If a `maxsignif` argument is provided, then `b < maxsignif`.
"""
@inline function reduce_shortest(f::T, maxsignif=nothing) where {T}
    U = uinttype(T)
    uf = reinterpret(U, f)
    m = uf & significand_mask(T)
    e = ((uf & exponent_mask(T)) >> significand_bits(T)) % Int

    ## Step 1
    #  mf * 2^ef == f
    mf = (one(U) << significand_bits(T)) | m
    ef = e - exponent_bias(T) - significand_bits(T)
    f_isinteger = mf & ((one(U) << -ef) -% one(U)) == 0

    if ef > 0 || ef < -Base.significand_bits(T) || !f_isinteger
        # fixup subnormals
        if e == 0
            ef = 1 - exponent_bias(T) - significand_bits(T)
            mf = m
        end

        ## Step 2
        #  u * 2^e2 == (f + prevfloat(f))/2
        #  v * 2^e2 == f
        #  w * 2^e2 == (f + nextfloat(f))/2
        e2 = ef - 2
        mf_iseven = iseven(mf) # trailing bit of significand is zero

        v = U(4) * mf
        w = v + U(2)
        u_shift_half = m == 0 && e > 1 # if first element of binade, other than first normal one
        u = v - U(2) + u_shift_half

        ## Step 3
        #  a == floor(u * 2^e2 / 10^e10), exact if a_allzero
        #  b == floor(v * 2^e2 / 10^e10), exact if b_allzero
        #  c == floor(w * 2^e2 / 10^e10)
        a_allzero = false
        b_allzero = false
        b_lastdigit = 0x00
        if e2 >= 0
            q = log10pow2(e2) - (T == Float64 ? (e2 > 3) : 0)
            e10 = q
            k = pow5_inv_bitcount(T) + pow5bits(q) - 1
            i = -e2 + q + k
            a, b, c = mulshiftinvsplit(T, u, v, w, q, i)
            if T == Float32 || T == Float16
                if q != 0 && div(c - 1, 10) <= div(a, 10)
                    l = pow5_inv_bitcount(T) + pow5bits(q - 1) - 1
                    mul = pow5invsplit_lookup(T, q-1)
                    b_lastdigit = (mulshift(v, mul, -e2 + q - 1 + l) % 10) % UInt8
                end
            end
            if q <= qinvbound(T)
                if ((v % UInt32) -% 5 *% div(v, 5)) == 0
                    b_allzero = pow5(v, q)
                elseif mf_iseven
                    a_allzero = pow5(u, q)
                else
                    c -= pow5(w, q)
                end
            end
        else
            q = log10pow5(-e2) - (T == Float64 ? (-e2 > 1) : 0)
            e10 = q + e2
            i = -e2 - q
            k = pow5bits(i) - pow5_bitcount(T)
            j = q - k
            a, b, c = mulshiftsplit(T, u, v, w, i, j)
            if T == Float32 || T == Float16
                if q != 0 && div(c - 1, 10) <= div(a, 10)
                    j = q - 1 - (pow5bits(i + 1) - pow5_bitcount(T))
                    mul = pow5split_lookup(T, i+1)
                    b_lastdigit = (mulshift(v, mul, j) % 10) % UInt8
                end
            end
            if q <= 1
                b_allzero = true
                if mf_iseven
                    a_allzero = !u_shift_half
                else
                    c -= 1
                end
            elseif q < qbound(T)
                b_allzero = pow2(v, q - (T != Float64))
            end
        end

        ## Step 4: reduction
        if a_allzero || b_allzero
            # a) slow loop
            while true
                c_div10 = div(c, 10)
                a_div10 = div(a, 10)
                if c_div10 <= a_div10
                    break
                end
                a_mod10 = (a % UInt32) -% UInt32(10) *% (a_div10 % UInt32)
                b_div10 = div(b, 10)
                b_mod10 = (b % UInt32) -% UInt32(10) *% (b_div10 % UInt32)
                a_allzero &= a_mod10 == 0
                b_allzero &= b_lastdigit == 0
                b_lastdigit = b_mod10 % UInt8
                b = b_div10
                c = c_div10
                a = a_div10
                e10 += 1
            end
            if a_allzero
                while true
                    a_div10 = div(a, 10)
                    a_mod10 = (a % UInt32) -% UInt32(10) *% (a_div10 % UInt32)
                    if a_mod10 != 0 && (maxsignif === nothing || b < maxsignif)
                        break
                    end
                    c_div10 = div(c, 10)
                    b_div10 = div(b, 10)
                    b_mod10 = (b % UInt32) -% UInt32(10) *% (b_div10 % UInt32)
                    b_allzero &= b_lastdigit == 0
                    b_lastdigit = b_mod10 % UInt8
                    b = b_div10
                    c = c_div10
                    a = a_div10
                    e10 += 1
                end
            end
            if b_allzero && b_lastdigit == 5 && iseven(b)
                b_lastdigit = UInt8(4)
            end
            roundup = (b == a && (!mf_iseven || !a_allzero)) || b_lastdigit >= 5
        else
            # b) specialized for common case (99% Float64, 96% Float32)
            roundup = b_lastdigit >= 5
            c_div100 = div(c, 100)
            a_div100 = div(a, 100)
            if c_div100 > a_div100
                b_div100 = div(b, 100)
                b_mod100 = (b % UInt32) -% UInt32(100) *% (b_div100 % UInt32)
                roundup = b_mod100 >= 50
                b = b_div100
                c = c_div100
                a = a_div100
                e10 += 2
            end
            while true
                c_div10 = div(c, 10)
                a_div10 = div(a, 10)
                if c_div10 <= a_div10
                    break
                end
                b_div10 = div(b, 10)
                b_mod10 = (b % UInt32) -% UInt32(10) *% (b_div10 % UInt32)
                roundup = b_mod10 >= 5
                b = b_div10
                c = c_div10
                a = a_div10
                e10 += 1
            end
            roundup = (b == a || roundup)
        end
        if maxsignif !== nothing && b > maxsignif
            # reduce to max significant digits
            while true
                b_div10 = div(b, 10)
                b_mod10 = (b % UInt32) -% UInt32(10) *% (b_div10 % UInt32)
                if b <= maxsignif
                    break
                end
                b = b_div10
                roundup = (b_allzero && iseven(b)) ? b_mod10 > 5 : b_mod10 >= 5
                b_allzero &= b_mod10 == 0
                e10 += 1
            end
            b = b + roundup

            # remove trailing zeros
            while true
                b_div10 = div(b, 10)
                b_mod10 = (b % UInt32) -% UInt32(10) *% (b_div10 % UInt32)
                if b_mod10 != 0
                    break
                end
                b = b_div10
                e10 += 1
            end
        else
            b = b + roundup
        end
    else
        # c) specialized f an integer < 2^53
        b = mf >> -ef
        e10 = 0

        if maxsignif !== nothing && b > maxsignif
            roundup = false
            b_allzero = true
            # reduce to max significant digits
            while true
                b_div10 = div(b, 10)
                b_mod10 = (b % UInt32) -% UInt32(10) *% (b_div10 % UInt32)
                if b <= maxsignif
                    break
                end
                b = b_div10
                roundup = (b_allzero && iseven(b)) ? b_mod10 > 5 : b_mod10 >= 5
                b_allzero &= b_mod10 == 0
                e10 += 1
            end
            b = b + roundup
        end
        while true
            b_div10 = div(b, 10)
            b_mod10 = (b % UInt32) -% UInt32(10) *% (b_div10 % UInt32)
            if b_mod10 != 0
                break
            end
            b = b_div10
            e10 += 1
        end
    end
    return b, e10
end
```
-/
def reduceShortest (x : RyuShortestFloat) (maxsignif : Option Int := none) :
    ParsePrint.Ryu.U64 × Int :=
  match x with
  | .float16 value =>
    JuliaLean.MemSafety.G2.ryuSmallReduce (smallFloat16 value) maxsignif
  | .float32 value =>
    JuliaLean.MemSafety.G2.ryuSmallReduce (smallFloat32 value) maxsignif
  | .float64 value => ParsePrint.Ryu.reduceShortest value maxsignif
structure ShortestBufferOps (Buffer : Type) where
  length : Buffer → Nat
  writeByte : Buffer → Nat → JInt .u8 → Buffer

inductive ShortestWriteError where
  | julia (error : JlError)
  | assertionError (message : String)

def liftShortestResult {A : Type} (result : JuliaLean.Jl A) : Except ShortestWriteError A :=
  match result with
  | .ok value => .ok value
  | .error error => .error (.julia error)

def shortestBytes (x : RyuShortestFloat) (plus space hash : Bool) (precision : Int)
    (expchar : Nat) (padexp : Bool) (decchar : Nat) (typed compact : Bool) :
    Except ShortestWriteError (List Nat) :=
  match x with
  | .float16 value =>
    liftShortestResult (writeshortest16 value plus space hash precision expchar padexp decchar typed compact)
  | .float32 value =>
    liftShortestResult (writeshortest32 value plus space hash precision expchar padexp decchar typed compact)
  | .float64 value =>
    liftShortestResult (writeshortest64 value plus space hash precision expchar padexp decchar compact)

def writeShortestBytes {Buffer : Type} (ops : ShortestBufferOps Buffer)
    (buffer : Buffer) (position : Nat) : List Nat → Buffer
  | [] => buffer
  | byte :: bytes =>
    writeShortestBytes ops (ops.writeByte buffer position (JInt.wrap .u8 (Int.ofNat byte)))
      (position + 1) bytes

/-!
Julia source: base/ryu/shortest.jl:228-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function writeshortest(buf::AbstractVector{UInt8}, pos, x::T,
                       plus=false, space=false, hash=true,
                       precision=-1, expchar=UInt8('e'), padexp=false, decchar=UInt8('.'),
                       typed=false, compact=false) where {T}
    pos = Int(pos)
    precision = Int(precision)
    precision >= -1 || throw(ArgumentError("precision must be at least -1"))
    @assert 0 < pos <= length(buf) "invalid pos"
    # special cases
    if x == 0
        if typed && x isa Float16
            @inbounds buf[pos] = UInt8('F')
            @inbounds buf[pos + 1] = UInt8('l')
            @inbounds buf[pos + 2] = UInt8('o')
            @inbounds buf[pos + 3] = UInt8('a')
            @inbounds buf[pos + 4] = UInt8('t')
            @inbounds buf[pos + 5] = UInt8('1')
            @inbounds buf[pos + 6] = UInt8('6')
            @inbounds buf[pos + 7] = UInt8('(')
            pos += 8
        end
        pos = append_sign(x, plus, space, buf, pos)
        @inbounds buf[pos] = UInt8('0')
        pos += 1
        if hash
            @inbounds buf[pos] = decchar
            pos += 1
        end
        if precision == -1
            if hash
                @inbounds buf[pos] = UInt8('0')
                pos += 1
            end
            if typed && x isa Float32
                @inbounds buf[pos] = UInt8('f')
                @inbounds buf[pos + 1] = UInt8('0')
                pos += 2
            end
            if typed && x isa Float16
                @inbounds buf[pos] = UInt8(')')
                pos += 1
            end
            return pos
        end
        while hash && precision > 1
            @inbounds buf[pos] = UInt8('0')
            pos += 1
            precision -= 1
        end
        if typed && x isa Float32
            @inbounds buf[pos] = UInt8('f')
            @inbounds buf[pos + 1] = UInt8('0')
            pos += 2
        end
        if typed && x isa Float16
            @inbounds buf[pos] = UInt8(')')
            pos += 1
        end
        return pos
    elseif isnan(x)
        pos = append_sign(x, plus, space, buf, pos)
        @inbounds buf[pos] = UInt8('N')
        @inbounds buf[pos + 1] = UInt8('a')
        @inbounds buf[pos + 2] = UInt8('N')
        if typed
            if x isa Float32
                @inbounds buf[pos + 3] = UInt8('3')
                @inbounds buf[pos + 4] = UInt8('2')
            elseif x isa Float16
                @inbounds buf[pos + 3] = UInt8('1')
                @inbounds buf[pos + 4] = UInt8('6')
            end
        end
        return pos + 3 + (typed && x isa Union{Float32, Float16} ? 2 : 0)
    elseif !isfinite(x)
        pos = append_sign(x, plus, space, buf, pos)
        @inbounds buf[pos] = UInt8('I')
        @inbounds buf[pos + 1] = UInt8('n')
        @inbounds buf[pos + 2] = UInt8('f')
        if typed
            if x isa Float32
                @inbounds buf[pos + 3] = UInt8('3')
                @inbounds buf[pos + 4] = UInt8('2')
            elseif x isa Float16
                @inbounds buf[pos + 3] = UInt8('1')
                @inbounds buf[pos + 4] = UInt8('6')
            end
        end
        return pos + 3 + (typed && x isa Union{Float32, Float16} ? 2 : 0)
    end

    output, nexp = reduce_shortest(x, compact ? 999_999 : nothing)

    if typed && x isa Float16
        @inbounds buf[pos] = UInt8('F')
        @inbounds buf[pos + 1] = UInt8('l')
        @inbounds buf[pos + 2] = UInt8('o')
        @inbounds buf[pos + 3] = UInt8('a')
        @inbounds buf[pos + 4] = UInt8('t')
        @inbounds buf[pos + 5] = UInt8('1')
        @inbounds buf[pos + 6] = UInt8('6')
        @inbounds buf[pos + 7] = UInt8('(')
        pos += 8
    end
    pos = append_sign(x, plus, space, buf, pos)

    olength = decimallength(output)
    exp_form = true
    pt = nexp + olength
    if -4 < pt <= (precision == -1 ? (T == Float16 ? 3 : 6) : precision) &&
        !(pt >= olength && abs(mod(x + 0.05, 10^(pt - olength)) - 0.05) > 0.05)
        exp_form = false
        if pt <= 0
            @inbounds buf[pos] = UInt8('0')
            pos += 1
            @inbounds buf[pos] = decchar
            pos += 1
            for _ = 1:abs(pt)
                @inbounds buf[pos] = UInt8('0')
                pos += 1
            end
        # elseif pt >= olength
            # nothing to do at this point
        # else
            # nothing to do at this point
        end
    else
        # make space for decchar
        pos += 1
    end

    append_c_digits(olength, output, buf, pos)

    if !exp_form
        if pt <= 0
            pos += olength
            precision -= olength
        elseif pt >= olength
            pos += olength
            precision -= olength
            for _ = 1:nexp
                @inbounds buf[pos] = UInt8('0')
                pos += 1
                precision -= 1
            end
            if hash
                @inbounds buf[pos] = decchar
                pos += 1
                if precision < 0
                    @inbounds buf[pos] = UInt8('0')
                    pos += 1
                end
            end
        else
            pointoff = olength - abs(nexp)
            # shift bytes after pointoff to make room for decchar
            buf_cconv = Base.cconvert(Ptr{UInt8}, buf)
            GC.@preserve buf_cconv begin
                ptr = Base.unsafe_convert(Ptr{UInt8}, buf_cconv)
                memmove(ptr + pos + pointoff, ptr + pos + pointoff - 1, (olength - pointoff)%Csize_t)
            end
            @inbounds buf[pos + pointoff] = decchar
            pos += olength + 1
            precision -= olength
        end
        if hash
            while precision > 0
                @inbounds buf[pos] = UInt8('0')
                pos += 1
                precision -= 1
            end
        end
        if typed && x isa Float32
            @inbounds buf[pos] = UInt8('f')
            @inbounds buf[pos + 1] = UInt8('0')
            pos += 2
        end
    else
        # move leading digit into place
        @inbounds buf[pos - 1] = buf[pos]
        if olength > 1 || hash
            @inbounds buf[pos] = decchar
            pos += olength
            precision -= olength
        end
        if hash
            if olength == 1
                @inbounds buf[pos] = UInt8('0')
                pos += 1
            end
            while precision > 0
                @inbounds buf[pos] = UInt8('0')
                pos += 1
                precision -= 1
            end
        end

        @inbounds buf[pos] = expchar
        pos += 1
        exp2 = nexp + olength - 1
        if exp2 < 0
            @inbounds buf[pos] = UInt8('-')
            pos += 1
            exp2 = -exp2
        elseif padexp
            @inbounds buf[pos] = UInt8('+')
            pos += 1
        end

        if exp2 >= 100
            c = exp2 % 10
            @inbounds d100 = DIGIT_TABLE16[(div(exp2, 10) % Int) + 1]
            @inbounds buf[pos] = d100 % UInt8
            @inbounds buf[pos + 1] = (d100 >> 0x8) % UInt8
            @inbounds buf[pos + 2] = UInt8('0') + (c % UInt8)
            pos += 3
        elseif exp2 >= 10
            @inbounds d100 = DIGIT_TABLE16[(exp2 % Int) + 1]
            @inbounds buf[pos] = d100 % UInt8
            @inbounds buf[pos + 1] = (d100 >> 0x8) % UInt8
            pos += 2
        else
            if padexp
                @inbounds buf[pos] = UInt8('0')
                pos += 1
            end
            @inbounds buf[pos] = UInt8('0') + (exp2 % UInt8)
            pos += 1
        end
    end
    if typed && x isa Float16
        @inbounds buf[pos] = UInt8(')')
        pos += 1
    end

    return pos
end
```
-/
def writeshortestBuffer {Buffer : Type} (ops : ShortestBufferOps Buffer)
    (buffer : Buffer) (pos : Int) (x : RyuShortestFloat)
    (plus : Bool := false) (space : Bool := false) (hash : Bool := true)
    (precision : Int := -1) (expchar : Nat := 101) (padexp : Bool := false)
    (decchar : Nat := 46) (typed : Bool := false) (compact : Bool := false) :
    Except ShortestWriteError (Buffer × Int) := do
  if precision < -1 then
    throw (.julia (.argumentError "precision must be at least -1"))
  if !decide (0 < pos ∧ pos ≤ Int.ofNat (ops.length buffer)) then
    throw (.assertionError "invalid pos")
  let bytes ← shortestBytes x plus space hash precision expchar padexp decchar typed compact
  let updated := writeShortestBytes ops buffer pos.toNat bytes
  pure (updated, pos + Int.ofNat bytes.length)
end JuliaLean.base.ryu.Ryu

