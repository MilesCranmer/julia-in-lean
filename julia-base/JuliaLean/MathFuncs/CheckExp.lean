import JuliaLean.MathFuncs.Exp

/-!
Differential corpus for `JuliaLean.MathFuncs.Exp`. Run with
`lake env lean --run JuliaLean/MathFuncs/CheckExp.lean float|int [start] [count]` and compare
with `julia repro/mathfuncs-differential-exp.jl`, which prints the
`float` lines followed by the `int` lines.
-/

namespace JuliaLean.MathFuncs.CheckExp

open JuliaLean.Float

/-- 64-bit LCG step shared with the Julia oracle. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

/-- Edge bit patterns. -/
def specials : List Nat := [0, 2^63, 1, 2^63 + 1, 0x000fffffffffffff, 0x800fffffffffffff,
  0x0010000000000000, 0x8010000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
  0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0xfff8000000000000,
  0x7ff0000000000001, 0x3ff0000000000000, 0xbff0000000000000, 0x3fe0000000000000,
  0xbfe0000000000000, 0x3c90000000000000, 0xbc90000000000000]

/-- Branch thresholds; each is printed with its ±50-ulp neighbourhood. -/
def thresholds : List Nat := [0x4090000000000000, 0x40862e42fefa39f0, 0x40734413509f79ff,
  0xc090cc0000000000, 0xc0874910d52d3052, 0xc07439b746e36b52,
  0x408ff00000000000, 0x4086232bdd7abcd2, 0x40733a7146f72a41,
  0xc08ff00000000000, 0xc086232bdd7abcd2, 0xc0733a7146f72a41,
  0xbfd269621134db92, 0x3fcc8ff7c79a9a22, 0x40862e42fefa39f4, 0xc042b708872320e2,
  0x4042b708872320e2, 0, 0x0010000000000000, 0x7fefffffffffffff]

/-- Multipliers `k` placed at `k*log(b,2)` boundaries of the reduction. -/
def kList : List Int := [-1080, -1077, -1076, -1075, -1074, -1073, -1060, -1023, -1022,
  -1021, -1000, -60, -55, -54, -53, -52, -51, -3, -2, -1, 1, 2, 52, 53, 54, 105, 106, 107,
  500, 1022, 1023, 1024, 1025]

/-- `log(2)`, `log10(2)`, `1.0`. -/
def kScales : List F64 := [lit 0x3fe62e42fefa39ef, lit 0x3fd34413509f79ff, F64.one]

/-- `lo + (hi - lo) * (Float64(r >> 11) / 2.0^53)`. -/
def unif (r : Nat) (lo hi : F64) : F64 :=
  F64.add lo (F64.mul (F64.sub hi lo) (F64.div (F64.ofInt (r / 2^11)) (lit 0x4340000000000000)))

/-- Float inputs as bit patterns. -/
def inputs : Array Nat := Id.run do
  let mut a : Array Nat := specials.toArray
  for t in thresholds do
    for j in [0:101] do
      a := a.push (bitsOf (F64.nextfloat (lit t) ((j : Int) - 50)))
  for k in kList do
    for c in kScales do
      let x := F64.mul (F64.ofInt k) c
      for j in [0:7] do
        a := a.push (bitsOf (F64.nextfloat x ((j : Int) - 3)))
  let mut s : Nat := 0x9e3779b97f4a7c15
  for _ in [0:200] do
    s := lcg s
    let m : Int := ((s / 2^11) % 537000 : Nat) - 275000
    let x := F64.div (F64.ofInt (2 * m + 1)) (lit 0x4080000000000000)
    a := a.push (bitsOf x) |>.push (bitsOf (F64.nextfloat x 1)) |>.push (bitsOf (F64.prevfloat x 1))
  for c in [lit 0x40771547652b82fe, lit 0x408a934f0979a371] do
    for _ in [0:100] do
      s := lcg s
      let m : Int := ((s / 2^11) % 537000 : Nat) - 275000
      let x := F64.div (F64.add (F64.ofInt m) (lit 0x3fe0000000000000)) c
      for j in [0:5] do
        a := a.push (bitsOf (F64.nextfloat x ((j : Int) - 2)))
  for b in [ExpBase.two, .e, .ten] do
    for _ in [0:150] do
      s := lcg s
      a := a.push (bitsOf (unif s (minExp b) (F64.neg (subnormExp b))))
  for (n, lo, hi) in [(600, lit 0xc087700000000000, lit 0x4087700000000000),
      (600, lit 0xc091300000000000, lit 0x4091300000000000),
      (600, lit 0xc044000000000000, lit 0x4044000000000000),
      (400, lit 0xbff0000000000000, lit 0x3ff0000000000000)] do
    for _ in [0:n] do
      s := lcg s
      a := a.push (bitsOf (unif s lo hi))
  for _ in [0:300] do
    s := lcg s
    let e := 953 + (s / 2^11) % 82
    s := lcg s
    a := a.push ((s / 2^63) * 2^63 + e * 2^52 + s % 2^52)
  for _ in [0:200] do
    s := lcg s
    a := a.push s
  return a

/-- Decimal UInt64 bits, or `nan`. -/
def out (x : F64) : String := if F64.isnan x then "nan" else toString (bitsOf x)

/-- The ten integer types in oracle order. -/
def types : List IntTy := [.i8, .i16, .i32, .i64, .i128, .u8, .u16, .u32, .u64, .u128]

/-- Integer inputs for one type, before range filtering. -/
def intCandidates (t : IntTy) : Array Int := Id.run do
  let mut a : Array Int := #[t.min, t.min + 1, t.min + 2, t.max, t.max - 1, -1, 0, 1, 2]
  for v in [0:2301] do
    a := a.push ((v : Int) - 1150)
  for j in [0:80] do
    a := a.push (-(2^64 : Int) - 1074 + (j : Int) - 5)
    a := a.push (-(2^65 : Int) - 1074 + (j : Int) - 5)
    a := a.push (-(2^127 : Int) + (j : Int))
    a := a.push ((2^64 : Int) - 1074 + (j : Int) - 5)
  let mut s : Nat := 0x2545f4914f6cdd1d + t.bits
  for _ in [0:100] do
    s := lcg s
    let hi := s
    s := lcg s
    let w : Int := ((hi * 2^64 + s) % 2^t.bits : Nat)
    a := a.push (if t.signed && w ≥ 2^(t.bits - 1) then w - 2^t.bits else w)
  return a.filter (fun v => t.min ≤ v ∧ v ≤ t.max)

/-- Print the float or integer corpus slice. -/
def main (args : List String) : IO Unit := do
  let start := (args[1]?.bind String.toNat?).getD 0
  let count := (args[2]?.bind String.toNat?).getD 1000000
  if args[0]? == some "int" then
    let mut i := 0
    for t in types do
      for v in intCandidates t do
        if start ≤ i ∧ i < start + count then
          IO.println s!"{i} exp2i_{t.name} {out (exp2Int (JInt.wrap t v))}"
        i := i + 1
  else
    let xs := inputs
    for j in [start:min xs.size (start + count)] do
      let x := lit xs[j]!
      IO.println s!"{j} in {xs[j]!}"
      IO.println s!"{j} exp {out (exp x)}"
      IO.println s!"{j} exp2 {out (exp2 x)}"
      IO.println s!"{j} exp10 {out (exp10 x)}"
      IO.println s!"{j} expm1 {out (expm1 x)}"
      let xlo := F64.mul x (lit 0x3c80000000000000)
      IO.println s!"{j} explo {out (expImplLo x xlo .e)}"

end JuliaLean.MathFuncs.CheckExp

/-- Entry point. -/
def main (args : List String) : IO Unit := JuliaLean.MathFuncs.CheckExp.main args
