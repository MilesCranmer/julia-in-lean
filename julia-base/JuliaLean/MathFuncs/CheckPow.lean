import JuliaLean.MathFuncs.Pow

/-!
Differential corpus for `JuliaLean.MathFuncs.Pow`. Run with
`lake env lean --run JuliaLean/MathFuncs/CheckPow.lean ff|fi [start] [count]` and compare
with `julia repro/mathfuncs-differential-pow.jl`, which prints the
`ff` lines followed by the `fi` lines.
-/

namespace JuliaLean.MathFuncs.CheckPow

open JuliaLean.Float

/-- 64-bit LCG step shared with the Julia oracle. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

/-- `lo + (hi - lo) * (Float64(r >> 11) / 2.0^53)`. -/
def unif (r : Nat) (lo hi : F64) : F64 :=
  F64.add lo (F64.mul (F64.sub hi lo) (F64.div (F64.ofInt (r / 2^11)) (lit 0x4340000000000000)))

/-- A random bit pattern with biased exponent in `[e0, e0 + w)`, negative with
probability `1/neg`. -/
def randBits (s1 s2 : Nat) (e0 w neg : Nat) : Nat :=
  (if (s1 / 2^20) % neg == 0 then 2^63 else 0) + (e0 + (s1 / 2^11) % w) * 2^52 + s2 % 2^52

/-- Special bases. -/
def xSpecials : List Nat := [0, 2^63, 0x3ff0000000000000, 0xbff0000000000000,
  0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 1, 2^63 + 1,
  0x000fffffffffffff, 0x800fffffffffffff, 0x0010000000000000, 0x8010000000000000,
  0x7fefffffffffffff, 0xffefffffffffffff, 0x4000000000000000, 0xc000000000000000,
  0x3fe0000000000000, 0xbfe0000000000000, 0x4008000000000000, 0xc008000000000000,
  0x4024000000000000, 0x3ff0000000000001, 0x3fefffffffffffff, 0xbfefffffffffffff,
  0xbff0000000000001, 2, 0x3ff8000000000000, 0x7fe0000000000000, 0x0008000000000000,
  0x01a56e1fc2f8f359, 0x3fb999999999999a, 0xbfb999999999999a]

/-- Positive special exponents; each is used with both signs. -/
def yPos : List Nat := [0, 0x3ff0000000000000, 0x4000000000000000, 0x4008000000000000,
  0x3fe0000000000000, 0x7ff0000000000000, 0x40d8000000000000, 0x40d8004000000000,
  0x40b0000000000000, 0x40b0010000000000, 0x433fffffffffffff, 0x43d8000000000000,
  0x43d7ffffffffffff, 0x43d8000000000001, 0x7e37e43c8800759c, 0x3ff8000000000000,
  0x4004000000000000, 0x01a56e1fc2f8f359, 1, 0x43e0000000000000, 0x408ff80000000000,
  0x4090000000000000, 0x4090c80000000000, 0x4090cc0000000000, 0x40d8002000000000,
  0x40b0008000000000, 0x40affe0000000000, 0x40afff0000000000, 0x7fefffffffffffff]

/-- Special exponents. -/
def ySpecials : List Nat :=
  yPos ++ yPos.map (· + 2^63) ++ [0x7ff8000000000000, 0xfff8000000000000]

/-- Divisors `k` of the near-overflow/underflow exponents. -/
def kList : List Int := [1, 2, 3, 5, 8, 13, -1, -2, -3, -5, -8, -13]

/-- `(x, y)` bit-pattern pairs for `^(::Float64, ::Float64)`. -/
def ffPairs : Array (Nat × Nat) := Id.run do
  let mut a : Array (Nat × Nat) := #[]
  for x in xSpecials do
    for y in ySpecials do
      a := a.push (x, y)
  let mut s : Nat := 0x853c49e6748fea9b
  for _ in [0:1800] do
    s := lcg s
    let s1 := s
    s := lcg s
    let x := randBits s1 s 1003 41 4
    s := lcg s
    a := a.push (x, bitsOf (unif s (lit 0xc04e000000000000) (lit 0x404e000000000000)))
  for _ in [0:300] do
    s := lcg s
    let s1 := s
    s := lcg s
    let x := randBits s1 s 1003 41 2
    s := lcg s
    let m : Int := ((s / 2^11) % 35000 : Nat) - 5000
    a := a.push (x, bitsOf (F64.ofInt m))
  for k in kList do
    for _ in [0:125] do
      s := lcg s
      let base := F64.mul (lit (((1023 + k) * 2^52).toNat))
        (F64.add F64.one (unif s F64.zero (lit 0x3f50000000000000)))
      s := lcg s
      let t := if s / 2^63 == 0 then unif s (lit 0x408fb80000000000) (lit 0x4090080000000000)
        else unif s (lit 0xc090e00000000000) (lit 0xc08fb80000000000)
      a := a.push (bitsOf base, bitsOf (F64.div t (F64.ofInt k)))
  for _ in [0:200] do
    s := lcg s
    let x := s % 2^52
    s := lcg s
    a := a.push (x, bitsOf (unif s (lit 0xbff3333333333333) (lit 0x3ff3333333333333)))
  for _ in [0:400] do
    s := lcg s
    let x := unif s (lit 0x3fefffffff800000) (lit 0x3ff0000000400000)
    let x := if (s / 2^20) % 2 == 0 then F64.neg x else x
    s := lcg s
    let m : Int := ((s / 2^11) % 2^40 : Nat) + 24577
    let m := if (s / 2^5) % 3 == 0 then -m else m
    a := a.push (bitsOf x, bitsOf (F64.ofInt m))
  for _ in [0:400] do
    s := lcg s
    let x := s
    s := lcg s
    a := a.push (x, s)
  return a

/-- Integer exponents with the Julia type used by the oracle (`i64`, `i128`, `u64`, `big`). -/
def nList : List (String × Int) :=
  (([0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -4096, -4097, -4095, 24576, 24577, 24575, 30000, 100001,
    -100001, 1023, -1023, 1024, -1074, -1075, 1075, 1025, -1025, 2^53, 2^53 + 1, -(2^53 + 1),
    2^62 + 1, 2^62, 1048575, -1048575, -2^63, -2^63 + 1, 2^63 - 1, 2^63 - 2] : List Int).map
    (("i64", ·)))
  ++ [("i128", 2^63), ("i128", -2^63 - 1), ("i128", 2^64 + 1), ("i128", -2^64 - 1),
    ("i128", 2^64), ("u64", 2^63 + 1), ("u64", 2^64 - 1), ("u64", 2^63),
    ("big", 2^100 + 1), ("big", -2^100 - 1), ("big", 2^100), ("big", -2^100)]

/-- Bases for the integer-exponent grid. -/
def fiBases : Array Nat := Id.run do
  let mut a : Array Nat := xSpecials.toArray
  for d in [1, 2, 3, 10, 1000] do
    a := a.push (0x3ff0000000000000 + d) |>.push (0x3ff0000000000000 - d)
    a := a.push (0xbff0000000000000 + d)
  for b in [0x3feffffe00000000, 0x3ff0000100000000, 0x3fefffffffffe000, 0x3ff0000000001000] do
    a := a.push b |>.push (b + 2^63)
  let mut s : Nat := 0xda3e39cb94b95bdb
  for _ in [0:30] do
    s := lcg s
    let s1 := s
    s := lcg s
    a := a.push (randBits s1 s 983 81 2)
  return a

/-- `(x, n)` pairs for `^(::Float64, ::Integer)`. -/
def fiPairs : Array (Nat × String × Int) := Id.run do
  let mut a : Array (Nat × String × Int) := #[]
  for x in fiBases do
    for (ty, n) in nList do
      a := a.push (x, ty, n)
  let mut s : Nat := 0x6a09e667f3bcc909
  for _ in [0:1000] do
    s := lcg s
    let s1 := s
    s := lcg s
    let x := randBits s1 s 1013 21 2
    s := lcg s
    a := a.push (x, "i64", ((s / 2^11) % 35000 : Nat) - 5000)
  for _ in [0:500] do
    s := lcg s
    let x := unif s (lit 0x3feffffffffffff8) (lit 0x3ff0000000000004)
    let x := if (s / 2^20) % 2 == 0 then F64.neg x else x
    s := lcg s
    let n : Int := if s ≥ 2^63 then (s : Int) - 2^64 else s
    a := a.push (bitsOf x, "i64", n)
  return a

/-- Decimal UInt64 bits, `nan`, or the error kind. -/
def out : Jl F64 → String
  | .ok x => if F64.isnan x then "nan" else toString (bitsOf x)
  | .error (.domainError _) => "domain"
  | .error .boundsError => "bounds"
  | .error (.methodError _) => "method"
  | .error _ => "other"

/-- Print the `ff` or `fi` corpus slice. -/
def main (args : List String) : IO Unit := do
  let start := (args[1]?.bind String.toNat?).getD 0
  let count := (args[2]?.bind String.toNat?).getD 1000000
  if args[0]? == some "fi" then
    let ps := fiPairs
    for j in [start:min ps.size (start + count)] do
      let (x, _, n) := ps[j]!
      IO.println s!"{j} powfi {out (.ok (powFI (lit x) n))}"
  else
    let ps := ffPairs
    for j in [start:min ps.size (start + count)] do
      let (x, y) := ps[j]!
      IO.println s!"{j} powff {out (powFF (lit x) (lit y))}"

end JuliaLean.MathFuncs.CheckPow

/-- Entry point. -/
def main (args : List String) : IO Unit := JuliaLean.MathFuncs.CheckPow.main args
