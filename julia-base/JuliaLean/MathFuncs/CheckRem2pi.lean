import JuliaLean.MathFuncs.Rem2pi

/-!
Differential test of `remPio2Kernel`, `paynehanek`, `rem2pi` and `mod2pi` against
`repro/mathfuncs-differential-rem2pi.jl`. Run with
`lake env lean --run JuliaLean/MathFuncs/CheckRem2pi.lean [start count]`.
-/

namespace JuliaLean.MathFuncs.CheckRem2pi

open JuliaLean.Float JuliaLean.MathFuncs

/-- One step of the 64-bit LCG shared with the Julia oracle. -/
def step (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

/-- Edge bit patterns; each is also used with the sign bit set. -/
def edges : List Nat := [0, 1, 2, 0x000ffffffffffffe, 0x000fffffffffffff,
  0x0010000000000000, 0x0010000000000001, 0x3fe0000000000000, 0x3ff0000000000000,
  0x4000000000000000, 0x3ff8000000000000, 0x4004000000000000, 0x4330000000000000,
  0x4340000000000000, 0x43e0000000000000, 0x7feffffffffffffe, 0x7fefffffffffffff,
  0x7ff0000000000000, 0x7ff0000000000001, 0x7ff8000000000000, 0x7fffffffffffffff]

/-- High-word thresholds of `rem_pio2_kernel` and the high words of π/4, π/2, π. -/
def thresholds : List Nat := [0x400f6a7a, 0x4002d97c, 0x401c463b, 0x4015fdbc, 0x4012d97c,
  0x401921fb, 0x413921fb, 0x3ff921fb, 0x400921fb, 0x3fe921fb]

/-- The deterministic corpus of Float64 bit patterns. -/
def corpus : Array Nat := Id.run do
  let mut ws : Array Nat := #[]
  let mut st : Nat := 0x9e3779b97f4a7c15
  for w in edges do
    ws := ws.push w |>.push (w + 2^63)
  for k in [0:41] do
    let a := F64.ofInt k
    let h := F64.div (F64.ofInt (2 * k + 1)) (F64.ofInt 2)
    ws := ws.push (bitsOf a) |>.push (bitsOf (F64.neg a))
    ws := ws.push (bitsOf h) |>.push (bitsOf (F64.neg h))
  for b in [0x3ff921fb54442d18, 0x3fe921fb54442d18] do
    for k in [0:201] do
      let c := F64.mul (F64.ofInt ((k : Int) - 100)) (lit b)
      for d in [0:7] do
        ws := ws.push (bitsOf (F64.nextfloat c ((d : Int) - 3)))
  for t in thresholds do
    for dh in [0:3] do
      let h := t + dh - 1
      st := step st
      for lo in [0, 1, 0x7fffffff, 0xffffffff, st / 2^32] do
        let w := h * 2^32 + lo
        ws := ws.push w |>.push (w + 2^63)
  for e in [0:1041] do
    st := step st
    let s := (st / 2^63) * 2^63
    ws := ws.push (s + (e * 2^20 + 0x921fb) * 2^32 + st % 2^32)
    ws := ws.push (s + (e * 2^20 + 0x921fa) * 2^32 + 0xffffffff)
    ws := ws.push (s + (e * 2^20 + 0x921fc) * 2^32)
  let c := F64.ldexp (lit 0x3ff921fb54442d18) 20
  for d in [0:7] do
    let v := F64.nextfloat c ((d : Int) - 3)
    ws := ws.push (bitsOf v) |>.push (bitsOf (F64.neg v))
  for b in [0x401921fb54442d18, 0x400921fb54442d18, 0x4012d97c7f3321d2, 0x3ff921fb54442d18] do
    for d in [0:7] do
      let v := F64.nextfloat (lit b) ((d : Int) - 3)
      ws := ws.push (bitsOf v) |>.push (bitsOf (F64.neg v))
  for e in [0:2047] do
    for _ in [0:2] do
      st := step st
      ws := ws.push ((st % 2) * 2^63 + e * 2^52 + st / 2^12)
  for _ in [0:1500] do
    st := step st
    let r1 := st
    st := step st
    ws := ws.push ((r1 / 2^63) * 2^63 + (1000 + r1 % 48) * 2^52 + st / 2^12)
  for _ in [0:500] do
    st := step st
    ws := ws.push st
  return ws

/-- Decimal bit pattern, or `nan`. -/
def out (x : F64) : String := if F64.isnan x then "nan" else toString (bitsOf x)

/-- A `Jl F64` result: bit pattern, `nan`, or the error kind. -/
def outJl : Jl F64 → String
  | .ok x => out x
  | .error (.methodError _) => "method"
  | .error (.domainError _) => "domain"
  | .error .boundsError => "bounds"
  | .error e => s!"unexpected:{repr e}"

/-- Print every operation on corpus entries `start ..< start+count`. -/
def run (start count : Nat) : IO Unit := do
  let ws := corpus
  for j in [start:min ws.size (start + count)] do
    let x := F64.ofBits ws[j]!
    let (n, hi, lo) := remPio2Kernel x
    IO.println s!"{j} kn {n}"
    IO.println s!"{j} khi {out hi}"
    IO.println s!"{j} klo {out lo}"
    if (bitsOf x / 2^32) % 2^31 ≥ 0x413921fb then
      let (q, phi, plo) := paynehanek x
      IO.println s!"{j} pn {q}"
      IO.println s!"{j} phi {out phi}"
      IO.println s!"{j} plo {out plo}"
    IO.println s!"{j} rn {outJl (rem2pi x .RoundNearest)}"
    IO.println s!"{j} rz {outJl (rem2pi x .RoundToZero)}"
    IO.println s!"{j} rd {outJl (rem2pi x .RoundDown)}"
    IO.println s!"{j} ru {outJl (rem2pi x .RoundUp)}"
    IO.println s!"{j} ra {outJl (rem2pi x .RoundNearestTiesAway)}"
    IO.println s!"{j} m2 {out (mod2pi x)}"

end JuliaLean.MathFuncs.CheckRem2pi

def main (args : List String) : IO Unit :=
  JuliaLean.MathFuncs.CheckRem2pi.run ((args[0]?.bind String.toNat?).getD 0)
    ((args[1]?.bind String.toNat?).getD 100000)
