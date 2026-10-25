import JuliaLean.MathFuncs.Trig
import JuliaLean.MathFuncs.Cbrt

/-!
Differential corpus for the `sinpi`/`cospi`/`sincospi`/`tanpi`/`cbrt` models. Run with
`lake env lean --run JuliaLean/MathFuncs/CheckTrig.lean nightly|release [start] [count]`
and compare with `julia repro/mathfuncs-differential-trig.jl` run on the matching Julia
version (`release` is 1.13.2, `nightly` is master).
The integer-method lines are printed when `start` is 0.
-/

namespace JuliaLean.MathFuncs.CheckTrig

open JuliaLean.Float

/-- One step of the 64-bit LCG shared with the Julia oracle. -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

/-- Bit pattern of the exact value `n / 2^k` (or `n * 2^-k` for negative `k`). -/
def ratBits (n : Int) (k : Int) : Nat :=
  if k ≥ 0 then F64.toBits (F64.roundRat n (2^k.toNat) false)
  else F64.toBits (F64.roundRat (n * 2^(-k).toNat) 1 false)

def edges : List Nat :=
  [0, 1, 2, 0x000ffffffffffffe, 0x000fffffffffffff, 0x0010000000000000,
   0x0010000000000001, 0x3ff0000000000000, 0x3fefffffffffffff, 0x3ff0000000000001,
   0x7fefffffffffffff, 0x7feffffffffffffe, 0x7ff0000000000000, 0x7ff8000000000000,
   0x7ff0000000000001, 0x7fffffffffffffff, 0x3e10000000000000, 0x3cb0000000000000]

def words : Array Nat := Id.run do
  let mut ws : Array Nat := #[]
  for w in edges do
    ws := ws.push w |>.push (w + 2^63)
  for i in [0:401] do
    let k : Int := (i : Int) - 200
    if k != 0 then
      let w := ratBits k 3
      for j in [0:5] do
        ws := ws.push (w + j - 2)
  for i in [0:2098] do
    ws := ws.push (ratBits 1 (1074 - (i : Int)))
  for e in [51, 52, 53] do
    let w := ratBits 1 (-(e : Int))
    for j in [0:41] do
      ws := ws.push (w + j - 20) |>.push (w + j - 20 + 2^63)
  for m in [1:301] do
    ws := ws.push (ratBits ((m : Int)^3) 0) |>.push (ratBits (-(m : Int)^3) 0)
  for j in [-350, -100, -20, 20, 100, 300] do
    for m in [1:21] do
      ws := ws.push (ratBits ((m : Int)^3) (-3 * j))
  let mut s := 0x243f6a8885a308d3
  for _ in [0:3000] do
    s := lcg s
    let e := s / 2^53 % 91
    let sign := s / 2^52 % 2
    ws := ws.push (sign * 2^63 + (e + 1023 - 30) * 2^52 + s % 2^52)
  for _ in [0:1000] do
    s := lcg s
    ws := ws.push s
  for _ in [0:300] do
    s := lcg s
    ws := ws.push (s / 2^63 * 2^63 + s % 2^52)
  return ws

def ints : Array Int := Id.run do
  let mut xs : Array Int := #[]
  for i in [0:41] do
    xs := xs.push ((i : Int) - 20)
  for v in [-(2^63 : Int), 2^63 - 1, -(2^63 : Int) + 1, 2^63 - 2, 2^53, 2^53 + 1, -(2^53 : Int) - 1] do
    xs := xs.push v
  let mut s := 0x9e3779b97f4a7c15
  for _ in [0:200] do
    s := lcg s
    xs := xs.push (if s ≥ 2^63 then (s : Int) - 2^64 else (s : Int))
  return xs

def out (x : F64) : String := if F64.isnan x then "nan" else toString (F64.toBits x)

def outJl : Jl F64 → String
  | .ok x => out x
  | .error (.domainError _) => "domain"
  | .error (.boundsError) => "bounds"
  | .error (.methodError _) => "method"
  | .error _ => "error"

def emit (i : Nat) (op v : String) : IO Unit := IO.println s!"{i} {op} {v}"

def run (release : Bool) (start count : Nat) : IO Unit := do
  let ws := words
  for j in [start:min ws.size (start + count)] do
    let i := j + 1
    let x := F64.ofBits ws[j]!
    emit i "sinpi" (outJl (if release then sinpiRelease x else sinpi x))
    emit i "cospi" (outJl (if release then cospiRelease x else cospi x))
    match (if release then sincospiRelease x else sincospi x) with
    | .ok p => do emit i "sincospi_s" (out p.1); emit i "sincospi_c" (out p.2)
    | .error e => do emit i "sincospi_s" (outJl (.error e)); emit i "sincospi_c" (outJl (.error e))
    emit i "tanpi" (outJl (if release then tanpiRelease x else tanpi x))
    emit i "sinpi_kernel" (out (if release then sinpiKernelRelease x else sinpiKernel x))
    emit i "cospi_kernel" (out (if release then cospiKernelRelease x else cospiKernel x))
    emit i "cbrt" (out (cbrt x))
  if start == 0 then
    let xs := ints
    for j in [0:xs.size] do
      let n := xs[j]!
      emit (j + 1) "isinpi" (out (sinpiInt n))
      emit (j + 1) "icospi" (out (cospiInt n))
      emit (j + 1) "itanpi" (out (tanpiInt n))

end JuliaLean.MathFuncs.CheckTrig

def main (args : List String) : IO Unit :=
  JuliaLean.MathFuncs.CheckTrig.run (args[0]? == some "release")
    ((args[1]?.bind String.toNat?).getD 0) ((args[2]?.bind String.toNat?).getD 1000000)
