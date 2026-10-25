import JuliaLean.MathFuncs.Basic

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs

private def edges : List Nat := [
  0, 1, 2, 0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001, 0x1CC0000000000000,
  0x2000000000000000, 0x1fffffffffffffff, 0x3E46A09E667F3BCD, 0x3fe0000000000000,
  0x3ff0000000000000, 0x3ff0000000000001, 0x4000000000000000, 0x4008000000000000,
  0x4010000000000000, 0x5FE6A09E667F3BCC, 0x5FE6A09E667F3BCD, 0x7fefffffffffffff,
  0x7ff0000000000000, 0x7ff8000000000000, 0x7ff0000000000001, 0x4066800000000000,
  0x400921FB54442D18]

private def allEdges : List Nat := edges ++ edges.map (· + 2^63)

private def step (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2^64

private def out (x : F64) : String := if F64.isnan x then "nan" else toString (F64.toBits x)
private def outJl {α} (f : α → String) : Jl α → String
  | .ok v => f v
  | .error (.domainError _) => "domain"
  | .error _ => "error"

private def withExp (w e : Nat) : Nat := w / 2^63 * 2^63 + e * 2^52 + w % 2^52

def main (_ : List String) : IO Unit := do
  let mut i := 0
  for a in allEdges do
    for b in allEdges do
      i := i + 1
      let x := F64.ofBits a
      let y := F64.ofBits b
      IO.println s!"{i} min {out (fmin x y)}"
      IO.println s!"{i} max {out (fmax x y)}"
      IO.println s!"{i} hypot {out (hypot x y)}"
      IO.println s!"{i} hypot3 {out (hypotN [x, y, F64.ofBits allEdges[i % allEdges.length]!])}"
      IO.println s!"{i} clamp {out (clamp x y (F64.ofBits allEdges[(7*i) % allEdges.length]!))}"
  let mut s := 0x243f6a8885a308d3
  for k in [0:6000] do
    i := i + 1
    s := step s
    let w1 := s
    s := step s
    let w2 := s
    s := step s
    let w3 := s
    let e1 := (w3 >>> 3) % 2047
    let d := (w3 >>> 20) % 40
    let e2 := if e1 > d then e1 - d else 0
    let e3 := if e1 > 2*d then e1 - 2*d else 0
    let x := F64.ofBits (if k % 5 == 0 then w1 else withExp w1 e1)
    let y := F64.ofBits (if k % 5 == 0 then w2 else withExp w2 e2)
    let z := F64.ofBits (withExp w3 e3)
    IO.println s!"{i} hypot {out (hypot x y)}"
    IO.println s!"{i} hypot3 {out (hypotN [x, y, z])}"
    IO.println s!"{i} deg2rad {out (deg2rad x)}"
    IO.println s!"{i} rad2deg {out (rad2deg x)}"
    IO.println s!"{i} fourthroot {outJl out (fourthroot x)}"
    IO.println s!"{i} min {out (fmin x y)}"
    IO.println s!"{i} max {out (fmax x y)}"
    let sh := (w3 >>> 40) % 64
    let n0 : Int := (Int.ofNat (w1 % 2^64)) - 2^63
    let d0 : Int := Int.ofNat ((w2 >>> sh) % 2^63) + 1
    let num : Int := if k % 7 == 0 then 2^60 - (Int.ofNat (w1 % 1000)) else n0 / 2^(w3 % 64)
    let den : Int := if k % 7 == 0 then 2^60 else d0
    if num != 0 then
      let g : Int := Int.ofNat (Nat.gcd num.natAbs den.natAbs)
      IO.println s!"{i} exponentrat {outJl toString (exponentRat (JInt.wrap .i64 (num / g)) (JInt.wrap .i64 (den / g)))}"
  for a in [0, 1, 2, 127, 128, 255, 2^63 - 1, 2^63, 2^64 - 1, 2^64 - 128] do
    for b in [0, 1, 2^63, 2^64 - 1, 2^64 - 128] do
      i := i + 1
      let x : JInt .i64 := JInt.wrap .i64 a
      let y : JInt .i64 := JInt.wrap .i64 b
      let x8 : JInt .i8 := JInt.wrap .i8 a
      let y8 : JInt .i8 := JInt.wrap .i8 b
      IO.println s!"{i} copysign64 {(copysignInt x y).val}"
      IO.println s!"{i} flipsign64 {(flipsignInt x y).val}"
      IO.println s!"{i} copysign8 {(copysignInt x8 y8).val}"
      IO.println s!"{i} flipsign8 {(flipsignInt x8 y8).val}"
  IO.println s!"COUNT {i}"
