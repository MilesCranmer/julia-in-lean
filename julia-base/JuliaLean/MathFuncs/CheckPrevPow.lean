import JuliaLean.MathFuncs.PrevPow

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs

private def step (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

def main (_ : List String) : IO Unit := do
  let bases : List Nat := [0x40000000, 0x40200000, 0x40400000, 0x41200000, 0x3fc00000, 0x3f800001, 0x40490fdb, 0x3f800000]
  let mut s := 0x243f6a8885a308d3
  let mut i := 0
  for a in bases do
    for _ in [0:120] do
      i := i + 1
      s := step s
      let e := s % 140
      s := step s
      let x := F64.ofBits ((e + 1023) * 2^52 + s % 2^52)
      let r := prevpow32 (BitVec.ofNat 32 a) x
      let o := match r with
        | .ok v => toString v.toNat
        | .error (.domainError _) => "domain"
        | .error (.inexactError _) => "inexact"
        | .error _ => "error"
      IO.println s!"{i} {o}"
