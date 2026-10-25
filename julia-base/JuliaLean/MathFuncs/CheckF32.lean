import JuliaLean.MathFuncs.PropsSpecial

open JuliaLean JuliaLean.Float JuliaLean.MathFuncs

private def step (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

def main (_ : List String) : IO Unit := do
  let edges : List Nat := [0, 1, 2, 0x7fffff, 0x800000, 0x3f800000, 0x40c90fdb, 0x40c90fda,
    0x7f7fffff, 0x7f800000, 0x7fc00000, 0x7f800001, 0x33d6bf95, 0x34000000]
  let mut ws : List Nat := edges ++ edges.map (· + 2^31)
  let mut s := 0x243f6a8885a308d3
  for _ in [0:4000] do
    s := step s
    ws := ws ++ [s / 2^32]
  let mut i := 0
  for w in ws do
    i := i + 1
    let x : F32 := BitVec.ofNat 32 w
    let d := ofF32 x
    IO.println s!"{i} f64 {if F64.isnan d then "nan" else toString (F64.toBits d)}"
    IO.println s!"{i} mod2pi32 {if F32.isfinite x then toString (mod2pi32 x).toNat else "skip"}"
    s := step s
    let y := F64.ofBits s
    let r := toF32 y
    IO.println s!"{i} f32 {if F64.isnan y then "nan" else toString r.toNat}"
