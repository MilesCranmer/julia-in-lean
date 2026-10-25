import JuliaLean.Complex.IntModel

/-!
Deterministic differential corpus for the complex model. The Julia oracle builds
the same bit words, pairings and exponents, and prints results as decimal UInt64
bit patterns with NaNs normalized.
-/

namespace JuliaLean.Complex.Validation

open JuliaLean JuliaLean.Float

private def edge : Array Nat := #[
  0, 0x8000000000000000, 0x3ff0000000000000, 0xbff0000000000000, 0x4000000000000000,
  0x4008000000000000, 0x4048800000000000, 0x3fe0000000000000, 0x7fefffffffffffff,
  0xffefffffffffffff, 0x0010000000000000, 0x0000000000000001, 0x0000000000000003,
  0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0x7e37e43c8800759c,
  0x01a56e1fc2f8f359, 0x3ddb7cdfd9d7bdbb, 0x7e70000000000000, 0x0170000000000000,
  0x5fe0000000000000, 0x2000000000000000, 0x41d0000000000000, 0xc1d0000000000000,
  0x41b0c5ad00000000, 0x7fe0000000000000, 0x0020000000000000, 0x4330000000000000,
  0x3cb0000000000000]

/-- Complex corpus: every pair of the first 16 edge words, then 256 seeded pairs. -/
def complexes : Array CF64 := Id.run do
  let mut zs : Array CF64 := #[]
  for i in [:16] do
    for j in [:16] do
      zs := zs.push ⟨F64.ofBits edge[i]!, F64.ofBits edge[j]!⟩
  let mut state := 0x243f6a8885a308d3
  let next := fun (s : Nat) => (s * 6364136223846793005 + 1442695040888963407) % 2^64
  for _ in [:256] do
    state := next state
    let a := if state % 4 == 0 then edge[(state / 4) % edge.size]! else state
    state := next state
    let b := if state % 4 == 0 then edge[(state / 4) % edge.size]! else state
    zs := zs.push ⟨F64.ofBits a, F64.ofBits b⟩
  return zs

private def out (x : F64) : String := if F64.isnan x then "nan" else toString (F64.toBits x)
private def outC (z : CF64) : String := s!"{out z.re},{out z.im}"
private def outJl {α : Type} (f : α → String) : Jl α → String
  | .ok x => f x
  | .error (.domainError _) => "domain"
  | .error e => s!"unexpected:{repr e}"
private def outI {t : IntTy} (z : CInt t) : String := s!"{z.re.val},{z.im.val}"

private def exps : Array Int := #[-3, -2, -1, 0, 1, 2, 3, 5, 7, 10, -9223372036854775808]

private def ints : Array Int := #[0, 1, -1, 2, 3, -5, 7, 1000003, -9223372036854775808,
  9223372036854775807, 4611686018427387904, -4611686018427387905, 1234567890123]

/-- Print every modelled operation on the corpus. -/
def differential : IO Unit := do
  let zs := complexes
  let n := zs.size
  for i in [:n] do
    let z := zs[i]!
    let w := zs[(7 * i + 3) % n]!
    let x := zs[(13 * i + 5) % n]!
    IO.println s!"{i} mul {outC (CF64.mul z w)}"
    IO.println s!"{i} div {outC (CF64.div z w)}"
    IO.println s!"{i} divreal {outC (CF64.divReal z w.re)}"
    IO.println s!"{i} muladd {outC (CF64.muladd z w x)}"
    IO.println s!"{i} inv {outJl outC (CF64.inv z)}"
    IO.println s!"{i} abs {outJl out (CF64.abs z)}"
    IO.println s!"{i} abs2 {out (CF64.abs2 z)}"
    IO.println s!"{i} sqrt {outJl outC (CF64.sqrt z)}"
    IO.println s!"{i} pow {outJl outC (CF64.powInt z (JInt.wrap .i64 exps[i % exps.size]!))}"
  for i in [:ints.size] do
    for j in [:ints.size] do
      for k in [:ints.size] do
        let l := (i + 2 * j + 3 * k) % ints.size
        let a : CInt .i64 := ⟨JInt.wrap .i64 ints[i]!, JInt.wrap .i64 ints[j]!⟩
        let b : CInt .i64 := ⟨JInt.wrap .i64 ints[k]!, JInt.wrap .i64 ints[l]!⟩
        IO.println s!"{i}-{j}-{k} idiv {outC (CInt.div a b)}"
        IO.println s!"{i}-{j}-{k} imul {outI (CInt.mul a b)}"
        IO.println s!"{i}-{j}-{k} ipow {outJl outI (CInt.powInt a (JInt.wrap .i64 exps[k % exps.size]!))}"
  IO.println s!"COUNT {n}"

end JuliaLean.Complex.Validation
