import JuliaLean.RandomSampling.Model

/-!
Differential corpus for the sampling model. The Julia reference builds
the same splitmix64 word stream as a custom `AbstractRNG` and prints the same lines.
Each request (`rand(rng, UInt32)`, `UInt64`, `UInt128`, `UInt52Raw()`) consumes one
word `w`; `UInt32` answers `w % UInt32` and `UInt128` answers `(UInt128(w) << 64) | w`.
-/

namespace JuliaLean.RandomSampling.Validation

open JuliaLean JuliaLean.Float

/-- splitmix64 output for counter `n`. -/
def splitmix (n : Nat) : Nat :=
  let m := 2 ^ 64
  let z := (n + 1) * 0x9e3779b97f4a7c15 % m
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9 % m
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb % m
  z ^^^ (z >>> 31)

/-- The oracle RNG; its state is the number of words consumed. -/
def smRng : Rng Nat where
  next st q := match q with
    | .int u =>
      let w := splitmix st
      ((JInt.wrap u (if u = .u128 then w * 2 ^ 64 + w else w) : JInt u), st + 1)
    | .raw52 => ((JInt.wrap .u64 (splitmix st) : JInt .u64), st + 1)

/-- Words that force `randexp`'s slow paths: even counters set bits 8-51 (and, for
`idx0`, clear bits 0-7, so the table index is 0); odd counters are plain splitmix. -/
def altWord (idx0 : Bool) (st : Nat) : Nat :=
  let w := splitmix st
  if st % 2 = 1 then w
  else
    let w := w ||| 0x000fffffffffff00
    if idx0 then w &&& 0xffffffffffffff00 else w

def altRng (idx0 : Bool) : Rng Nat where
  next st q := match q with
    | .int u => ((JInt.wrap u (altWord idx0 st) : JInt u), st + 1)
    | .raw52 => ((JInt.wrap .u64 (altWord idx0 st) : JInt .u64), st + 1)

private def fuel : Nat := 64

private def runStr {α : Type} (f : α → String) : Run Nat α → String
  | none => "fuel"
  | some (.error e) => s!"error {repr e}"
  | some (.ok (v, st)) => s!"{f v} @{st}"

/-- `n` successive draws with one sampler, printed with the final state. -/
private def drawsNDL {t : IntTy} (a b : Int) (n : Nat) : String :=
  match ndlSampler (JInt.wrap t a) (JInt.wrap t b) with
  | .error _ => " error"
  | .ok sp => Id.run do
    let mut st := 0
    let mut out := ""
    for _ in [:n] do
      match ndlRand smRng sp fuel st with
      | some (.ok (v, st')) => out := out ++ s!" {v.val}"; st := st'
      | _ => return out ++ " fail"
    return out ++ s!" @{st}"

private def drawsFast {t : IntTy} (a b : Int) (n : Nat) : String :=
  match fastSampler (JInt.wrap t a) (JInt.wrap t b) with
  | .error _ => " error"
  | .ok sp => Id.run do
    let mut st := 0
    let mut out := ""
    for _ in [:n] do
      match fastRand smRng sp fuel st with
      | some (.ok (v, st')) => out := out ++ s!" {v.val}"; st := st'
      | _ => return out ++ " fail"
    return out ++ s!" @{st}"

private def ranges : List (IntTy × Int × Int) :=
  let ts := [IntTy.i8, .u8, .i16, .u16, .i32, .u32, .i64, .u64]
  ts.flatMap fun t => [
    (t, 1, 6), (t, t.min, t.max), (t, t.min, t.max - 1), (t, 0, 2 ^ (t.bits - 1)),
    (t, t.min + 3, t.min + 3), (t, t.max - 100, t.max), (t, 0, 2 ^ (t.bits - 2) * 3)]

private def ranges128 : List (IntTy × Int × Int) :=
  [.i128, .u128].flatMap fun t => [
    (t, 1, 6), (t, t.min, t.max), (t, 0, 2 ^ 64 - 1), (t, 0, 2 ^ 64), (t, 5, 2 ^ 100 + 7),
    (t, t.max - 2 ^ 70, t.max), (t, 0, 2 ^ 126 * 3 - 1)]

private def arr (n : Nat) (a : Nat → Int) : String :=
  " ".intercalate ((List.range n).map fun k => toString (a (k + 1)))

/-- Print every modelled operation on the corpus. -/
def differential : IO Unit := do
  for (t, a, b) in ranges do
    IO.println s!"range {t.name} {a} {b}:{@drawsNDL t a b 6}"
  for (t, a, b) in ranges128 do
    IO.println s!"range {t.name} {a} {b}:{@drawsFast t a b 6}"
  for n in [:9] do
    for s0 in [0, 7, 100] do
      IO.println s!"randperm {n} {s0}: {runStr (arr n) (randperm smRng fuel n s0)}"
      IO.println s!"randcycle {n} {s0}: {runStr (arr n) (randcycle smRng fuel n s0)}"
      IO.println s!"shuffle {n} {s0}: {runStr (arr n) (shuffle smRng fuel n (fun k => 10 * k) s0)}"
  for s0 in [:40] do
    IO.println s!"randexp {s0}: {runStr (fun x => toString (F64.toBits x)) (randexp smRng fuel s0)}"
    IO.println s!"float {s0}: {F64.toBits (randFloat64 smRng s0).1}"
    IO.println s!"char {s0}: {runStr toString (randCharCode smRng fuel s0)}"
  let ps : List Nat := [0x3fb999999999999a, 0x3fa999999999999a, 0x3fd3333333333333,
    0x3f50624dd2f1a9fc, 0x3fc3333333333333]
  for p in ps do
    for s0 in [0, 1, 2] do
      IO.println s!"randsubseq {p} {s0}: {runStr toString
        (randsubseq smRng fuel ((List.range 50).map fun k => ((k + 1 : Nat) : Int)) (F64.ofBits p) s0)}"
  for s0 in [0, 3] do
    IO.println s!"randstring {s0}: {runStr (fun bs => toString (bs.map UInt8.toNat))
      (randstringBytes smRng fuel [0x61, 0x62, 0xc3] 7 s0)}"
  for s0 in [:60] do
    let s0 := 2 * s0
    IO.println s!"randexp-slow {s0}: {runStr (fun x => toString (F64.toBits x)) (randexp (altRng false) 2000 s0)}"
    IO.println s!"randexp-idx0 {s0}: {runStr (fun x => toString (F64.toBits x)) (randexp (altRng true) 2000 s0)}"

end JuliaLean.RandomSampling.Validation
