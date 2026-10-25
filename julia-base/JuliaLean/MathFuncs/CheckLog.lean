import JuliaLean.MathFuncs.Log

/-!
Differential corpus for `JuliaLean.MathFuncs.Log`. Prints `<index> <op> <result>` lines,
matched by `repro/mathfuncs-differential-log.jl`. Optional arguments `start count` select
a slice of the combined corpus.
-/

namespace JuliaLean.MathFuncs.CheckLog

open JuliaLean.Float JuliaLean.MathFuncs

def lcgNext (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

def gen (n : Nat) (f : Nat → Nat) (s : Nat) : List Nat × Nat :=
  let (acc, s) := (List.range n).foldl (fun (acc, s) _ =>
    let s' := lcgNext s
    (f s' :: acc, s')) ([], s)
  (acc.reverse, s)

def edges : List Nat :=
  [0, 0x8000000000000000, 1, 0x000fffffffffffff, 0x8000000000000001, 0x800fffffffffffff,
   0x0010000000000000, 0x8010000000000000, 0x7fefffffffffffff, 0xffefffffffffffff,
   0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000, 0xfff8000000000000,
   0x7ff0000000000001, 0x3ff0000000000000, 0xbff0000000000000, 0x4000000000000000,
   0x3fe0000000000000, 0x4024000000000000, 0x3fb999999999999a, 0x4059000000000000,
   0x408f400000000000, 0x4005bf0a8b145769, 0x3ff0000000000001, 0x3fefffffffffffff,
   0x0008000000000000, 0x0000000000000002, 0x3ca0000000000000, 0xbca0000000000000,
   0x3cb0000000000000, 0xbc90000000000000, 0x0010000000000001, 0x7fe0000000000000,
   0x4330000000000000, 0x4340000000000000, 0x43e0000000000000, 0xc000000000000000]

def thresholds : List Nat :=
  [0x3fee0fabfbc702a3, 0x3ff1082b577d34ee, 0x3ca0000000000000, 0xbca0000000000000,
   0xbfaf0540438fd5c4, 0x3fb082b577d34ed8, 0xbff0000000000000, 0x3ff0000000000000]

def cells : List Nat := (List.range 128).map fun j => 0x3ff0000000000000 + (2 * j + 1) * 2^44

def around (b : Int) : List Nat := [(b - 1).toNat, b.toNat, (b + 1).toNat]

def mainCorpus : List Nat :=
  let thr := thresholds.flatMap fun t => (List.range 7).map fun d => t + d - 3
  let tab := ([0, -1, 7, -1000, 1000] : List Int).flatMap fun e =>
    cells.flatMap fun (c : Nat) => around ((c : Int) + e * 2^52)
  let sub := (List.range 128).flatMap fun j => around (((2 * j + 1) * 2^34 : Nat) : Int)
  let l1p := ([-2, -1, 0, 1, 2] : List Int).flatMap fun e =>
    cells.flatMap fun (c : Nat) =>
      around (F64.toBits (F64.sub (F64.ofBits ((c : Int) + e * 2^52).toNat) F64.one))
  let negOne := (List.range 30).map (fun k => 0xbff0000000000000 - (k + 1)) ++
    (List.range 30).map (fun k => 0xbfefffffffffffff - k * 2^40) ++
    (List.range 5).map (fun k => 0xbff0000000000000 + (k + 1))
  let s := 0x2545f4914f6cdd1d
  let (r1, s) := gen 1500 (fun s => s % 0x7ff0000000000000) s
  let (r2, s) := gen 500 (fun s => s % 2^52) s
  let (r3, s) := gen 1000
    (fun s => 0x3feccccccccccccd + s % (0x3ff199999999999a - 0x3feccccccccccccd)) s
  let (r4, s) := gen 1000 (fun s => s / 2^63 * 2^63 + s % 2^63 % 0x3ff0000000000001) s
  let (r5, s) := gen 500
    (fun s => s / 2^63 * 2^63 + 0x3fa999999999999a + s % (0x3fb1eb851eb851ec - 0x3fa999999999999a)) s
  let (r6, _) := gen 300 id s
  edges ++ thr ++ tab ++ sub ++ l1p ++ negOne ++ r1 ++ r2 ++ r3 ++ r4 ++ r5 ++ r6

/-- `reinterpret(UInt64, x*0x1p52) & ~sign_mask - (52 << 52)` for a subnormal `x`. -/
def denormAdjust (xb : Nat) : Nat :=
  (F64.toBits (F64.mul (F64.ofBits xb) (F64.ofBits 0x4330000000000000)) % 2^63 + 2^64 - 52 * 2^52)
    % 2^64

def extCorpus : List Nat :=
  let ed := [0x3ff0000000000000, 0x0010000000000000, 0x7fefffffffffffff, 0x4000000000000000,
    0x3fe0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff, 0x4008000000000000]
  let edSub := [1, 0x000fffffffffffff, 0x0008000000000000, 2, 3].map denormAdjust
  let tab := ([-1021, -1000, -1, 0, 1, 500, 1023] : List Int).flatMap fun e =>
    (List.range 128).flatMap fun (j : Nat) => around (0x3fe6955500000000 + (j : Int) * 2^45 + e * 2^52)
  let s := 0x9e3779b97f4a7c15
  let (r1, s) := gen 1500 (fun s => 0x0010000000000000 + s % (0x7ff0000000000000 - 0x0010000000000000)) s
  let (r2, s) := gen 1000 (fun s => denormAdjust (1 + s % (2^52 - 1))) s
  let (r3, _) := gen 500 (fun s => 0x3fe0000000000000 + s % 2^53) s
  ed ++ edSub ++ tab ++ r1 ++ r2 ++ r3

def fmt (x : F64) : String := if F64.isnan x then "nan" else toString (F64.toBits x)

def fmtJ : Jl F64 → String
  | .ok x => fmt x
  | .error (.domainError _) => "domain"
  | .error .boundsError => "bounds"
  | .error _ => "method"

def lines (i : Nat) : Sum Nat Nat → List String
  | .inl b =>
    let x := F64.ofBits b
    [s!"{i} in {b}", s!"{i} log {fmtJ (log x)}", s!"{i} log2 {fmtJ (log2 x)}",
     s!"{i} log10 {fmtJ (log10 x)}", s!"{i} log1p {fmtJ (log1p x)}"]
  | .inr b =>
    let (h, l) := logExt b
    [s!"{i} in {b}", s!"{i} logext_hi {fmt h}", s!"{i} logext_lo {fmt l}"]

def corpus : List (Sum Nat Nat) := mainCorpus.map .inl ++ extCorpus.map .inr

end JuliaLean.MathFuncs.CheckLog

open JuliaLean.MathFuncs.CheckLog in
def main (args : List String) : IO Unit := do
  let c := corpus
  let (start, count) := match args with
    | [a, b] => (a.toNat!, b.toNat!)
    | _ => (0, c.length)
  for (v, i) in ((c.zip (List.range c.length)).drop start).take count do
    for l in lines i v do
      IO.println l
