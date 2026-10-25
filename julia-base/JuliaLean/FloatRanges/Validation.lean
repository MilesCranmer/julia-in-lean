import JuliaLean.FloatRanges.StepRangeLen
import JuliaLean.FloatRanges.LinRange

/-!
Deterministic differential corpus for the float-range model. The Julia oracle
`repro/floatranges-differential.jl` draws the same cases from the same tables with the
same 64-bit LCG and prints the same lines: internal fields of every constructed range
(`ref`, `step`, `len`, `offset`), elements, `step`, `in`, `reverse`, `-r` and scalar
broadcasts. Floats print as decimal UInt64 bit patterns; NaNs print as `nan`.
-/

namespace JuliaLean.FloatRanges.Validation

open JuliaLean.Float JuliaLean.FloatRanges

/-- Endpoint table (bit patterns). -/
def values : Array Nat := #[
  0x0000000000000000,0x8000000000000000,0x3ff0000000000000,0xbff0000000000000,0x3fb999999999999a,
  0xbfb999999999999a,0x3fc999999999999a,0x3fd3333333333333,0x3fe0000000000000,0x3ff8000000000000,
  0x4000000000000000,0x4008000000000000,0x4024000000000000,0x3fe6666666666666,0x3ff199999999999a,
  0x4061866666666666,0xbff028f5c28f5c29,0x3fd5555555555555,0x400921fb54442d18,0x3d06849b86a12b9b,
  0x01a56e1fc2f8f359,0x0000000000000001,0x8000000000000001,0x4340000000000000,0x4340000000000001,
  0x430c6bf526340000,0x4170000000000000,0x4170000010000000,0x42a2309ce5400000,0x7fefffffffffffff,
  0xffefffffffffffff,0x3ff0000000000001,0x3fefffffffffffff,0x7ff0000000000000,0xfff0000000000000,
  0x7ff8000000000000,0x3fb8c7e28240b780,0x3faf06f694467382,0x402fae147ae147ae,0xbf9bda5119ce075f,
  0x43e02207973f6440,0x43dfeb3dd0676600,0x7fe1ccf385ebc8a0,0xffe1ccf385ebc8a0,0x4089f4cccccccccd,
  0x4089f4ccccccccd7,0xc083580000000000,0x4065c00000000000,0x3fbcf41f212d7732,0x3ee4f8b588e368f1,
  0x401c000000000000,0xc00c000000000000,0x4059000000000000,0x416312d000000000,0x3e8ad7f29abcaf48,
  0x3fd0000000000000]

/-- Step table (bit patterns). -/
def steps : Array Nat := #[
  0x3fb999999999999a,0xbfb999999999999a,0x3fd3333333333333,0x3ff0000000000000,0xbff0000000000000,
  0x3fe0000000000000,0x3fd5555555555555,0x400921fb54442d18,0x3f9bda5119ce075f,0xbf9bda5119ce075f,
  0x404a266666666666,0x01a56e1fc2f8f359,0x4000000000000000,0x46293e5939a08cea,0x7ff0000000000000,
  0xfff0000000000000,0x7ff8000000000000,0x0000000000000000,0x7fefffffffffffff,0x3f86872b020c49ba,
  0x3f99ce075f6fd220,0x401c000000000000,0xc0440ccccccccccd,0x42a2309ce5400000,0x3fa8e965e6eef808,
  0xbfd0000000000000,0x3f50624dd2f1a9fc,0x3e45798ee2308c3a,0x4008000000000000,0xbfe6666666666666,
  0x3efa36e2eb1c432d,0x7e37e43c8800759c]

/-- Length table. -/
def lengths : Array Int := #[0, 1, 2, 3, 4, 5, 6, 10, 24, 100, 1476, 4096, 1000000,
  10000000000000000, 4611686018427387904, 9223372036854775807, -1, 7, 11, 1490]

/-- One differential case. -/
inductive Case where
  | colon (a s b : F64)
  | rangeLen (a b : F64) (n : I64)
  | startStep (a s : F64) (n : I64)
  | stopStep (s b : F64) (n : I64)
  | lin (a b : F64) (n : I64)
  | bcast (a s b x : F64)
  | rat (x : F64)

private def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

/-- The corpus: 1200 colon, 800 length, 500 start-step, 300 stop-step, 600 LinRange,
300 broadcast cases, then `rat` of every table value. -/
def cases : Array Case := Id.run do
  let mut st := 0x243f6a8885a308d3
  let mut out : Array Case := #[]
  let counts := #[1200, 800, 500, 300, 600, 300]
  for kind in [0:6] do
    for _ in [0:counts[kind]!] do
      let mut picks : Array Nat := #[]
      for _ in [0:4] do
        st := lcg st
        picks := picks.push (st >>> 33)
      let v (k : Nat) : F64 := F64.ofBits (values[picks[k]! % values.size]!)
      let s (k : Nat) : F64 := F64.ofBits (steps[picks[k]! % steps.size]!)
      let n (k : Nat) : I64 := i64 (lengths[picks[k]! % lengths.size]!)
      out := out.push <| match kind with
        | 0 => .colon (v 0) (s 1) (v 2)
        | 1 => .rangeLen (v 0) (v 1) (n 2)
        | 2 => .startStep (v 0) (s 1) (n 2)
        | 3 => .stopStep (s 0) (v 1) (n 2)
        | 4 => .lin (v 0) (v 1) (n 2)
        | _ => .bcast (v 0) (s 1) (v 2) (v 3)
  for w in values ++ steps do out := out.push (.rat (F64.ofBits w))
  return out

def outF (x : F64) : String := if F64.isnan x then "nan" else toString (F64.toBits x)
def outB (b : Bool) : String := if b then "true" else "false"
def outErr : JlError → String
  | .argumentError _ => "E:argument"
  | .inexactError _ => "E:inexact"
  | .divideError => "E:divide"
  | .boundsError => "E:bounds"
  | .overflowError _ => "E:overflow"
  | .domainError _ => "E:domain"
  | .methodError _ => "E:method"
def outJ {α} (f : α → String) : Jl α → String
  | .ok a => f a
  | .error e => outErr e

def fieldsS (r : SRL) : String :=
  s!"{r.len.val} {r.offset.val} {outF r.ref.hi} {outF r.ref.lo} {outF r.step.hi} {outF r.step.lo}"

def descS (r : SRL) : String :=
  let mid := i64 (max 1 (r.len.val / 2))
  let xm := r.unsafeGet mid
  let ins := [r.first, r.last, xm, F64.nextfloat xm].map (fun x => outJ outB (r.contains x))
  s!"{fieldsS r} | {outF r.first} {outF r.last} {outJ outF (r.get (i64 2))} {outJ outF (r.get mid)} {outF r.stepF} | {" ".intercalate ins} | rev {outJ (fun q => s!"{fieldsS q} {outJ outF (q.get (i64 2))}") r.reverse} | neg {outJ fieldsS r.neg}"

def fieldsL (r : Lin) : String :=
  s!"{outF r.start} {outF r.stop} {r.len.val} {r.lendiv.val}"

def descL (r : Lin) : String :=
  let mid := i64 (max 1 (r.len.val / 2))
  let xm := r.unsafeGet mid
  let ins := [r.unsafeGet (i64 2), xm, F64.nextfloat xm].map (fun x => outJ outB (r.contains x))
  s!"{fieldsL r} | {outJ outF (r.get (i64 1))} {outJ outF (r.get (i64 2))} {outJ outF (r.get mid)} {outJ outF (r.get r.len)} {outF r.stepF} | {" ".intercalate ins} | rev {outJ (fun q => outJ outF (q.get (i64 2))) r.reverse} | neg {outJ (fun q => outJ outF (q.get (i64 2))) r.neg} | add {outJ (fun q => outJ outF (q.get (i64 2))) (r.addScalar (F64.ofBits 0x3fb999999999999a))} | mul {outJ (fun q => outJ outF (q.get (i64 2))) (r.bcastMul (F64.ofBits 0x4008000000000000))}"

def descSmall (r : SRL) : String :=
  s!"{fieldsS r} {outF r.first} {outF r.last} {outJ outF (r.get (i64 2))}"

def run : Case → String
  | .colon a s b => s!"colon {outJ descS (colon a s b)}"
  | .rangeLen a b n => s!"rangelen {outJ descS (rangeStartStopLength a b n)}"
  | .startStep a s n => s!"startstep {outJ descS (rangeStartStepLength a s n)}"
  | .stopStep s b n => s!"stopstep {outJ descS (rangeStepStopLength s b n)}"
  | .lin a b n => s!"lin {outJ descL (Lin.mk' a b n)}"
  | .bcast a s b x => s!"bcast {outJ (fun r => s!"{outJ descSmall (r.addScalar x)} / {outJ descSmall (r.bcastMul x)} / {outJ descSmall (SRL.scalarMul x r)}") (colon a s b)}"
  | .rat x => s!"rat {outJ (fun (p : I64 × I64) => s!"{p.1.val} {p.2.val}") (FloatRanges.rat x)}"

/-- Print cases `start, ..., start+count-1`. -/
def differential (start count : Nat) : IO Unit := do
  let cs := cases
  for i in [start:min cs.size (start + count)] do
    if let some c := cs[i]? then IO.println s!"{i} {run c}"

end JuliaLean.FloatRanges.Validation
