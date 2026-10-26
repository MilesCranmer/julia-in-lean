import JuliaLean.MiscCov.Basic

/-!
# `base/parsers/Parsers.jl` and `base/parsers/ints.jl`

The byte helpers use natural numbers reduced modulo `2^64`, matching `UInt64`.
The integer parser records the observable value/failure result. Its `Bool` case
keeps the generic method's `T(base)` conversion, which is the source of the
documented counterexample.
-/

namespace JuliaLean.MiscCov.Parsers

open JuliaLean.MiscCov

inductive Failure where
  | invalid | overflow | underflow
  deriving DecidableEq, Repr

inductive Result where
  | failure (f : Failure)
  | value (n : Int)
  deriving DecidableEq, Repr

/-- `Base.show(io, x::ParseFailure)`, `base/parsers/Parsers.jl:52-53`. -/
def showFailure : Failure → String
  | .invalid => "Base.Parsers.INVALID"
  | .overflow => "Base.Parsers.OVERFLOW"
  | .underflow => "Base.Parsers.UNDERFLOW"

private def byte (buf : List Nat) (i : Nat) : Nat := (buf[i]?).getD 0
private def u64 (x : Nat) : Nat := x % 2^64
private def add64 (x y : Nat) : Nat := u64 (x + y)
private def sub64 (x y : Nat) : Nat := u64 (x + 2^64 - y % 2^64)
private def mul64 (x y : Nat) : Nat := u64 (x * y)

/-- The little-endian word read by all three `load8` methods. -/
def load8Word (buf : List Nat) (i : Nat) : Nat :=
  u64 ((List.range 8).foldl (fun w k => w + byte buf (i + k) * 256^k) 0)

/-- Stable-pointer `unsafe_load` overload, `base/parsers/ints.jl:10-13`. -/
def load8Stable (buf : List Nat) (i : Nat) : Nat := load8Word buf i

/-- Dense UTF-8 `CodeUnits` overload, `base/parsers/ints.jl:14-15`. -/
def load8CodeUnits (buf : List Nat) (i : Nat) : Nat := load8Word buf i

/-- Generic `AbstractVector` loop, `base/parsers/ints.jl:16-22`. -/
def load8Generic (buf : List Nat) (i : Nat) : Nat :=
  (List.range 8).reverse.foldl (fun w k => u64 (w * 256 ||| byte buf (i + k))) 0

/-- `isdigits8`, `base/parsers/ints.jl:26-28`. -/
def isdigits8 (w : Nat) : Bool :=
  let mask := 0xf0f0f0f0f0f0f0f0
  ((w &&& mask) ||| ((add64 w 0x0606060606060606 &&& mask) >>> 4)) == 0x3333333333333333

/-- `digits8`, `base/parsers/ints.jl:33-38`. -/
def digits8 (w0 : Nat) : Nat :=
  let w := sub64 w0 0x3030303030303030
  let w := add64 (mul64 w 10) (w >>> 8)
  (((mul64 (w &&& 0x000000ff000000ff) 0x000f424000000064) +
    mul64 ((w >>> 16) &&& 0x000000ff000000ff) 0x0000271000000001) % 2^64) >>> 32

/-- `bytesin`, `base/parsers/ints.jl:41-43`. -/
def bytesin (w lo hi : Nat) : Nat :=
  (mul64 (0x80 - lo) 0x0101010101010101 |> add64 w) &&&
  (Nat.xor (mul64 (0x7f - hi) 0x0101010101010101 |> add64 w) (2^64 - 1)) &&&
  0x8080808080808080

/-- `ishexdigits8`, `base/parsers/ints.jl:46-49`. -/
def ishexdigits8 (w : Nat) : Bool :=
  (w &&& 0x8080808080808080 == 0) &&
    ((bytesin w 0x30 0x39 ||| bytesin (w ||| 0x2020202020202020) 0x61 0x66) ==
      0x8080808080808080)

/-- `hexdigits8`, `base/parsers/ints.jl:54-59`. -/
def hexdigits8 (w0 : Nat) : Nat :=
  let w := add64 (w0 &&& 0x0f0f0f0f0f0f0f0f) (mul64 ((w0 >>> 6) &&& 0x0101010101010101) 9)
  let w := ((w <<< 4) ||| (w >>> 8)) &&& 0x00ff00ff00ff00ff
  let w := ((w <<< 8) ||| (w >>> 16)) &&& 0x0000ffff0000ffff
  ((w <<< 16) ||| (w >>> 32)) &&& 0x00000000ffffffff

/-- `digitvalue`, `base/parsers/ints.jl:64-69`. -/
def digitvalue (b base : Nat) : Nat :=
  if 0x30 ≤ b && b ≤ 0x39 then b - 0x30
  else if 0x41 ≤ b && b ≤ 0x5a then b - 0x41 + 10
  else if 0x61 ≤ b && b ≤ 0x7a then b - 0x61 + (if base ≤ 36 then 10 else 36)
  else 255

/-- `overflowfailure`, `base/parsers/ints.jl:73-78`. Indices are zero based here. -/
def overflowfailure (buf : List Nat) (i j base : Nat) : Failure :=
  if ((buf.drop i).take (j + 1 - i)).all (fun b => digitvalue b base < base)
  then .overflow else .invalid

private def parseMagnitude (buf : List Nat) (base : Nat) : Option Nat :=
  buf.foldl (fun acc b => acc.bind fun n =>
    let d := digitvalue b base
    if d < base then some (n * base + d) else none) (some 0)

/-- Observable result of the `T<:BitInteger` method, `base/parsers/ints.jl:86-157`.
The decimal, small-type, hexadecimal and other-base branches select the same
digit accumulation with the source method's final representability check. -/
def parseintBit (bits : Nat) (signed neg : Bool) (buf : List Nat) (i j base : Nat) : Result :=
  if j < i then .failure .invalid
  else
    let digits := (buf.drop i).take (j + 1 - i)
    let parsed := if base = 10 then parseMagnitude digits 10
      else if bits < 32 then parseMagnitude digits base
      else if base = 16 then parseMagnitude digits 16
      else parseMagnitude digits base
    match parsed with
    | none => .failure .invalid
    | some n =>
      let limit := if signed then (if neg then 2^(bits - 1) else 2^(bits - 1) - 1) else 2^bits - 1
      if n ≤ limit then .value (if neg then -(n : Int) else n) else .failure .overflow

inductive IntegerKind where
  | bool | arbitrary
  deriving DecidableEq, Repr

private def convertKind : IntegerKind → Nat → M Int
  | .bool, n => if n ≤ 1 then .ok n else .error .inexactError
  | .arbitrary, n => .ok n

/-- Generic `T<:Integer` method, `base/parsers/ints.jl:161-173`, including the
`T(base)` conversion before the loop body. -/
def parseintInteger (kind : IntegerKind) (buf : List Nat) (i j base : Nat) (neg : Bool) : M Result := do
  if j < i then return .failure .invalid
  let b ← convertKind kind base
  let rec loop : List Nat → Int → M Result
    | [], n => pure (.value n)
    | x :: xs, n => do
      let d := digitvalue x base
      if base ≤ d then return .failure .invalid
      let td ← convertKind kind d
      loop xs (n * b + if neg then -td else td)
  loop ((buf.drop i).take (j + 1 - i)) 0

/-- `parsevalue(::Type{T}, bytes; base)`, `base/parsers/ints.jl:175-190` for
the generic integer path. -/
def parsevalue (kind : IntegerKind) (signed : Bool) (bytes : List Nat) (base : Nat) : M Result := do
  if !(2 ≤ base && base ≤ 62) then throw (.argumentError "invalid base")
  let (neg, i) := match bytes with
    | b :: _ => if signed && (b == 0x2d || b == 0x2b) then (b == 0x2d, 1) else (false, 0)
    | [] => (false, 0)
  parseintInteger kind bytes i (bytes.length - 1) base neg

def HelperContract : Prop :=
  (∀ buf i, i + 8 ≤ buf.length →
    load8Stable buf i = load8CodeUnits buf i ∧ load8Stable buf i = load8Word buf i) ∧
  (∀ buf i, load8Generic buf i =
    (List.range 8).reverse.foldl (fun w k => u64 (w * 256 ||| byte buf (i + k))) 0) ∧
  (∀ w, isdigits8 w =
    (((w &&& 0xf0f0f0f0f0f0f0f0) |||
      ((add64 w 0x0606060606060606 &&& 0xf0f0f0f0f0f0f0f0) >>> 4)) == 0x3333333333333333)) ∧
  (∀ w, digits8 w =
    let x := sub64 w 0x3030303030303030
    let x := add64 (mul64 x 10) (x >>> 8)
    (((mul64 (x &&& 0x000000ff000000ff) 0x000f424000000064) +
      mul64 ((x >>> 16) &&& 0x000000ff000000ff) 0x0000271000000001) % 2^64) >>> 32) ∧
  (∀ w lo hi, bytesin w lo hi =
    (mul64 (0x80 - lo) 0x0101010101010101 |> add64 w) &&&
    Nat.xor (mul64 (0x7f - hi) 0x0101010101010101 |> add64 w) (2^64 - 1) &&&
    0x8080808080808080) ∧
  (∀ w, ishexdigits8 w =
    ((w &&& 0x8080808080808080 == 0) &&
      ((bytesin w 0x30 0x39 ||| bytesin (w ||| 0x2020202020202020) 0x61 0x66) ==
        0x8080808080808080))) ∧
  (∀ w, hexdigits8 w =
    let x := add64 (w &&& 0x0f0f0f0f0f0f0f0f) (mul64 ((w >>> 6) &&& 0x0101010101010101) 9)
    let x := ((x <<< 4) ||| (x >>> 8)) &&& 0x00ff00ff00ff00ff
    let x := ((x <<< 8) ||| (x >>> 16)) &&& 0x0000ffff0000ffff
    ((x <<< 16) ||| (x >>> 32)) &&& 0x00000000ffffffff) ∧
  (∀ buf i j base, overflowfailure buf i j base =
    if ((buf.drop i).take (j + 1 - i)).all (fun b => digitvalue b base < base)
    then .overflow else .invalid) ∧
  showFailure .invalid = "Base.Parsers.INVALID" ∧
  showFailure .overflow = "Base.Parsers.OVERFLOW" ∧
  showFailure .underflow = "Base.Parsers.UNDERFLOW" ∧
  digitvalue 0x30 10 = 0 ∧ digitvalue 0x39 10 = 9 ∧
  digitvalue 0x41 16 = 10 ∧ digitvalue 0x61 16 = 10 ∧ digitvalue 0x61 62 = 36

theorem helperContract_proven : HelperContract := by
  unfold HelperContract
  refine ⟨fun buf i _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl,
    rfl, rfl, rfl, ?_⟩
  decide

/-- The docstring promises a value or `ParseFailure`, without throwing, for
every integer type and valid base. -/
def ParsevalueNoThrow : Prop := ∀ bytes base, 2 ≤ base → base ≤ 62 →
  ∃ r, parsevalue .bool false bytes base = .ok r

theorem parsevalueNoThrow_refuted : ¬ ParsevalueNoThrow := by
  intro h
  rcases h [0x31] 10 (by decide) (by decide) with ⟨r, hr⟩
  simp [parsevalue, parseintInteger, convertKind, bind, Except.bind] at hr

def ParseContract : Prop :=
  (∀ bits signed neg buf i j base,
    parseintBit bits signed neg buf i j base =
      if j < i then .failure .invalid else
        let ds := (buf.drop i).take (j + 1 - i)
        let p := if base = 10 then parseMagnitude ds 10
          else if bits < 32 then parseMagnitude ds base
          else if base = 16 then parseMagnitude ds 16 else parseMagnitude ds base
        match p with
        | none => .failure .invalid
        | some n =>
          let lim := if signed then (if neg then 2^(bits - 1) else 2^(bits - 1) - 1) else 2^bits - 1
          if n ≤ lim then .value (if neg then -(n : Int) else n) else .failure .overflow) ∧
  (∀ bytes base, parsevalue .arbitrary true bytes base =
    if !(2 ≤ base && base ≤ 62) then .error (.argumentError "invalid base")
    else
      let (neg, i) := match bytes with
        | b :: _ => if b == 0x2d || b == 0x2b then (b == 0x2d, 1) else (false, 0)
        | [] => (false, 0)
      parseintInteger .arbitrary bytes i (bytes.length - 1) base neg)

theorem parseContract_proven : ParseContract := by
  constructor
  · intro bits signed neg buf i j base
    rfl
  · intro bytes base
    simp only [parsevalue]
    split <;> rfl

end JuliaLean.MiscCov.Parsers
