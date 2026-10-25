import JuliaLean.Core

/-!
`Printf.Format(f::AbstractString)`, `stdlib/Printf/src/Printf.jl:128-275` at
master `bbfa0ce4150` (identical in behaviour in 1.13.2, which spells the digit
test `b - UInt8('0') < 0x0a`).

The byte position is represented by the unconsumed suffix of `codeunits(f)`:
every `b = bytes[pos]; pos += 1` is one `pop`, and `pos > len` is "the suffix is
empty". `bytes[pos]` past the end throws `BoundsError`; the reads the source
guards with `pos > len && throw(...)` throw `InvalidFormatStringError`
(`Error.invalidFormat`). Width and precision accumulate in `Int` and wrap.

The literal text between conversions is kept as the source keeps it: the raw
code units of `substringranges[i]` (lines 153 and 272), with `%%` pairs still
doubled; `format` drops the second `%` of each pair while printing.
-/

namespace JuliaLean.Printf

open JuliaLean

/-- Code units, as natural numbers below 256. -/
abbrev Bytes := List Nat
/-- Julia `Int`. -/
abbrev I := JInt64

/-- An `Int` literal. -/
def ix (n : Int) : I := JInt.lit .i64 n

/-- `codeunits(s)` of a Lean string (UTF-8). -/
def bytes (s : String) : Bytes := s.toUTF8.data.toList.map UInt8.toNat

/-- Exceptions and undefined behaviour of Printf. -/
inductive Error where
  /-- `Printf.InvalidFormatStringError`. -/
  | invalidFormat
  /-- A Base exception. -/
  | julia (e : JlError)
  /-- A failed `::Integer` type assertion, `Printf.jl:300,304`. -/
  | typeError
  /-- A store outside the buffer where bounds checks are off (`@inbounds`, or C code
  writing through a pointer). Julia does not throw; the heap is corrupted. -/
  | unsafeWrite
  /-- An argument/conversion combination outside the model. -/
  | unmodelled
  deriving DecidableEq, Repr

abbrev Result (α : Type) := Except Error α

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.ok h)
    | .isFalse h => .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => match decEq a b with
    | .isTrue h => .isTrue (congrArg Except.error h)
    | .isFalse h => .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/-- `struct Spec{T}`, `Printf.jl:33-43`; `conv` is the character in `T = Val{conv}`. -/
structure Spec where
  conv : Nat := 100
  leftalign : Bool := false
  plus : Bool := false
  space : Bool := false
  zero : Bool := false
  hash : Bool := false
  width : I := ix 0
  precision : I := ix 0
  dynamicWidth : Bool := false
  dynamicPrecision : Bool := false
  deriving DecidableEq, Repr

/-- Conversion bytes. -/
def cd : Nat := 100
def ci : Nat := 105
def cu : Nat := 117
def co : Nat := 111
def cx : Nat := 120
def cX : Nat := 88
def ce : Nat := 101
def cE : Nat := 69
def cf : Nat := 102
def cF : Nat := 70
def cg : Nat := 103
def cG : Nat := 71
def ca : Nat := 97
def cA : Nat := 65
def cc : Nat := 99
def cC : Nat := 67
def cs : Nat := 115
def cS : Nat := 83

/-- The dispatch unions of `Printf.jl:14-20` (`Ints` is `d i u x X o`, `Floats` is `e E f F g G a A`). -/
def isInts (c : Nat) : Bool := [100, 105, 117, 120, 88, 111].contains c
def isFloats (c : Nat) : Bool := [101, 69, 102, 70, 103, 71, 97, 65].contains c
def isChars (c : Nat) : Bool := c == cc || c == cC
def isStrings (c : Nat) : Bool := c == cs || c == cS
def isHexA (c : Nat) : Bool := c == ca || c == cA

/-- `base(T)`, `Printf.jl:96`. -/
def base (c : Nat) : Nat := if [120, 88, 97, 65].contains c then 16 else if c == co then 8 else 10

/-- `b = bytes[pos]; pos += 1` without a preceding end check. -/
def pop : Bytes → Result (Nat × Bytes)
  | [] => .error (.julia .boundsError)
  | b :: r => .ok (b, r)

/-- The flag loop, `Printf.jl:160-181`. -/
def parseFlags (s : Spec) (b : Nat) (r : Bytes) : Result (Spec × Nat × Bytes) :=
  let s' := if b == 45 then some {s with leftalign := true}
    else if b == 43 then some {s with plus := true}
    else if b == 32 then some {s with space := true}
    else if b == 48 then some {s with zero := true}
    else if b == 35 then some {s with hash := true}
    else none
  match s' with
  | none => .ok ({s with zero := s.zero && !s.leftalign}, b, r)
  | some s' => match r with
    | [] => .error .invalidFormat
    | c :: r' => parseFlags s' c r'
termination_by structural r

def isDigit (b : Nat) : Bool := 48 ≤ b && b ≤ 57

/-- The digit loops of `Printf.jl:191-196` and `215-220`: the next byte is read
before the end test, so a final digit at the end of the string reads past it. -/
def parseDigits (n : I) (b : Nat) (r : Bytes) : Result (I × Nat × Bytes) :=
  if isDigit b then
    let n := ix 10 * n + ix (b - 48)
    match r with
    | [] => .error (.julia .boundsError)
    | c :: r' => if r'.isEmpty then .ok (n, c, r') else parseDigits n c r'
  else .ok (n, b, r)
termination_by structural r

/-- Width, `Printf.jl:183-197`; `numarguments` is counted by `numArguments`. -/
def parseWidth (s : Spec) (b : Nat) (r : Bytes) : Result (Spec × Nat × Bytes) := do
  if b == 42 then
    let (b, r) ← pop r
    pure ({s with dynamicWidth := true}, b, r)
  else
    let (w, b, r) ← parseDigits (ix 0) b r
    pure ({s with width := w}, b, r)

/-- Precision, `Printf.jl:199-223`; the `Bool` is `parsedprecdigits`. -/
def parsePrecision (s : Spec) (b : Nat) (r : Bytes) : Result (Spec × Bool × Nat × Bytes) := do
  if b != 46 then pure (s, false, b, r) else
    if r.isEmpty then .error .invalidFormat else
      let (b, r) ← pop r
      if r.isEmpty then pure (s, true, b, r) else
        if b == 42 then
          let (b, r) ← pop r
          pure ({s with dynamicPrecision := true}, true, b, r)
        else
          let (p, b, r) ← parseDigits (ix 0) b r
          pure ({s with precision := p}, true, b, r)

/-- Length modifiers, read and ignored, `Printf.jl:225-239`. -/
def parseLength (b : Nat) (r : Bytes) : Result (Nat × Bytes) := do
  if b == 104 || b == 108 then
    if r.isEmpty then .error .invalidFormat else
      let (c, r) ← pop r
      if c == b then
        if r.isEmpty then .error .invalidFormat else pop r
      else pure (c, r)
  else if [76, 106, 113, 116, 122].contains b then  -- "Ljqtz"
    if r.isEmpty then .error .invalidFormat else pop r
  else pure (b, r)

/-- The accepted conversion characters `b"diouxXDOUeEfFgGaAcCsSpn"`, `Printf.jl:241`. -/
def accepted : Bytes :=
  [100, 105, 111, 117, 120, 88, 68, 79, 85, 101, 69, 102, 70, 103, 71, 97, 65, 99, 67, 115, 83, 112, 110]

/-- Type check and defaults, `Printf.jl:241-255`. -/
def finishSpec (s : Spec) (parsedprecdigits : Bool) (b : Nat) : Result Spec :=
  if !accepted.contains b then .error .invalidFormat else
    let s := {s with conv := b}
    if isInts b && s.precision.val > 0 then .ok {s with zero := false}
    else if (isStrings b || isChars b) && !parsedprecdigits then .ok {s with precision := ix (-1)}
    else if isHexA b && !parsedprecdigits then .ok {s with precision := ix (-1)}
    else if isFloats b && !parsedprecdigits then .ok {s with precision := ix 6}
    else .ok s

/-- One conversion specification, from the byte after `%`, `Printf.jl:156-255`. -/
def parseSpec (b : Nat) (r : Bytes) : Result (Spec × Bytes) := do
  let (s, b, r) ← parseFlags {} b r
  let (s, b, r) ← parseWidth s b r
  let (s, prec, b, r) ← parsePrecision s b r
  let (b, r) ← parseLength b r
  let s ← finishSpec s prec b
  pure (s, r)

/-- The literal scan loops, `Printf.jl:138-152` and `257-271`. Returns the code
units consumed, the last byte read (`b`), and the byte after a `%` that starts a
conversion together with the rest. -/
def scanLoop (acc : Bytes) (b : Nat) : Bytes → Result (Bytes × Nat × Option (Nat × Bytes))
  | [] => .ok (acc, b, none)
  | [37] => .error .invalidFormat
  | 37 :: 37 :: r => scanLoop (acc ++ [37, 37]) 37 r
  | 37 :: d :: r => .ok (acc ++ [37], 37, some (d, r))
  | c :: r => scanLoop (acc ++ [c]) c r

/-- The substring range `start:pos - 1 - (b == UInt8('%'))`, `Printf.jl:153,272`. -/
def range (acc : Bytes) (b : Nat) : Bytes := if b == 37 then acc.dropLast else acc

/-- `struct Format`, `Printf.jl:82-93`. -/
structure Format where
  substrings : List Bytes
  formats : List Spec
  numarguments : Nat
  deriving DecidableEq, Repr

/-- Arguments consumed by one specification, `Printf.jl:187,210,254`. -/
def Spec.nargs (s : Spec) : Nat :=
  1 + (if s.dynamicWidth then 1 else 0) + (if s.dynamicPrecision then 1 else 0)

/-- The main loop, `Printf.jl:155-273`, after its first `%`. Each iteration
consumes at least two bytes, so `len` iterations suffice. -/
def parseRest : Nat → Nat → Bytes → Result (List Spec × List Bytes)
  | 0, _, _ => .error .invalidFormat
  | fuel + 1, b, r => do
    let (s, r) ← parseSpec b r
    let (acc, last, next) ← scanLoop [] s.conv r
    match next with
    | none => pure ([s], [range acc last])
    | some (c, r) =>
      let (ss, ls) ← parseRest fuel c r
      pure (s :: ss, range acc last :: ls)

/-- `Printf.Format(f)`, `Printf.jl:128-275`. -/
def parseBytes (f : Bytes) : Result Format := do
  let (acc, b, next) ← scanLoop [] 0 f
  match next with
  | none => pure ⟨[range acc b], [], 0⟩
  | some (c, r) =>
    let (ss, ls) ← parseRest f.length c r
    pure ⟨range acc b :: ls, ss, (ss.map Spec.nargs).sum⟩

def parse (f : String) : Result Format := parseBytes (bytes f)

end JuliaLean.Printf
