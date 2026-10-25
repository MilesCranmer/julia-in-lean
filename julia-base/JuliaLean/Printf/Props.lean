import JuliaLean.Printf.Model

/-!
Properties of Printf. C99 means ISO/IEC 9899:1999 7.19.6.1 (n1256), which the
`Printf.Format` docstring promises ("Create a C printf-compatible format object",
`Printf.jl:68`) and the `@printf` docstring refers to (`Printf.jl:955,984`).
-/

namespace JuliaLean.Printf

open JuliaLean JuliaLean.Float

/-- An integer argument of type `t`. -/
def intArg {t : IntTy} (x : JInt t) : Arg := .int (.bits t x)

/-- An `Int` argument (wrapping literal). -/
def iarg (n : Int) : Arg := .int (.bits .i64 (ix n))

/-- An ASCII string argument. -/
def asciiArg (s : Bytes) : Arg := .str (s.map fun b => ⟨[b], 1⟩)

/-- `string(n)`: decimal digits in a format string. -/
def dec (n : Nat) : Bytes := digits 10 false n

/-- `@sprintf(f, args...)` with the format string given by its code units. -/
def sprintfB (f : Bytes) (args : List Arg) : Result Bytes := do format (← parseBytes f) args

/-- Format string bytes: `%` `.` `*` `#` `-` `+` space `0`. -/
def pc : Nat := 37
def dot : Nat := 46
def star : Nat := 42
def hashC : Nat := 35
def minusC : Nat := 45
def plusC : Nat := 43
def spaceC : Nat := 32
def zeroC : Nat := 48

/-- The flag characters `-+ #0`. -/
def isFlag (b : Nat) : Bool := b == 45 || b == 43 || b == 32 || b == 48 || b == 35

/-- The `Spec` fields a list of flags sets (C99 p4,p6: any order; `0` is
ignored with `-`). -/
def flagSpec (fl : List Nat) : Spec :=
  { leftalign := fl.contains 45, plus := fl.contains 43, space := fl.contains 32,
    zero := fl.contains 48 && !fl.contains 45, hash := fl.contains 35 }

/-- Escape every `%` of a literal text as `%%` (C99 p8, `%` conversion). -/
def escapePercent : Bytes → Bytes
  | [] => []
  | b :: r => if b == 37 then 37 :: 37 :: escapePercent r else b :: escapePercent r

/-- The `Spec` the parser builds for `%[-][+][ ][0]<W>[.<P>]c` (`Printf.jl:241-255`). -/
def intSpec (c : Nat) (left plus space zero : Bool) (W : Nat) (P : Option Nat) : Spec :=
  { conv := c, leftalign := left, plus := plus, space := space,
    zero := zero && !left && (match P with | some p => p == 0 | none => true),
    width := ix W, precision := ix (P.getD 0) }

/-- C99 p8 `d`/`i`: sign, then at least `P` digits (default 1); p4,p6: field width
with `-` (left adjustment) or `0` (zeros after the sign, only without precision). -/
def c99Int (left plus space zero : Bool) (W : Nat) (P : Option Nat) (v : Int) : Bytes :=
  let D := digits 10 false v.natAbs
  let sign := if v < 0 then [45] else if plus then [43] else if space then [32] else []
  let body := zeros (P.getD 1 - D.length) ++ D
  let len := sign.length + body.length
  if len < W then
    if left then sign ++ body ++ List.replicate (W - len) 32
    else if zero && P.isNone then sign ++ zeros (W - len) ++ body
    else List.replicate (W - len) 32 ++ sign ++ body
  else sign ++ body

/-- Formatting one argument with a single-conversion `Format` and no literal text. -/
def run1 (s : Spec) (a : Arg) : Result Bytes := format ⟨[[], []], [s], 1⟩ [a]

/-- `x` is exactly halfway between two multiples of `10^-P`. -/
def halfway (x : F64) (P : Nat) : Bool :=
  let (n, d) := F64.toRat x
  d != 0 && 2 * ((n.natAbs * 10 ^ P) % d) == d

/-- Fixed notation with `P` decimals, ties away from zero (the `@printf` caveat). -/
def fixedAway (x : F64) (P : Nat) : Bytes :=
  let (n, d) := F64.toRat x
  let m := (2 * n.natAbs * 10 ^ P + d) / (2 * d)
  (if F64.signbit x then [45] else []) ++ digits 10 false (m / 10 ^ P) ++
    (if P > 0 then 46 :: padDigits P (m % 10 ^ P) else [])

/-! ## Parsing -/

/-- Every invalid format string is rejected with `InvalidFormatStringError`, the
error `Format` throws for every other malformed specification (`Printf.jl:143-241`). -/
def FormatErrorsAreInvalidFormat : Prop :=
  ∀ (f : Bytes) (e : Error), parseBytes f = .error e → e = .invalidFormat

/-- Every conversion `Format` accepts has a formatting method: `computelen`
never throws `MethodError` from a missing `plength(::Spec{T})` method. -/
def AcceptedHaveMethods : Prop :=
  ∀ (f : Bytes) (F : Format), parseBytes f = .ok F → ∀ s ∈ F.formats, ∀ a : Arg,
    plengthArg s a ≠ .error (.julia (.methodError "plength"))

/-- C99 p4: flags come in any order and may repeat; `0` is ignored with `-`. -/
def FlagsAnyOrder : Prop :=
  ∀ (fl : Bytes) (b : Nat) (r : Bytes), (∀ c ∈ fl, isFlag c = true) → isFlag b = false →
    parseFlags {} ((fl ++ [b]).headD 0) ((fl ++ [b]).tail ++ r) = .ok (flagSpec fl, b, r)

/-- C99 p8 `%`: a format string without conversions prints its text with each
`%%` written as `%` (for every text shorter than `2^40` bytes, so that the
`Int` buffer length cannot overflow). -/
def LiteralPercent : Prop :=
  ∀ s : Bytes, s.length < 2 ^ 40 → (parseBytes (escapePercent s) >>= fun f => format f []) = .ok s

/-! ## Integer conversions -/

/-- C99 p4,p6,p8 for `d`/`i`: sign, precision and field width for every
`Int`-range value, all flags but `#`, and precision absent or positive. -/
def IntLayoutC99 : Prop :=
  ∀ (c : Nat) (left plus space zero : Bool) (W : Nat) (P : Option Nat) (t : IntTy) (x : JInt t),
    (c = cd ∨ c = ci) → W < 2 ^ 40 → (∀ p, P = some p → 0 < p ∧ p < 2 ^ 40) →
    run1 (intSpec c left plus space zero W P) (intArg x) = .ok (c99Int left plus space zero W P x.val)

/-- C99 p8: "The result of converting a zero value with a precision of zero is no
characters", for `d i o u x X` (`%.0d` etc.). -/
def IntegerZeroPrecision : Prop :=
  ∀ (c : Nat) (t : IntTy) (x : JInt t), isInts c = true → x.val = 0 →
    sprintfB [pc, dot, zeroC, c] [intArg x] = .ok []

/-- C99 p6: for `d i o u x X`, "if a precision is specified, the 0 flag is ignored". -/
def ZeroFlagPrecision : Prop :=
  ∀ (W P : Nat) (t : IntTy) (x : JInt t),
    sprintfB ([pc, zeroC] ++ dec W ++ [dot] ++ dec P ++ [cd]) [intArg x] =
      sprintfB ([pc] ++ dec W ++ [dot] ++ dec P ++ [cd]) [intArg x]

/-- C99 p6 `#` with `o`: it "increases the precision, if and only if necessary, to
force the first digit of the result to be a zero". -/
def OctalHashPrecision : Prop :=
  ∀ (P : Nat) (t : IntTy) (x : JInt t), 0 < x.val →
    sprintfB ([pc, hashC, dot] ++ dec P ++ [co]) [intArg x] =
      .ok (zeros (max P (ndigits 8 x.val.natAbs + 1) - ndigits 8 x.val.natAbs) ++
        digits 8 false x.val.natAbs)

/-- C99 p6 `#` with `x`/`X`: "a nonzero result has 0x (or 0X) prefixed to it";
zero has no prefix. -/
def HexZeroPrefix : Prop :=
  ∀ (c : Nat) (t : IntTy) (x : JInt t), c ∈ [cx, cX] → x.val = 0 →
    sprintfB [pc, hashC, c] [intArg x] = .ok [48]

/-- C99 p6 `+` and space apply to signed conversions only: `o u x X` of a
nonnegative value are unchanged by them. -/
def PlusUnsigned : Prop :=
  ∀ (c fl : Nat) (t : IntTy) (x : JInt t), c ∈ [co, cu, cx, cX] → fl ∈ [plusC, spaceC] →
    0 ≤ x.val → sprintfB [pc, fl, c] [intArg x] = sprintfB [pc, c] [intArg x]

/-- C99 p5: "A negative field width argument is taken as a - flag followed by a
positive field width". -/
def NegativeWidth : Prop :=
  ∀ (w : Nat) (t : IntTy) (x : JInt t), 0 < w →
    sprintfB [pc, star, cd] [iarg (-(w : Int)), intArg x] = sprintfB ([pc, minusC] ++ dec w ++ [cd]) [intArg x]

/-- C99 p5: "A negative precision argument is taken as if the precision were
omitted" (shown for `%.*s`). -/
def NegativePrecision : Prop :=
  ∀ (p : Int) (s : Bytes), (∀ b ∈ s, b < 128) → p < 0 →
    sprintfB [pc, dot, star, cs] [iarg p, asciiArg s] = sprintfB [pc, cs] [asciiArg s]

/-- Formatting an integer with a dynamic precision stores only inside the buffer
`format` allocated (`Printf.jl:441` stores digits `@inbounds`). -/
def IntDigitsInBounds : Prop :=
  ∀ (c : Nat) (p : Int) (t : IntTy) (x : JInt t), isInts c = true →
    sprintfB [pc, dot, star, c] [iarg p, intArg x] ≠ .error .unsafeWrite

/-! ## Strings and characters -/

/-- `%Ws`/`%-Ws` (no precision) pad the whole string to `W` columns, measured
with `textwidth` (`Printf.jl:1002-1006`). -/
def StringWidth : Prop :=
  ∀ (left : Bool) (W : Nat) (gs : List Glyph), W < 2 ^ 40 → textwidth gs < 2 ^ 40 →
    sizeofGlyphs gs < 2 ^ 40 →
    run1 {conv := cs, leftalign := left, width := ix W, precision := ix (-1)} (.str gs) =
      .ok (if left then gs.flatMap Glyph.bytes ++ List.replicate (W - textwidth gs) 32
           else List.replicate (W - textwidth gs) 32 ++ gs.flatMap Glyph.bytes)

/-- `%Wc`/`%-Wc` pad the character to `W` columns of `textwidth`. -/
def CharWidth : Prop :=
  ∀ (left : Bool) (W : Nat) (g : Glyph), W < 2 ^ 40 → g.width < 2 ^ 40 → g.bytes.length < 2 ^ 40 →
    run1 {conv := cc, leftalign := left, width := ix W, precision := ix (-1)} (.chr g) =
      .ok (if left then g.bytes ++ List.replicate (W - g.width) 32
           else List.replicate (W - g.width) 32 ++ g.bytes)

/-- `%W.Ps` prints whole characters of the string and pads the field to at least
`W` columns of `textwidth` (C99 p4 minimum field width; `Printf.jl:1002-1006`). -/
def StringFieldWidth : Prop :=
  ∀ (W P : Nat) (gs : List Glyph), ∃ k,
    sprintfB ([pc] ++ dec W ++ [dot] ++ dec P ++ [cs]) [.str gs] =
      .ok (List.replicate (W - textwidth (gs.take k)) 32 ++ (gs.take k).flatMap Glyph.bytes)

/-! ## Floating-point conversions -/

/-- C99 p8 `g`: the style is chosen from the exponent `X` of the `e`-style
conversion with precision `P - 1`. -/
def GeneralStyle : Prop :=
  ∀ (P : Nat) (x : F64), 0 < P → F64.isfinite x = true →
    sprintfB ([pc, dot] ++ dec P ++ [cg]) [.f64 x] =
      .ok (c99FloatBody {conv := cg} (F64.signbit x) (F64.toRat x).1.natAbs (F64.toRat x).2 P)

/-- C99 p6 `#` with `a`/`A`: the result "always contains a decimal-point character". -/
def HexZeroHash : Prop :=
  ∀ x : F64, F64.iszero x = true → (sprintfB [pc, hashC, ca] [.f64 x]).map (·.contains 46) = .ok true

/-- The `@printf` caveat (`Printf.jl:989-991`): "if a floating point number is
equally close to the numeric values of two possible output strings, the output
string further away from zero is chosen". -/
def TiesAway : Prop :=
  ∀ (P : Nat) (x : F64), F64.isfinite x = true → halfway x P = true →
    sprintfB ([pc, dot] ++ dec P ++ [cf]) [.f64 x] = .ok (fixedAway x P)

/-- `Inf` and `NaN` print as `Inf` and `NaN` (with sign and padding) for
`a A e E f F g G` (`Printf.jl:988-989`), for every flag, width and nonnegative precision. -/
def InfNaNText : Prop :=
  ∀ (c : Nat) (fl : List Nat) (W P : Nat) (x : F64), isFloats c = true → F64.isfinite x = false →
    W < 2 ^ 40 → P < 2 ^ 40 →
    ∃ (pre sign post : Bytes), pre.all (· == 32) ∧ post.all (· == 32) ∧ sign.length ≤ 1 ∧
      run1 {flagSpec fl with conv := c, width := ix W, precision := ix P} (.f64 x) =
        .ok (pre ++ sign ++ (if F64.isnan x then [78, 97, 78] else [73, 110, 102]) ++ post)

/-! ## BigFloat -/

/-- A finite `BigFloat` printed after literal text stays inside the buffer. -/
def BigFloatInBounds : Prop :=
  ∀ (pre : Bytes) (neg : Bool) (num den : Nat), pre.contains pc = false → 0 < den →
    sprintfB (pre ++ [pc, cf]) [.big (.finite neg num den)] ≠ .error .unsafeWrite

/-- `%Wf` of a finite `BigFloat` prints what MPFR prints (C99), without truncation. -/
def BigFloatWidth : Prop :=
  ∀ (W : Nat) (neg : Bool) (num den : Nat), 0 < den →
    sprintfB ([pc] ++ dec W ++ [cf]) [.big (.finite neg num den)] =
      c99Float {conv := cf, width := ix W, precision := ix 6} neg num den

/-! ## Docstring examples -/

/-- `Float64` value with the given bits, for docstring arguments. -/
def fb (n : Nat) : Arg := .f64 (F64.ofBits n)

/-- The `jldoctest` examples of `@printf` (`Printf.jl:958-1000`) and `@sprintf`
(`Printf.jl:1031-1033`), with `Float64` arguments given by their bits
(`1.234`, `1.23456`, `1.23`, `1.23e7`, `0.12345`, `Inf`, `NaN`, `0.5`, `0.025`,
`-0.0078125`, `34.567`). -/
def DocstringExamples : Prop :=
  sprintf "Hello %s" [asciiArg (bytes "world")] = .ok (bytes "Hello world") ∧
  sprintf "Scientific notation %e" [fb 0x3ff3be76c8b43958] = .ok (bytes "Scientific notation 1.234000e+00") ∧
  sprintf "Scientific notation three digits %.3e" [fb 0x3ff3c0c1fc8f3238] =
    .ok (bytes "Scientific notation three digits 1.235e+00") ∧
  sprintf "Decimal two digits %.2f" [fb 0x3ff3c0c1fc8f3238] = .ok (bytes "Decimal two digits 1.23") ∧
  sprintf "Padded to length 5 %5i" [iarg 123] = .ok (bytes "Padded to length 5   123") ∧
  sprintf "Padded with zeros to length 6 %06i" [iarg 123] = .ok (bytes "Padded with zeros to length 6 000123") ∧
  sprintf "Use shorter of decimal or scientific %g %g" [fb 0x3ff3ae147ae147ae, fb 0x416775dc00000000] =
    .ok (bytes "Use shorter of decimal or scientific 1.23 1.23e+07") ∧
  sprintf "Use dynamic width and precision  %*.*f" [iarg 10, iarg 2, fb 0x3fbf9a6b50b0f27c] =
    .ok (bytes "Use dynamic width and precision        0.12") ∧
  sprintf "%f %F %f %F" [fb 0x7ff0000000000000, fb 0x7ff0000000000000, fb 0x7ff8000000000000,
    fb 0x7ff8000000000000] = .ok (bytes "Inf Inf NaN NaN") ∧
  sprintf "%.0f %.1f %f" [fb 0x3fe0000000000000, fb 0x3f9999999999999a, fb 0xbf80000000000000] =
    .ok (bytes "0 0.0 -0.007812") ∧
  sprintf "this is a %s %15.1f" [asciiArg (bytes "test"), fb 0x4041489374bc6a7f] =
    .ok (bytes "this is a test            34.6")

end JuliaLean.Printf
