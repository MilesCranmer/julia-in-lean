import JuliaLean.base.checked
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.parsers.ints
import JuliaLean.base.strings.unicode


/-!
Integer parsing from UTF-8 bytes, `base/parse.jl` and `base/parsers/ints.jl` at
master `bbfa0ce4150`.

A Julia `String` is its list of code units (`Bytes`); index arithmetic on `Int`
indices (`i`, `j`, `k`, `d`, `p`) stays within the string length, so it is
modelled with `Int`. Code units are `UInt8` values and their arithmetic wraps as
in Julia.

The UTF-8 decoding (`iterate`, `getindex`, `thisind`) and `isspace` follow
`base/strings/string.jl:243-271,504-560`, `base/char.jl:111-192` and
`base/strings/unicode.jl:372-382,624-626`. The only Unicode data `isspace`
needs is the set of code points in categories Zs, Zl and Zp (Unicode 16):
U+0020, U+00A0, U+1680, U+2000-U+200A, U+2028, U+2029, U+202F, U+205F, U+3000.

Each `while` loop is recursion on fuel that exceeds the number of iterations:
every iteration advances an index by at least one within the string.

Julia 1.13.2 parses integers with a different, `Char`-based implementation
(`base/parse.jl:51-183` at `v1.13.2`) that this module does not model.
-/

namespace JuliaLean.ParsePrint.IntParse

open JuliaLean JuliaLean.ParsePrint


/-! ### Whitespace, `base/parse.jl:53-97` -/

/-- `isspace_ascii(b)`, `base/parse.jl:53`. -/
def isspaceAscii (b : Byte) : Bool := b.val == 32 || (9 ≤ b.val && b.val ≤ 13)

/-- `skipspacechar(s, i)`, `base/parse.jl:57-60`. -/
def skipspacechar (s : Bytes) (i : Int) : Int :=
  let (c, next) := iterate s i
  if isspaceChar c then next else i

/-- `skipspacechar_back(s, i, j)`, `base/parse.jl:63-66`. -/
def skipspacecharBack (s : Bytes) (i j : Int) : Int :=
  let k := thisind s j
  if k ≥ i ∧ isspaceChar (getChar s k) then k - 1 else j

/-- The loop of `skipspace(s, i, j)`, `base/parse.jl:70-82`. -/
def skipspaceLoop (s : Bytes) (j : Int) : Nat → Int → Int
  | 0, i => i
  | n+1, i =>
    if i ≤ j then
      let b := cu s i
      if isspaceAscii b then skipspaceLoop s j n (i + 1)
      else if b.val ≥ 0x80 ∧ skipspacechar s i > i then skipspaceLoop s j n (skipspacechar s i)
      else i
    else i

/-- `skipspace(s, i, j)`: the first index in `i:j` not starting a whitespace character. -/
def skipspace (s : Bytes) (i j : Int) : Int := skipspaceLoop s j (s.length + 1) i

/-- The loop of `skipspace_back(s, i, j)`, `base/parse.jl:85-97`. -/
def skipspaceBackLoop (s : Bytes) (i : Int) : Nat → Int → Int
  | 0, j => j
  | n+1, j =>
    if j ≥ i then
      let b := cu s j
      if isspaceAscii b then skipspaceBackLoop s i n (j - 1)
      else if b.val ≥ 0x80 ∧ skipspacecharBack s i j < j then
        skipspaceBackLoop s i n (skipspacecharBack s i j)
      else j
    else j

/-- `skipspace_back(s, i, j)`: the last index in `i:j` before trailing whitespace. -/
def skipspaceBack (s : Bytes) (i j : Int) : Int := skipspaceBackLoop s i (s.length + 1) j

/-- `parseint_preamble(signed, base, s, i, j)`, `base/parse.jl:102-123`:
`(sgn, base, index of the first digit)`. -/
def preamble (signed : Bool) (base : Int) (s : Bytes) (i j : Int) : Int × Int × Int :=
  let i := skipspace s i j
  if i > j then (0, 0, 0) else
  let (sgn, i, stop) :=
    if signed ∧ (cuN s i = 45 ∨ cuN s i = 43) then
      let sgn : Int := if cuN s i = 45 then -1 else 1
      let i := skipspace s (i + 1) j
      (sgn, i, decide (i > j))
    else ((1 : Int), i, false)
  if stop then (0, 0, 0) else
  if base == 0 then
    if i < j ∧ cuN s i = 48 then
      let c := cuN s (i + 1)
      let b : Int := if c = 98 then 2 else if c = 111 then 8 else if c = 120 then 16 else 10
      if b == 10 then (sgn, b, i) else (sgn, b, if i + 2 ≤ j then i + 2 else 0)
    else (sgn, 10, i)
  else (sgn, base, i)


/-! ### `base/parse.jl:127-171` -/

/-- The error `throw_parseint_error(T, s, i, j, sgn, base, d)` throws,
`base/parse.jl:153-171`; it never returns. Messages are abbreviated. -/
def throwParseintError (t : IntTy) (s : Bytes) (j sgn base d : Int) : Jl JlError := do
  if sgn == 0 then return .argumentError "input string is empty or only contains whitespace"
  if ¬ (2 ≤ base ∧ base ≤ 62) then return .argumentError "invalid base"
  if d == 0 then return .argumentError "premature end of integer"
  let k := skipspaceBack s d j
  let scan : Nat → Int → Int := fun fuel p0 =>
    (List.range fuel).foldl (fun p _ =>
      if p ≤ k ∧ (digitvalue (cu s p) base).val < base then p + 1 else p) p0
  let p := scan (s.length + 1) d
  if p > d then
    if (← parseint t s d (p - 1) base (decide (sgn < 0))) == .overflow then
      return .overflowError "overflow parsing"
  if ¬ (1 ≤ p ∧ p ≤ ncu s) then return .boundsError
  let c := getChar s p
  if p > d ∧ isspaceChar c then return .argumentError "extra characters after whitespace"
  return .argumentError "invalid base digit"

/-- The arguments of the `throw_parseint_error` call when `parseint_utf8` fails. -/
structure Fail where
  sgn : Int
  base : Int
  d : Int

/-- The sign of the decimal fast path, `base/parse.jl:131`. -/
def fastNeg (t : IntTy) (s : Bytes) (i : Int) : Bool := t.signed && cuN s i == 45

/-- The first digit of the decimal fast path, after a sign, `base/parse.jl:132`. -/
def fastK (t : IntTy) (s : Bytes) (i : Int) : Int :=
  i + (if fastNeg t s i || (t.signed && cuN s i == 43) then 1 else 0)

/-- Whether `parseint_utf8` takes its decimal fast path, `base/parse.jl:129-133`:
a first digit `1-9` after an optional sign, and a last byte that is a digit
(`UInt8` differences, which wrap). -/
def fastCond (t : IntTy) (s : Bytes) (i j base : Int) : Prop :=
  (base = 0 ∨ base = 10) ∧ i ≤ j ∧ fastK t s i ≤ j ∧
    (cu s (fastK t s i) - byte 49).val ≤ 8 ∧ (cu s j - byte 48).val ≤ 9

instance (t : IntTy) (s : Bytes) (i j base : Int) : Decidable (fastCond t s i j base) := by
  unfold fastCond; infer_instance

/-- `parseint_utf8` after `parseint_preamble`, `base/parse.jl:141-146`. -/
def slowPath (t : IntTy) (s : Bytes) (j : Int) : Int × Int × Int → Jl (Sum (JInt t) Fail)
  | (sgn, b, d) =>
    if sgn ≠ 0 ∧ 2 ≤ b ∧ b ≤ 62 ∧ d ≠ 0 then
      (parseint t s d (skipspaceBack s d j) b (decide (sgn < 0))).map fun
        | .val n => .inl n
        | _ => .inr ⟨sgn, b, d⟩
    else pure (.inr ⟨sgn, b, d⟩)

/-- `parseint_utf8(T, s, i, j, base, raise)`, `base/parse.jl:127-148`, before the
`raise` branch: the value, or the arguments of the error to throw. When the fast
path fails it returns or throws directly (lines 135-138); otherwise control
continues with the preamble (line 141). -/
def parseintUtf8Core (t : IntTy) (s : Bytes) (i j base : Int) : Jl (Sum (JInt t) Fail) :=
  if fastCond t s i j base then
    (parseint t s (fastK t s i) j 10 (fastNeg t s i)).map fun
      | .val n => .inl n
      | _ => .inr ⟨if fastNeg t s i then -1 else 1, 10, fastK t s i⟩
  else slowPath t s j (preamble t.signed base s i j)

/-- `parseint_utf8(T, s, i, j, base, raise)`: `nothing` or a thrown error on failure. -/
def parseintUtf8 (t : IntTy) (s : Bytes) (i j base : Int) (raise : Bool) :
    Jl (Option (JInt t)) := do
  match ← parseintUtf8Core t s i j base with
  | .inl n => return some n
  | .inr f =>
    if raise then .error (← throwParseintError t s j f.sgn f.base f.d)
    else return none

/-- `check_valid_base(base)` and the `0` default, `base/parse.jl:234-239,259`. -/
def validBase (base : Option Int) : Jl Int :=
  match base with
  | none => pure 0
  | some b => if 2 ≤ b ∧ b ≤ 62 then pure b else .error (.argumentError "invalid base")

/-- `tryparse(T, s; base)` for `T <: BitInteger` and `s::String`, `base/parse.jl:247-262`. -/
def tryparse (t : IntTy) (s : Bytes) (base : Option Int := none) : Jl (Option (JInt t)) := do
  parseintUtf8 t s 1 (ncu s) (← validBase base) false

/-- `parse(T, s; base)` for `T <: BitInteger` and `s::String`, `base/parse.jl:250-262`. -/
def parse (t : IntTy) (s : Bytes) (base : Option Int := none) : Jl (JInt t) := do
  match ← parseintUtf8 t s 1 (ncu s) (← validBase base) true with
  | some v => pure v
  | none => .error (.argumentError "should not happen")

end JuliaLean.ParsePrint.IntParse
section

/-!
# `base/parse.jl` beyond the integer grammar

The integer grammar on UTF-8 bytes (`isspace_ascii` through `throw_parseint_error`,
`base/parse.jl:53-171`) is `JuliaLean.ParsePrint.IntParse`. This file models the
remaining methods of `base/parse.jl` at master `bbfa0ce4150`: `parse` of a `Char`,
`tryparse_internal` with explicit positions, `Bool`, the float and complex
parsers and the generic fallbacks.

Strings are their UTF-8 bytes (`IntParse.Bytes`). Floating-point parsing itself is
`Base.Parsers.parsefloat` (`base/parsers/floats.jl`, another area), passed in as a
function `pf` from the bytes of a slice to the parsed value or `none`
(`ParseFailure`). A float is any type `F` with the operations the complex parser
uses.
-/

namespace JuliaLean.DocsSyntaxCov.Parse

open JuliaLean
open JuliaLean.ParsePrint.IntParse

/-- The bytes `s[i:j]` (empty if `j < i`). -/
def slice (s : Bytes) (i j : Int) : Bytes := (s.drop (i - 1).toNat).take (j - i + 1).toNat

/-- `nextind(s, i)` for a valid index `i` of a `String`: the index after its character. -/
def nextind (s : Bytes) (i : Int) : Int := (iterate s i).2

/-- `prevind(s, i)` for `1 ≤ i ≤ ncodeunits(s) + 1`: `thisind(s, i - 1)`, and `0` at `i = 1`. -/
def prevind (s : Bytes) (i : Int) : Int := if i ≤ 1 then 0 else thisind s (i - 1)

/-- `lastindex(s)`. -/
def lastindex (s : Bytes) : Int := if s.isEmpty then 0 else thisind s (ncu s)

/-- `isspace(s[i])`. -/
def isspaceAt (s : Bytes) (i : Int) : Bool := isspaceChar (getChar s i)

/-- The code point of `s[i]` when it is ASCII, else a value above `0x7f`. -/
def asciiAt (s : Bytes) (i : Int) : Nat := if cuN s i < 0x80 then cuN s i else 0x100

/-! ## `parse(::Type{Union{}}, ...)`, `base/parse.jl:37,263` -/

/-- `parse(::Type{Union{}}, slurp...; kwargs...)` and `tryparse(::Type{Union{}}, ...)`:
both throw `ErrorException("cannot parse a value as Union{}")`; the result type is
empty, so the model returns the message. -/
def parseUnionAll {α : Type} (_args : List α) : String := "cannot parse a value as Union{}"

/-! ## `parse(T, c::AbstractChar; base)`, `base/parse.jl:39-47` -/

/-- The digit value of `c` in `parse(T, c::AbstractChar)`, `base/parse.jl:42-44`, with `a` the
value of `'a'` (10 up to base 36, 36 above); `none` for a character that is no digit. -/
def charDigit (c : Nat) (a : Int) : Option Int :=
  if 48 ≤ c ∧ c ≤ 57 then some ((c : Int) - 48)
  else if 65 ≤ c ∧ c ≤ 90 then some ((c : Int) - 65 + 10)
  else if 97 ≤ c ∧ c ≤ 122 then some ((c : Int) - 97 + a)
  else none

/-- `parse(::Type{T}, c::AbstractChar; base = 10)` for a `BitInteger` `T` and a valid `Char`
with code point `c`, `base/parse.jl:39-47`. `Char` comparisons compare code points for
valid characters. -/
def parseChar (t : IntTy) (c : Nat) (base : Int := 10) : Jl (JInt t) :=
  let a : Int := if base ≤ 36 then 10 else 36
  if ¬ (2 ≤ base ∧ base ≤ 62) then .error (.argumentError "invalid base")
  else match charDigit c a with
    | none => .error (.argumentError "invalid digit")
    | some d => if ¬ d < base then .error (.argumentError "invalid base digit") else JInt.convert (t.name) t d

/-! ## `tryparse_internal` for integers with positions, `base/parse.jl:173-182,365-366` -/

/-- `tryparse_internal(T, s::UTF8String, startpos, endpos, base, raise)` for
`T <: BitInteger`, `base/parse.jl:173-178`: the bytes up to the end of the character
at `endpos`. -/
def tryparseInternalInt (t : IntTy) (s : Bytes) (startpos endpos base : Int) (raise : Bool) :
    Jl (Option (JInt t)) :=
  let j := if 1 ≤ startpos ∧ startpos ≤ endpos then nextind s endpos - 1 else startpos - 1
  parseintUtf8 t s startpos j base raise

/-- `tryparse_internal(T, s, startpos, endpos, raise) where T<:Integer`,
`base/parse.jl:365-366`: base 10. -/
def tryparseInternalInt10 (t : IntTy) (s : Bytes) (startpos endpos : Int) (raise : Bool) :
    Jl (Option (JInt t)) :=
  tryparseInternalInt t s startpos endpos 10 raise

/-- The UTF-8 copy `String(SubString(s, startpos, endpos))` that
`tryparse_internal` parses for a string type other than `UTF8String`,
`base/parse.jl:179-181`, given the copy's bytes. -/
def tryparseInternalIntCopy (t : IntTy) (copy : Bytes) (base : Int) (raise : Bool) :
    Jl (Option (JInt t)) :=
  parseintUtf8 t copy 1 (ncu copy) base raise

/-- `parseint_string(T, s, base, raise)` for `T <: BitInteger` and `s::UTF8String`,
`base/parse.jl:258-262`. -/
def parseintString (t : IntTy) (s : Bytes) (base : Option Int) (raise : Bool) :
    Jl (Option (JInt t)) := do
  let b ← validBase base
  parseintUtf8 t s 1 (ncu s) b raise

/-- `check_valid_base(base)`, `base/parse.jl:234-239`. -/
def checkValidBase (base : Int) : Jl Int :=
  if 2 ≤ base ∧ base ≤ 62 then pure base else .error (.argumentError "invalid base")

/-! ## `tryparse_internal(::Type{Bool}, ...)`, `base/parse.jl:184-232` -/

/-- The loop skipping leading whitespace, `base/parse.jl:202-204`. -/
def skipLeading (s : Bytes) (endpos : Int) : Nat → Int → Int
  | 0, i => i
  | n + 1, i => if i ≤ endpos ∧ isspaceAt s i then skipLeading s endpos n (nextind s i) else i

/-- The loop skipping trailing whitespace, `base/parse.jl:205-207`. -/
def skipTrailing (s : Bytes) (startpos : Int) : Nat → Int → Int
  | 0, j => j
  | n + 1, j => if j ≥ startpos ∧ isspaceAt s j then skipTrailing s startpos n (prevind s j) else j

def trueBytes : Bytes := [byte 116, byte 114, byte 117, byte 101]
def falseBytes : Bytes := [byte 102, byte 97, byte 108, byte 115, byte 101]

/-- `all(isspace, SubString(s, a, b))`. -/
def allSpace (s : Bytes) (a b : Int) : Nat → Int → Bool
  | 0, _ => true
  | n + 1, i => if i > b then true else isspaceAt s i && allSpace s a b n (nextind s i)

/-- `tryparse_internal(::Type{Bool}, sbuff::String, startpos, endpos, base, raise)`.
`isnumeric` is `Base.isnumeric` on the raw `Char` of `sbuff[1]`. -/
def tryparseBool (isnumeric : Nat → Bool) (s : Bytes) (startpos endpos base : Int) (raise : Bool) :
    Jl (Option Bool) := do
  if s.isEmpty then
    if raise then .error (.argumentError "input string is empty") else return none
  if isnumeric (getChar s 1) then
    let intres ← tryparseInternalInt .u8 s startpos endpos base false
    if intres.map (·.val) == some 1 then return some true
    if intres.map (·.val) == some 0 then return some false
    if raise then .error (.argumentError "invalid Bool representation")
  let origStart := startpos
  let origEnd := endpos
  let fuel := s.length + 1
  let startpos := skipLeading s endpos fuel startpos
  let endpos := skipTrailing s startpos fuel endpos
  let len := endpos - startpos + 1
  if len == 4 ∧ slice s startpos (startpos + 3) == trueBytes then return some true
  if len == 5 ∧ slice s startpos (startpos + 4) == falseBytes then return some false
  if raise then
    if allSpace s origStart origEnd fuel origStart then
      .error (.argumentError "input string only contains whitespace")
    else .error (.argumentError "invalid Bool representation")
  return none

/-- `parse(Bool, s)` / `tryparse(Bool, s)`: `parseint_string` with no base calls
`tryparse_internal(Bool, s, firstindex(s), lastindex(s), 0, raise)`, `base/parse.jl:250-262`. -/
def parseBoolStr (isnumeric : Nat → Bool) (s : Bytes) (raise : Bool) : Jl (Option Bool) :=
  tryparseBool isnumeric s 1 (lastindex s) 0 raise

/-! ## Floats, `base/parse.jl:268-280` -/

/-- The forward loop of `tryparse_internal(T, s, i, j)` for `T <: IEEEFloat`. -/
def skipAsciiFwd (s : Bytes) (j : Int) : Nat → Int → Int
  | 0, i => i
  | n + 1, i => if i ≤ j ∧ isspaceAscii (cu s i) then skipAsciiFwd s j n (i + 1) else i

/-- The backward loop of `tryparse_internal(T, s, i, j)` for `T <: IEEEFloat`. -/
def skipAsciiBack (s : Bytes) (i : Int) : Nat → Int → Int
  | 0, j => j
  | n + 1, j => if j ≥ i ∧ isspaceAscii (cu s j) then skipAsciiBack s i n (j - 1) else j

/-- `tryparse_internal(::Type{T}, s::DenseUTF8String, i, j) where {T<:IEEEFloat}`,
`base/parse.jl:268-277`: ASCII whitespace is trimmed, then `Parsers.parsefloat`
(`pf`, on the remaining bytes) decides. -/
def tryparseFloatRange {F : Type} (pf : Bytes → Option F) (s : Bytes) (i j : Int) : Option F :=
  let i := skipAsciiFwd s j (s.length + 1) i
  let j := skipAsciiBack s i (s.length + 1) j
  pf (slice s i j)

/-- `tryparse(::Type{T}, s::DenseUTF8String) where {T<:IEEEFloat}`, `base/parse.jl:278-279`,
and `tryparse(T, s::AbstractString) = tryparse(T, String(s))`, line 280 (on the UTF-8
copy's bytes). -/
def tryparseFloat {F : Type} (pf : Bytes → Option F) (s : Bytes) : Option F :=
  tryparseFloatRange pf s 1 (ncu s)

/-! ## Generic fallbacks, `base/parse.jl:346-363,368-374` -/

/-- `tryparse_internal(T, s, startpos, endpos) where T<:Real`, `base/parse.jl:346-347`:
the whole string, or a `SubString` of it; `tp` is `tryparse(T, ·)` on bytes. -/
def tryparseInternalReal {R : Type} (tp : Bytes → Option R) (s : Bytes) (startpos endpos : Int) :
    Option R :=
  if startpos == 1 ∧ endpos == lastindex s then tp s
  else tp (slice s startpos (nextind s endpos - 1))

/-- `_parse_failure(T, s, startpos, endpos)`, `base/parse.jl:362-363`: the
`ArgumentError` naming `s[startpos:endpos]`. -/
def parseFailure (s : Bytes) (startpos endpos : Int) : Bytes × JlError :=
  (slice s startpos (nextind s endpos - 1), .argumentError "cannot parse")

/-- `tryparse_internal(T, s, startpos, endpos, raise) where T<:Real`, `base/parse.jl:348-354`. -/
def tryparseInternalRealRaise {R : Type} (tp : Bytes → Option R) (s : Bytes)
    (startpos endpos : Int) (raise : Bool) : Jl (Option R) :=
  let result := tryparseInternalReal tp s startpos endpos
  if raise ∧ result.isNone then .error (parseFailure s startpos endpos).2 else pure result

/-- `tryparse_internal(T, s, raise; kwargs...) where T<:Real`, `base/parse.jl:355-361`. -/
def tryparseInternalRealKw {R : Type} (tp : Bytes → Option R) (s : Bytes) (raise : Bool) :
    Jl (Option R) :=
  let result := tp s
  if raise ∧ result.isNone then .error (parseFailure s 1 (lastindex s)).2 else pure result

/-- `parse(T, s; kwargs...) where T<:Real = convert(T, tryparse_internal(T, s, true; kwargs...))`,
`base/parse.jl:368-369`. -/
def parseReal {R : Type} (tp : Bytes → Option R) (s : Bytes) : Jl R := do
  match ← tryparseInternalRealKw tp s true with
  | some r => pure r
  | none => .error (.methodError "convert")

/-! ## Complex numbers, `base/parse.jl:284-343,370-374` -/

/-- Operations on the component type `T` the complex parser needs. -/
structure FloatOps (F : Type) where
  zero : F
  neg : F → F

/-- `findnext(in(('+','-')), s, i)`: the first `+` or `-` character at or after `i`, or `0`
(`something(..., 0)`). Characters are visited with `nextind`. -/
def findnextSign (s : Bytes) : Nat → Int → Int
  | 0, _ => 0
  | n + 1, i =>
    if i > ncu s then 0
    else if asciiAt s i = 43 ∨ asciiAt s i = 45 then i
    else findnextSign s n (nextind s i)

/-- `findprev(in(('m','i','j')), s, e)`, or `0`. -/
def findprevUnit (s : Bytes) : Nat → Int → Int
  | 0, _ => 0
  | n + 1, i =>
    if i < 1 then 0
    else if asciiAt s i = 109 ∨ asciiAt s i = 105 ∨ asciiAt s i = 106 then i
    else findprevUnit s n (prevind s i)

/-- `tryparse_internal(::Type{Complex{T}}, s::DenseUTF8String, i, e, raise)`,
`base/parse.jl:284-339`. `tp s a b raise` is `tryparse_internal(T, s, a, b, raise)`
for the component type. The result is `(re, im)`. -/
def tryparseComplex {F : Type} (ops : FloatOps F) (tp : Bytes → Int → Int → Bool → Jl (Option F))
    (s : Bytes) (i e : Int) (raise : Bool) : Jl (Option (F × F)) := do
  let fuel := s.length + 1
  let i := skipLeading s e fuel i
  if i > e then
    if raise then .error (.argumentError "input string is empty or only contains whitespace")
    return none
  let ip := findnextSign s fuel i
  let ip := if ip == i then findnextSign s fuel (ip + 1) else ip
  let ip := if ip != 0 ∧ (asciiAt s (prevind s ip) = 101 ∨ asciiAt s (prevind s ip) = 69) then
      findnextSign s fuel (ip + 1) else ip
  let ii := findprevUnit s fuel e
  let ii ← if ii > 0 ∧ asciiAt s ii = 109 then
      let ii := prevind s ii
      if asciiAt s ii ≠ 105 then
        if raise then .error (.argumentError "expected trailing \"im\", found only \"m\"")
        return none
      pure ii
    else pure ii
  if ip == 0 then
    if ii > i ∧ ¬ (ii == i + 1 ∧ (asciiAt s i = 43 ∨ asciiAt s i = 45)) then
      match ← tp s i (prevind s ii) raise with
      | none => return none
      | some x => return some (ops.zero, x)
    else
      match ← tp s i e raise with
      | none => return none
      | some x => return some (x, ops.zero)
  if ii < ip then
    if raise then .error (.argumentError "missing imaginary unit")
    return none
  match ← tp s i (prevind s ip) raise with
  | none => return none
  | some re =>
    match ← tp s (ip + 1) (prevind s ii) raise with
    | none => return none
    | some im => return some (re, if asciiAt s ip = 45 then ops.neg im else im)

/-- `tryparse(Complex{S}, s)`, `base/parse.jl:373-374`, and (with `raise`) `parse(T, s) where
T<:Complex`, lines 370-371; non-`String` strings are first copied to a `String`
(`tryparse_internal(T::Type{Complex{S}}, s::AbstractString, ...)`, lines 342-343). -/
def tryparseComplexStr {F : Type} (ops : FloatOps F) (tp : Bytes → Int → Int → Bool → Jl (Option F))
    (s : Bytes) (raise : Bool) : Jl (Option (F × F)) :=
  tryparseComplex ops tp s 1 (lastindex s) raise

/-- The component parser `tryparse_internal(T, s, a, b, raise)` for `T <: IEEEFloat`, as
`tryparse_internal` with positions (`base/parse.jl:268-277,348-354`) builds it from `pf`. -/
def floatComponent {F : Type} (pf : Bytes → Option F) (s : Bytes) (a b : Int) (raise : Bool) :
    Jl (Option F) :=
  let r := tryparseFloatRange pf s a b
  if raise ∧ r.isNone then .error (parseFailure s a b).2 else pure r

end JuliaLean.DocsSyntaxCov.Parse

end


/-!
# Model of `base/parse.jl`

Typed models for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit platform
(`Int === Int64`). Each translated method's docstring carries its verbatim source; its body keeps
the source's byte and character checks, branch order, and error precedence.

* Fixed-width integer results are `JInt t`; IEEE float results use `JuliaLean.base.float.FV T`.
* `StringOps`, `IntegerOps`, `FloatOps`, and `ComplexOps` expose string operations and parser calls
  as explicit interfaces. The external `Parsers.parseint` and `Parsers.parsefloat` functions are
  not Base methods.
* Source methods that remain unsupported stay visible as untranslated blocks with a reason.
-/

namespace JuliaLean.base.parse

open JuliaLean

inductive ParseIntResult (α : Type) where
  | value (value : α)
  | failure
  | overflow

inductive ParseFloatResult (α : Type) where
  | value (value : α)
  | failure

structure StringOps (S : Type) where
  codeunit : S → Nat → Nat
  ncodeunits : S → Nat
  iterate : S → Nat → Char × Nat
  thisind : S → Nat → Nat
  charAt : S → Nat → Char
  nextind : S → Nat → Nat
  prevind : S → Nat → Nat
  isSpace : Char → Bool
  isNumeric : Char → Bool
  isUtf8 : S → Bool
  firstindex : S → Nat
  lastindex : S → Nat
  substring : S → Nat → Nat → S
  toUtf8 : S → S
  toString : S → S
  emptyUtf8 : S
  isEmpty : S → Bool
  isTrueSlice : S → Nat → Nat → Bool
  isFalseSlice : S → Nat → Nat → Bool
  allSpace : S → Nat → Nat → Bool
  findNextSign : S → Nat → Nat
  findPrevImaginaryUnit : S → Nat → Nat

structure IntegerOps (S T : Type) where
  signed : Bool
  bitInteger : Bool
  parseDigits : S → Nat → Nat → Nat → Bool → ParseIntResult T
  digitValue : Nat → Nat → Nat
  convertDigit : Int → Jl T
  convertParsed : T → Jl T

structure FloatOps (S : Type) (T : JuliaLean.base.float.FTy) where
  parseFloat : S → Nat → Nat → ParseFloatResult (JuliaLean.base.float.FV T)

structure ComplexValue (R : Type) where
  re : R
  im : R

structure ComplexOps (S R : Type) where
  parseRealInternal : S → Nat → Nat → Bool → Jl (Option R)
  toString : S → S
  zero : R → R
  neg : R → R

inductive UnionBottomError where
  | errorException (message : String)

-- UNTRANSLATED
-- Source: base/parse.jl:1-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## string to integer functions ##
-- 
-- """
--     parse(type, str; base)
-- 
-- Parse a string as a number. For `Integer` types, a base can be specified
-- (the default is 10). For floating-point types, the string is parsed as a decimal
-- floating-point number.  `Complex` types are parsed from decimal strings
-- of the form `"R±Iim"` as a `Complex(R,I)` of the requested type; `"i"` or `"j"` can also be
-- used instead of `"im"`, and `"R"` or `"Iim"` are also permitted.
-- If the string does not contain a valid number, an error is raised.
-- 
-- !!! compat "Julia 1.1"
--     `parse(Bool, str)` requires at least Julia 1.1.
-- 
-- # Examples
-- ```jldoctest
-- julia> parse(Int, "1234")
-- 1234
-- 
-- julia> parse(Int, "1234", base = 5)
-- 194
-- 
-- julia> parse(Int, "afc", base = 16)
-- 2812
-- 
-- julia> parse(Float64, "1.2e-3")
-- 0.0012
-- 
-- julia> parse(Complex{Float64}, "3.2e-1 + 4.5im")
-- 0.32 + 4.5im
-- ```
-- """
-- parse(T::Type, str; base = Int)
-- /Source
-- Reason: The public `parse(type, str; base)` declaration is documentation only.
/-!
Julia source: base/parse.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parse(::Type{Union{}}, slurp...; kwargs...) = error("cannot parse a value as Union{}")
```
-/
def parseUnionBottom {Args Kwargs Result : Type} (_slurp : Args) (_kwargs : Kwargs) :
    Except UnionBottomError Result :=
  .error (.errorException "cannot parse a value as Union{}")

/--
Julia source: base/parse.jl:39-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse(::Type{T}, c::AbstractChar; base::Integer = 10) where T<:Integer
    a::Int = (base <= 36 ? 10 : 36)
    2 <= base <= 62 || throw(ArgumentError("invalid base: base must be 2 ≤ base ≤ 62, got $base"))
    d = '0' <= c <= '9' ? c-'0'    :
        'A' <= c <= 'Z' ? c-'A'+10 :
        'a' <= c <= 'z' ? c-'a'+a  : throw(ArgumentError("invalid digit: $(repr(c))"))
    d < base || throw(ArgumentError("invalid base $base digit $(repr(c))"))
    convert(T, d)
end
```
-/
def parse_char_Integer {T : Type} (charCode : Char → Nat) (convert : Int → Jl T)
    (c : Char) (base : Int) : Jl T := do
  let radixOffset := if base ≤ 36 then 10 else 36
  if !(2 ≤ base ∧ base ≤ 62) then throw (.argumentError "invalid integer base")
  let code := charCode c
  let digit ←
    if 48 ≤ code ∧ code ≤ 57 then pure (code - 48)
    else if 65 ≤ code ∧ code ≤ 90 then pure (code - 65 + 10)
    else if 97 ≤ code ∧ code ≤ 122 then pure (code - 97 + radixOffset)
    else throw (.argumentError "invalid digit")
  if Int.ofNat digit ≥ base then throw (.argumentError "digit is outside the base")
  convert (Int.ofNat digit)

/--
Julia source: base/parse.jl:48-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Base's integer grammar, on the UTF-8 bytes of a string:
#     [whitespace] [sign] [whitespace] [0x | 0o | 0b] digits [whitespace]
# A sign is only accepted for signed types, and a radix prefix only when no base is given.

isspace_ascii(b::UInt8) = (b == UInt8(' ')) | (UInt8('\t') <= b <= UInt8('\r'))

```
-/
def isspace_ascii (b : Nat) : Bool :=
(b == 32) || (decide (9 ≤ b) && decide (b ≤ 13))

/--
Julia source: base/parse.jl:55-60 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Whitespace beyond ASCII is rare; decoding it stays out of the inlined loops below.
# The index after the character at `i` of `s` if it is whitespace, else `i`.
@noinline function skipspacechar(s::UTF8String, i::Int)
    c, next = iterate(s, i)::Tuple{Char, Int}
    return isspace(c) ? next : i
end
```
-/
def skipspacechar {S : Type} (ops : StringOps S) (s : S) (i : Nat) : Nat :=
  let (c, next) := ops.iterate s i
  if ops.isSpace c then next else i

/--
Julia source: base/parse.jl:61-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# The index before the character ending at `j` of `s` if it is whitespace starting at or
# after `i`, else `j`.
@noinline function skipspacechar_back(s::UTF8String, i::Int, j::Int)
    k = thisind(s, j)
    return k >= i && isspace(s[k]) ? k - 1 : j
end
```
-/
def skipspacechar_back {S : Type} (ops : StringOps S) (s : S) (i j : Nat) : Nat :=
  let k := ops.thisind s j
  if decide (k ≥ i) && ops.isSpace (ops.charAt s k) then k - 1 else j

/--
Julia source: base/parse.jl:67-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# The first index in `i:j` of `s` that does not start a whitespace character, or `j + 1`.
# `i:j` must be in bounds, as for the functions below.
@inline function skipspace(s::UTF8String, i::Int, j::Int)
    while i <= j
        b = @inbounds codeunit(s, i)
        if isspace_ascii(b)
            i += 1
        elseif b >= 0x80 && (next = skipspacechar(s, i)) > i
            i = next
        else
            break
        end
    end
    return i
end
```
-/
def skipspace {S : Type} (ops : StringOps S) (s : S) (i j : Nat) : Nat :=
  List.foldl (fun current _ =>
    if current ≤ j then
      let b := ops.codeunit s current
      if isspace_ascii b then current + 1
      else if b ≥ 128 then
        let next := skipspacechar ops s current
        if next > current then next else current
      else current
    else current) i (List.range (j - i + 1))

/--
Julia source: base/parse.jl:83-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# The last index in `i:j` of `s` before any trailing whitespace, or `i - 1`.
@inline function skipspace_back(s::UTF8String, i::Int, j::Int)
    while j >= i
        b = @inbounds codeunit(s, j)
        if isspace_ascii(b)
            j -= 1
        elseif b >= 0x80 && (prev = skipspacechar_back(s, i, j)) < j
            j = prev
        else
            break
        end
    end
    return j
end

```
-/
def skipspace_back {S : Type} (ops : StringOps S) (s : S) (i j : Nat) : Nat :=
  List.foldl (fun current _ =>
    if i ≤ current then
      let b := ops.codeunit s current
      if isspace_ascii b then current - 1
      else if b ≥ 128 then
        let previous := skipspacechar_back ops s i current
        if previous < current then previous else current
      else current
    else current) j (List.range (j - i + 1))

/--
Julia source: base/parse.jl:99-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Parse the grammar before the digits in the bytes `i:j` of `s`. Returns the sign, the base
# (from the prefix, or 10, if `base` is 0) and the index of the first digit; `(0, 0, 0)` if
# only whitespace and a sign remain, and a zero index if a prefix has nothing after it.
@inline function parseint_preamble(signed::Bool, base::Int, s::UTF8String, i::Int, j::Int)
    i = skipspace(s, i, j)
    i > j && return 0, 0, 0
    sgn = 1
    if signed
        c = @inbounds codeunit(s, i)
        if c == UInt8('-') || c == UInt8('+')
            c == UInt8('-') && (sgn = -1)
            i = skipspace(s, i + 1, j)
            i > j && return 0, 0, 0
        end
    end
    if base == 0
        base = 10
        if i < j && @inbounds(codeunit(s, i)) == UInt8('0')
            c = @inbounds codeunit(s, i + 1)
            base = c == UInt8('b') ? 2 : c == UInt8('o') ? 8 : c == UInt8('x') ? 16 : 10
            base == 10 || (i = i + 2 <= j ? i + 2 : 0)
        end
    end
    return sgn, base, i
end

```
-/
def parseint_preamble {S : Type} (ops : StringOps S) (signed : Bool) (base : Int)
    (s : S) (start finish : Nat) : Int × Int × Nat := Id.run do
  let mut i := skipspace ops s start finish
  if i > finish then return (0, 0, 0)
  let mut sign : Int := 1
  if signed then
    let c := ops.codeunit s i
    if c == 45 || c == 43 then
      if c == 45 then sign := -1
      i := skipspace ops s (i + 1) finish
      if i > finish then return (0, 0, 0)
  let mut radix := base
  if radix == 0 then
    radix := 10
    if decide (i < finish) && ops.codeunit s i == 48 then
      let c := ops.codeunit s (i + 1)
      radix := if c == 98 then 2 else if c == 111 then 8 else if c == 120 then 16 else 10
      if radix != 10 then i := if i + 2 ≤ finish then i + 2 else 0
  return (sign, radix, i)

/--
Julia source: base/parse.jl:149-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Throw the error for the bytes `i:j` of `s` that `parseint_utf8` rejected, given the
# preamble's results. In the digits, it is the first problem from the left: a non-digit,
# overflow, or anything but whitespace after whitespace.
@noinline function throw_parseint_error(::Type{T}, s::UTF8String, i::Int, j::Int,
                                        sgn::Int, base::Int, d::Int) where {T}
    sgn == 0 && throw(ArgumentError("input string is empty or only contains whitespace"))
    2 <= base <= 62 ||
        throw(ArgumentError(LazyString("invalid base: base must be 2 ≤ base ≤ 62, got ", base)))
    str = repr(SubString(s, i, thisind(s, j)))
    d == 0 && throw(ArgumentError("premature end of integer: $str"))
    k = skipspace_back(s, d, j)
    p = d
    while p <= k && Parsers.digitvalue(codeunit(s, p), base) < base
        p += 1
    end
    if p > d && Parsers.parseint(T, codeunits(s), d, p - 1, base, sgn < 0) === Parsers.OVERFLOW
        throw(OverflowError("overflow parsing $str"))
    end
    c = s[p]
    p > d && isspace(c) && throw(ArgumentError("extra characters after whitespace in $str"))
    throw(ArgumentError("invalid base $base digit $(repr(c)) in $str"))
end

```
-/
def throw_parseint_error {S T : Type} (sops : StringOps S) (iops : IntegerOps S T)
    (s : S) (_start finish : Nat) (sign base : Int) (digitStart : Nat) : Jl Unit := do
  if sign == 0 then throw (.argumentError "empty integer input")
  if !(2 ≤ base ∧ base ≤ 62) then throw (.argumentError "invalid integer base")
  if digitStart == 0 then throw (.argumentError "premature end of integer")
  let lastDigit := skipspace_back sops s digitStart finish
  let radix := base.toNat
  let p := List.foldl (fun current _ =>
    if decide (current ≤ lastDigit) && iops.digitValue (sops.codeunit s current) radix < radix
    then current + 1 else current) digitStart (List.range (lastDigit - digitStart + 1))
  if p > digitStart then
    match iops.parseDigits s digitStart (p - 1) radix (sign < 0) with
    | .overflow => throw (.overflowError "integer parsing overflow")
    | _ => pure ()
  if decide (p > digitStart) && sops.isSpace (sops.charAt s p) then
    throw (.argumentError "extra characters after whitespace in integer")
  throw (.argumentError "invalid integer digit")

/--
Julia source: base/parse.jl:125-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Parse the bytes `i:j` of `s`, which must be in bounds, with the grammar above. Returns the
# value, or `nothing` (or throws, if `raise`) when the bytes are not a valid `T`.
@inline function parseint_utf8(::Type{T}, s::UTF8String, i::Int, j::Int, base::Int, raise::Bool) where {T<:Integer}
    # Decimal digits not starting with '0', after an optional sign, need none of the grammar.
    if (base == 0 || base == 10) && i <= j
        c = @inbounds codeunit(s, i)
        neg = T <: Signed && c == UInt8('-')
        k = i + (neg | (T <: Signed && c == UInt8('+')))
        if k <= j && ((@inbounds codeunit(s, k)) - UInt8('1') <= 0x08) &
                     ((@inbounds codeunit(s, j)) - UInt8('0') <= 0x09)
            n = Parsers.parseint(T, codeunits(s), k, j, 10, neg)
            n isa Parsers.ParseFailure || return n
            raise && throw_parseint_error(T, s, i, j, neg ? -1 : 1, 10, k)
            return nothing
        end
    end
    sgn, b, d = parseint_preamble(T <: Signed, base, s, i, j)
    if sgn != 0 && 2 <= b <= 62 && d != 0
        n = Parsers.parseint(T, codeunits(s), d, skipspace_back(s, d, j), b, sgn < 0)
        n isa Parsers.ParseFailure || return n
    end
    raise && throw_parseint_error(T, s, i, j, sgn, b, d)
    return nothing
end
```
-/
def parseint_utf8 {S T : Type} (sops : StringOps S) (iops : IntegerOps S T)
    (s : S) (start finish : Nat) (base : Int) (raise : Bool) : Jl (Option T) := do
  if (base == 0 || base == 10) && decide (start ≤ finish) then
    let c := sops.codeunit s start
    let negative := iops.signed && c == 45
    let hasSign := negative || (iops.signed && c == 43)
    let firstDigit := start + (if hasSign then 1 else 0)
    if decide (firstDigit ≤ finish) &&
        decide (49 ≤ sops.codeunit s firstDigit) && decide (sops.codeunit s firstDigit ≤ 57) &&
        decide (48 ≤ sops.codeunit s finish) && decide (sops.codeunit s finish ≤ 57) then
      match iops.parseDigits s firstDigit finish 10 negative with
      | .value value => return some value
      | .failure | .overflow =>
          if raise then
            let _ ← throw_parseint_error sops iops s start finish (if negative then -1 else 1) 10 firstDigit
          return none
  let (sign, radix, digitStart) := parseint_preamble sops iops.signed base s start finish
  if sign != 0 && digitStart != 0 && decide (2 ≤ radix) && decide (radix ≤ 62) then
    let lastDigit := skipspace_back sops s digitStart finish
    match iops.parseDigits s digitStart lastDigit radix.toNat (sign < 0) with
    | .value value => return some value
    | .failure | .overflow => pure ()
  if raise then
    let _ ← throw_parseint_error sops iops s start finish sign radix digitStart
  return none

/--
Julia source: base/parse.jl:173-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tryparse_internal(::Type{T}, s::AbstractString, startpos::Int, endpos::Int, base::Integer, raise::Bool) where T<:Integer
    if s isa UTF8String
        # the last byte of the span, which is empty if `startpos` is not positive
        j = 1 <= startpos <= endpos ? nextind(s, endpos) - 1 : startpos - 1
        return parseint_utf8(T, s, startpos, j, Int(base), raise)
    end
    # other string types are parsed from a UTF-8 copy
    str = 1 <= startpos <= endpos ? String(SubString(s, startpos, endpos)) : ""
    return parseint_utf8(T, str, 1, ncodeunits(str), Int(base), raise)
end
```
-/
def tryparse_internal_Integer {S T : Type} (sops : StringOps S) (iops : IntegerOps S T)
    (s : S) (startPos endPos : Nat) (base : Int) (raise : Bool) : Jl (Option T) := do
  if sops.isUtf8 s then
    let lastByte := if 1 ≤ startPos ∧ startPos ≤ endPos then sops.nextind s endPos - 1 else startPos - 1
    parseint_utf8 sops iops s startPos lastByte base raise
  else
    let utf8 := if 1 ≤ startPos ∧ startPos ≤ endPos
      then sops.toUtf8 (sops.substring s startPos endPos) else sops.emptyUtf8
    parseint_utf8 sops iops utf8 1 (sops.ncodeunits utf8) base raise

/--
Julia source: base/parse.jl:183-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function tryparse_internal(::Type{Bool}, sbuff::AbstractString,
        startpos::Int, endpos::Int, base::Integer, raise::Bool)
    if isempty(sbuff)
        raise && throw(ArgumentError("input string is empty"))
        return nothing
    end

    if isnumeric(sbuff[1])
        intres = tryparse_internal(UInt8, sbuff, startpos, endpos, base, false)
        (intres == 1) && return true
        (intres == 0) && return false
        raise && throw(ArgumentError("invalid Bool representation: $(repr(sbuff))"))
    end

    orig_start = startpos
    orig_end   = endpos

    # Ignore leading and trailing whitespace
    while startpos <= endpos && isspace(sbuff[startpos])
        startpos = nextind(sbuff, startpos)
    end
    while endpos >= startpos && isspace(sbuff[endpos])
        endpos = prevind(sbuff, endpos)
    end

    len = endpos - startpos + 1
    if sbuff isa Union{String, SubString{String}}
        p = pointer(sbuff) + startpos - 1
        truestr = "true"
        falsestr = "false"
        GC.@preserve sbuff truestr falsestr begin
            (len == 4) && (0 == memcmp(p, unsafe_convert(Ptr{UInt8}, truestr), 4)) && (return true)
            (len == 5) && (0 == memcmp(p, unsafe_convert(Ptr{UInt8}, falsestr), 5)) && (return false)
        end
    else
        (len == 4) && (SubString(sbuff, startpos:startpos+3) == "true") && (return true)
        (len == 5) && (SubString(sbuff, startpos:startpos+4) == "false") && (return false)
    end

    if raise
        substr = SubString(sbuff, orig_start, orig_end) # show input string in the error to avoid confusion
        if all(isspace, substr)
            throw(ArgumentError("input string only contains whitespace"))
        else
            throw(ArgumentError("invalid Bool representation: $(repr(substr))"))
        end
    end
    return nothing
end
```
-/
def tryparse_internal_Bool {S : Type} (sops : StringOps S)
    (tryparseUInt8 : S → Nat → Nat → Int → Bool → Jl (Option (JInt .u8)))
    (s : S) (startPos endPos : Nat) (base : Int) (raise : Bool) : Jl (Option Bool) := do
  if sops.isEmpty s then
    if raise then throw (.argumentError "empty Bool input") else return none
  if sops.isNumeric (sops.charAt s (sops.firstindex s)) then
    let intResult ← tryparseUInt8 s startPos endPos base false
    match intResult with
    | some value =>
        if value.val == 1 then return some true
        if value.val == 0 then return some false
    | none => pure ()
    if raise then throw (.argumentError "invalid Bool representation")
    return none
  let originalStart := startPos
  let originalEnd := endPos
  let start := List.foldl (fun current _ =>
    if decide (current ≤ endPos) && sops.isSpace (sops.charAt s current)
    then sops.nextind s current else current) startPos
      (List.range (endPos - startPos + 1))
  let finish := List.foldl (fun current _ =>
    if decide (start ≤ current) && sops.isSpace (sops.charAt s current)
    then sops.prevind s current else current) endPos
      (List.range (endPos - startPos + 1))
  let length := if finish < start then 0 else finish - start + 1
  if length == 4 && sops.isTrueSlice s start finish then return some true
  if length == 5 && sops.isFalseSlice s start finish then return some false
  if raise then
    if sops.allSpace s originalStart originalEnd then
      throw (.argumentError "Bool input contains only whitespace")
    else throw (.argumentError "invalid Bool representation")
  return none

/--
Julia source: base/parse.jl:233-239 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

@inline function check_valid_base(base)
    if 2 <= base <= 62
        return base
    end
    throw(ArgumentError("invalid base: base must be 2 ≤ base ≤ 62, got $base"))
end
```
-/
def check_valid_base (base : Int) : Jl Int :=
  if 2 ≤ base ∧ base ≤ 62 then .ok base
  else .error (.argumentError "invalid base: expected 2 through 62")

/--
Julia source: base/parse.jl:256-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Parse all of `s`. Base's fixed-width types parse UTF-8 strings directly; other integer
# types, such as `BigInt`, can have their own `tryparse_internal` methods.
@inline function parseint_string(::Type{T}, s::AbstractString, base, raise::Bool) where {T<:Integer}
    b = base === nothing ? 0 : Int(check_valid_base(base))  # 0 takes the base from a prefix
    T <: BitInteger && s isa UTF8String && return parseint_utf8(T, s, 1, ncodeunits(s), b, raise)
    return tryparse_internal(T, s, firstindex(s), lastindex(s), b, raise)
end
```
-/
def parseint_string {S T : Type} (sops : StringOps S) (iops : IntegerOps S T)
    (tryparseInternal : S → Nat → Nat → Int → Bool → Jl (Option T))
    (s : S) (base : Option Int) (raise : Bool) : Jl (Option T) := do
  let radix ← match base with
    | none => pure 0
    | some value => check_valid_base value
  if iops.bitInteger && sops.isUtf8 s then
    parseint_utf8 sops iops s 1 (sops.ncodeunits s) radix raise
  else tryparseInternal s (sops.firstindex s) (sops.lastindex s) radix raise

/--
Julia source: base/parse.jl:240-248 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    tryparse(type, str; base)

Like [`parse`](@ref), but returns either a value of the requested type,
or [`nothing`](@ref) if the string does not contain a valid number.
"""
tryparse(::Type{T}, s::AbstractString; base::Union{Nothing,Integer} = nothing) where {T<:Integer} =
    parseint_string(T, s, base, false)
```
-/
def tryparse_Integer {S T : Type} (sops : StringOps S) (iops : IntegerOps S T)
    (tryparseInternal : S → Nat → Nat → Int → Bool → Jl (Option T))
    (s : S) (base : Option Int) : Jl (Option T) :=
  parseint_string sops iops tryparseInternal s base false

/--
Julia source: base/parse.jl:249-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function parse(::Type{T}, s::AbstractString; base::Union{Nothing,Integer} = nothing) where {T<:Integer}
    v = parseint_string(T, s, base, true)
    v === nothing && error("should not happen")
    convert(T, v)
end

```
-/
def parse_Integer {S T : Type} (sops : StringOps S) (iops : IntegerOps S T)
    (tryparseInternal : S → Nat → Nat → Int → Bool → Jl (Option T))
    (s : S) (base : Option Int) : Jl T := do
  let result ← parseint_string sops iops tryparseInternal s base true
  match result with
  | some value => iops.convertParsed value
  | none => throw (.argumentError "should not happen")

/-!
Julia source: base/parse.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tryparse(::Type{Union{}}, slurp...; kwargs...) = error("cannot parse a value as Union{}")
```
-/
def tryparseUnionBottom {Args Kwargs Result : Type} (_slurp : Args) (_kwargs : Kwargs) :
    Except UnionBottomError Result :=
  .error (.errorException "cannot parse a value as Union{}")
/--
Julia source: base/parse.jl:264-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## string to float functions ##

# Parse `s[i:j]` as a float, ignoring ASCII whitespace around it
function tryparse_internal(::Type{T}, s::DenseUTF8String, i::Int, j::Int) where {T<:IEEEFloat}
    while i <= j && isspace_ascii(codeunit(s, i))
        i += 1
    end
    while j >= i && isspace_ascii(codeunit(s, j))
        j -= 1
    end
    x = Parsers.parsefloat(T, codeunits(s), i, j)
    return x isa Parsers.ParseFailure ? nothing : x
end
```
-/
def tryparse_internal_Float {S : Type} {T : JuliaLean.base.float.FTy}
    (sops : StringOps S) (fops : FloatOps S T) (s : S) (start finish : Nat) : Option (JuliaLean.base.float.FV T) :=
  let i := List.foldl (fun current _ =>
    if decide (current ≤ finish) && isspace_ascii (sops.codeunit s current)
    then current + 1 else current) start (List.range (finish - start + 1))
  let j := List.foldl (fun current _ =>
    if decide (i ≤ current) && isspace_ascii (sops.codeunit s current)
    then current - 1 else current) finish (List.range (finish - start + 1))
  match fops.parseFloat s i j with
  | .value value => some value
  | .failure => none

/--
Julia source: base/parse.jl:278-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tryparse(::Type{T}, s::DenseUTF8String) where {T<:IEEEFloat} =
    tryparse_internal(T, s, 1, ncodeunits(s))
```
-/
def tryparse_Float_UTF8 {S : Type} {T : JuliaLean.base.float.FTy}
    (sops : StringOps S) (fops : FloatOps S T) (s : S) : Option (JuliaLean.base.float.FV T) :=
  tryparse_internal_Float sops fops s 1 (sops.ncodeunits s)

/--
Julia source: base/parse.jl:280-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
tryparse(::Type{T}, s::AbstractString) where {T<:IEEEFloat} = tryparse(T, String(s)::String)
```
-/
def tryparse_Float_Abstract {S : Type} {T : JuliaLean.base.float.FTy}
    (sops : StringOps S) (fops : FloatOps S T) (s : S) : Option (JuliaLean.base.float.FV T) :=
  tryparse_Float_UTF8 sops fops (sops.toString s)

/--
Julia source: base/parse.jl:281-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## string to complex functions ##

function tryparse_internal(::Type{Complex{T}}, s::DenseUTF8String, i::Int, e::Int, raise::Bool) where {T<:Real}
    # skip initial whitespace
    while i ≤ e && isspace(s[i])
        i = nextind(s, i)
    end
    if i > e
        raise && throw(ArgumentError("input string is empty or only contains whitespace"))
        return nothing
    end

    # find index of ± separating real/imaginary parts (if any)
    i₊ = something(findnext(in(('+','-')), s, i), 0)
    if i₊ == i # leading ± sign
        i₊ = something(findnext(in(('+','-')), s, i₊+1), 0)
    end
    if i₊ != 0 && s[prevind(s, i₊)] in ('e','E') # exponent sign
        i₊ = something(findnext(in(('+','-')), s, i₊+1), 0)
    end

    # find trailing im/i/j
    iᵢ = something(findprev(in(('m','i','j')), s, e), 0)
    if iᵢ > 0 && s[iᵢ] == 'm' # im
        iᵢ = prevind(s, iᵢ)
        if s[iᵢ] != 'i'
            raise && throw(ArgumentError("expected trailing \"im\", found only \"m\""))
            return nothing
        end
    end

    if i₊ == 0 # purely real or imaginary value
        if iᵢ > i && !(iᵢ == i+1 && s[i] in ('+','-')) # purely imaginary (not "±inf")
            x = tryparse_internal(T, s, i, prevind(s, iᵢ), raise)
            x === nothing && return nothing
            return Complex{T}(zero(x),x)
        else # purely real
            x = tryparse_internal(T, s, i, e, raise)
            x === nothing && return nothing
            return Complex{T}(x)
        end
    end

    if iᵢ < i₊
        raise && throw(ArgumentError("missing imaginary unit"))
        return nothing # no imaginary part
    end

    # parse real part
    re = tryparse_internal(T, s, i, prevind(s, i₊), raise)
    re === nothing && return nothing

    # parse imaginary part
    im = tryparse_internal(T, s, i₊+1, prevind(s, iᵢ), raise)
    im === nothing && return nothing

    return Complex{T}(re, s[i₊]=='-' ? -im : im)
end
```
-/
def tryparse_internal_Complex {S R : Type} (sops : StringOps S) (cops : ComplexOps S R)
    (s : S) (start finish : Nat) (raise : Bool) : Jl (Option (ComplexValue R)) := do
  let i := List.foldl (fun current _ =>
    if decide (current ≤ finish) && sops.isSpace (sops.charAt s current)
    then sops.nextind s current else current) start (List.range (finish - start + 1))
  if i > finish then
    if raise then throw (.argumentError "input string is empty or whitespace") else return none
  let mut plusMinus := sops.findNextSign s i
  if plusMinus == i then plusMinus := sops.findNextSign s (plusMinus + 1)
  if plusMinus != 0 && (sops.charAt s (sops.prevind s plusMinus) == 'e' ||
      sops.charAt s (sops.prevind s plusMinus) == 'E') then
    plusMinus := sops.findNextSign s (plusMinus + 1)
  let mut imaginary := sops.findPrevImaginaryUnit s finish
  if decide (imaginary > 0) && sops.charAt s imaginary == 'm' then
    imaginary := sops.prevind s imaginary
    if sops.charAt s imaginary != 'i' then
      if raise then throw (.argumentError "expected trailing im") else return none
  if plusMinus == 0 then
    if decide (imaginary > i) && !(imaginary == i + 1 &&
        (sops.charAt s i == '+' || sops.charAt s i == '-')) then
      let value ← cops.parseRealInternal s i (sops.prevind s imaginary) raise
      match value with
      | none => return none
      | some value => return some ⟨cops.zero value, value⟩
    else
      let value ← cops.parseRealInternal s i finish raise
      match value with
      | none => return none
      | some value => return some ⟨value, cops.zero value⟩
  if imaginary < plusMinus then
    if raise then throw (.argumentError "missing imaginary unit") else return none
  let parsedReal ← cops.parseRealInternal s i (sops.prevind s plusMinus) raise
  match parsedReal with
  | none => return none
  | some real =>
      let parsedImag ← cops.parseRealInternal s (plusMinus + 1) (sops.prevind s imaginary) raise
      match parsedImag with
      | none => return none
      | some imag =>
          let signedImag := if sops.charAt s plusMinus == '-' then cops.neg imag else imag
          return some ⟨real, signedImag⟩

/--
Julia source: base/parse.jl:340-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# the ±1 indexing above for ascii chars is specific to String, so convert:
tryparse_internal(T::Type{Complex{S}}, s::AbstractString, i::Int, e::Int, raise::Bool) where S<:Real =
    tryparse_internal(T, String(s), i, e, raise)

```
-/
def tryparse_internal_Complex_Abstract {S R : Type} (sops : StringOps S) (cops : ComplexOps S R)
    (s : S) (start finish : Nat) (raise : Bool) : Jl (Option (ComplexValue R)) :=
  tryparse_internal_Complex sops cops (cops.toString s) start finish raise

/--
Julia source: base/parse.jl:345-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# fallback methods for tryparse_internal
tryparse_internal(::Type{T}, s::AbstractString, startpos::Int, endpos::Int) where T<:Real =
    startpos == firstindex(s) && endpos == lastindex(s) ? tryparse(T, s) : tryparse(T, SubString(s, startpos, endpos))
```
-/
def tryparse_internal_Real {S R : Type} (sops : StringOps S)
    (tryparseWhole : S → Jl (Option R)) (tryparseSlice : S → Nat → Nat → Jl (Option R))
    (s : S) (start finish : Nat) : Jl (Option R) :=
  if start == sops.firstindex s && finish == sops.lastindex s then tryparseWhole s
  else tryparseSlice s start finish

/--
Julia source: base/parse.jl:362-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _parse_failure(T, s::AbstractString, startpos = firstindex(s), endpos = lastindex(s)) =
    throw(ArgumentError(LazyString("cannot parse ", repr(s[startpos:endpos]), " as ", T)))
```
-/
def parse_failure {S : Type} (_sops : StringOps S) (_s : S) (_start _finish : Nat) : Jl Unit :=
  .error (.argumentError "cannot parse value as requested type")

/--
Julia source: base/parse.jl:348-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tryparse_internal(::Type{T}, s::AbstractString, startpos::Int, endpos::Int, raise::Bool) where T<:Real
    result = tryparse_internal(T, s, startpos, endpos)
    if raise && result === nothing
        _parse_failure(T, s, startpos, endpos)
    end
    return result
end
```
-/
def tryparse_internal_Real_raise {S R : Type} (sops : StringOps S)
    (tryparseSpan : S → Nat → Nat → Jl (Option R))
    (s : S) (start finish : Nat) (raise : Bool) : Jl (Option R) := do
  let result ← tryparseSpan s start finish
  if raise && result.isNone then
    let _ ← parse_failure sops s start finish
  return result

/--
Julia source: base/parse.jl:355-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tryparse_internal(::Type{T}, s::AbstractString, raise::Bool; kwargs...) where T<:Real
    result = tryparse(T, s; kwargs...)
    if raise && result === nothing
        _parse_failure(T, s)
    end
    return result
end
```
-/
def tryparse_internal_Real_kwargs {S R : Type} (sops : StringOps S)
    (tryparseWhole : S → Jl (Option R)) (s : S) (raise : Bool) : Jl (Option R) := do
  let result ← tryparseWhole s
  if raise && result.isNone then
    let _ ← parse_failure sops s (sops.firstindex s) (sops.lastindex s)
  return result

/--
Julia source: base/parse.jl:364-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

tryparse_internal(::Type{T}, s::AbstractString, startpos::Int, endpos::Int, raise::Bool) where T<:Integer =
    tryparse_internal(T, s, startpos, endpos, 10, raise)
```
-/
def tryparse_internal_Integer_defaultBase {S T : Type}
    (tryparseInternal : S → Nat → Nat → Int → Bool → Jl (Option T))
    (s : S) (start finish : Nat) (raise : Bool) : Jl (Option T) :=
  tryparseInternal s start finish 10 raise

/--
Julia source: base/parse.jl:367-369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

parse(::Type{T}, s::AbstractString; kwargs...) where T<:Real =
    convert(T, tryparse_internal(T, s, true; kwargs...))
```
-/
def parse_Real {S R T : Type} (tryparseInternal : S → Bool → Jl (Option R))
    (convert : Option R → Jl T) (s : S) : Jl T := do
  let result ← tryparseInternal s true
  convert result

/--
Julia source: base/parse.jl:370-371 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parse(::Type{T}, s::AbstractString) where T<:Complex =
    convert(T, tryparse_internal(T, s, firstindex(s), lastindex(s), true))
```
-/
def parse_Complex {S R C : Type} (sops : StringOps S) (cops : ComplexOps S R)
    (convert : Option (ComplexValue R) → Jl C) (s : S) : Jl C := do
  let result ← tryparse_internal_Complex sops cops s
    (sops.firstindex s) (sops.lastindex s) true
  convert result
/--
Julia source: base/parse.jl:372-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

tryparse(T::Type{Complex{S}}, s::AbstractString) where S<:Real =
    tryparse_internal(T, s, firstindex(s), lastindex(s), false)
```
-/
def tryparse_Complex {S R : Type} (sops : StringOps S) (cops : ComplexOps S R)
    (s : S) : Jl (Option (ComplexValue R)) :=
  tryparse_internal_Complex sops cops s (sops.firstindex s) (sops.lastindex s) false


end JuliaLean.base.parse

namespace JuliaLean.BigNums

open JuliaLean

/-- ASCII whitespace: `isspace_ascii` (`base/strings/unicode.jl`) and C `isspace`. -/
def isSpace (c : Char) : Bool := c = ' ' || (9 ≤ c.toNat && c.toNat ≤ 13)

/-- `parseint_preamble(true, base, s, i, j)`, `base/parse.jl:96-121`: the sign, the base (from an
`0b`/`0o`/`0x` prefix when `base == 0`), and the digits after the preamble (`none` for the
zero index returned when a prefix has nothing after it). -/
def preamble (base : Nat) (s : List Char) : Int × Nat × Option (List Char) :=
  let s := s.dropWhile isSpace
  if s = [] then (0, 0, none)
  else
    let (sgn, s) := match s with
      | '-' :: t => (-1, t.dropWhile isSpace)
      | '+' :: t => (1, t.dropWhile isSpace)
      | _ => (1, s)
    if s = [] then (0, 0, none)
    else if base = 0 then
      match s with
      | '0' :: c :: t =>
        let b := if c = 'b' then 2 else if c = 'o' then 8 else if c = 'x' then 16 else 10
        if b = 10 then (sgn, 10, some s)
        else (sgn, b, if t = [] then none else some t)
      | _ => (sgn, 10, some s)
    else (sgn, base, some s)

end JuliaLean.BigNums
