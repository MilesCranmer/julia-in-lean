import JuliaLean.ParsePrint.IntParse

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
    | some d => if ¬ d < base then .error (.argumentError "invalid base digit") else JInt.convert t d

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
